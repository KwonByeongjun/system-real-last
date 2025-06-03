#include "../include/client.h"
#include "../include/game.h"      // directions[8][2] 등 제공
#include "../include/json.h"
#include "../include/board.h"
#include "../libs/cJSON.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/socket.h>
#include <netdb.h>
#include <arpa/inet.h>
#include <time.h>
#include <math.h>

// -----------------------------------------------------------------------------
//  Greedy‑specific 설정값 & 헬퍼
// -----------------------------------------------------------------------------
#define INF             1000000000
#define BOARD_N         BOARD_SIZE   // 8
#define MAX_MOVES_EST   256          // 안전 여유치
#define FEATURE_CNT     8

// 단계별(초반/중반/종반) 가중치 테이블
static const int W[3][FEATURE_CNT] = {
    /* 0:Opening */ { +100, +60, +800, +40, -30, -20, +10,   0 },
    /* 1:Mid     */ { +100, +80, +400, +60, -30, -10,   0,   0 },
    /* 2:End     */ {  +30, +40, +100,   0,   0,  -5,   0, +50 }
};

static inline int phase_index(int empty_cnt) {
    if (empty_cnt > 32) return 0;     // opening
    if (empty_cnt > 12) return 1;     // mid‑game
    return 2;                         // end‑game
}

static inline int in_board(int r, int c) {
    return (unsigned)r < BOARD_N && (unsigned)c < BOARD_N;
}

// Manhattan 거리  → 중앙화 보너스 (‑distance)
static inline int central_bonus(int r, int c) {
    static const int table[BOARD_N][BOARD_N] = {
        { 7,6,5,4,4,5,6,7 },
        { 6,5,4,3,3,4,5,6 },
        { 5,4,3,2,2,3,4,5 },
        { 4,3,2,1,1,2,3,4 },
        { 4,3,2,1,1,2,3,4 },
        { 5,4,3,2,2,3,4,5 },
        { 6,5,4,3,3,4,5,6 },
        { 7,6,5,4,4,5,6,7 }
    };
    return -table[r][c];
}

// -----------------------------------------------------------------------------
//  빠른 mobility / frontier 계산용 LUT  (8‑bit neighborhood mask → frontier?
// -----------------------------------------------------------------------------
static unsigned char FRONTIER_LUT[256];
static void init_frontier_lut(void) {
    for (int m = 0; m < 256; ++m) {
        int is_frontier = 0;
        for (int bit = 0; bit < 8; ++bit) if (!(m & (1 << bit))) { is_frontier = 1; break; }
        FRONTIER_LUT[m] = (unsigned char)is_frontier;
    }
}

// -----------------------------------------------------------------------------
//  시뮬레이션 적용 (clone / jump) + 특징 추출
// -----------------------------------------------------------------------------
static int evaluate_move(char bd[BOARD_N][BOARD_N], int r1, int c1, int r2, int c2,
                         char me, char opp, int empty_cnt_before)
{
    int feat[FEATURE_CNT] = {0};
    int is_jump = (abs(r1 - r2) > 1 || abs(c1 - c2) > 1);

    // ---- immediate gain & flips ----
    int flip_cnt = 0;
    if (is_jump) bd[r1][c1] = '.';
    bd[r2][c2] = me;

    for (int d = 0; d < 8; ++d) {
        int nr = r2 + directions[d][0];
        int nc = c2 + directions[d][1];
        if (in_board(nr, nc) && bd[nr][nc] == opp) {
            bd[nr][nc] = me;
            ++flip_cnt;
        }
    }
    feat[0] = flip_cnt;                         // Immediate gain

    // ---- mobility difference after move ----
    int my_mob = 0, opp_mob = 0;
    for (int r = 0; r < BOARD_N; ++r) {
        for (int c = 0; c < BOARD_N; ++c) {
            if (bd[r][c] == '.') continue;
            char who = bd[r][c];
            for (int d = 0; d < 8; ++d) {
                int nr = r + directions[d][0];
                int nc = c + directions[d][1];
                for (int step = 1; step <= 2; ++step, nr += directions[d][0], nc += directions[d][1]) {
                    if (!in_board(nr, nc)) break;
                    if (bd[nr][nc] != '.') continue;
                    if (who == me) ++my_mob; else ++opp_mob;
                    goto NEXT_CELL;   // 한 칸이라도 비어있으면 mobility 확보
                }
            }
        NEXT_CELL: ;
        }
    }
    feat[1] = my_mob - opp_mob;                 // Mobility Δ

    // ---- corner & edge ----
    const int corner = ( (r2 == 0 && c2 == 0) || (r2 == 0 && c2 == 7)
                      || (r2 == 7 && c2 == 0) || (r2 == 7 && c2 == 7) );
    feat[2] = corner;                           // Corner capture
    const int edge = (!corner) && (r2 == 0 || r2 == 7 || c2 == 0 || c2 == 7);
    feat[3] = edge;                             // Edge stability

    // ---- frontier penalty (after move) ----
    int frontier_cnt = 0;
    for (int r = 0; r < BOARD_N; ++r) {
        for (int c = 0; c < BOARD_N; ++c) if (bd[r][c] == me) {
            unsigned char mask = 0;
            int bit = 0;
            for (int dr = -1; dr <= 1; ++dr) {
                for (int dc = -1; dc <= 1; ++dc) if (dr || dc) {
                    int nr = r + dr, nc = c + dc;
                    if (!in_board(nr, nc) || bd[nr][nc] != '.') mask |= (1 << bit);
                    ++bit;
                }
            }
            frontier_cnt += FRONTIER_LUT[mask] ^ 1; // 1 if any neighbor empty
        }
    }
    feat[4] = frontier_cnt;

    // ---- jump discount ----
    feat[5] = is_jump;

    // ---- central bonus ----
    feat[6] = central_bonus(r2, c2);

    // ---- parity (빈칸 짝/홀) ----
    int empty_after = empty_cnt_before - 1 - (is_jump ? 0 : 0); // 점프/클론 모두 ‑1
    feat[7] = (empty_after & 1) ^ 1;  // 짝수면 1, 홀수면 0

    // ---- 가중치 합산 ----
    int idx = phase_index(empty_after);
    int score = 0;
    for (int i = 0; i < FEATURE_CNT; ++i) score += feat[i] * W[idx][i];

    return score;
}

// -----------------------------------------------------------------------------
//  Greedy move generator (TOP‑16 beam)
// -----------------------------------------------------------------------------
int generate_move(char board[BOARD_N][BOARD_N], char my_color,
                  int *sr, int *sc, int *dr, int *dc)
{
    static int lut_init = 0;
    if (!lut_init) { init_frontier_lut(); lut_init = 1; }

    char opp = (my_color == 'R' ? 'B' : 'R');

    int empty_cnt = 0;
    for (int r = 0; r < BOARD_N; ++r)
        for (int c = 0; c < BOARD_N; ++c)
            if (board[r][c] == '.') ++empty_cnt;

    int best_score = -INF;
    int best_r1 = -1, best_c1 = -1, best_r2 = -1, best_c2 = -1;

    // 1) legal move enumeration + feature scoring
    typedef struct { int r1,c1,r2,c2,score; } Move;
    Move moves[MAX_MOVES_EST];
    int mcnt = 0;

    for (int r = 0; r < BOARD_N; ++r) {
        for (int c = 0; c < BOARD_N; ++c) if (board[r][c] == my_color) {
            for (int d = 0; d < 8; ++d) {
                int nr = r + directions[d][0];
                int nc = c + directions[d][1];
                for (int step = 1; step <= 2; ++step, nr += directions[d][0], nc += directions[d][1]) {
                    if (!in_board(nr, nc)) break;
                    if (board[nr][nc] != '.') continue;

                    char sim[BOARD_N][BOARD_N];
                    memcpy(sim, board, sizeof(char)*BOARD_N*BOARD_N);
                    int sc_score = evaluate_move(sim, r, c, nr, nc, my_color, opp, empty_cnt);

                    moves[mcnt++] = (Move){r,c,nr,nc,sc_score};
                }
            }
        }
    }
    if (mcnt == 0) return 0;   // 패스

    // 2) partial sort – 상위 16 개만 선별 (O(N*16))
    const int BEAM = 16;
    int limit = mcnt < BEAM ? mcnt : BEAM;
    for (int i = 0; i < limit; ++i) {
        int bestj = i;
        for (int j = i+1; j < mcnt; ++j)
            if (moves[j].score > moves[bestj].score) bestj = j;
        if (bestj != i) { Move tmp = moves[i]; moves[i] = moves[bestj]; moves[bestj] = tmp; }
    }

    // 3) 자살 수(상대 mobility 급증+내 급감) 필터 & 최종 선택
    int chosen = 0;
    for (int i = 0; i < limit; ++i) {
        int r1=moves[i].r1, c1=moves[i].c1, r2=moves[i].r2, c2=moves[i].c2;
        char sim[BOARD_N][BOARD_N];
        memcpy(sim, board, sizeof(char)*BOARD_N*BOARD_N);
        int is_jump = (abs(r1-r2)>1 || abs(c1-c2)>1);
        evaluate_move(sim, r1, c1, r2, c2, my_color, opp, empty_cnt); // sim 에 반영

        // mobility 재계산
        int my_m=0, op_m=0;
        for (int r=0;r<BOARD_N;++r)for(int c=0;c<BOARD_N;++c){
            if(sim[r][c]=='.')continue;char w=sim[r][c];
            for(int d=0;d<8;++d){int nr=r+directions[d][0],nc=c+directions[d][1];
                for(int s=1;s<=2;++s,nr+=directions[d][0],nc+=directions[d][1]){
                    if(!in_board(nr,nc))break; if(sim[nr][nc]!='.')continue;
                    if(w==my_color)++my_m; else ++op_m; goto L1;} } L1:; }
        if(op_m-my_m>70 && my_m<5) continue; // 자살 수 컷

        best_score = moves[i].score;
        best_r1=r1;best_c1=c1;best_r2=r2;best_c2=c2;
        chosen=1;
        break;
    }

    if(!chosen){ best_r1=moves[0].r1;best_c1=moves[0].c1;best_r2=moves[0].r2;best_c2=moves[0].c2; }

    *sr=best_r1; *sc=best_c1; *dr=best_r2; *dc=best_c2;
    return 1;
}

// ========================
// 서버 연결 유틸
// ========================
static int connect_to_server(const char *ip, const char *port) {
    struct addrinfo hints, *res, *p;
    int sockfd;
    memset(&hints, 0, sizeof hints);
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    if (getaddrinfo(ip, port, &hints, &res) != 0) {
        perror("getaddrinfo");
        return -1;
    }
    for (p = res; p; p = p->ai_next) {
        sockfd = socket(p->ai_family, p->ai_socktype, p->ai_protocol);
        if (sockfd < 0) continue;
        if (connect(sockfd, p->ai_addr, p->ai_addrlen) == 0) break;
        close(sockfd);
    }
    freeaddrinfo(res);
    if (!p) {
        fprintf(stderr, "Failed to connect to %s:%s\n", ip, port);
        return -1;
    }
    return sockfd;
}

// ========================
// 클라이언트 메인 루프
// ========================
int client_run(const char *ip, const char *port, const char *username) {
    int sockfd = connect_to_server(ip, port);
    if (sockfd < 0) {
        fprintf(stderr, "Failed to connect to %s:%s\n", ip, port);
        return EXIT_FAILURE;
    }

    // 1) register 요청
    {
        cJSON *reg = cJSON_CreateObject();
        cJSON_AddStringToObject(reg, "type", "register");
        cJSON_AddStringToObject(reg, "username", username);
        if (send_json(sockfd, reg) < 0) {
            fprintf(stderr, "Failed to send register message\n");
            cJSON_Delete(reg);
            close(sockfd);
            return EXIT_FAILURE;
        }
        cJSON_Delete(reg);
    }

    int waiting_for_result = 0;
    char my_color = 0;

    while (1) {
        cJSON *msg = recv_json(sockfd);
        if (!msg) {
            break;
        }
        cJSON *jtype = cJSON_GetObjectItem(msg, "type");
        if (!jtype || !jtype->valuestring) {
            cJSON_Delete(msg);
            continue;
        }
        const char *type = jtype->valuestring;

        // register_ack
        if (strcmp(type, "register_ack") == 0) {
            printf("Registered as %s\n", username);
            cJSON_Delete(msg);
            continue;
        }
        // register_nack
        else if (strcmp(type, "register_nack") == 0) {
            cJSON *jreason = cJSON_GetObjectItem(msg, "reason");
            if (jreason && jreason->valuestring)
                printf("Register failed: %s\n", jreason->valuestring);
            else
                printf("Register failed (unknown reason)\n");
            cJSON_Delete(msg);
            break;
        }
        // game_start
        else if (strcmp(type, "game_start") == 0) {
            printf("Game started\n");
            cJSON *jplayers = cJSON_GetObjectItem(msg, "players");
            if (jplayers && cJSON_IsArray(jplayers)) {
                const cJSON *p0 = cJSON_GetArrayItem(jplayers, 0);
                if (p0 && p0->valuestring && strcmp(username, p0->valuestring) == 0)
                    my_color = 'R';
                else
                    my_color = 'B';
            }
            cJSON_Delete(msg);
            continue;
        }
        // your_turn
        else if (strcmp(type, "your_turn") == 0) {
            cJSON *jbarr = cJSON_GetObjectItem(msg, "board");
            if (jbarr && cJSON_IsArray(jbarr)) {
                int nrows = cJSON_GetArraySize(jbarr);
                printf("Current board:\n");
                for (int i = 0; i < nrows && i < BOARD_SIZE; i++) {
                    const cJSON *jrow = cJSON_GetArrayItem(jbarr, i);
                    if (jrow && jrow->valuestring) {
                        memcpy(board_arr[i], jrow->valuestring, BOARD_SIZE);
                        update_led_matrix(board_arr);
                        char rowbuf[BOARD_SIZE+1];
                        memcpy(rowbuf, jrow->valuestring, BOARD_SIZE);
                        rowbuf[BOARD_SIZE] = '\0';
                        printf("%s\n", rowbuf);
                    }
                }
            }
            cJSON *jtimeout = cJSON_GetObjectItem(msg, "timeout");
            if (jtimeout)
                printf("Timeout: %.1f s\n", jtimeout->valuedouble);

            printf("Your turn (%c)\n", my_color);
            int r1, c1, r2, c2;
            int has_move = generate_move(board_arr, my_color, &r1, &c1, &r2, &c2);

            cJSON *mv = cJSON_CreateObject();
            cJSON_AddStringToObject(mv, "type", "move");
            cJSON_AddStringToObject(mv, "username", username);
            if (has_move) {
                cJSON_AddNumberToObject(mv, "sx", r1 + 1);
                cJSON_AddNumberToObject(mv, "sy", c1 + 1);
                cJSON_AddNumberToObject(mv, "tx", r2 + 1);
                cJSON_AddNumberToObject(mv, "ty", c2 + 1);
            } else {
                cJSON_AddNumberToObject(mv, "sx", 0);
                cJSON_AddNumberToObject(mv, "sy", 0);
                cJSON_AddNumberToObject(mv, "tx", 0);
                cJSON_AddNumberToObject(mv, "ty", 0);
            }
            if (send_json(sockfd, mv) < 0) {
                fprintf(stderr, "Failed to send move/pass message\n");
                cJSON_Delete(mv);
                cJSON_Delete(msg);
                break;
            }
            waiting_for_result = 1;
            cJSON_Delete(mv);
            cJSON_Delete(msg);
            continue;
        }
        // move_ok / invalid_move / pass
        else if (strcmp(type, "move_ok") == 0 ||
                 strcmp(type, "invalid_move") == 0 ||
                 strcmp(type, "pass") == 0)
        {
            if (waiting_for_result) {
                printf("Move result: %s\n", type);
                printf("Next player's turn\n");
                waiting_for_result = 0;
            }
            cJSON *jbarr = cJSON_GetObjectItem(msg, "board");
            if (jbarr && cJSON_IsArray(jbarr)) {
                int nrows = cJSON_GetArraySize(jbarr);
                for (int i = 0; i < nrows && i < BOARD_SIZE; i++) {
                    const cJSON *jrow = cJSON_GetArrayItem(jbarr, i);
                    if (jrow && jrow->valuestring) {
                        memcpy(board_arr[i], jrow->valuestring, BOARD_SIZE);
                    }
                }
                update_led_matrix(board_arr);
            }
            cJSON_Delete(msg);
            continue;
        }
        // game_over
        else if (strcmp(type, "game_over") == 0) {
            printf("Game Over\n");
            cJSON *jbarr = cJSON_GetObjectItem(msg, "board");
            if (jbarr && cJSON_IsArray(jbarr)) {
                int nrows = cJSON_GetArraySize(jbarr);
                printf("Final board:\n");
                for (int i = 0; i < nrows && i < BOARD_SIZE; i++) {
                    const cJSON *jrow = cJSON_GetArrayItem(jbarr, i);
                    if (jrow && jrow->valuestring) {
                        memcpy(board_arr[i], jrow->valuestring, BOARD_SIZE);
                        char rowbuf[BOARD_SIZE+1];
                        memcpy(rowbuf, jrow->valuestring, BOARD_SIZE);
                        rowbuf[BOARD_SIZE] = '\0';
                        printf("%s\n", rowbuf);
                    }
                }
                update_led_matrix(board_arr);
            }
            cJSON *jscores = cJSON_GetObjectItem(msg, "scores");
            if (jscores && cJSON_IsObject(jscores)) {
                printf("Final scores:\n");
                cJSON *child = jscores->child;
                while (child) {
                    if (child->string) {
                        printf("  %s: %d\n", child->string, child->valueint);
                    }
                    child = child->next;
                }
            }
            cJSON_Delete(msg);
            break;
        }
        cJSON_Delete(msg);
    }

    close(sockfd);
    return EXIT_SUCCESS;
}





kwon@raspberrypi:~/real_real/System-Programming-OctaFlip/hw3_202311160 $ g++ -Iinclude -Ilibs/rpi-rgb-led-matrix/include main.c src/server.c src/client.c src/json.c src/game.c src/board.c libs/cJSON.c -Llibs/rpi-rgb-led-matrix/lib -lrgbmatrix -lpthread -lrt -o hw3 
src/client.c: In function ‘int alpha_beta(char (*)[8], char, char, int, int, int)’:
src/client.c:164:31: error: invalid use of incomplete type ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  164 |         int r1 = g_move_list[i].r1;
      |                               ^
src/client.c:159:19: note: forward declaration of ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                   ^~~~~~~~~~~~~
src/client.c:165:31: error: invalid use of incomplete type ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  165 |         int c1 = g_move_list[i].c1;
      |                               ^
src/client.c:159:19: note: forward declaration of ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                   ^~~~~~~~~~~~~
src/client.c:166:31: error: invalid use of incomplete type ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  166 |         int r2 = g_move_list[i].r2;
      |                               ^
src/client.c:159:19: note: forward declaration of ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                   ^~~~~~~~~~~~~
src/client.c:167:31: error: invalid use of incomplete type ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  167 |         int c2 = g_move_list[i].c2;
      |                               ^
src/client.c:159:19: note: forward declaration of ‘struct alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                   ^~~~~~~~~~~~~
src/client.c: At global scope:
src/client.c:187:29: error: conflicting declaration ‘MoveCandidate g_move_list [128]’
  187 | static struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                             ^~~~~~~~~~~
src/client.c:159:33: note: previous declaration as ‘alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate g_move_list [128]’
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |                                 ^~~~~~~~~~~
src/client.c:188:12: error: ‘g_move_cnt’ was declared ‘extern’ and later ‘static’ [-fpermissive]
  188 | static int g_move_cnt = 0;
      |            ^~~~~~~~~~
src/client.c:158:16: note: previous declaration of ‘g_move_cnt’
  158 |     extern int g_move_cnt;
      |                ^~~~~~~~~~
src/client.c: In function ‘void generate_all_moves(const char (*)[8], char)’:
src/client.c:207:21: error: ‘g_move_list’ was not declared in this scope; did you mean ‘g_move_cnt’?
  207 |                     g_move_list[g_move_cnt++] = (struct MoveCandidate){
      |                     ^~~~~~~~~~~
      |                     g_move_cnt
src/client.c:219:17: error: ‘g_move_list’ was not declared in this scope; did you mean ‘g_move_cnt’?
  219 |             if (g_move_list[j].static_score > g_move_list[maxj].static_score) {
      |                 ^~~~~~~~~~~
      |                 g_move_cnt
src/client.c:224:40: error: ‘g_move_list’ was not declared in this scope; did you mean ‘g_move_cnt’?
  224 |             struct MoveCandidate tmp = g_move_list[i];
      |                                        ^~~~~~~~~~~
      |                                        g_move_cnt
src/client.c: In function ‘int generate_move(char (*)[8], char, int*, int*, int*, int*)’:
src/client.c:260:22: error: ‘g_move_list’ was not declared in this scope; did you mean ‘g_move_cnt’?
  260 |             int r1 = g_move_list[i].r1;
      |                      ^~~~~~~~~~~
      |                      g_move_cnt
src/client.c: At global scope:
src/client.c:159:33: error: ‘alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate g_move_list [128]’, declared using local type ‘alpha_beta(char (*)[8], char, char, int, int, int)::MoveCandidate’, is used but never defined [-fpermissive]
  159 |     extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
      |
