#include "../include/client.h"
#include "../include/game.h"
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

#define INF 1000000000
#define MAX_DEPTH 6                  // 탐색 깊이 제한
#define MOVE_ARRAY_SIZE 128          // Move 후보 개수 제한
#define CANDIDATE_K 32               // Top-K 후보만 깊이 탐색
static const double TIME_LIMIT = 2.6;  // 2.6초 시간 제한

static struct timespec start_time;
static char board_arr[BOARD_SIZE][BOARD_SIZE];

// ========================
// 시간 체크 유틸리티
// ========================
static double elapsed_time(void) {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec  - start_time.tv_sec)
         + (now.tv_nsec - start_time.tv_nsec) * 1e-9;
}

static inline int time_exceeded(void) {
    return elapsed_time() >= TIME_LIMIT;
}

// ========================
// 보드 복사, 수 적용, 평가 함수
// ========================
static inline void copy_board(char dst[BOARD_SIZE][BOARD_SIZE],
                              const char src[BOARD_SIZE][BOARD_SIZE]) {
    memcpy(dst, src, BOARD_SIZE * BOARD_SIZE);
}

static inline void apply_move_sim(char bd[BOARD_SIZE][BOARD_SIZE],
                                  int r1, int c1, int r2, int c2,
                                  char me, int is_jump)
{
    if (is_jump) bd[r1][c1] = '.';
    bd[r2][c2]  = me;
    char opp = (me == 'R' ? 'B' : 'R');
    for (int d = 0; d < 8; ++d) {
        int nr = r2 + directions[d][0];
        int nc = c2 + directions[d][1];
        if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE
            && bd[nr][nc] == opp) {
            bd[nr][nc] = me;
        }
    }
}

static int mobility(const char bd[BOARD_SIZE][BOARD_SIZE], char me) {
    int cnt = 0;
    for (int r = 0; r < BOARD_SIZE; ++r) {
        for (int c = 0; c < BOARD_SIZE; ++c) {
            if (bd[r][c] == me) {
                for (int d = 0; d < 8; ++d) {
                    int nr = r + directions[d][0], nc = c + directions[d][1];
                    for (int step = 1; step <= 2; ++step,
                         nr += directions[d][0], nc += directions[d][1]) {
                        if (nr < 0 || nr >= BOARD_SIZE || nc < 0 || nc >= BOARD_SIZE)
                            break;
                        if (bd[nr][nc] == '.') {
                            ++cnt;
                            goto NEXT_CELL;
                        }
                    }
                }
            }
        NEXT_CELL: ;
        }
    }
    return cnt;
}

static int evaluate_board(const char bd[BOARD_SIZE][BOARD_SIZE], char me) {
    char opp = (me == 'R' ? 'B' : 'R');
    int my_cnt = 0, opp_cnt = 0;
    for (int r = 0; r < BOARD_SIZE; ++r) {
        for (int c = 0; c < BOARD_SIZE; ++c) {
            if      (bd[r][c] == me)  ++my_cnt;
            else if (bd[r][c] == opp) ++opp_cnt;
        }
    }
    int piece_diff = my_cnt - opp_cnt;
    int my_mob = mobility(bd, me);
    int opp_mob = mobility(bd, opp);
    int mob_diff = my_mob - opp_mob;
    return piece_diff * 100 + mob_diff * 10;
}

static int has_moves(const char bd[BOARD_SIZE][BOARD_SIZE], char player) {
    for (int r = 0; r < BOARD_SIZE; ++r) {
        for (int c = 0; c < BOARD_SIZE; ++c) {
            if (bd[r][c] == player) {
                for (int d = 0; d < 8; ++d) {
                    int nr = r + directions[d][0], nc = c + directions[d][1];
                    for (int step = 1; step <= 2; ++step,
                         nr += directions[d][0], nc += directions[d][1]) {
                        if (nr < 0 || nr >= BOARD_SIZE || nc < 0 || nc >= BOARD_SIZE)
                            break;
                        if (bd[nr][nc] == '.') return 1;
                    }
                }
            }
        }
    }
    return 0;
}

// ========================
// Alpha-Beta 탐색
// ========================
static int alpha_beta(char bd[BOARD_SIZE][BOARD_SIZE],
                      char me, char player,
                      int depth, int alpha, int beta)
{
    if (time_exceeded()) {
        return evaluate_board(bd, me);
    }
    if (depth == 0) {
        return evaluate_board(bd, me);
    }

    char opp = (player == 'R' ? 'B' : 'R');

    // 패스 처리
    if (!has_moves(bd, player)) {
        if (!has_moves(bd, opp)) {
            int my_cnt = 0, opp_cnt = 0;
            for (int r = 0; r < BOARD_SIZE; ++r)
                for (int c = 0; c < BOARD_SIZE; ++c) {
                    if      (bd[r][c] == me)  ++my_cnt;
                    else if (bd[r][c] == opp) ++opp_cnt;
                }
            if      (my_cnt > opp_cnt) return  INF/2;
            else if (my_cnt < opp_cnt) return -INF/2;
            else                       return 0;
        }
        return -alpha_beta(bd, me, opp, depth, -beta, -alpha);
    }

    int best_val = -INF;
    extern int g_move_cnt;
    extern struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];

    int limit = g_move_cnt < CANDIDATE_K ? g_move_cnt : CANDIDATE_K;
    for (int i = 0; i < limit; ++i) {
        if (time_exceeded()) break;
        int r1 = g_move_list[i].r1;
        int c1 = g_move_list[i].c1;
        int r2 = g_move_list[i].r2;
        int c2 = g_move_list[i].c2;
        char sim[BOARD_SIZE][BOARD_SIZE];
        copy_board(sim, bd);
        apply_move_sim(sim, r1, c1, r2, c2, player,
            (abs(r1 - r2) > 1 || abs(c1 - c2) > 1));
        int val = -alpha_beta(sim, me, opp, depth - 1, -beta, -alpha);
        if (val > best_val) best_val = val;
        if (best_val > alpha) alpha = best_val;
        if (alpha >= beta) break;
    }
    return best_val;
}

// ========================
// Move 후보를 한 번만 생성 + Top-K 정렬
// ========================
struct MoveCandidate {
    int r1, c1, r2, c2;
    int static_score;
};
static struct MoveCandidate g_move_list[MOVE_ARRAY_SIZE];
static int g_move_cnt = 0;

static void generate_all_moves(const char bd[BOARD_SIZE][BOARD_SIZE], char player) {
    g_move_cnt = 0;
    for (int r = 0; r < BOARD_SIZE; ++r) {
        for (int c = 0; c < BOARD_SIZE; ++c) {
            if (bd[r][c] != player) continue;
            for (int d = 0; d < 8; ++d) {
                int nr = r + directions[d][0], nc = c + directions[d][1];
                for (int step = 1; step <= 2; ++step,
                     nr += directions[d][0], nc += directions[d][1]) {
                    if (nr < 0 || nr >= BOARD_SIZE || nc < 0 || nc >= BOARD_SIZE) break;
                    if (bd[nr][nc] != '.') continue;
                    if (g_move_cnt >= MOVE_ARRAY_SIZE) break;
                    char sim[BOARD_SIZE][BOARD_SIZE];
                    copy_board(sim, bd);
                    apply_move_sim(sim, r, c, nr, nc, player,
                        (abs(r - nr) > 1 || abs(c - nc) > 1));
                    int st_score = evaluate_board(sim, player);
                    g_move_list[g_move_cnt++] = (struct MoveCandidate){
                        r, c, nr, nc, st_score
                    };
                }
            }
        }
    }
    // Top-K 후보만 앞쪽에 오도록 partial selection
    int limit = g_move_cnt < CANDIDATE_K ? g_move_cnt : CANDIDATE_K;
    for (int i = 0; i < limit; ++i) {
        int maxj = i;
        for (int j = i + 1; j < g_move_cnt; ++j) {
            if (g_move_list[j].static_score > g_move_list[maxj].static_score) {
                maxj = j;
            }
        }
        if (maxj != i) {
            struct MoveCandidate tmp = g_move_list[i];
            g_move_list[i] = g_move_list[maxj];
            g_move_list[maxj] = tmp;
        }
    }
    // g_move_cnt 그대로 두면, 검색 시 CANDIDATE_K 까지만 사용됨
}

// ========================
// 개선된 generate_move()
// ========================
int generate_move(char board[BOARD_SIZE][BOARD_SIZE],
                  char player_color,
                  int *out_r1, int *out_c1, int *out_r2, int *out_c2)
{
    clock_gettime(CLOCK_MONOTONIC, &start_time);

    char me  = player_color;
    char opp = (me == 'R' ? 'B' : 'R');

    // 1) 후보 이동을 한 번만 생성
    generate_all_moves(board, me);

    int best_score_overall = -INF;
    int best_r1 = -1, best_c1 = -1, best_r2 = -1, best_c2 = -1;

    // 2) Iterative Deepening
    for (int depth = 1; depth <= MAX_DEPTH; ++depth) {
        if (time_exceeded()) break;

        int local_best_score = -INF;
        int local_r1 = -1, local_c1 = -1, local_r2 = -1, local_c2 = -1;

        int limit = g_move_cnt < CANDIDATE_K ? g_move_cnt : CANDIDATE_K;
        for (int i = 0; i < limit; ++i) {
            if (time_exceeded()) break;
            int r1 = g_move_list[i].r1;
            int c1 = g_move_list[i].c1;
            int r2 = g_move_list[i].r2;
            int c2 = g_move_list[i].c2;
            char sim[BOARD_SIZE][BOARD_SIZE];
            copy_board(sim, board);
            apply_move_sim(sim, r1, c1, r2, c2, me,
                (abs(r1 - r2) > 1 || abs(c1 - c2) > 1));
            int score = -alpha_beta(sim, me, opp, depth - 1, -INF, +INF);
            if (score > local_best_score) {
                local_best_score = score;
                local_r1 = r1; local_c1 = c1;
                local_r2 = r2; local_c2 = c2;
            }
        }

        if (!time_exceeded() && local_r1 >= 0) {
            best_score_overall = local_best_score;
            best_r1 = local_r1; best_c1 = local_c1;
            best_r2 = local_r2; best_c2 = local_c2;
        } else {
            break;
        }
    }

    if (best_r1 < 0) {
        *out_r1 = *out_c1 = *out_r2 = *out_c2 = 0;
        return 0; // 패스
    } else {
        *out_r1 = best_r1; *out_c1 = best_c1;
        *out_r2 = best_r2; *out_c2 = best_c2;
        return 1; // 유효한 수
    }
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
