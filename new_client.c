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

#define SIMULATION_TIME 3.0
#define SIZE            BOARD_SIZE   // 8
#define INF             1000000000

static char board_arr[BOARD_SIZE][BOARD_SIZE];

/* 기존 count_flips 함수 그대로 유지 */
int count_flips(char board[BOARD_SIZE][BOARD_SIZE],
                int r, int c, char player_color) {
    int flip_count = 0;
    char opponent = (player_color == 'R') ? 'B' : 'R';
    for (int d = 0; d < 8; ++d) {
        int nr = r + directions[d][0];
        int nc = c + directions[d][1];
        if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE) {
            if (board[nr][nc] == opponent) {
                flip_count++;
            }
        }
    }
    return flip_count;
}

/* =================================================================
 *                  시간 제한용 유틸리티
 * =================================================================*/
static struct timespec start_time;
static const double TIME_LIMIT = 2.9;  // 2.9초 후 탐색 중단

static double elapsed_time() {
    struct timespec now;
    clock_gettime(CLOCK_MONOTONIC, &now);
    return (now.tv_sec - start_time.tv_sec)
         + (now.tv_nsec - start_time.tv_nsec) * 1e-9;
}

static int time_exceeded() {
    return elapsed_time() >= TIME_LIMIT;
}

/* =================================================================
 *                        AI  (Iterative Deepening + α-β 가지치기)
 * =================================================================*/

// 8방향 증분 배열 (상, 상좌, 상우, 좌, 우, 하좌, 하, 하우)
static const int DR[8] = { -1, -1, -1,  0,  0,  1,  1,  1 };
static const int DC[8] = { -1,  0,  1, -1,  1, -1,  0,  1 };

/* 보드 복사 */
static inline void copy_board(char dst[SIZE][SIZE], char src[SIZE][SIZE]) {
    memcpy(dst, src, SIZE * SIZE);
}

/* 주어진 이동을 보드에 적용 (점프인지 아닌지 구분) */
static void apply_move_sim(char bd[SIZE][SIZE],
                           int r1, int c1, int r2, int c2,
                           char me, int is_jump) {
    if (is_jump) bd[r1][c1] = '.';
    bd[r2][c2] = me;
    char opp = (me == 'R') ? 'B' : 'R';
    for (int d = 0; d < 8; ++d) {
        int nr = r2 + DR[d], nc = c2 + DC[d];
        if (0 <= nr && nr < SIZE && 0 <= nc && nc < SIZE && bd[nr][nc] == opp) {
            bd[nr][nc] = me;
        }
    }
}

/* 모빌리티 계산: 특정 색의 돌이 둘 수 있는 빈 칸 개수 세기 */
static int mobility(char bd[SIZE][SIZE], char me) {
    int cnt = 0;
    for (int r = 0; r < SIZE; ++r) {
        for (int c = 0; c < SIZE; ++c) {
            if (bd[r][c] != me) continue;
            for (int d = 0; d < 8; ++d) {
                int nr = r + DR[d], nc = c + DC[d];
                for (int step = 1; step <= 2; ++step, nr += DR[d], nc += DC[d]) {
                    if (nr < 0 || nr >= SIZE || nc < 0 || nc >= SIZE) break;
                    if (bd[nr][nc] == '.') {
                        ++cnt;
                        goto NEXT_CELL;
                    }
                }
            }
            NEXT_CELL: ;
        }
    }
    return cnt;
}

/* 보드 평가 함수: 말 개수 차이 *100 + 모빌리티 차이 *10 */
static int evaluate_board(char bd[SIZE][SIZE], char me) {
    char opp = (me == 'R') ? 'B' : 'R';
    int my_cnt = 0, opp_cnt = 0;
    for (int i = 0; i < SIZE; ++i) {
        for (int j = 0; j < SIZE; ++j) {
            if      (bd[i][j] == me)  ++my_cnt;
            else if (bd[i][j] == opp) ++opp_cnt;
        }
    }
    int piece_diff = my_cnt - opp_cnt;
    int my_mob  = mobility(bd, me);
    int opp_mob = mobility(bd, opp);
    int mob_diff = my_mob - opp_mob;
    return piece_diff * 100 + mob_diff * 10;
}

/* 현재 플레이어가 둘 수 있는 수가 하나라도 있는지 검사 */
static int has_moves(char bd[SIZE][SIZE], char player) {
    for (int r = 0; r < SIZE; ++r) {
        for (int c = 0; c < SIZE; ++c) {
            if (bd[r][c] != player) continue;
            for (int d = 0; d < 8; ++d) {
                int nr = r + DR[d], nc = c + DC[d];
                for (int step = 1; step <= 2; ++step, nr += DR[d], nc += DC[d]) {
                    if (nr < 0 || nr >= SIZE || nc < 0 || nc >= SIZE) break;
                    if (bd[nr][nc] == '.') return 1;
                }
            }
        }
    }
    return 0;
}

/* α-β 가지치기 탐색 (negamax 형태) */
static int alpha_beta(char bd[SIZE][SIZE],
                      char me, char player,
                      int depth, int alpha, int beta) {
    if (time_exceeded()) {
        return evaluate_board(bd, me);
    }
    if (depth == 0) {
        return evaluate_board(bd, me);
    }

    char opp = (player == 'R') ? 'B' : 'R';

    /* 현재 플레이어가 둘 수 없으면(턴 건너뛰기 검사) */
    if (!has_moves(bd, player)) {
        if (!has_moves(bd, opp)) {
            /* 양쪽 모두 못 두면 게임 종료, 터미널 스코어 */
            int my_cnt = 0, opp_cnt = 0;
            for (int i = 0; i < SIZE; ++i) {
                for (int j = 0; j < SIZE; ++j) {
                    if      (bd[i][j] == me)  ++my_cnt;
                    else if (bd[i][j] == opp) ++opp_cnt;
                }
            }
            if      (my_cnt > opp_cnt) return  INF/2;
            else if (my_cnt < opp_cnt) return -INF/2;
            else                        return  0;
        }
        /* 상대만 수가 있으면, 내 차례 건너뛰기 */
        int val = -alpha_beta(bd, me, opp, depth, -beta, -alpha);
        return val;
    }

    int best_val = -INF;
    typedef struct {
        int r1, c1, r2, c2;
        int static_score;
    } Move;
    Move all_moves[256];
    int move_cnt = 0;

    /* (1) 가능한 모든 수 생성 & 정적 평가값(static_score) 계산 */
    for (int r = 0; r < SIZE; ++r) {
        for (int c = 0; c < SIZE; ++c) {
            if (bd[r][c] != player) continue;
            for (int d = 0; d < 8; ++d) {
                int nr = r + DR[d], nc = c + DC[d];
                for (int step = 1; step <= 2; ++step, nr += DR[d], nc += DC[d]) {
                    if (nr < 0 || nr >= SIZE || nc < 0 || nc >= SIZE) break;
                    if (bd[nr][nc] != '.') continue;

                    /* 임시 보드에 한 수 적용 */
                    char sim[SIZE][SIZE];
                    copy_board(sim, bd);
                    apply_move_sim(sim, r, c, nr, nc, player, (step == 2));
                    /* 정적 평가: evaluate_board(…, player) 사용 */
                    int st_score = evaluate_board(sim, player);
                    all_moves[move_cnt++] = (Move){r, c, nr, nc, st_score};
                }
            }
        }
    }

    /* (2) 정적 평가(static_score) 내림차순으로 정렬(버블 정렬) */
    for (int i = 0; i < move_cnt; ++i) {
        for (int j = i + 1; j < move_cnt; ++j) {
            if (all_moves[j].static_score > all_moves[i].static_score) {
                Move tmp = all_moves[i];
                all_moves[i] = all_moves[j];
                all_moves[j] = tmp;
            }
        }
    }

    /* (3) α‐β 탐색: ordering된 순서대로 탐색 */
    for (int i = 0; i < move_cnt; ++i) {
        int r1 = all_moves[i].r1, c1 = all_moves[i].c1;
        int r2 = all_moves[i].r2, c2 = all_moves[i].c2;
        char sim[SIZE][SIZE];
        copy_board(sim, bd);
        apply_move_sim(sim, r1, c1, r2, c2, player,
                       (abs(r1 - r2) > 1 || abs(c1 - c2) > 1));

        int val = -alpha_beta(sim, me, opp, depth - 1, -beta, -alpha);
        if (val > best_val) best_val = val;
        if (best_val > alpha) alpha = best_val;
        if (alpha >= beta) break;
        if (time_exceeded()) break;
    }

    return best_val;
}

/* Iterative Deepening + α-β 가지치기를 이용한 generate_move */
int generate_move(char board[BOARD_SIZE][BOARD_SIZE], char player_color,
                  int *out_r1, int *out_c1,
                  int *out_r2, int *out_c2) {
    /* 탐색 시작 시각 기록 */
    clock_gettime(CLOCK_MONOTONIC, &start_time);

    char me = player_color;
    char opp = (me == 'R') ? 'B' : 'R';

    int best_score_overall = -INF;
    int best_r1 = -1, best_c1 = -1, best_r2 = -1, best_c2 = -1;

    /* 시간 내에 가능한 만큼 깊이(depth)를 1씩 늘리며 탐색 */
    for (int depth = 1; depth <= 8; ++depth) {
        if (time_exceeded()) break;

        int local_best_score = -INF;
        int local_r1 = -1, local_c1 = -1, local_r2 = -1, local_c2 = -1;

        typedef struct {
            int r1, c1, r2, c2;
            int static_score;
        } Move;
        Move all_moves[256];
        int move_cnt = 0;

        /* (1) 후보 생성 & 정적 평가 */
        for (int r = 0; r < SIZE; ++r) {
            for (int c = 0; c < SIZE; ++c) {
                if (board[r][c] != me) continue;
                for (int d = 0; d < 8; ++d) {
                    int nr = r + DR[d], nc = c + DC[d];
                    for (int step = 1; step <= 2; ++step, nr += DR[d], nc += DC[d]) {
                        if (nr < 0 || nr >= SIZE || nc < 0 || nc >= SIZE) break;
                        if (board[nr][nc] != '.') continue;

                        char sim[SIZE][SIZE];
                        copy_board(sim, board);
                        apply_move_sim(sim, r, c, nr, nc, me,
                                       (abs(r - nr) > 1 || abs(c - nc) > 1));
                        int st_score = evaluate_board(sim, me);
                        all_moves[move_cnt++] = (Move){r, c, nr, nc, st_score};
                    }
                }
            }
        }

        /* (2) 정렬: 정적 점수 내림차순 */
        for (int i = 0; i < move_cnt; ++i) {
            for (int j = i + 1; j < move_cnt; ++j) {
                if (all_moves[j].static_score > all_moves[i].static_score) {
                    Move tmp = all_moves[i];
                    all_moves[i] = all_moves[j];
                    all_moves[j] = tmp;
                }
            }
        }

        /* (3) α‐β 탐색 (한 번에 하나씩 살펴보며 값 계산) */
        for (int i = 0; i < move_cnt; ++i) {
            if (time_exceeded()) break;

            int r1 = all_moves[i].r1, c1 = all_moves[i].c1;
            int r2 = all_moves[i].r2, c2 = all_moves[i].c2;
            char sim[SIZE][SIZE];
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

        /* (4) 이 깊이 탐색을 완료했다면, 최고 결과를 “전체 최적”으로 갱신 */
        if (!time_exceeded() && local_r1 >= 0) {
            best_score_overall = local_best_score;
            best_r1 = local_r1; best_c1 = local_c1;
            best_r2 = local_r2; best_c2 = local_c2;
        } else {
            /* 시간이 다 되었거나 후보가 없으면 종료 */
            break;
        }
    }

    /* 둘 수 없으면 패스 신호 (0 반환) */
    if (best_r1 < 0) {
        *out_r1 = *out_c1 = *out_r2 = *out_c2 = 0;
        return 0;
    }

    *out_r1 = best_r1;
    *out_c1 = best_c1;
    *out_r2 = best_r2;
    *out_c2 = best_c2;
    return 1;
}

/* =================================================================
 *              이하 connect_to_server(), client_run()는 수정 금지
 * =================================================================*/
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
            // 서버 연결이 끊기거나 오류 발생
            break;
        }
        cJSON *jtype = cJSON_GetObjectItem(msg, "type");
        if (!jtype || !jtype->valuestring) {
            cJSON_Delete(msg);
            continue;
        }
        const char *type = jtype->valuestring;

        // 2-1) register_ack
        if (strcmp(type, "register_ack") == 0) {
            printf("Registered as %s\n", username);
            cJSON_Delete(msg);
            continue;
        }
        // 2-2) register_nack
        else if (strcmp(type, "register_nack") == 0) {
            cJSON *jreason = cJSON_GetObjectItem(msg, "reason");
            if (jreason && jreason->valuestring)
                printf("Register failed: %s\n", jreason->valuestring);
            else
                printf("Register failed (unknown reason)\n");
            cJSON_Delete(msg);
            break;
        }
        // 2-3) game_start 
        else if (strcmp(type, "game_start") == 0) {
            printf("Game started\n");
            cJSON *jplayers = cJSON_GetObjectItem(msg, "players");
            if (jplayers && cJSON_IsArray(jplayers)) {
                const cJSON *p0 = cJSON_GetArrayItem(jplayers, 0);
                // 첫 번째 R, 아니면 B
                if (p0 && p0->valuestring && strcmp(username, p0->valuestring) == 0)
                    my_color = 'R';
                else
                    my_color = 'B';
            }

            cJSON_Delete(msg);
            continue;
        }
        // 2-4) your_turn (board + timeout 전달)
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
            // timeout
            cJSON *jtimeout = cJSON_GetObjectItem(msg, "timeout");
            if (jtimeout)
                printf("Timeout: %.1f s\n", jtimeout->valuedouble);

            printf("Your turn (%c)\n", my_color);
            int r1, c1, r2, c2;
            int has_move = generate_move(board_arr, my_color, &r1, &c1, &r2, &c2);

            // move, pass
            cJSON *mv = cJSON_CreateObject();
            cJSON_AddStringToObject(mv, "type", "move");
            cJSON_AddStringToObject(mv, "username", username);
            if (has_move) {
                cJSON_AddNumberToObject(mv, "sx", r1 + 1);
                cJSON_AddNumberToObject(mv, "sy", c1 + 1);
                cJSON_AddNumberToObject(mv, "tx", r2 + 1);
                cJSON_AddNumberToObject(mv, "ty", c2 + 1);
            } else {
                // no valid move -> pass
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
            // score
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
