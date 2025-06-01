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

#define SIMULATION_TIME 3.0

static char board_arr[BOARD_SIZE][BOARD_SIZE];

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

int generate_move(char board[BOARD_SIZE][BOARD_SIZE], char player_color,
                  int *out_r1, int *out_c1,
                  int *out_r2, int *out_c2) {
    sleep(2);
    int best_score = -1;
  
    update_led_matrix(board);

    for (int r = 0; r < BOARD_SIZE; ++r) {
        for (int c = 0; c < BOARD_SIZE; ++c) {
            if (board[r][c] != player_color) continue;

            // clone
            for (int d = 0; d < 8; ++d) {
                int nr = r + directions[d][0];
                int nc = c + directions[d][1];
                if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE &&
                    board[nr][nc] == '.') {
                    int flips = count_flips(board, nr, nc, player_color);
                    if (flips > best_score) {
                        best_score = flips;
                        *out_r1 = r; *out_c1 = c;
                        *out_r2 = nr; *out_c2 = nc;
                    }
                }
            }

            // jump
            for (int d = 0; d < 8; ++d) {
                int nr = r + 2 * directions[d][0];
                int nc = c + 2 * directions[d][1];
                if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE &&
                    board[nr][nc] == '.') {
                    int flips = count_flips(board, nr, nc, player_color);
                    if (flips > best_score) {
                        best_score = flips;
                        *out_r1 = r; *out_c1 = c;
                        *out_r2 = nr; *out_c2 = nc;
                    }
                }
            }
        }
    }

    if (best_score == -1) {
        *out_r1 = *out_c1 = *out_r2 = *out_c2 = 0;
        return 0;
    }
    return 1;
}

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
