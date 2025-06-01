#ifndef CLIENT_H
#define CLIENT_H

#include "server.h"

int generate_move(char board[BOARD_SIZE][BOARD_SIZE], char player_color, int *out_r1, int *out_c1, int *out_r2, int *out_c2);
static int connect_to_server(const char *ip, const char *port);
int client_run(const char *ip, const char *port, const char *username);

#endif