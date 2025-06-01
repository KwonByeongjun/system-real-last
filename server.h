#ifndef SERVER_H
#define SERVER_H

#include <stdio.h>
#include <stdint.h>
#include "../libs/cJSON.h"

#define BOARD_SIZE 8
#define MAX_CLIENTS 2
#define TIMEOUT 5

typedef struct {
    int socket;
    char username[32];
    char color;
    int registered; 
} Player;

typedef struct {
    Player players[MAX_CLIENTS];
    int current_turn; 
    char board[BOARD_SIZE][BOARD_SIZE];
} GameState;

void init_game_state(GameState *game);
int server_run(const char *port);


#endif 
