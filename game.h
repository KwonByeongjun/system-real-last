#ifndef GAME_H
#define GAME_H

#include "server.h"

#define IS_WS(ch)    ((ch)==' ' || (ch)=='\t' || (ch)=='\n' || \
                      (ch)=='\r' || (ch)=='\f' || (ch)=='\v')
#define VALID_CH(ch) ((ch)=='R' || (ch)=='B' || (ch)=='.' || (ch)=='#')
static const int directions[8][2] = {
    {-1,  0}, { 1,  0}, { 0, -1}, { 0,  1},
    {-1, -1}, {-1,  1}, { 1, -1}, { 1,  1}
};

int readCoordinates(int *r1, int *c1, int *r2, int *c2);
int isValidInput(char board[BOARD_SIZE][BOARD_SIZE],
                 int r1, int c1,
                 int r2, int c2);
int isValidMove(char board[BOARD_SIZE][BOARD_SIZE],
                char currentPlayer,
                int r1, int c1,
                int r2, int c2);
int Move(char board[BOARD_SIZE][BOARD_SIZE],
         int turn,
         int r1, int c1,
         int r2, int c2);
int hasValidMove(char board[BOARD_SIZE][BOARD_SIZE],
                 char currentPlayer);
int isGameOver(char board[BOARD_SIZE][BOARD_SIZE]);
int countDot(char board[BOARD_SIZE][BOARD_SIZE]);
int countR(char board[BOARD_SIZE][BOARD_SIZE]);
int countB(char board[BOARD_SIZE][BOARD_SIZE]);
int countObstacle(char board[BOARD_SIZE][BOARD_SIZE]);
void printResult(char board[BOARD_SIZE][BOARD_SIZE]);

#endif
