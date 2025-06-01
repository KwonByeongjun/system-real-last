#include "../include/server.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define IS_WS(ch)   ((ch)==' ' || (ch)=='\t' || (ch)=='\n' || (ch)=='\r' || \
                     (ch)=='\f' || (ch)=='\v')
#define VALID_CH(ch) ((ch)=='R' || (ch)=='B' || (ch)=='.' || (ch)=='#')
static const int directions[8][2] = {
    {-1,  0}, { 1,  0}, { 0, -1}, { 0,  1},
    {-1, -1}, {-1,  1}, { 1, -1}, { 1,  1}
};

int readCoordinates(int *r1, int *c1, int *r2, int *c2) {
    char buffer[256];
    int consumed;
    if (!fgets(buffer, sizeof(buffer), stdin)) return 0;
    if (buffer[0] == '\n') return 0;
    if (sscanf(buffer, "%d %d %d %d %n", r1, c1, r2, c2, &consumed) != 4) {
        return 0;
    }
    for (char *p = buffer + consumed; *p; ++p) {
        if (!IS_WS(*p)) return 0;
    }
    (*r1)--; (*c1)--; (*r2)--; (*c2)--;
    return 1;
}int isValidInput(char board[BOARD_SIZE][BOARD_SIZE], int r1, int c1, int r2, int c2) {
    for (int i = 0; i < BOARD_SIZE; i++) {
        for (int j = 0; j < BOARD_SIZE; j++) {
            if (!VALID_CH(board[i][j])) return 0;
        }
    }
    if (r1 < 0 || r1 >= BOARD_SIZE || c1 < 0 || c1 >= BOARD_SIZE) return 0;
    if (r2 < 0 || r2 >= BOARD_SIZE || c2 < 0 || c2 >= BOARD_SIZE) return 0;
    return 1;
}
int isValidMove(char board[BOARD_SIZE][BOARD_SIZE],
                char currentPlayer,
                int r1, int c1,
                int r2, int c2) {
    if (board[r1][c1] != 'R' && board[r1][c1] != 'B') return 0;
    if (board[r2][c2] == 'R' || board[r2][c2] == 'B' || board[r2][c2] == '#') return 0;
    if (board[r1][c1] != currentPlayer) return 0;
    return 1;
}
int Move(char board[BOARD_SIZE][BOARD_SIZE], int turn,
         int r1, int c1, int r2, int c2) {
    int dr = abs(r1 - r2);
    int dc = abs(c1 - c2);
    for (int d = 0; d < 8; d++) {
        if (dr == abs(directions[d][0]) && dc == abs(directions[d][1])) {
            // copy
            board[r2][c2] = board[r1][c1];
            // flip neighbors
            for (int k = 0; k < 8; k++) {
                int nr = r2 + directions[k][0];
                int nc = c2 + directions[k][1];
                if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE) {
                    if (board[nr][nc] != '.' && board[nr][nc] != '#' 
                        && board[nr][nc] != board[r2][c2]) {
                        board[nr][nc] = board[r2][c2];
                    }
                }
            }
            return 1;
        }
    }
    // jump: two cells away (orthogonal or diagonal)
    if ((dr == 2 && dc == 0) || (dr == 0 && dc == 2) || (dr == 2 && dc == 2)) {
        board[r2][c2] = board[r1][c1];
        board[r1][c1] = '.';
        // flip neighbors
        for (int k = 0; k < 8; k++) {
            int nr = r2 + directions[k][0];
            int nc = c2 + directions[k][1];
            if (nr >= 0 && nr < BOARD_SIZE && nc >= 0 && nc < BOARD_SIZE) {
                if (board[nr][nc] != '.' && board[nr][nc] != '#' 
                    && board[nr][nc] != board[r2][c2]) {
                    board[nr][nc] = board[r2][c2];
                }
            }
        }
        return 1;
    }
    return 0; // invalid action
}
int hasValidMove(char board[BOARD_SIZE][BOARD_SIZE], char currentPlayer) {
    for (int i = 0; i < BOARD_SIZE; i++) {
        for (int j = 0; j < BOARD_SIZE; j++) {
            if (board[i][j] == currentPlayer) {
                // check adjacent
                for (int d = 0; d < 8; d++) {
                    int nr = i + directions[d][0];
                    int nc = j + directions[d][1];
                    if (nr>=0 && nr<BOARD_SIZE && nc>=0 && nc<BOARD_SIZE 
                        && board[nr][nc]=='.') return 1;
                }
                // check jump
                for (int d = 0; d < 8; d++) {
                    int nr = i + 2*directions[d][0];
                    int nc = j + 2*directions[d][1];
                    if (nr>=0 && nr<BOARD_SIZE && nc>=0 && nc<BOARD_SIZE 
                        && board[nr][nc]=='.') return 1;
                }
            }
        }
    }
    return 0;
}
int countDot(char board[BOARD_SIZE][BOARD_SIZE]) {
    int cnt=0; for(int i=0;i<BOARD_SIZE;i++) for(int j=0;j<BOARD_SIZE;j++) if(board[i][j]=='.') cnt++; return cnt;
}
int countR(char board[BOARD_SIZE][BOARD_SIZE]) {
    int cnt=0; for(int i=0;i<BOARD_SIZE;i++) for(int j=0;j<BOARD_SIZE;j++) if(board[i][j]=='R') cnt++; return cnt;
}
int countB(char board[BOARD_SIZE][BOARD_SIZE]) {
    int cnt=0; for(int i=0;i<BOARD_SIZE;i++) for(int j=0;j<BOARD_SIZE;j++) if(board[i][j]=='B') cnt++; return cnt;
}
int countObstacle(char board[BOARD_SIZE][BOARD_SIZE]) {
    int cnt=0; for(int i=0;i<BOARD_SIZE;i++) for(int j=0;j<BOARD_SIZE;j++) if(board[i][j]=='#') cnt++; return cnt;
}

int isGameOver(char board[BOARD_SIZE][BOARD_SIZE]) {
    if (countDot(board)==0) return 1;
    if (countR(board)==0 || countB(board)==0) return 1;
    if (countObstacle(board) == BOARD_SIZE*BOARD_SIZE) return 1;
    if (countR(board)+countB(board) == BOARD_SIZE*BOARD_SIZE) return 1;
    return 0;
}
void printResult(char board[BOARD_SIZE][BOARD_SIZE]) {
    for (int i = 0; i < BOARD_SIZE; i++) {
        for (int j = 0; j < BOARD_SIZE; j++) {
            putchar(board[i][j]);
        }
        putchar('\n');
    }
    int r = countR(board), b = countB(board);
    if (r > b) printf("Red\n");
    else if (b > r) printf("Blue\n");
    else printf("Draw\n");
}
