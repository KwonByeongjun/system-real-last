#ifndef BOARD_H
#define BOARD_H

#include <stdint.h> 
#include <unistd.h> 

int init_led_matrix(int *argc, char ***argv);
void update_led_matrix(const char board[8][8]);
void close_led_matrix(void);
void local_led_test(void);

#endif // BOARD_H
