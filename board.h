// include/board.h

#ifndef BOARD_H
#define BOARD_H

#include <stdint.h>  // uint8_t 사용 시 필요
#include <unistd.h>  // usleep 등 필요하다면

// LED 매트릭스 초기화: argc, argv를 그대로 넘겨줌
// main 함수에서 init_led_matrix(&argc, argv); 식으로 호출
int init_led_matrix(int *argc, char ***argv);

// 8×8 보드 배열을 받아서 LED 매트릭스에 그려주는 함수
void update_led_matrix(const char board[8][8]);

// LED 매트릭스 닫을 때 호출
void close_led_matrix(void);

// 로컬 테스트용: 8줄의 보드 입력을 받아 LED에 반복 출력 (디버그용)
void local_led_test(void);

#endif // BOARD_H
