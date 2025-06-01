#include "../libs/rpi-rgb-led-matrix/include/led-matrix-c.h"
#include "../include/board.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <stdint.h>

// 전역 RGB 매트릭스 핸들
static struct RGBLedMatrix *matrix_handle = NULL;
// 시그널 처리용 플래그
static volatile sig_atomic_t interrupted_flag = 0;

// 시그널 핸들러: SIGINT 또는 SIGTERM이 들어오면 interrupted_flag를 1로 세팅
static void handle_sig(int signo) {
    (void)signo;
    interrupted_flag = 1;
}


// (1) 격자선 좌표를 미리 배열로 만든 뒤, 개별 선을 순차적으로 그리는 함수
static void draw_grid_lines(struct LedCanvas *canvas) {
    // 8셀을 64픽셀 선으로 나눠야 하므로, 경계선 위치는 {0, 8, 16, …, 64}
    int lines[9];
    for (int idx = 0; idx <= 8; ++idx) {
        lines[idx] = idx * 8;
    }

    uint8_t gx = 80, gy = 80, gz = 80;

    // 수평선 그리기: y가 lines[i]인 행에 x=0..63
    for (int i = 0; i < 9; ++i) {
        int y = lines[i];
        // 0~63 범위만 허용 → 64는 무시
        if (y >= 0 && y < 64) {
            for (int x = 0; x < 64; ++x) {
                led_canvas_set_pixel(canvas, x, y, gx, gy, gz);
            }
        }
    }
    // 수직선만 그리기: x가 lines[j]인 열에 y=0..63
    for (int j = 0; j < 9; ++j) {
        int x = lines[j];
        if (x >= 0 && x < 64) {
            for (int y = 0; y < 64; ++y) {
                led_canvas_set_pixel(canvas, x, y, gx, gy, gz);
            }
        }
    }
}

// (2) 8×8 보드의 특정 셀(row, col)에 돌을 그리는 함수

static void draw_piece_circle(struct LedCanvas *canvas, int row, int col, char piece) {
    // cell 내부의 실제 그릴 영역(6×6 중앙부) 좌상단 좌표:
    int origin_x = col * 8 + 1; // 예: col=0 → x=1, col=1 → x=9 ...
    int origin_y = row * 8 + 1;

    // 원형 반지름을 픽셀 기준으로 2.5 정도(원 근사치용 정수값 2) 로 설정
    const int radius = 2;
    // 원의 중심 좌표: origin + (6/2) = origin + 3
    const int center_x = origin_x + 2;
    const int center_y = origin_y + 2;

    // 색상 배열 초기화 (R,G,B)
    uint8_t color[3] = {0, 0, 0};
    if (piece == 'R') {
        color[0] = 255; // 빨강 돌
    } else if (piece == 'B') {
        color[2] = 255; // 파랑 돌
    } else {
        return; // '.', '#' 등은 그리지 않음
    }

    // 5×5 박스 내에서 원 근사치 계산 (dx^2 + dy^2 <= radius^2) 방식으로 픽셀 선택
    for (int dy = -radius; dy <= radius; ++dy) {
        for (int dx = -radius; dx <= radius; ++dx) {
            // 원 근사치: dx^2 + dy^2 <= radius^2
            if (dx * dx + dy * dy <= radius * radius) {
                int px = center_x + dx;
                int py = center_y + dy;
                // px, py는 반드시 [0,63] 범위 내여야 함
                if (px >= 0 && px < 64 && py >= 0 && py < 64) {
                    led_canvas_set_pixel(canvas, px, py, color[0], color[1], color[2]);
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────
// (3) LED 매트릭스 초기화 함수 (원본과 시그니처 동일)
//  내부 옵션 설정만 간단히 수정(밝기, 경계선 색 변경 등)
int init_led_matrix(int *argc, char ***argv) {
    struct RGBLedMatrixOptions opts;
    memset(&opts, 0, sizeof(opts));
    // 64×64 매트릭스
    opts.rows = 64;
    opts.cols = 64;
    // 하드웨어 매핑: 고정값 유지
    opts.hardware_mapping = "adafruit-hat";
    // 매트릭스 밝기를 기본 100으로 세팅 (원본: 옵션 없음)
    opts.brightness = 100;

    matrix_handle = led_matrix_create_from_options(&opts, argc, argv);
    if (!matrix_handle) {
        fprintf(stderr, "Error: LED 매트릭스 생성에 실패했습니다. sudo 권한으로 실행하세요.\n");
        return -1;
    }

    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    // 첫 화면: 검은색으로 초기화 후 격자만 그리기
    led_canvas_clear(canvas);
    draw_grid_lines(canvas);
    led_matrix_swap_on_vsync(matrix_handle, canvas);
    printf("LED Matrix: 초기 격자 화면 출력 완료\n");
    return 0;
}

// ─────────────────────────────────────────────────────────────────────
// (4) 보드를 받아서 “격자 + 돌”을 모두 새로 그리는 함수 (원본과 시그니처 동일)
void update_led_matrix(const char board[8][8]) {
    if (!matrix_handle) return;

    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    // 화면 전체 초기화
    led_canvas_clear(canvas);
    // (1) 격자선 다시 그리기
    draw_grid_lines(canvas);
    // (2) 보드 배열 순회하며 돌 있으면 원형 모양으로 그리기
    for (int r = 0; r < 8; ++r) {
        for (int c = 0; c < 8; ++c) {
            char ch = board[r][c];
            if (ch == 'R' || ch == 'B') {
                draw_piece_circle(canvas, r, c, ch);
            }
        }
    }
    // (3) 동기화된 화면 교체
    led_matrix_swap_on_vsync(matrix_handle, canvas);
}

// ─────────────────────────────────────────────────────────────────────
// (5) 매트릭스 종료 함수 (원본과 시그니처 동일)
void close_led_matrix(void) {
    if (!matrix_handle) return;
    // 화면 지우고
    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    led_canvas_clear(canvas);
    // 매트릭스 핸들 삭제
    led_matrix_delete(matrix_handle);
    matrix_handle = NULL;
    printf("LED Matrix: 정상 종료됨\n");
}

// ─────────────────────────────────────────────────────────────────────
// (6) 로컬 테스트용 함수 (원본과 시그니처 동일)
//  터미널에서 직접 보드 8줄 입력 후, 반복해서 화면에 표시
void local_led_test(void) {
    if (!matrix_handle) {
        fprintf(stderr, "Error: 매트릭스가 초기화되지 않아 로컬 테스트 불가\n");
        return;
    }

    // SIGINT/SIGTERM 처리해서 Ctrl+C로 종료 가능하도록 설정
    struct sigaction sa;
    sa.sa_handler = handle_sig;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);

    // 사용자 입력용 8×8 배열 (각 줄마다 문자열 8자)
    char input_board[8][9];
    printf("------ 로컬 LED 테스트 모드 ------\n");
    printf("8줄의 보드 상태(R, B, ., #)를 순서대로 입력하세요.\n");
    for (int i = 0; i < 8; ++i) {
        printf("Line %d > ", i + 1);
        if (scanf("%8s", input_board[i]) != 1) {
            fprintf(stderr, "[Error] 보드 입력 실패\n");
            return;
        }
        // 개행문자 제거
        int ch;
        while ((ch = getchar()) != '\n' && ch != EOF);
    }
    printf("입력 종료. Ctrl+C 누르면 테스트 종료됩니다.\n");

    // 인터럽트 신호가 올 때까지 반복
    interrupted_flag = 0;
    while (!interrupted_flag) {
        // 화면 갱신
        update_led_matrix((const char (*)[8])input_board);
        // 0.1초 딜레이 (원본과 약간 다르게 100ms)
        usleep(100000);
    }

    // 시그널 리셋
    sigaction(SIGINT, NULL, NULL);
    sigaction(SIGTERM, NULL, NULL);
    printf("로컬 테스트 모드 종료\n");
}
