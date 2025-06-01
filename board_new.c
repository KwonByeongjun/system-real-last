#include "../libs/rpi-rgb-led-matrix/include/led-matrix-c.h"
#include "../include/board.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <stdint.h>

static struct RGBLedMatrix *matrix_handle = NULL;
static volatile sig_atomic_t interrupted_flag = 0;

static void handle_sig(int signo) {
    (void)signo;
    interrupted_flag = 1;
}

static void draw_grid_lines(struct LedCanvas *canvas) {
    int lines[9];
    for (int idx = 0; idx <= 8; ++idx) {
        lines[idx] = idx * 8;
    }
    uint8_t gx = 80, gy = 80, gz = 80;
    for (int i = 0; i < 9; ++i) {
        int y = lines[i];
        if (y >= 0 && y < 64) {
            for (int x = 0; x < 64; ++x) {
                led_canvas_set_pixel(canvas, x, y, gx, gy, gz);
            }
        }
    }
    for (int j = 0; j < 9; ++j) {
        int x = lines[j];
        if (x >= 0 && x < 64) {
            for (int y = 0; y < 64; ++y) {
                led_canvas_set_pixel(canvas, x, y, gx, gy, gz);
            }
        }
    }
}

static void draw_piece_circle(struct LedCanvas *canvas, int row, int col, char piece) {
    int origin_x = col * 8 + 1;
    int origin_y = row * 8 + 1;
    const int radius = 2;
    const int center_x = origin_x + 2;
    const int center_y = origin_y + 2;

    uint8_t color[3] = {0, 0, 0};
    if (piece == 'R') {
        color[0] = 255;
    } else if (piece == 'B') {
        color[2] = 255;
    } else {
        return;
    }

    for (int dy = -radius; dy <= radius; ++dy) {
        for (int dx = -radius; dx <= radius; ++dx) {
            if (dx * dx + dy * dy <= radius * radius) {
                int px = center_x + dx;
                int py = center_y + dy;
                if (px >= 0 && px < 64 && py >= 0 && py < 64) {
                    led_canvas_set_pixel(canvas, px, py, color[0], color[1], color[2]);
                }
            }
        }
    }
}

int init_led_matrix(int *argc, char ***argv) {
    struct RGBLedMatrixOptions opts;
    memset(&opts, 0, sizeof(opts));
    opts.rows = 64;
    opts.cols = 64;
    opts.hardware_mapping = "adafruit-hat";
    opts.brightness = 100;

    matrix_handle = led_matrix_create_from_options(&opts, argc, argv);
    if (!matrix_handle) {
        fprintf(stderr, "Error: Fail to initialize LED matrix.\n");
        return -1;
    }

    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    led_canvas_clear(canvas);
    draw_grid_lines(canvas);
    led_matrix_swap_on_vsync(matrix_handle, canvas);
    return 0;
}

void update_led_matrix(const char board[8][8]) {
    if (!matrix_handle) return;

    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    led_canvas_clear(canvas);
    draw_grid_lines(canvas);
    
    for (int r = 0; r < 8; ++r) {
        for (int c = 0; c < 8; ++c) {
            char ch = board[r][c];
            if (ch == 'R' || ch == 'B') {
                draw_piece_circle(canvas, r, c, ch);
            }
        }
    }
    led_matrix_swap_on_vsync(matrix_handle, canvas);
}

void close_led_matrix(void) {
    if (!matrix_handle) return;
    struct LedCanvas *canvas = led_matrix_get_canvas(matrix_handle);
    led_canvas_clear(canvas);
    led_matrix_delete(matrix_handle);
    matrix_handle = NULL;
}

void local_led_test(void) {
    if (!matrix_handle) {
        fprintf(stderr, "Error: Matrix is not initialized.\n");
        return;
    }

    struct sigaction sa;
    sa.sa_handler = handle_sig;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0;
    sigaction(SIGINT, &sa, NULL);
    sigaction(SIGTERM, &sa, NULL);

    char input_board[8][9];
    printf("------ Local LED Test ------\n");
    printf("<8 lines>: initial board state (each line has 8 characters: R, B, ., or #).\n");
    for (int i = 0; i < 8; ++i) {
        printf("Line %d > ", i + 1);
        if (scanf("%8s", input_board[i]) != 1) {
            fprintf(stderr, "[Error] 보드 입력 실패\n");
            return;
        }
        int ch;
        while ((ch = getchar()) != '\n' && ch != EOF);
    }
    printf("Press Ctrl+C to Terminate.\n");

    interrupted_flag = 0;
    while (!interrupted_flag) {
        update_led_matrix((const char (*)[8])input_board);
        usleep(100000);
    }
    sigaction(SIGINT, NULL, NULL);
    sigaction(SIGTERM, NULL, NULL);
    printf("Local test Terminated.\n");
}

#ifdef BOARD_STANDALONE
int main(int argc, char **argv) {
    // 1) LED 초기화 (argv에 LED 옵션 포함될 것)
    if (init_led_matrix(&argc, &argv) < 0) {
        return EXIT_FAILURE;
    }

    // 2) 표준입력에서 8줄 읽기 (각 줄 8문자: R, B, ., #)
    char input_board[8][8];
    for (int i = 0; i < 8; ++i) {
        char buf[64];
        if (fgets(buf, sizeof(buf), stdin) == NULL) {
            fprintf(stderr, "[Error] Board input 부족: %d번째 줄을 읽을 수 없습니다.\n", i + 1);
            close_led_matrix();
            return EXIT_FAILURE;
        }
        size_t len = strcspn(buf, "\r\n");
        if (len < 8) {
            fprintf(stderr, "[Error] Board input 형식 오류: %d번째 줄이 8문자 미만입니다.\n", i + 1);
            close_led_matrix();
            return EXIT_FAILURE;
        }
        memcpy(input_board[i], buf, 8);
    }

    // 3) 읽은 보드를 LED에 한 번 그리기
    update_led_matrix((const char (*)[8])input_board);

    // 4) 화면 유지: 10초 동안 대기
    sleep(10);

    // 5) LED 매트릭스 종료
    close_led_matrix();
    return EXIT_SUCCESS;
}
#endif  // BOARD_STANDALONE
