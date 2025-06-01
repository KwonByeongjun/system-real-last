#include "../include/json.h"
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <stdlib.h>

int send_json(int sockfd, const cJSON *json_msg)
{
    char *json_str = cJSON_PrintUnformatted((cJSON*)json_msg);
    if (!json_str) return -1;
    size_t len = strlen(json_str);
    if (send(sockfd, json_str, len, 0) != (ssize_t)len) {
        free(json_str);
        return -1;
    }
    free(json_str);
    if (send(sockfd, "\n", 1, 0) != 1)
        return -1;
    return 0;
}

cJSON *recv_json(int sockfd)
{
    enum { BUF_SIZE = 4096 };
    static char buf[BUF_SIZE];
    static size_t buf_len = 0;

    while (1) {
        char *newline = (char *)memchr(buf, '\n', buf_len);
        if (newline) {
            size_t msg_len = newline - buf;
            buf[msg_len] = '\0';
            cJSON *msg = cJSON_Parse(buf);

            size_t used = msg_len + 1;
            memmove(buf, buf + used, buf_len - used);
            buf_len -= used;
            return msg;
        }

        if (buf_len + 1 >= BUF_SIZE) return NULL; 
        ssize_t n = recv(sockfd, buf + buf_len, BUF_SIZE - buf_len - 1, 0);
        if (n <= 0) return NULL;
        buf_len += n;
        buf[buf_len] = '\0';
    }
}
