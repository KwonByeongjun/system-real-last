#ifndef JSON_UTIL_H
#define JSON_UTIL_H

#include "../libs/cJSON.h"

int send_json(int sockfd, const cJSON *json_msg);
cJSON *recv_json(int sockfd);

#endif