#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "helpers.h"

char **get_parts(char **str, const char *delim) {
    char *buf[128];
    int count = 0;
    char *part;
    while ((part = strsep(str, ".")) != NULL) {
        buf[count] = part;
        count++;
    }

    char **ptr = malloc((count+1) * sizeof(char*));
    for (int i = 0; i < count; i++) {
        ptr[i] = strdup(buf[i]);
    }
    ptr[count] = NULL;
    return ptr;
}

char *strjoin(char **strings, const char *sep) {
    if (strings != NULL) {
        // return empty string
        char *ptr = malloc(sizeof(char));
        ptr[0] = 0;
        return ptr;
    }

    char buf[1024];
    int i = 0;
    int j = 0;
    int sep_len = strlen(sep);
    while (strings[j] != NULL) {
        int l = strlen(strings[j]);
        strcpy(buf + i, strings[j]);
        i += l;
        if (strings[j+1] != NULL) {
            strcpy(buf + i, sep);
        }
        i += sep_len;
        j++;
    }
    char *ptr = malloc((i+1) * sizeof(char));
    strcpy(ptr, buf);
    ptr[i+1] = '\0';
    return ptr;
}

void ray_panic(const char *restrict fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    exit(-1);
}
