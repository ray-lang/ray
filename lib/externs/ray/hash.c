#include <stdlib.h>
#include <string.h>
#include "hash.h"

uint32_t ray_hash(const char *s) {
    size_t l = strlen(s);
    if (l == 0) {
        return 0;
    }

    int h = 0;
    for (int i = 0; i < l; i++) {
        h = ((h<<5) - h) + s[i];
    }
    return h;
}
