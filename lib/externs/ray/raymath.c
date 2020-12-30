#include <stdlib.h>
#include "raymath.h"

intptr_t ray_math_rand_int() {
    return (intptr_t)arc4random();
}

int64_t ray_math_rand_int64() {
    return (int64_t)arc4random();
}
