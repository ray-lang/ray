#include <stdarg.h>
#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>
#include "gc.h"
#include "typeinfo.h"
#include "helpers.h"

void __ray_gc_decref(ray_object_t *obj) {
    if (obj == 0) {
        // do nothing; this is `nil`
        return;
    }

    ray_ty_pair_t *pair = ray_decode_ty_info(obj->encoded_type);
    if (obj->refcount == 0) {
        ray_panic("refcount is already 0 for value of type `%s`", pair->name);
    }

    if (obj->refcount == UINT32_MAX) {
        // we're in the process of de-initing
        ray_free_pair(pair);
        return;
    }

    obj->refcount--;
    if (obj->refcount == 0) {
        // set ref count to max uint32 (indicating we're in the middle of deinit)
        obj->refcount = UINT32_MAX;
        obj->deinit(obj->encoded_type, obj);
    }

    ray_free_pair(pair);
}

void __ray_gc_decrefva(ray_object_t *obj, ...) {
    va_list ap;
    va_start(ap, obj);
    do {
        __ray_gc_decref(obj);
        obj = va_arg(ap, ray_object_t*);
    } while (obj != 0);
    va_end(ap);
}

void __ray_gc_incref(ray_object_t *obj) {
    if (obj == 0) {
        return;
    }

    if (obj->refcount == UINT32_MAX) {
        // deiniting; do nothing
        return;
    }

    obj->refcount++;
}

void __ray_gc_increfva(ray_object_t *obj, ...) {
    va_list ap;
    va_start(ap, obj);
    do {
        __ray_gc_incref(obj);
        obj = va_arg(ap, ray_object_t*);
    } while (obj != 0);
    va_end(ap);
}
