#include <stdlib.h>
#include <string.h>
#include "externs.h"
#include "gc.h"
#include "hash.h"
#include "helpers.h"
#include "memory.h"
#include "rayarray.h"
#include "rayint.h"
#include "raystring.h"
#include "typeinfo.h"

ray_ty_path_t *__ray_array_path() {
    ray_ty_path_t *path = malloc(sizeof(ray_ty_path_t));
    path->name = "Array";
    path->scope = malloc(sizeof(char*));
    path->scope[0] = 0; // no scope
    path->module = malloc(sizeof(char*)*2);
    path->module[0] = strdup("stdlib");
    path->module[1] = 0;
    path->has_impl = 0;
    path->is_static = 0;
    return path;
}

uintptr_t **__ray_rawlist_add_segment(void *rawlist, int size) {
    int ptr = sizeof(uintptr_t*);
    uintptr_t **segment = (uintptr_t**)(rawlist + ptr);
    while (*segment != 0) {
        uintptr_t **next = segment + ptr;
        if (*next == 0) {
            *next = malloc((size + 2)*ptr);
            // set the size of the segment
            (*next)[0] = size;
            // set the value of the next segment address (0)
            (*next)[1] = 0;
            return next;
        }

        segment = next;
    }

    ray_panic("%s", "BUG: Could not find last segment.");
    return 0;
}

void *__ray_array_getraw(ray_object_t *obj) {
    return *(void**)RAY_FIELD(obj, "%%raw%%");
}

void ray_array_deinit(const char* _ti, ray_object_t* arr) {
    void *list_ptr = __ray_array_getraw(arr);
    uintptr_t *len = *(uintptr_t**)RAY_FIELD(arr, "%%length%%");

    // decref each array element
    for (int i = 0; i < *len; i++) {;
        ray_object_t **elptr = (ray_object_t**)ray_rawlist_getelptr(list_ptr, i);
        DECREF(*elptr);
    }

    // free the rawlist
    ray_rawlist_free(list_ptr);

    // free the length ptr
    free(len);

    // free the struct fields
    ray_rawlist_free(arr->value);

    // free the struct
    ray_struct_free(arr);
}

ray_object_t *ray_array_new(uintptr_t count, void *enc_ti, ray_bool_t is_raw) {
    // oversize the array; let's multiply it by 3
    uintptr_t length = count;
    if (length != 0) {
        count *= 3;
    } else {
        count = 3;
    }

    void *rawlist = ray_rawlist_new(count);

    uintptr_t *len_obj = malloc(sizeof(uintptr_t));
    *len_obj = length;

    ray_field_pair_t **fields = malloc(2*sizeof(ray_field_pair_t*));
    fields[0] = malloc(sizeof(ray_field_pair_t));
    fields[0]->key = "%%raw%%";
    fields[0]->value = rawlist;
    fields[1] = malloc(sizeof(ray_field_pair_t));
    fields[1]->key = "%%length%%";
    fields[1]->value = len_obj;

    void *fields_ptr = __ray_make_fields(fields, 2);
    char *ti;
    if (is_raw) {
        ti = (char*)enc_ti;
    } else {
        ti = ray_string_to_raw((ray_object_t*)enc_ti);
    }
    return __ray_make_struct(fields_ptr, ti, ray_array_deinit);
}

uintptr_t ray_array_len(ray_object_t *arr) {
    return **(uintptr_t**)RAY_FIELD(arr, "%%length%%");
}

ray_object_t *ray_array_init(const char* enc_ti) {
    // initializes an array of size 0 (which _new will "oversize" to 3)
    return ray_array_new(0, (void*)enc_ti, 1);
}

ray_object_t *ray_array_reserve(const char* enc_ti, uintptr_t count) {
    return ray_array_new(count, (void*)enc_ti, 1);
}

ray_object_t *ray_array_get(ray_object_t *arr, intptr_t idx) {
    INCREF(arr);
    void *rawlist = __ray_array_getraw(arr);
    ray_object_t *value = *(ray_object_t**)ray_rawlist_getelptr(rawlist, idx);
    DECREF(arr);
    return value;
}

void ray_array_set(ray_object_t *arr, intptr_t idx, ray_object_t *value) {
    INCREF(arr, value);
    void *rawlist = __ray_array_getraw(arr);
    ray_rawlist_set(rawlist, idx, value);
    DECREF(arr);
}

void ray_array_append(ray_object_t *arr, ray_object_t *value) {
    INCREF(arr, value);
    void *rawlist = __ray_array_getraw(arr);
    uintptr_t len = ray_array_len(arr);
    uintptr_t rawlist_size = ray_rawlist_len(rawlist);
    if (len + 1 > rawlist_size) {
        // add segment
        __ray_rawlist_add_segment(rawlist, len*3);
    }

    ray_rawlist_set(rawlist, len, value);
    DECREF(arr);
}
