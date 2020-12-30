#include <stdlib.h>
#include <string.h>
#include "gc.h"
#include "hash.h"
#include "memory.h"
#include "rayarray.h"
#include "rayint.h"
#include "raystring.h"
#include "raytuple.h"
#include "typeinfo.h"

typedef ray_object_t* (*to_string_t)(ray_object_t*);

ray_object_t *ray_tuple_init(const char *ti, uintptr_t count) {
    ray_tuple_t *tuple = malloc(sizeof(ray_tuple_t));
    tuple->len = count;
    tuple->elements = malloc(count * sizeof(ray_object_t*));
    return __ray_make_struct(tuple, ti, ray_tuple_deinit);
}

void ray_tuple_deinit(const char *_ti, ray_object_t *obj) {
    ray_tuple_t *tup = (ray_tuple_t*)obj->value;
    for (int i = 0; i < tup->len; i++) {
        DECREF(tup->elements[i]);
    }

    free(tup->elements);
    ray_struct_free(obj);
}

ray_object_t *ray_tuple_get(ray_object_t *obj, uint32_t idx) {
    ray_tuple_t *tup = (ray_tuple_t*)obj->value;
    return tup->elements[idx];
}

void ray_tuple_set(ray_object_t *obj, uint32_t idx, ray_object_t *val) {
    ray_tuple_t *tup = (ray_tuple_t*)obj->value;
    tup->elements[idx] = val;
}

ray_object_t *ray_tuple_len(ray_object_t *obj) {
    ray_tuple_t *tup = (ray_tuple_t *)obj->value;
    return ray_int_from_raw(tup->len);
}

ray_object_t *ray_tuple_to_string(ray_object_t *obj) {
    ray_tuple_t *tup = (ray_tuple_t *)obj->value;
    if (tup->len == 0) {
        return ray_string_from_raw("stdlib.String", "()");
    }

    return ray_string_from_raw("stdlib.String", "(...)");

    // uint32_t to_string_hash = ray_hash("stdlib.ToString$to_string");

    // size_t curr_size = 128;
    // char *str = malloc(curr_size * sizeof(char));
    // str[0] = '(';

    // int str_idx = 1;
    // for (int i = 0; i < tup->len; i++) {
    //     ray_object_t *elem = tup->elements[0];
    //     to_string_t to_string = (to_string_t)__ray_get_proto_method(elem, to_string_hash);
    //     ray_object_t *elem_str = to_string(elem);
    //     INCREF(elem_str);

    //     char *raw_str = ray_string_to_raw(elem_str);
    //     int raw_len = strlen(raw_str);

    //     for (int j = 0; j < raw_len; j++) {
    //         char c = raw_str[j];
    //         str[str_idx] = c;
    //         if (str_idx == curr_size - 1) {
    //             // realloc
    //             curr_size *= 2;
    //             str = realloc(str, curr_size * sizeof(char));
    //         }

    //         str_idx++;
    //     }

    //     DECREF(elem_str);
    //     free(raw_str);
    // }

    // if (str_idx >= curr_size - 2) {
    //     str = realloc(str, (curr_size + 2) * sizeof(char));
    // }

    // str[str_idx] = ')';
    // str[str_idx+1] = '\0';
    // ray_object_t *strobj = ray_string_from_raw("stdlib.String", str);
    // free(str);
    // return strobj;
}
