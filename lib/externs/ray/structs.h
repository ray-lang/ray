#ifndef _STRUCTS_H
#define _STRUCTS_H

#include "raybool.h"
#include "typeinfo.h"

typedef struct ray_object_t {
    void *value;
    char *encoded_type;
    uint32_t refcount;
    void (*deinit)(const char*, struct ray_object_t*);
} ray_object_t;

typedef struct ray_field_pair_t {
    const char *key;
    void *value;
} ray_field_pair_t;

ray_object_t *__ray_make_struct(void *value, const char *enc_ty_info, void (*deinit)(const char*, ray_object_t*));
ray_object_t *ray_make_struct(void *value, const char *ti, void (*deinit)(const char*, ray_object_t*));
void ray_object_deinit(const char *ti, ray_object_t *obj);
void ray_struct_free(ray_object_t *obj);

ray_bool_t __ray_ty_implements(ray_object_t *obj, uint32_t ty_hash);
uintptr_t __ray_get_proto_method(ray_object_t *obj, uint32_t method_hash);

void __ray_make_struct_field(void *rawlist, const char *key, void *value, int field_idx);
void *__ray_make_fields(ray_field_pair_t **fields, uintptr_t field_count);
void *__ray_get_struct_field(ray_object_t *obj, uint32_t field_hash);

ray_object_t *ray_typestring(ray_object_t *obj);

#define RAY_FIELD(obj, field) __ray_get_struct_field(obj, ray_hash(field))

#endif
