#include "hash.h"
#include "structs.h"
#include "typeinfo.h"

ray_object_t *__ray_cast(ray_object_t *obj, uint32_t to_ty_hash) {
    ray_ty_pair_t *pair = ray_decode_ty_info(obj->encoded_type);
    uint32_t from_ty_hash = ray_hash(pair->name);
    if (to_ty_hash == from_ty_hash || __ray_ty_implements(obj, to_ty_hash)) {
        return obj;
    }
    return 0;
}
