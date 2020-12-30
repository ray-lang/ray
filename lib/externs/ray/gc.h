#ifndef _GC_H
#define _GC_H

#include "structs.h"

void __ray_gc_decref(ray_object_t *obj);
void __ray_gc_incref(ray_object_t *obj);

void __ray_gc_decrefva(ray_object_t *obj, ...);
void __ray_gc_increfva(ray_object_t *obj, ...);

#define DECREF(obj, ...) __ray_gc_decrefva(obj, ##__VA_ARGS__)
#define INCREF(obj, ...) __ray_gc_increfva(obj, ##__VA_ARGS__)

#endif
