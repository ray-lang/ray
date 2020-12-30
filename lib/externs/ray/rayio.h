#ifndef _RAYIO_H
#define _RAYIO_H

#include "structs.h"

ray_object_t *ray_io_open(ray_object_t *path, ray_object_t *mode);
ray_object_t *ray_io_fputs(ray_object_t *fobj, ray_object_t *strobj);

extern ray_object_t *ray_file_init(ray_object_t *);

#endif
