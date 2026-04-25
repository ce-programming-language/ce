#include <stdio.h>
#include <unistd.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>

extern void* GC_malloc(size_t size);

typedef struct {
    void* data;
    void* tag_or_vtable;
} ce_any_t;

char* unsafe_format(ce_any_t* val_ptr) {
    if (!val_ptr) {
        char* res = (char*)GC_malloc(6);
        strcpy(res, "<nil>");
        return res;
    }

    ce_any_t val = *val_ptr;
    intptr_t tag = (intptr_t)val.tag_or_vtable;
    char buffer[256];
    char* result = NULL;

    switch (tag) {
        case 1: {
            int32_t v = *(int32_t*)val.data;
            snprintf(buffer, sizeof(buffer), "%d", v);
            break;
        }
        case 2: {
            double v = *(double*)val.data;
            snprintf(buffer, sizeof(buffer), "%g", v);
            break;
        }
        case 3: {
            bool v = *(bool*)val.data;
            snprintf(buffer, sizeof(buffer), "%s", v ? "true" : "false");
            break;
        }
        case 4: {
            char* v = (char*)val.data; 
            if (!v) {
                snprintf(buffer, sizeof(buffer), "<nil>");
                break;
            }
            size_t len = strlen(v);
            result = (char*)GC_malloc(len + 1);
            strcpy(result, v);
            return result;
        }
        case 5: {
            char v = *(char*)val.data;
            snprintf(buffer, sizeof(buffer), "%c", v);
            break;
        }
        default: { 
            snprintf(buffer, sizeof(buffer), "<complex type or unknown>");
            break;
        }
    }

    if (!result) {
        size_t len = strlen(buffer);
        result = (char*)GC_malloc(len + 1);
        strcpy(result, buffer);
    }
    
    return result;
}
