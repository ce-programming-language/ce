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

typedef struct {
    void* _ptr;
    int32_t _len;
    int32_t cap;
} ce_slice_t;

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
        case 6:
        case 7:
        case 8:
        case 9:
        case 10: {
            ce_slice_t* slice = (ce_slice_t*)val.data;
            intptr_t base_tag = tag - 5; 
            size_t elem_size = 0;
            
            if (base_tag == 1) elem_size = sizeof(int32_t);
            else if (base_tag == 2) elem_size = sizeof(double);
            else if (base_tag == 3) elem_size = sizeof(bool);
            else if (base_tag == 4) elem_size = sizeof(char*);
            else if (base_tag == 5) elem_size = sizeof(char);

            size_t cap = 128;
            result = (char*)GC_malloc(cap);
            strcpy(result, "[");

            for (int32_t i = 0; i < slice->_len; i++) {
                ce_any_t elem_any;
                elem_any.tag_or_vtable = (void*)base_tag;
                elem_any.data = (char*)slice->_ptr + (i * elem_size);
                char* elem_str = unsafe_format(&elem_any);
                size_t needed = strlen(result) + strlen(elem_str) + 6;
                if (needed > cap) {
                    while (cap < needed) cap *= 2;
                    char* new_result = (char*)GC_malloc(cap);
                    strcpy(new_result, result);
                    result = new_result;
                }
                
                if (base_tag == 4) strcat(result, "\"");
                else if (base_tag == 5) strcat(result, "'");
                
                strcat(result, elem_str);
                
                if (base_tag == 4) strcat(result, "\"");
                else if (base_tag == 5) strcat(result, "'");

                if (i < slice->_len - 1) strcat(result, ", ");
            }
            strcat(result, "]");
            return result;
        }
        default: { 
            snprintf(buffer, sizeof(buffer), "<unknown>");
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
