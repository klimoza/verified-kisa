#include <stdbool.h>
#include <stdlib.h>

size_t strlen(const char *str) {
  size_t i;
  for (i=0; ; i++)
    if (str[i]==0) return i;
}

char *strcpy(char *dest, const char *src) {
  size_t i;
  for(i = 0;; i++){
    char d = src[i];
    dest[i] = d;
    if(d == 0) return dest;
  }
}

char *strcat(char *dest, const char *src) {
  size_t i,j;
  for(i = 0;; i++){
    char d = dest[i];
    if(d == 0) break;
  }
  for(j = 0;; j++){
    char d = src[j];
    dest[i + j] = d;
    if(d == 0) return dest;
  }
}

unsigned int max(unsigned int a, unsigned int b) {
  if (a <= b)
    return b;
  return a;
}

struct list {
  size_t shift;
  char *line;
  struct list *tail;
} typedef list;

list *list_copy(list *l) {
  if (l == NULL)
    return NULL;

  list *new = malloc(sizeof(list));
  if(!new) exit(1);

  list *cur = new;
  list *l_cur = l;
  while(true) {
    cur->shift = l_cur->shift;
    cur->line = malloc(strlen(l_cur->line) + 1);
    if(!cur->line) exit(1);
    strcpy(cur->line, l_cur->line);
    cur->tail = NULL;

    if (l_cur->tail == NULL) {
      cur = NULL;
      break;
    }
    cur->tail = malloc(sizeof(list));
    if(!cur->tail) exit(1);
    cur = cur->tail;
    l_cur = l_cur->tail;
  }
  return new;
}

list* new_list() {
  list* result = malloc(sizeof(list));
  if(!result) exit(1);
  result->shift = 0;
  result->line = NULL;
  result->tail = NULL;
  return result;
}

char *sp(size_t n) {
  char *result = malloc(n + 1);
  if(!result) exit(1);
  char space = ' ';
  for (size_t i = 0; i < n; i++) {
    result[i] = space;
  }
  result[n] = 0;
  return result;
}

size_t get_applied_length(list *to_text, size_t shift, char* line) {
  if(to_text == NULL)
    return strlen(line);

  size_t total_length = to_text->shift + strlen(to_text->line);
  list* to_text_cpy = to_text->tail;
  total_length += strlen(line);
  while(to_text_cpy != NULL) {
    total_length += 1 + to_text_cpy->shift + shift + strlen(to_text_cpy->line);
    to_text_cpy = to_text_cpy->tail;
  }
  return total_length;
}

char* to_text_apply(list *to_text, size_t shift, char* line) {
  if(to_text == NULL)
    return line;

  size_t total_length = get_applied_length(to_text, shift, line);
  char* result = malloc(total_length + 1);
  strcpy(result, to_text->line);
  while(to_text != NULL) {
    strcat(result, sp(to_text->shift + shift));
    strcat(result, to_text->line);
    to_text = to_text->tail;
  }
  return result;
}

struct t {
  unsigned int height;
  unsigned int first_line_width;
  unsigned int middle_width;
  unsigned int last_line_width;
  list *to_text;
} typedef t;

bool less_components(t *G, t *F) {
  return G->height <= F->height && G->first_line_width <= F->first_line_width &&
         G->middle_width <= F->middle_width && G->last_line_width <= F->last_line_width;
}

bool is_less_than(t *G, t *F) {
  if (G->height != 1 && F->height == 1 || G->height == 1 && F->height != 1)
    return false;
  else
    return less_components(G, F);
}

t *empty() {
  t *result = malloc(sizeof(t));
  if(!result) exit(1);
  result->height = 0;
  result->first_line_width = 0;
  result->middle_width = 0;
  result->last_line_width = 0;
  result->to_text = NULL;
  return result;
}

t *line(char *nt) {
  t *result = malloc(sizeof(struct t));
  if(!result) exit(1);
  result->height = 1;
  result->first_line_width = strlen(nt);
  result->middle_width = strlen(nt);
  result->last_line_width = strlen(nt);
  result->to_text = malloc(sizeof(struct list));
  if(!result->to_text) exit(1);
  result->to_text->shift = 0;
  result->to_text->line = nt;
  result->to_text->tail = NULL;
  return result;
}

char *newline = "\n";

t* format_copy(t *G) {
  t* result = malloc(sizeof(t));
  if(!result) exit(1);
  result->height = G->height;
  result->first_line_width = G->first_line_width;
  result->middle_width = G->middle_width;
  result->last_line_width = G->last_line_width;
  result->to_text = list_copy(G->to_text);
  return result;
}

list* get_list_tail(list* l) {
  list* cur = l;
  while(cur->tail != NULL) {
    cur = cur->tail;
  }
  return cur;
}

list* list_concat(list *l1, list *l2) {
  list* l1_tail = get_list_tail(l1);
  l1_tail->tail = l2;
  return l1;
}

unsigned int mdw_add_above(t *G, t *F) {
  if(G->height == 0)
    return F->middle_width;
  if(F->height == 0)
    return G->middle_width;

  unsigned int middle_width_new;
  if (G->height == 1 && F->height == 1) {
    middle_width_new = G->first_line_width;
  } else if (G->height == 1 && F->height != 1) {
    middle_width_new = max(F->first_line_width, F->middle_width);
  } else if (G->height == 2 && F->height == 1) {
    middle_width_new = G->last_line_width;
  } else if (G->height != 1 && F->height == 1) {
    middle_width_new = max(G->last_line_width, G->middle_width);
  } else if (G->height == 2 && F->height != 1) {
    middle_width_new = max(G->last_line_width, max(F->first_line_width, F->middle_width));
  } else {
    middle_width_new = max(G->middle_width, max(G->last_line_width, max(F->first_line_width, F->middle_width)));
  }
  return middle_width_new;
}

list* to_text_add_above(t *G, t *F) {
  if(G->height == 0)
    return list_copy(F->to_text);
  if (F->height == 0)
    return list_copy(G->to_text);

  list* to_text_head = list_concat(list_copy(G->to_text), list_copy(F->to_text));
  return to_text_head;
}

t* add_above(t *G, t *F) {
  if (G->height == 0) {
    return format_copy(F);
  } 
  if (F->height == 0) {
    return format_copy(G);
  }

  t* result = malloc(sizeof(t));
  if(!result) exit(1);

  unsigned int middle_width_new = mdw_add_above(G, F);
  list *to_text_new = to_text_add_above(G, F);

  result->height = G->height + F->height;
  result->first_line_width = G->first_line_width;
  result->middle_width = middle_width_new;
  result->last_line_width = F->last_line_width;
  result->to_text = to_text_new;
  return result;
}

unsigned int mdw_add_beside(t *G, t *F) {
  if(G->height == 0)
    return F->middle_width;
  if(F->height == 0)
    return G->middle_width;

  unsigned int middle_width_new;
  if (G->height == 1 && F->height == 1) {
    middle_width_new = G->first_line_width + F->first_line_width;
  } else if(G->height == 1 && F->height == 2) {
    middle_width_new = G->first_line_width + F->first_line_width;
  } else if (F->height == 1) {
    middle_width_new = G->middle_width;
  } else if (G->height == 1) {
    middle_width_new = G->last_line_width + F->middle_width;
  } else if (G->height == 2) {
    middle_width_new = max(G->last_line_width + F->first_line_width, G->last_line_width + F->middle_width);
  } else {
    middle_width_new = max(G->middle_width,
                           max(G->last_line_width + F->first_line_width, G->last_line_width + F->middle_width));
  }
  return middle_width_new;
}

unsigned int flw_add_beside(t *G, t *F) {
  if(G->height == 0)
    return F->first_line_width;
  if(F->height == 0)
    return G->first_line_width;

  unsigned int first_line_width_new;
  if (G->height == 1)
    first_line_width_new = G->first_line_width + F->first_line_width;
  else
    first_line_width_new = G->first_line_width;
  return first_line_width_new;
}

char *line_concats(char *l1, size_t n, char *l2) {
  char *new_line = malloc(strlen(l1) + n + strlen(l2) + 1);
  if(!new_line) exit(1);
  new_line[0] = '\0';

  char *shifted = sp(n);
  new_line = strcat(new_line, l1);
  new_line = strcat(new_line, shifted);
  new_line = strcat(new_line, l2);
  free(l1);
  free(shifted);
  free(l2);
  return new_line;
}

list *shift_list(list *sigma, size_t n) {
  list *cur_sigma = sigma;
  while(cur_sigma != NULL) {
    cur_sigma->shift += n;
    cur_sigma = cur_sigma->tail;
  }
  return sigma;
}

list *to_text_add_beside(t *G, t *F) {
  if(G->height == 0)
    return list_copy(F->to_text);
  if (F->height == 0)
    return list_copy(G->to_text);
  list *head = list_copy(G->to_text);
  list *tail = get_list_tail(head);
  list *copy_F = list_copy(F->to_text);
  tail->line = line_concats(tail->line, copy_F->shift, copy_F->line);
  shift_list(copy_F->tail, G->last_line_width);
  tail->tail = copy_F->tail;
  free(copy_F);
  return head;
}

t *add_beside(t *G, t *F) {
  if (G->height == 0) {
    return format_copy(F);
  } 
  if (F->height == 0) {
    return format_copy(G);
  }

  t* result = malloc(sizeof(t));
  if(!result) exit(1);

  unsigned int middle_width_new = mdw_add_beside(G, F);
  unsigned int first_line_width_new = flw_add_beside(G, F);
  list *to_text_new = to_text_add_beside(G, F);

  result->height = G->height + F->height - 1;
  result->first_line_width = first_line_width_new;
  result->middle_width = middle_width_new;
  result->last_line_width = G->last_line_width + F->last_line_width;
  result->to_text = to_text_new;

  
  return result;
}

unsigned int mdw_add_fill(t *G, t *F, size_t shift) {
  if(G->height == 0)
    return F->middle_width;
  if(F->height == 0)
    return G->middle_width;

  unsigned int middle_width_new;
  if (G->height == 1 && F->height == 1) {
    middle_width_new = G->first_line_width + F->first_line_width;
  } else if(G->height == 1 && F->height == 2) {
    middle_width_new = G->first_line_width + F->first_line_width;
  } else if (G->height == 1) {
    middle_width_new = shift + F->middle_width;
  } else if (G->height == 2 && F->height == 1) {
    middle_width_new = G->first_line_width;
  } else if (G->height == 2 && F->height == 2) {
    middle_width_new = G->last_line_width + F->first_line_width;
  } else if (G->height == 2) {
    middle_width_new = max(G->last_line_width + F->first_line_width, shift + F->middle_width);
  } else if (F->height == 1) {
    middle_width_new = G->middle_width;
  } else if (F->height == 2) {
    middle_width_new = max(G->middle_width, G->last_line_width + F->first_line_width);
  } else {
    middle_width_new = max(G->middle_width, max(G->last_line_width + F->first_line_width, shift + F->middle_width));
  }
  return middle_width_new;
}

unsigned int llw_add_fill(t *G, t *F, size_t shift) {
  if(G->height == 0)
    return F->last_line_width;
  if(F->height == 0)
    return G->last_line_width;

  unsigned int last_line_width_new;
  if (F->height == 1)
    last_line_width_new = F->last_line_width + G->last_line_width;
  else
    last_line_width_new = F->last_line_width + shift;
  return last_line_width_new;
}

unsigned int flw_add_fill(t *G, t *F) {
  if(G->height == 0)
    return F->first_line_width;
  if(F->height == 0)
    return G->first_line_width;

  unsigned int first_line_width_new;
  if (G->height == 1)
    first_line_width_new = G->first_line_width + F->first_line_width;
  else
    first_line_width_new = G->first_line_width;
  return first_line_width_new;
}

list *to_text_add_fill(t *G, t *F, size_t shift) {
  if(G->height == 0)
    return list_copy(F->to_text);
  if (F->height == 0)
    return list_copy(G->to_text);
  list *head = list_copy(G->to_text);
  list *tail = get_list_tail(head);
  list *copy_F = list_copy(F->to_text);
  tail->line = line_concats(tail->line, copy_F->shift, copy_F->line);
  shift_list(copy_F->tail, shift);
  tail->tail = copy_F->tail;
  free(copy_F);
  return head;
}

t *add_fill(t *G, t *F, size_t shift) {
  if (G->height == 0) {
    return format_copy(F);
  } 
  if (F->height == 0) {
    return format_copy(G);
  }

  t* result = malloc(sizeof(t));
  if(!result) exit(1);

  unsigned int middle_width_new = mdw_add_fill(G, F, shift);
  unsigned int first_line_width_new = flw_add_fill(G, F);
  unsigned int last_line_width_new = llw_add_fill(G, F, shift);
  list *to_text_new = to_text_add_fill(G, F, shift);

  result->height = G->height + F->height - 1;
  result->first_line_width = first_line_width_new;
  result->middle_width = middle_width_new;
  result->last_line_width = last_line_width_new;
  result->to_text = to_text_new;
  
  return result;
}

char *to_string(t *f) {
  unsigned int total_length = 0;
  list *to_text = f->to_text;
  while(to_text != NULL) {
    total_length += strlen(to_text->line);
    total_length += to_text->shift;
    to_text = to_text->tail;
  }
  char *result = malloc(total_length + 1);
  if(!result) exit(1);
  to_text = f->to_text;
  while(to_text != NULL) {
    result = strcat(result, sp(to_text->shift));
    result = strcat(result, to_text->line);
    if(to_text -> tail != NULL) {
      result = strcat(result, newline);
    }
    to_text = to_text->tail;
  }
  return result;
}

unsigned int total_width(t *f) {
  return max(f->first_line_width, max(f->middle_width, f->last_line_width));
}

t *of_string(char* s) {
  // TODO
  return NULL;
}

t *indent(t *f, unsigned int shift) {
  t *result = malloc(sizeof(t));
  if(!result) exit(1);
  result->height = f->height;
  result->first_line_width = f->first_line_width + shift;
  result->middle_width = f->middle_width + shift;
  result->last_line_width = f->last_line_width + shift;

  list *to_text = f->to_text;
  while(to_text != NULL) {
    to_text->shift += shift;
    to_text = to_text->tail;
  }

  return result;
}

struct format_list {
  t* G;
  struct format_list *tail;
} typedef format_list;

void clear_to_text(list *l) {
  if(l == NULL)
    return;
  clear_to_text(l->tail);
  if(l->line != NULL)
    free(l->line);
  free(l);
}

void clear_format_list(format_list *fs) {
  if(fs == NULL)
    return;
  clear_format_list(fs->tail);
  if(fs->G != NULL) {
    clear_to_text(fs->G->to_text);
    free(fs->G);
  }
  free(fs);
}

bool max_width_check(t *G, unsigned int width, unsigned int height) {
  if(total_width(G) > width)
    return false;
  if(G->height > height)
    return false;
  return true;
}

format_list* beside_doc(unsigned int width, unsigned int height, format_list *fs1, format_list *fs2) {
  if (fs1 == NULL) {
    if (fs2 != NULL)
      clear_format_list(fs2);
    return NULL;
  }
  if (fs2 == NULL) {
    clear_format_list(fs1);
    return NULL;
  }

  format_list *result = malloc(sizeof(format_list));
  if(result == NULL) exit(1);
  result->G = empty();
  result->tail = NULL;
  format_list *result_tail = result;
  bool has_item = false;

  format_list *fs2_tail = fs2;
  while(fs2_tail != NULL) {
    format_list *fs1_tail = fs1;
    while(fs1_tail != NULL) {
      t* G = add_beside(fs1_tail->G, fs2_tail->G);
      if(max_width_check(G, width, height)) {
        clear_to_text(result_tail->G->to_text);
        free(result_tail->G);
        result_tail->G = G;
        result_tail->tail = malloc(sizeof(format_list));
        if(result_tail->tail == NULL) exit(1);
        result_tail->tail->G = empty();
        result_tail->tail->tail = NULL;
        result_tail = result_tail->tail;
        has_item = true;
      } else {
        clear_to_text(G->to_text);
        free(G);
      }
      fs1_tail = fs1_tail->tail;
    }
    fs2_tail = fs2_tail->tail;
  }
  
  clear_format_list(fs1);
  clear_format_list(fs2);
  if(!has_item) {
    clear_format_list(result);
    return NULL;
  }
  format_list *new_result_tail = result;
  while(new_result_tail->tail->tail != NULL) {
    new_result_tail = new_result_tail->tail;
  }
  clear_format_list(new_result_tail->tail);
  new_result_tail->tail = NULL;
  return result;
}