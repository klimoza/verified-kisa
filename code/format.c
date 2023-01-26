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
  size_t i,j; char d;
  for(i = 0;; i++){
    d = dest[i];
    if(d == 0) break;
  }
  for(j = 0;; j++){
    d = src[j];
    dest[i + j] = d;
    if(d == 0) return dest;
  }
}

void *memcpy(void *dest, const void * src, size_t n) {
  size_t i;
  for(i = 0; i < n; i++){
    char d = ((char*)src)[i];
    ((char*)dest)[i] = d;
  }
  return dest;
}

unsigned int max(unsigned int a, unsigned int b) {
  if (a <= b)
    return b;
  return a;
}

struct list {
  unsigned int shift;
  char *line;
  struct list *tail;
} typedef list;

list *list_copy(list *l) {
  if (l == NULL)
    return NULL;

  list *new = malloc(sizeof(list));
  if(!new) exit(1);

  new->shift = l->shift;
  new->line = malloc(strlen(l->line) + 1);
  if(!new->line) exit(1);
  strcpy(new->line, l->line);
  new->tail = NULL;

  list *cur_tail = new;
  l = l->tail;
  while (l != NULL) {
    cur_tail->tail = malloc(sizeof(list));
    if(!cur_tail->tail) exit(1);

    cur_tail = cur_tail->tail;
    cur_tail->shift = l->shift;
    cur_tail->line = malloc(strlen(l->line) + 1);
    if(!cur_tail->line) exit(1);
    strcpy(cur_tail->line, l->line);
    cur_tail->tail = NULL;
    l = l->tail;
  }
  return new;
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
  result->to_text->shift = 0;
  result->to_text->line = nt;
  result->to_text->tail = NULL;
  return result;
}

char *newline = "\n";

char *sp(int n) {
  char *result = "";
  for (int i = 0; i < n; i++) {
    result = strcat(" ", result);
  }
  return result;
}


t *add_above(t *G, t *F) {
  t* result = malloc(sizeof(t));
  if(!result) exit(1);
  if (G->height == 0) {
    result = memcpy(result, F, sizeof(t));
  } else if (F->height == 0) {
    result = memcpy(result, G, sizeof(t));
  } else {
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

    list *to_text_new = list_copy(G->to_text);
    list *to_text_new_tail = to_text_new;
    while (to_text_new_tail->tail != NULL) {
      to_text_new_tail = to_text_new_tail->tail;
    }
    to_text_new_tail->tail = list_copy(F->to_text);

    result->height = G->height + F->height;
    result->first_line_width = G->first_line_width;
    result->middle_width = middle_width_new;
    result->last_line_width = F->last_line_width;
    result->to_text = to_text_new;
  }
  return result;
}

t *add_beside(t *G, t *F) {
  t* result = malloc(sizeof(t));
  if(!result) exit(1);
  if (G->height == 0) {
    result = memcpy(result, F, sizeof(t));
  } else if (F->height == 0) {
    result = memcpy(result, G, sizeof(t));
  } else {
    unsigned int middle_width_new;
    if (G->height == 1 && (F->height == 1 || F->height == 2)) {
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

    unsigned int first_line_width_new;
    if (G->height == 1)
      first_line_width_new = G->first_line_width + F->first_line_width;
    else
      first_line_width_new = G->first_line_width;

    list *to_text_new = list_copy(G->to_text);
    list *to_text_new_tail = to_text_new;
    while (to_text_new_tail->tail != NULL) {
      to_text_new_tail = to_text_new_tail->tail;
    }
    to_text_new_tail->line = realloc(to_text_new_tail->line, strlen(to_text_new_tail->line) + F->to_text->shift + strlen(F->to_text->line));
    to_text_new_tail->line = strcat(to_text_new_tail->line, sp(F->to_text->shift));
    to_text_new_tail->line = strcat(to_text_new_tail->line, F->to_text->line);
    to_text_new_tail->tail = list_copy(F->to_text->tail);
    to_text_new_tail = to_text_new_tail->tail;
    while(to_text_new_tail != NULL) {
      to_text_new_tail->shift += G->last_line_width;
      to_text_new_tail = to_text_new_tail->tail;
    }

    result->height = G->height + F->height - 1;
    result->first_line_width = first_line_width_new;
    result->middle_width = middle_width_new;
    result->last_line_width = G->last_line_width + F->last_line_width;
    result->to_text = to_text_new;

  }
  return result;
}

t *add_fill(t *G, t *F, unsigned int shift) {
  t *result = malloc(sizeof(t));
  if(!result) exit(1);
  if (G->height == 0) {
    memcpy(result, F, sizeof(t));
  } else if (F->height == 0) {
    memcpy(result, G, sizeof(t));
  } else {
    unsigned int middle_width_new;
    if (G->height == 1 && (F->height == 1 || F->height == 2)) {
      middle_width_new = G->first_line_width + F->first_line_width;
    } else if (G->height == 1) {
      middle_width_new = shift + G->middle_width;
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

    unsigned int first_line_width_new;
    if (G->height == 1)
      first_line_width_new = G->first_line_width + F->first_line_width;
    else
      first_line_width_new = G->first_line_width;

    unsigned int last_line_width_new;
    if (F->height == 1)
      last_line_width_new = F->last_line_width + G->last_line_width;
    else
      last_line_width_new = F->last_line_width + shift;

    list *to_text_new = list_copy(G->to_text);
    list *to_text_new_tail = to_text_new;
    while (to_text_new_tail->tail != NULL) {
      to_text_new_tail = to_text_new_tail->tail;
    }
    to_text_new_tail->line = realloc(to_text_new_tail->line, strlen(to_text_new_tail->line) + F->to_text->shift + strlen(F->to_text->line) + 1);
    to_text_new_tail->line = strcat(to_text_new_tail->line, sp(F->to_text->shift));
    to_text_new_tail->line = strcat(to_text_new_tail->line, F->to_text->line);
    to_text_new_tail->tail = list_copy(F->to_text->tail);
    to_text_new_tail = to_text_new_tail->tail;
    while(to_text_new_tail != NULL) {
      to_text_new_tail->shift += shift;
      to_text_new_tail = to_text_new_tail->tail;
    }

    result->height = G->height + F->height - 1;
    result->first_line_width = first_line_width_new;
    result->middle_width = middle_width_new;
    result->last_line_width = last_line_width_new;
    result->to_text = to_text_new;
  }
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