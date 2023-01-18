#include <stdbool.h>
#include <stdlib.h>
#include <string.h>

unsigned int max(unsigned int a, unsigned int b) {
  if (a <= b)
    return b;
  return a;
}

struct list {
  int shift;
  char *line;
  struct list *tail;
} typedef list;

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
  result->height = 0;
  result->first_line_width = 0;
  result->middle_width = 0;
  result->last_line_width = 0;
  result->to_text = NULL;
  return result;
}

t *line(char *nt) {
  t *result = malloc(sizeof(struct t));
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
  if (G->height == 0) {
//    memccpy(result, F, sizeof(t), 1);
    return F;
  } else if (F->height == 0) {
//    memccpy(result, G, sizeof(t), 1);
    return G;
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

    list *to_text_new = G->to_text;
    list *to_text_new_tail = to_text_new;
    while(to_text_new_tail->tail != NULL) {
      to_text_new_tail = to_text_new_tail->tail;
    }
    to_text_new_tail->tail = malloc(sizeof(struct list));
    to_text_new_tail->tail->shift = 0;
    to_text_new_tail->tail->line = newline;
    to_text_new_tail->tail->tail = F->to_text;

    t *result = malloc(sizeof(struct t));
    result->height = G->height + F->height;
    result->first_line_width = G->first_line_width;
    result->middle_width = middle_width_new;
    result->last_line_width = F->last_line_width;
    result->to_text = to_text_new;

    return result;
  }
}

t *add_beside(t *G, t *F) {
  t *result = malloc(sizeof(t));
  if (G->height == 0) {
    memccpy(result, F, sizeof(t), 1);
  } else if (F->height == 0) {
    memccpy(result, G, sizeof(t), 1);
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

    result->height = G->height + F->height - 1;
    result->first_line_width = first_line_width_new;
    result->middle_width = middle_width_new;
    result->last_line_width = G->last_line_width + F->last_line_width;
//  result->to_text =
  }
  return result;
}

t *add_fill(t *G, t *F, unsigned int shift) {
  t *result = malloc(sizeof(t));
  if (G->height == 0) {
    memccpy(result, F, sizeof(t), 1);
  } else if (F->height == 0) {
    memccpy(result, G, sizeof(t), 1);
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

    result->height = G->height + F->height - 1;
    result->first_line_width = first_line_width_new;
    result->middle_width = middle_width_new;
    result->last_line_width = last_line_width_new;
//  result->to_text =
  }
  return result;
}

//char *to_string(t *f) {
//
//}

unsigned int total_width(t *f) {
  return max(f->first_line_width, max(f->middle_width, f->last_line_width));
}

t *indent(t *f, unsigned int shift) {
  t *result = malloc(sizeof(t));
  result->height = f->height;
  result->first_line_width = f->first_line_width + shift;
  result->middle_width = f->middle_width + shift;
  result->last_line_width = f->last_line_width + shift;
//  result->to_text =
  return result;
}