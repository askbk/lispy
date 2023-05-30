#include <stdio.h>
#include <stdlib.h>

#include <editline.h>
#include "vendor/mpc.h"

enum lval_type { LVAL_NUM, LVAL_ERR, LVAL_SYM, LVAL_SEXPR };

struct lval {
  enum lval_type type;
  long num;

  char* err;
  char* sym;

  int count;

  struct lval** cell;
};

struct lval* lval_num(long x) {
  struct lval* v = malloc(sizeof(struct lval));
  v->type = LVAL_NUM;
  v->num = x;

  return v;
}

struct lval* lval_err(char* m) {
  struct lval* v = malloc(sizeof(struct lval));
  v->type = LVAL_ERR;
  v->err = malloc(strlen(m) + 1);
  strcpy(v->err, m);

  return v;
}

struct lval* lval_sym(char* s) {
  struct lval* v = malloc(sizeof(struct lval));
  v->type = LVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);

  return v;
}

struct lval* lval_sexpr(void) {
  struct lval* v = malloc(sizeof(struct lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;

  return v;
}

void lval_del(struct lval* v) {
  switch (v->type) {
    case LVAL_NUM:
      break;
    case LVAL_ERR:
      free(v->err);
      break;
    case LVAL_SYM:
      free(v->sym);
      break;
    case LVAL_SEXPR:
      for (int i = 0; i < v->count; ++i) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
      break;
    default:
      break;
  }

  free(v);

  return;
}

struct lval* lval_read_num(mpc_ast_t* ast) {
  errno = 0;
  long n = strtol(ast->contents, NULL, 10);

  return errno == ERANGE ? lval_err("Invalid number") : lval_num(n);
}

struct lval* lval_add(struct lval* v, struct lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(struct lval) * v->count);
  v->cell[v->count - 1] = x;

  return v;
}

struct lval* lval_read(mpc_ast_t* ast) {
  if (strstr(ast->tag, "number")) return lval_read_num(ast);
  if (strstr(ast->tag, "symbol")) return lval_sym(ast->contents);

  struct lval* x = NULL;
  if (strcmp(ast->tag, ">") == 0) x = lval_sexpr();
  if (strstr(ast->tag, "sexpr")) x = lval_sexpr();

  for (int i = 0; i < ast->children_num; ++i) {
    if (strcmp(ast->children[i]->contents, "(") == 0) continue;
    if (strcmp(ast->children[i]->contents, ")") == 0) continue;
    if (strcmp(ast->children[i]->tag, "regex") == 0) continue;
    x = lval_add(x, lval_read(ast->children[i]));
  }

  return x;
}

void lval_print(struct lval* v);

void lval_sexpr_print(struct lval* v, char open, char close) {
  putchar(open);

  for (int i = 0; i < v->count; ++i) {
    lval_print(v->cell[i]);

    if (i != v->count - 1) putchar(' ');
  }

  putchar(close);
}

void lval_print(struct lval* v) {
  switch (v->type) {
    case LVAL_NUM:
      printf("%li", v->num);
      break;
    case LVAL_ERR:
      printf("Error: %s", v->err);
      break;
    case LVAL_SYM:
      printf("%s", v->sym);
      break;
    case LVAL_SEXPR:
      lval_sexpr_print(v, '(', ')');
      break;
    default:
      break;
  }

  return;
}

void lval_println(struct lval* v) {
  lval_print(v);
  putchar('\n');
}

struct lval* lval_pop(struct lval* v, int i) {
  struct lval* x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i + 1],
          sizeof(struct lval*) * (v->count - i - 1));

  --v->count;

  v->cell = realloc(v->cell, sizeof(struct lval*) * v->count);

  return x;
}

struct lval* lval_take(struct lval* v, int i) {
  struct lval* x = lval_pop(v, i);
  lval_del(v);

  return x;
}

struct lval* builtin_op(struct lval* a, char* op) {
  for (int i = 0; i < a->count; ++i) {
    if (a->cell[i]->type != LVAL_NUM) {
      lval_del(a);
      return lval_err("Not a number");
    }
  }

  struct lval* x = lval_pop(a, 0);

  if (a->count == 0 && strcmp(op, "-") == 0) x->num = -x->num;

  while (a->count > 0) {
    struct lval* y = lval_pop(a, 0);

    if (strcmp(op, "+") == 0) x->num += y->num;
    if (strcmp(op, "-") == 0) x->num -= y->num;
    if (strcmp(op, "*") == 0) x->num *= y->num;
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        x = lval_err("Division by zero.");
        break;
      };
      x->num /= y->num;
    }

    lval_del(y);
  }

  lval_del(a);

  return x;
}

struct lval* lval_eval(struct lval* v);
struct lval* lval_eval_sexpr(struct lval* v) {
  for (int i = 0; i < v->count; ++i) {
    v->cell[i] = lval_eval(v->cell[i]);
  }

  for (int i = 0; i < v->count; ++i) {
    if (v->cell[i]->type == LVAL_ERR) return v->cell[i];
  }

  if (v->count == 0) return v;
  if (v->count == 1) return lval_take(v, 0);

  struct lval* f = lval_pop(v, 0);

  if (f->type != LVAL_SYM) {
    lval_del(f);
    lval_del(v);
    return lval_err("S-expression does not start with a symbol!");
  }

  struct lval* result = builtin_op(v, f->sym);
  lval_del(f);

  return result;
}

struct lval* lval_eval(struct lval* v) {
  if (v->type == LVAL_SEXPR) return lval_eval_sexpr(v);

  return v;
}

int main(void) {
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Sexpr = mpc_new("sexpr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            "                                \
    number : /-?[0-9]+/                    ; \
    symbol : /[+-\\/*]/                    ; \
    sexpr  : '(' <expr>* ')'               ; \
    expr   : <number> | <symbol> | <sexpr> ; \
    lispy  : /^/ <expr>* /$/               ; \
    ",
            Number, Symbol, Expr, Lispy, Sexpr);

  puts("Ctrl-C to exit");

  while (1) {
    char* input = readline("CLISP> ");

    mpc_result_t result;

    if (mpc_parse("<stdin>", input, Lispy, &result)) {
      struct lval* x = lval_eval(lval_read(result.output));
      lval_println(x);
      lval_del(x);
      mpc_ast_delete(result.output);
    } else {
      mpc_err_print(result.error);
      mpc_err_delete(result.error);
    }

    add_history(input);

    free(input);
  }

  mpc_cleanup(5, Number, Symbol, Expr, Lispy, Sexpr);

  return 0;
}