#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>

#include <editline.h>
#include "vendor/mpc.h"

#define LASSERT(args, cond, fmt, ...)           \
  if (!(cond)) {                                \
    lval* err = lval_err((fmt), ##__VA_ARGS__); \
    lval_del(args);                             \
    return err;                                 \
  }

typedef struct lval lval;
typedef struct lenv lenv;
enum lval_type {
  LVAL_NUM,
  LVAL_ERR,
  LVAL_SYM,
  LVAL_SEXPR,
  LVAL_QEXPR,
  LVAL_FUN
};

char* ltype_name(enum lval_type t) {
  if (t == LVAL_NUM) return "Number";
  if (t == LVAL_ERR) return "Error";
  if (t == LVAL_SYM) return "Symbol";
  if (t == LVAL_SEXPR) return "S-expression";
  if (t == LVAL_QEXPR) return "Q-expression";
  if (t == LVAL_FUN) return "Function";

  return "Unknown";
}

typedef lval* (*lbuiltin)(lenv*, lval*);

struct lval {
  enum lval_type type;
  long num;

  char* err;
  char* sym;
  lbuiltin fun;

  int count;

  struct lval** cell;
};

lval* lval_copy(lval* v) {
  lval* c = malloc(sizeof(lval));
  c->type = v->type;

  if (v->type == LVAL_NUM) {
    c->num = v->num;
    return c;
  }

  if (v->type == LVAL_FUN) {
    c->fun = v->fun;
    return c;
  }

  if (v->type == LVAL_ERR) {
    c->err = malloc(strlen(v->err) + 1);
    strcpy(c->err, v->err);
    return c;
  }

  if (v->type == LVAL_SYM) {
    v->sym = malloc(strlen(v->sym) + 1);
    strcpy(c->sym, v->sym);
    return c;
  }

  if (v->type == LVAL_SEXPR || v->type == LVAL_QEXPR) {
    c->count = v->count;
    c->cell = malloc(sizeof(lval) * c->count);
    for (int i = 0; i < c->count; ++i) {
      c->cell[i] = lval_copy(v->cell[i]);
    }

    return c;
  }

  return c;
}

void lval_print(lval* v);

void lval_sexpr_print(lval* v, char open, char close) {
  putchar(open);

  for (int i = 0; i < v->count; ++i) {
    lval_print(v->cell[i]);

    if (i != v->count - 1) putchar(' ');
  }

  putchar(close);
}

void lval_print(lval* v) {
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
    case LVAL_QEXPR:
      lval_sexpr_print(v, '{', '}');
      break;
    case LVAL_FUN:
      printf("<function>");
      break;
    default:
      break;
  }

  return;
}

void lval_println(lval* v) {
  lval_print(v);
  putchar('\n');
}

struct lenv {
  int count;
  char** syms;
  lval** vals;
};

lenv* lenv_new(void) {
  lenv* e = malloc(sizeof(lenv));
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

void lval_del(lval* v) {
  switch (v->type) {
    case LVAL_NUM:
      break;
    case LVAL_ERR:
      free(v->err);
      break;
    case LVAL_SYM:
      free(v->sym);
      break;
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      for (int i = 0; i < v->count; ++i) {
        lval_del(v->cell[i]);
      }
      free(v->cell);
      break;
    case LVAL_FUN:
      break;
    default:
      break;
  }

  free(v);

  return;
}

// Adds a new entry to the environment e with symbol k->sym and value v
void lenv_put(lenv* e, lval* k, lval* v) {
  for (int i = 0; i < e->count; ++i) {
    if (strcmp(e->syms[i], k->sym) == 0) {
      lval_del(e->vals[i]);
      e->vals[i] = lval_copy(v);
      return;
    }
  }

  ++(e->count);
  e->vals = realloc(e->vals, sizeof(lval*) * e->count);
  e->syms = realloc(e->syms, sizeof(char*) * e->count);

  int last = e->count - 1;
  e->vals[last] = lval_copy(v);
  e->syms[last] = malloc(strlen(k->sym) + 1);
  strcpy(e->syms[last], k->sym);
}

void lenv_del(lenv* e) {
  for (int i = 0; i < e->count; ++i) {
    free(e->syms[i]);
    lval_del(e->vals[i]);
  }

  free(e->syms);
  free(e->vals);
  free(e);
}

lval* lval_num(long x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;

  return v;
}

lval* lval_err(char* fmt, ...) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;

  va_list va;
  va_start(va, fmt);

  v->err = malloc(512);

  vsnprintf(v->err, 511, fmt, va);

  v->err = realloc(v->err, strlen(v->err) + 1);

  va_end(va);

  return v;
}

lval* lenv_get(lenv* e, lval* k) {
  for (int i = 0; i < e->count; ++i) {
    if (strcmp(e->syms[i], k->sym) == 0) return lval_copy(e->vals[i]);
  }

  return lval_err("Unbound symbol '%s'!", k->sym);
}

lval* lval_sym(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);

  return v;
}

lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;

  return v;
}

lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;

  return v;
}

lval* lval_fun(lbuiltin func) {
  lval* f = malloc(sizeof(lval));
  f->type = LVAL_FUN;
  f->fun = func;

  return f;
}

lval* lval_read_num(mpc_ast_t* ast) {
  errno = 0;
  long n = strtol(ast->contents, NULL, 10);

  return errno == ERANGE ? lval_err("Invalid number") : lval_num(n);
}

lval* lval_add(lval* v, lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(lval) * v->count);
  v->cell[v->count - 1] = x;

  return v;
}

lval* lval_read(mpc_ast_t* ast) {
  if (strstr(ast->tag, "number")) return lval_read_num(ast);
  if (strstr(ast->tag, "symbol")) return lval_sym(ast->contents);

  lval* x = NULL;
  if (strcmp(ast->tag, ">") == 0) x = lval_sexpr();
  if (strstr(ast->tag, "sexpr")) x = lval_sexpr();
  if (strstr(ast->tag, "qexpr")) x = lval_qexpr();

  for (int i = 0; i < ast->children_num; ++i) {
    if (strcmp(ast->children[i]->contents, "(") == 0) continue;
    if (strcmp(ast->children[i]->contents, ")") == 0) continue;
    if (strcmp(ast->children[i]->contents, "{") == 0) continue;
    if (strcmp(ast->children[i]->contents, "}") == 0) continue;
    if (strcmp(ast->children[i]->tag, "regex") == 0) continue;
    x = lval_add(x, lval_read(ast->children[i]));
  }

  return x;
}

// Removes and returns child i of v without deleting v.
lval* lval_pop(lval* v, int i) {
  lval* x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i + 1], sizeof(lval*) * (v->count - i - 1));

  --v->count;

  v->cell = realloc(v->cell, sizeof(lval*) * v->count);

  return x;
}

// Removes and returns child i of v, deleting v.
lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);

  return x;
}
lval* lval_eval(lenv* e, lval* v);
lval* builtin_head(lenv* e, lval* v) {
  LASSERT(v, v->count == 1,
          "Function head must be called with one argument, received %i!",
          v->count);
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function head requires a Q-expression as its argument, received %s!",
          ltype_name(v->cell[0]->type));
  LASSERT(v, v->cell[1]->count > 0, "Function head received argument {}!");

  lval* list = lval_take(v, 0);
  lval* result = lval_qexpr();
  lval_add(result, lval_take(list, 0));

  return result;
}

lval* builtin_tail(lenv* e, lval* v) {
  LASSERT(v, v->count == 1, "Function tail must be called with one argument!");
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function tail requires a Q-expression as its argument!");
  LASSERT(v, v->cell[1]->count > 0, "Function tail received argument {}!");

  lval* list = lval_take(v, 0);

  lval_del(lval_pop(list, 0));

  return list;
}

lval* builtin_list(lenv* e, lval* v) {
  v->type = LVAL_QEXPR;
  return v;
}

lval* builtin_eval(lenv* e, lval* v) {
  LASSERT(v, v->count == 1, "Function eval only takes a single argument!");
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function eval only takes Q-expressions as argument!");
  lval* x = lval_take(v, 0);
  x->type = LVAL_SEXPR;

  return lval_eval(e, x);
}

lval* lval_join(lval* x, lval* y) {
  while (y->count) x = lval_add(x, lval_pop(y, 0));

  lval_del(y);

  return x;
}

lval* builtin_join(lenv* e, lval* v) {
  for (int i = 0; i < v->count; ++i) {
    LASSERT(v, v->cell[i]->type == LVAL_QEXPR,
            "All arguments passed to 'join' must be Q-expressions!");
  }

  lval* x = lval_pop(v, 0);

  while (v->count) x = lval_join(x, lval_pop(v, 0));

  lval_del(v);

  return x;
}

lval* builtin_def(lenv* e, lval* v) {
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "First argument to 'def' should be a Q-expression containing all "
          "symbols to bind!");

  lval* syms = v->cell[0];

  for (int i = 0; i < syms->count; ++i) {
    LASSERT(v, syms->cell[i]->type == LVAL_SYM,
            "Only symbols may be bound to values!");
  }

  LASSERT(v, syms->count == v->count - 1,
          "The number of symbols to bind should match the number of subsequent "
          "arguments to 'def'!");

  for (int i = 0; i < syms->count; ++i) {
    lenv_put(e, syms->cell[i], v->cell[i + 1]);
  }

  lval_del(v);

  return lval_sexpr();
}

lval* builtin_op(lenv* e, lval* a, char* op) {
  for (int i = 0; i < a->count; ++i) {
    if (a->cell[i]->type != LVAL_NUM) {
      printf("attempted to perform op %s on lval", op);
      lval_println(a);
      lval_del(a);
      return lval_err("Not a number");
    }
  }

  lval* x = lval_pop(a, 0);

  if (a->count == 0 && strcmp(op, "-") == 0) x->num = -x->num;

  while (a->count > 0) {
    lval* y = lval_pop(a, 0);

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

lval* builtin_add(lenv* e, lval* a) { return builtin_op(e, a, "+"); }
lval* builtin_sub(lenv* e, lval* a) { return builtin_op(e, a, "-"); }
lval* builtin_mul(lenv* e, lval* a) { return builtin_op(e, a, "*"); }
lval* builtin_div(lenv* e, lval* a) { return builtin_op(e, a, "/"); }

void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name);
  lval* f = lval_fun(func);
  lenv_put(e, k, f);
  lval_del(k);
  lval_del(f);
}

void lenv_add_builtins(lenv* e) {
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "head", builtin_head);
  lenv_add_builtin(e, "tail", builtin_tail);
  lenv_add_builtin(e, "join", builtin_join);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "def", builtin_def);
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);
}

lval* lval_eval_sexpr(lenv* e, lval* v) {
  lval_println(v);
  for (int i = 0; i < v->count; ++i) {
    v->cell[i] = lval_eval(e, v->cell[i]);
  }

  for (int i = 0; i < v->count; ++i) {
    if (v->cell[i]->type == LVAL_ERR) return lval_take(v, i);
  }

  if (v->count == 0) return v;
  if (v->count == 1) return lval_take(v, 0);

  lval* f = lval_pop(v, 0);

  if (f->type != LVAL_FUN) {
    lval_del(v);
    lval_del(f);
    return lval_err("First element of S-expression is not a function!");
  }

  lval* result = f->fun(e, v);
  lval_del(f);

  return result;
}

lval* lval_eval(lenv* e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval* x = lenv_get(e, v);
    lval_del(v);
    return x;
  }

  if (v->type == LVAL_SEXPR) return lval_eval_sexpr(e, v);

  return v;
}

int main(void) {
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Sexpr = mpc_new("sexpr");
  mpc_parser_t* Qexpr = mpc_new("qexpr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            "                                          \
    number : /-?[0-9]+/                              ; \
    symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&]+/        ; \
    sexpr  : '(' <expr>* ')'                         ; \
    qexpr  : '{' <expr>* '}'                         ; \
    expr   : <number> | <symbol> | <sexpr> | <qexpr> ; \
    lispy  : /^/ <expr>* /$/                         ; \
    ",
            Number, Symbol, Expr, Lispy, Sexpr, Qexpr);

  puts("Ctrl-C to exit");

  lenv* e = lenv_new();
  lenv_add_builtins(e);
  lval* test_expr = lval_sexpr();
  test_expr = lval_add(
      lval_add(lval_add(test_expr, lval_sym("+")), lval_num(1)), lval_num(2));
  lval* result = lval_eval(e, test_expr);
  lval_println(result);

  while (1) {
    char* input = readline("lispy> ");
    add_history(input);

    mpc_result_t result;
    if (mpc_parse("<stdin>", input, Lispy, &result)) {
      lval* x = lval_eval(e, lval_read(result.output));
      lval_println(x);
      lval_del(x);

      mpc_ast_delete(result.output);
    } else {
      mpc_err_print(result.error);
      mpc_err_delete(result.error);
    }

    free(input);
  }

  lenv_del(e);

  mpc_cleanup(6, Number, Symbol, Expr, Lispy, Sexpr, Qexpr);

  return 0;
}