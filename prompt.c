#include <stdio.h>
#include <stdlib.h>

#include <editline.h>
#include "vendor/mpc.h"

#define LASSERT(lval, cond, err) \
  if (!(cond)) {                 \
    lval_del(lval);              \
    return lval_err(err);        \
  }

enum lval_type { LVAL_NUM, LVAL_ERR, LVAL_SYM, LVAL_SEXPR, LVAL_QEXPR };

typedef struct lval {
  enum lval_type type;
  long num;

  char* err;
  char* sym;

  int count;

  struct lval** cell;
} lval;

lval* lval_num(long x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;

  return v;
}

lval* lval_err(char* m) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  v->err = malloc(strlen(m) + 1);
  strcpy(v->err, m);

  return v;
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
    default:
      break;
  }

  free(v);

  return;
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
    default:
      break;
  }

  return;
}

void lval_println(lval* v) {
  lval_print(v);
  putchar('\n');
}

// Returns child i of v without deleting v.
lval* lval_pop(lval* v, int i) {
  lval* x = v->cell[i];
  memmove(&v->cell[i], &v->cell[i + 1], sizeof(lval*) * (v->count - i - 1));

  --v->count;

  v->cell = realloc(v->cell, sizeof(lval*) * v->count);

  return x;
}

// Return child i of v and deletes v.
lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);

  return x;
}
lval* lval_eval(lval* v);
lval* builtin_head(lval* v) {
  LASSERT(v, v->count == 1, "Function head must be called with one argument!");
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function head requires a Q-expression as its argument!");
  LASSERT(v, v->cell[1]->count > 0, "Function head received argument {}!");

  lval* list = lval_take(v, 0);
  lval* result = lval_qexpr();
  lval_add(result, lval_take(list, 0));

  return result;
}

lval* builtin_tail(lval* v) {
  LASSERT(v, v->count == 1, "Function tail must be called with one argument!");
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function tail requires a Q-expression as its argument!");
  LASSERT(v, v->cell[1]->count > 0, "Function tail received argument {}!");

  lval* list = lval_take(v, 0);

  lval_del(lval_pop(list, 0));

  return list;
}

lval* builtin_list(lval* v) {
  v->type = LVAL_QEXPR;
  return v;
}

lval* builtin_eval(lval* v) {
  LASSERT(v, v->count == 1, "Function eval only takes a single argument!");
  LASSERT(v, v->cell[0]->type == LVAL_QEXPR,
          "Function eval only takes Q-expressions as argument!");
  lval* x = lval_take(v, 0);
  x->type = LVAL_SEXPR;

  return lval_eval(x);
}

lval* lval_join(lval* x, lval* y) {
  while (y->count) x = lval_add(x, lval_pop(y, 0));

  lval_del(y);

  return x;
}

lval* builtin_join(lval* v) {
  for (int i = 0; i < v->count; ++i) {
    LASSERT(v, v->cell[i]->type == LVAL_QEXPR,
            "All arguments passed to 'join' must be Q-expressions!");
  }

  lval* x = lval_pop(v, 0);

  while (v->count) x = lval_join(x, lval_pop(v, 0));

  lval_del(v);

  return x;
}

lval* builtin_op(lval* a, char* op) {
  for (int i = 0; i < a->count; ++i) {
    if (a->cell[i]->type != LVAL_NUM) {
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

lval* builtin(lval* a, char* func) {
  if (strcmp("list", func) == 0) return builtin_list(a);
  if (strcmp("head", func) == 0) return builtin_head(a);
  if (strcmp("tail", func) == 0) return builtin_tail(a);
  if (strcmp("join", func) == 0) return builtin_join(a);
  if (strcmp("eval", func) == 0) return builtin_eval(a);
  if (strstr("+-/*", func)) return builtin_op(a, func);
  lval_del(a);
  return lval_err("Unknown function!");
}

lval* lval_eval_sexpr(lval* v) {
  for (int i = 0; i < v->count; ++i) {
    v->cell[i] = lval_eval(v->cell[i]);
  }

  for (int i = 0; i < v->count; ++i) {
    if (v->cell[i]->type == LVAL_ERR) return v->cell[i];
  }

  if (v->count == 0) return v;
  if (v->count == 1) return lval_take(v, 0);

  lval* f = lval_pop(v, 0);

  if (f->type != LVAL_SYM) {
    lval_del(f);
    lval_del(v);
    return lval_err("S-expression does not start with a symbol!");
  }

  lval* result = builtin(v, f->sym);
  lval_del(f);

  return result;
}

lval* lval_eval(lval* v) {
  if (v->type == LVAL_SEXPR) return lval_eval_sexpr(v);

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
    symbol : '+' | '-' | '*' | '/' | \"list\"          \
             | \"head\"  | \"tail\"  | \"join\"        \
             | \"eval\"                              ; \
    sexpr  : '(' <expr>* ')'                         ; \
    qexpr  : '{' <expr>* '}'                         ; \
    expr   : <number> | <symbol> | <sexpr> | <qexpr> ; \
    lispy  : /^/ <expr>* /$/                         ; \
    ",
            Number, Symbol, Expr, Lispy, Sexpr, Qexpr);

  puts("Ctrl-C to exit");

  while (1) {
    char* input = readline("CLISP> ");

    mpc_result_t result;

    if (mpc_parse("<stdin>", input, Lispy, &result)) {
      lval* x = lval_eval(lval_read(result.output));
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

  mpc_cleanup(6, Number, Symbol, Expr, Lispy, Sexpr, Qexpr);

  return 0;
}