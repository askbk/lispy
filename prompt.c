#include <stdio.h>
#include <stdlib.h>

#include <editline.h>
#include "vendor/mpc.h"

enum lval_type { LVAL_NUM, LVAL_ERR };
enum lval_error { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

struct lval {
  long num;
  enum lval_type type;
  enum lval_error err;
};

struct lval lval_num(long x) {
  struct lval v = {
      .num = x,
      .type = LVAL_NUM,
  };
  return v;
}

struct lval lval_err(enum lval_error e) {
  struct lval v = {
      .err = e,
      .type = LVAL_ERR,
  };
  return v;
}

void lval_print(struct lval v) {
  if (v.type == LVAL_ERR) {
    switch (v.err) {
      case LERR_BAD_NUM:
        puts("Error: Bad number!");
        break;

      case LERR_BAD_OP:
        puts("Error: Bad operator!");
        break;

      case LERR_DIV_ZERO:
        puts("Error: Division by zero!");
        break;

      default:
        break;
    }
  }

  if (v.type == LVAL_NUM) {
    printf("%li", v.num);
  }

  return;
}

void lval_println(struct lval v) {
  lval_print(v);
  putchar('\n');
}

struct lval eval_op(char* op, struct lval x, struct lval y) {
  if (x.type == LVAL_ERR) return x;
  if (y.type == LVAL_ERR) return y;

  if (strcmp(op, "+") == 0) return lval_num(x.num + y.num);
  if (strcmp(op, "-") == 0) return lval_num(x.num - y.num);
  if (strcmp(op, "*") == 0) return lval_num(x.num * y.num);
  if (strcmp(op, "/") == 0)
    return y.num == 0 ? lval_err(LERR_DIV_ZERO) : lval_num(x.num / y.num);

  return lval_err(LERR_BAD_OP);
}

struct lval eval(mpc_ast_t* ast) {
  if (strstr(ast->tag, "number")) {
    errno = 0;
    long n = strtol(ast->contents, NULL, 10);
    return errno == ERANGE ? lval_err(LERR_BAD_NUM) : lval_num(n);
  }

  char* op = ast->children[1]->contents;

  struct lval x = eval(ast->children[2]);

  for (int i = 3; i < ast->children_num - 1; ++i) {
    x = eval_op(op, x, eval(ast->children[i]));
  }

  return x;
}

int main(void) {
  mpc_parser_t* Operator = mpc_new("operator");
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Expr = mpc_new("expr");
  mpc_parser_t* Lispy = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
            "                                         \
    number  : /-?[0-9]+/                            ; \
    operator: /[+-\\/*]/                            ; \
    expr    : <number> | '(' <operator> <expr>+ ')' ; \
    lispy   : /^/ <operator> <expr>+ /$/            ; \
    ",
            Number, Operator, Expr, Lispy);

  puts("Ctrl-C to exit");

  while (1) {
    char* input = readline("CLISP> ");

    mpc_result_t result;

    if (mpc_parse("<stdin>", input, Lispy, &result)) {
      lval_println(eval(result.output));
      mpc_ast_delete(result.output);
    } else {
      mpc_err_print(result.error);
      mpc_err_delete(result.error);
    }

    add_history(input);

    free(input);
  }

  mpc_cleanup(4, Number, Operator, Expr, Lispy);
  return 0;
}