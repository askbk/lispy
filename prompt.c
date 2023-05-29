#include <stdio.h>
#include <stdlib.h>

#include <editline.h>
#include "vendor/mpc.h"

long eval_op(char* op, long x, long y) {
  if (strcmp(op, "+") == 0)
    return x + y;
  if (strcmp(op, "-") == 0)
    return x - y;
  if (strcmp(op, "/") == 0)
    return x / y;
  if (strcmp(op, "*") == 0)
    return x * y;

  return 0;
}

long eval(mpc_ast_t* ast) {
  if (strstr(ast->tag, "number")) {
    return atoi(ast->contents);
  }

  char* op = ast->children[1]->contents;

  long x = eval(ast->children[2]);

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
      printf("%li\n", eval(result.output));
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