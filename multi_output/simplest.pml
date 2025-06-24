/* Standard defines */
#define NULL 0
#define TRUE 1
#define FALSE 0
#define MAX_SIZE 255

/* Global variables */
int counter = 0;
int results[5]; /* Promela doesn't support array initialization.  Will initialize in init process */

int global_var = 10;

/* Inline function for conditional assignment. Avoids labels. */
inline assign_global_var(condition) {
  if
  :: condition -> global_var = 1
  :: else -> global_var = 0
  fi
}

proctype main_process() {
  int a = 5;
  int b = 7;

  /* Simple operation */
  a = a + b;

  /* Simple conditional */
  assign_global_var(a > 10);

  printf("a: %d, global_var: %d\n", a, global_var)
}

init {
  int i;

  /* Array Initialization */
  for (i = 0; i < 5; i++) {
    results[i] = 0; // Initialize array elements
  };

  run main_process()
}