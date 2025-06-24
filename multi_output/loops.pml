/* Standard defines */
#define NULL 0
#define TRUE 1
#define FALSE 0
#define MAX_SIZE 255

/* Global variables */
int global_var = 10;

/* Loops Promela test file */

int counter = 0;
int results[5];

proctype main() {
  int i = 0;
  
  /* Simple for loop */
  i = 0;
  do
  :: i < 5 ->
     results[i] = i * 2;
     i++
  :: else ->
     break
  od;
  
  /* While loop */
  i = 0;
  do
  :: i < 5 ->
     counter = counter + results[i];
     i++
  :: else ->
     break
  od;
  
  /* Do-while loop */
  i = 5;
  do
  :: i > 0 ->
    counter = counter - 1;
    i--
  :: else ->
     break
  od;
  
  /* Loop with break */
  i = 0;
  do
  :: i < 10 ->
     if
     :: i > 5 ->
        break;
     :: else ->
        counter++
     fi;
     i++
  :: else ->
     break
  od;
  
  /* Loop with continue */
  i = 0;
  do
  :: i < 5 ->
    if
    :: (i % 2) == 0 ->
       goto next_iteration
    :: else ->
       counter = counter + 10
    fi;
next_iteration:
    i++
  :: else ->
     break
  od
}

init {
  run main()
}