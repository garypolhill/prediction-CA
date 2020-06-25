/* asynchCA.c
 *
 * Program to run a 1D (elementary) CA asynchronously to get the distribution
 * of zeros and ones in each cell after each time step
 */

#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

/******************************************************************************
 * types
 */

typedef struct __state {
  unsigned char *cell;
} state_t;

typedef struct __step {
  state_t *state;
  struct __step *tail;
} step_t;

/******************************************************************************
 * globals
 */

int n_cell;
int n_cell_factorial;
int rule;
int *schedule;
unsigned long long ram;
double secs;

/******************************************************************************
 * procedure declarations
 */

state_t *run_ca(state_t *state, int *sched, int sync);
unsigned char ca_state(unsigned char l, unsigned char c, unsigned char r);
void print_step(int t, step_t *step);
double *p1(step_t *step);
step_t *next_step(step_t *prev, int sync);
state_t *new_state(void);
step_t *push_step(state_t *state, step_t *step);
void free_step(step_t *step);
int *start(void);
int next(int **ordering, int *i);
int *reorder(int *items, int n, int i);
void print_reorder(void);

/******************************************************************************
 * procedure definitions
 */

/* main()
 *
 * Main function
 */

int main(int argc, char *argv[]) {
  int t_max;
  int i, t;
  int opt_end;
  int test_ordering = 0;
  int test_synchrony = 0;
  int randomize = 0;
  state_t *state0;
  step_t *step0;
  step_t *stepT;

  /* process command line options
   */
  opt_end = 0;
  while(opt_end + 1 < argc && argv[opt_end + 1][0] == '-') {
    opt_end++;
    if(strcmp(argv[opt_end], "--test-ordering") == 0) {
      test_ordering = 1;
    }
    else if(strcmp(argv[opt_end], "--synchrony") == 0) {
      test_synchrony = 1;
    }
    else if(strcmp(argv[opt_end], "--randomize") == 0) {
      randomize = 1;
      srand((unsigned)time(NULL) ^ (unsigned)getpid());
    }
    else {
      fprintf(stderr, "Unrecognized option %s\n", argv[opt_end]);
    }
  }

  if(argc != opt_end + 4) {
    fprintf(stderr, "Usage: %s [--test-ordering] [--synchrony] [--randomize]"
	    " <init_state> <t_max> <rule>\n", argv[0]);
    exit(1);
  }

  if(randomize) {
    n_cell = atoi(argv[opt_end + 1]);
  }
  else {
    n_cell = strlen(argv[opt_end + 1]);
  }
  t_max = atoi(argv[opt_end + 2]);
  rule = atoi(argv[opt_end + 3]);

  /* compute n_cell! to save time
   */
  n_cell_factorial = 1;
  for(i = 2; i <= n_cell; i++) {
    n_cell_factorial *= i;
  }

  /* initialize the schedule (it's just an array of size n_cell 0,1,...,n-1)
   */
  schedule = start();

  /* test that the ordering works -- this is activated by the --test-ordering
   * command-line option and it outputs all the possible orderings of the
   * schedule array
   */
  if(test_ordering) {
    print_reorder();
    free(schedule);
    return 0;
  }

  /* output CSV headers
   */
  printf("step,bytes,secs");
  for(i = 1; i <= n_cell; i++) {
    printf(",cell.%d.p1", i);
  }
  printf("\n");

  /* set up the initial state and print it
   */
  ram = (unsigned long long)0;
  secs = 0.0;
  
  state0 = new_state();
  for(i = 0; i < n_cell; i++) {
    if(randomize) {
      state0->cell[i] = (unsigned char)(rand() > rand() ? 0 : 1);
    }
    else {
      state0->cell[i] = (unsigned char)(argv[opt_end + 1][i] == '0' ? 0 : 1);
    }
  }
  step0 = push_step(state0, NULL);
  print_step(0, step0);
  
  stepT = step0;		/* for some reason I thought the
				   initial state should be saved */

  /* run the simulation
   */

  for(t = 1; t <= t_max; t++) {
    step_t *stepTp1;
    clock_t start_time;
    
    ram = (unsigned long long)0;
    start_time = clock();
    
    stepTp1 = next_step(stepT, test_synchrony);

    secs = (double)(clock() - start_time) / (double)(CLOCKS_PER_SEC);

    if(t > 1) {
      free_step(stepT);
    }
    stepT = stepTp1;
    
    print_step(t, stepT);
  }

  /* free memory and exit
   */

  free_step(step0);
  free_step(stepT);
  free(schedule);

  return 0;
}

/* run_ca()
 *
 * run the CA asynchronously for one step using the specified schedule,
 * though synchrony is an option if sync is non-zero
 */

state_t *run_ca(state_t *state, int *sched, int sync) {
  state_t *nxt;
  int i;

  nxt = new_state();

  /* initialize the next state to '2' (to mean 'undefined')
   */
  for(i = 0; i < n_cell; i++) {
    nxt->cell[i] = (unsigned char)2;
  }
  
  /* compute the next state
   */
  for(i = 0; i < n_cell; i++) {
    int left_ix, left;
    int right_ix, right;

    /* implement 'wrap-around' -- the cell to the left of cell 0 is cell n - 1
     * and that to the right of cell n - 1 is cell 0, where the cell we are
     * trying to work out the left and right of is given by sched[i].
     */
    left_ix = (sched[i] == 0 ? n_cell - 1 : sched[i] - 1);
    right_ix = (sched[i] == (n_cell - 1) ? 0 : sched[i] + 1);

    /* get the states of the cells to the left and right, using values in the
     * 'next' state if they have been computed -- this simulates asynchrony
     */
    left = (sync || nxt->cell[left_ix] == (unsigned char)2
	    ? state->cell[left_ix]
	    : nxt->cell[left_ix]);
    right = (sync || nxt->cell[right_ix] == (unsigned char)2
	     ? state->cell[right_ix]
	     : nxt->cell[right_ix]);

    /* compute the next state of 'this' cell
     */
    nxt->cell[sched[i]] = ca_state(left, state->cell[sched[i]], right);
  }

  return nxt;
}

/* ca_state()
 *
 * Return the next state of a cell given the values of the cells to the left,
 * and right and the cell itself. This uses Wolfram coding to interpret the
 * (global) rule parameter
 */

unsigned char ca_state(unsigned char l, unsigned char c, unsigned char r) {
  int i;
  int bit;

  i = 0;
  if(l == (unsigned char)1) i += 4;
  if(c == (unsigned char)1) i += 2;
  if(r == (unsigned char)1) i += 1;

  bit = (1 << i);

  /* paranoia:
   */

  if(bit < 0 || bit > 255) {
    fprintf(stderr, "somehow bit is %d, outwith the range [0, 255]\n", i);
    exit(1);
  }

  /* compute the next state
   */
  if((rule & bit) > 0) {
    return (unsigned char)1;
  }
  else {
    return (unsigned char)0;
  }
}

/* print_step()
 *
 * Print a step in CSV format. Each step prints the proportion of times each
 * cell is in state 1.
 */

void print_step(int t, step_t *step) {
  double *ps;
  int i;

  printf("%d,%llu,%.15g", t, ram, secs);
  ps = p1(step);
  
  for(i = 0; i < n_cell; i++) {
    printf(",%.15g", ps[i]);
  }
  printf("\n");

  free(ps);
}

/* p1()
 *
 * Work through the step and compute the proportion of times each cell is in
 * state 1 across all the states in the step
 */

double *p1(step_t *step) {
  double *ps;
  double n;
  step_t *i;
  int j;

  ps = (double *)calloc(n_cell, sizeof(double));
  if(ps == NULL) {
    perror("Allocating proportions array");
    exit(1);
  }
  /* extreme paranoia given use of calloc() above
   */
  for(j = 0; j < n_cell; j++) {
    ps[j] = 0.0;
  }

  n = 0.0;
  for(i = step; i != NULL; i = i->tail) {
    n += 1.0;
    for(j = 0; j < n_cell; j++) {
      if(i->state->cell[j] == (unsigned char)1) {
	ps[j] += 1.0;
      }
    }
  }

  for(j = 0; j < n_cell; j++) {
    ps[j] /= n;
  }

  return ps;
}

/* next_step()
 *
 * Compute the next step -- each state in the previous step is run under each
 * possible schedule to create the states in the next step. There is the
 * option to run this synchronously if desired.
 */

step_t *next_step(step_t *prev, int sync) {
  step_t *nxt;
  step_t *i;

  nxt = NULL;

  for(i = prev; i != NULL; i = i->tail) {
    int j;
    int *sched;
    state_t *asynch_state;

    j = 0;
    if(sync) {
      next(&sched, &j);
    }
    else {
      while(next(&sched, &j)) {
        asynch_state = run_ca(i->state, sched, sync);

        nxt = push_step(asynch_state, nxt);
      }
    }
    asynch_state = run_ca(i->state, sched, sync);

    nxt = push_step(asynch_state, nxt);

    free(sched);
  }

  return nxt;
}

/* new_state()
 *
 * Return a newly allocated state
 */

state_t *new_state(void) {
  state_t *s;

  s = (state_t *)calloc(1, sizeof(state_t));
  if(s == NULL) {
    perror("Allocating a state");
    exit(1);
  }

  s->cell = (unsigned char *)calloc(n_cell, sizeof(unsigned char));
  if(s->cell == NULL) {
    perror("Allocating cells array");
    exit(1);
  }

  ram += (unsigned long long)(sizeof(state_t)
			      + (n_cell * sizeof(unsigned char)));
  return s;
}

/* push_step()
 *
 * Add a state to the front of the step_t list, returning the new front
 */

step_t *push_step(state_t *state, step_t *step) {
  step_t *s;

  if(state == NULL) {
    fprintf(stderr, "ERROR! state is NULL\n");
    exit(1);
  }

  s = (step_t *)calloc(1, sizeof(step_t));
  if(s == NULL) {
    perror("Allocating a step item");
    exit(1);
  }

  s->state = state;
  s->tail = step;

  ram += (unsigned long long)sizeof(step_t);
  return s;
}

/* free_step()
 *
 * Free all the memory allocated for a step
 */

void free_step(step_t *step) {
  step_t *i, *j;

  j = NULL;
  for(i = step; i != NULL; i = j) {
    free(i->state);
    j = i->tail;
    free(i);
  }
}

/* start()
 *
 * Return an initial schedule
 */

int *start(void) {
  int *sched;
  int i;

  sched = (int *)calloc(n_cell, sizeof(int));
  if(sched == NULL) {
    perror("Allocating schedule");
    exit(1);
  }
  for(i = 0; i < n_cell; i++) {
    sched[i] = i;
  }

  return sched;
}

/* next()
 *
 * Return the ith reordering of the schedule global variable and increment i
 * When i is n_cell! return 0 so the caller knows to stop
 */

int next(int **ordering, int *i) {
  int j;

  (*ordering) = reorder(schedule, n_cell, (*i));

  (*i)++;
  return (*i) != n_cell_factorial;
}

/* reorder()
 *
 * Return the ith reordering of n items
 */

int *reorder(int *items, int n, int i) {
  int *result;
  int *sub_result;
  int j, k;

  result = (int *)calloc(n, sizeof(int));
  if(result == NULL) {
    perror("Allocating schedule reordering");
    exit(1);
  }
  
  if(n == 1) {
    result[0] = items[0];
    return result;
  }

  j = i % n;

  sub_result = reorder(items, n - 1, i / n);

  for(k = 0; k < n; k++) {
    if(k < j) {
      result[k] = sub_result[k];
    }
    else if(k > j) {
      result[k] = sub_result[k - 1];
    }
    else {
      result[k] = items[n - 1];
    }
  }

  free(sub_result);
  return result;
}

/* print_reorder()
 * 
 * Provides a basis on which the reorder() function can be tested. Using the
 * --test-ordering commandline option, main() calls this function to print
 * all the orderings. reorder() works if (shell-like syntax):
 *
 * nonunique=`./asynchCA --test-ordering <args> | wc -l`
 * unique=`./asynchCA --test-ordering <args> | sort -u | wc -l`
 * test $nonunique -eq $unique
 *
 * # ...and $nonunique eq strlen args[0] factorial
 */

void print_reorder(void) {
  int i, j;
  int *sched;

  i = 0;
  while(next(&sched, &i)) {
    for(j = 0; j < n_cell; j++) {
      printf("%d ", sched[j]);
    }
    printf("\n");
  }
  for(j = 0; j < n_cell; j++) {
    printf("%d ", sched[j]);
  }
  printf("\n");
  free(sched);
}
  
