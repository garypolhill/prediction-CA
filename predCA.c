/* predCA.c
 *
 * Program to run a 1D (elementary) CA synchronously and work out the 
 * predictability.
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
#define N_RULE 256
#define RANDOM_PROB(P) (((double)rand() / (double)RAND_MAX) < ((double)(P)))
#define CELL1_STR "1"
#define CELL0_STR "0"
#define DATA1_STR "3"
#define DATA0_STR "2"
#define INVAR_STR "4"
#define ASYMM_STR "6"
#define SYMM_STR  "7"

typedef struct __state {
  int *data;
} state_t;

typedef struct __step {
  state_t *state;
  int rule;
  struct __step *tail;
} step_t;

typedef struct __predictablity {
  int n_invar;
  int n_asymm;
  int n_symm;
} pred_t;

/******************************************************************************
 * globals
 */

int n_cell;
int n_cell_arr;
int real_rule;
unsigned long long ram;
double secs;
int rule_errors[N_RULE];

/******************************************************************************
 * procedure declarations
 */

int get_cell(state_t *state, int i);
void set_cell(state_t *state, int i, int value);
state_t *run_ca(state_t *state, int rule);
void print_state(state_t *state, state_t *data);
int ca_stat(int l, int c, int r, int f);
void print_step(FILE *fp, int t, step_t *step);
pred_t predictability(step_t *step);
int *n_10(step_t *step);
void print_pred(step_t *step);
int step_len(step_t *step);
step_t *next_step(step_t *prev);
state_t *new_state(void);
state_t *data_state(int n_data, double p_data);
step_t *next_data_step(step_t *prev, state_t *data, int init, int *errs);
int get_error(state_t *s, state_t *d, state_t *is_d);
int n_rule(int *errs);
step_t *push_step(state_t *state, step_t *step, int rule);
void free_step(step_t *step);

/******************************************************************************
 * procedure definitions
 */

/* main()
 *
 * Main function
 */

int main(int argc, char *argv[]) {
  int t_pred;
  int i, t;
  int opt_end;
  int t_run_in = 0;
  int t_data = 1;
  int show_run_in = 0;
  int show_data = 0;
  int show_pred = 0;
  int data_max = 0;
  FILE *fp = stdout;
  double random_start = -1.0;
  double random_data = 1.0;
  int n_errors = 0;
  state_t *state0;
  state_t *stateD;
  step_t **stepT;

  srand((unsigned)time(NULL) ^ (unsigned)getpid());
  
  /* process command line options
   */
  opt_end = 0;
  while(opt_end + 1 < argc && argv[opt_end + 1][0] == '-') {
    opt_end++;
    if(strcmp(argv[opt_end], "--random-start") == 0 && argc > opt_end + 1) {
      opt_end++;
      random_start = atof(argv[opt_end]);
    }
    else if(strcmp(argv[opt_end], "--show-run-in") == 0) {
      show_run_in = 1;
    }
    else if(strcmp(argv[opt_end], "--show-data") == 0) {
      show_data = 1;
    }
    else if(strcmp(argv[opt_end], "--show-pred") == 0) {
      show_pred = 1;
    }
    else if(strcmp(argv[opt_end], "--write-csv") == 0 && argc > opt_end + 1) {
      opt_end++;
      fp = fopen(argv[opt_end], "w");
      if(fp == NULL) {
	perror(argv[opt_end]);
	exit(1);
      }
    }
    else if(strcmp(argv[opt_end], "--t-run-in") == 0 && argc > opt_end + 1) {
      opt_end++;
      t_run_in = atoi(argv[opt_end]);
    }
    else if(strcmp(argv[opt_end], "--t-data") == 0 && argc > opt_end + 1) {
      opt_end++;
      t_data = atoi(argv[opt_end]);
    }
    else if(strcmp(argv[opt_end], "--random-data") == 0 && argc > opt_end + 1) {
      opt_end++;
      random_data = atof(argv[opt_end]);
    }
    else if(strcmp(argv[opt_end], "--data-max") == 0 && argc > opt_end + 1) {
      opt_end++;
      data_max = atoi(argv[opt_end]);
    }
    else if(strcmp(argv[opt_end], "--n-errors") == 0 && argc > opt_end + 1) {
      opt_end++;
      n_errors = atoi(argv[opt_end]);
    }
    else {
      fprintf(stderr, "Unrecognized option %s\n", argv[opt_end]);
    }
  }

  if(argc != opt_end + 4) {
    fprintf(stderr, "Usage: %s [--random-start <P(1)>] [--show-run-in] "
	    "[--show-data] [--show-pred] [--write-csv <file>] "
	    "[--t-run-in <steps>] [--t-data <steps>] [--random-data <P(data)>] "
	    "[--data-max <cell>] [--n-errors <error>] <init_state> <t_pred> "
	    "<real_rule>\n", argv[0]);
    exit(1);
  }

  if(random_start != -1.0) {
    n_cell = atoi(argv[opt_end + 1]);
  }
  else {
    n_cell = strlen(argv[opt_end + 1]);
  }
  n_cell_arr = (n_cell / sizeof(int)) + (n_cell % sizeof(int) ? 0 : 1);
  t_pred = atoi(argv[opt_end + 2]);
  real_rule = atoi(argv[opt_end + 3]);

  /* set up the initial state
   */
  ram = (unsigned long long)0;
  secs = 0.0;
  
  state0 = new_state();
  for(i = 0; i < n_cell; i++) {
    if(random_start != -1.0) {
      set_cell(state0, i, (RANDOM_PROB(random_start) ? 1 : 0));
    }
    else {
      set_cell(state0, i, (argv[opt_end + 1][i] == '0' ? 0 : 1));
    }
  }

  /* set up the initial state
   */

  stepT = (step_t **)calloc(t_data + 2, sizeof(step_t *));
  stepT[0] = push_step(state0, NULL, real_rule);
  for(t = 1; t <= t_run_in; t++) {
    if(show_run_in) print_state(stepT[0]->state, NULL);
    stepT[0] = next_step(stepT[0]);
  }
  if(show_run_in) print_state(stepT[0]->state, NULL);
  
  /* output CSV headers
   */
  fprintf(fp, "step,bytes,secs,n.rule,n.invariable,n.asymmetric,n.symmetric\n");

  /* initialize rule_errors
   */

  for(i = 0; i < N_RULE; i++) {
    rule_errors[i] = n_errors;
  }
  
  /* set up the data 'state'
   */

  stateD = data_state(data_max, random_data);
  for(t = 1; t <= t_data; t++) {
    clock_t start_time;

    ram = (unsigned long long)0;
    start_time = clock();

    stepT[t] = next_data_step(stepT[t - 1], stateD, t == 1, rule_errors);

    secs = (double)(clock() - start_time) / (double)(CLOCKS_PER_SEC);

    if(show_data) print_state(stepT[t]->state, stateD);
    print_step(fp, t - t_data, stepT[t]);

    if(random_data < 1.0) {
      free(stateD);
      stateD = data_state(data_max, random_data);
    }
  }

  /* run the simulation
   */

  for(t = 1; t <= t_pred; t++) {
    clock_t start_time;
    
    ram = (unsigned long long)0;
    start_time = clock();
    
    stepT[t_data + 1] = next_step(stepT[t_data + (t == 1 ? 0 : 1)]);

    secs = (double)(clock() - start_time) / (double)(CLOCKS_PER_SEC);

    if(show_pred) print_pred(stepT[t_data + 1]);
    print_step(fp, t, stepT[t_data + 1]);
  }

  /* free memory and exit
   */

  for(t = 0; t <= t_data + 1; t++) {
    free_step(stepT[t]);
  }
  free(stepT);
  free(stateD);

  if(fp != stdout) {
    fclose(fp);
  }

  return 0;
}

/* get_cell()
 *
 * Return the setting of a cell as 1 or 0
 */

int get_cell(state_t *state, int i) {
  int j;
  int k;
  
  if(i < -1 || i > n_cell) {
    fprintf(stderr, "Attempt to get cell %d of state with %d cells\n",
	    i, n_cell);
    exit(1);
  }
  if(i == -1) i = n_cell - 1;
  else if(i == n_cell) i = 0;

  j = i / sizeof(int);
  k = (1 << (i % sizeof(int)));

  return (state->data[j] & k) ? 1 : 0;
}

/* set_cell()
 *
 * Set a cell to 1 or 0
 */

void set_cell(state_t *state, int i, int value) {
  int j;
  int k;

  if(value == 0) return;

  if(i < -1 || i > n_cell) {
    fprintf(stderr, "Attempt to set cell %d of state with %d cells\n",
	    i, n_cell);
    exit(1);
  }
  if(i == -1) i = n_cell - 1;
  else if(i == n_cell) i = 0;

  j = i / sizeof(int);
  k = (1 << (i % sizeof(int)));

  state->data[j] |= k;
}

/* print_state()
 *
 * Print a state
 */

void print_state(state_t *state, state_t *data) {
  int i;

  for(i = 0; i < n_cell; i++) {
    int v;
    int d = -1;

    v = get_cell(state, i);
    if(data != NULL) d = get_cell(data, i);

    if(i > 0) printf(" ");
    if(d > 0) printf(v ? DATA1_STR : DATA0_STR);
    else printf(v ? CELL1_STR : CELL0_STR);
  }
  printf("\n");
}

/* run_ca()
 *
 * run the CA synchronously for one step using the specified schedule,
 * though synchrony is an option if sync is non-zero
 */

state_t *run_ca(state_t *state, int rule) {
  state_t *nxt;
  int i;

  nxt = new_state();
  
  /* compute the next state
   */
  for(i = 0; i < n_cell; i++) {
    int left;
    int right;

    left = get_cell(state, i - 1);
    right = get_cell(state, i + 1);

    /* compute the next state of 'this' cell
     */
    set_cell(nxt, i, ca_stat(left, get_cell(state, i), right, rule));
  }

  return nxt;
}

/* ca_stat()
 *
 * Return the next state of a cell given the values of the cells to the left,
 * and right and the cell itself. This uses Wolfram coding to interpret the
 * (global) rule parameter
 */

int ca_stat(int l, int c, int r, int f) {
  int i;
  int bit;

  i = 0;
  if(l == 1) i += 4;
  if(c == 1) i += 2;
  if(r == 1) i += 1;

  bit = (1 << i);

  /* paranoia:
   */

  if(bit < 0 || bit > 255) {
    fprintf(stderr, "somehow bit is %d, outwith the range [0, 255]\n", i);
    exit(1);
  }

  /* compute the next state
   */
  if((f & bit) > 0) {
    return 1;
  }
  else {
    return 0;
  }
}

/* print_step()
 *
 * Print a step in CSV format. Each step prints the proportion of times each
 * cell is in state 1.
 */

void print_step(FILE *fp, int t, step_t *step) {
  int i;
  pred_t pred;

  pred = predictability(step);
  fprintf(fp, "%d,%llu,%.15g,%d,%d,%d,%d\n", t, ram, secs, n_rule(rule_errors),
	  pred.n_invar, pred.n_asymm, pred.n_symm);
}

/* predictability()
 *
 * Return the predictability of a step
 */

pred_t predictability(step_t *step) {
  pred_t pred;
  int i;
  int *n10;

  pred.n_invar = 0;
  pred.n_asymm = 0;
  pred.n_symm = 0;

  n10 = n_10(step);

  for(i = 0; i < n_cell; i++) {    
    if(n10[i] == 0 || n10[n_cell + i] == 0) pred.n_invar++;
    else if(n10[i] == n10[n_cell + i]) pred.n_symm++;
    else pred.n_asymm++;
  }

  free(n10);

  return pred;
}

/* n_10()
 *
 * Count the number of ones and zeros across each rule in each cell, and return
 * the result as a one-dimensional array, with zeros from 0 to n_cell - 1 and
 * ones from n_cell to (2 * n_cell) - 1. This is done to make the result more
 * convenient to free.
 */

int *n_10(step_t *step) {
  int *n10;
  step_t *i;

  n10 = (int *)calloc(2 * n_cell, sizeof(int));

  for(i = step; i != NULL; i = i->tail) {
    int j;

    for(j = 0; j < n_cell; j++) {
      n10[(get_cell(i->state, j) * n_cell) + j]++;
    }
  }

  return n10;
}

/* print_pred()
 *
 * Print the predictability of each cell. 
 */

void print_pred(step_t *step) {
  int *n10;
  int i;

  n10 = n_10(step);

  for(i = 0; i < n_cell; i++) {
    if(i > 0) printf(" ");
    if(n10[i] == 0 || n10[i + n_cell] == 0) printf(INVAR_STR);
    else if(n10[i] == n10[i + n_cell]) printf(SYMM_STR);
    else printf(ASYMM_STR);
  }
  printf("\n");
  
  free(n10);
}

/* next_step()
 *
 * Compute the next step -- each state in the previous step is run under each
 * possible schedule to create the states in the next step. There is the
 * option to run this synchronously if desired.
 */

step_t *next_step(step_t *prev) {
  step_t *nxt;
  step_t *i;

  nxt = NULL;

  for(i = prev; i != NULL; i = i->tail) {
    state_t *state;

    state = run_ca(i->state, i->rule);

    nxt = push_step(state, nxt, i->rule);
  }

  return nxt;
}

/* next_data_step()
 *
 * Compute the next data step
 */

step_t *next_data_step(step_t *prev, state_t *data, int init, int *errs) {
  step_t *nxt;
  step_t *i;
  state_t *data_state;

  /* paranoia
   */
  if(prev == NULL) {
    fprintf(stderr, "prev is NULL!\n");
    exit(1);
  }
  if(prev->rule != real_rule) {
    fprintf(stderr, "prev->rule is %d not real_rule %d\n",
	    prev->rule, real_rule);
    exit(1);
  }
  
  i = prev;
  data_state = run_ca(i->state, i->rule);
  i = i->tail;
  nxt = NULL;

  if(init) {			/* Initial step -- add all other rules */
    int j;

    for(j = 0; j < N_RULE; j++) {
      state_t *state;

      if(j == prev->rule) continue;

      state = run_ca(prev->state, j);

      errs[j] -= get_error(state, data_state, data);

      if(errs[j] >= 0) nxt = push_step(state, nxt, j);
    }
  }
  else {
    while(i != NULL) {
      state_t *state;
      
      state = run_ca(i->state, i->rule);

      errs[i->rule] -= get_error(state, data_state, data);

      if(errs[i->rule] >= 0) nxt = push_step(state, nxt, i->rule);
      
      i = i->tail;
    }
  }

  /* keep the data state at the head of the list
   */
  nxt = push_step(data_state, nxt, prev->rule);

  return nxt;
}

/* get_error()
 *
 * Return the error of a state
 */

int get_error(state_t *s, state_t *d, state_t *is_d) {
  int i;
  int err;

  err = 0;
  for(i = 0; i < n_cell; i++) {
    if(get_cell(is_d, i) && get_cell(s, i) != get_cell(d, i)) {
      err++;
    }
  }
  return err;
}

/* n_rule()
 *
 * Return the number of rules that still have non-negative errors
 */

int n_rule(int *errs) {
  int i;
  int n;

  n = 0;
  for(i = 0; i < N_RULE; i++) {
    if(errs[i] >= 0) n++;
  }
  return n;
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

  s->data = (int *)calloc(n_cell_arr, sizeof(int));
  if(s->data == NULL) {
    perror("Allocating cells array");
    exit(1);
  }

  ram += (unsigned long long)(sizeof(state_t) + (n_cell_arr * sizeof(int)));
  return s;
}

/* data_state()
 *
 * Create a new data state array, which is 1 where a cell is a data cell,
 * and 0 where it isn't
 */

state_t *data_state(int n_data, double p_data) {
  state_t *s;
  int i;
  
  s = new_state();
  for(i = 0; i < n_cell; i++) {
    if((n_data == 0 || i < n_data) && RANDOM_PROB(p_data)) {
      set_cell(s, i, 1);
    }
    else {
      set_cell(s, i, 0);
    }
  }

  return s;
}

/* push_step()
 *
 * Add a state to the front of the step_t list, returning the new front
 */

step_t *push_step(state_t *state, step_t *step, int rule) {
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
  s->rule = rule;
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

