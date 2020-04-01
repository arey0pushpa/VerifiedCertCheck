/*
 This file is part of QRPcheck.

 QRPcheck, a proof checker for Q-Resolution Proofs in QRP format.
 Copyright (c) 2011, 2012 Aina Niemetz.

 QRPcheck is free software: you can redistribute it and/or modify
 it under the terms of the GNU General Public License as published by
 the Free Software Foundation, either version 3 of the License, or (at
 your option) any later version.

 QRPcheck is distributed in the hope that it will be useful, but
 WITHOUT ANY WARRANTY; without even the implied warranty of
 MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 General Public License for more details.

 You should have received a copy of the GNU General Public License
 along with QRPcheck.  If not, see <http://www.gnu.org/licenses/>.
*/

#ifndef INCLUDE_QRPC_H
#define INCLUDE_QRPC_H

typedef int Lit;
typedef unsigned int VarId;
typedef unsigned int StepId;
typedef unsigned int ClauseId;

typedef char byte_t;

#define SUCCESS 0
#define ERROR 1

#define QRPC_ABORT(cond, msg, ...)                \
  if (cond) {                                     \
    fprintf(stderr, "[QRPcheck] %s: ", __func__); \
    fprintf(stderr, msg, ##__VA_ARGS__);          \
    fprintf(stderr, "\n");                        \
    cleanup();                                    \
    abort();                                      \
  }

#define QRPC_ABORT_PARSER(cond, msg, ...)                                \
  if (cond) {                                                            \
    fprintf(stderr, "[QRPcheck] %s:%d:%d: ", p.filename, p.line, p.col); \
    fprintf(stderr, msg, ##__VA_ARGS__);                                 \
    fprintf(stderr, "\n");                                               \
    cleanup();                                                           \
    abort();                                                             \
  }

#define QRPC_REALLOC(a, old_size, new_size)                                  \
  do {                                                                       \
    a = (typeof(a))realloc(a, (new_size) * sizeof(typeof(*a)));              \
    QRPC_ABORT(a == NULL, "memory (re)allocation failed");                   \
    if ((unsigned int)(new_size) > (old_size))                               \
      memset(a + old_size, 0, (new_size - (old_size)) * sizeof(typeof(*a))); \
  } while (0)

/* ------------------------------------------------------------------------ */

#define NONE 0
#define POS 1
#define NEG 2
#define DCP 3  /* don't care, but must be pos */
#define DCN 4  /* don't care, but must be neg */
#define DCPN 5 /* don't care, can be both, don't care if neg or pos occ */

#define DELETED 1

#define GET_MARK(vid) (mark_occs[vid] & 7)
#define SET_MARK(vid, ant, mark) mark_occs[vid] = ((mark) | ((ant) << 3))
#define GET_ANT_MARK(vid) ((mark_occs[vid] & 8) >> 3)

#define PRINT_MARK(vid)                     \
  do {                                      \
    fprintf(stderr, "%d [", vars[vid].idx); \
    switch (GET_MARK(vid)) {                \
      case POS:                             \
        fprintf(stderr, "POS");             \
        break;                              \
      case NEG:                             \
        fprintf(stderr, "NEG");             \
        break;                              \
      case DCN:                             \
        fprintf(stderr, "DCN");             \
        break;                              \
      case DCP:                             \
        fprintf(stderr, "DCP");             \
        break;                              \
      case DCPN:                            \
        fprintf(stderr, "DCPN");            \
        break;                              \
      default:                              \
        fprintf(stderr, "NONE");            \
    }                                       \
    fprintf(stderr, "] ");                  \
  } while (0)

/* ------------------------------------------------------------------------ */

#define STACK_SIZE 100

#define STACK_DECLARE(type) \
  typedef struct {          \
    unsigned long size;     \
    type *bp;               \
    type *sp;               \
  } type##Stack;

#define STACK_INIT(stack, stack_size)                            \
  do {                                                           \
    QRPC_ABORT(stack_size <= 0, "invalid stack size");           \
    stack.size = stack_size;                                     \
    stack.bp = malloc(stack.size * sizeof(typeof(*stack.bp)));   \
    QRPC_ABORT(stack.bp == NULL, "memory allocation failed");    \
    memset(stack.bp, 0, stack.size * sizeof(typeof(*stack.bp))); \
    stack.sp = stack.bp;                                         \
  } while (0)

#define PUSH(stack, num)                                          \
  do {                                                            \
    *stack.sp = num;                                              \
    stack.sp += 1;                                                \
    if ((unsigned int)(stack.sp - stack.bp) >= stack.size) {      \
      stack.size <<= 1;                                           \
      stack.bp = (typeof(stack.bp))realloc(                       \
          stack.bp, stack.size * sizeof(typeof(*stack.bp)));      \
      QRPC_ABORT(stack.bp == NULL, "memory reallocation failed"); \
      stack.sp = stack.bp + (stack.size >> 1);                    \
    }                                                             \
  } while (0)

#define STACK_RESET(stack) (stack.sp = stack.bp)

#define STACK_RELEASE(stack)              \
  do {                                    \
    if (stack.bp != NULL) free(stack.bp); \
    stack.bp = NULL;                      \
  } while (0)

STACK_DECLARE(VarId);
STACK_DECLARE(StepId);
STACK_DECLARE(Lit);

/* ------------------------------------------------------------------------ */

typedef enum { QTYPE_UNDEF, QTYPE_EXISTS, QTYPE_FORALL } QType;

typedef enum { QRPTYPE_UNDEF, QRPTYPE_SAT, QRPTYPE_UNSAT } QRPType;

typedef struct {
  VarId id;  /* internal index */
  VarId idx; /* original index as given by input */
  QType type;
  int s_level; /* scope level */
  int num_pos_occs;
  int num_neg_occs;
  ClauseId *pos_occs;
  ClauseId *neg_occs;
} Var;

typedef struct {
  ClauseId id;
  int num_lits;
  int s_level;
  char *lits;
  byte_t is_sat : 1;
  byte_t is_taut : 1;
} Clause;

typedef struct {
  StepId id;  /* internal index */
  StepId idx; /* original index as given by input */
  byte_t visited : 1;
  byte_t is_initial : 1; /* either orig. clause or initial cube */
  int num_lits;
  int num_ants;
  int s_level_sat;   /* scope level of innermost a var */
  int s_level_unsat; /* scope level of innermost e var */
  char *lits;
  StepId ants[2];
} Step;

typedef struct {
  byte_t verbosity;
  byte_t is_bqrp : 1;
  byte_t print_proof : 1;
  byte_t print_proof_only : 1;
  byte_t print_statistics : 1;
  byte_t check_icubes : 1;
} QRPCOptions;

/* ------------------------------------------------------------------------ */

#define TIMER_CPU(time) time = get_cpu_time() - time;

#define TIMER_WC(time) time = get_wc_time() - time;

#define STATS(msg, ...) fprintf(stderr, msg, ##__VA_ARGS__);

#define STATS_HR                                           \
  do {                                                     \
    fprintf(stderr, "----------------------------------"); \
    fprintf(stderr, "----------------------------------"); \
    fprintf(stderr, "\n");                                 \
  } while (0)

#define STATS_MEM(factor, unit) \
  do {                          \
    if (size > mib) {           \
      factor = mib;             \
      unit = smib;              \
    } else if (size > kib) {    \
      factor = kib;             \
      unit = skib;              \
    } else {                    \
      factor = 1;               \
      unit = sb;                \
    }                           \
  } while (0)

typedef struct {
  unsigned int num_vars;
  unsigned int num_free_vars;
  unsigned int num_steps_total;
  unsigned int num_steps_initial;
  unsigned int num_steps_initial_full; /* full assignment */
  unsigned int num_steps_red;
  unsigned int num_steps_res;
  unsigned long long num_literals;
  unsigned long long num_literals_core;
  unsigned long long num_literals_initial;
  unsigned int num_steps_total_core;
  unsigned int num_steps_red_core;
  unsigned int num_steps_res_core;
  unsigned int num_step_ref_total;

  double time_cpu_total;    /* cpu time (kernel and user mode) */
  double time_cpu_pqrp;     /* parse qrp */
  double time_cpu_pqdimacs; /* parse qdimcas */
  double time_cpu_cqrp;     /* check qrp */
  double time_cpu_cicubes;  /* check initial cubes */
  double time_wc_total;     /* wall clock time */
  double time_wc_pqrp;      /* parse qrp */
  double time_wc_pqdimacs;  /* parse qdimcas */
  double time_wc_cqrp;      /* check qrp */
  double time_wc_cicubes;   /* check initial cubes */

  unsigned int size_vars;
  unsigned int size_vidx2id;
  unsigned int size_mark_occs;
  unsigned int size_steps;
  unsigned int size_sidx2id;
  unsigned int size_clauses;
  unsigned int size_occurrences;
  unsigned int size_stack_occs;
  unsigned int size_stack_universals;
  unsigned int size_stack_initial_cubes;
  unsigned int size_stack_res_lits;
  unsigned int num_realloc_vidx2id;
  unsigned int num_realloc_vars;
  unsigned int num_realloc_mark_occs;
  unsigned int num_realloc_sidx2id;
  unsigned int num_realloc_steps;
  unsigned int num_realloc_clauses;
  unsigned int num_realloc_occurrences;
  unsigned int num_realloc_stack_occs;
  unsigned int num_realloc_stack_universals;
  unsigned int num_realloc_stack_initial_cubes;
  unsigned int num_realloc_stack_res_lits;
} QRPCStatistics;

/* -------------------------------- Parser -------------------------------- */

#define QDIMACS 0
#define QRP_ASCII 1
#define QRP_BINARY 2

#define QRP_COMMENT '#'
#define QRP_PREAMBLE 'p'
#define QRP_EOL '0'
#define QRP_RESULT 'r'
#define QRP_FORALL 'a'
#define QRP_EXISTS 'e'

#define BQRP_EOL 0

#define QDIMACS_COMMENT 'c'
#define QDIMACS_PREAMBLE 'p'
#define QDIMACS_EOL '0'
#define QDIMACS_FORALL 'a'
#define QDIMACS_EXISTS 'e'

#define MINUS '-'
#define EOL 0

#define READ_CHAR             \
  do {                        \
    if (p.pos == p.in_size) { \
      ch = EOF;               \
      break;                  \
    }                         \
    ch = p.in[p.pos++];       \
    p.col += 1;               \
  } while (0);

#define SKIP_SPACE_WHILE \
  while (isspace(ch)) {  \
    READ_CHAR;           \
    if (ch == '\n') {    \
      p.line += 1;       \
      p.col = 0;         \
    }                    \
  }

#define SKIP_SPACE_DO_WHILE \
  do {                      \
    READ_CHAR;              \
    if (ch == '\n') {       \
      p.line += 1;          \
      p.col = 0;            \
    }                       \
  } while (isspace(ch))

#define SKIP_SPACE_WHILE_IF(cond) \
  if (cond) SKIP_SPACE_WHILE;

#define SKIP_SPACE_DO_WHILE_IF(cond) \
  if (cond) SKIP_SPACE_DO_WHILE;

typedef struct {
  byte_t is_qrp;
  char *filename;
  char *in;
  long in_size;
  long pos;
  int line;
  int col;
  int (*read_number)(void);
  int (*read_literal)(void);
} QRPCParser;

/* ---------------------------- end Parser -------------------------------- */

#endif
