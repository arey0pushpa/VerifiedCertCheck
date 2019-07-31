/*  QRPcert: Tool for extracting QBF certificates from Q-resolution proofs. 
 *
 *  Copyright (c) 2011-2012 Mathias Preiner.
 *
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the GNU General Public License as published by
 *  the Free Software Foundation, either version 3 of the License, or
 *  (at your option) any later version.
 *  
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU General Public License for more details.
 *  
 *  You should have received a copy of the GNU General Public License
 *  along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */

#ifndef INCLUDE_QRPCERT_H 
#define INCLUDE_QRPCERT_H

#include <sys/unistd.h>
#include "simpleaig.h"

#define QRPCERT_PABORT(cond, msg, ...)                                      \
  do                                                                        \
  {                                                                         \
    if (cond)                                                               \
    {                                                                       \
      fprintf (stderr, "[QRPCERT] %s:%u:%u: ", reader.filename, reader.line,\
               reader.col);                                                 \
      fprintf (stderr, msg, ## __VA_ARGS__);                                \
      fprintf (stderr, "\n");                                               \
      if (options.out_filename != NULL)                                     \
        unlink (options.out_filename);                                      \
      cleanup ();                                                           \
      abort ();                                                             \
    }                                                                       \
  }                                                                         \
  while (0)

#define QRPCERT_ABORT(cond, msg, ...)                \
  do                                                 \
  {                                                  \
    if (cond)                                        \
    {                                                \
      fprintf (stderr, "[QRPCERT] %s: ", __func__);  \
      fprintf (stderr, msg, ## __VA_ARGS__);         \
      fprintf (stderr, "\n");                        \
      if (options.out_filename != NULL)              \
        unlink (options.out_filename);               \
      cleanup ();                                    \
      abort ();                                      \
    }                                                \
  }                                                  \
  while (0)

#define QRPCERT_REALLOC(a, new, old, mem_val)                             \
  do                                                                      \
  {                                                                       \
    a = (typeof (a)) realloc (a, (new) * sizeof (typeof (*a)));           \
    QRPCERT_ABORT (a == NULL, "memory reallocation failed");              \
    if ((unsigned) (new) > (old))                                         \
      memset (a + old, mem_val, ((new) - (old)) * sizeof (typeof (*a)));  \
  }                                                                       \
  while (0)

#define STACK_DECLARE(type) \
  typedef struct            \
  {                         \
    unsigned size;          \
    type *bp;               \
    type *sp;               \
  } type ## Stack;


#define STACK_INIT(stack, stack_size)                                  \
  do                                                                   \
  {                                                                    \
    QRPCERT_ABORT (stack_size == 0, "stack size has to be greater 0"); \
    (stack).bp = NULL;                                                 \
    QRPCERT_REALLOC ((stack).bp, stack_size, 0, 0);                    \
    (stack).sp = (stack).bp;                                           \
    (stack).size = stack_size;                                         \
  }                                                                    \
  while (0)

#define STACK_RESIZE_VALUE(size) ((size >> 2) + 1)

#define STACK_FREE(stack) \
  free ((stack).bp)

#define STACK_IS_EMPTY(stack) \
  ((stack).bp == (stack).sp)

#define STACK_RESET(stack) \
  ((stack).sp = (stack).bp)

#define STACK_CNT(stack) \
  ((unsigned) ((stack).sp - (stack).bp))

#define PUSH(stack, num)                                                \
  do                                                                    \
  {                                                                     \
    *((stack).sp) = num;                                                \
    (stack).sp += 1;                                                    \
    if ((unsigned) ((stack).sp - (stack).bp) >= (stack).size)           \
    {                                                                   \
      QRPCERT_REALLOC ((stack).bp,                                      \
                       (stack).size + STACK_RESIZE_VALUE((stack).size), \
                       (stack).size, 0);                                \
      (stack).sp = (stack).bp + (stack).size;                           \
      (stack).size += STACK_RESIZE_VALUE((stack).size);                 \
    }                                                                   \
  }                                                                     \
  while (0)

#define POP(stack, num)  \
  do                     \
  {                      \
    (stack).sp -= 1;     \
    num = *((stack).sp); \
    *((stack).sp) = 0;   \
  }                      \
  while(0)

#define STATS(s, val_format, ...) \
  fprintf (stderr, "  %-34s" val_format "\n", s ":", __VA_ARGS__)

#define XiB(byte) \
  ((byte < 1048576) ? (double) (byte) / 1024 : (double) (byte) / 1048576)

#define XiBSTR(byte) \
  ((byte < 1048576) ? "KiB" : "MiB")

#define TIMER(end, start) \
  do                      \
  {                       \
    t = get_time ();      \
    end = t - end;        \
    start = t;            \
  }                       \
  while (0)

#define REDUCTION_TYPE\
  ((proof_type == PTYPE_SAT) ? QTYPE_EXISTS : QTYPE_FORALL)

#define PIVOT_TYPE\
  ((proof_type == PTYPE_SAT) ? QTYPE_FORALL : QTYPE_EXISTS)

#define GET_INNERMOST_VAR(vertex_id)\
  ((proof_type == PTYPE_SAT) ? vertices[vertex_id].innermost_a \
                             : vertices[vertex_id].innermost_e)

#define QRP_COMMENT '#'
#define QRP_PREAMBLE 'p'
#define QRP_PREAMBLE_BQRP "bqrp"
#define QRP_PREAMBLE_QRP "qrp"
#define QRP_RESULT_S 's'
#define QRP_RESULT 'r'
#define QRP_RESULT_SAT "sat"
#define QRP_RESULT_U 'u'
#define QRP_RESULT_UNSAT "unsat"
#define QRP_FORALL 'a'
#define QRP_EXISTS 'e'
#define QRP_DELIM '0'
#define BQRP_DELIM 0
#define MINUS '-'

typedef int VarId;
typedef VarId Lit;
typedef int VertexId;

STACK_DECLARE (VarId);
STACK_DECLARE (VertexId);

typedef enum
{
  QTYPE_EXISTS = -1,
  QTYPE_UNDEF = 0,
  QTYPE_FORALL = 1
} QType;

typedef enum
{
  PTYPE_UNDEF,
  PTYPE_SAT,
  PTYPE_UNSAT
} PType;

typedef enum
{
  BTYPE_UNDEF,
  BTYPE_TRUE,
  BTYPE_FALSE
} BType;

typedef struct
{
  VarId id;
  QType type;
  BType val;
  unsigned s_level;
  VertexIdStack rfao_stack;
  char extract:1;
} Var; 

typedef struct
{
  VertexId id;
  BType val;
  char reduced:1;
  unsigned num_refs;
  unsigned num_pushed_refs;

  unsigned num_lits;
  unsigned num_lits_static;
  int aig_out;

  Lit *lits;
  unsigned lits_size;
  VarId innermost_e;
  VarId innermost_a;

  unsigned num_ants;
  VertexId ants[2];
} Vertex;

typedef struct
{
  char statistics:1;
  char simplify:1;
  char extract:1; 
  char aiger_binary:1;
  char print_rfao;
  char *out_filename;
  size_t incr_size;
  VarIdStack extract_vars;
} QRPCertOptions;

typedef struct
{
  unsigned num_ex_vars;
  unsigned num_un_vars;
  unsigned num_var_functions; 
  unsigned num_const_functions;
  unsigned num_dont_cares;
  unsigned size_rfaos;
  unsigned num_vertices_core;
  unsigned long long num_literals_core;
  unsigned long long num_reduced_literals;
  unsigned long long num_literals_compact;
  unsigned long long size_literals;
  unsigned long long size_literals_compact;
  unsigned long long num_ands_skipped;

  double time_parsing;
  double time_sort;
  double time_extract;
  double time_simplify;
  double time_mark;
  double time_compact;
  double time_generating;
  double time_writing;
  double time_total;
} QRPCertStatistics;

typedef struct
{
  unsigned line;
  unsigned col;
  char qrp_binary;
  int ch;
  int delim;
  unsigned num;
  Lit lit;
  int (*getch)(void);
  int (*getnextch)(void);
  unsigned (*getnum)(void);
  Lit (*getlit)(void);
  char *filename;
  char *mmap;
  size_t mmap_size;
  unsigned long mmap_pos;
} QRPReader;

static void cleanup (void);

/* parser  */
static void parse_qrp (void);
static void parse_preamble (VarId *, VertexId *);
static void parse_qsets (void);
static void parse_vertices (void);
static int get_non_ws_ch (void); 
static int stdin_getnextch (void);
static int mmap_getnextch (void);
static unsigned bqrp_read_num (void);
static Lit bqrp_read_lit (void);
static unsigned qrp_read_num (void);
static Lit qrp_read_lit (void);

/* extract functions  */
static void extract_functions (void);
static void collect_reduced_literals (VertexId, VertexId, QType);

/* simplify  */
static void simplify_functions (void);
static BType simplify_function (VarId); 
static BType simplify_vertex (VertexId, unsigned);
static BType eval_lit (Lit);

/* vertex  */
static inline void vertex_add_reduced_literal (VertexId, Lit);
static void vertex_add_antecedent (VertexId, VertexId);
static inline void vertex_remove_literal (VertexId, unsigned);
static inline unsigned vertex_literal_insert_pos (VertexId, Lit, int, int);
static void print_vertex (VertexId);

/* aig  */
static void aig_add_function (simpleaig *, VarId);
static int aig_add_vertex (simpleaig *, VertexId, VarId, char);
static void generate_aiger_certificate (simpleaig *);
static void generate_aiger_certificate_incremental (simpleaig *);

#ifndef NDEBUG
  static int assert_literals_sorted (void);
  static int assert_static_literals_sorted (void);
  static int assert_reduced_literals_sorted (void);
  static int assert_reduced_literals_type (void);
  static int assert_literals_simplified (void);
  static int assert_vertices_simplified (void);
#endif

#endif
