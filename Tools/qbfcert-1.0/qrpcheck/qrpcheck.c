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

#include <stdlib.h>
#include <stdio.h>
#include <ctype.h>
#include <string.h>
#include <dirent.h>
#include <fcntl.h>
#include <assert.h>
#include <unistd.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/mman.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "qrpcheck.h"

#ifndef NPICOSAT
#include "picosat.h"
#endif

#define VERSION "QRPcheck-1.0.3"


static char ch;
static int num;
static byte_t neg;
static VarId vid;

static char *in_qrp = NULL;
static long in_qrp_size = 0;
#ifndef NPICOSAT
static char *in_qdimacs = NULL;
static long in_qdimacs_size = 0;
#endif

static int qrp_format = QRP_ASCII;

static QRPCParser p;

static long pos = 0;
static void (*read_literal_qrp) (char *) = NULL;
#ifndef NPICOSAT
static void (*read_literal_qdimacs) (char *) = NULL;
#endif
static void (*print_num) (int, int) = NULL;
  

QRPType qrp_type = QRPTYPE_UNDEF;    /* sat or unsat? */
QType ptype = QTYPE_UNDEF;           /* pivot var type */
QType rtype = QTYPE_UNDEF;           /* forall/existential reduction? */

static int num_scopes;

static Var *vars = NULL;
static VarId max_vidx = 0, num_vars = 0, size_vars = 0;
static VarId *vidx2id = NULL, size_vidx2id = 0;

static Step *steps = NULL;
static StepId max_sidx = 0, num_steps = 0, size_steps = 0;
static StepId *sidx2id = NULL, size_sidx2id = 0;

static StepId start_sidx;            /* empty clause/cube */

#ifndef NPICOSAT
static unsigned int num_clauses = 0, num_occurrences = 0;
static Clause *clauses = NULL;
static ClauseId *occurrences = NULL;

static VarIdStack universals;
static StepIdStack initial_cubes;
static LitStack occs;
#endif
static VarIdStack res_lits;

static byte_t *mark_occs = NULL;


static QRPCOptions options =
  {
    .verbosity = 0,
    .is_bqrp = 0,
    .print_proof = 1,
    .print_proof_only = 0,
    .print_statistics = 0,
    .check_icubes = 0
  };

static QRPCStatistics statistics;


static void 
print_usage (void)
{
#ifdef NPICOSAT
  printf ("===============================================================");
  printf ("\nWARNING: option '-f' not available, PicoSAT not linked!\n");
  printf ("===============================================================\n");
#endif
  printf ("\nQRPcheck: A tool for extracting and validating proofs\n");
  printf ("          in ascii or binary QRP format.\n\n");
  printf ("Usage: qrpcheck [<OPTIONS>] <FILE>\n\n");
  printf ("  File:\n");
  printf ("    a QBF resolution proof/trace in ascii/binary QRP format");
  printf ("\n\n  Options:\n");
  printf ("    -h, --help        print this message and exit\n");
  printf ("    --version         print version\n");
  printf ("    -v                increase verbosity incrementally\n");
  printf ("    -p [<format>]     print core proof\n");
  printf ("                        format: qrp, bqrp ");
  printf ("(default: as input proof/trace)\n");
  printf ("    -P [<format>]     print core proof without checking\n");
  printf ("                        format: qrp, bqrp ");
  printf ("(default: as input proof/trace)\n");
  printf ("    -f <file>         check against original formula (if sat)\n");
  printf ("    -s                print statistics\n");
}

static void
print_version (void)
{
  printf ("%s\n", VERSION);
}


static inline double
get_cpu_time ()
{
  struct rusage u;

  if (getrusage (RUSAGE_SELF, &u))
    return 0;

  return 1e3 * u.ru_utime.tv_sec + 1e-3 * u.ru_utime.tv_usec +
         1e3 * u.ru_stime.tv_sec + 1e-3 * u.ru_stime.tv_usec;
}

static inline double
get_wc_time ()
{
  struct timeval t;
  
  if (gettimeofday (&t, NULL))
    return 0;

  return 1e3 * t.tv_sec + t.tv_usec * 1e-3;
}

static int  check_proof (void);
#ifndef NPICOSAT
static int  check_initial_cubes (void);
#endif
static void print_statistics (void);
static void print_proof (void);
static void print_bin_num (int, int);
static void print_ascii_num (int, int);
static void parse_qrp (char *, char *, long);
#ifndef NPICOSAT
static void parse_qdimacs (char *, char *, long);
#endif
static void cleanup (void);

struct Node {
  int data;
  struct Node * next;
} Node;

int 
main (int argc, char **argv)
{

  DIR *dir = NULL;
  char *filename_qrp = NULL;
  int in_qrp_fd = 0;
#ifndef NPICOSAT
  char *filename_qdimacs = NULL;
  int in_qdimacs_fd = 0;
#endif
  struct stat file_info;
  int i;

  memset (&statistics, 0, sizeof (QRPCStatistics));

  TIMER_CPU (statistics.time_cpu_total);
  TIMER_WC (statistics.time_wc_total);

  for (i = 1; i < argc; i++)
  {
    if (strcmp (argv[i], "-h") == 0 || strcmp (argv[i], "--help") == 0)
    {
      print_usage ();
      return (EXIT_SUCCESS);
    }
    else if (strcmp (argv[i], "--version") == 0)
    {
      print_version ();
      return (EXIT_SUCCESS);
    }
    else if (strcmp (argv[i], "-v") == 0)
    {
      options.verbosity += 1;
    }
    else if (strcmp (argv[i], "-p") == 0 || strcmp (argv[i], "-P") == 0)
    {
      if (strcmp (argv[i], "-P") == 0)
        options.print_proof_only = 1;
      options.print_proof = 1;

      if (++i < argc)
      {
        if (strcmp (argv[i], "qrp") == 0)
          print_num = &print_ascii_num;
        else if (strcmp (argv[i], "bqrp") == 0)
          print_num = &print_bin_num;
        else if (argv[i][0] == '-' || in_qrp == NULL)
          i -= 1;
        else
          QRPC_ABORT (1, "unknown output format for option %s: %s", 
                      argv[i-1], argv[i]);
      }
    }
    else if (strcmp (argv[i], "-s") == 0)
    {
      options.print_statistics = 1;
    }
    else if (strcmp (argv[i], "-f") == 0)
    {
#ifdef NPICOSAT
      QRPC_ABORT (1, "option '-f' not available (PicoSAT not linked)");
#else
      QRPC_ABORT (++i >= argc, "missing filename for original formula");
      filename_qdimacs = argv[i];
      if ((dir = opendir (filename_qdimacs)) != NULL)
      {
        closedir (dir);
        QRPC_ABORT (1, "'%s' is a directory", filename_qdimacs);
      }

      options.check_icubes = 1;
      QRPC_ABORT ((in_qdimacs_fd = open (filename_qdimacs, O_RDONLY)) == -1,
                  "failed to open '%s'", filename_qdimacs);
      QRPC_ABORT (fstat (in_qdimacs_fd, &file_info) == -1,
                  "failed to fstat '%s'", filename_qdimacs);
      in_qdimacs_size = file_info.st_size;
      QRPC_ABORT ((in_qdimacs = (char *)
                   mmap (0, in_qdimacs_size, PROT_READ, MAP_PRIVATE |
                         MAP_NORESERVE, in_qdimacs_fd, 0)) == MAP_FAILED,
                  "failed to mmap original formula");
      close (in_qdimacs_fd);
#endif
    }
    else
    {
      filename_qrp = argv[i];
      if ((dir = opendir (filename_qrp)) != NULL)
      {
        closedir (dir);
        QRPC_ABORT (1, "'%s' is a directory", filename_qrp);
      }
      QRPC_ABORT ((in_qrp_fd = open (filename_qrp, O_RDONLY)) == -1,
                 "failed to open '%s'", filename_qrp);
      QRPC_ABORT (fstat (in_qrp_fd, &file_info) == -1,
                 "failed to fstat '%s'", filename_qrp);
      in_qrp_size = file_info.st_size;
      QRPC_ABORT ((in_qrp = (char *)
                    mmap (0, in_qrp_size, PROT_READ, MAP_PRIVATE |
                          MAP_NORESERVE, in_qrp_fd, 0)) == MAP_FAILED,
                  "failed to mmap original formula");
      close (in_qrp_fd);
    }
  }

  QRPC_ABORT (filename_qrp == NULL, "missing filename for qresolution proof");
  
#ifndef NPICOSAT
  if (options.print_proof_only) 
    options.check_icubes = 0;
#endif

  if (options.print_statistics)
  {
    TIMER_CPU (statistics.time_cpu_pqrp);
    TIMER_WC (statistics.time_wc_pqrp);
  }
  
  // Parse the trace file and add informtaion 
  // to the internal datastruture 'steps'
  parse_qrp (filename_qrp, in_qrp, in_qrp_size);

  if (options.print_statistics)
  {
    TIMER_CPU (statistics.time_cpu_pqrp);
    TIMER_WC (statistics.time_wc_pqrp);
  }

  if (options.print_statistics)
  {
    statistics.num_realloc_stack_res_lits += 1;
#ifndef NPICOSAT
    if (options.check_icubes)
      statistics.num_realloc_stack_initial_cubes += 1;
#endif
    TIMER_CPU (statistics.time_cpu_cqrp);
    TIMER_WC (statistics.time_wc_cqrp);
  }

  if (check_proof () == ERROR)
  {
    fprintf (stderr, "FAILURE\n");
    cleanup ();
    exit (EXIT_FAILURE);
  }

  if (options.print_statistics)
  {
    statistics.size_stack_res_lits = res_lits.size;
    TIMER_CPU (statistics.time_cpu_cqrp);
    TIMER_WC (statistics.time_wc_cqrp);
  }

  if (options.print_proof)
    print_proof ();

#ifndef NPICOSAT
  if (options.check_icubes)
  {
    if (options.print_statistics)
    {
      TIMER_CPU (statistics.time_cpu_pqdimacs);
      TIMER_WC (statistics.time_wc_pqdimacs);
    }

    parse_qdimacs (filename_qdimacs, in_qdimacs, in_qdimacs_size);
    
    if (options.print_statistics)
    {
      TIMER_CPU (statistics.time_cpu_pqdimacs);
      TIMER_WC (statistics.time_wc_pqdimacs);
      TIMER_CPU (statistics.time_cpu_cicubes);
      TIMER_WC (statistics.time_wc_cicubes);
    } 
    
    if (check_initial_cubes () == ERROR)
    {
      fprintf (stderr, "FAILURE\n");
      cleanup ();
      exit (EXIT_FAILURE);
    }
    
    if (options.print_statistics)
    {
      TIMER_CPU (statistics.time_cpu_cicubes);
      TIMER_WC (statistics.time_wc_cicubes);
    }
  }
#endif

  if (options.print_statistics)
  {
    TIMER_CPU (statistics.time_cpu_total);
    TIMER_WC (statistics.time_wc_total);
    print_statistics ();
  }

  cleanup ();
  fprintf (stderr, "OK\n");
  exit (EXIT_SUCCESS);
}


static unsigned char
get_non_eof_ch (char *in, long *pos, long in_size)
{
  char ch;
  QRPC_ABORT ((*pos == in_size), "unexpected EOF");
  ch = in[(*pos)++];
  return ch;
}

static void
read_bin_lit (char *lits)
{
  unsigned int x = 0, i = 0;
  unsigned char ch;

  while ((ch = get_non_eof_ch (lits, &pos, in_qrp_size)) & 0x80)
    x |= (ch & 0x7f) << (7 * i++);
  vid = x | (ch << (7 * i));
  neg = (vid & 1) != 0;
  vid >>= 1;
  vid = vidx2id[vid];
}

static void
read_ascii_lit (char *lits)
{
  do
  {
    ch = lits[pos++];
  } while (isspace (ch));

  if ((neg = ch == MINUS))
  {
    do
    {
      ch = lits[pos++];
    } while (isspace (ch));
  }

  vid = 0;
  for (;;)
  {
    QRPC_ABORT (!isdigit (ch), "digit expected");
    vid = vid * 10 + (ch - '0');
    ch = lits[pos++];
    if (isspace (ch))
      break;
  }

  vid = vidx2id[vid];
}


/* Note: we use SET_MARK / GET_MARK for accessing mark_occs to encode 
 *       antecedent id into marking (taut/contr check). */
static int
_check (StepId id)
{
  assert (id > 0 && id <= num_steps);
  assert (steps[id].num_ants >= 0 && steps[id].num_ants <= 2);
  assert ((steps[id].is_initial && steps[id].num_ants == 0) ||
          (!steps[id].is_initial && steps[id].num_ants > 0));


  int i, j, num_lits_min = 0, num_lits_ndc = 0, ant_s_level;
  int cnt_occ_res_s_level = 0, res_s_level = 0, prev_res_s_level = 0;
  VarId pivot = 0, *tmp;

  if (options.print_statistics)
    statistics.num_step_ref_total += 1;

  if (steps[id].visited) 
    return SUCCESS;

  steps[id].visited = 1;

  if (options.print_statistics)
  {
    statistics.num_literals_core += steps[id].num_lits;
    statistics.num_steps_total_core += 1;
    if (steps[id].num_ants == 1)
      statistics.num_steps_red_core += 1;
    else if (steps[id].num_ants == 2)
      statistics.num_steps_res_core += 1;
  }

  if (options.verbosity >= 1)
  {
    fprintf (stderr, "step @%d", steps[id].idx);
    if (options.verbosity == 1)
      fprintf (stderr, "\n");
  }

  if (steps[id].num_ants == 0)  /* original clause / initial cube */
  {
    if (options.verbosity > 1)
      fprintf (stderr, ": input clause/cube\n");
#ifndef NPICOSAT
    if (options.check_icubes)
    {
      if (options.print_statistics && (unsigned int) 
          (initial_cubes.sp - initial_cubes.bp) >= initial_cubes.size)
        statistics.num_realloc_stack_initial_cubes += 1;
      PUSH (initial_cubes, id);
    }
#endif
    if (options.print_statistics)
      statistics.num_literals_initial += steps[id].num_lits;
    return SUCCESS;
  }

  if (options.print_proof_only)
    goto CHECK_ANTECEDENTS;

  memset (mark_occs, 0, (num_vars + 1) * sizeof (byte_t));
  STACK_RESET (res_lits);

  for (i = 0; i < steps[id].num_ants; i++)
  {
    if (options.verbosity > 1 && steps[steps[id].ants[i]].id == 0)
      fprintf (stderr, "\n");

    QRPC_ABORT (steps[steps[id].ants[i]].id == 0, 
                "step @%u: invalid antecedent: '%u'\n", 
                steps[id].idx, steps[steps[id].ants[i]].idx);

    if (id == steps[id].ants[i])
    {
      if (options.verbosity > 1)
        fprintf (stderr, ": ERROR: invalid antecedent: %u\n", steps[id].idx);
      return ERROR;
    }

    for (j = 0, pos = 0; j < steps[steps[id].ants[i]].num_lits; j++)
    {
      assert (steps[steps[id].ants[i]].lits >= in_qrp && 
              steps[steps[id].ants[i]].lits < in_qrp + in_qrp_size); 

      ant_s_level = qrp_type == QRPTYPE_SAT ? 
                        steps[steps[id].ants[i]].s_level_sat : 
                        steps[steps[id].ants[i]].s_level_unsat; 

      read_literal_qrp (steps[steps[id].ants[i]].lits);

      /* skip duplicate ptype vars, else res_s_level computation will be
       * incorrect (e.g. in case of duplicate pivot literals) */
      if (vars[vid].type == ptype &&
          (!neg || GET_MARK (vid) != NEG) && (neg || GET_MARK (vid) != POS))
      {
        /* determine resolvent's scope level of innermost e/a var */
        if (vars[vid].s_level > res_s_level)
        {
          prev_res_s_level = res_s_level;
          res_s_level = vars[vid].s_level;
          cnt_occ_res_s_level = 1;
        }
        else if (vars[vid].s_level == res_s_level)
          cnt_occ_res_s_level += 1;
        /* In case that pivot variable is innermost ptype variable in first
         * antecedent, check if there exists a more inner "second innermost"
         * variable in the second antecedent (than in the first). */
        else if (i == 1 && vars[vid].s_level > prev_res_s_level)
          prev_res_s_level = vars[vid].s_level;
      }

      /* complementary literal, first occ. (-)DC */
      if ((!neg && GET_MARK (vid) == DCN) || (neg && GET_MARK (vid) == DCP))
      {
        /* tautology/contradiction in antecedent */
        if (i == GET_ANT_MARK (vid))
        {
          if (options.verbosity > 1)
          {
            fprintf (stderr, ": ERROR: taut./contr. in antecedent @%u: ",
                     steps[steps[id].ants[i]].idx);
            /* first occurrence */
            PRINT_MARK (vid); 
            fprintf (stderr, "(@%u)", steps[steps[id].ants[i]].idx);
            /* second (current) occurrence */
            fprintf (stderr, ", %d (@%u)\n", 
                    neg ? -vars[vid].idx : vars[vid].idx,
                    steps[steps[id].ants[i]].idx);
          }
          return ERROR; 
        }

        if (vars[vid].s_level >= ant_s_level)
        {
          /* no tautology/contradiction, DC in both ants -> don't care if
           * given occ is pos or neg */
          SET_MARK (vid, i, DCPN);
          continue;
        }
         
        /* DC in left ant only -> may not be DC in given resolvent (must be
         * reduced, else error) */
        SET_MARK (vid, i, neg ? NEG : POS);
        num_lits_min += 1;
      }
      else  /* complementary literal, first occ. POS/NEG */
        if ((!neg && GET_MARK (vid) == NEG) || (neg && GET_MARK (vid) == POS))
      {
        /* tautology/contradiction in antecedent */
        if (i == GET_ANT_MARK (vid))
        {
          if (options.verbosity > 1)
          {
            fprintf (stderr, ": ERROR: taut./contr. in antecedent @%u: ",
                     steps[steps[id].ants[i]].idx);
            /* first occurrence */
            PRINT_MARK (vid); 
            fprintf (stderr, "(@%u)", steps[steps[id].ants[i]].idx);
            /* second (current) occurrence */
            fprintf (stderr, ", %d (@%u)\n", 
                    neg ? -vars[vid].idx : vars[vid].idx,
                    steps[steps[id].ants[i]].idx);
          }
          return ERROR; 
        }

        if (vars[vid].type == rtype && 
            vars[vid].s_level >= ant_s_level)
        {
          /* DC in right ant only -> may not be DC in given resolvent (must be
           * reduced, else error) */
           continue;
        }
        
        assert (steps[id].num_ants != 1);

        if (pivot == 0 && vars[vid].type == ptype)
        {
          pivot = vid;
          SET_MARK (pivot, i, neg ? NEG : POS);
          num_lits_min -= 1;

          /* innermost is pivot var, no other occ. from this level */
          if (vars[pivot].s_level == res_s_level && cnt_occ_res_s_level == 2)
            res_s_level = prev_res_s_level;
        }
        else /* tautology/contradiction in resolvent */
        {  
          if (options.verbosity > 1)
          {
            fprintf (stderr, ": ERROR: taut./contr. in resolvent: ");
            /* first occurrence */
            PRINT_MARK (vid); 
            fprintf (stderr, "(@%u)", 
                     steps[steps[id].ants[GET_ANT_MARK (vid)]].idx);
            /* second (current) occurrence */
            fprintf (stderr, ", %d (@%u)\n", 
                     neg ? -vars[vid].idx : vars[vid].idx,
                     steps[steps[id].ants[i]].idx);
          }
          return ERROR;
        }
      }
      else if (GET_MARK (vid) == DCPN)
      {
        /* mark DCPN can only happen in second antecedent */
        assert (GET_ANT_MARK (vid) == 1);
        if (options.verbosity > 1)
        {
          fprintf (stderr, ": ERROR: taut./contr. in antecedent @%u: ",
                   steps[steps[id].ants[i]].idx);
          /* first occurrence */
          PRINT_MARK (vid); 
          fprintf (stderr, "(@%u)", steps[steps[id].ants[i]].idx);
          /* second (current) occurrence */
          fprintf (stderr, ", %d (@%u)\n", 
                  neg ? -vars[vid].idx : vars[vid].idx,
                  steps[steps[id].ants[i]].idx);
        }
        return ERROR;
      }
      else /* no duplicate, either NONE or (-) DC */
        if ((!neg && GET_MARK (vid) != POS) || (neg && GET_MARK (vid) != NEG))
      {
        if (vars[vid].type == rtype && vars[vid].s_level >= ant_s_level)
        {
          assert ((GET_MARK (vid) != DCP && GET_MARK (vid) != DCN) ||
                  (neg && GET_MARK (vid) == DCN) ||
                  (!neg && GET_MARK (vid) == DCP));

          SET_MARK (vid, i, neg ? DCN : DCP);
        }
        else
        {
          if (options.print_statistics && 
              (unsigned int) (res_lits.sp - res_lits.bp) >= res_lits.size)
            statistics.num_realloc_stack_res_lits += 1;
          PUSH (res_lits, vid);
          SET_MARK (vid, i, neg ? NEG : POS);
          num_lits_min += 1;
        }
      }
    }
  }

  SET_MARK (pivot, 0, NONE);

  if (options.verbosity > 1)
    fprintf (stderr, ":\n");

#ifndef NDEBUG
  if (options.verbosity > 1 && steps[id].num_ants == 2)
  {
    fprintf (stderr, "  stack res_lits (prev. to red.):\n    ( ");
    for (tmp = res_lits.bp; tmp < res_lits.sp; tmp++)
    {
      vid = *tmp;
      PRINT_MARK (vid);
    }
    fprintf (stderr, ")\n");
  }
#endif

  /* reduce resolvent 
   * Note: if red. step, all DC have already been identified */
  for (tmp = res_lits.bp; steps[id].num_ants == 2 && tmp < res_lits.sp; tmp++)
  {
    vid = *tmp;

    assert ((vid == pivot && GET_MARK (vid) == NONE)
            || GET_MARK (vid) == POS 
            || GET_MARK (vid) == NEG);

    if (vars[vid].type == rtype && vars[vid].s_level >= res_s_level)
    {
      assert (vid != pivot);  /* pivot is on res_lits (1st ant) */
      
      SET_MARK (vid, 0, GET_MARK (vid) == NEG ? DCN : DCP);
      num_lits_min -= 1;
    }
#ifndef NDEBUG
    else
      assert (vid == pivot || GET_MARK (vid) == POS || GET_MARK (vid) == NEG);
#endif
  }

  if (options.verbosity > 1)
  {
    fprintf (stderr, "  expected:\n    ( "); 
    for (tmp = res_lits.bp; tmp < res_lits.sp; tmp++)
      PRINT_MARK (*tmp);
    fprintf (stderr, ")\n");
  }

  if (steps[id].num_lits < num_lits_min)
  {
    if (options.verbosity > 1)
    {
      fprintf (stderr, "  given:\n    ( ");
      for (i = 0, pos = 0; i < steps[id].num_lits; i++)
      {
        read_literal_qrp (steps[id].lits);
        fprintf (stderr, "%d [%s] ", vars[vid].idx, neg ? "NEG" : "POS");
      }
      fprintf (stderr, 
               ")\n  ERROR: number of literals given < expected (%d < %d)\n",
               steps[id].num_lits, num_lits_min);
    }
    return ERROR;
  }

  /* check if all occurrences in given constraint match the expected
   * (their respective marking). */
  for (i = 0, pos = 0; i < steps[id].num_lits; i++)
  {
    assert (steps[id].lits >= in_qrp && steps[id].lits < in_qrp + in_qrp_size); 
    read_literal_qrp (steps[id].lits);

    if (GET_MARK (vid) == DCPN)
      SET_MARK (vid, 0, neg ? DCN : DCP);
    
    if ((neg && GET_MARK (vid) != NEG && GET_MARK(vid) != DCN) ||
        (!neg && GET_MARK (vid) != POS && GET_MARK(vid) != DCP))
    {
      if (options.verbosity > 1)
      {
        VarId c_vid = vid;
        byte_t c_neg = neg;

        fprintf (stderr, "  given:\n    ( ");
        for (i = 0, pos = 0; i < steps[id].num_lits; i++)
        {
          read_literal_qrp (steps[id].lits);
          fprintf (stderr, "%d [%s] ", vars[vid].idx, neg ? "NEG" : "POS");
        }
        fprintf (stderr, ")\n");
        fprintf (stderr, "  ERROR: var %d is [%s], but [", 
                 vars[c_vid].idx, c_neg ? "NEG" : "POS");
        
        switch (GET_MARK (c_vid))
        {
          case POS: fprintf (stderr, "POS"); break; 
          case NEG: fprintf (stderr, "NEG"); break;
          case DCN: fprintf (stderr, "DCN"); break;
          case DCP: fprintf (stderr, "DCP"); break;
          default:  fprintf (stderr, "NONE");
        }
        fprintf (stderr, "] expected\n");
      }
      return ERROR;
    }
    
    /* make sure that all literals that must occur in given constraint (non-DC
     * literals) do indeed occur (if so, the number of non-DC literals given 
     * matches the minimum number of literals expected) */
    if (GET_MARK (vid) == POS || GET_MARK (vid) == NEG)
      num_lits_ndc += 1;
  }

  /* number of non-DC literals given must match min. number of literals 
   * expected (see above) */
  if (num_lits_ndc != num_lits_min)
  {
    if (options.verbosity > 1)
    {
      fprintf (stderr, "  given:\n    ( ");
      for (i = 0, pos = 0; i < steps[id].num_lits; i++)
      {
        read_literal_qrp (steps[id].lits);
        fprintf (stderr, "%d [%s] ", vars[vid].idx, neg ? "NEG" : "POS");
      }
        fprintf (stderr, ")\n");
      fprintf (stderr, 
               "  ERROR: number of POS/NEG literals (%d)", num_lits_ndc);
      fprintf (stderr, "doesn't match expected (%d)\n", num_lits_min);
      fprintf (stderr, "         (duplicates not considered)\n");
    }
    return ERROR;
  }

  if (options.verbosity > 1)
    fprintf (stderr, "  ok\n");

CHECK_ANTECEDENTS:
  if (_check (steps[id].ants[0]) == ERROR)
    return ERROR;
  else if (steps[id].num_ants == 2)
    return _check (steps[id].ants[1]);

  return SUCCESS;
}

static int
check_proof (void)
{
  read_literal_qrp = qrp_format == QRP_BINARY ? &read_bin_lit : &read_ascii_lit;

  STACK_INIT (res_lits, num_vars);
#ifndef NPICOSAT
  if (options.check_icubes)
    STACK_INIT (initial_cubes, STACK_SIZE);
#endif
  return _check (start_sidx);
}


#ifndef NPICOSAT
static unsigned int
simplify_qcnf (StepId id)
{
  assert (steps[id].num_lits >= 0 && steps[id].num_ants == 0);

  int i, j, num_occs;
  unsigned int cnt_sat = 0;
  VarId *tmp;
  ClauseId *occs_tmp;

  memset (mark_occs, 0, (num_vars + 1) * sizeof (byte_t));

  /* apply cube literals to original clauses */
  for (i = 0, pos = 0; i < steps[id].num_lits; i++)
  {
    read_literal_qrp (steps[id].lits);

    /* mark all 'negative' occs as 'deleted' and all 'positive' occs as 'sat' */
    if (neg)
    {
      num_occs = vars[vid].num_neg_occs;
      occs_tmp = vars[vid].neg_occs;  
    }
    else
    {
      num_occs = vars[vid].num_pos_occs;
      occs_tmp = vars[vid].pos_occs; 
    }
    mark_occs[vid] = DELETED;

    for (j = 0; j < num_occs; j++)
    {
      if (clauses[occs_tmp[j]].is_sat)
        continue;
      /* we require clause to be a-reduced */
      if (vars[vid].type == QTYPE_FORALL && 
          vars[vid].s_level >= clauses[occs_tmp[j]].s_level)
        continue;
      clauses[occs_tmp[j]].is_sat = 1;
      cnt_sat += 1;
    }
  }
  assert (cnt_sat <= num_clauses);
  
  /* given cube was non-coverintg set and not all clauses are satisfied,
   * 'delete' all universal lits possibly left in qcnf */
  if (cnt_sat < num_clauses)
  {
    for (tmp = universals.bp; tmp != universals.sp; tmp++)
      mark_occs[*tmp] = DELETED;
  }
  return cnt_sat;
}

static int
check_initial_cubes (void)
{
  int j, k, cnt_deleted;
  unsigned int i;
  StepId *tmp;
  Lit lit;
  struct Node* head = NULL;
  //struct Node* second = NULL;
  head = (struct Node*)malloc(sizeof(struct Node));
  //second = (struct Node*)malloc(sizeof(struct Node));

  read_literal_qrp = qrp_format == QRP_BINARY ? &read_bin_lit : &read_ascii_lit;
  read_literal_qdimacs = &read_ascii_lit;
  
  for (tmp = initial_cubes.bp; tmp != initial_cubes.sp; tmp++)
  {
    if (options.verbosity >= 1)
    {
      fprintf (stderr, "cube @%d: ", steps[*tmp].idx);
      for (k = 0, pos = 0; k < steps[*tmp].num_lits; k++)
      {
        read_literal_qrp (steps[*tmp].lits);
        fprintf (stderr, "%d ", neg ? -vars[vid].idx : vars[vid].idx);
      }
      fprintf (stderr, ": ");
    }

    if (simplify_qcnf (*tmp) == num_clauses)
    {
      if (options.verbosity >= 1)
        fprintf (stderr, "OK (cover set)\n");
      if (options.print_statistics)
        statistics.num_steps_initial_full += 1;

      for (i = 0; i < num_clauses; i++)
      {
        if (!clauses[i].is_taut)
          clauses[i].is_sat = 0; /* reset */
      }
      continue;
    }

    if (options.verbosity > 1)
      fprintf (stderr, " initialize PicoSAT\n");
    picosat_init ();

    for (i = 0; i < num_clauses; i++)
    {
      if (clauses[i].is_sat)
      {
        if (!clauses[i].is_taut)
          clauses[i].is_sat = 0;  /* reset */
        continue;
      }
      cnt_deleted = 0;

      if (options.verbosity > 1)
        fprintf (stderr, "  added clauses[%d]: (", i);
      
      for (j = 0, pos = 0; j < clauses[i].num_lits; j++)
      {
        assert (clauses[i].lits >= in_qdimacs && 
                clauses[i].lits < in_qdimacs + in_qdimacs_size); 
        read_literal_qdimacs (clauses[i].lits);
        lit = neg ? -vars[vid].idx : vars[vid].idx;
        
        if (mark_occs[vid] == DELETED)
        {
          if (options.verbosity > 1)
            fprintf (stderr, " [%d]", lit);
          cnt_deleted += 1;
          continue;
        }
        if (options.verbosity > 1)
          fprintf (stderr, " %d", lit);
        head->data = lit;
        head->next = NULL;
        picosat_add (lit);
      }
      if (options.verbosity > 1)
        fprintf (stderr, " )\n");
      
      picosat_add (0);

      if (cnt_deleted == clauses[i].num_lits)  /* empty */
      {
        if (options.verbosity >= 1)
        {
          fprintf (stderr, "FAILED ");
          fprintf (stderr, "(empty clause (%u) in simplified qcnf)\n", i);
        }
        return ERROR;
      }
    }

    // Store the result of the PICOSAT call. 
    int result_picosat_call = picosat_sat(-1);
    int sat_assgmt = 0;
    int lit_value = 0;
    if (result_picosat_call == PICOSAT_UNSATISFIABLE)
    {
      if (options.verbosity >= 1)
        fprintf (stderr, "FAILED (unsat)\n");
      return ERROR;
    } else if (result_picosat_call == PICOSAT_SATISFIABLE) {
         struct Node *cursor = head;
         while (cursor != NULL) {
           sat_assgmt = picosat_deref (cursor->data);
           lit_value = cursor->data;
           sat_assgmt > 0 ? fprintf(stderr, "%d %d %d\n", tmp[0], lit_value, 0): fprintf(stderr, "%d %d %d\n", tmp[0], lit_value * -1, 0);
           cursor = cursor->next;
         }
    }

    if (options.verbosity >= 1)
      fprintf (stderr, "OK (non-covering set)\n");

    picosat_reset ();
  }
  return SUCCESS;
}
#endif


static void
print_bin_num (int num, int is_literal)
{
  unsigned char ch;
  unsigned int x = num;

  if (is_literal)
    x = num < 0 ? (-x << 1) | 1 : x << 1;

  while (x & ~0x7f)
  {
    ch = (x & 0x7f) | 0x80;
    putc (ch, stdout);
    x >>= 7;
  }
  ch = x;
  putc (ch, stdout);
}

static void
print_ascii_num (int num, int is_literal)
{
  assert (num >= 0 || is_literal);
#ifdef NDEBUG
  is_literal = 0;  /* get rid of compiler warning */
#endif
  printf ("%d ", num);
}

static void
print_proof (void)
{
  char c;
  int j;
  unsigned int i, cnt_free_vars = 0;
  QType q = QTYPE_UNDEF;

  if (print_num == NULL)
  {
    if (qrp_format == QRP_BINARY)
      print_num = &print_bin_num;
    else
      print_num = &print_ascii_num;
  }

  if (print_num == &print_bin_num)
    printf ("p bqrp %u %u%c", max_vidx, max_sidx, BQRP_EOL);
  else
    printf ("p qrp %u %u%c", max_vidx, max_sidx, '\n');

  if (num_scopes == 1)
    goto PRINT_NONFREE_VARS;
 
  /* free vars -> outermost existential scope */
  for (i = num_vars; vars[i].s_level == 0 && vars[i].type == QTYPE_EXISTS; i--)
  {
    if (i == num_vars)
    {
      if (print_num == &print_bin_num)
        print_num (0, 0);

      printf ("%c", 'e');
      if (print_num == &print_ascii_num)
        printf (" ");
      q = QTYPE_EXISTS;
    }
    print_num (vars[i].idx, 0);
    cnt_free_vars += 1;
  }

PRINT_NONFREE_VARS:
  /* non-free vars in outermost existential scope */
  for (i = 1; i <= num_vars - cnt_free_vars && vars[i].s_level == 0; i++)
  {
    if (i == 1 && q == QTYPE_UNDEF)
    {
      assert (vars[i].type != QTYPE_FORALL);
      if (print_num == &print_bin_num)
        print_num (0, 0);
      printf ("%c", 'e');
      if (print_num == &print_ascii_num)
        printf (" ");
      q = QTYPE_EXISTS;
    }
    print_num (vars[i].idx, 0);
  }
  if (q != QTYPE_UNDEF)
  {
    print_num (0, 0);
    if (print_num == &print_ascii_num)
      printf ("\n");
  }

  /* remaining scopes */
  for (j = 0; i <= num_vars - cnt_free_vars; i++, j++)
  {
    if (q != vars[i].type)
    {
      if (j > 0)
      {
        print_num (0, 0);
        if (print_num == &print_ascii_num)
          printf ("\n");
      }

      q = vars[i].type;
      c = q == QTYPE_EXISTS ? 'e' : 'a';
      if (print_num == &print_bin_num)
        print_num (0, 0);
      printf ("%c", c);
      if (print_num == &print_ascii_num)
        printf (" ");
    }
    print_num (vars[i].idx, 0);
  }
  if (j > 0)
  {
    print_num (0, 0);
    if (print_num == &print_ascii_num)
      printf ("\n");
  }

  /* steps*/
  for (i = 1; i <= num_steps; i++)
  {
    if (!steps[i].visited)
      continue;

    print_num (steps[i].idx, 0);

    for (j = 0, pos = 0; j < steps[i].num_lits; j++)
    {
      assert (steps[i].lits >= in_qrp && steps[i].lits < in_qrp + in_qrp_size); 
      read_literal_qrp (steps[i].lits);
      print_num (neg ? -vars[vid].idx : vars[vid].idx, 1);
    }
    print_num (0, 0);
    for (j = 0; j < steps[i].num_ants; j++)
      print_num (steps[steps[i].ants[j]].idx, 0);
    print_num (0, 0);
    if (print_num == &print_ascii_num)
      printf ("\n");
  }

  /* result */
  if (print_num == &print_bin_num)
    print_num (0, 0);
  printf ("r %s\n", qrp_type == QRPTYPE_SAT ? "sat" : "unsat");
}


static void 
print_statistics (void)
{
  double size;
  int kib = 1024, mib = 1024 * 1024, factor;
  char *skib = "KiB", *smib = "MiB", *sb = "B", *unit;

  STATS ("\n----------------------------");
  STATS (" STATISTICS ");
  STATS ("----------------------------\n");
  STATS ("GENERAL\n\n");
  STATS ("total number of variables:                              %11u\n", 
         statistics.num_vars);
  STATS ("total number of free variables:                         %11u\n", 
         statistics.num_free_vars);
  STATS ("total number of literals:                               %11llu\n", 
         statistics.num_literals);
  STATS ("total number of proof steps:                            %11u\n", 
         statistics.num_steps_total);
  STATS ("total number of original clauses / initial cubes:       %11d\n", 
         statistics.num_steps_initial);
  STATS ("total number of reduction steps:                        %11u\n", 
         statistics.num_steps_red);
  STATS ("total number of resolution steps:                       %11u\n", 
         statistics.num_steps_res);
  STATS_HR;
  STATS ("CORE PROOF\n\n");
  STATS ("number of literals:                                     %11llu\n", 
         statistics.num_literals_core);
  STATS ("number of literals in %s                %11llu\n\n",
         qrp_type == QRPTYPE_UNSAT ? "original clauses: " : 
                                     "initial cubes:    ",
         statistics.num_literals_initial);
  STATS ("number of proof steps: \t\t\t\t\t%11u\n",
         statistics.num_steps_total_core);
  STATS ("number of %s                            %11d\n", 
         qrp_type == QRPTYPE_UNSAT ? "original clauses: " : 
                                     "initial cubes:    ",
         statistics.num_steps_total_core - statistics.num_steps_red_core -
         statistics.num_steps_res_core);

#ifndef NPICOSAT
  if (options.check_icubes)
  {
    STATS ("number of cover sets:                                 %11d\n",
           statistics.num_steps_initial_full);
    STATS ("number of non-covering sets:                          %11d\n",
           statistics.num_steps_total_core - statistics.num_steps_red_core -
           statistics.num_steps_res_core - statistics.num_steps_initial_full);
  }
#endif
  STATS ("number of reduction steps:                              %11u\n",
         statistics.num_steps_red_core); 
  STATS ("number of resolution steps:                             %11u\n\n",
         statistics.num_steps_res_core);
  STATS ("total number of step references:                        %11u\n",
         statistics.num_step_ref_total); 
  STATS ("number of references per step:                          %11.2f\n",
         (double) statistics.num_step_ref_total / 
                  statistics.num_steps_total_core);
  STATS_HR;
  STATS ("TIME\n\n");
  STATS ("total                                                   %8.2f ms\n",
         statistics.time_wc_total);
  STATS ("total for proof parsed:                                 %8.2f ms\n", 
         statistics.time_wc_pqrp);
  STATS ("total for proof check:                                  %8.2f ms\n", 
         statistics.time_wc_cqrp);
#ifndef NPICOSAT
  if (options.check_icubes)
  {
    STATS ("total for qdimacs parser:                             %8.2f ms\n", 
           statistics.time_wc_pqdimacs);
    STATS ("total for initial cubes check:                        %8.2f ms\n", 
           statistics.time_wc_cicubes);
  }
#endif
  STATS ("cpu total                                               %8.2f ms\n",
         statistics.time_cpu_total);
  STATS ("cpu for proof parsed:                                   %8.2f ms\n", 
         statistics.time_cpu_pqrp);
  STATS ("cpu for proof check:                                    %8.2f ms\n", 
         statistics.time_cpu_cqrp);
#ifndef NPICOSAT
  if (options.check_icubes)
  {
    STATS ("cpu for qdimacs parser:                               %8.2f ms\n", 
           statistics.time_cpu_pqdimacs);
    STATS ("cpu for initial cubes check:                          %8.2f ms\n", 
           statistics.time_cpu_cicubes);
  }
#endif
  STATS_HR;
  STATS ("MEMORY\n\n");
  size = (double) statistics.size_vars * sizeof (Var);
  STATS_MEM (factor, unit);
  STATS ("variables array:                                %s%15.2f %s\n",  
         unit == sb ? "  " : "", size / factor, unit);
  STATS ("  number of (re)allocations:                            %11u\n",
         statistics.num_realloc_vars);
  size = (double) statistics.size_vidx2id * sizeof (VarId);
  STATS_MEM (factor, unit);
  STATS ("variables index mapping array:                  %s%15.2f %s\n", 
         unit == sb ? "  " : "", size / factor, unit);
  STATS ("  number of (re)allocations:                            %11u\n",
         statistics.num_realloc_vidx2id);
  size = (double) statistics.size_mark_occs * sizeof (VarId);
  STATS_MEM (factor, unit);
  STATS ("mark occurrences array:                          %s%15.2f %s\n", 
         unit == sb ? "  " : "", size / factor, unit);
  STATS (" number of (re)allocations:                             %11u\n",
         statistics.num_realloc_mark_occs);
  size = (double) statistics.size_steps * sizeof (Step);
  STATS_MEM (factor, unit);
  STATS ("steps array:                                    %s%15.2f %s\n",
         unit == sb ? "  " : "", size / factor, unit);
  STATS ("  number of (re)allocations:                            %11u\n",
         statistics.num_realloc_steps);
  size = (double) statistics.size_sidx2id * sizeof (StepId);
  STATS_MEM (factor, unit);
  STATS ("steps index mapping array:                      %s%15.2f %s\n", 
         unit == sb ? "  " : "", size / factor, unit);
  STATS ("  number of (re)allocations:                            %11u\n",
         statistics.num_realloc_sidx2id);
#ifndef NPICOSAT
  if (options.check_icubes)
  {
    size = (double) statistics.size_clauses * sizeof (Clause);
    STATS_MEM (factor, unit);
    STATS ("clauses array:                                %s%15.2f %s\n",
           unit == sb ? "  " : "", size / factor, unit);
    STATS ("  number of (re)allocations:                         %11u\n",
           statistics.num_realloc_clauses);
    size = (double) statistics.size_occurrences * sizeof (Lit);
    STATS_MEM (factor, unit);
    STATS ("occurrences array:                             %s%15.f %s\n",
           unit == sb ? "  " : "", size / factor, unit);
    STATS ("  number of (re)allocations:                         %11u\n",
           statistics.num_realloc_occurrences);
    size = (double) statistics.size_stack_occs * sizeof (Lit);
    STATS_MEM (factor, unit);
    STATS ("occurrences stack:                             %s%15.f %s\n",
           unit == sb ? "  " : "", size / factor, unit);
    STATS ("  number of (re)allocations:                         %11u\n",
           statistics.num_realloc_stack_occs);
    size = (double) statistics.size_stack_universals * sizeof (Lit);
    STATS_MEM (factor, unit);
    STATS ("universals stack:                             %s%15.f %s\n",
           unit == sb ? "  " : "", size / factor, unit);
    STATS ("  number of (re)allocations:                         %11u\n",
           statistics.num_realloc_stack_universals);
    size = (double) statistics.size_stack_initial_cubes * sizeof (Lit);
    STATS_MEM (factor, unit);
    STATS ("initial cubes stack:                          %s%15.f %s\n",
           unit == sb ? "  " : "", size / factor, unit);
    STATS ("  number of (re)allocations:                         %11u\n",
           statistics.num_realloc_stack_initial_cubes);
  }
#endif
  size = (double) statistics.size_stack_res_lits * sizeof (Lit);
  STATS_MEM (factor, unit);
  STATS ("resolvent literals stack:                       %s%15.f %s\n",
         unit == sb ? "  " : "", size / factor, unit);
  STATS ("  number of (re)allocations:                            %11u\n",
         statistics.num_realloc_stack_res_lits);
  STATS_HR;
  STATS ("\n");
}


/* ------------------------------ Parser ------------------------------ */

static int
parse_bin_num (void)
{
  unsigned int x = 0, i = 0;
  unsigned char ch;

  while ((ch = get_non_eof_ch (p.in, &(p.pos), p.in_size)) & 0x80)
  {
    p.col += 1;
    x |= (ch & 0x7f) << (7 * i++);
  }
  num = x | (ch << (7 * i));
  return num;
}

static int
parse_bin_lit (void)
{
  parse_bin_num ();
  neg = (num & 1) != 0;
  num >>= 1;
  return num;
}


static int
parse_ascii_num (void)
{
  QRPC_ABORT_PARSER (ch == MINUS, "pos. number expected");

  num = 0;
  for (;;)                                
  {                                       
    QRPC_ABORT_PARSER (!isdigit (ch), "digit expected");
    num = num * 10 + (ch - '0');           
    ch = p.in[p.pos++];                        

    if (ch == BQRP_EOL) break;

    if (isspace (ch))
    {                                     
      if (ch == '\n')                      
      {                                   
        p.line += 1;                        
        p.col = 0;                          
      }                                   
      else                                
        p.pos -= 1;                         
      break;                              
    }                                     
    p.col += 1;                             
  }                                       
  if (p.pos == p.in_size)                     
    ch = EOF;                                
  return num;
}

static int
parse_ascii_lit (void)
{
  if ((neg = ch == MINUS))
    SKIP_SPACE_DO_WHILE;
  parse_ascii_num ();
  return num;
}


/* Note: Preamble is in ASCII in any case (QRP, binQRP, QDIMACS). */
static void
parse_preamble (void)
{
  char comment = p.is_qrp ? QRP_COMMENT : QDIMACS_COMMENT;
  char preamble = p.is_qrp ? QRP_PREAMBLE : QDIMACS_PREAMBLE;

  SKIP_SPACE_DO_WHILE;
  QRPC_ABORT (ch == EOF, "invalid input (empty file)");

  ch = tolower (ch);
  while (ch == comment)
  {
    while (p.pos < p.in_size && (ch = p.in[p.pos++]) != '\n');
    p.line += 1;
    p.col = 0;
    SKIP_SPACE_DO_WHILE;
  }

  QRPC_ABORT_PARSER (ch != preamble, "missing preamble");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  if (ch == 'b')
  {
    qrp_format = QRP_BINARY;
    SKIP_SPACE_DO_WHILE;
    ch = tolower (ch);
  }
  QRPC_ABORT_PARSER ((p.is_qrp && ch != 'q') || (!p.is_qrp && ch != 'c'), 
                     "invalid preamble");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  QRPC_ABORT_PARSER ((p.is_qrp && ch != 'r') || (!p.is_qrp && ch != 'n'), 
                     "invalid preamble");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  QRPC_ABORT_PARSER ((p.is_qrp && ch != 'p') || (!p.is_qrp && ch != 'f'), 
                     "invalid preamble");
  SKIP_SPACE_DO_WHILE;
  
  /* Note: if qdimacs, max_vidx != 0! */
  if ((unsigned int) p.read_number() >= size_vidx2id)
  {
    QRPC_REALLOC (vidx2id, size_vidx2id, num + 1);
    max_vidx = num;
    size_vidx2id = num + 1;

    if (vars == NULL)
    {
      QRPC_REALLOC (vars, 0, num + 1);
      size_vars = num + 1;
      if (options.print_statistics)
        statistics.num_realloc_vars += 1;
    }
    if (options.print_statistics)
      statistics.num_realloc_vidx2id += 1;
  }

  SKIP_SPACE_WHILE;
  p.read_number ();

  if (p.is_qrp)
  {
    max_sidx = num;
    QRPC_REALLOC (sidx2id, 0, max_sidx + 1);
    size_sidx2id = max_sidx + 1;
    QRPC_REALLOC (steps, 0, max_sidx + 1);
    size_steps = max_sidx + 1;
    if (options.print_statistics)
    {
      statistics.num_realloc_sidx2id += 1;
      statistics.num_realloc_steps += 1;
    }
  }
#ifndef NPICOSAT
  else
  {
    num_clauses = num;
    QRPC_REALLOC (clauses, 0, num_clauses);
    if (options.print_statistics)
      statistics.num_realloc_clauses += 1;
  }
#endif
}


static void 
parse_scopes (void)
{
  QType scope_type = QTYPE_UNDEF;
  char e = p.is_qrp ? QRP_EXISTS : QDIMACS_EXISTS;
  char a = p.is_qrp ? QRP_FORALL : QDIMACS_FORALL;
  char eol = p.is_qrp ? QRP_EOL : QDIMACS_EOL;

  eol = p.is_qrp && qrp_format == QRP_BINARY ? BQRP_EOL : eol;
  num_scopes = 0;

  for (;;)
  {
    if (p.is_qrp && qrp_format == QRP_BINARY) 
    {
      if (p.read_number () != eol) break;  /* initial 0 of 0a.../0e... */
      READ_CHAR;
      if (ch == QRP_RESULT) return;
      QRPC_ABORT_PARSER (ch != e && ch != a, "quantifier expected");
    }
    else
    {
      SKIP_SPACE_DO_WHILE;
      ch = tolower (ch);
      if (ch != e && ch != a) break;
    }
    scope_type = ch == e ? QTYPE_EXISTS : QTYPE_FORALL;
    /* outermost scope is existential by default */
    if (num_scopes == 0 && scope_type == QTYPE_FORALL)
      num_scopes += 1;

    for (;;)
    {
      if (p.is_qrp && qrp_format == QRP_BINARY) 
      {
        if (p.read_number () == eol) break;
      }
      else
      {
        SKIP_SPACE_DO_WHILE;
        if (ch == eol) break;
        QRPC_ABORT_PARSER (ch == EOF, "'0' expected");
        p.read_number ();
      }

      if ((unsigned) num >= size_vidx2id)
      {
        QRPC_REALLOC (vidx2id, size_vidx2id, num + 1);
        max_vidx = num;
        size_vidx2id = num + 1;

        if (options.print_statistics)
          statistics.num_realloc_vidx2id += 1;
      }

      if (p.is_qrp || vidx2id[num] == 0)
      {
        vidx2id[num] = ++num_vars;
        if (num_vars >= size_vars)
        {
          unsigned int new_size = size_vars + (size_vars >> 2) + 2;
          QRPC_REALLOC (vars, size_vars, new_size);
          size_vars = new_size;
          if (options.print_statistics)
            statistics.num_realloc_vars += 1;
        }

        vars[vidx2id[num]].idx = num;
        vars[vidx2id[num]].id = vidx2id[num];
        vars[vidx2id[num]].type = scope_type;
        vars[vidx2id[num]].s_level = num_scopes;
      }
#ifndef NPICOSAT
      else  /* qdimacs only */
      {
        if (vars[vidx2id[num]].s_level != num_scopes)
          vars[vidx2id[num]].s_level = num_scopes;

        QRPC_ABORT_PARSER (vars[vidx2id[num]].type != QTYPE_UNDEF &&
                           vars[vidx2id[num]].type != scope_type,
                           "mismatching quantifier");
      }
      /* collect universals for initial cube checking */ 
      if (!p.is_qrp && scope_type == QTYPE_FORALL)
      {
        if (options.print_statistics &&
            (unsigned int) (universals.sp - universals.bp) >= universals.size)
          statistics.num_realloc_stack_universals += 1;
        PUSH (universals, vidx2id[num]);
      }
#endif
    }
    /* Note: it's not necessery to explicitely merge consecutive scopes of the
     * same quantifier type (makes no difference in our case) */
    num_scopes += 1;
  }
}


static void
parse_literals (unsigned int id)
{
  char eol = p.is_qrp ? QRP_EOL : QDIMACS_EOL;
  
#ifndef NPICOSAT
  if (!p.is_qrp)
    memset (mark_occs, 0, (num_vars + 1) * sizeof (byte_t));
#endif

  eol = p.is_qrp && qrp_format == QRP_BINARY ? BQRP_EOL : eol;
  SKIP_SPACE_WHILE_IF (!p.is_qrp || qrp_format != QRP_BINARY);

  for (;;)
  {
#ifndef NPICOSAT
    if (!p.is_qrp && ch == eol)  /* qdimacs only */
    {
      if (options.print_statistics &&
          (unsigned int) (occs.sp - occs.bp) >= occs.size)
        statistics.num_realloc_stack_occs += 1;
      PUSH (occs, EOL);
    }
#endif

    QRPC_ABORT_PARSER ((!p.is_qrp || qrp_format != QRP_BINARY) && ch == EOF, 
                       "unexpected EOF");

    if (p.read_literal () == EOL) break;

    if ((VarId) num >= size_vidx2id)
    {
      QRPC_REALLOC (vidx2id, size_vidx2id, num + 1);
      max_vidx = num;
      size_vidx2id = num + 1;
      if (options.print_statistics)
        statistics.num_realloc_vidx2id += 1;
    }

    if (vidx2id[num] == 0)  /* free var */
    {
      vidx2id[num] = ++num_vars;
      if (num_vars >= size_vars)
      {
        QRPC_REALLOC (vars, size_vars, num_vars + 1);
        QRPC_REALLOC (mark_occs, size_vars, num_vars + 1);
        size_vars = num_vars + 1;
        if (options.print_statistics)
        {
          statistics.num_realloc_vars += 1;
          statistics.num_realloc_mark_occs += 1;
        }
      }
      vars[vidx2id[num]].idx = num;
      vars[vidx2id[num]].id = vidx2id[num];
      vars[vidx2id[num]].type = QTYPE_EXISTS;
      vars[vidx2id[num]].s_level = 0;

      if (options.print_statistics)
        statistics.num_free_vars += 1;
    }

    num = vidx2id[num];
#ifndef NPICOSAT
    if (!p.is_qrp)  /* qdimacs only */
    {
      if (neg)
      {
        if (mark_occs[num] == NEG)
        {
          SKIP_SPACE_DO_WHILE;
          continue;
        }
        if (mark_occs[num] == POS)
        {
          clauses[id].is_taut = 1;
          clauses[id].is_sat = 1;
        }
        vars[num].num_neg_occs += 1;

        if (options.print_statistics &&
            (unsigned int) (occs.sp - occs.bp) >= occs.size)
          statistics.num_realloc_stack_occs += 1;
        
        PUSH (occs, -num);
        num_occurrences +=1;
        mark_occs[num] = NEG;
      }
      else
      {
        if (mark_occs[num] == POS)
        {
          SKIP_SPACE_DO_WHILE;
          continue;
        }
        if (mark_occs[num] == NEG)
        {
          clauses[id].is_taut = 1;
          clauses[id].is_sat = 1;
        }
        vars[num].num_pos_occs += 1;

        if (options.print_statistics &&
            (unsigned int) (occs.sp - occs.bp) >= occs.size)
          statistics.num_realloc_stack_occs += 1;
        
        PUSH (occs, num);
        num_occurrences +=1;
        mark_occs[num] = POS;
      }
      clauses[id].num_lits += 1;
      if (vars[num].type == QTYPE_EXISTS && 
          clauses[id].s_level < vars[num].s_level)
        clauses[id].s_level = vars[num].s_level;
    }
    else
#endif
    {
      steps[id].num_lits += 1;
      /* determine scope level for a/e-reduction */
      if (vars[num].type == QTYPE_FORALL 
          && steps[id].s_level_sat < vars[num].s_level)
        steps[id].s_level_sat = vars[num].s_level;
      else if (vars[num].type == QTYPE_EXISTS
               && steps[id].s_level_unsat < vars[num].s_level)
        steps[id].s_level_unsat = vars[num].s_level;
    }
    SKIP_SPACE_DO_WHILE_IF (!p.is_qrp || qrp_format != QRP_BINARY);
  }
}


static void
parse_qrp (char *filename_qrp, char *in_qrp, long in_qrp_size)
{
  char eol = QRP_EOL;
  unsigned int new_size;
  StepId sidx;

  memset (&p, 0, sizeof (QRPCParser));

  p.filename = filename_qrp;
  p.in = in_qrp;
  p.in_size = in_qrp_size;
  p.line = 1;
  p.is_qrp = QRP_ASCII;

  p.read_number  = &parse_ascii_num;  /* preamble is ascii for all */

  parse_preamble ();

  if (qrp_format == QRP_BINARY)
  {
    eol = BQRP_EOL;
    p.read_number = &parse_bin_num;
    p.read_literal = &parse_bin_lit;
  }
  else
    p.read_literal = &parse_ascii_lit;

  parse_scopes ();

  QRPC_REALLOC (mark_occs, 0, size_vars);
  if (options.print_statistics)
    statistics.num_realloc_mark_occs += 1;

  /* Note: if bqrp then num == 1st sidx or BQRP_EOL (if #steps == 0) */
  for (;;)
  {
    if (qrp_format == QRP_BINARY) 
    {
      if (num == eol) break;
    }
    else
    {
      ch = tolower (ch);
      if (ch == QRP_RESULT || ch == EOF) break;
      QRPC_ABORT_PARSER (ch == QRP_EXISTS || ch == QRP_FORALL,
                         "step expected, found quantifier set");
      p.read_number ();
    }
    if ((sidx = num) >= size_sidx2id)
    {
      new_size =  sidx + (sidx >> 2) + 2;
      QRPC_REALLOC (sidx2id, size_sidx2id, new_size);
      size_sidx2id = new_size;
      if (sidx > max_sidx)
        max_sidx = sidx;

      if (options.print_statistics)
        statistics.num_realloc_sidx2id += 1;
    }
    if (sidx2id[sidx] == 0)
    {
      if ((sidx2id[sidx] = ++(num_steps)) >= size_steps) /* increase by half */
      {
        new_size = num_steps + (num_steps >> 2) + 2;
        QRPC_REALLOC (steps, size_steps, new_size);
        size_steps = new_size;

        if (options.print_statistics)
          statistics.num_realloc_steps += 1;
      }
    }
    QRPC_ABORT_PARSER (steps[sidx2id[sidx]].id != 0, 
                       "invalid step index '%u' (not unique)", sidx);
    assert (steps[sidx2id[sidx]].idx == 0 || steps[sidx2id[sidx]].idx == sidx);
    steps[sidx2id[sidx]].id = sidx2id[sidx]; 
    steps[sidx2id[sidx]].idx = sidx; 
  
    SKIP_SPACE_WHILE_IF (qrp_format != QRP_BINARY);
    steps[sidx2id[sidx]].lits = 
      qrp_format == QRP_BINARY ? p.in + p.pos : p.in + p.pos - 1;

    /* literals */
    parse_literals (sidx2id[sidx]);
    if (steps[sidx2id[sidx]].num_lits == 0)
    {
      QRPC_ABORT_PARSER (start_sidx != 0 && qrp_type == QRPTYPE_UNSAT, 
                         "invalid proof: more than one empty clause given");
      QRPC_ABORT_PARSER (start_sidx != 0 && qrp_type == QRPTYPE_SAT, 
                         "invalid proof: more than one empty cube given");
      start_sidx = sidx2id[sidx];
    }
    if (options.print_statistics)
      statistics.num_literals += steps[sidx2id[sidx]].num_lits;
    
    SKIP_SPACE_WHILE_IF (qrp_format != QRP_BINARY);

    /* antecedents */
    for (;;)
    {
      if (qrp_format == QRP_BINARY) 
      {
        if (p.read_number () == eol) break;
        QRPC_ABORT_PARSER (steps[sidx2id[sidx]].num_ants >= 2, 
                           "invalid number of antecedents");
      }
      else
      {
        if (ch == eol) break;
        QRPC_ABORT_PARSER (ch == EOF, "'%c' expected", eol);
        QRPC_ABORT_PARSER (steps[sidx2id[sidx]].num_ants >= 2, 
                           "invalid number of antecedents");
        p.read_number ();
      }

      if ((unsigned int) num >= size_sidx2id)
      {
        new_size =  num + (num >> 2) + 2;
        QRPC_REALLOC (sidx2id, size_sidx2id, new_size);
        size_sidx2id = new_size;
        if ((unsigned int) num > max_sidx)
          max_sidx = sidx;

        if (options.print_statistics)
          statistics.num_realloc_sidx2id += 1;
      }
      if (sidx2id[num] == 0)
      {
        /* increase by half */
        if ((sidx2id[num] = ++(num_steps)) >= size_steps)
        {
          new_size = num_steps + (num_steps >> 2) + 2;
          QRPC_REALLOC (steps, size_steps, new_size);
          size_steps = new_size;

          if (options.print_statistics)
            statistics.num_realloc_steps += 1;
        }
      }
      steps[sidx2id[num]].idx = num;  /* set idx for all antecedents to later
                                         be able to identifiy invalid ones */
      num = sidx2id[num];
      steps[sidx2id[sidx]].ants[steps[sidx2id[sidx]].num_ants++] = num;
      SKIP_SPACE_DO_WHILE_IF (qrp_format != QRP_BINARY); 
    }

    if (steps[sidx2id[sidx]].num_ants == 0)
      steps[sidx2id[sidx]].is_initial = 1;

    if (options.print_statistics)
    {
      switch (steps[sidx2id[sidx]].num_ants)
      {
        case 0: statistics.num_steps_initial += 1; break;
        case 1: statistics.num_steps_red += 1; break;
        default: statistics.num_steps_res += 1;
      }
    }

    /* next sidx */
    if (qrp_format == QRP_BINARY) 
      p.read_number ();
    else
      SKIP_SPACE_DO_WHILE;
  }

  if (qrp_format == QRP_BINARY) 
  {
    READ_CHAR;
    QRPC_ABORT_PARSER (ch != QRP_RESULT, "invalid result statement");
  }
  QRPC_ABORT_PARSER (ch == EOF, "missing result statement");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  QRPC_ABORT_PARSER (ch != 's' && ch != 'u',
                     "invalid result statement: 'sat' or 'unsat' expected");
  qrp_type = ch == 's' ? QRPTYPE_SAT : QRPTYPE_UNSAT;
  QRPC_ABORT (qrp_type == QRPTYPE_UNSAT && options.check_icubes,
              "invalid option for UNSAT proof: -f");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  if (qrp_type == QRPTYPE_UNSAT)
  {
    ptype = QTYPE_EXISTS;
    rtype = QTYPE_FORALL;

    QRPC_ABORT_PARSER (ch != 'n', "'unsat' expected");
    SKIP_SPACE_DO_WHILE;
    ch = tolower (ch);
    QRPC_ABORT_PARSER (ch != 's', "'unsat' expected");
    SKIP_SPACE_DO_WHILE;
    ch = tolower (ch);
  }
  else
  {
    ptype = QTYPE_FORALL;
    rtype = QTYPE_EXISTS;
  }

  QRPC_ABORT_PARSER (ch != 'a', "'sat' or 'unsat' expected");
  SKIP_SPACE_DO_WHILE;
  ch = tolower (ch);
  QRPC_ABORT_PARSER (ch != 't', "'sat' or 'unsat' expected");
  QRPC_ABORT (num_steps == 0, "invalid proof: no steps given");
  QRPC_ABORT (start_sidx == 0, "invalid proof: no empty clause/cube given");

  if (size_steps > num_steps + 1)
  {
    QRPC_REALLOC (steps, size_steps, num_steps + 1);
    size_steps = num_steps + 1;
    if (options.print_statistics)
      statistics.num_realloc_steps += 1;
  }
  if (size_vars > num_vars + 1)
  {
    QRPC_REALLOC (vars, size_vars, num_vars + 1);
    size_vars = num_vars + 1;
    if (options.print_statistics)
      statistics.num_realloc_vars += 1;
  }
  if (options.print_statistics)
  {
    statistics.num_vars = num_vars;
    statistics.num_steps_total = num_steps;
    statistics.size_vars = size_vars;
    statistics.size_vidx2id = size_vidx2id;
    statistics.size_mark_occs = size_vars;
    statistics.size_steps = size_steps;
    statistics.size_sidx2id = size_sidx2id;
  }

  free (sidx2id);
  sidx2id = NULL;
}


#ifndef NPICOSAT
static void
parse_qdimacs (char *filename_qdimacs, char *in_qdimacs, long in_qdimacs_size)
{
  unsigned int i, cnt_clauses = 0;
  ClauseId *occs_tmp;
  Lit *tmp;

  p.filename = filename_qdimacs;
  p.in = in_qdimacs;
  p.in_size = in_qdimacs_size;

  p.pos = 0;
  p.line = 1;
  p.col = 0;
  
  p.is_qrp = 0;
  
  p.read_number = &parse_ascii_num;
  p.read_literal = &parse_ascii_lit;

  STACK_INIT (universals, (num_vars >> 2) + 1);
  
  parse_preamble ();
  parse_scopes ();

  STACK_INIT (occs, num_clauses << 1);
  if (options.print_statistics)
  {
    statistics.num_realloc_stack_occs += 1;
    statistics.num_realloc_stack_universals += 1;
  }

  while (ch != EOF)
  {
    ch = tolower (ch);
    QRPC_ABORT_PARSER (ch == QDIMACS_EXISTS || ch == QDIMACS_FORALL,
                       "clause expected, found quantified set");
    if (cnt_clauses == num_clauses)
    {
      QRPC_REALLOC (clauses, num_clauses, cnt_clauses + 1);
      num_clauses = cnt_clauses + 1;
      if (options.print_statistics)
        statistics.num_realloc_clauses += 1;
    }

    clauses[cnt_clauses].id = (ClauseId) cnt_clauses;
    clauses[cnt_clauses].lits = p.in + p.pos - 1;
    parse_literals (cnt_clauses);
    cnt_clauses += 1;
    SKIP_SPACE_DO_WHILE;
  }

  QRPC_REALLOC (occurrences, 0, num_occurrences);
  if (options.print_statistics)
    statistics.num_realloc_occurrences += 1;

  occs_tmp = occurrences;
  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].num_pos_occs)
    {
      vars[i].pos_occs = occs_tmp;
      occs_tmp += vars[i].num_pos_occs;
      vars[i].num_pos_occs = 0;
    }
    if (vars[i].num_neg_occs)
    {
      vars[i].neg_occs = occs_tmp;
      occs_tmp += vars[i].num_neg_occs;
      vars[i].num_neg_occs = 0;
    }
  }
  for (i = 0, tmp = occs.bp; i < cnt_clauses; i++, tmp++)
  {
    for (; *tmp != EOL; tmp++)
    {
      if (*tmp > 0)
        vars[*tmp].pos_occs[vars[*tmp].num_pos_occs++] = i;
      else
        vars[-*tmp].neg_occs[vars[-*tmp].num_neg_occs++] = i;
    }
  }

  if (options.print_statistics)
  {
    statistics.size_clauses = num_clauses;
    statistics.size_occurrences = num_occurrences;
    statistics.size_stack_occs = occs.size;
    statistics.size_stack_universals = universals.size;
    statistics.size_stack_initial_cubes = initial_cubes.size;
  }
  
  STACK_RELEASE (occs);
}
#endif

/* -------------------------- end Parser ------------------------------ */


static void
cleanup (void)
{
  if (vidx2id != NULL)
    free (vidx2id);
  if (sidx2id != NULL)
    free (sidx2id);
  if (vars != NULL)
    free (vars);
  if (steps != NULL)
    free (steps);
  if (mark_occs != NULL)
    free (mark_occs);
#ifndef NPICOSAT
  if (occurrences != NULL)
    free (occurrences);
  if (clauses != NULL)
    free (clauses);
  STACK_RELEASE (initial_cubes);
  STACK_RELEASE (universals);
  STACK_RELEASE (occs);
#endif
  STACK_RELEASE (res_lits);
  if (in_qrp != NULL)
    munmap (in_qrp, in_qrp_size);
#ifndef NPICOSAT
  if (in_qdimacs != NULL)
    munmap (in_qdimacs, in_qdimacs_size);
#endif
}


