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

#include <assert.h>
#include <ctype.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "qrpcert.h"
#include "qrpcert_version.h"

static PType proof_type = PTYPE_UNDEF;
static VertexId empty_vertex = 0;
static FILE *out = NULL;
static Var *vars = NULL;
static unsigned vars_size = 0;
static Vertex *vertices = NULL;
static unsigned vertices_size = 0;
static VarId *map_var = NULL;
static unsigned map_var_size = 0;
static VertexId *map_c2v = NULL;
static unsigned map_c2v_size = 0;
static char *var_lookup = NULL;
static VarId max_var_index = 0;
static unsigned num_vars = 0;
static unsigned num_vertices = 0;
static unsigned num_vertices_compact = 0;
static unsigned num_vertices_pushed = 0;
static unsigned num_vertices_simplified = 0;
static unsigned long long num_literals = 0;
static unsigned long long num_literals_pushed = 0;
static unsigned long long num_literals_simplified = 0;
static QRPCertStatistics statistics;

/* QRPcert default options  */
static QRPCertOptions options = 
  {
    .print_rfao = 0,
    .statistics = 0,
    .simplify = 0,
    .extract = 0,
    .incr_size = 0,
    .aiger_binary = 1,
    .out_filename = NULL,
  };

static QRPReader reader = 
  {
    .line = 1,
    .col = 0,
    .qrp_binary = 0,
    .delim = QRP_DELIM,
    .getch = get_non_ws_ch,
    .getnextch = stdin_getnextch,
    .getnum = qrp_read_num,
    .getlit = qrp_read_lit,
    .filename = "stdin",
    .mmap = NULL,
    .mmap_size = 0,
    .mmap_pos = 0,
  };

static void
print_usage (void)
{
  printf ("qrpcert [<options>] [<file>]\n\n");
  printf ("  file:\n");
  printf ("    QBF resolution proof or trace in QRP format ");
  printf ("(stdin if not given)\n\n");
  printf ("  options:\n");
  printf ("    -o <filename>      name of the output file (default: stdout)\n");
  printf ("    -e <string>        only extract functions for given list of ");
  printf ("variables,\n");
  printf ("                       any non-digit character is treated as ");
  printf ("separator\n");
  printf ("    -i <num><unit>     write AIG incrementally to file if it ");
  printf ("exceeds given size \n");
  printf ("                       in unit: M (megabyte), G (gigabyte). ");
  printf ("option -o required\n");
  printf ("    -p, --print-rfao   print RFAO stacks, increase incrementally\n");
  printf ("                       level 1: print only vertex ids\n");
  printf ("                       level 2: print literals of vertices\n");
  printf ("    --simplify         enable constant propagation\n");
  printf ("    --aiger-ascii      write AIG in AIGER ASCII format\n");
  printf ("    -s, --statistics   show statistics\n");
  printf ("    -h, --help         print this message and exit\n");
  printf ("    --version          print version and exit\n");
}

static void
print_version (void)
{
  printf ("%s\n", QRPCERT_VERSION);
}

static void
print_statistics (simpleaig *aig)
{
  simpleaigstats aigstats;
  simpleaig_statistics (aig, &aigstats);
  unsigned long long num_ands_total;

  fprintf (stderr, "----- PROOF STATISTICS -----\n");
  STATS ("variables (ex./un.)", "%u (%u/%u)", num_vars,
          statistics.num_ex_vars, statistics.num_un_vars);
  STATS ("vertices (core proof)", "%u (%u)", num_vertices, 
         statistics.num_vertices_core);
  STATS ("literals (core proof)", "%llu (%llu)", num_literals,
         statistics.num_literals_core);
  STATS ("vertices with reduction", "%u", num_vertices_compact);
  STATS ("literals removed by reduction", "%llu",
         statistics.num_reduced_literals);

  fprintf (stderr, "\n----- %s FUNCTIONS STATISTICS -----\n",
           (proof_type == PTYPE_SAT) ? "SKOLEM" : "HERBRAND");
  STATS ("functions repr. variables", "%u", statistics.num_var_functions);
  STATS ("functions repr. constants", "%u", statistics.num_const_functions);
  STATS ("don't cares (unused variables)", "%u", statistics.num_dont_cares);
  STATS ("literals (simplified)", "%llu (-%llu)", 
         num_literals_pushed - num_literals_simplified,
         num_literals_simplified);
  STATS ("vertices (simplified)", "%u (-%u)", 
         num_vertices_pushed - num_vertices_simplified, 
         num_vertices_simplified);

  num_ands_total = aigstats.num_ands + statistics.num_ands_skipped + 
                   aigstats.num_ands_shared;
  fprintf (stderr, "\n----- AIG STATISTICS -----\n");
  STATS ("inputs", "%u", aig->num_inputs);
  STATS ("outputs", "%u", aig->num_outputs);
  STATS ("and gates (shared/shared %)", "%llu (%llu/%.2f%%)", 
         aigstats.num_ands, num_ands_total - aigstats.num_ands,
         (num_ands_total > 0) 
         ? (double) (num_ands_total - aigstats.num_ands) / num_ands_total * 100
         : 0);
  STATS ("and gates without sharing", "%llu", num_ands_total);

  fprintf (stderr, "\n----- AIG HASHING STATISTICS -----\n");
  STATS ("alloc. buckets (empty/empty %)", "%u (%u/%.2f%%)", 
         aigstats.num_buckets, aigstats.num_empty_buckets,
         (double) aigstats.num_empty_buckets / aigstats.num_buckets * 100);
  STATS ("avg. bucket count (min./max.)", "%.1f (%u/%u)", 
          aigstats.avg_bucket_cnt, aigstats.min_bucket_cnt, 
          aigstats.max_bucket_cnt);
  STATS ("avg. bucket size (min./max.)", "%.1f (%u/%u)", 
          aigstats.avg_bucket_size, aigstats.min_bucket_size, 
          aigstats.max_bucket_size);

  fprintf (stderr, "\n----- MEMORY STATISTICS -----\n");
  STATS ("variables", "%.1f %s", XiB (num_vars * sizeof (Var)), 
         XiBSTR (num_vars * sizeof (Var)));
  STATS ("vertices", "%.1f %s", XiB (num_vertices * sizeof (Vertex)),
         XiBSTR (num_vertices * sizeof (Vertex)));
  STATS ("literals (used/alloc)", "%.1f/%.1f %s", 
         XiB (num_literals * sizeof (Lit)),
         XiB (statistics.size_literals * sizeof (Lit)),
         XiBSTR (statistics.size_literals * sizeof (Lit)));
  STATS ("compacted vertices", "%.1f %s",
         XiB (num_vertices_compact * sizeof (Vertex)),
         XiBSTR (num_vertices_compact * sizeof (Vertex)));
  STATS ("compacted literals (used/alloc)", "%.1f/%.1f %s", 
         XiB (statistics.num_literals_compact * sizeof (Lit)),
         XiB (statistics.size_literals_compact * sizeof (Lit)),
         XiBSTR (statistics.size_literals_compact * sizeof (Lit)));
  STATS ("RFAO stacks (used/alloc)", "%.1f/%.1f %s",
         XiB ((num_vertices_pushed - num_vertices_simplified) * 
              sizeof (VertexId)),
         XiB (statistics.size_rfaos * sizeof (VertexId)),
         XiBSTR (statistics.size_rfaos * sizeof (VertexId)));
  STATS ("AIG (used/alloc)", "%.1f/%.1f %s",
         XiB (aigstats.mem_total_used - aigstats.mem_hash_used),
         XiB (aigstats.mem_total_alloc - aigstats.mem_hash_alloc),
         XiBSTR (aigstats.mem_total_alloc - aigstats.mem_hash_alloc));
  STATS ("hash table (used/alloc)", "%.1f/%.1f %s",
         XiB (aigstats.mem_hash_used), XiB (aigstats.mem_hash_alloc),
         XiBSTR (aigstats.mem_hash_alloc));

  fprintf (stderr, "\n----- TIME STATISTICS -----\n");
  STATS ("parse", "%.3fs (%.2f%%)", statistics.time_parsing, 
         (double) statistics.time_parsing / statistics.time_total * 100);
  STATS ("mark vertices", "%.3fs (%.2f%%)", statistics.time_mark, 
         (double) statistics.time_mark / statistics.time_total * 100);
  STATS ("sort literals", "%.3fs (%.2f%%)", statistics.time_sort, 
         (double) statistics.time_sort / statistics.time_total * 100);
  STATS ("extract functions", "%.3fs (%.2f%%)", 
         statistics.time_extract,
         (double) statistics.time_extract / statistics.time_total * 100);
  STATS ("simplify functions", "%.3fs (%.2f%%)", 
         statistics.time_simplify,
         (double) statistics.time_simplify / statistics.time_total * 100);
  STATS ("compact vertices", "%.3fs (%.2f%%)", statistics.time_compact,
         (double) statistics.time_compact / statistics.time_total * 100);
  STATS ("generate AIGER certificate", "%.3fs (%.2f%%)", 
         statistics.time_generating,
         (double) statistics.time_generating / statistics.time_total * 100);
  STATS ("write to file", "%.3fs (%.2f%%)", statistics.time_writing, 
         (double) statistics.time_writing / statistics.time_total * 100);
  STATS ("total", "%.3fs", statistics.time_total);
}

static double
get_time (void)
{
  double time = 0;
  struct rusage ru;

  if (!getrusage (RUSAGE_SELF, &ru))
  {
    time += ru.ru_utime.tv_sec + 1e-6 * ru.ru_utime.tv_usec;
    time += ru.ru_stime.tv_sec + 1e-6 * ru.ru_stime.tv_usec;
  }

  return time;
}

/**
 * Compute reference count of each vertex in the proof. This cannot be done 
 * while parsing, as the input file may contain resolution steps that are not 
 * required for deriving the empty vertex (traces).
 */
static void
compute_ref_cnts ()
{
  unsigned i;
  VertexId vid;
  VertexIdStack visit;

  STACK_INIT (visit, 32);
  PUSH (visit, empty_vertex);

  while (!STACK_IS_EMPTY (visit))
  {
    POP (visit, vid);

    if (vertices[vid].num_refs == 0)
    {
      for (i = 0; i < vertices[vid].num_ants; i++)
        PUSH (visit, vertices[vid].ants[i]);
    }

    vertices[vid].num_refs += 1;
  }

  STACK_FREE (visit);
}

static void
compact_vertices ()
{
  assert (map_c2v == NULL);

  unsigned i, j, num_vertices_tmp = 1;
  VertexId vid;
  Vertex *vertices_tmp = NULL;

  QRPCERT_REALLOC (vertices_tmp, num_vertices_compact + 1, 0, 0);
  QRPCERT_REALLOC (map_c2v, num_vertices + 1, 0, 0);

  for (i = 1; i <= num_vertices; i++)
  {
    if (options.statistics)
      statistics.size_literals += vertices[i].lits_size;

    if (!vertices[i].reduced)
    {
      free (vertices[i].lits);
      continue;
    }

    if (options.statistics)
      statistics.size_literals_compact += vertices[i].lits_size;

    map_c2v[i] = num_vertices_tmp;
    assert (num_vertices_tmp <= num_vertices_compact);
    memcpy (vertices_tmp + num_vertices_tmp, vertices + i, sizeof (Vertex));
    num_vertices_tmp += 1;
  }

  /* update vertex indices on RFAO stacks  */
  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].rfao_stack.bp == NULL)
      continue;

    for (j = 0; j < STACK_CNT (vars[i].rfao_stack); j++)
    {
      vid = vars[i].rfao_stack.bp[j];
      vars[i].rfao_stack.bp[j] = (vid < 0) ? -map_c2v[-vid] : map_c2v[vid];
    }
  }
  empty_vertex = map_c2v[empty_vertex];

  free (vertices);
  vertices = vertices_tmp;
}

static void
parse_options (int argc, char **argv)
{
  int i;
  char *str;

  for  (i = 1; i < argc; i++)
  {
    str = argv[i];

    if (strcmp (str, "-h") == 0 || strcmp (str, "--help") == 0)
    {
      print_usage ();
      exit (EXIT_SUCCESS); 
    }
    else if (strcmp (str, "--version") == 0)
    {
      print_version ();
      exit (EXIT_SUCCESS);
    }
    else if (strcmp (str, "-o") == 0)
    {
      QRPCERT_ABORT (i + 1 >= argc, "missing file name for -o");
      options.out_filename = argv[++i];
      QRPCERT_ABORT (options.out_filename[0] == '-', 
                     "missing file name for -o");
      out = fopen (options.out_filename, "w");
      QRPCERT_ABORT (out == NULL, "failed to open output file '%s'", 
                     options.out_filename);
    }
    else if (strcmp (str, "-p") == 0 || strcmp (str, "--print-rfao") == 0)
    {
      options.print_rfao += 1;
    }
    else if (strcmp (str, "-e") == 0)
    {
      unsigned j;
      unsigned num = 0;
      QRPCERT_ABORT (i + 1 >= argc, "missing value for -e");

      STACK_INIT (options.extract_vars, 8);
      str = argv[++i];

      for (j = 0; j <= strlen (str); j++)
      {
        /* everything that is not a digit is a separator  */
        if (!isdigit (str[j]))
        {
          if (num > 0)
          {
            PUSH (options.extract_vars, num);
            num = 0;
          }
          continue;
        }
        num = num * 10 + (str[j] - '0'); 
      }

      options.extract = 1;
      QRPCERT_ABORT (STACK_CNT (options.extract_vars) == 0, 
                     "no variables for extraction given");
    }
    else if (strcmp (str, "-i") == 0)
    {
      QRPCERT_ABORT (i + 1 >= argc, "missing value for -i");
      QRPCERT_ABORT (argv[++i][0] == '-', "missing value for -i");
      str = argv[i];
      unsigned len = strlen (str);

      if (tolower (str[len - 1]) == 'm')
      {
        str[len - 1] = '\0';
        options.incr_size = (unsigned) atoi (str) * 1024 * 1024;
      }
      else if (tolower (str[len - 1]) == 'g')
      {
        str[len - 1] = '\0';
        options.incr_size = (unsigned) atoi (str) * 1024 * 1024 * 1024;
      }
      else
        QRPCERT_ABORT (1, "invalid unit '%c' for -i given", str[len - 1]);
    }
    else if (strcmp (str, "-s") == 0 || strcmp (str, "--statistics") == 0)
    {
      memset (&statistics, 0, sizeof (QRPCertStatistics));
      options.statistics = 1;
    }
    else if (strcmp (str, "--simplify") == 0)
    {
      options.simplify = 1;
    }
    else if (strcmp (str, "--aiger-ascii") == 0)
    {
      options.aiger_binary = 0;
    }
    else if (str[0] == '-')
    {
      QRPCERT_ABORT (1, "invalid option '%s'", str); 
    }
    else
    {
      int in_mmap_fd;
      struct stat s;

      in_mmap_fd = open (str, O_RDONLY); 
      QRPCERT_ABORT (in_mmap_fd == -1, "failed to open input file '%s'", str);
      QRPCERT_ABORT (fstat (in_mmap_fd, &s) == -1,
                     "failed to get file status of '%s'", str);
      reader.mmap_size = s.st_size;
      reader.mmap = (char *) mmap (0, reader.mmap_size, PROT_READ, 
                                   MAP_PRIVATE | MAP_NORESERVE, in_mmap_fd, 0);
      QRPCERT_ABORT (reader.mmap == MAP_FAILED, "failed to mmap input file");
      close (in_mmap_fd);

      reader.getnextch = mmap_getnextch;
      reader.filename = str;
    }
  }

  QRPCERT_ABORT (options.out_filename == NULL && options.incr_size > 0,
                 "inremental write mode is only available with option -o");
  QRPCERT_ABORT (options.incr_size > 0 && options.aiger_binary,
                 "incremental write mode only available with --ascii-aiger");
}

static void
sort_literals (void)
{
  unsigned i, j, pos;
  Lit lit;

  for (i = 1; i <= num_vertices; i++)
  {
    /* skip vertices that are not part of the proof or have only one literal  */
    if (vertices[i].num_refs == 0 || vertices[i].num_lits <= 1)
      continue;

    for (j = 1; j < vertices[i].num_lits; j++)
    {
      lit = vertices[i].lits[j];
      pos = vertex_literal_insert_pos (i, lit, 0, j - 1); 

      assert (abs (lit) > 0);
      assert (pos < vertices[i].num_lits);
      assert (pos != j || lit == vertices[i].lits[pos]);

      /* already in position  */
      if (pos == j)
        continue;

      assert (abs (lit) < abs (vertices[i].lits[pos]));
      assert (j - pos > 0);

      memmove (vertices[i].lits + pos + 1, vertices[i].lits + pos, 
               (j - pos) * sizeof (Lit));

      vertices[i].lits[pos] = lit;
    }
  }
}

int
main (int argc, char **argv)
{
  unsigned i;
  double t;
  simpleaig *aig;

  out = stdout;

  parse_options (argc, argv);

  if (options.statistics)
    statistics.time_parsing = get_time ();

  parse_qrp ();

  /* check if variables for extraction are valid  */
  if (options.extract)
  {
    VarId v;
    for (i = 0; i < STACK_CNT (options.extract_vars); i++)
    {
      v = options.extract_vars.bp[i];
      QRPCERT_ABORT (v < 0 || v > max_var_index || map_var[v] == 0, 
                     "given variable '%u' to extract does not exist in proof", 
                     v);
      QRPCERT_ABORT (vars[map_var[v]].type != REDUCTION_TYPE,
                     "cannot extract %s variable '%d' from %s proof",
                     (proof_type == PTYPE_SAT) ? "universal" : "existential",
                     v, (proof_type == PTYPE_SAT) ? "SAT" : "UNSAT");
      vars[map_var[v]].extract = 1;
    }
  }

  free (map_var);
  map_var = NULL;

  QRPCERT_ABORT (empty_vertex == 0, "incomplete proof, empty %s not found",
                 proof_type == PTYPE_SAT ? "cube" : "clause");
  QRPCERT_ABORT (vertices[empty_vertex].num_ants == 0, 
                 "incomplete derivation of empty %s",
                 proof_type == PTYPE_SAT ? "cube" : "clause");

  if (options.statistics)
    TIMER (statistics.time_parsing, statistics.time_mark);

  compute_ref_cnts ();

  if (options.statistics)
    TIMER (statistics.time_mark, statistics.time_sort);
  
  sort_literals ();

  assert (assert_literals_sorted ());

  if (options.statistics)
    TIMER (statistics.time_sort, statistics.time_extract);

  extract_functions ();

  assert (assert_static_literals_sorted ());
  assert (assert_reduced_literals_sorted ());
  assert (assert_reduced_literals_type ());

  if (options.statistics)
    TIMER (statistics.time_extract, statistics.time_simplify);

  simplify_functions ();

  assert (!options.simplify || assert_literals_simplified ());
  assert (!options.simplify || assert_vertices_simplified ());

  if (options.statistics)
    TIMER (statistics.time_simplify, statistics.time_compact);

  compact_vertices ();

  if (options.statistics)
    TIMER (statistics.time_compact, statistics.time_generating);

  aig = simpleaig_init ();
  /* set start index for new AND gates, start with max_var_index + 1 to prevent
   * overwriting existing input/output indices  */
  aig->lhs_aux = max_var_index + 1;

  if (options.incr_size > 0)
    generate_aiger_certificate_incremental (aig);
  else
    generate_aiger_certificate (aig);

  if (options.statistics)
  {
    statistics.time_total = get_time ();
    print_statistics (aig);
  }

  simpleaig_reset (aig);
  cleanup ();

  return EXIT_SUCCESS;
}

static void
var_init (VarId id, QType type, int s_level)
{
  if (id > max_var_index)
  {
    QRPCERT_REALLOC (map_var, id + 1, map_var_size, 0);
    map_var_size = id + 1;
    max_var_index = id;
  }

  if (num_vars + 1 >= vars_size)
  {
    QRPCERT_REALLOC (vars, vars_size + 1, vars_size, QTYPE_UNDEF);
    vars_size += 1;
  }

  if (options.statistics)
  {
    if (type == QTYPE_EXISTS)
      statistics.num_ex_vars += 1;
    else
      statistics.num_un_vars += 1;
  }

  assert (map_var[id] == 0);

  VarId vid = ++num_vars;
  map_var[id] = vid;
  memset (vars + vid, 0, sizeof (Var));

  vars[vid].id = id;
  vars[vid].type = type;
  vars[vid].s_level = s_level;
  vars[vid].val = BTYPE_UNDEF;
  vars[vid].extract = (options.extract) ? 0 : 1;
}

static VertexId 
vertex_init (VertexId id)
{
  assert (map_c2v != NULL);
  
  VertexId vid;

  if ((unsigned) id >= map_c2v_size)
  {
    QRPCERT_REALLOC (map_c2v, id * 1.5 + 1, map_c2v_size, 0);
    map_c2v_size = id * 1.5;
  }

  if (num_vertices + 1 >= vertices_size)
  {
    QRPCERT_REALLOC (vertices, vertices_size * 1.5 + 1, vertices_size, 0);
    vertices_size *= 1.5;
  }

  /* already initialized  */
  if (map_c2v[id] != 0)
    return map_c2v[id];

  /* initialize vertex  */
  vid = ++num_vertices;
  map_c2v[id] = vid;
  memset (vertices + vid, 0, sizeof (Vertex));

  vertices[vid].id = id;
  vertices[vid].lits_size = 4;
  QRPCERT_REALLOC (vertices[vid].lits, vertices[vid].lits_size, 0, 0);
  vertices[vid].val = BTYPE_UNDEF;

  return vid;
}

static void
vertex_add_antecedent (VertexId id, VertexId aid)
{
  assert (vertices[id].num_ants <= 2);
  vertices[id].ants[vertices[id].num_ants] = aid;
  vertices[id].num_ants += 1;
}

static inline unsigned 
vertex_literal_insert_pos (VertexId vid, Lit lit, int low, int high)
{
  int mid;
  Lit l, lmid;

  l = abs (lit);

  while (low <= high)
  {
    mid = (low + high) / 2;
    lmid = abs (vertices[vid].lits[mid]);

    if (l < lmid)
      high = mid - 1;
    else if (l > lmid)
      low = mid + 1;
    else
      return mid;
  }

  return low;
}

static void
vertex_add_literal (VertexId vid, Lit lit)
{
  unsigned pos, new_size, old_size;

  assert (!vertices[vid].reduced);

  if (vertices[vid].num_lits == vertices[vid].lits_size)
  {
    old_size = vertices[vid].lits_size;
    new_size = old_size + (old_size >> 2) + 1;
    QRPCERT_REALLOC (vertices[vid].lits, new_size, old_size, 0); 
    vertices[vid].lits_size = new_size;
  }

  assert (vertices[vid].num_lits + 1 <= vertices[vid].lits_size);

  pos = vertices[vid].num_lits;
  vertices[vid].lits[pos] = lit;
  vertices[vid].num_lits += 1;
  vertices[vid].num_lits_static += 1;

  if (vars[abs (lit)].type == QTYPE_EXISTS && 
      vertices[vid].innermost_e < abs (lit))
    vertices[vid].innermost_e = abs (lit);
  else if (vars[abs (lit)].type == QTYPE_FORALL &&
           vertices[vid].innermost_a < abs (lit))
    vertices[vid].innermost_a = abs (lit);

  assert (vertices[vid].num_lits_static == vertices[vid].num_lits);
}

static inline void
vertex_add_reduced_literal (VertexId vid, Lit lit)
{
  unsigned pos, new_size, old_size;

  if (vertices[vid].num_lits == vertices[vid].lits_size)
  {
    old_size = vertices[vid].lits_size;
    new_size = old_size + (old_size >> 2) + 1;
    QRPCERT_REALLOC (vertices[vid].lits, new_size, old_size, 0); 
    vertices[vid].lits_size = new_size;
  }

  assert (vertices[vid].num_lits + 1 <= vertices[vid].lits_size);

  /* get insert position in static literals  */
  pos = vertex_literal_insert_pos (vid, lit, 0, 
                                   vertices[vid].num_lits_static - 1);

  if (vertices[vid].lits[pos] == lit)
  {
    /* if pos == num_lits_static, then lit is already reduced  */
    assert (pos <= vertices[vid].num_lits_static);

    /* only delete lit if it is not the last lit  */
    if (pos < vertices[vid].num_lits_static)
    {
      /* nothing to move, delete lit  */
      if (vertices[vid].num_lits == pos + 1)
        vertices[vid].lits[pos] = 0;
      else
      {
        /* delete lit from static literals  */
        memmove (vertices[vid].lits + pos, vertices[vid].lits + pos + 1, 
                 (vertices[vid].num_lits - pos - 1) * sizeof (Lit));
      }
      assert (vertices[vid].lits[pos] != lit);

      vertices[vid].num_lits -= 1;
      vertices[vid].num_lits_static -= 1;
    }
  }

  /* get insert position of lit in reduced literals  */
  pos = vertex_literal_insert_pos (vid, lit, vertices[vid].num_lits_static,
                                   vertices[vid].num_lits - 1);

  assert (vertices[vid].reduced || pos == vertices[vid].num_lits_static);
  assert (vertices[vid].num_lits_static <= pos);
  assert (pos >= vertices[vid].num_lits_static);

  /* mark vertex as reduced  */
  vertices[vid].reduced = 1;

  /* literal already in vertex  */
  if (lit == vertices[vid].lits[pos])
    return;

  /* add sorted  */
  if (abs (lit) < abs (vertices[vid].lits[pos]))
  {
    memmove (vertices[vid].lits + pos + 1, vertices[vid].lits + pos, 
             (vertices[vid].num_lits - pos) * sizeof (Lit));
  }

  vertices[vid].lits[pos] = lit;
  vertices[vid].num_lits += 1;
}

static inline void
vertex_remove_literal (VertexId vid, unsigned pos)
{
  assert (pos < vertices[vid].num_lits);
  vertices[vid].num_lits -= 1;

  /* only move if there are still more literals  */
  if (vertices[vid].num_lits > 1)
  {
    memmove (vertices[vid].lits + pos, vertices[vid].lits + pos + 1,
             (vertices[vid].num_lits - pos) * sizeof (Lit));
  }

  if (pos < vertices[vid].num_lits_static)
    vertices[vid].num_lits_static -= 1;
}


static BType 
eval_lit (Lit lit)
{
  BType val = vars[abs (lit)].val;

  if (val == BTYPE_UNDEF)
    return BTYPE_UNDEF;

  if (lit < 0)
    return (val == BTYPE_FALSE) ? BTYPE_TRUE : BTYPE_FALSE;
    
  return val;
}

static BType
simplify_vertex (VertexId vid, unsigned num_lits)
{
  BType val;
  unsigned j;
  Lit lit;

  if (vertices[vid].val != BTYPE_UNDEF)
    return vertices[vid].val;

  j = 0;
  while (j < num_lits)
  {
    lit = vertices[vid].lits[j];
    val = eval_lit (lit);

    if (val == BTYPE_UNDEF)
    {
      j += 1;
      continue;
    }

    /* only literal in vertex defines value of vertex  */
    if (num_lits == 1)
      return val;

    /* clause is true  */
    if (proof_type == PTYPE_UNSAT && val == BTYPE_TRUE)
    {
      if (j < vertices[vid].num_lits_static)
        vertices[vid].val = BTYPE_TRUE;
      return BTYPE_TRUE;
    }

    /* cube is false  */
    if (proof_type == PTYPE_SAT && val == BTYPE_FALSE)
    {
      if (j < vertices[vid].num_lits_static)
        vertices[vid].val = BTYPE_FALSE;
      return BTYPE_FALSE;
    }

    /* true (resp. false) literals in cubes (resp. clauses) can be removed  */
    if (j < vertices[vid].num_lits_static)
      num_literals_simplified += 1;

    assert (num_literals_simplified <= num_literals_pushed);
    vertex_remove_literal (vid, j);
    num_lits -= 1;
  }

  /* empty vertex all literals have been simplified  */
  if (num_lits == 0)
  {
    val = (proof_type == PTYPE_SAT) ? BTYPE_TRUE : BTYPE_FALSE;
    vertices[vid].val = val;
    return val;
  }
    
  return BTYPE_UNDEF;
}

static inline void
var_remove_vertex_at_pos (VarId var, unsigned pos)
{
  assert (pos < STACK_CNT (vars[var].rfao_stack));
  VertexId vid = abs (vars[var].rfao_stack.bp[pos]);

  vertices[vid].num_pushed_refs -= 1;

  if (vertices[vid].num_pushed_refs == 0)
    num_literals_simplified += vertices[vid].num_lits_static;

  assert (num_literals_simplified <= num_literals_pushed);

  /* check if vertices > pos are on the stack  */
  if (pos + 1 < STACK_CNT (vars[var].rfao_stack))
  {
    memmove (vars[var].rfao_stack.bp + pos, 
             vars[var].rfao_stack.bp + pos + 1, 
             (STACK_CNT (vars[var].rfao_stack) - pos - 1) * sizeof (VertexId));
  }
  vars[var].rfao_stack.sp -= 1;
}

static inline void
var_remove_vertices_until_pos (VarId var, unsigned pos)
{
  assert (pos < STACK_CNT (vars[var].rfao_stack));
  unsigned i;
  VertexId vid;

  for (i = 0; i < pos; i++)
  {
    vid = abs (vars[var].rfao_stack.bp[i]);
    vertices[vid].num_pushed_refs -= 1;

    if (vertices[vid].num_pushed_refs == 0)
      num_literals_simplified += vertices[vid].num_lits_static;
  }

  assert (num_literals_simplified <= num_literals_pushed);

  /* check if vertices < pos are on the stack  */
  if (pos > 0)
  {
    memmove (vars[var].rfao_stack.bp, vars[var].rfao_stack.bp + pos, 
             (STACK_CNT (vars[var].rfao_stack) - pos) * sizeof (VertexId));
  }
  vars[var].rfao_stack.sp -= pos;
}

static BType 
simplify_function (VarId var)
{
  assert (var > 0);
  assert ((unsigned) var <= num_vars);
  assert (vars[var].val == BTYPE_UNDEF);

  int i;
  char is_neg, is_clause, next_is_clause;
  unsigned num_lits, num_pushed_lits = 0;
  BType val;
  VertexId vid;

  for (i = 0; i < (int) STACK_CNT (vars[var].rfao_stack); i++)
  {
    is_neg = 0;
    vid = vars[var].rfao_stack.bp[i];

    if (vid < 0)
    {
      vid = -vid;
      is_neg = 1;
    }

    num_lits = vertex_literal_insert_pos (vid, var, 0,
                                          vertices[vid].num_lits_static - 1);
    val = simplify_vertex (vid, num_lits);

    if (val == BTYPE_UNDEF)
      continue;

    if (is_neg)
      val = (val == BTYPE_FALSE) ? BTYPE_TRUE : BTYPE_FALSE;

    is_clause = (proof_type == PTYPE_UNSAT && !is_neg) || 
                (proof_type == PTYPE_SAT && is_neg);

    if (vertices[vid].num_pushed_refs == 1)
      num_pushed_lits += vertices[vid].num_lits;

    /* check innermost term  */
    if (i == 0 && STACK_CNT (vars[var].rfao_stack) > 1)
    {
      vid = vars[var].rfao_stack.bp[i + 1];
      next_is_clause = (proof_type == PTYPE_UNSAT && vid > 0) ||
                       (proof_type == PTYPE_SAT && vid < 0);

      /* clause /\ cur_vertex: true  -> remove cur_vertex  */
      /* cube \/ cur_vertex: false  -> remove cur_vertex  */
      if ((next_is_clause && val == BTYPE_TRUE) || 
          (!next_is_clause && val == BTYPE_FALSE))
      {
        var_remove_vertex_at_pos (var, i);
        i -= 1;
        continue;
      }
      /* clause /\ cur_vertex: false -> remove clause  */
      /* cube \/ cur_vertex: true -> remove cube  */
      else if ((next_is_clause && val == BTYPE_FALSE) ||
               (!next_is_clause && val == BTYPE_TRUE))
      {
        var_remove_vertex_at_pos (var, i + 1);
        i -= 1;
        continue;
      }
    }

    /* cur_vertex: true /\ ( ... ), cur_vertex is clause -> remove cur_vertex
     * cur_vertex: false \/ ( ... ), cur_vertex is cube -> remove cur_vertex  */
    if ((is_clause && val == BTYPE_TRUE) || 
        (!is_clause && val == BTYPE_FALSE) 
        || STACK_CNT (vars[var].rfao_stack) == 1)
    {
      var_remove_vertex_at_pos (var, i);
      i -= 1;

      /* if stack is empty, simplify variable to constant  */
      if (STACK_IS_EMPTY (vars[var].rfao_stack))
          return val;
    }
    /* cur_vertex: false /\ ( ... ), cur_vertex is clause -> remove ( ... )
     * cur_vertex: true \/ ( ... ), cur_vertex is cube -> remove ( ... )  */
    else if ((is_clause && val == BTYPE_FALSE) || 
             (!is_clause && val == BTYPE_TRUE))
    {
      var_remove_vertices_until_pos (var, i);
      i = -1; /* reset to start of stack  */
    }
  }
  
  return BTYPE_UNDEF;
}

static void
simplify_functions (void)
{
  unsigned i, stack_cnt;

  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].rfao_stack.bp == NULL)
      continue;

    /* only simplify if there are variables that may be reduced to constants  */
    if (options.simplify && (vertices[empty_vertex].reduced || 
        vertices[empty_vertex].num_ants == 1))
    {
      stack_cnt = STACK_CNT (vars[i].rfao_stack);
      vars[i].val = simplify_function (i);
      num_vertices_simplified += stack_cnt - STACK_CNT (vars[i].rfao_stack);
    }

    if (options.statistics)
    {
      if (vars[i].val != BTYPE_UNDEF)
        statistics.num_const_functions += 1;
      else
      {
        if (STACK_CNT (vars[i].rfao_stack) == 0)
          statistics.num_dont_cares += 1;
        else
          statistics.num_var_functions += 1;
      }
      statistics.size_rfaos += vars[i].rfao_stack.size;
    }
  }
}

static void
collect_reduced_literals (VertexId vid, VertexId aid, QType type)
{
  unsigned i, num_lits = 0;
  VarId var, pivot = 0, innermost_aid, innermost_vid;
  VertexId v;
  Lit lits_tmp[vertices[aid].num_lits], lit;

  innermost_aid = GET_INNERMOST_VAR(aid);
  innermost_vid = GET_INNERMOST_VAR(vid);
  assert (proof_type != PTYPE_SAT || 
          innermost_aid == vertices[aid].innermost_a);
  assert (proof_type != PTYPE_UNSAT || 
          innermost_aid == vertices[aid].innermost_e);
  assert (proof_type != PTYPE_SAT || 
          innermost_vid == vertices[vid].innermost_a);
  assert (proof_type != PTYPE_UNSAT || 
          innermost_vid == vertices[vid].innermost_e);
  assert (innermost_aid == 0 || vars[innermost_aid].type == PIVOT_TYPE);
  assert (innermost_vid == 0 || vars[innermost_vid].type == PIVOT_TYPE);

  /* find reduced literals  */
  for (i = 0; i < vertices[aid].num_lits; i++)
  {
    lit = vertices[aid].lits[i]; 
    var = abs (lit);
    assert (vars[var].type != QTYPE_UNDEF);

    if ((var_lookup[var] == 0 || (lit > 0 && var_lookup[var] < 0) || 
         (lit < 0 && var_lookup[var] > 0)) && vars[var].type == type)
      lits_tmp[num_lits++] = lit;

    /* find pivot variable  */
    if (var_lookup[var] == 0 && vars[var].type != type)
    {
      assert (pivot == 0);
      assert (vars[var].type == PIVOT_TYPE);
      pivot = var;
    }
  }

  assert (pivot != 0 || vertices[vid].num_ants == 1);
  assert (pivot == 0 || vertices[vid].num_ants == 2);
  assert (pivot <= innermost_aid);

  for (i = 0; i < num_lits; i++)
  {
    lit = lits_tmp[i]; 
    var = abs (lit);

    /* literal reduced before resolution  */
    if (var > innermost_aid)
      v = aid;
    /* literal reduced after resolution  */
    else
    {
      assert (pivot == 0 || pivot == innermost_aid);
      assert (pivot == 0 || pivot != innermost_vid);

      QRPCERT_ABORT (var < innermost_vid,
                     "invalid reduction of literal %d in vertex %d.",
                     (lit < 0) ? -vars[-lit].id : vars[lit].id,
                     vertices[vid].id);
      v = vid;
    }

    vertex_add_reduced_literal (v, lit);
  }
}

static void 
extract_functions ()
{
  unsigned i;
  VertexIdStack visit;
  VertexId vid, aid;
  VarId var;
  Lit lit;
  QType type;

  /* set quantifier type for variables to be extracted  */
  type = REDUCTION_TYPE;

  /* initialize stack of variables  */
  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].type == type)
      STACK_INIT (vars[i].rfao_stack, 4);
  }

  num_vertices_compact = 0;  /* reset - was set in parse_qrp  */
  STACK_INIT (visit, 32);
  PUSH (visit, empty_vertex);
  QRPCERT_REALLOC (var_lookup, num_vars + 1, 0, 0);

  /* traverse dag from start vertex in dfs order */
  while (!STACK_IS_EMPTY (visit))
  {
    POP (visit, vid); 

    assert (vid > 0);
    assert ((unsigned) vid <= num_vertices);
    assert (vertices[vid].num_lits > 0 || vid == empty_vertex);
    assert (vertices[vid].num_refs > 0);

    vertices[vid].num_refs -= 1;

    /* continue if not yet all parents of current vertex are processed  */
    if (vertices[vid].num_refs > 0)
      continue;

    if (options.statistics)
    {
      statistics.num_vertices_core += 1;
      statistics.num_literals_core += vertices[vid].num_lits;
    }

    memset (var_lookup, 0, (num_vars + 1) * sizeof (char));

    /* mark literals in current vertex  */
    for (i = 0; i < vertices[vid].num_lits; i++)
    {
      lit = vertices[vid].lits[i];
      var = abs (lit);
      assert (var_lookup[var] == 0);

      /* save phase of literal  */
      var_lookup[var] = (lit < 0) ? -1 : 1;
    }

    for (i = 0; i < vertices[vid].num_ants; i++)
    {
      aid = vertices[vid].ants[i];
      collect_reduced_literals (vid, aid, type);
      PUSH (visit, aid);
    }

    /* check if current vertex has been reduced  */
    if (vertices[vid].reduced)
    {
      num_vertices_compact += 1;

      if (options.statistics)
      {
        statistics.num_reduced_literals += 
          vertices[vid].num_lits - vertices[vid].num_lits_static;
        statistics.num_literals_compact += vertices[vid].num_lits;
      }

      /* process reduced literals in current vertex  */
      for (i = vertices[vid].num_lits_static; i < vertices[vid].num_lits; i++)
      {
        lit = vertices[vid].lits[i];
        var = abs (lit);
        assert (vars[var].type == type);

        if (lit > 0)
          PUSH (vars[var].rfao_stack, vid);
        else
          PUSH (vars[var].rfao_stack, -vid);

        vertices[vid].num_pushed_refs += 1;
      }
      num_vertices_pushed += 
        vertices[vid].num_lits - vertices[vid].num_lits_static;
      num_literals_pushed += vertices[vid].num_lits_static;
    }
  }

  STACK_FREE (visit);
}

static void
print_vertex (VertexId vid)
{
  char is_neg = 0;
  unsigned i, num_lits;
  Lit lit;

  if (options.print_rfao == 1)
  {
    fprintf (stderr, "%d ", (vid < 0) ? -vertices[-vid].id : vertices[vid].id);
    return;
  }

  if (vid < 0)
  {
    vid = -vid;
    is_neg = 1;
  }

  num_lits = vertices[vid].num_lits_static; 

  if (abs (vertices[vid].lits[num_lits]) == GET_INNERMOST_VAR(vid))
    num_lits += 1;

  if (is_neg)
    fprintf (stderr, "-");
  fprintf (stderr, "( ");

  if (num_lits == 0)
    fprintf (stderr, "%d ", (proof_type == PTYPE_SAT) ? 1 : 0);

  for (i = 0; i < num_lits; i++) 
  {
    lit = vertices[vid].lits[i];
    assert (vars[abs (lit)].val == BTYPE_UNDEF);
    fprintf (stderr, "%c(%d) ",
             (vars[abs (lit)].type == QTYPE_EXISTS) ? 'E' : 'A',
             (lit < 0) ? -vars[-lit].id : vars[lit].id);
  }

  fprintf (stderr, ") ");
}

static int
aig_add_vertex (simpleaig *aig, VertexId vid, VarId output, char is_clause)
{
  assert (aig != NULL);
  assert (abs (vid) > 0 && (unsigned) abs (vid) <= num_vertices);
  assert (vertices[abs (vid)].val == BTYPE_UNDEF);

  int lit = 0, lhs = 0, rhs[2];
  char is_neg = 0;
  unsigned i, num_rhs = 0, num_lits;

  /* check if given vertex is negated  */
  if (vid < 0)
  {
    vid = -vid;
    is_neg = 1;
  }

  assert (vertices[vid].reduced);

  /* AIG of vertex vid already built  */
  if (vertices[vid].aig_out > 0)
  {
    lit = vertices[vid].aig_out;

    if (is_clause)
      lit = simpleaig_not (lit);

    if (output > 0)
      simpleaig_add_and (aig, output, lit, SIMPLEAIG_TRUE);

    return lit;
  }
  num_lits = vertices[vid].num_lits_static; 

  /* vertex with only one literal  */
  if (num_lits == 1 || (!options.simplify && num_lits == 0))
  {
    if (num_lits == 1)
    {
      lit = vertices[vid].lits[0];
      lit = (lit < 0) ? simpleaig_not (vars[-lit].id) : vars[lit].id;
    }
    else
    {
      lit = (proof_type == PTYPE_SAT) ? SIMPLEAIG_TRUE : SIMPLEAIG_FALSE;
    }

    if (is_neg)
      lit = simpleaig_not (lit);

    /* if it's the last vertex in the rfao, add and with out = lit /\ true  */
    if (output > 0)
      simpleaig_add_and (aig, output, lit, SIMPLEAIG_TRUE);

    return lit;
  }
  assert (vertices[vid].aig_out == 0);

  /* construct AIG from vertex  */
  for (i = 0; i < num_lits; i++)
  {
    lit = vertices[vid].lits[i];
    lit = (lit < 0) ? simpleaig_not (vars[-lit].id) : vars[lit].id;

    /* apply de morgan's law if vertex is a clause  
     * no double negation if is_neg && is_clause  */
    if ((is_clause && !is_neg) || (is_neg && !is_clause))
      lit = simpleaig_not (lit);

    rhs[num_rhs++] = lit;

    if (num_rhs == 2)
    {
      /* if output is given and we add the last AND gate, we have to set lhs
       * to output  */
      lhs = (i + 1 == num_lits && output > 0) ? output : SIMPLEAIG_FALSE;
      lhs = simpleaig_add_and (aig, lhs, rhs[0], rhs[1]);
      rhs[0] = lhs; 
      num_rhs = 1;
    }
  }
  assert (lhs > 0);
  vertices[vid].aig_out = lhs;

  /* apply de morgan's law  */
  if (is_clause)
    return simpleaig_not (lhs);

  return lhs;
}

static void
aig_add_function (simpleaig *aig, VarId var)
{
  assert (aig != NULL);

  int lhs, *tmp;
  char finished = 0;
  unsigned i, num_rhs = 0, stack_cnt;
  VertexId vid;

  if (options.print_rfao > 0)
    fprintf (stderr, "RFAO[%d] = ", vars[var].id);

  /* check if variable was simplified to a constant  */
  if (vars[var].val != BTYPE_UNDEF)
  {
    lhs = (vars[var].val == BTYPE_TRUE) ? SIMPLEAIG_TRUE : SIMPLEAIG_FALSE;

    if (options.print_rfao > 0)
      fprintf (stderr, "%d\n", (vars[var].val == BTYPE_TRUE) ? 1 : 0);

    simpleaig_add_and (aig, vars[var].id, lhs, lhs);
    return;
  }

  stack_cnt = STACK_CNT (vars[var].rfao_stack);

  /* RFAO stack is empty, variable not used in proof  */
  if (stack_cnt == 0)
  {
    if (options.print_rfao > 0)
      fprintf (stderr, "empty\n");

    /* variables not required in the proof are not considered  */
    return;
  }
  
  /* RFAO stack contains only one vertex and it is a cube  */
  if (stack_cnt == 1)
  {
    vid = *(vars[var].rfao_stack.bp);

    /* vertex is a cube  */
    if ((proof_type == PTYPE_SAT && vid > 0) || 
        (proof_type == PTYPE_UNSAT && vid < 0))
    {
      if (options.print_rfao > 0)
      {
        print_vertex (vid);
        fprintf (stderr, "\n");
      }
      aig_add_vertex (aig, vid, vars[var].id, 0);
      return;
    }
  }

  int rhs[stack_cnt + 1];
  char rhs_is_clause[stack_cnt + 1];

  /* always set last vertex to true  */
  rhs[stack_cnt] = SIMPLEAIG_TRUE;
  rhs_is_clause[stack_cnt] = 1;

  /* build AIGs from all vertices on RFAO stack, start with innermost vertex  */
  for (tmp = vars[var].rfao_stack.bp; tmp < vars[var].rfao_stack.sp; tmp++)
  {
    vid = *tmp;

    if (options.print_rfao > 0)
      print_vertex (vid);

    /* check if given vertex is a clause  */
    rhs_is_clause[num_rhs] = (proof_type == PTYPE_SAT && vid < 0) || 
                             (proof_type == PTYPE_UNSAT && vid > 0);

    rhs[num_rhs] = aig_add_vertex (aig, vid, SIMPLEAIG_FALSE, 
                                   rhs_is_clause[num_rhs]);
    num_rhs += 1;
  }

  if (options.print_rfao > 0)
    fprintf (stderr, "\n");

  i = 0;
  while (!finished)
  {
    assert (i < num_rhs);
    /* set output of function to var if last vertex is a:
     * clause: F[var] = clause AND aig
     * cube:   F[var] = not(not(cube) AND not(aig)) AND true  */
    if ((rhs_is_clause[num_rhs - 1] && i + 2 >= num_rhs) ||
        (!rhs_is_clause[num_rhs - 1] && i + 1 >= num_rhs))
    {
      lhs = vars[var].id;
      finished = 1;
    }
    else
    {
      lhs = SIMPLEAIG_FALSE;
    }

    /* determine boolean operator for RFAO: clause AND ..., cube OR ... 
     * second rhs determines boolean operator  */
    if (rhs_is_clause[i + 1])  /* clause AND RFAO  */
    {
      lhs = simpleaig_add_and (aig, lhs, rhs[i + 1], rhs[i]);
    }
    else  /* cube OR RFAO  */
    {
      /* apply de morgan's law  */
      lhs = simpleaig_add_and (aig, lhs, simpleaig_not (rhs[i + 1]), 
                               simpleaig_not (rhs[i]));
      lhs = simpleaig_not (lhs);
    }
      
    rhs[i + 1] = lhs;
    i += 1;
  }
}

static void
generate_aiger_certificate (simpleaig *aig)
{
  assert (aig != NULL);

  unsigned i;
  double t;
  QType type;

  type = REDUCTION_TYPE;

  simpleaig_set_buckets (aig, 
    (unsigned) num_literals_pushed - num_literals_simplified + 
    num_vertices_pushed + 1);

  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].type == type)
    {
      if (!vars[i].extract)
        continue;

      /* only add variables required in the proof (skip don't cares)  */
      if (STACK_CNT (vars[i].rfao_stack) > 0 || vars[i].val != BTYPE_UNDEF)
        simpleaig_add_output (aig, vars[i].id);

      aig_add_function (aig, i);
    }
    else
    {
      simpleaig_add_input (aig, vars[i].id);
    }
  }

  if (options.statistics)
    TIMER (statistics.time_generating, statistics.time_writing);

  simpleaig_write_aiger_to_file (aig, out, options.aiger_binary);

  if (options.statistics)
    statistics.time_writing = get_time () - statistics.time_writing;
}

static void
generate_aiger_certificate_incremental (simpleaig *aig)
{
  assert (aig != NULL);

  unsigned i, buckets_size; 
  size_t ands_size;
  double t = 0;
  QType type;

  type = REDUCTION_TYPE;

  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].type == type)
    {
      if (!vars[i].extract)
        continue;

      /* only add var as output, if it is needed in the proof  */
      if (STACK_CNT (vars[i].rfao_stack) > 0 || vars[i].val != BTYPE_UNDEF)
        simpleaig_add_output (aig, vars[i].id);
    }
    else
    {
      simpleaig_add_input (aig, vars[i].id); 
    }
  }

  if (options.statistics)
    statistics.time_writing = get_time ();

  simpleaig_write_aiger_header (aig, out, options.aiger_binary, 1);
  simpleaig_write_aiger_ios (aig, out);

  if (options.statistics)
    statistics.time_writing = get_time () - statistics.time_writing; 

  buckets_size = options.incr_size / sizeof (simpleaigand) + 1;
  ands_size = options.incr_size + 1;
  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].type != type)
      continue;

    if (!vars[i].extract)
      continue;

    /* write constructed functions to file and reset data structures  */
    if (ands_size > options.incr_size)
    {
      if (options.statistics)
        t = get_time ();

      simpleaig_write_aiger_ands (aig, out);

      if (options.statistics)
        statistics.time_writing += get_time () - t;

      simpleaig_reset_ands (aig);
      simpleaig_set_buckets (aig, buckets_size); 
    }

    aig_add_function (aig, i);
    ands_size = aig->num_ands * sizeof (simpleaigand);
  }

  if (options.statistics)
    t = get_time ();

  simpleaig_write_aiger_ands (aig, out);
  simpleaig_write_aiger_header (aig, out, options.aiger_binary, 0);

  if (options.statistics)
  {
    statistics.time_writing += get_time () - t;
    statistics.time_generating = get_time () - statistics.time_generating - 
                                 statistics.time_writing;
  }
}

static void 
cleanup (void)
{
  unsigned i;

  if (reader.mmap != NULL)
    munmap (reader.mmap, reader.mmap_size);
  if (out != NULL)
    fclose (out);
  if (vars != NULL)
  {
    for (i = 1; i <= num_vars; i++)
    {
      if (vars[i].rfao_stack.bp != NULL)
        STACK_FREE (vars[i].rfao_stack);
    }
    free (vars);
  }
  if (vertices != NULL)
  {
    for (i = 1; i <= num_vertices_compact; i++)
      free (vertices[i].lits);

    free (vertices);
  }
  if (map_var != NULL)
    free (map_var);
  if (map_c2v != NULL)
    free (map_c2v);
  if (var_lookup != NULL)
    free (var_lookup);
  if (options.extract)
    STACK_FREE (options.extract_vars);
}

/* parser functions  */
static void
parse_qrp (void)
{
  char *str;
  unsigned i;
  VertexId max_vertex_index;

  parse_preamble (&max_var_index, &max_vertex_index);

  QRPCERT_REALLOC (map_var, max_var_index + 1, 0, 0);
  map_var_size = max_var_index + 1;
  QRPCERT_REALLOC (vars, max_var_index + 1, 0, QTYPE_UNDEF);
  vars_size = max_var_index + 1;
  QRPCERT_REALLOC (map_c2v, max_vertex_index + 1, 0, 0);
  map_c2v_size = max_vertex_index + 1;
  QRPCERT_REALLOC (vertices, max_vertex_index + 1, 0, 0);
  vertices_size = max_vertex_index + 1;

  parse_qsets ();
  parse_vertices ();
  num_vertices_compact = num_vertices;  /* set in case abort cleanup  */

  /* resize data structures  */
  assert (vertices_size >= num_vertices);
  QRPCERT_REALLOC (vertices, num_vertices + 1, vertices_size, 0);

  /* reset reader.getch in order to skip whitespaces again (binary format)  */
  reader.getch = get_non_ws_ch;

  /* parse result line  */
  QRPCERT_PABORT (reader.ch != QRP_RESULT, "result line expected");

  if (tolower (reader.getch ()) == QRP_RESULT_S)
  {
    str = QRP_RESULT_SAT;
    proof_type = PTYPE_SAT;
  }
  else if (tolower (reader.ch) == QRP_RESULT_U)
  {
    str = QRP_RESULT_UNSAT;
    proof_type = PTYPE_UNSAT;
  }
  else
    QRPCERT_PABORT (1, "invalid result statement '%d'", reader.ch);

  for (i = 1; str[i] != '\0'; i++)
  {
    QRPCERT_PABORT (tolower (reader.getch ()) != str[i], 
                    "invalid result statement, '%s' expected", str);
  }

  free (map_c2v);
  map_c2v = NULL;

  if (reader.mmap != NULL)
  {
    munmap (reader.mmap, reader.mmap_size);
    reader.mmap = NULL;
  }
}

static void
parse_preamble (VarId *max_var_index, VertexId *max_vertex_index)
{
  assert (max_var_index != NULL);
  assert (max_vertex_index != NULL);

  char *str;
  unsigned i;

  QRPCERT_PABORT (reader.getch () == EOF, "empty file given");

  /* skip comments  */
  while (reader.ch == QRP_COMMENT)
  {
    while (reader.getnextch () != '\n' && reader.ch != EOF);
    reader.getch ();
  }

  /* preamble  */
  QRPCERT_PABORT (reader.ch != QRP_PREAMBLE, "missing preamble");

  str = QRP_PREAMBLE_QRP;
  for (i = 0; str[i] != '\0'; i++)
  {
    reader.getch ();
    if (i == 0 && reader.ch != str[i])
    {
      reader.qrp_binary = 1;
      str = QRP_PREAMBLE_BQRP;
    }
    QRPCERT_PABORT (reader.ch != str[i], 
                    "invalid preamble, '%s' expected", str);
  }

  *max_var_index = reader.getnum ();
  *max_vertex_index = reader.getnum ();

  if (reader.qrp_binary)
  {
    reader.delim = BQRP_DELIM;
    reader.getch = reader.getnextch;  /* do not skip whitespaces  */
    reader.getnum = bqrp_read_num;
    reader.getlit = bqrp_read_lit;
  }
}

static void
parse_qsets (void)
{
  unsigned s_level = 1;
  QType type;

  /* reader.ch contains either '\n' or BQRP_DELIM  */
  for (;;)
  {
    /* check beginning of binary quantifiers set  */
    if (reader.qrp_binary && reader.getch () != reader.delim)
      break;
    
    /* get quantifier symbol  */
    reader.getch ();

    if (reader.ch == QRP_FORALL)
      type = QTYPE_FORALL;
    else if (reader.ch == QRP_EXISTS)
      type = QTYPE_EXISTS;
    else if (reader.qrp_binary)
      QRPCERT_PABORT (1,"quantifier set expected");
    else
      break;

    /* reader.ch contains QRP_FORALL or QRP_EXISTS  */
    /* parse variables in quantifier set  */
    while (reader.getch () != reader.delim)
      var_init (reader.getnum (), type, s_level);

    s_level += 1;
  }

  /* no quantifier set parsed  */
  QRPCERT_PABORT (s_level == 1, "quantifier set expected");
}

static void
parse_vertices (void)
{
  VertexId vid, aid;

  QRPCERT_PABORT (reader.ch == BQRP_DELIM, "no vertices given");
  
  assert (var_lookup == NULL);
  QRPCERT_REALLOC (var_lookup, num_vars + 1, 0, 0);

  /* reader.ch contains first digit of first vertex id  */
  for (;;)
  {
    vid = vertex_init (reader.getnum ());
    QRPCERT_PABORT (vertices[vid].num_lits != 0, "duplicate step index '%d'", 
                    reader.num);

    memset (var_lookup, 0, (num_vars + 1) * sizeof (char));

    /* parse literals  */
    /* reader.ch contains either a whitespace or last digit of vid  */
    for (;;)
    {
      if (reader.getch () == reader.delim)
        break;

      reader.getlit ();

      QRPCERT_PABORT (reader.num > (unsigned) max_var_index, 
                      "invalid literal '%d' in step '%d'", 
                      reader.lit, vertices[vid].id);

      QRPCERT_PABORT (vars[map_var[reader.num]].type == QTYPE_UNDEF, 
                      "free variable '%d' in step '%d'", reader.num, 
                      vertices[vid].id);

      if (var_lookup[map_var[abs (reader.lit)]] == 1)
        continue;

      var_lookup[map_var[abs (reader.lit)]] = 1;

      vertex_add_literal (vid, reader.lit < 0 ? -map_var[-reader.lit] 
                                              : map_var[reader.lit]); 
      num_literals += 1;
    }

    /* parse antecedents  */
    /* reader.ch contains reader.delim  */
    for (;;)
    {
      if (reader.getch () == reader.delim)
        break;

      aid = vertex_init (reader.getnum ());
      QRPCERT_PABORT (vertices[vid].num_ants >= 2, 
                      "invalid number of antecedents at step '%d'", aid);

      vertex_add_antecedent (vid, aid);
    }

    /* empty clause/cube  */
    if (vertices[vid].num_lits == 0)
    {
      assert (empty_vertex == 0);
      empty_vertex = vid;
    }

    /* reader.ch contains reader.delim  */
    reader.getch ();

    if ((!reader.qrp_binary && reader.ch == QRP_RESULT) || reader.ch == EOF)
      break;

    /* check for binary result statement  */
    if (reader.qrp_binary && reader.ch == reader.delim)
    {
      if (reader.getch () == QRP_RESULT || reader.ch == EOF)
        break;
    }
  }
}

static int
get_non_ws_ch (void)
{
  /* get next non whitespace character  */
  while (isspace (reader.getnextch ()));

  return reader.ch;
}

static int
stdin_getnextch (void)
{
  reader.ch = getc (stdin);

  if (reader.ch == '\n') 
  {
    reader.line += 1;
    reader.col = 0;
  }
  else
    reader.col += 1;

  return reader.ch;
}

static int
mmap_getnextch (void)
{
  if (reader.mmap_pos == reader.mmap_size)
    reader.ch = EOF;
  else
    reader.ch = (unsigned char) reader.mmap[reader.mmap_pos++];

  if (reader.ch == '\n') 
  {
    reader.line += 1;
    reader.col = 0;
  }
  else
    reader.col += 1;

  return reader.ch;
}

static unsigned
bqrp_read_num (void)
{
  unsigned i = 0;

  /* get first byte if not already parsed  */
  if (reader.ch == reader.delim)
    reader.getch ();

  reader.num = 0;
  for (;;)
  {
    QRPCERT_PABORT (reader.ch == EOF, "unexpected EOF");
    if (!(reader.ch & 0x80))
      break;

    reader.num |= (reader.ch & 0x7f) << (7 * i++);
    reader.getch ();
  }

  reader.num = reader.num | (reader.ch << (7 * i));
  return reader.num;
}

static Lit 
bqrp_read_lit (void)
{
  reader.getnum ();

  if (reader.num & 1)
    reader.lit = -(reader.num >> 1);
  else
    reader.lit = reader.num >> 1;

  /* save var  */
  reader.num = reader.num >> 1;

  return reader.lit;
}

static unsigned
qrp_read_num (void)
{
  /* get first digit if not already parsed  */
  if (!isdigit (reader.ch))
    reader.getch ();

  reader.num = 0;
  do
  {
    if (!isdigit (reader.ch))
      QRPCERT_PABORT (1, "digit expected");
    reader.num = reader.num * 10 + (reader.ch - '0');
  }
  while (!isspace (reader.getnextch ()) &&
         (!reader.qrp_binary || reader.ch != BQRP_DELIM));
  /* reader.ch != BQRP_DELIM required for preamble parsing  */

  return reader.num;
}

static Lit
qrp_read_lit (void)
{
  int neg;

  if (isspace (reader.ch))
    reader.getch ();

  neg = reader.ch == MINUS;
  reader.getnum ();
  reader.lit = neg ? -reader.num : reader.num;
  return reader.lit;
}

#ifndef NDEBUG
static int
assert_literals_sorted (void)
{
  unsigned i, j;

  for (i = 1; i <= num_vertices; i++)
  {
    if (vertices[i].num_refs == 0 || vertices[i].num_lits <= 1)
      continue;

    for (j = 1; j < vertices[i].num_lits; j++)
      assert (abs (vertices[i].lits[j - 1]) < abs (vertices[i].lits[j]));
  }
  return 1;
}

static int 
assert_static_literals_sorted (void)
{
  unsigned i, j;

  for (i = 1; i <= num_vertices; i++)
  {
    if (vertices[i].num_lits_static <= 1 || !vertices[i].reduced)
      continue;

    for (j = 1; j < vertices[i].num_lits_static; j++)
      assert (abs (vertices[i].lits[j - 1]) < abs (vertices[i].lits[j]));
  }
  return 1;
}

static int 
assert_reduced_literals_sorted (void)
{
  unsigned i, j;

  for (i = 1; i <= num_vertices; i++)
  {
    if (!vertices[i].reduced)
      continue;

    if (vertices[i].num_lits - vertices[i].num_lits_static <= 1)
      continue;

    for (j = vertices[i].num_lits_static + 1; j < vertices[i].num_lits; j++)
      assert (abs (vertices[i].lits[j - 1]) < abs (vertices[i].lits[j]));
  }
  return 1;
}

static int
assert_reduced_literals_type (void)
{
  unsigned i, j;
  QType type = REDUCTION_TYPE;

  for (i = 1; i <= num_vertices; i++)
  {
    if (!vertices[i].reduced)
      continue;

    for (j = vertices[i].num_lits_static; j < vertices[i].num_lits; j++)
      assert (vars[abs (vertices[i].lits[j])].type == type);
  }
  return 1;
}

static int
assert_literals_simplified (void)
{
  unsigned i, j, k;
  VertexId vid;

  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].rfao_stack.bp == NULL)
      continue;

    for (j = 0; j < STACK_CNT (vars[i].rfao_stack); j++)
    {
      vid = abs (vars[i].rfao_stack.bp[j]);
      for (k = 0; k < vertices[vid].num_lits; k++)
      {
        if ((unsigned) abs (vertices[vid].lits[k]) >= i)
          break;
        assert (vars[abs (vertices[vid].lits[k])].val == BTYPE_UNDEF);
      }
    }
  }
  return 1;
}

static int
assert_vertices_simplified (void)
{
  unsigned i, j;

  for (i = 1; i <= num_vars; i++)
  {
    if (vars[i].rfao_stack.bp == NULL)
      continue;

    for (j = 0; j < STACK_CNT (vars[i].rfao_stack); j++)
      assert (vertices[abs (vars[i].rfao_stack.bp[j])].val == BTYPE_UNDEF);
  }
  return 1;
}
#endif
