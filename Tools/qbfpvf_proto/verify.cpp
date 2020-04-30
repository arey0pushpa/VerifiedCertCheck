#include "common.h"
#include "lexer.h"



class Variable {
private:
  lit_int_t v;

public:
  inline explicit Variable(lit_int_t _v) : v(_v) { assert (v>=0); };

  inline size_t idx() const {return static_cast<size_t>(v);};
  inline string str() const {return to_string(v);}

  inline lit_int_t raw() const {return v; }

  inline bool operator ==(Variable const&var) const {return v==var.v;};
  inline bool operator !=(Variable const&var) const {return v!=var.v;};

  inline bool in_bounds(size_t num_vars) const {return idx()<=num_vars; }

  inline bool is_valid() const {return v!=0;}

public:
  static Variable const invalid;

};

Variable const Variable::invalid = Variable(0);



class Literal {
private:
  lit_int_t l;

public:
  inline Literal() : l(0) {};
  inline explicit Literal(lit_int_t _l) : l(_l) {};
  inline explicit Literal(Variable const&v) : l(v.raw()) {}

  inline bool is_valid() const {return l!=0;}


  inline string str() const {return std::to_string(l);}

  inline lit_int_t raw() const {return l;}

  inline bool operator ==(Literal const&lit) const {return l==lit.l;};
  inline bool operator !=(Literal const&lit) const {return l!=lit.l;};
//   inline bool operator <(Literal const&lit) const {return abs(l) < abs(lit.l); };

  inline Literal neg() const { assert(is_valid()); return Literal(-l);}
  inline Literal operator -() const {return neg();}

  Variable var() const {return Variable(abs(l));}

  static Literal const invalid;

  inline bool in_bounds(size_t num_vars) const {return var().in_bounds(num_vars); }



};

Literal const Literal::invalid = Literal(0);

enum class Quant {
  ALL,
  EX
};

// Map from everything that can be converted to size_t.
// T must default-initialize to T::invalid, and have an is_valid() method

inline size_t to_size_t(size_t x) {return x;}
inline size_t to_size_t(Variable v) {return v.idx();}



template<typename K,typename V> class Basic_Int_Cnv_Map {
private:
  vector<V> map;

public:
  inline V lookup(K key) const {
    size_t i = to_size_t(key);
    if (i<map.size()) return map[i]; else return V();
  }

  inline V& define(K key) {
    size_t i = to_size_t(key);
    if (!(i<map.size())) map.resize(i+1);
    return map[i];
  }

  inline K next_key() const {return K(map.size());}

  inline K define_next(V const &v) {
    K res = K(map.size());
    map.push_back(v);
    return res;
  }

  inline void print_stats(string name) {
    log(name+": " + pretty_vector_stats(map));
  }


};





template<typename K,typename V> class Int_Cnv_Map : public Basic_Int_Cnv_Map<K,V> {
public:
  inline bool contains(K k) const {
    return (this->lookup(k).is_valid());
  }

  inline V const& the_lookup(K k) const {
    assert(contains(k));
    return this->lookup(k);
  }

  inline V& the_lookup(K k) {
    assert(contains(k));
    return this->define(k);
  }

  inline void remove(K k) {
    the_lookup(k) = V();
  }

  inline void remove_if_ex(K k) {
    if (contains(k)) remove(k);
  }


};


template<typename T> class Basic_Varmap : public Basic_Int_Cnv_Map<Variable,T> {};
template<typename T> class Varmap : public Int_Cnv_Map<Variable,T> {};






template<typename T, T invalid_val> class Wrap_Invalid {
private:
  T x = invalid_val;

public:
  inline Wrap_Invalid() : x(invalid_val) {}
  inline Wrap_Invalid(T _x) : x(_x) {}
  inline operator T() const {return x;}

  inline bool is_valid() const {return x!=invalid_val;}
};


template<typename T, T invalid_val> class Wrap_Invalid_Expl {
private:
  T x = invalid_val;

public:
  inline Wrap_Invalid_Expl() : x(invalid_val) {}
  explicit inline Wrap_Invalid_Expl(T _x) : x(_x) {}
  explicit inline operator T() const {return x;}

  inline bool is_valid() const {return x!=invalid_val;}
};


class ClauseDB {
private:

  // Quantifiers
  Varmap<Wrap_Invalid<size_t,0>> varpos; // Counting starts at 1, zero for invalid variable
  size_t cur_pos = 1;
  Basic_Varmap<Quant> varq; // Quantifier of variable

  Variable max_var = Variable::invalid;


public:
  inline size_t get_pos(Variable v) {
    return varpos.the_lookup(v);
  }

  inline bool is_valid(Variable v) {
    return varpos.contains(v);
  }

  inline Quant get_q(Variable v) {
    assert(is_valid(v));
    return varq.lookup(v);
  }

  inline Quant get_q(Literal l) {
    return get_q(l.var());
  }

  inline void add_var(Quant q, Variable v) {
    if (varpos.contains(v)) error("Duplicate variable declaration " + v.str());
    varpos.define(v) = cur_pos++;
    varq.define(v) = q;

    if (v.idx()>max_var.idx()) max_var=v;
  }

  Variable get_maxvar() {
    return max_var;
  }


  // Literals are ordered by variable position
  inline bool less_lit(Literal l1, Literal l2) {
    return get_pos(l1.var()) < get_pos(l2.var());
  }


public:
  typedef Wrap_Invalid_Expl<size_t,0> ClauseId;
  typedef Wrap_Invalid_Expl<size_t,SIZE_MAX> Clause_Iterator;


private:
  // Clauses
  vector<Literal> db;  // The clause database
  Int_Cnv_Map<ClauseId,Clause_Iterator> idmap; // Map from clause IDs to start positions in database.

  size_t last_clause_start = SIZE_MAX;
  Quant reduceq = Quant::EX; // Quantifier on which reduction can be performed
  bool initialized=false;

  bool contains_empty_flag = false; // True if this contains the empty clause

  size_t db_max = 0;


public:
  // Create clause
  inline void start_clause() {
    assert(initialized);
    assert(last_clause_start == SIZE_MAX);
    last_clause_start = db.size();
  }

  // returns argument. Makes for more elegant parsing loops.
  inline Literal add_lit(Literal l) {
    assert(initialized);
    assert(last_clause_start!= SIZE_MAX);
    if (l.is_valid()) db.push_back(l); // Ignore final 0, will be added by commit-clause

    db_max = max(db_max,db.capacity());

    return l;
  }

  inline void discard_clause() {
    assert(initialized);
    assert(last_clause_start!= SIZE_MAX);
    assert(last_clause_start <= db.size());
    db.resize(last_clause_start);
    last_clause_start = SIZE_MAX;
  }

  // Note: If clause is not sorted, sort must be true.
  inline ClauseId commit_clause(bool sort, bool reduce=true) {
    assert(initialized);
    assert(last_clause_start!= SIZE_MAX);
    assert(last_clause_start <= db.size());

    if (sort) {
      std::sort(db.begin() + last_clause_start, db.end(),[this](Literal a, Literal b){return less_lit(a,b);});
    }

    if (reduce) {
      // Find new ending position
      size_t i = db.size();

      while (i>last_clause_start && get_q(db[i-1]) == reduceq) --i;

      db.resize(i);
    }

    if (last_clause_start==db.size()) contains_empty_flag=true;

    // Append terminator 0
    db.push_back(Literal::invalid);
    db_max = max(db_max,db.capacity());

    ClauseId res = idmap.define_next(Clause_Iterator(last_clause_start));
    last_clause_start = SIZE_MAX;

    return res;
  }

  inline ClauseId cur_id() {return idmap.next_key();}

  inline void remove(ClauseId cid) {
    idmap.remove(cid);
    // TODO trigger garbage collection when too empty (e.g. more than half of the clauses deleted.
    //    Counting literals (i.e. db storage space) may be more precise, but requires a num-literals field, or literal counting on removal)
    //    Literal count of clause may be given as hint, as it will be known from previous resolution step anyway!
  }


  inline Clause_Iterator lookup(ClauseId cid) {
    if (!idmap.contains(cid)) error("Invalid clause/cube id: " + to_string((size_t)cid));
    return idmap.the_lookup(cid);
  }

  inline Literal ci_peek(Clause_Iterator it) {
    assert((size_t)it < db.size());
    return db[(size_t)it];
  }

  inline bool ci_at_end(Clause_Iterator it) {
    return !ci_peek(it).is_valid();
  }

  inline Literal ci_next(Clause_Iterator &it) {
    Literal res=ci_peek(it);
    it=Clause_Iterator((size_t)it + 1);
    return res;
  }

  inline bool contains_empty() {return contains_empty_flag;}



  ClauseId resolution(ClauseId cid1, ClauseId cid2) {

    auto ci1 = lookup(cid1);
    auto ci2 = lookup(cid2);

    start_clause();

    /* Merge, eliminating duplicates, and allowing one resolution.
     *
     * This assumes that the clauses are sorted (which is an invariant for all clauses in the db)
     */
    bool seen_res_lit=false;

    while (!ci_at_end(ci1) && !ci_at_end(ci2)) {
      Literal l1 = ci_peek(ci1);
      Literal l2 = ci_peek(ci2);

      if (less_lit(l1,l2)) {  // l1 < l2
        add_lit(l1);
        ci_next(ci1);
      } else if (l1 == l2) {
        add_lit(l1);
        ci_next(ci1);
        ci_next(ci2);
      } else if (l1 == -l2) {
        if (seen_res_lit) error("Resolution yields tautology: literal " + l1.str());
        ci_next(ci1);
        ci_next(ci2);
        seen_res_lit=true;
      } else {
        add_lit(l2);
        ci_next(ci2);
      }
    }

    // Handle rest
    while (!ci_at_end(ci1)) add_lit(ci_next(ci1));
    while (!ci_at_end(ci2)) add_lit(ci_next(ci2));

    if (!seen_res_lit) error("No resolution"); // We make this an error, though it would be sound to simply combine two clauses without resolution

    // Commit clause. Reduce. Sorting not required, b/c already sorted due to merge of sorted clauses.
    return commit_clause(false,true);


  }


public:
  ClauseDB() {}

  void initialize(Quant _reduceq) {
    assert(!initialized);

    reduceq = _reduceq;

    // Clause-ID 0 does not exist. We just add an invalid ID here.
    [[maybe_unused]]ClauseId id0 = idmap.define_next(Clause_Iterator());
    assert((size_t)id0 == 0);

    initialized=true;
  }


  void print_stats() {
    varpos.print_stats("varpos map");
    varq.print_stats("varq map");
    idmap.print_stats("id map");

    log("max clause db: " + pretty_size(db_max * sizeof(Literal)));
  }


};

inline size_t to_size_t(ClauseDB::ClauseId cid) {return (size_t)cid;}


/*
 * Parallel Valuation. Uses bit-vectors to store multiple valuations in parallel.
 *   Bit-vectors fit into machine-words here.
 */
class ParValuation {

public:
    typedef uint64_t mask_t;

private:

  static_assert(numeric_limits<mask_t>::is_integer,"");
  static_assert(!numeric_limits<mask_t>::is_signed,"");

  static const size_t bit_width = sizeof(mask_t)*8;
  static const mask_t max_mask = ((mask_t)1)<<(bit_width-1);

private:
  mask_t cur_mask=1; // Bit that is currently added. 0 when full.

private:
  size_t n = 0;
  mask_t *base = NULL;
  mask_t *m = NULL;

  ParValuation(ParValuation const &) = delete;
  ParValuation &operator=(ParValuation const &) = delete;


private:
  inline bool in_range(Literal l) {return (size_t)(abs(l.raw())) <= n;}

public:

  void clear() {
    assert(m);
    fill(base,base+(2*n+1),0);
    cur_mask=1;
  }

  void init(size_t _n) {
    assert(!m && _n>0);
    n=_n;
    base = new mask_t[2*n+1];
    m = base + n;
    clear();

    log("Using deferred initial cube checking, bit_width = " + to_string(bit_width));
  }

  void init(Variable max_var) { init(max_var.idx()); }



  ParValuation() {}
  ParValuation(size_t _n) { init(_n); }
  ~ParValuation() { if (base) delete [] base;}


  // Getting and setting literals
  inline void set(Literal l) {
    assert(m);
    assert(in_range(l));

    auto li = l.raw();
    assert((m[-li]&cur_mask) == 0);

    m[li]|=cur_mask;
  }

  inline mask_t get(Literal l) {
    assert(m && in_range(l));
    auto i = l.raw();
    return m[i];
  }

  // Management of remaining slots
  inline bool is_full() {
    return cur_mask == 0;
  }

  inline bool is_empty() {
    return cur_mask==1;
  }

  inline void next_slot() {
    assert(!is_full());
    cur_mask<<=1;
  }

  // All used bits
  inline mask_t bits() {
    return cur_mask-1;
  }

public:
  void print_stats() {
    log("Par-Valuation: " + pretty_size((2*n+1)*sizeof(mask_t)));
  }

};





class Initial_Cube_Checker {
private:
  vector<Literal> clauses;
  ParValuation val;

//  ClauseDB &db;

public:

//  inline Initial_Cube_Checker(ClauseDB &_db) : db(_db) {}

// Disabled, as this causes funny double-exceptions when error is thrown in flush_checks()
//   inline ~Initial_Cube_Checker() {
//     flush_checks();
//   }

  // Must be called before cubes can be checked. Literals can be added earlier.
  inline void init(Variable max_var) {
    val.init(max_var);
  }


  // Add literals and 0s of formula's clauses
  inline Literal add_fml_lit(Literal l) {clauses.push_back(l); return l;}

  // Add next literal of a cube
  inline void add_cube_lit(Literal l) {
    assert(!val.is_full());
    val.set(l);
  }

  // Declare current cube as finished (and get ready for next one)
  inline void commit_cube() {
    val.next_slot();
    if (val.is_full()) flush_checks();
  }

//   inline void check_cube(ClauseDB::Clause_Iterator cid) {
//     if (val.is_full()) flush_checks();
//     assert(!val.is_full());
//
//     // Initialize this slot of parallel valuation with cube's literals
//     clog<<"icube "<<endl;
//     for (;!db.ci_at_end(cid);db.ci_next(cid)) {
//       clog<<db.ci_peek(cid).str()<<" ";
//       val.set(db.ci_peek(cid));
//     }
//     clog<<"0"<<endl;
//
//     val.next_slot();
//   }

  inline void flush_checks() {
    if (val.is_empty()) return; // Nothing to check

    ParValuation::mask_t bits = val.bits();

    // The outer loops iterates over the clauses, consuming the final zero in each increment step
    for (auto it = clauses.begin(); it!=clauses.end();++it) {
      ParValuation::mask_t m=0;

      // Accumulate valuation over literals of clause
      while (it->is_valid()) {
        m|=val.get(*it);
        ++it;
        assert(it!=clauses.end());
      }

      // Check
      if (m != bits) {
        // clog<<m<<" != "<<bits<<endl;
        error("Initial cube check failed");
      }
    }

    // Everything checked. Flush.
    val.clear();
  }

  void print_stats() {
    log("ICC formula clauses: " + pretty_vector_stats(clauses));
  }


};



class Verifier {
private:
  MMap_Range fml_range;
  MMap_Range prf_range;

  Lexer plx;

  ClauseDB db;

  Initial_Cube_Checker icc;


  size_t prf_first_id = 0;
  bool sat_mode = false;
  bool verified = false;


public:
  Verifier(string dimacs_file, string proof_file) : fml_range(dimacs_file), prf_range(proof_file), plx(prf_range), db(), icc() { }

  inline bool is_sat() {assert(verified); return sat_mode;}


// Parsing
private:
  void parse_prf_header() {
    plx.eol();
    plx.keyword("p");
    plx.keyword("redcqrp");
    prf_first_id = plx.unsafe_id_int();
    plx.eol();

    plx.keyword("r");
    {
      string s = plx.word();
      if (s=="SAT") sat_mode=true;
      else if (s=="UNSAT") sat_mode=false;
      else error("Unknown mode: " + s);
      plx.eol();
    }

    // Initialize db
    db.initialize(sat_mode? Quant::EX : Quant::ALL);
  }

  static inline Literal parse_literal(Lexer &lx) { return Literal(lx.lit_int()); }
  static inline Literal parse_unsafe_literal(Lexer &lx) { return Literal(lx.unsafe_lit_int()); }

  void parse_formula() {
    Lexer lx(fml_range);

    // Header (Everything ignored)
    lx.eol();
    lx.keyword("p");
    lx.keyword("cnf");
    lx.id_int();
    lx.id_int();
    lx.eol();

    // Variable declarations
    while (true) {
      // Parse quantifier, break if no more quantifiers
      Quant q;
      if (lx.peek()=='e') q=Quant::EX;
      else if (lx.peek()=='a') q=Quant::ALL;
      else break;
      lx.next(); lx.eow();

      // Parse variable list
      {
        lit_int_t v;

        while (true) {
          v = lx.var_int();
          if (v==0) break;
          db.add_var(q,Variable(v));
        }
      }

      lx.eol();
    }

    if (sat_mode) icc.init(db.get_maxvar());

    // Clauses
    while (!lx.is_eof()) {

      if (sat_mode) {
        // Parse formula clauses to their own database
        while (icc.add_fml_lit(parse_literal(lx)).is_valid()) {};
        lx.eol();
      } else {
        // Parse formula clauses to main database
        db.start_clause();
        while (db.add_lit(parse_literal(lx)).is_valid()) {};

        lx.eol();

        // Sort and reduce
        db.commit_clause(true,true);
      }
    }

    // Check match of implicit IDs

    if ((size_t)db.cur_id() != prf_first_id) {
      error("Current ID after parsing formula ("+to_string((size_t)db.cur_id())+") "
          + "does not match start ID declared in proof header ("+to_string(prf_first_id)+")");
    }



  }


  inline auto parse_delid() {
    bool del = plx.peek()=='d';
    if (del) plx.next();

    return make_pair(ClauseDB::ClauseId(plx.unsafe_id_int()), del);
  }

  void parse_proof() {

    while (!plx.is_eof() && !db.contains_empty()) {

      if (plx.peek() == '0') {
        // Initial cube
        plx.unsafe_id_int(); // Skip the zero

        if (!sat_mode) error("Initial cube step in SAT mode");

        // Read cube, and add all its literals to cube checker.
        // NOTE we must add all literals. Some of them may be lost after reduction upon commit_clause.
        db.start_clause();
        while (true) {
          Literal l = Literal(plx.lit_int());
          if (!l.is_valid()) break;
          db.add_lit(l);
          icc.add_cube_lit(l);
        }

        plx.eol();

        // Commit cube to cube checker
        icc.commit_cube();

        // Commit cube to DB (sorts and reduces)
        db.commit_clause(true,true);

      } else {
        // Resolution step
        auto [cid1,del1] = parse_delid();
        auto [cid2,del2] = parse_delid();
        plx.eol();

        db.resolution(cid1,cid2);

        if (del1) db.remove(cid1);
        if (del2) db.remove(cid2);
      }
    }

    if (sat_mode) icc.flush_checks();

    if (!db.contains_empty()) error("Found no empty clause/cube");

    if (!plx.is_eof()) log("Proof file contains additional content after empty clause/cube was produced");

  }


public:
  void do_check() {
    parse_prf_header();
    parse_formula();
    parse_proof();

    verified=true;
  }

  void print_stats() {
    db.print_stats();
    if (sat_mode) icc.print_stats();
  }



};


int main(int argc, char **argv) {
  try {


    if (argc != 3) error("Usage: verify <qdimacs-file> <proof-file>");

    Verifier vrf(argv[1],argv[2]);

    vrf.do_check();

    if (vrf.is_sat()) cout<<"s SAT"<<endl;
    else cout<<"s UNSAT"<<endl;

    vrf.print_stats();

    return 0;

  } catch (exception &e) {
    cout<<"s ERROR"<<endl;
    cerr<<e.what()<<endl;
    return 1;
  };

}

