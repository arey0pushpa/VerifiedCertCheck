// Second attempt ...

#include <iostream>
#include <fstream>
#include <cassert>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <boost/format.hpp>

#define BOOST_STACKTRACE_USE_ADDR2LINE
#include <boost/stacktrace.hpp>

#include <boost/iostreams/device/mapped_file.hpp>


using namespace std;

class error_e : public exception {
  string msg;

public:
  error_e() : msg("") {}
  error_e(string _msg) : msg(_msg) {}

  void specify(string m) {
    if (msg != "") msg = m + " >> " + msg;
  }

  virtual const char *what() const throw() {
    return msg.c_str();
  };

};


[[noreturn]] void error(string msg) {
//   cout<<"s ERROR "<<msg<<endl;
//
//   cerr<<boost::stacktrace::stacktrace()<<endl;
//
//   exit(1);

  throw error_e(msg);

}

[[noreturn]] void error(boost::format fmt) {error (fmt.str());}

template<typename T> bool can(T op) {
  try { op(); return true; } catch (error_e &) {return false;}
}


int loglevel = 0;

void log(int level, string msg) {
  if (level<=loglevel) {
    if (level==0) cout<<"c "<<msg<<endl;
    else clog<<"c ("<<level<<") "<<msg<<endl;
  }
}

void log(int level, ostringstream const &msg) {log(level,msg.str()); }

void log(string msg) {log(0,msg);}
// void log(ostringstream &msg) {log(0,msg);}
// void log(ostringstream const &msg) {log(0,msg);}


string pretty_size(size_t s) {
  char const *orders [] = {"B","KiB","MiB","GiB","TiB",nullptr};

  size_t i=0;

  while (s>1024 && orders[i+1]) {
    s/=1024;
    ++i;
  }

  return to_string(s)+orders[i];
}

template<typename T> string pretty_vector_stats(vector<T> const &v) {
  return pretty_size(v.size()*sizeof(T)) + "("+ pretty_size(v.capacity()*sizeof(T)) +")";
}



// For internal use. Wrap into Variable or Literal as soon as possible!
typedef int32_t lit_int_t;
typedef size_t id_int_t;

static_assert(!numeric_limits<id_int_t>::is_signed,"");
static_assert(numeric_limits<id_int_t>::max() > numeric_limits<lit_int_t>::max(),"");


class Lexer;

class MMap_Range {
  friend Lexer;
private:
  // Range to be parsed
  char const *begin = nullptr;
  char const *end = nullptr;

private:
  boost::iostreams::mapped_file_source file;

public:
  MMap_Range(string fname) : file(fname) {
    if (!file.is_open()) error("Error opening file '" + fname + "'"); // Is this check required?

    begin = file.data();
    end = file.data() + file.size();
  }

  ~MMap_Range() {
    file.close();  // Is this required, or done automatically by destructor of file?
  }

};



/*
 * Provides a stream of numbers, parsed from a range in memory.
 *
 * A lexer is constructed from a range, and, optionally, a position
 */
class Lexer {
private:
  char const *begin = nullptr;  // Start of range (probably only needed for error message generation)
  char const *cur = nullptr;    // Current character
  char const *end = nullptr;    // End of range

public:
  string position_context() {
    char const *b = cur-begin>50?cur-50:begin;
    char const *e = end-cur>50?cur+50:end;

    ostringstream res;
    for (char const *i = b; i!=e; ++i) {
      if (i==cur) res<<'|';
      res<<*i;
    }
    return res.str();
  }


protected:

  [[noreturn]] void error(string msg) {
    size_t pos = end - cur;
    ::error("Parser error at position: " + to_string(pos) + ": " + msg + " [context '" + position_context() + "']");
  }


private:
  Lexer(Lexer const&) = delete;
  Lexer &operator=(Lexer const&) = delete;


public:
  // A stored position. Together with the range, the lexer can be re-initialized from this data
  class Position {
    friend Lexer;

  private:
    char const *p;
    inline Position(char const *_p) :p(_p) {}
    inline operator char const *() const {return p;}
    inline operator char const *&() {return p;}

  public:
    inline bool is_invalid() {return p==nullptr;}

    static Position invalid;

  };

public:
  inline Lexer(MMap_Range const &r) : begin(r.begin), cur(r.begin), end(r.end) { assert (begin <= end); }
  inline Lexer(MMap_Range const &r, Position p) : begin(r.begin), cur(p), end(r.end) { assert (begin <= p && p <= end); }

  inline Position get_pos() {return cur;}
  inline void set_pos(Position pos) {cur=pos;}

  // Primitives
  inline bool is_eof() { assert(cur<=end); return cur==end;}
  inline char peek() { if (is_eof()) error("unexpected EOF"); return *cur;}
  inline char next() { if (is_eof()) error("unexpected EOF"); return *(cur++); }

  // Derived
  inline void expect(char c) { if (next() != c) error("Expected " + to_string(c)); }
  inline void expect(string s) { for (char c : s) expect(c); }

  inline string word() {
    ostringstream res;
    while (!is_eof()) {
      char c = next();
      if (is_whitespace(c)) break;
      res<<c;
    }

    whitespace();
    return res.str();
  }

  inline void keyword(string s) { if (word()!=s) error("Expected keyword '" + s + "'"); }

  inline void rest_of_line() {
    while (!is_eof() && next()!='\n');
  }

  static inline bool is_whitespace(char c) {
    return (c==' ' || c=='\n' || c=='\t' || c=='\f');
  }

  // Eat at least one whitespace, or EOF
  inline void whitespace1() {
    if (is_eof()) return;

    if (!is_whitespace(next())) error("Expected whitespace");
    while (!is_eof() && is_whitespace(peek())) next();
  }

  inline void whitespace() {
    if (is_eof()) return;
    while (!is_eof() && is_whitespace(peek())) next();
  }

  // Eat whitespace and comments
  inline void whitespace_cmt() {
    while (!is_eof()) {
      if (peek()=='c') {rest_of_line(); continue; }
      if (is_whitespace(peek())) {next(); continue; }
      break;
    }
  }


  // Numbers
  /*
   * We provide to sets of parsers. The safe parsers will do overflow checks etc, to ensure that the input is syntactically correct.
   * The unsafe parsers do no checks, their guarantee is: if there is a syntactically valid entity, it will be returned.
   *  Otherwise, an arbitrary value may be returned. Note that both, safe and unsafe parsers, must never result in undefined behavior though!
   *
   * The rationale behind this is as follows: when parsing an input formula, we want to ensure that it is syntactically correct,
   * to avoid confusion and ambiguity caused by claiming to have verified some property of a (syntactically malformed) formula.
   * On the other hand, when parsing a proof, we can safely ignore syntax errors:
   * Whenever our interpretation of the proof is a valid proof for the property of the formula, this is fine.
   * Note that, most likely, syntax errors in the proof will result in the proof being rejected by the checker.
   *
   * We hope that omitting the unnecessary checks leads to faster parsing speed.
   *
   */


  // Safe parsers. Use for parsing formulas.
  inline unsigned char digit() {
    char c = next();
    if (c<'0' || c>'9') error(string("expected digit, but got '")+c+"'");
    return c-'0';
  }

  inline id_int_t id_int() {
    static_assert(!numeric_limits<id_int_t>::is_signed,"this impl depends on overflow not causing undef behaviour, i.e., on unsigned type!");

    id_int_t cur=0;

    if (peek() == '0') {
      next();
    } else {
      do {
        id_int_t last = cur;
        cur = cur*10 + digit();
        if (cur < last) error("integer overflow");
      } while (!is_eof() && !is_whitespace(peek()));
    }

    whitespace1();

    return cur;
  }

  inline size_t size_t_int() {
    static_assert(is_same<size_t,id_int_t>(),"");
    return id_int();
  }

  inline lit_int_t var_int() {
    id_int_t res = id_int();
    if (res > static_cast<id_int_t>(numeric_limits<lit_int_t>::max())) error("variable too big");
    return res;
  }

  inline lit_int_t lit_int() {
    lit_int_t sign=1;
    if (peek()=='-') {next(); sign=-1; }
    return sign*var_int();
  }


  // Unsafe parsers. Only minimal checks. Use for parsing proofs, as everything that convinces the checker is safe, be it syntactically correct or not!
  inline unsigned char unsafe_digit() {
    return (unsigned char)next() - '0';
  }

  inline id_int_t unsafe_id_int() {
    static_assert(!numeric_limits<id_int_t>::is_signed,"this impl depends on overflow not causing undef behaviour, i.e., on unsigned type!");
    id_int_t cur = 0;

    if (peek() == '0') {
      next();
      whitespace1();
    } else {
      while (!is_eof()) {
        char c=next();
        if (is_whitespace(c)) break;
        cur = cur * 10 + ((id_int_t)c-'0');
      }
      whitespace();
   }

    return cur;
  }

  inline lit_int_t unsafe_var_int() {
    id_int_t res = unsafe_id_int();
    return res; // "Implementation defined" behavior on overflow!
  }

  inline lit_int_t unsafe_lit_int() {
    lit_int_t sign=1;
    if (peek()=='-') {next(); sign=-1; }
    return sign*unsafe_var_int(); // Overflow cannot occur (C++ guarantees minimum range -(2^(n-1)-1)..+(2^(n-1)-1). C++20 even assumed 2s complement repr. )
  }


  static void whitespace1_again(Position &p) {
    while (is_whitespace(*(p++)));
  }

  /*
   * Parses a literal from a position.
   * Warning, this assumes that the safe or unsafe parser has already successfully parsed a
   * literal at this position, and that every literal is part of a 0 terminated clause, otherwise the behavior will be undefined!
   * Moreover, parsing beyond the terminating zero is not allowed.
   *
   * In detail, the assumption is that literals have no leading 0s, such
   * that a 0 at the beginning indicates the terminator symbol. Thus, no EOF checks are required.
   *
   * Unless having parsed a 0, the position will be set to the start of the next literal, by skipping over whitespace.
   */
  static lit_int_t lit_int_again(Position &p) {
    if (*p == '0') {++p; return 0;} // Terminal symbol. Do not attempt to skip over whitespace.

    lit_int_t sign=1;
    if (*p=='-') {++p; sign=-1; }

    lit_int_t cur=0;

    while (true) {
      char c=*(p++);
      if (is_whitespace(c)) break;
      cur=cur*10 + (c-'0');
    }

    while (is_whitespace(*p)) ++p;

    return cur;
  }

};

Lexer::Position Lexer::Position::invalid = Lexer::Position(nullptr);



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

public:
  static Variable const zero;

};

Variable const Variable::zero = Variable(0);



class Literal {
private:
  lit_int_t l;

public:
  inline Literal() : l(0) {};
  inline explicit Literal(lit_int_t _l) : l(_l) {};
  inline explicit Literal(Variable const&v) : l(v.raw()) {}

  inline string str() const {return std::to_string(l);}

  inline lit_int_t raw() const {return l;}

  inline bool operator ==(Literal const&lit) const {return l==lit.l;};
  inline bool operator !=(Literal const&lit) const {return l!=lit.l;};
  inline bool operator <(Literal const&lit) const {return abs(l) < abs(lit.l); };

  inline Literal neg() const {return Literal(-l);}
  inline Literal operator -() const {return neg();}

  Variable var() const {return Variable(abs(l));}

  static Literal const zero;

  inline bool in_bounds(size_t num_vars) const {return var().in_bounds(num_vars); }


};

Literal const Literal::zero = Literal(0);

/*
 * Clause database. Used to (temporarily) store clauses.
 *
 * Provides addition of clauses (also by parsing), and iteration over clauses
 */
class ClauseDB {
private:
  static vector<Literal> db;


public:
  class clause_t {
    friend ClauseDB;
  private:
    size_t idx;

    // Implicit conversions from/to size_t. but only privately!
    inline clause_t (size_t _idx) : idx(_idx) {}
    inline operator size_t() const {return idx;};

  public:
    inline bool is_invalid() {return idx==SIZE_MAX;}
    static clause_t invalid;


  };

  class checkpoint_t {
    friend ClauseDB;
  private:
    size_t idx = 0;

    // Implicit conversions from/to size_t. but only privately!
    inline checkpoint_t (size_t _idx) : idx(_idx) {}
    inline operator size_t() const {return idx;};

  public:
    checkpoint_t() {};
    checkpoint_t(checkpoint_t const &) = default;
    checkpoint_t &operator =(checkpoint_t const &) = default;
  };

  // Iterator over the literals of a clause. Valid as long as underlying db is not changed.
  class iterator {
    friend ClauseDB;
  private:
    Literal const *l = nullptr;
    inline iterator(Literal const *_l) : l(_l) {}

  public:
    inline iterator() {}
    inline void invalidate() {l=nullptr;}

    // Get literal at current position
    inline Literal peek() {return *l;}
    // Get current literal and advance
    inline Literal next() {return *(l++);}
    // Check if at end of clause
    inline bool at_end() {return peek()==Literal::zero;}

    inline Literal const &operator *() const {assert(l); return *l;}
    inline iterator &operator ++() {++l; return *this;}
    inline Literal const *operator->() const {return l; }

    inline bool operator==(iterator const&it) const {return l==it.l;}
    inline bool operator!=(iterator const&it) const {return l!=it.l;}
  };

public:
  static void clear() {db.clear();}
  static checkpoint_t get_checkpoint() {return db.size();}
  static void reset_to_checkpoint(checkpoint_t s) { assert(s<=db.size()); db.resize(s); }

  // Primitive addition of literals
  /*
   * Start new clause. Previous clause must be terminated by having added a 0!
   */
  static inline clause_t start_clause() {
    assert(db.size()==0 || db.back()==Literal::zero);
    return db.size();
  }
  static inline void add(Literal const &l) {db.push_back(l);}

  // Iterator from clause
  static inline iterator it(clause_t const &c) {return &db[c];}

  // Iterator from checkpoint
  static inline iterator it(checkpoint_t const &cp) { return db.data() + cp; }

//   // Iterator from begin
//   static inline iterator begin() { return db.data(); }


  static string str(clause_t const &c) {
    iterator i=it(c);
    ostringstream res;

    while (true) {
      Literal l=i.next();
      if (l==Literal::zero) break;
      res<<l.str()<<" ";
    }

    res<<"0";
    return res.str();
  }


private:
  template<bool sort_clause, typename NX> static clause_t parse_internal(NX nx, size_t num_vars) {
    clause_t res=start_clause();

    Literal l;
    do {
      l = Literal(nx());

      if (!l.in_bounds(num_vars)) error("Literal out of bounds: " + l.str());

      add(l);
    } while (l != Literal::zero);

    // Sort clause (excluding trailing 0)
    if (sort_clause) std::sort(db.begin()+res, db.end()-1);

    return res;
  }

public:
  /*
   * Safe parsing. Clause is sorted.
   */
  template<typename LX> static clause_t parse(LX &lx, size_t num_var) {
    return parse_internal<true>([&](){return lx.lit_int();},num_var);
  }

  /*
   * Unsafe parsing.
   * Note: bounds check still required, as it will be used for array indexing, etc.
   */
  template<typename LX> static clause_t unsafe_parse(LX &lx, size_t num_var) {
    return parse_internal<false>([&](){return lx.unsafe_lit_int();},num_var);
  }


public:
  static void print_stats() {
    log("ClauseDB: " + pretty_vector_stats(db));
  }



};

ClauseDB::clause_t ClauseDB::clause_t::invalid = ClauseDB::clause_t(SIZE_MAX);

vector<Literal> ClauseDB::db = vector<Literal>();


/*
 * T must have invalid element.
 *
 * T T::invalid()
 *
 * bool T::is_invalid()
 *
 *
 *
 */
template<typename T> class Id_Map;

// class CId {
//   template <typename T> friend class Id_Map;
// private:
//   size_t idx;
//   inline CId (size_t _idx) : idx(_idx) {}
//   inline operator size_t() const {return idx;}
//
// public:
// //    inline auto operator <=>(CId const &x) const = default;  // Not yet usable in clang-10, no <compare> header file provided!
// //   inline bool operator < (CId const &x) const {return idx < x.idx; };
// //   inline bool operator <=(CId const &x) const {return idx <= x.idx; };
// //   inline bool operator ==(CId const &x) const {return idx == x.idx; };
// //   inline bool operator > (CId const &x) const {return idx > x.idx; };
// //   inline bool operator >=(CId const &x) const {return idx >= x.idx; };
// //   inline bool operator !=(CId const &x) const {return idx != x.idx; };
//
// //   inline bool operator > (CId const &x) const = default;
// //   inline bool operator >=(CId const &x) const = default;
// //   inline bool operator !=(CId const &x) const = default;
//
// };


template<typename T> class Id_Map {
private:
  vector<T> map;

public:
  inline Id_Map() {
    // Clause with id zero is invalid!
    map.push_back(T::invalid);
  };

  inline size_t add(T elem) { size_t res = map.size(); map.push_back(elem); return res; }
  // Raw size, also counting gaps!
  inline size_t size() {return map.size();}


  inline size_t add_as(T elem, size_t id) {
    assert(!elem.is_invalid());
    // Make space
    if (!(id < map.size())) map.resize(id+1,T::invalid);
    // Check dup
    if (!map[id].is_invalid()) error("Duplicate id " + to_string(id));
    map[id] = elem;

    return id;
  }

  inline T lookup(size_t id) {
    if (!(id<map.size() && !map[id].is_invalid())) error("Invalid id " + to_string(id));
    return map[id];
  }

public:
  void print_stats(string name) {
    log(name+": " + pretty_vector_stats(map));
  }


};


template<typename T> class Var_Map {
private:
  vector<T> map;

public:
  inline Var_Map(size_t num_vars=0, T const &init = T()) : map(num_vars+1,init) {}

  inline void set_num_vars(size_t num_vars) {map.resize(num_vars+1);}
  inline size_t get_num_vars() const {return map.size();}

  inline T const &lookup(Variable v) const {assert(v.idx()<map.size()); return map[v.idx()];}
  inline T &lookup(Variable v) {assert(v.idx()<map.size()); return map[v.idx()];}

  inline T const &operator[](Variable v) const {return lookup(v);}
  inline T &operator[](Variable v) {return lookup(v);}


  inline void set(Variable v, T x) {lookup(v)=x;}


public:
  void print_stats(string name) {
    log(name+": " + pretty_vector_stats(map));
  }

};


typedef enum {Q_ALL, Q_EX} quantifier_t;


class QB_Formula {
private:
  size_t num_vars = 0;
  size_t cur_pos = 1;              // Current variable position
  Var_Map<quantifier_t> quants;    // Quantifier of variable
  Var_Map<size_t> varpos;          // Position of variable. Counting starts at 1, 0 being invalid/loose variable.

  ClauseDB::checkpoint_t fml_begin; // Begin of formula
  ClauseDB::checkpoint_t fml_end;   // End of formula

public:
  QB_Formula(size_t _num_vars=0) : num_vars(_num_vars), quants(_num_vars), varpos(_num_vars,0) {

  }

public:

  // Primitives

  size_t get_num_vars() {return num_vars;}

  void set_num_vars(size_t _num_vars) {
    num_vars=_num_vars;
    quants.set_num_vars(num_vars);
    varpos.set_num_vars(num_vars);
  }

  inline bool is_var_defined(Variable v) const {
    return (v.in_bounds(num_vars) && varpos[v]!=0);
  }

  inline size_t get_var_pos(Variable v) const {
    assert(v.in_bounds(num_vars));
    return varpos[v];
  }

  inline quantifier_t get_var_quant(Variable v) const {
    assert(is_var_defined(v));
    return quants[v];
  }

  inline void add_var(quantifier_t q, Variable v) {
    assert(v.in_bounds(num_vars));
    if (is_var_defined(v)) error("Duplicate bound variable: " + v.str());
    quants[v]=q;
    varpos[v]=cur_pos++;
  }

  void reset_to_fml() {ClauseDB::reset_to_checkpoint(fml_end);}


  ClauseDB::iterator begin() {return ClauseDB::it(fml_begin);}
  ClauseDB::iterator end() {return ClauseDB::it(fml_end);}


private:

//   Lexer::Position parse_clause(Lexer &lx) {
//     Lexer::Position res = lx.get_pos();
//
//     ClauseDB::parse(lx, num_vars);
//
//     lx.whitespace1();
//     lx.whitespace_cmt();
//
//     return res;
//   }


  Variable parse_var(Lexer &lx) {
    Variable v(lx.var_int());
    if (!v.in_bounds(num_vars)) error("Variable out of range: " + v.str());
    return v;
  }

  void parse_binding(Lexer &lx) {
    quantifier_t q;

    {
      string qw = lx.word();
      if (qw=="a") q=Q_ALL; else if (qw=="e") q=Q_EX; else error("Expected 'a' or 'e' quantifier, but got " + qw);
    }

    for (auto v = parse_var(lx); v != Variable::zero; v=parse_var(lx)) {
      add_var(q,v);
    }

    lx.whitespace_cmt();
  }

  void parse_bindings(Lexer &lx) {
    while (!lx.is_eof() && (lx.peek()=='a' || lx.peek()=='e')) parse_binding(lx);
  }


public:
  void parse_dimacs(Lexer &lx, Id_Map<ClauseDB::clause_t> *idm) {

    fml_begin=ClauseDB::get_checkpoint();

    lx.whitespace_cmt();

    log(2,"parsing dimacs header");
    // Header
    lx.keyword("p");lx.keyword("cnf");
    set_num_vars(lx.size_t_int());
    lx.size_t_int();
    lx.whitespace_cmt();

    log(2,"parsing dimacs var-bindings");
    // Bindings
    parse_bindings(lx);

    log(2,"parsing dimacs matrix");
    // Matrix
    while (!lx.is_eof()) {
      auto c = ClauseDB::parse(lx,num_vars);
      lx.whitespace_cmt();
      if (idm) idm->add(c);
    }

    fml_end = ClauseDB::get_checkpoint();
  }


public:
  void print_stats() {
    quants.print_stats("quantifier map");
    varpos.print_stats("varpos map");
  }

};



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
  static const mask_t max_mask = 1<<(bit_width-1);

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


  ParValuation() {}
  ParValuation(size_t _n) { init(_n); }
  ~ParValuation() { if (base) delete [] base;}


  // Getting and setting literals
  inline void set(Literal l) {
    assert(m && in_range(l));

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











class Proof_Checker {
public:
  enum mode_t {SAT,UNSAT};

private:
  // Memory mapped files
  MMap_Range fml_range;
  MMap_Range prf_range;

  // Lexer for current proof position
  Lexer prf_lx;

  // Formula
  QB_Formula formula;

  mode_t mode;


  // Id lookup.
  size_t first_proof_id=0;                 // First Id available for proof clauses
  Id_Map<ClauseDB::clause_t> fml_clauses;  // Clauses in formula (only populated in UNSAT mode)
  Id_Map<Lexer::Position> prf_clauses;     // Clauses in proof. TODO this map has a gap for the matrix clause ids.


  // Current step data
  enum kind_t {INIT,REDUCTION,RESOLUTION};
  struct {
    kind_t kind;
    size_t id;  // This step's id
    size_t id1; // First clause id (for REDUCTION,RESOLUTION)
    size_t id2; // Second clause id (for RESOLUTION)

    Lexer::Position pos = Lexer::Position::invalid; // Position of this step's clause

    ClauseDB::iterator it;  // Iterator over this step's clause
    ClauseDB::iterator it1; // Iterator over first referenced clause (for REDUCTION,RESOLUTION)
    ClauseDB::iterator it2; // Iterator over second referenced clause (for RESOLUTION)

    bool ignore=false;  // Set to ignore the clause produced by this step (used for initial clause/UNSAT)

  } step_data;

  bool seen_empty = false;

  // Initial cube checking (will only be initialized for SAT mode)
  ParValuation pval;

public:
  void print_stats() {
    ClauseDB::print_stats();
    formula.print_stats();
    fml_clauses.print_stats("formula-id map");
    prf_clauses.print_stats("proof-id map");
    pval.print_stats();
  }



public:
  Proof_Checker(string fml_file_name, string prf_file_name) : fml_range(fml_file_name), prf_range(prf_file_name), prf_lx(prf_range) {

    log(1,"parsing proof header");
    // Parse header of proof
    prf_lx.whitespace_cmt();

    prf_lx.keyword("r");
    {
      string m = prf_lx.word();
      if (m=="sat") mode=SAT;
      else if (m=="unsat") mode=UNSAT;
      else error("Unknown proof mode '"+m+"'");
    }


    prf_lx.whitespace_cmt();
    prf_lx.keyword("p");
    prf_lx.keyword("qrp");

    size_t prf_num_vars = prf_lx.size_t_int();
    prf_lx.size_t_int();
    prf_lx.whitespace_cmt();

    // Ignore quantifier decls in proof body
    while (!prf_lx.is_eof() && (prf_lx.peek()=='a' || prf_lx.peek()=='e')) {
      prf_lx.word();
      while (prf_lx.var_int() != 0);
      prf_lx.whitespace_cmt();
    }

    // Now we are at beginning of proof body

    log(1,"parsing formula");
    // Parse formula
    Lexer fml_lx(fml_range);
    formula.parse_dimacs(fml_lx,mode==UNSAT?&fml_clauses:nullptr);

    first_proof_id = mode==UNSAT?fml_clauses.size():0;

    // Checks
    if (prf_num_vars != formula.get_num_vars()) error("Declared number of variables in formula and proof mismatch!");


  }

  mode_t get_mode() const {return mode;}
  string get_mode_str() const {return mode==SAT?"SAT":"UNSAT";}


private:
  inline ClauseDB::clause_t lookup_clause(size_t id) {
    if (id<first_proof_id) {
      return fml_clauses.lookup(id);
    } else {
      Lexer lx(prf_range,prf_clauses.lookup(id));
      return ClauseDB::unsafe_parse(lx, formula.get_num_vars());
    }
  }

  inline void register_prf_clause(size_t id, Lexer::Position pos) {
    prf_clauses.add_as(pos,id);
  }


private:
  void parse_step() {
    // Prepare for new step
    formula.reset_to_fml();

    step_data.ignore=false;
    step_data.id1=0;
    step_data.id2=0;

    step_data.it1.invalidate();
    step_data.it2.invalidate();


    // Parse step
    step_data.id = prf_lx.id_int();
    step_data.pos = prf_lx.get_pos();

    // Note: we can only obtain an iterator once the clause-DB will not change any more!
    ClauseDB::clause_t c = ClauseDB::unsafe_parse(prf_lx,formula.get_num_vars());
    ClauseDB::clause_t c1(ClauseDB::clause_t::invalid);
    ClauseDB::clause_t c2(ClauseDB::clause_t::invalid);

    step_data.id1 = prf_lx.id_int();
    if (step_data.id1 == 0) {
      step_data.kind=INIT;
      if (mode==UNSAT) step_data.ignore=true;
    } else {
      c1 = lookup_clause(step_data.id1);
      step_data.id2 = prf_lx.id_int();
      if (step_data.id2 == 0) {
        step_data.kind=REDUCTION;
      } else {
        step_data.kind=RESOLUTION;
        c2 = lookup_clause(step_data.id2);
        if (prf_lx.id_int() != 0) error("Step can have at most 2 IDs");
      }
    }


    // Prepare iterators
    step_data.it = ClauseDB::it(c);
    if (!c1.is_invalid()) step_data.it1 = ClauseDB::it(c1);
    if (!c2.is_invalid()) step_data.it2 = ClauseDB::it(c2);

    // Set flag if we just parsed the empty clause
    seen_empty = step_data.it.at_end();

    prf_lx.whitespace_cmt();
  }

  void check_step() {
    switch (step_data.kind) {
      case INIT:
        if (mode == SAT) check_initial_cube(step_data.it);
        break;

      case REDUCTION:
        check_reduction(step_data.it, step_data.it1);
        break;

      case RESOLUTION:
        check_resolution(step_data.it, step_data.it1, step_data.it2);
        break;


    }
  }

private:

  // Shortcuts
  inline quantifier_t get_quant(Variable v) {return formula.get_var_quant(v);}
  inline size_t get_pos(Variable v) {return formula.get_var_pos(v);}


  void check_remaining_cubes() {
    assert(mode==SAT);

    if (pval.is_empty()) return; // Nothing to check

    ClauseDB::iterator it = formula.begin();

    // Iterate over clauses
    while (it!=formula.end()) {
      ParValuation::mask_t m=0;

      // Accumulate valuation over clause
      for (Literal l = it.next(); l!=Literal::zero; l=it.next() ) {
        m|=pval.get(l);
      }

      // Check
      if (m != pval.bits()) error("Initial cube check failed");
    }

    // Everything checked. Flush.
    pval.clear();
  }


  void check_initial_cube(ClauseDB::iterator it) {
    assert(mode==SAT);

    // If full, initiate check
    if (pval.is_full()) check_remaining_cubes();
    assert(!pval.is_full());

    // TODO: is a sortedness check actually required?
    while (*it != Literal::zero) {pval.set(*it); ++it; }

    pval.next_slot();
  }


  void check_reduction(ClauseDB::iterator it, ClauseDB::iterator it1) {
    // Quantifier that can be reduced
    quantifier_t red_quant = (mode==SAT)?Q_EX:Q_ALL;


    size_t min_red = SIZE_MAX; // Minimum variable position that has been reduced
    size_t max_nr = 0;         // Maximum non-reducible variable position


    while (true) {
      // Reduce all literals in original clause, until we found matching literal in new clause
      while (*it1 != *it) {
        if (it1.at_end()) error("Literal does not occur in original clause: " + it->str());

        Variable v = it1->var();

        assert(formula.is_var_defined(v)); // Comes from already checked clause!
        size_t vpos = formula.get_var_pos(v);

        min_red=min(min_red,vpos);
        if (formula.get_var_quant(v) != red_quant) error("Attempt to reduce wrong-polarity variable: " + v.str());

        ++it1;
      }

      if (it.at_end()) break;

      // Note: the literal at 'it' is valid here, as it equals a literal from a clause already in the DB
      // if (!valid_var(it->var())) error("Invalid variable");
      if (formula.get_var_quant(it->var()) != red_quant) max_nr = max (max_nr,formula.get_var_pos(it->var()));

      ++it; ++it1;
    }

    if (max_nr > min_red) error("Illegal reduction of variable: " + to_string(min_red) + " < " + to_string(max_nr));

  }

  void check_resolution(ClauseDB::iterator it, ClauseDB::iterator it1, ClauseDB::iterator it2) {
    // Quantifier that can be reduced
    quantifier_t red_quant = (mode==SAT)?Q_EX:Q_ALL;
    quantifier_t res_quant = (mode==SAT)?Q_ALL:Q_EX;

    size_t min_red = SIZE_MAX; // Minimum variable position that has been reduced
    size_t max_nr = 0;         // Maximum non-reducible variable position

    bool has_resolved=false;

    while (true) {
      Literal nl = *it;  // We have to match this literal
      bool at_end = it.at_end();

      // reduce-steps on c1
      while (!it1.at_end() && get_quant(it1->var()) == red_quant && (at_end || *it1 < nl)) {
        min_red = min(min_red, get_pos(it1->var()));
        ++it1;
      }

      // reduce-steps on c2
      while (!it2.at_end() && get_quant(it2->var()) == red_quant && (at_end || *it2 < nl)) {
        min_red = min(min_red, get_pos(it2->var()));
        ++it2;
      }

      // Check for resolution (and tautology)
      if (!it1.at_end() && !it2.at_end() && *it1 == -(*it2)) {
        if (get_quant(it1->var()) == res_quant) {
          if (has_resolved) error("double resolution. 2nd variable is " + it1->var().str());
          has_resolved=true;
          ++it1;
          ++it2;
          continue; // After resolution, some more reductions may follow
        } else {
          // This tries to introduce a tautology ...
          error("resolution results in tautology on variable " + it1->var().str());
        }
      }

//         if (!has_resolved &&  && get_quant(it1->var()) == res_quant) {
//           has_resolved=true;
//           ++it1;
//           ++it2;
//           continue; // After resolution, some more reductions may follow
//         }

      // Special case if we have reached end
      if (at_end) {
        if (!it1.at_end() || !it2.at_end()) error("Resolution got stuck at: " + nl.str() + " <- " + it1->str() + ", " + it2->str());
        if (!has_resolved) error("No resolution took place"); // Step would still be sound, as "C1 && C2" is equivalent to "C1 && C2 && (C1 || C2)", and dually for cubes.

        if (max_nr > min_red) error("Illegal reduction of variable: " + to_string(min_red) + " < " + to_string(max_nr));

        break;
      }


      /* Note: at this point, *it1 and *it2 are either equal or bigger than nl. Moreover, they are no opposite literals.
      *
      * Next, we check that one of them is equal to nl. This implies that the other one is also equal, or bigger.
      * As we can assume that clauses in the DB are sorted, the next literal we can check from it must be bigger than this literal, ensuring sortedness of this clause.
      */

      // Whenever we get here, the literal at "it" should be contained in at least one of the clauses
      bool found=false;
      if (nl == *it1) {found=true; ++it1;}
      if (nl == *it2) {found=true; ++it2;}

      if (!found) error("Resolution got stuck at: " + nl.str() + " <- " + it1->str() + ", " + it2->str());

      // Note: nl is a valid literal, as it equals (at least) one literal of an already checked clause from the DB
      // if (!valid_var(nl.var())) error("Invalid literal " + nl.str());
      // If non-reducible variable quantifier,
      if (get_quant(nl.var()) == res_quant) max_nr = max(max_nr,get_pos(nl.var()));

      ++it;
    }
  }

  void finish_step() {
    if (!step_data.ignore) register_prf_clause(step_data.id, step_data.pos);
  }

public:

  void do_check() {

    if (mode==SAT) pval.init(formula.get_num_vars());

    try {
      while (!seen_empty) {
        parse_step();
        check_step();
        finish_step();
      }

      if (mode==SAT) check_remaining_cubes();

    } catch (error_e &e) {
      e.specify("[context '" + prf_lx.position_context() + "']");
      throw;
    }

  }

};

void print_usage() {
  cerr<<"Usage qbfpvf <qdimacs-file> <qrp-file>"<<endl;
}


int main(int argc, char **argv) {
  try {

    if (argc!=3) {print_usage(); exit(1); }

    log("initializing");
    Proof_Checker chk(argv[1],argv[2]);
    log("checking proof ("+chk.get_mode_str()+")");
    chk.do_check();
    log("done");

    chk.print_stats();

    cout<<"s "<<chk.get_mode_str()<<endl;
    return 0;
  } catch (exception &e) {
    cout<<"s ERROR"<<endl;
    cerr<<e.what()<<endl;
    return 1;
  };

}







/*
xxx, ctd here:

  clause-id map
    plain map to whatever typename

    when do we need to store clauses in memory?

    SAT:
      we need formula quite often, for initial cube checking.
      BUT: initial clauses not assigned to IDs at all!


    UNSAT:
      initial formula clauses only needed, like any other clauses, for step checking:
        we can be uniform here, just having a map id -> Position, from where to parse the clause!


  QBF-Formula:
    info about quantifiers, max-var

    Parsers for matrix:
      store matrix in memory

      store clause positions in ID-map






*/




