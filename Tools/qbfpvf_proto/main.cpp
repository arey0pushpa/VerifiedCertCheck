#include <iostream>
#include <fstream>
#include <cassert>
#include <vector>
#include <unordered_set>
#include <algorithm>
#include <boost/format.hpp>

#define BOOST_STACKTRACE_USE_ADDR2LINE
#include <boost/stacktrace.hpp>

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

void parse_expect(string s, istream &in) {
  string ss; in>>ws>>ss;

  if (s!=ss) error("Expected '" + s + "', but found '"+ss+"'");
}

void parse_ignore_comments(istream &in) {
  in>>ws;
  while (!in.eof()) {
    if (in.peek()!='c') break;
    in.ignore(numeric_limits<streamsize>::max(), '\n');
    in>>ws;
  }
}






typedef int32_t var_t;

class variable {
private:
  var_t v;

public:
  variable(var_t _v) : v(_v) { assert (v>=0); };

  size_t idx() const {return static_cast<size_t>(v);};

  string str() const {return to_string(v);}

  bool operator ==(variable var) const {return v==var.v;};
  bool operator !=(variable var) const {return v!=var.v;};

};

static const variable var_zero = variable(0);

variable parse_variable(istream &in) {
  var_t l;
  in>>ws; in>>l;
  if (l<0) error("Negative variable");
  return (variable(l));
}


class literal {
private:
  var_t l;

public:
  literal() : l(0) {};
  literal(var_t _l) : l(_l) {};

  string str() const {return std::to_string(l);}

  var_t as_int() const {return l;}

  bool operator ==(literal lit) const {return l==lit.l;};
  bool operator !=(literal lit) const {return l!=lit.l;};
  bool operator <(literal lit) const {return abs(l) < abs(lit.l); };


  variable var() const {return variable(abs(l));}

};

static const literal lit_zero = literal();


literal parse_literal(istream &in) {
  var_t l;
  in>>ws; in>>l; return (literal(l));
}


/*
 * Note: The Clauses and clause class is used for both, clauses and cubes!
 */
class Clauses;

class clause {
  friend Clauses;
private:
  size_t idx;
  clause(size_t _idx) : idx(_idx) {};

public:
  clause() : idx(SIZE_MAX) {};

  bool is_invalid() {return idx == SIZE_MAX;}


};

static const clause cl_invalid = clause();

class clause_iterator {
  friend Clauses;
private:
  literal const *pos;
  clause_iterator(literal const *_pos) : pos(_pos) {};

public:

  bool hasnext() const { return *pos != lit_zero; }
  literal const &cur() const { return *pos; }
  void next() { assert(hasnext()); ++pos; }

  clause_iterator &operator++() {next(); return *this;}

  literal const &operator*() const {return cur(); }
  literal const *operator->() const {return &cur(); }

};

class Clauses {

private:
  vector<literal> store;

  bool valid_clause(clause c) const {return c.idx < store.size();}

public:
  struct Clause_Hash_Eq {
    Clauses const &clauses;

    size_t operator() (const clause &c) const; // Hash function
    bool operator() (const clause &c1, const clause &c2) const; // Equality
  };

  const Clause_Hash_Eq cheq;


public:
  Clauses () : cheq{*this} {}

public:
  clause start_clause() { return clause(store.size());};
  void add_literal(literal l) {store.push_back(l);}
  void finish_clause() {store.push_back(lit_zero);}

public:
  clause_iterator iter(clause c) const {assert(valid_clause(c)); return clause_iterator(&(store[c.idx])); };

  bool is_empty(clause c) const {return !iter(c).hasnext();}



public:
  void sort_clause(clause c);

public:
  clause parse_clause(istream &in);


};


class ClauseMap;

class clause_id {
//   friend ClauseMap;
private:
  size_t idx1;


public:
  clause_id() : idx1(0) {}
  clause_id(size_t _idx1) : idx1(_idx1) {}

//   clause_id& operator++() {++idx; return *this;}
  bool operator==(clause_id id) {return idx1==id.idx1;}
  bool operator!=(clause_id id) {return idx1!=id.idx1;}

  bool valid() {return idx1!=0;}
  bool is_zero() {return idx1==0;}
  size_t idx() {assert (valid()); return idx1-1;}

  string str() const {return std::to_string(idx1);}
};

clause_id parse_clause_id(istream &in) {
  size_t idx1;
  in>>ws>>idx1;
  return clause_id(idx1);
}


class ClauseMap {

private:
  vector<clause> map;

public:

  clause_id end() {
    return clause_id(map.size());
  }

  bool is_valid_id(clause_id id) {
    return id.idx() < map.size() && !map[id.idx()].is_invalid();
  }

  clause_id append(clause c) {
    auto res = clause_id(map.size());
    map.push_back(c);
    return res;
  }

  void append_as(clause c, clause_id id) {
    assert(!c.is_invalid());

    // Make space
    if (!(id.idx() < map.size())) map.resize(id.idx()+1);

    if (!map[id.idx()].is_invalid()) error("Clause id already in use " + id.str());

    map[id.idx()] = c;
  }

  clause lookup(clause_id id) {
    if (!is_valid_id(id)) error("Invalid clause id "+id.str());
    return map[id.idx()];
  }



};


typedef enum {Q_ALL, Q_EX} quantifier_t;
typedef enum {CM_SAT,CM_UNSAT} certmode_t;


class Valuation {
private:
  size_t n = 0;
  bool *base = NULL;
  bool *m = NULL;

  Valuation(Valuation const &) = delete;
  Valuation &operator=(Valuation const &) = delete;

public:

  void init(size_t _n) {
    assert(!m && _n>0);
    n=_n;
    base = new bool[2*n+1];
    fill(base,base+(2*n+1),false);
    m = base + n;
  }


  Valuation() {}
  Valuation(size_t _n) { init(_n); }
  ~Valuation() { if (base) delete [] base;}

  void set(literal l) {
    var_t i = l.as_int();
    assert(m);
    assert(abs(i)<=n);
    m[i]=true; m[-i]=false;
  }

  void reset(literal l) {
    var_t i = l.as_int();
    assert(m && abs(i)<=n);
    m[i]=false; m[-i]=false;
  }

  bool get(literal l) {
    var_t i = l.as_int();
    assert(m && abs(i)<=n);
    return m[i];
  }

};



class QBF_Main {
private:
  Clauses clauses;
  ClauseMap cmap;

  enum {INIT, VDECL, MDECL, DONE} phase = INIT;



//   bool initialized = false;
//   bool vars_declared = false;
//   bool matrix_finished = false;

  size_t n;                     // Number of variables
  vector<quantifier_t> quants;  // Quantifier of variable
  vector<size_t> varpos;        // Position of variable, counting starts at 1. 0 is used to indicate undeclared variables.
  size_t ndecl = 0;             // Number of declared variables

  clause_id cbegin;             // Start of matrix clauses
  clause_id cend;               // End of matrix clauses

  certmode_t mode=CM_SAT;

  unordered_set<clause,Clauses::Clause_Hash_Eq,Clauses::Clause_Hash_Eq> matrix;        // List of all clauses in matrix.

  bool seen_empty=false;            // True if empty clause/cube has been added and checked


  Valuation val;                    // Valuation used for checking initial cubes


public:
  QBF_Main() : matrix(1,clauses.cheq,clauses.cheq) {};

  void start_vardecl(certmode_t _mode, size_t _n) {
    assert(phase==INIT);

    mode=_mode;
    n=_n;

    quants.resize(n+1);
    varpos.resize(n+1,0);
    cbegin=cend=cmap.end();

    phase=VDECL;
  }

private:
  struct proof_step {
    enum { INITIAL, REDUCTION, RESOLUTION } kind;

    clause_id idt;

    clause c;

    clause_id id1;
    clause_id id2;
  };

  proof_step parse_proof_step(istream &in);


public:
  void parse_qdimacs(istream &in);


  void check_proof(istream &in);


  bool is_initial_clause(clause c) {return matrix.count(c)!=0;}


  bool valid_var(variable v) {
    return (v.idx() >= 1 && v.idx() <= n && varpos[v.idx()]!=0);
  }


  void declare_var(quantifier_t q, variable v) {
    assert(phase==VDECL);

    if (!(v.idx() >= 1 && v.idx() <= n)) error("Variable out of range " + to_string(v.idx()));
    if (varpos[v.idx()] != 0) error("Variable already declared " + to_string(v.idx()));

    quants[v.idx()] = q;
    varpos[v.idx()] = ++ndecl;
  }

  size_t get_pos(variable v) {
    assert(valid_var(v));
    return varpos[v.idx()];
  }

  quantifier_t get_quant(variable v) {
    assert(valid_var(v));
    return quants[v.idx()];
  }

  void finish_vardecl() {
    assert(phase==VDECL);
    phase=MDECL;
  }


  string str(clause c) const {
    string res;
    for (auto it = clauses.iter(c); it.hasnext(); ++it) {
      res+=it.cur().str();
      res+=" ";
    }

    res+="0";
    return res;
  }

  void check_wf_clause(clause c);

  void declare_matrix_clause(clause c) {
    try {
      assert(phase==MDECL);
      clauses.sort_clause(c);
      check_wf_clause(c);

      matrix.insert(c);

    } catch (error_e &e) {
      e.specify("Declaring matrix clause #" + cmap.end().str());
      throw;
    }
  }

  void finish_clausedecl() {
    assert(phase==MDECL);
    cend = cmap.end();
    phase=DONE;
  }


  void check_proof_step(proof_step step);



private:
  // Parsing

  bool parse_vardecl(istream &in);

  void parse_matrix_clause(istream &in) {
    declare_matrix_clause(clauses.parse_clause(in));
  }

private:
  void check_initial(clause c);
  void check_reduction(clause c, clause_id id1);
  void check_resolution(clause c, clause_id id1, clause_id id2);

  bool is_clause_sat(clause c) {
    for (auto it=clauses.iter(c);it.hasnext();++it) {
      if (val.get(*it)) return true;
    }
    return false;
  }

};


inline size_t Clauses::Clause_Hash_Eq::operator() (const clause &c) const {
  size_t sum=0, prod=1, xxor=0; // The hash-function from drat-trim

  for (auto it = clauses.iter(c); it.hasnext(); ++it) {
    size_t l = ((*it).var().idx()); // Note: implicit conversion from signed to unsigned happens here. It's actually well-defined!
    prod*=l; sum+=l; xxor^=l;
  }
  return (1023 * sum + prod) ^ (31 * xxor);
}

inline bool Clauses::Clause_Hash_Eq::operator() (const clause &c1, const clause &c2) const {

  auto i1 = clauses.iter(c1);
  auto i2 = clauses.iter(c1);

  while (true) {
    if (*i1 != *i2) return false;
    if (!i1.hasnext()) return true;
    ++i1; ++i2;
  }
}



void QBF_Main::check_proof(std::istream& in) {

  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);

  parse_expect("r",in);
  {
    string ms; in>>ws>>ms;

    if (ms=="sat") mode=CM_SAT;
    else if (ms=="unsat") mode=CM_UNSAT;
    else error("Unknown mode: r " + ms);
  }

  parse_expect("p",in); parse_expect("qrp",in);
  { size_t x; in>>x>>x; }

  parse_ignore_comments(in);

  // Add matrix clauses as initial clauses to clause map
// Disabled for now. But ultimately, we want implicit IDs for original clauses?
//   if (mode == CM_UNSAT) {
//     for (auto it = matrix.begin();it!=matrix.end();++it) {
//       cmap.append(*it);
//     }
//   }

  // Init valuation used for initial cube checking
  if (mode==CM_SAT) {
    val.init(n);
  }

  // Skip over quantifiers and comments (we do not even check them for consistency)
  parse_ignore_comments(in);
  while (!in.eof()) {
    char c = in.peek();
    if (!(c=='e' || c=='a')) break;
    in.ignore(numeric_limits<streamsize>::max(), '\n');
    parse_ignore_comments(in);
  }


  // Read steps

  while (!in.eof()) {
    check_proof_step(parse_proof_step(in));
    parse_ignore_comments(in);
  }


  // TODO: Check remaining initial cubes


  if (!seen_empty) error("Proof contains no empty clause/cube");


  switch (mode) {
    case CM_SAT: cout<<"s SAT"<<endl; break;
    case CM_UNSAT: cout<<"s UNSAT"<<endl; break;
  }

}

QBF_Main::proof_step QBF_Main::parse_proof_step(std::istream& in) {
  proof_step r;

  r.idt = parse_clause_id(in);
  if (!r.idt.valid()) error("Expected clause id");

  r.c = clauses.parse_clause(in);

  r.id1 = parse_clause_id(in);
  if (r.id1.is_zero()) {r.kind=proof_step::INITIAL; goto finally; }
  r.id2 = parse_clause_id(in);
  if (r.id2.is_zero()) {r.kind=proof_step::REDUCTION; goto finally; }

  if (parse_clause_id(in).is_zero()) {r.kind=proof_step::RESOLUTION; goto finally; }

  error("Expected at most 2 ids for step");


  finally:
    parse_ignore_comments(in);
    return r;

}

void QBF_Main::check_proof_step(QBF_Main::proof_step step) {

  check_wf_clause(step.c);

  switch (step.kind) {
    case proof_step::INITIAL: check_initial(step.c); break;
    case proof_step::REDUCTION: check_reduction(step.c,step.id1); break;
    case proof_step::RESOLUTION: check_resolution(step.c,step.id1,step.id2); break;
  }

  // Register clause
  cmap.append_as(step.c,step.idt);

  seen_empty = seen_empty || clauses.is_empty(step.c);


}

void QBF_Main::check_initial(clause c) {
  switch (mode) {
    case CM_SAT:

      // Set clause literals
      for (auto it=clauses.iter(c);it.hasnext();++it) val.set(*it);

      // Check that every clause of initial matrix is satisfied
      for (auto it = matrix.begin(); it!=matrix.end();++it) {
        if (!is_clause_sat(*it)) error("Initial cube does not satisfy matrix clause. cube: " + str(c) + " clause: " +str(*it));
      }

      // Reset clause literals
      for (auto it=clauses.iter(c);it.hasnext();++it) val.reset(*it);


      break; // TODO: Initial cube checking with additional witnesses!
    case CM_UNSAT:
      if (!is_initial_clause(c)) error("Initial clause not in formula: " + str(c));

      break;

  }
}

void QBF_Main::check_reduction(clause c, clause_id id1) {
  clause c1 = cmap.lookup(id1);

  clause_iterator it = clauses.iter(c);
  clause_iterator it1 = clauses.iter(c1);

  // Quantifier that can be reduced
  quantifier_t red_quant = (mode==CM_SAT)?Q_EX:Q_ALL;


  size_t min_red = SIZE_MAX; // Minimum variable position that has been reduced
  size_t max_nr = 0;         // Maximum non-reducible variable position


  while (true) {
    // Reduce all variables in original clause, until we found matching variable in new clause
    while (*it1 != *it) {
      if (!it1.hasnext()) error("Literal does not occur in original clause: " + it->str());

      variable v = it1->var();
      min_red=min(min_red,get_pos(v));
      if (get_quant(v) != red_quant) error("Attempt to reduce wrong-polarity variable: " + v.str());

      ++it1;
    }

    if (!it.hasnext()) break;

    if (get_quant(it->var()) != red_quant) max_nr = max (max_nr,get_pos(it->var()));

    ++it; ++it1;
  }

  if (max_nr > min_red) error("Illegal reduction of variable");
}

void QBF_Main::check_resolution(clause c, clause_id id1, clause_id id2) {

  //xxx, ctd here


}



/*
xxx: QBF-Formula: quantifier info and initial clauses.
  but wrt to extensible clause map

  then parsers
*/




void Clauses::sort_clause(clause c) {
  assert(valid_clause(c));

  // Determine begin and end of clause
  auto begin = store.begin() + c.idx;
  auto end = begin;
  for (; *end != lit_zero; ++end) assert(end<store.end());


  std::sort(begin,end);
}

void QBF_Main::check_wf_clause(clause c) {

  /*
   * We check for strict sortedness. As only literals with smaller variable compare, this
   * ensures absence of duplicates and tautologies.
   *
   * Moreover, we check that all variables are valid
   */

  try {
    auto it=clauses.iter(c);
    if (!it.hasnext()) return;

    literal prev = it.cur();

    for (++it;it.hasnext();++it) {
      if (!valid_var(prev.var())) error("invalid variable " + prev.var().str());

      if (!(prev < *it)) error("not sorted " + prev.str() + " " + (*it).str());
      prev=*it;
    }
  } catch (error_e &e) {
    e.specify("clause " + str(c));
    throw;
  }

}


clause Clauses::parse_clause(istream &in) {
  clause res = start_clause();

  while (true) {
    literal l = parse_literal(in);
    if (l==lit_zero) {finish_clause(); break;}
    add_literal(l);
  };

  return res;
}


bool QBF_Main::parse_vardecl(istream &in) {
  if (in.eof()) return false;

  // Read quantifier
  quantifier_t q;

  switch (in.peek()) {
    case 'e': q=Q_EX; break;
    case 'a': q=Q_ALL; break;
    default: return false;
  }
  in.get();

  // Read variables
  while (true) {
    variable v=parse_variable(in);
    if (v==var_zero) break;
    declare_var(q,v);
  }

  return true;
}



void QBF_Main::parse_qdimacs(istream &in) {
  in.exceptions(in.failbit|in.badbit);

  parse_ignore_comments(in);
  parse_expect("p",in);
  parse_expect("cnf",in);

  size_t num_var;
  in>>ws>>num_var;

  size_t num_clauses;
  in>>ws>>num_clauses;

  start_vardecl(CM_SAT,num_var);

  parse_ignore_comments(in);
  while (parse_vardecl(in)) parse_ignore_comments(in);
  finish_vardecl();

  for (size_t i=0;i<num_clauses;++i) {
    parse_ignore_comments(in);
    parse_matrix_clause(in);
  }

  parse_ignore_comments(in);

  if (!in.eof()) error("Additional material at end of qdimacs file");

}


void print_usage() {
  cerr<<"Usage qbfpvf <qdimacs-file> <qrp-file>"<<endl;
}


/*
xxx, ctd here:
  read proof

  based on code in here, write tool to compress ids in proof, and refer to implicit formula ids!

  implement checks for initial cube, reduction, resolution
*/



int main(int argc, char **argv) {
  try {

    if (argc!=3) {print_usage(); exit(1); }

    string dimacs_file=argv[1];
    string qrp_file=argv[2];

    QBF_Main qbf;


    {
      cout<<"c parsing "<<dimacs_file<<endl;
      ifstream fs(dimacs_file,ifstream::in);
      qbf.parse_qdimacs(fs);
      fs.close();
      cout<<"c parsed"<<endl;
    }


    cout<<"c parsing "<<qrp_file<<endl;
    ifstream pfs(qrp_file,ifstream::in);
    qbf.check_proof(pfs);
    cout<<"c parsed"<<endl;



    return 0;

  } catch (exception &e) {
    cout<<"s ERROR"<<endl;
    cerr<<e.what()<<endl;
    return 1;
  };

}
