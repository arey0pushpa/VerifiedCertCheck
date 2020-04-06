#include <iostream>
#include <fstream>
#include <cassert>
#include <vector>
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


void error(string msg) {
//   cout<<"s ERROR "<<msg<<endl;
//
//   cerr<<boost::stacktrace::stacktrace()<<endl;
//
//   exit(1);

  throw error_e(msg);

}

void error(boost::format fmt) {error (fmt.str());}

void parse_expect(string s, istream &in) {
  string ss; in>>ws>>ss;

  if (s!=ss) error("Expected '" + s + "', but found '"+ss+"'");
}





typedef int32_t var_t;

class variable {
private:
  var_t v;

public:
  variable(var_t _v) : v(_v) { assert (v>=0); };

  size_t idx() {return static_cast<size_t>(v);};

  string str() {return to_string(v);}

  bool operator ==(variable var) {return v==var.v;};
  bool operator !=(variable var) {return v!=var.v;};

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

  string str() {return std::to_string(l);}


  bool operator ==(literal lit) {return l==lit.l;};
  bool operator !=(literal lit) {return l!=lit.l;};
  bool operator <(literal lit) {return abs(l) < abs(lit.l); };


  variable var() {return variable(abs(l));}

};

static const literal lit_zero = literal();


literal parse_literal(istream &in) {
  var_t l;
  in>>ws; in>>l; return (literal(l));
}



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
  literal *pos;
  clause_iterator(literal *_pos) : pos(_pos) {};

public:

  bool hasnext() { return *pos != lit_zero; }
  literal &cur() {assert (hasnext()); return *pos; }
  void next() { assert(hasnext()); ++pos; }

  clause_iterator &operator++() {next(); return *this;}

  literal &operator*() {return cur(); }

};

class Clauses {
private:
  vector<literal> store;

  bool valid_clause(clause c) {return c.idx < store.size();}

public:
  clause start_clause() { return clause(store.size());};
  void add_literal(literal l) {store.push_back(l);}
  void finish_clause() {store.push_back(lit_zero);}

public:
  clause_iterator iter(clause c) {assert(valid_clause(c)); return clause_iterator(&(store[c.idx])); };


public:
  void sort_clause(clause c);

public:
  clause parse_clause(istream &in);


};


class ClauseMap;

class clause_id {
  friend ClauseMap;
private:
  size_t idx;
  clause_id(size_t _idx) : idx(_idx) {}


public:
  clause_id() : idx(0) {}

  clause_id& operator++() {++idx; return *this;}
  bool operator==(clause_id id) {return idx==id.idx;}
  bool operator!=(clause_id id) {return idx!=id.idx;}

  string str() {return std::to_string(idx);}

};


class ClauseMap {

private:
  vector<clause> map;

public:

  clause_id end() {
    return clause_id(map.size());
  }

  bool is_valid_id(clause_id id) {
    return id.idx < map.size() && !map[id.idx].is_invalid();
  }

  clause_id append(clause c) {
    auto res = clause_id(map.size());
    map.push_back(c);
    return res;
  }

  void append_as(clause c, clause_id id) {
    assert(!c.is_invalid());

    // Make space
    if (!(id.idx < map.size())) map.resize(id.idx+1);

    if (!map[id.idx].is_invalid()) error(boost::format("Clause id already in use %d")%id.idx);

    map[id.idx] = c;
  }

  clause lookup(clause_id id) {
    if (!is_valid_id(id)) error(boost::format("Invalid clause id %d")%id.idx);
    return map[id.idx];
  }



};


typedef enum {Q_ALL, Q_EX} quantifier_t;

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

public:
  QBF_Main() {};

  void start_vardecl(size_t _n) {
    assert(phase==INIT);

    n=_n;

    quants.resize(n+1);
    varpos.resize(n+1,0);
    cbegin=cend=cmap.end();

    phase=VDECL;
  }


  void parse_qdimacs(istream &in);


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

  quantifier_t get_quant(variable v) {
    assert(valid_var(v));
    return quants[v.idx()];
  }

  void finish_vardecl() {
    assert(phase==VDECL);
    phase=MDECL;
  }


  string str(clause c) {
    string res;
    for (auto it = clauses.iter(c); it.hasnext(); ++it)
      res+=it.cur().str();

    res+=" 0";
    return res;
  }

  void check_wf_clause(clause c);

  clause_id declare_matrix_clause(clause c) {
    try {
      assert(phase==MDECL);
      clauses.sort_clause(c);
      check_wf_clause(c);
      return cmap.append(c);
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



private:
  // Parsing

  bool parse_vardecl(istream &in);

  clause_id parse_matrix_clause(istream &in) {
    return declare_matrix_clause(clauses.parse_clause(in));
  }

  void parse_ignore_comments(istream &in) {
    in>>ws;
    while (!in.eof()) {
      if (in.peek()!='c') break;
      in.ignore(numeric_limits<streamsize>::max(), '\n');
      in>>ws;
    }
  }



};




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

  start_vardecl(num_var);

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
  cerr<<"Usage XXX"<<endl;
}

int main(int argc, char **argv) {
  try {

    if (argc<2) {print_usage(); exit(1); }

    string dimacs_file=argv[1];

    QBF_Main qbf;


    cout<<"c parsing "<<dimacs_file<<endl;

    ifstream fs(dimacs_file,ifstream::in);
    qbf.parse_qdimacs(fs);
    fs.close();


    cout<<"c parsed"<<endl;

    return 0;

  } catch (exception &e) {
    cout<<"s ERROR"<<endl;
    cerr<<e.what()<<endl;
    return 1;
  };

}
