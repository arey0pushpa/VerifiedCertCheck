#include "common.h"
#include "lexer.h"

// xxx, ctd here: add delete markers to steps, that indicate
//   when clauses become unused.
//
//   delete marker: negative cid.
//
//   how to implement: decrease refcnt in second pass
//     never mark initial formula clauses as deleted?
//     alternative: also allow deletion of initial formula clauses.
//       optional: emit deletion info for unused clauses up front.
//
//
//   easily collectable statistics:
//     max number of clauses required in memory simultaneously
//
//




// Wrapping an ID, but type-safe to not accidentally mix up with uncompressed Ids
class Compressed_Id {
  id_int_t id = 0;

private:
  explicit Compressed_Id(id_int_t _id) : id(_id) {}


public:
  Compressed_Id() {}

  inline id_int_t to_id_int() {return id;}
  inline string str() { assert(is_valid()); return to_string(id);}

  // Return current id and increment
  inline Compressed_Id next() { return Compressed_Id(id++); }

  inline bool is_valid() const { return id!=0;}

  inline bool operator<=(Compressed_Id const&cid) const {return id<=cid.id;}
  inline bool operator<(Compressed_Id const&cid) const {return id<cid.id;}
  inline bool operator==(Compressed_Id const&cid) const {return id==cid.id;}
  inline bool operator!=(Compressed_Id const&cid) const {return id!=cid.id;}

  static const Compressed_Id first;
  static const Compressed_Id invalid;
};

const Compressed_Id Compressed_Id::first = Compressed_Id(1);
const Compressed_Id Compressed_Id::invalid = Compressed_Id(0);


class Clause_Info {

  id_int_t id1 = 0;
  union {id_int_t id2 = 0; Compressed_Id cid; };
  size_t refcnt = 0; // 0 is invalid. Counting starts at 1 for no-refs!

public:

  inline Clause_Info() {}

  static inline bool valid_id(id_int_t id) {return id!=0 && id<SIZE_MAX;}

private:
  inline void mk_valid() {
    assert(!is_valid());
    refcnt=1;
  }

public:

  enum state_t {PRED, DEFER};

  inline bool is_valid() const {return refcnt!=0;}

  // Initial clause or cube
  inline void mk_initial() {
    mk_valid();
  }

  // Reduction
  inline void mk_reduction(id_int_t _id1) {
    mk_valid();
    id1=_id1;
    assert(valid_id(id1));
  }

  // Resolution
  inline void mk_resolution(id_int_t _id1, id_int_t _id2) {
    mk_valid();
    id1=_id1;
    id2=_id2;
    assert(valid_id(id1));
    assert(valid_id(id2));
  }


  inline state_t get_state() const {
    assert(is_valid());
    if (id1 == SIZE_MAX) return DEFER;
    else return PRED;
  }

  inline void set_compressed_id(Compressed_Id const _cid) {
    assert(is_valid());
    assert(get_state()==PRED);
    id1=SIZE_MAX;
    cid = _cid;
  }

  inline Compressed_Id const get_compressed_id() const {
    assert(is_valid());
    assert(get_state()==DEFER);
    return cid;
  }


  inline id_int_t get_id1() const {
    assert(is_valid());
    assert(get_state()==PRED);
    return id1;
  }

  inline id_int_t get_id2() const {
    assert(is_valid());
    assert(get_state()==PRED);
    return id2;
  }

  inline void set_id1(id_int_t _id1) {
    assert(is_valid());
    assert(get_state()==PRED);
    id1=_id1;
  }

  inline void set_id2(id_int_t _id2) {
    assert(is_valid());
    assert(get_state()==PRED);
    id2=_id2;
  }

  inline bool is_initial() {
    assert(is_valid());
    assert(get_state()==PRED);
    return !id1 && !id2;
  }

  inline bool is_reduction() {
    assert(is_valid());
    assert(get_state()==PRED);
    return id1 && !id2;
  }

  inline bool is_resolution() {
    assert(is_valid());
    assert(get_state()==PRED);
    return id1 && id2;
  }

  inline size_t get_refcnt() const {
    assert(is_valid());
    return refcnt-1;
  }

  // Returns old ref-count
  inline size_t incr_refcnt() {
    assert(is_valid());
    size_t res = get_refcnt();
    ++refcnt;
    return res;
  }

  // Returns new ref-count
  inline size_t decr_refcnt() {
    assert(is_valid());
    assert(get_refcnt()>0);
    --refcnt;
    return get_refcnt();
  }


};


template<typename T> class Id_Map {
private:
  vector<T> map;

public:
  inline bool contains(id_int_t id) const {
    return id<map.size() && map[id].is_valid();
  }

  inline T& operator[](id_int_t id) {
    assert (contains(id));
    return map[id];
  }

  inline T const& operator[](id_int_t id) const {
    assert (contains(id));
    return map[id];
  }

  inline T& define(id_int_t id) {
    if (!Clause_Info::valid_id(id)) error("Malformed id " + to_string(id));
    if (!(id<map.size())) map.resize(id+1);

//     clog<<"define "<<id<<endl;

    return map[id];
  }

};

class Compressor {

public:
  enum mode_t {UNDEF,SAT,UNSAT};


private:
  Id_Map<Clause_Info> m;

  id_int_t first_proof_id = 0; // 0 indicates not yet set

  void check_defined(id_int_t id) {
    if (!m.contains(id)) error("Undefined id " + to_string(id));
  }

  id_int_t final_id = 0;

  mode_t mode = UNDEF;

private:
  inline size_t incr_refcnt(Clause_Info &mid) {
    return mid.incr_refcnt();
  }

  inline size_t decr_refcnt(Clause_Info &mid) {
    return mid.decr_refcnt();
  }


public:

  inline void set_first_proof_id(id_int_t id) {
    assert(first_proof_id == 0);
    assert(id != 0);
    first_proof_id = id;

    // Mark all formula clause IDs as initial
    for (id_int_t i=1;i<first_proof_id;++i) m.define(i).mk_initial();
  }

  inline id_int_t get_first_proof_id() {
    assert(first_proof_id);
    return first_proof_id;
  }

  // Phase 1: filling in trace information

  inline void init_cube_step(id_int_t id) {
    m.define(id).mk_initial();
  }

  inline void reduction_step(id_int_t id, id_int_t id1) {
    check_defined(id1);
    m.define(id).mk_reduction(id1);
  }

  inline void resolution_step(id_int_t id, id_int_t id1, id_int_t id2) {
    check_defined(id1);
    check_defined(id2);
    m.define(id).mk_resolution(id1,id2);
  }


  inline void set_final_id(id_int_t id) {
    assert(final_id==0);
    check_defined(id);
    final_id=id;
  }

  inline void set_mode(mode_t m) {
    assert(mode==UNDEF);
    mode=m;
  }

  inline mode_t get_mode() const {
    assert(mode!=UNDEF);
    return mode;
  }

  inline bool is_sat() const {
    return get_mode()==SAT;
  }

  inline bool is_fml_id(id_int_t id) const {
    assert(first_proof_id);
    return id<first_proof_id;
  }


// Phase 2: marking. Returns new final id (in case of reduction chasing)
private:
  id_int_t chase_id(id_int_t);

public:
  void mark();

// Phase 3: filtering. Iterate over proof again, adjust IDs.
private:
  Compressed_Id cur_id = Compressed_Id::invalid;

  inline Compressed_Id const compress_id(Clause_Info &mid) {
    mid.set_compressed_id(cur_id);
    Compressed_Id res = cur_id;
    cur_id.next();
    return res;
  }


public:

  // Returns number of active initial clauses
  inline size_t init_iterate_again() {
    assert(!cur_id.is_valid());

    size_t num_active=0;

    cur_id = Compressed_Id::first;

    if (!is_sat()) {
      // Initialize compressed ids of initial clauses
      for (id_int_t i=1;i<get_first_proof_id();++i) {
        m[i].set_compressed_id(cur_id.next());
        if (m[i].get_refcnt()>0) {
          ++num_active;
        }
      }
    }

    return num_active;
  }

  inline Compressed_Id adjust_initial_cube(id_int_t &id) {
    auto &mid=m[id];

    if (!mid.get_refcnt()) return Compressed_Id::invalid;
    if (!is_sat()) error("Reachable initial cube step in UNSAT proof");

    return compress_id(mid);
  }

  inline id_int_t dbg_get_ant1(id_int_t id) {
    return m[id].get_id1();
  }
  inline id_int_t dbg_get_ant2(id_int_t id) {
    return m[id].get_id2();
  }

  inline Compressed_Id adjust_resolution(
      id_int_t &id, Compressed_Id &cid1, Compressed_Id &cid2,
      bool &del1, bool &del2
  ) {
    auto &mid=m[id];

    if (!mid.get_refcnt()) return Compressed_Id::invalid;

    assert(mid.is_resolution());

//     clog<<"adjust "<<id<<" "<<mid.get_id1()<<" "<<mid.get_id2()<<endl;

    auto &mid1 = m[mid.get_id1()];
    auto &mid2 = m[mid.get_id2()];

    cid1 = mid1.get_compressed_id();
    cid2 = mid2.get_compressed_id();

    del1 = decr_refcnt(mid1) == 0;
    del2 = decr_refcnt(mid2) == 0;

    // Compress this id
    return compress_id(mid);
  }

  inline id_int_t get_final_id() {
    return final_id;
  }

  inline Compressed_Id adjust_final_id() {
    decr_refcnt(m[final_id]);

    return m[final_id].get_compressed_id();
  }


  inline Compressed_Id get_cur_id() {
    return cur_id;
  }


};



id_int_t Compressor::chase_id(id_int_t id) {

  // Find target id
  id_int_t tid=id;

  while (true) {
    auto &mid = m[tid];

    if (!mid.is_reduction()) break; // Found a non-reduction step.

    tid = mid.get_id1(); // Get next node id in chain

    // Increment this node's ref-count
    if (incr_refcnt(mid) > 0) {
      // Found already processed node. Target is this node's id
      assert(!m[tid].is_reduction());
      break;
    }
  }

  // Redirect all nodes
  while (id != tid) {
    auto &mid = m[id];
    assert(mid.is_reduction());
    id = mid.get_id1();
    mid.set_id1(tid);
  }

  return tid;
}



void Compressor::mark() {

  final_id = chase_id(final_id);

  vector<id_int_t> worklist;
  worklist.push_back(final_id);


  while (!worklist.empty()) {
    id_int_t id = worklist.back(); worklist.pop_back();
    auto &mid = m[id];

    assert(!mid.is_reduction()); // Only chased nodes on worklist

    bool visited = (incr_refcnt(mid) != 0);

    if (!visited && mid.is_resolution()) {
      // Chase down antecedent ids
      mid.set_id1(chase_id(mid.get_id1()));
      mid.set_id2(chase_id(mid.get_id2()));

      // Add chased down ids to worklist
      worklist.push_back(mid.get_id1());
      worklist.push_back(mid.get_id2());
    }
  }
};



class Compressor_Driver {
private:
  MMap_Range trace;
  Lexer lx;

  Lexer::Position lxbegin;


  Compressor cmp;


  size_t active_clauses = 0;
  size_t max_active_clauses = 0;

public:
  Compressor_Driver(string filename) : trace(filename), lx(trace), lxbegin(lx.get_pos()) {}




private:
  inline id_int_t parse_header() {
    lx.eol();
    lx.keyword("p"); lx.keyword("cqrp");
    id_int_t res = lx.id_int();
    lx.eol();
    return res;
  }

  template <typename T> inline void parse_clause(T f) {
    lit_int_t l;

    do {
      l=lx.unsafe_lit_int();
      f(l);
    } while (l!=0);
  }

  inline void skip_clause() {
    parse_clause([](lit_int_t){});
  }

  inline void copy_clause(ostream &out) {
//     // For debugging only: sorting by abs(lit) TODO: remove
//     vector<lit_int_t> lits;
//     parse_clause([&](lit_int_t l){if (l) lits.push_back(l);});
//     std::sort(lits.begin(),lits.end(),[](auto a, auto b){ return (abs(a)<abs(b)); });
//     for (auto l : lits) out<<l<<" ";
//     out<<"0";

    // TODO: original code without sorting
    parse_clause([&](lit_int_t l){out<<l; if (l) out<<" ";});
  }

  inline bool parse_step(id_int_t &id, id_int_t &id1, id_int_t &id2) {
    id=id1=id2=0;

    if (lx.peek()=='f') return false;

    id=lx.unsafe_id_int();
    id1=lx.unsafe_id_int();

    if (id1 == 0) {
      skip_clause();
    } else {
      if (!lx.is_eol()) id2=lx.unsafe_id_int();
    }

    lx.eol();

    return true;
  }

  inline id_int_t parse_final_id() {
    lx.keyword("f");
    id_int_t res = lx.unsafe_id_int();
    lx.eol();
    return res;
  }

  inline Compressor::mode_t parse_mode() {
    lx.keyword("r");
    string ms = lx.word();
    lx.eol();

    if (ms == "UNSAT") return Compressor::UNSAT;
    else if (ms == "SAT") return Compressor::SAT;
    else error("Undefined mode '" + ms + "'");
  }





private:
  void first_pass() {
    // Header
    cmp.set_first_proof_id(parse_header()+1);

    // Steps
    while (true) {
      id_int_t id,id1,id2;

      if (!parse_step(id,id1,id2)) break;

//       clog<<"parse "<<id<<" "<<id1<<" "<<id2<<endl;

      if (id2) cmp.resolution_step(id,id1,id2);
      else if (id1) cmp.reduction_step(id,id1);
      else cmp.init_cube_step(id);
    }

    // Final id
    cmp.set_final_id(parse_final_id());

    // Mode
    cmp.set_mode(parse_mode());
  }

  void mark() {
    cmp.mark();
  }

//   unordered_set<id_int_t> dbg_active;


  inline void incr_active() {
    ++active_clauses;
    max_active_clauses = max(max_active_clauses,active_clauses);

//     assert(dbg_active.count(id)==0);
//     dbg_active.insert(id);
//
//     clog<<"activate "<<id<<endl;

  }

  inline void decr_active(bool del) {
    if (del) {
      assert(active_clauses>0);
      --active_clauses;

//       assert(dbg_active.count(id)>0);
//       dbg_active.erase(id);
//
//       clog<<"deactivate "<<id<<endl;
    }
  }


  void second_pass(ostream &out) {

    active_clauses = cmp.init_iterate_again();
    max_active_clauses = active_clauses;

    lx.set_pos(lxbegin);

    // Header
    parse_header(); // Skip over file header

    out<<"p redcqrp "<<cmp.get_cur_id().str()<<'\n';

    if (cmp.is_sat()) out<<"r SAT"<<'\n';
    else out<<"r UNSAT"<<'\n';


    Compressed_Id chk_cur_id = cmp.get_cur_id(); // Used for self-check, to assert that implicit IDs are in sync

    // Steps. TODO redundancy with parse_step
    while (lx.peek() != 'f') {

      assert(chk_cur_id == cmp.get_cur_id());

      id_int_t id,id1;

      id=lx.unsafe_id_int();
      id1=lx.unsafe_id_int();

      if (id1==0) {
        Compressed_Id cid = cmp.adjust_initial_cube(id);
        if (cid.is_valid()) {
          chk_cur_id.next();
          assert(chk_cur_id == cmp.get_cur_id());
          incr_active();
          out<<"0 ";
          copy_clause(out);
          out<<"\n";
        } else {
          skip_clause();
        }
      } else {
        if (!lx.is_eol()) {
          lx.unsafe_id_int(); // Ignore second id (we'll use the red-chased one from m)
          Compressed_Id cid,cid1,cid2;
          bool del1 = false, del2 = false;

          cid=cmp.adjust_resolution(id,cid1,cid2,del1,del2);
          if (cid.is_valid()) {
            chk_cur_id.next();
            assert(chk_cur_id == cmp.get_cur_id());

            incr_active();
            decr_active(del1);
            decr_active(del2);

            //out<<cid.str()<<" ";
            if (del1) out<<"d";
            out<<cid1.str()<<" ";
            if (del2) out<<"d";
            out<<cid2.str()<<'\n';


          }
        }
      }

      lx.eol();
    }

//     // Final clause
//     out<<"f "<<cmp.adjust_final_id().str()<<'\n';

    out.flush();

    // Check that active count is back to zero. If this fails, the marking and ref-counting algo is somehow broken
    decr_active(true);

//     if (active_clauses != 0) {
//       clog<<"ERR ac = "<<active_clauses<<endl;
//
//       for (auto id : dbg_active) clog<<id<<" ";
//       clog<<endl;
//     }

    assert(active_clauses == 0);

    log("Max active clauses " + to_string(max_active_clauses));
  }

public:
  void do_compress(ostream &out) {
    log("First pass");
    first_pass();
    log("Marking");
    mark();
    log("Second pass");
    second_pass(out);
    log("Done");
  }


};


int main(int argc, char **argv) {
  try {
    if (argc!=3) error("Usage: reduce <tracefile> <outfile>");

    Compressor_Driver cd(argv[1]);

    ofstream out(argv[2], ios_base::out | ios_base::trunc);

    out.imbue(locale::classic());
    out.exceptions(ios_base::badbit | ios_base::failbit);
    out.flush();

    cd.do_compress(out);
    out.close();

    return 0;

  } catch (exception &e) {
    cout<<"s ERROR"<<endl;
    cerr<<e.what()<<endl;
    return 1;
  };


}



