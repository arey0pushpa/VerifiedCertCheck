#pragma once

#include "common.h"


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
    size_t pos = cur - begin;
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

/*
  static inline bool is_whitespace(char c) {
    return (c==' ' || c=='\t');
  }


  static inline bool is_whitespacenl(char c) {
    return (c==' ' || c=='\n' || c=='\t' || c=='\r');
  }
*/




  inline string word() {
    ostringstream res;
    while (!is_eow()) res<<next();
    eow();
    return res.str();
  }

  inline void keyword(string s) { if (word()!=s) error("Expected keyword '" + s + "'"); }


  inline bool is_eol() {
    return (is_eof() || peek()=='\n' || peek()=='\r');
  }

  inline void eol() {
    while (!is_eof()) {
      if (peek()=='c') {rest_of_line(); continue; }
      if (is_eol()) {next(); continue; }
      break;
    }
  }

  inline bool is_eow() {
    return is_eol() || peek()==' ' || peek()=='\t';
  }

  inline void eow() {
    while (!is_eol() && is_eow()) next();
  }

  inline void rest_of_line() {
    while (!is_eol()) next();
    eol();
  }

  /*
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
      if (is_whitespacenl(peek())) {next(); continue; }
      break;
    }
  }
  */

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
      } while (!is_eow());
    }

    eow();

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
    } else {
      while (!is_eow()) {
        char c=next();
        cur = cur * 10 + ((id_int_t)c-'0');
      }
    }

    eow();

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


//   static void whitespace1_again(Position &p) {
//     while (is_whitespace(*(p++)));
//   }
//
//   /*
//    * Parses a literal from a position.
//    * Warning, this assumes that the safe or unsafe parser has already successfully parsed a
//    * literal at this position, and that every literal is part of a 0 terminated clause, otherwise the behavior will be undefined!
//    * Moreover, parsing beyond the terminating zero is not allowed.
//    *
//    * In detail, the assumption is that literals have no leading 0s, such
//    * that a 0 at the beginning indicates the terminator symbol. Thus, no EOF checks are required.
//    *
//    * Unless having parsed a 0, the position will be set to the start of the next literal, by skipping over whitespace.
//    */
//   static lit_int_t lit_int_again(Position &p) {
//     if (*p == '0') {++p; return 0;} // Terminal symbol. Do not attempt to skip over whitespace.
//
//     lit_int_t sign=1;
//     if (*p=='-') {++p; sign=-1; }
//
//     lit_int_t cur=0;
//
//     while (true) {
//       char c=*(p++);
//       if (is_whitespace(c)) break;
//       cur=cur*10 + (c-'0');
//     }
//
//     while (is_whitespace(*p)) ++p;
//
//     return cur;
//   }

};

Lexer::Position Lexer::Position::invalid = Lexer::Position(nullptr);
