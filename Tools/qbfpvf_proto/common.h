#pragma once

#include <iostream>
#include <sstream>
#include <fstream>
#include <cassert>
#include <vector>
#include <unordered_set>
#include <unordered_map>
#include <algorithm>
#include <boost/format.hpp>

// #define BOOST_STACKTRACE_USE_ADDR2LINE
// #include <boost/stacktrace.hpp>

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
//    cerr<<boost::stacktrace::stacktrace()<<endl;
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
    if (level==0) { clog.flush(); cerr<<"c "<<msg<<endl;}
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


