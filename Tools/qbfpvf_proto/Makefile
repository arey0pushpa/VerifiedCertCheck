CC=clang++
# CC=g++

BASIC_CFLAGS= -std=c++17 -Wall -Wextra
LIBS=-ldl -lboost_iostreams

CFLAGS=$(BASIC_CFLAGS) -g -lprofiler -O3
# CFLAGS=$(BASIC_CFLAGS) -g -D NDEBUG -lprofiler -O3
# CFLAGS=$(BASIC_CFLAGS) -D NDEBUG -O3
#CFLAGS=$(BASIC_CFLAGS) -g

all: qbfpvf1 qbfpvf2 reduce verify


qbfpvf1: main.cpp *.h
	$(CC) $(CFLAGS) -o qbfpvf1 main.cpp $(LIBS)

qbfpvf2: main2.cpp *.h
	$(CC) $(CFLAGS) -o qbfpvf2 main2.cpp $(LIBS)

reduce: reduce.cpp *.h
	$(CC) $(CFLAGS) -o reduce reduce.cpp $(LIBS)

verify: verify.cpp *.h
	$(CC) $(CFLAGS) -o verify verify.cpp $(LIBS)

clean:
	rm -vfr qbfpvf_proto qbfpvf1 qbfpvf2 reduce verify
