CC=clang++
CFLAGS=-Wall -std=c++2a -ldl

debug:clean
	$(CC) $(CFLAGS) -g -o qbfpvf_proto main.cpp
stable:clean
	$(CC) $(CFLAGS) -O3 -o qbfpvf_proto main.cpp
clean:
	rm -vfr *~ qbfpvf_proto
