CC=clang++
CFLAGS=-Wall -Wextra -std=c++2a -ldl -lboost_iostreams

profile:clean
	$(CC) $(CFLAGS) -g -lprofiler -O3 -o qbfpvf_proto main.cpp
profile_na:clean
	$(CC) $(CFLAGS) -D NDEBUG -g -lprofiler -O3 -o qbfpvf_proto main.cpp

stable:clean
	$(CC) $(CFLAGS) -D NDEBUG -O3 -o qbfpvf_proto main.cpp
debug:clean
	$(CC) $(CFLAGS) -g -o qbfpvf_proto main.cpp
clean:
	rm -vfr *~ qbfpvf_proto
