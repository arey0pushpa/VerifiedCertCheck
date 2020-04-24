CC=clang++
CFLAGS=-Wall -Wextra -std=c++2a -ldl -lboost_iostreams

profile:
	$(CC) $(CFLAGS) -g -lprofiler -O3 -o qbfpvf2 main2.cpp

stable:
	$(CC) $(CFLAGS) -D NDEBUG -O3 -o qbfpvf2 main2.cpp


profile1:
	$(CC) $(CFLAGS) -g -lprofiler -O3 -o qbfpvf1 main.cpp
profile_na1:
	$(CC) $(CFLAGS) -D NDEBUG -g -lprofiler -O3 -o qbfpvf1 main.cpp

stable1:
	$(CC) $(CFLAGS) -D NDEBUG -O3 -o qbfpvf1 main.cpp
debug1:
	$(CC) $(CFLAGS) -g -o qbfpvf1 main.cpp
#clean:
	#rm -vfr *~ qbfpvf_proto
