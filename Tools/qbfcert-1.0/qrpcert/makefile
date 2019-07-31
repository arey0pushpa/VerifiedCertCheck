CC=gcc
CFLAGSOPT=-O3 -W -Wall -Wextra -Wunused -DNDEBUG
CFLAGSDEF=-W -Wall -Wextra -Wunused -g

all: opt

opt: qrpcert.c simpleaig.c qrpcert_version.h
	${CC} ${CFLAGSOPT} -c simpleaig.c -o simpleaig.o
	${CC} ${CFLAGSOPT} qrpcert.c -o qrpcert simpleaig.o

debug: qrpcert.c simpleaig.c qrpcert_version.h
	${CC} ${CFLAGSDEF} -c simpleaig.c -o simpleaig.o
	${CC} ${CFLAGSDEF} qrpcert.c -o qrpcert simpleaig.o

clean:
	rm -f *.o
	rm -f qrpcert 

.PHONY: all clean 
