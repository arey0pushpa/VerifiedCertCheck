CC=gcc
CFLAGS=-W -Wall -Wextra -O3 -DNDEBUG
CFLAGSDEBUG=-W -Wall -Wextra -g
CFLAGSNPICOSAT=-W -Wall -Wextra -O3 -DNPICOSAT -DNDEBUG
CFLAGSNPICOSATDEBUG=-W -Wall -Wextra -g -DNPICOSAT
PICOSATDIR=./libs/picosat

all: qrpcheck

qrpcheck: qrpcheck.c 
	${CC} ${CFLAGS} qrpcheck.c -o qrpcheck \
		                         -L${PICOSATDIR} -lpicosat -I${PICOSATDIR}

debug: qrpcheck.c
	${CC} ${CFLAGSDEBUG} qrpcheck.c -o qrpcheck \
		                              -L${PICOSATDIR} -lpicosat -I${PICOSATDIR}

nopicosat: qrpcheck.c
	${CC} ${CFLAGSNPICOSAT} qrpcheck.c -o qrpcheck

nopicosatdebug: qrpcheck.c
	${CC} ${CFLAGSNPICOSATDEBUG} qrpcheck.c -o qrpcheck

clean: 
	rm -f *.o 
	rm -f qrpcheck

.PHONY: all clean 
