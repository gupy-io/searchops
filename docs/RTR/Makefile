# https://github.com/pmer/tla-bin

%.out : %.tla
	pcal $<
	-tlc $< > $@

all: zdr1.out zdr2.out zdr3.out
