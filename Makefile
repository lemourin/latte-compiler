SHELL = /bin/bash
BNFC ?= /home/students/inf/PUBLIC/MRJP/bin/bnfc

.SUFFIXES:
.PHONY: FORCE

BNFC_SOURCES = \
	grammar/ParLatte.hs \
	grammar/AbsLatte.hs \
	grammar/LexLatte.hs \
	grammar/ErrM.hs

LATTE_SOURCES = \
	$(BNFC_SOURCES) \
	src/Latte.hs \
	src/Compiler.hs

all: latc_x86_64_run

lib/runtime.o: lib/runtime.c
	gcc -c $^ -o $@

latc_x86_64_run: $(LATTE_SOURCES) lib/runtime.o
	ghc --make $^ -o $@

grammar/LexLatte.hs: grammar/ParLatte.hs
	alex -g grammar/LexLatte.x

TestLatte: grammar/TestLatte.hs
	ghc --make $< -o TestLatte

grammar/ErrM.hs grammar/TestLatte.hs grammar/ParLatte.y grammar/LexLatte.x: grammar/Latte.cf
	$(BNFC) -o grammar --functor $<

grammar/ParLatte.hs: grammar/ParLatte.y
	happy -gca $<

%.s: %.lat latc_x86_64_run FORCE
	./latc_x86_64_run < $< > $@; \
	if [ $$? -ne 0 ]; then \
		rm $@; \
		exit 1; \
	fi;

%.o: %.s
	nasm -f elf64 -o $@ $<

%: %.o lib/runtime.o
	gcc -static -o $@ $^

clean:
	rm -f \
		grammar/*.log \
		grammar/*.aux \
		grammar/*.hi \
		grammar/*.o \
		grammar/*.dvi \
		src/*.o \
		src/*.hi \
		lib/*.o \
		grammar/DocLatte.ps \
		latc_x86_64_run

distclean: clean
	rm -f \
		grammar/DocLatte.* grammar/LexLatte.* grammar/ParLatte.* \
		grammar/LayoutLatte.* grammar/SkelLatte.* grammar/PrintLatte.* \
		grammar/TestLatte.* grammar/AbsLatte.* grammar/TestLatte grammar/ErrM.* \
		grammar/SharedString.* grammar/Latte.dtd grammar/XMLLatte.* \

