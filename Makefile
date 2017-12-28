BNFC_SOURCES = \
	grammar/ParLatte.hs \
	grammar/AbsLatte.hs \
	grammar/LexLatte.hs \
	grammar/ErrM.hs

LATTE_SOURCES = \
	$(BNFC_SOURCES) \
	src/Latte.hs \
	src/Compiler.hs

all: latte

lib/runtime.o: lib/runtime.c
	gcc -c $^ -o $@

latte: $(LATTE_SOURCES)
	ghc --make $^ -o latte

grammar/LexLatte.hs: grammar/ParLatte.hs
	alex -g grammar/LexLatte.x

TestLatte: grammar/TestLatte.hs
	ghc --make $< -o TestLatte

grammar/ErrM.hs grammar/TestLatte.hs grammar/ParLatte.y grammar/LexLatte.x: grammar/Latte.cf
	bnfc -o grammar --functor $<

grammar/ParLatte.hs: grammar/ParLatte.y
	happy -gca $<

%.S: %.lat latte
	./latte < $< > $@

%.o: %.S
	nasm -f elf64 -o $@ $<

%.exe: %.o lib/runtime.o
	ld -o $@ $^ -dynamic-linker /lib64/ld-linux-x86-64.so.2 -lc -melf_x86_64

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
		grammar/DocLatte.ps

distclean: clean
	rm -f \
		grammar/DocLatte.* grammar/LexLatte.* grammar/ParLatte.* \
		grammar/LayoutLatte.* grammar/SkelLatte.* grammar/PrintLatte.* \
		grammar/TestLatte.* grammar/AbsLatte.* grammar/TestLatte grammar/ErrM.* \
		grammar/SharedString.* grammar/Latte.dtd grammar/XMLLatte.* \

