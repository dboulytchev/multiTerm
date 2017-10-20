TESTS=Expr ExprDef
GHC=ghc

all: $(TESTS)

test: $(TESTS)
	@for f in $(TESTS) ; do \
	     ./$$f > $$f.log && \
	     if diff orig/$$f.orig $$f.log > $$ff.log.diff ; \
	        then echo "Test $$f ok" ; \
	        else echo "Test $$f failed, see $$f.log.diff" ; \
	     fi ; \
	   done

clean:
	rm -Rf *~  $(TESTS) *.log *.hi *.o

%: %.hs
	$(GHC) -o $@ $<


