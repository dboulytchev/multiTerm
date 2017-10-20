TESTS=Expr ExprDef

%: %.hs
	$(GHC) -o $@ $<

test: $(TESTS)

clean:
	rm -Rf *~  $(TESTS) *.log *.hi *.o

