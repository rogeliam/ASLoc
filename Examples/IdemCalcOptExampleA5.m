// Example: Optimized idempotent computation for A5
// A5 is a finite Coxeter group with 5 generators and |W| = 720.
AttachSpec("ASLoc.spec");

W := CoxeterGroup(GrpFPCox, "A5");
B := BSCategory(CartanMatrix("A5"), W);

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

act := function(w)
    return FActionByElt(B, w);
end function;

IC := CreateOptIdemCollection(B, C, act);

// Compute idempotent for the longest element w_0
x := LongestElement(W);
printf "Computing optimized idempotent for w_0 = %o (length %o)\n", Eltseq(x), #Eltseq(x);
printf "|W| = %o\n", #W;

t := Cputime();
opt_x := BuildOptIdempotent(IC, x);
printf "Time: %.2o s\n", Cputime(t);
printf "Reduced matrix: %o x %o\n",
    Nrows(opt_x`reduced_matrix`mat), Ncols(opt_x`reduced_matrix`mat);

// Verify idempotent property
red := opt_x`reduced_matrix;
assert red`mat eq (red * red)`mat;
printf "Idempotent check: OK\n";

printf "Cached idempotents: %o\n", NumberOfCachedIdempotents(IC);
printf "Cached light leaves: %o\n", NumberOfCachedLightLeaves(IC);
