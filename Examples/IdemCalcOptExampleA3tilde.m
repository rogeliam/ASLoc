// Example: Optimized idempotent computation for A~3
// A~3 is an affine Coxeter group with 4 generators.
AttachSpec("ASLoc.spec");

W := CoxeterGroup(GrpFPCox, "A~3");
B := BSCategory(CartanMatrix("A~3"), W);

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

act := function(w)
    return FActionByElt(B, w);
end function;

IC := CreateOptIdemCollection(B, C, act);
SetShowProgress(IC,true);
// Compute idempotent for element [2,4,1,3,2,4,1,3,2,4,1,3,2,4] (length 14)
x := W![2,4,1,3,2,4,1,3,2,4,1,3,2,4];
printf "Computing optimized idempotent for x = %o (length %o)\n", Eltseq(x), #Eltseq(x);

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
