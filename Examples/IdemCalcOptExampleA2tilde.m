// Example: Optimized idempotent computation for A~2
// A~2 is an affine Coxeter group (infinite), so there is no longest element.
// We compute a long element instead.
AttachSpec("ASLoc.spec");

W := CoxeterGroup(GrpFPCox, "A~2");
B := BSCategory(CartanMatrix("A~2"), W);

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

act := function(w)
    return FActionByElt(B, w);
end function;

IC := CreateOptIdemCollection(B, C, act);

// Compute idempotent for a length-10 element
x := W![1,2,3,1,2,3,1,2,3,1];
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
