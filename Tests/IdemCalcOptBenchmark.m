// Benchmark: IdemCalc vs IdemCalcOpt
// Compares speed of normal and optimized idempotent computation
// on the longest elements of A3, A4, and B3.
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetVerbose("IdemCalc", 0);
SetVerbose("IdemCalcOpt", 0);

printf "=============================================================\n";
printf "Benchmark: IdemCalc vs IdemCalcOpt\n";
printf "=============================================================\n\n";

// ============================================================
// A3: longest element w_0 (length 6, |W| = 24)
// ============================================================
printf "A3 Setup...\n";
W_A3 := CoxeterGroup(GrpFPCox, "A3");
B_A3 := BSCategory(CartanMatrix("A3"), W_A3);
HAlg_A3 := IHeckeAlgebra(W_A3);
H_A3 := StandardBasis(HAlg_A3);
C_A3 := CanonicalBasis(HAlg_A3);

act_A3 := function(w)
    return FActionByElt(B_A3, w);
end function;

w0_A3 := LongestElement(W_A3);
printf "  w_0 = %o (length %o, |W| = %o)\n\n", Eltseq(w0_A3), #Eltseq(w0_A3), #W_A3;

// A3 normal
printf "A3 IdemCalc (normal)...\n";
IC_A3 := CreateIdemCollection(B_A3, C_A3, act_A3);
ResetMaximumMemoryUsage();
t := Cputime();
e_A3 := BuildIdempotent(IC_A3, w0_A3);
t_A3_normal := Cputime(t);
mem_A3_normal := GetMaximumMemoryUsage();
printf "  Time: %.2o s\n", t_A3_normal;
printf "  Memory: %.2o MB\n", mem_A3_normal / (1024^2);
printf "  Matrix: %o x %o\n\n", Nrows(e_A3`mat), Ncols(e_A3`mat);

// A3 optimized
printf "A3 IdemCalcOpt (optimized)...\n";
IC_A3_opt := CreateOptIdemCollection(B_A3, C_A3, act_A3);
ResetMaximumMemoryUsage();
t := Cputime();
opt_A3 := BuildOptIdempotent(IC_A3_opt, w0_A3);
t_A3_opt := Cputime(t);
mem_A3_opt := GetMaximumMemoryUsage();
red_A3 := opt_A3`reduced_matrix;
printf "  Time: %.2o s\n", t_A3_opt;
printf "  Memory: %.2o MB\n", mem_A3_opt / (1024^2);
printf "  Reduced matrix: %o x %o\n\n", Nrows(red_A3`mat), Ncols(red_A3`mat);

// A3 comparison
full_A3 := GetFullIdempotent(IC_A3_opt, opt_A3);
assert full_A3`mat eq e_A3`mat;
printf "A3 Comparison:\n";
printf "  Normal == GetFullIdempotent: OK\n";
printf "  Speedup: %.2ox\n", t_A3_normal / t_A3_opt;
printf "  Memory reduction: %.2ox\n", mem_A3_normal / mem_A3_opt;
printf "  Full matrix: %o x %o vs reduced: %o x %o\n\n",
    Nrows(e_A3`mat), Ncols(e_A3`mat), Nrows(red_A3`mat), Ncols(red_A3`mat);

// ============================================================
// A4: longest element w_0 (length 10, |W| = 120)
// ============================================================
printf "=============================================================\n";
printf "A4 Setup...\n";
W_A4 := CoxeterGroup(GrpFPCox, "A4");
B_A4 := BSCategory(CartanMatrix("A4"), W_A4);
HAlg_A4 := IHeckeAlgebra(W_A4);
H_A4 := StandardBasis(HAlg_A4);
C_A4 := CanonicalBasis(HAlg_A4);

act_A4 := function(w)
    return FActionByElt(B_A4, w);
end function;

w0_A4 := LongestElement(W_A4);
printf "  w_0 = %o (length %o, |W| = %o)\n\n", Eltseq(w0_A4), #Eltseq(w0_A4), #W_A4;

// A4 normal
printf "A4 IdemCalc (normal)...\n";
IC_A4 := CreateIdemCollection(B_A4, C_A4, act_A4);
ResetMaximumMemoryUsage();
t := Cputime();
e_A4 := BuildIdempotent(IC_A4, w0_A4);
t_A4_normal := Cputime(t);
mem_A4_normal := GetMaximumMemoryUsage();
printf "  Time: %.2o s\n", t_A4_normal;
printf "  Memory: %.2o MB\n", mem_A4_normal / (1024^2);
printf "  Matrix: %o x %o\n\n", Nrows(e_A4`mat), Ncols(e_A4`mat);

// A4 optimized
printf "A4 IdemCalcOpt (optimized)...\n";
IC_A4_opt := CreateOptIdemCollection(B_A4, C_A4, act_A4);
ResetMaximumMemoryUsage();
t := Cputime();
opt_A4 := BuildOptIdempotent(IC_A4_opt, w0_A4);
t_A4_opt := Cputime(t);
mem_A4_opt := GetMaximumMemoryUsage();
red_A4 := opt_A4`reduced_matrix;
printf "  Time: %.2o s\n", t_A4_opt;
printf "  Memory: %.2o MB\n", mem_A4_opt / (1024^2);
printf "  Reduced matrix: %o x %o\n\n", Nrows(red_A4`mat), Ncols(red_A4`mat);

// A4 comparison
full_A4 := GetFullIdempotent(IC_A4_opt, opt_A4);
assert full_A4`mat eq e_A4`mat;
printf "A4 Comparison:\n";
printf "  Normal == GetFullIdempotent: OK\n";
printf "  Speedup: %.2ox\n", t_A4_normal / t_A4_opt;
printf "  Memory reduction: %.2ox\n", mem_A4_normal / mem_A4_opt;
printf "  Full matrix: %o x %o vs reduced: %o x %o\n\n",
    Nrows(e_A4`mat), Ncols(e_A4`mat), Nrows(red_A4`mat), Ncols(red_A4`mat);

// ============================================================
// B3: longest element w_0 (length 9, |W| = 48)
// ============================================================
printf "=============================================================\n";
printf "B3 Setup...\n";
W_B3 := CoxeterGroup(GrpFPCox, "B3");
B_B3 := BSCategory(CartanMatrix("B3"), W_B3);
HAlg_B3 := IHeckeAlgebra(W_B3);
H_B3 := StandardBasis(HAlg_B3);
C_B3 := CanonicalBasis(HAlg_B3);

act_B3 := function(w)
    return FActionByElt(B_B3, w);
end function;

w0_B3 := LongestElement(W_B3);
printf "  w_0 = %o (length %o, |W| = %o)\n\n", Eltseq(w0_B3), #Eltseq(w0_B3), #W_B3;

// B3 normal
printf "B3 IdemCalc (normal)...\n";
IC_B3 := CreateIdemCollection(B_B3, C_B3, act_B3);
ResetMaximumMemoryUsage();
t := Cputime();
e_B3 := BuildIdempotent(IC_B3, w0_B3);
t_B3_normal := Cputime(t);
mem_B3_normal := GetMaximumMemoryUsage();
printf "  Time: %.2o s\n", t_B3_normal;
printf "  Memory: %.2o MB\n", mem_B3_normal / (1024^2);
printf "  Matrix: %o x %o\n\n", Nrows(e_B3`mat), Ncols(e_B3`mat);

// B3 optimized
printf "B3 IdemCalcOpt (optimized)...\n";
IC_B3_opt := CreateOptIdemCollection(B_B3, C_B3, act_B3);
ResetMaximumMemoryUsage();
t := Cputime();
opt_B3 := BuildOptIdempotent(IC_B3_opt, w0_B3);
t_B3_opt := Cputime(t);
mem_B3_opt := GetMaximumMemoryUsage();
red_B3 := opt_B3`reduced_matrix;
printf "  Time: %.2o s\n", t_B3_opt;
printf "  Memory: %.2o MB\n", mem_B3_opt / (1024^2);
printf "  Reduced matrix: %o x %o\n\n", Nrows(red_B3`mat), Ncols(red_B3`mat);

// B3 comparison
full_B3 := GetFullIdempotent(IC_B3_opt, opt_B3);
assert full_B3`mat eq e_B3`mat;
printf "B3 Comparison:\n";
printf "  Normal == GetFullIdempotent: OK\n";
printf "  Speedup: %.2ox\n", t_B3_normal / t_B3_opt;
printf "  Memory reduction: %.2ox\n", mem_B3_normal / mem_B3_opt;
printf "  Full matrix: %o x %o vs reduced: %o x %o\n\n",
    Nrows(e_B3`mat), Ncols(e_B3`mat), Nrows(red_B3`mat), Ncols(red_B3`mat);

// ============================================================
// Summary
// ============================================================
printf "=============================================================\n";
printf "SUMMARY\n";
printf "=============================================================\n";
printf "         | Normal (s) | Opt (s)  | Speedup  | Full size | Reduced size\n";
printf "  A3 w_0 | %10.2o | %8.2o | %7.2ox | %4o x %-4o | %4o x %-4o\n",
    t_A3_normal, t_A3_opt, t_A3_normal / t_A3_opt,
    Nrows(e_A3`mat), Ncols(e_A3`mat), Nrows(red_A3`mat), Ncols(red_A3`mat);
printf "  A4 w_0 | %10.2o | %8.2o | %7.2ox | %4o x %-4o | %4o x %-4o\n",
    t_A4_normal, t_A4_opt, t_A4_normal / t_A4_opt,
    Nrows(e_A4`mat), Ncols(e_A4`mat), Nrows(red_A4`mat), Ncols(red_A4`mat);
printf "  B3 w_0 | %10.2o | %8.2o | %7.2ox | %4o x %-4o | %4o x %-4o\n",
    t_B3_normal, t_B3_opt, t_B3_normal / t_B3_opt,
    Nrows(e_B3`mat), Ncols(e_B3`mat), Nrows(red_B3`mat), Ncols(red_B3`mat);
printf "=============================================================\n";
