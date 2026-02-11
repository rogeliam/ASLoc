// LLOptBenchmarkH3.m - Benchmark UseOptLL vs standard LL for H3
//
// For each length l = 0, 1, ..., max_length(H3):
//   - Build all optimized idempotents using IC (UseOptLL := true)
//   - Build all optimized idempotents using ICslow (UseOptLL := false)
//   - Compare total time per length
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetVerbose("IdemCalc", 0);
SetVerbose("IdemCalcOpt", 0);

printf "=============================================================\n";
printf "Benchmark: UseOptLL (true vs false) on H3\n";
printf "=============================================================\n\n";

// =============================================
// Setup H3
// =============================================
carH3 := CartanMatrix("H3");
W := CoxeterGroup(GrpFPCox, "H3");

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

// H3 Cartan matrix lives over a cyclotomic field (golden ratio),
// so we must construct BSCat manually.
f := BaseRing(carH3);
FR := RationalFunctionField(f, Rank(W));

B := New(BSCat);
B`C := carH3;
B`W := W;
B`FR := FR;
B`FAct := [ hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
B`I := [];
B`Q := FR;
B`QBase := Rationals();
B`Spec := hom< FR -> FR | [FR.i : i in [1..Rank(W)]] >;
B`StdProdSimpleCache := AssociativeArray();
B`FActionByEltCache := AssociativeArray();
B`FSpecActionByEltCache := AssociativeArray();
B`BSActIdCache := AssociativeArray();
B`BraidCache := AssociativeArray();
B`meta := AssociativeArray();

act := function(w)
    return FActionByElt(B, w);
end function;

w0 := LongestElement(W);
max_len := #Eltseq(w0);
printf "H3: |W| = %o, longest element length = %o\n\n", #W, max_len;

// Enumerate all elements, grouped by length
all_elts := EnumerateCoxeterGroup(W);
elts_by_length := [[] : i in [1..max_len+1]];
for w in all_elts do
    l := #Eltseq(w);
    Append(~elts_by_length[l+1], w);  // index 1 = length 0
end for;

// =============================================
// Create both collections
// =============================================
IC := CreateOptIdemCollection(B, C, act : UseOptLL := true);
ICslow := CreateOptIdemCollection(B, C, act : UseOptLL := false);

// =============================================
// Benchmark by length
// =============================================
times_opt := [];
times_slow := [];
counts := [];

printf "%-8o %-8o %-14o %-14o %-10o\n", "Length", "#Elts", "OptLL (s)", "StdLL (s)", "Speedup";
printf "%-8o %-8o %-14o %-14o %-10o\n", "------", "-----", "---------", "---------", "-------";

for l := 0 to max_len do
    elts := elts_by_length[l+1];
    n_elts := #elts;

    // --- OptLL (UseOptLL = true) ---
    t1 := Cputime();
    for w in elts do
        _ := BuildOptIdempotent(IC, w);
    end for;
    t_opt := Cputime(t1);

    // --- StdLL (UseOptLL = false) ---
    t2 := Cputime();
    for w in elts do
        _ := BuildOptIdempotent(ICslow, w);
    end for;
    t_slow := Cputime(t2);

    Append(~times_opt, t_opt);
    Append(~times_slow, t_slow);
    Append(~counts, n_elts);

    printf "%-8o %-8o %-14o %-14o ",
        l, n_elts, Sprintf("%.4o", t_opt), Sprintf("%.4o", t_slow);
    if t_slow gt 0.001 and t_opt gt 0.001 then
        printf "%-10o\n", Sprintf("%.2ox", t_slow / t_opt);
    else
        printf "%-10o\n", "-";
    end if;
end for;

// =============================================
// Summary
// =============================================
total_opt := &+times_opt;
total_slow := &+times_slow;

printf "\n=============================================================\n";
printf "SUMMARY\n";
printf "=============================================================\n";
printf "Total elements:   %o\n", &+counts;
printf "Total OptLL time: %.4os\n", total_opt;
printf "Total StdLL time: %.4os\n", total_slow;
if total_opt gt 0 then
    printf "Overall speedup:  %.2ox\n", total_slow / total_opt;
end if;
printf "Cached idempotents (OptLL): %o\n", NumberOfCachedIdempotents(IC);
printf "Cached idempotents (StdLL): %o\n", NumberOfCachedIdempotents(ICslow);
printf "Cached light leaves (OptLL): %o\n", NumberOfCachedLightLeaves(IC);
printf "Cached light leaves (StdLL): %o\n", NumberOfCachedLightLeaves(ICslow);
printf "=============================================================\n";
