// LLOptBenchmark.m - Compare LLOptDownTo vs LLDownTo on B3
//
// For the longest element of B3, we pick random subexpressions,
// compute the target element from the subexpression, and then
// compare the standard and optimized light leaves for correctness and speed.

AttachSpec("ASLoc.spec");

// =============================================
// Setup A5
// =============================================
W := CoxeterGroup(GrpFPCox, "A5");
B := BSCategory(CartanMatrix("A5"), W);

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

act := function(w)
    return FActionByElt(B, w);
end function;

IC := CreateOptIdemCollection(B, C, act : UseOptLL := true);

// =============================================
// Build longest element and all idempotents
// =============================================
x := LongestElement(W);
bsword := Eltseq(x);
n := #bsword;
printf "A4 longest element: %o (length %o)\n\n", bsword, n;

// Pre-build the idempotent for x (this also caches all shorter elements)
printf "Building optimized idempotent for longest element...\n";
t_build := Cputime();
opt_ex := BuildOptIdempotent(IC, x);
printf "Done in %.2os. Cached idempotents: %o\n\n", Cputime(t_build), NumberOfCachedIdempotents(IC);

// =============================================
// Helper: compute target element from subexpression
// =============================================
function subexp_target(W, bsword, subexp)
    w := Id(W);
    for i := 1 to #bsword do
        if subexp[i] eq 1 then
            w := w * W.bsword[i];
        end if;
    end for;
    return w;
end function;

// =============================================
// Run tests: 100 random subexpressions
// =============================================
num_tests := 100;
total_std := 0.0;
total_opt := 0.0;
all_match := true;

printf "%-5o %-20o %-15o %-12o %-12o %-8o\n", "Test", "Subexpression", "Target", "Std (s)", "Opt (s)", "Match";
printf "%-5o %-20o %-15o %-12o %-12o %-8o\n", "----", "-------------", "------", "-------", "-------", "-----";

test := 0;
while test lt num_tests do
    // Random 0-1 subexpression
    subexp := [Random(0, 1) : i in [1..n]];

    // Compute target element
    w := subexp_target(W, bsword, subexp);
    target_seq := Eltseq(w);

    // Skip short target elements
    if #target_seq lt 10 then
        continue;
    end if;
    test +:= 1;

    // Pre-build target idempotent (don't count this in timing)
    opt_ey := BuildOptIdempotent(IC, w);

    // ------ Standard LLDownTo ------
    t1 := Cputime();
    ll_std := LLDownTo(B, bsword, subexp, target_seq);
    t_std := Cputime(t1);

    // ------ Optimized LLOptDownTo ------
    t2 := Cputime();
    ll_opt := LLOptDownTo(IC, opt_ex, opt_ey, subexp);
    t_opt := Cputime(t2);

    // ------ Compare: reduce standard to match optimized ------
    len_x := #bsword;
    len_y := #target_seq;
    if len_x ge 2 and len_y ge 2 then
        proj_x, incl_x := GetPrefixInclProj(IC, opt_ex, 1);
        proj_y, incl_y := GetPrefixInclProj(IC, opt_ey, 1);
        ll_std_reduced := proj_y * ll_std`stdmor * incl_x;
        match := ll_std_reduced eq ll_opt;
    elif len_x le 1 and len_y le 1 then
        match := ll_std`stdmor eq ll_opt;
    elif len_y le 1 then
        proj_x, incl_x := GetPrefixInclProj(IC, opt_ex, 1);
        ll_std_reduced := ll_std`stdmor * incl_x;
        match := ll_std_reduced eq ll_opt;
    else
        proj_y, incl_y := GetPrefixInclProj(IC, opt_ey, 1);
        ll_std_reduced := proj_y * ll_std`stdmor;
        match := ll_std_reduced eq ll_opt;
    end if;

    total_std +:= t_std;
    total_opt +:= t_opt;
    if not match then
        all_match := false;
    end if;

    printf "%-5o %-20o %-15o %-12o %-12o %-8o\n",
        test, subexp, target_seq, Sprintf("%.4o", t_std), Sprintf("%.4o", t_opt),
        match select "OK" else "FAIL";
end while;

printf "\n";
printf "Total standard:  %.4os\n", total_std;
printf "Total optimized: %.4os\n", total_opt;
if total_opt gt 0 then
    printf "Speedup:         %.2ox\n", total_std / total_opt;
end if;
printf "All match:       %o\n", all_match;

/*
// =============================================
// Step-by-step check: build LL for x[1..i] with expr[1..i]
// and compare standard vs optimized at each prefix length.
// This pinpoints the exact step where the optimized version diverges.
// =============================================
printf "\n=============================================================\n";
printf "Step-by-step prefix check\n";
printf "=============================================================\n\n";

// Pick a random subexpression for the full word
subexp_step := [Random(0, 1) : i in [1..n]];
printf "bsword = %o\n", bsword;
printf "subexp = %o\n\n", subexp_step;

// First compute the decoration for each step (mirrors LLOptDownTo logic)
decorations := [];
wu_track := Id(W);
for i := 1 to n do
    si := bsword[i];
    ei := subexp_step[i];
    if Length(wu_track * W.si) gt Length(wu_track) then
        if ei eq 0 then
            Append(~decorations, "U0");
        else
            Append(~decorations, "U1");
            wu_track := wu_track * W.si;
        end if;
    else
        wu_seq_t := Eltseq(wu_track);
        if wu_seq_t[#wu_seq_t] eq si then
            if ei eq 0 then
                Append(~decorations, "D0");
            else
                Append(~decorations, "D1");
                wu_track := wu_track * W.si;
            end if;
        else
            if ei eq 0 then
                Append(~decorations, "Db0");
            else
                Append(~decorations, "Db1");
                wu_track := wu_track * W.si;
            end if;
        end if;
    end if;
end for;

printf "Decorations: %o\n\n", decorations;

printf "%-5o %-8o %-8o %-8o %-15o %-15o %-8o\n", "i", "si", "ei", "Case", "Target", "Std size", "Match";
printf "%-5o %-8o %-8o %-8o %-15o %-15o %-8o\n", "---", "---", "---", "----", "------", "--------", "-----";

for i := 1 to n do
    // Prefix of the word and subexpression
    bsword_i := bsword[1..i];
    subexp_i := subexp_step[1..i];

    // Compute target element for this prefix
    w_i := subexp_target(W, bsword_i, subexp_i);
    target_i := Eltseq(w_i);

    // Build idempotents for the prefix element and target
    x_i := W ! bsword_i;
    opt_ex_i := BuildOptIdempotent(IC, x_i);
    opt_ey_i := BuildOptIdempotent(IC, w_i);

    // Standard light leaf for prefix
    ll_std_i := LLDownTo(B, bsword_i, subexp_i, target_i);

    // Optimized light leaf for prefix
    ll_opt_i := LLOptDownTo(IC, opt_ex_i, opt_ey_i, subexp_i);

    // Reduce standard to compare (only possible when both x_i and w_i have length >= 1)
    len_xi := #Eltseq(x_i);
    len_yi := #target_i;
    if len_xi ge 2 and len_yi ge 2 then
        proj_xi, incl_xi := GetPrefixInclProj(IC, opt_ex_i, 1);
        proj_yi, incl_yi := GetPrefixInclProj(IC, opt_ey_i, 1);
        ll_std_i_red := proj_yi * ll_std_i`stdmor * incl_xi;
        match_i := ll_std_i_red eq ll_opt_i;
    elif len_xi le 1 and len_yi le 1 then
        // Both are short: reduced = full, compare directly
        match_i := ll_std_i`stdmor eq ll_opt_i;
    elif len_yi le 1 then
        // Only x has incl/proj
        proj_xi, incl_xi := GetPrefixInclProj(IC, opt_ex_i, 1);
        ll_std_i_red := ll_std_i`stdmor * incl_xi;
        match_i := ll_std_i_red eq ll_opt_i;
    else
        // Only y has incl/proj
        proj_yi, incl_yi := GetPrefixInclProj(IC, opt_ey_i, 1);
        ll_std_i_red := proj_yi * ll_std_i`stdmor;
        match_i := ll_std_i_red eq ll_opt_i;
    end if;

    printf "%-5o %-8o %-8o %-8o %-15o %-15o %-8o\n",
        i, bsword[i], subexp_step[i], decorations[i], target_i,
        Sprintf("%ox%o", Nrows(ll_std_i`stdmor`mat), Ncols(ll_std_i`stdmor`mat)),
        match_i select "OK" else "FAIL";

    if not match_i then
        printf "  >>> MISMATCH at step %o (case %o)! Stopping.\n", i, decorations[i];
        printf "  x[1..%o] = %o, target = %o\n", i, bsword_i, target_i;
        printf "  subexp[1..%o] = %o\n", i, subexp_i;
        printf "  std reduced: %o x %o\n", Nrows(ll_std_i_red`mat), Ncols(ll_std_i_red`mat);
        printf "  opt:         %o x %o\n", Nrows(ll_opt_i`mat), Ncols(ll_opt_i`mat);
        break;
    end if;
end for;
*/
