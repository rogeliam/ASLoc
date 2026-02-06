// Tests for IdemCalcOpt.m - Optimized idempotent calculation
// Tests B3, H3, and A~2 to verify optimized construction
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);
SetVerbose("IdemCalcOpt", 0);

n_passed := 0;
n_failed := 0;

// ============================================================
// Helper: compute expected reduced matrix size from Hecke algebra
// ============================================================
// Express C_x in the standard basis H, evaluate all Laurent polynomial
// coefficients at v=1, and sum them. This gives the expected Nrows of
// the reduced idempotent matrix.
function ExpectedReducedSize(H, C, x)
    h_cx := H ! C.Eltseq(x);
    _, coeffs := Support(h_cx);
    total := 0;
    for poly in coeffs do
        total +:= Evaluate(poly, 1);
    end for;
    return total;
end function;

// ============================================================
// B3 TESTS
// ============================================================
printf "=============================================================\n";
printf "B3 Tests\n";
printf "=============================================================\n\n";

cartan_B3 := CartanMatrix("B3");
W_B3 := CoxeterGroup(GrpFPCox, cartan_B3);
B_B3 := BSCategory(cartan_B3, W_B3);

HAlg_B3 := IHeckeAlgebra(W_B3);
H_B3 := StandardBasis(HAlg_B3);
C_B3 := CanonicalBasis(HAlg_B3);

act_B3 := function(w)
    return FActionByElt(B_B3, w);
end function;

// ============================================================
// Test 1: B3 basic construction and size check
// ============================================================
printf "Test 1: B3 basic construction and size check...\n";
try
    IC_B3 := CreateOptIdemCollection(B_B3, C_B3, act_B3);

    test_elts_B3 := [W_B3![1], W_B3![2], W_B3![3], W_B3![1,2], W_B3![2,3], W_B3![1,2,1], W_B3![2,3,2]];
    for x in test_elts_B3 do
        opt := BuildOptIdempotent(IC_B3, x);
        red_size := Nrows(opt`reduced_matrix`mat);
        expected := ExpectedReducedSize(H_B3, C_B3, x);
        assert red_size eq expected;
        printf "  %o: OK (reduced %o x %o, expected %o)\n", Eltseq(x),
            red_size, Ncols(opt`reduced_matrix`mat), expected;
    end for;
    printf "Test 1 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 1 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 2: B3 cache functionality
// ============================================================
printf "Test 2: B3 cache functionality...\n";
try
    assert HasCachedIdempotent(IC_B3, W_B3![1,2]);
    printf "  HasCachedIdempotent: OK\n";

    n_cached := NumberOfCachedIdempotents(IC_B3);
    assert n_cached ge #test_elts_B3;
    printf "  NumberOfCachedIdempotents (%o): OK\n", n_cached;

    e_cached := GetCachedIdempotent(IC_B3, W_B3![1,2]);
    e_fresh := BuildOptIdempotent(IC_B3, W_B3![1,2]);
    assert e_cached`reduced_matrix`mat eq e_fresh`reduced_matrix`mat;
    printf "  GetCachedIdempotent: OK\n";

    cached_list := CachedIdempotents(IC_B3);
    assert #cached_list eq n_cached;
    printf "  CachedIdempotents: OK\n";

    n_ll := NumberOfCachedLightLeaves(IC_B3);
    printf "  NumberOfCachedLightLeaves (%o): OK\n", n_ll;

    printf "Test 2 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 2 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 3: B3 longest element w_0
// ============================================================
printf "Test 3: B3 longest element w_0...\n";
try
    w0_B3 := LongestElement(W_B3);
    w0_seq := Eltseq(w0_B3);
    printf "  w_0 = %o (length %o)\n", w0_seq, #w0_seq;

    t := Cputime();
    opt_w0 := BuildOptIdempotent(IC_B3, w0_B3);
    printf "  Time: %.2o s\n", Cputime(t);

    red_size := Nrows(opt_w0`reduced_matrix`mat);
    expected := ExpectedReducedSize(H_B3, C_B3, w0_B3);
    assert red_size eq expected;
    printf "  Reduced matrix: %o x %o (expected %o)\n",
        red_size, Ncols(opt_w0`reduced_matrix`mat), expected;

    // Also verify the reduced matrix is idempotent
    red := opt_w0`reduced_matrix;
    assert red`mat eq (red * red)`mat;
    printf "  Reduced idempotent check: OK\n";

    printf "Test 3 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 3 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 4: B3 prefix/suffix inclusion/projection
// ============================================================
printf "Test 4: B3 prefix/suffix inclusion/projection...\n";
try
    x := W_B3![1,2,3];
    opt_x := BuildOptIdempotent(IC_B3, x);

    // Test prefix: get incl/proj at different k values
    for k := 1 to 3 do
        proj_k, incl_k := GetPrefixInclProj(IC_B3, opt_x, k);
        assert Type(proj_k) ne RngIntElt;
        assert Type(incl_k) ne RngIntElt;
        printf "  Prefix k=%o: OK (%o x %o)\n", k,
            Nrows(incl_k`mat), Ncols(incl_k`mat);
    end for;

    // Test suffix: get incl/proj at different k values
    for k := 1 to 3 do
        proj_k, incl_k := GetSuffixInclProj(IC_B3, opt_x, k);
        assert Type(proj_k) ne RngIntElt;
        assert Type(incl_k) ne RngIntElt;
        printf "  Suffix k=%o: OK (%o x %o)\n", k,
            Nrows(incl_k`mat), Ncols(incl_k`mat);
    end for;

    printf "Test 4 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 4 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// H3 TESTS
// ============================================================
printf "=============================================================\n";
printf "H3 Tests\n";
printf "=============================================================\n\n";

// H3 requires special BSCat setup (non-integer Cartan matrix)
carH3 := CartanMatrix("H3");
W_H3 := CoxeterGroup(GrpFPCox, "H3");

HAlg_H3 := IHeckeAlgebra(W_H3);
H_H3 := StandardBasis(HAlg_H3);
C_H3 := CanonicalBasis(HAlg_H3);

f := BaseRing(carH3);
FR := RationalFunctionField(f, Rank(W_H3));

B_H3 := New(BSCat);
B_H3`C := carH3;
B_H3`W := W_H3;
B_H3`FR := FR;
B_H3`FAct := [hom<FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W_H3)]]> : s in [1..Rank(W_H3)]];
B_H3`I := [];
B_H3`Q := FR;
B_H3`QBase := Rationals();
B_H3`Spec := hom<FR -> FR | [FR.i : i in [1..Rank(W_H3)]]>;
B_H3`StdProdSimpleCache := AssociativeArray();
B_H3`FActionByEltCache := AssociativeArray();
B_H3`FSpecActionByEltCache := AssociativeArray();
B_H3`BSActIdCache := AssociativeArray();
B_H3`BraidCache := AssociativeArray();
B_H3`meta := AssociativeArray();

act_H3 := function(w)
    return FActionByElt(B_H3, w);
end function;

// ============================================================
// Test 5: H3 basic construction and size check
// ============================================================
printf "Test 5: H3 basic construction and size check...\n";
try
    IC_H3 := CreateOptIdemCollection(B_H3, C_H3, act_H3);

    test_elts_H3 := [W_H3![1], W_H3![2], W_H3![3], W_H3![1,2], W_H3![2,3], W_H3![1,2,1]];
    for x in test_elts_H3 do
        opt := BuildOptIdempotent(IC_H3, x);
        red_size := Nrows(opt`reduced_matrix`mat);
        expected := ExpectedReducedSize(H_H3, C_H3, x);
        assert red_size eq expected;
        printf "  %o: OK (reduced %o x %o, expected %o)\n", Eltseq(x),
            red_size, Ncols(opt`reduced_matrix`mat), expected;
    end for;
    printf "Test 5 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 5 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 6: H3 long element [1,2,1,2,1,3,2,1,2,1,3] (length 11)
// ============================================================
printf "Test 6: H3 long element (length 11)...\n";
try
    x_H3 := W_H3![1,2,1,2,1,3,2,1,2,1,3];
    x_seq := Eltseq(x_H3);
    printf "  x = %o (length %o)\n", x_seq, #x_seq;

    t := Cputime();
    opt_x := BuildOptIdempotent(IC_H3, x_H3);
    t_elapsed := Cputime(t);
    printf "  Time: %.2o s\n", t_elapsed;

    red_size := Nrows(opt_x`reduced_matrix`mat);
    expected := ExpectedReducedSize(H_H3, C_H3, x_H3);
    assert red_size eq expected;
    printf "  Reduced matrix: %o x %o (expected %o)\n",
        red_size, Ncols(opt_x`reduced_matrix`mat), expected;

    // Verify reduced matrix is idempotent
    red := opt_x`reduced_matrix;
    assert red`mat eq (red * red)`mat;
    printf "  Reduced idempotent check: OK\n";

    printf "  Cached idempotents: %o\n", NumberOfCachedIdempotents(IC_H3);
    printf "  Cached light leaves: %o\n", NumberOfCachedLightLeaves(IC_H3);

    printf "Test 6 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 6 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// A~2 TESTS
// ============================================================
printf "=============================================================\n";
printf "A~2 Tests\n";
printf "=============================================================\n\n";

W_A2t := CoxeterGroup(GrpFPCox, "A~2");
cartan_A2t := CartanMatrix("A~2");
B_A2t := BSCategory(cartan_A2t, W_A2t);

HAlg_A2t := IHeckeAlgebra(W_A2t);
H_A2t := StandardBasis(HAlg_A2t);
C_A2t := CanonicalBasis(HAlg_A2t);

act_A2t := function(w)
    return FActionByElt(B_A2t, w);
end function;

// ============================================================
// Test 7: A~2 basic construction and size check
// ============================================================
printf "Test 7: A~2 basic construction and size check...\n";
try
    IC_A2t := CreateOptIdemCollection(B_A2t, C_A2t, act_A2t);

    test_elts_A2t := [W_A2t![1], W_A2t![2], W_A2t![3], W_A2t![1,2], W_A2t![2,3], W_A2t![3,1],
                       W_A2t![1,2,3], W_A2t![1,2,1]];
    for x in test_elts_A2t do
        opt := BuildOptIdempotent(IC_A2t, x);
        red_size := Nrows(opt`reduced_matrix`mat);
        expected := ExpectedReducedSize(H_A2t, C_A2t, x);
        assert red_size eq expected;
        printf "  %o: OK (reduced %o x %o, expected %o)\n", Eltseq(x),
            red_size, Ncols(opt`reduced_matrix`mat), expected;
    end for;
    printf "Test 7 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 7 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 8: A~2 longer elements
// ============================================================
printf "Test 8: A~2 longer elements...\n";
try
    long_elts := [W_A2t![1,2,3,1,2], W_A2t![1,2,3,1,2,3,1]];
    for x in long_elts do
        t := Cputime();
        opt := BuildOptIdempotent(IC_A2t, x);
        red_size := Nrows(opt`reduced_matrix`mat);
        expected := ExpectedReducedSize(H_A2t, C_A2t, x);
        assert red_size eq expected;
        printf "  %o: OK (reduced %o x %o, expected %o, %.2os)\n", Eltseq(x),
            red_size, Ncols(opt`reduced_matrix`mat), expected, Cputime(t);
    end for;
    printf "Test 8 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 8 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 9: Progress display toggle
// ============================================================
printf "Test 9: Progress display toggle...\n";
try
    IC_prog := CreateOptIdemCollection(B_B3, C_B3, act_B3 : ShowProgress := true);
    SetShowProgress(IC_prog, false);
    opt := BuildOptIdempotent(IC_prog, W_B3![1,2,3]);
    red_size := Nrows(opt`reduced_matrix`mat);
    expected := ExpectedReducedSize(H_B3, C_B3, W_B3![1,2,3]);
    assert red_size eq expected;
    printf "  ShowProgress toggle: OK\n";

    // Re-enable and build another
    SetShowProgress(IC_prog, true);
    printf "  (progress display on for next build)\n";
    opt2 := BuildOptIdempotent(IC_prog, W_B3![1,2,3,2]);
    red_size2 := Nrows(opt2`reduced_matrix`mat);
    expected2 := ExpectedReducedSize(H_B3, C_B3, W_B3![1,2,3,2]);
    assert red_size2 eq expected2;
    printf "  ShowProgress enabled: OK\n";

    printf "Test 9 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 9 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 10: Clear cache and rebuild
// ============================================================
printf "Test 10: Clear cache and rebuild...\n";
try
    IC_clear := CreateOptIdemCollection(B_B3, C_B3, act_B3);
    _ := BuildOptIdempotent(IC_clear, W_B3![1,2,3]);
    assert NumberOfCachedIdempotents(IC_clear) gt 0;
    printf "  Before clear: %o idempotents, %o light leaves\n",
        NumberOfCachedIdempotents(IC_clear), NumberOfCachedLightLeaves(IC_clear);

    ClearCache(IC_clear);
    assert NumberOfCachedIdempotents(IC_clear) eq 0;
    assert NumberOfCachedLightLeaves(IC_clear) eq 0;
    printf "  After clear: OK\n";

    // Rebuild should work fine
    opt := BuildOptIdempotent(IC_clear, W_B3![1,2,3]);
    red_size := Nrows(opt`reduced_matrix`mat);
    expected := ExpectedReducedSize(H_B3, C_B3, W_B3![1,2,3]);
    assert red_size eq expected;
    printf "  Rebuild after clear: OK\n";

    printf "Test 10 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 10 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// OPTIONAL: Test 11 - H3 longest element w_0 (~15-20 minutes)
// Set run_h3_w0 := true above to enable this test
// ============================================================
if assigned run_h3_w0 and run_h3_w0 then
    printf "Test 11: H3 longest element w_0 (SLOW, ~15-20 min)...\n";
    try
        w0_H3 := LongestElement(W_H3);
        w0_seq := Eltseq(w0_H3);
        printf "  w_0 = %o (length %o)\n", w0_seq, #w0_seq;
        printf "  |W| = %o\n", #W_H3;

        t := Cputime();
        SetShowProgress(IC_H3, true);
        opt_w0 := BuildOptIdempotent(IC_H3, w0_H3);
        SetShowProgress(IC_H3, false);
        t_elapsed := Cputime(t);
        printf "  Time: %.2o s\n", t_elapsed;

        red_size := Nrows(opt_w0`reduced_matrix`mat);
        expected := ExpectedReducedSize(H_H3, C_H3, w0_H3);
        assert red_size eq expected;
        printf "  Reduced matrix: %o x %o (expected %o)\n",
            red_size, Ncols(opt_w0`reduced_matrix`mat), expected;

        red := opt_w0`reduced_matrix;
        assert red`mat eq (red * red)`mat;
        printf "  Reduced idempotent check: OK\n";

        printf "  Cached idempotents: %o\n", NumberOfCachedIdempotents(IC_H3);
        printf "  Cached light leaves: %o\n", NumberOfCachedLightLeaves(IC_H3);

        printf "Test 11 PASSED\n\n";
        n_passed +:= 1;
    catch err
        printf "Test 11 FAILED: %o\n\n", err`Object;
        n_failed +:= 1;
    end try;
else
    printf "(Test 11: H3 w_0 SKIPPED - set run_h3_w0 := true; before loading to enable)\n\n";
end if;

// ============================================================
// Summary
// ============================================================
printf "=============================================================\n";
printf "Results: %o passed, %o failed\n", n_passed, n_failed;
if n_failed eq 0 then
    printf "ALL TESTS PASSED\n";
else
    printf "SOME TESTS FAILED\n";
    if assigned batch then quit 1; end if;
end if;
printf "=============================================================\n";
