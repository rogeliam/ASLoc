// Tests for IdemCalc.m - Idempotent calculation package
// Quick tests using A3 (should complete in seconds)
if assigned batch then SetQuitOnError(true); else SetDebugOnError(true); end if;

AttachSpec("ASLoc.spec");
SetColumns(0);
SetAssertions(3);

// ============================================================
// Setup A3
// ============================================================
cartan := CartanMatrix("A3");
W := CoxeterGroup(GrpFPCox, cartan);
B := BSCategory(cartan, W);

HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

act := function(w)
    return FActionByElt(B, w);
end function;

IC := CreateIdemCollection(B, C, act);

n_passed := 0;
n_failed := 0;

// ============================================================
// Test 1: Basic idempotent construction
// ============================================================
printf "Test 1: Basic idempotent construction...\n";
test_elts := [W![1], W![1,2], W![2,1], W![1,2,3], W![1,2,1,3]];
try
    for x in test_elts do
        e := BuildIdempotent(IC, x);
        assert Type(e) ne RngIntElt;  // Should return a morphism, not 0
        printf "  %o: OK\n", Eltseq(x);
    end for;
    printf "Test 1 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 1 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 2: Idempotent property (e^2 = e)
// ============================================================
printf "Test 2: Idempotent property (e^2 = e)...\n";
try
    for x in test_elts do
        e := BuildIdempotent(IC, x);
        e_squared := e * e;
        assert e`mat eq e_squared`mat;
        printf "  %o: OK\n", Eltseq(x);
    end for;
    printf "Test 2 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 2 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 3: Cache functionality
// ============================================================
printf "Test 3: Cache functionality...\n";
try
    // Check elements are cached
    assert HasCachedIdempotent(IC, W![1]);
    assert HasCachedIdempotent(IC, W![1,2,1,3]);
    printf "  HasCachedIdempotent: OK\n";

    // Check cache count
    n_cached := NumberOfCachedIdempotents(IC);
    assert n_cached ge #test_elts;
    printf "  NumberOfCachedIdempotents (%o): OK\n", n_cached;

    // Check GetCachedIdempotent returns same result
    e_12 := BuildIdempotent(IC, W![1,2]);
    e_12_cached := GetCachedIdempotent(IC, W![1,2]);
    assert e_12`mat eq e_12_cached`mat;
    printf "  GetCachedIdempotent: OK\n";

    // Check CachedIdempotents list
    cached_list := CachedIdempotents(IC);
    assert #cached_list eq n_cached;
    printf "  CachedIdempotents: OK\n";

    // Check light leave cache
    n_ll := NumberOfCachedLightLeaves(IC);
    printf "  NumberOfCachedLightLeaves (%o): OK\n", n_ll;

    printf "Test 3 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 3 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 4: Longest element w_0 in A3
// ============================================================
printf "Test 4: Longest element w_0 in A3...\n";
try
    w0 := LongestElement(W);
    w0_seq := Eltseq(w0);
    printf "  w_0 = %o (length %o)\n", w0_seq, #w0_seq;

    e_w0 := BuildIdempotent(IC, w0);

    // Check idempotent property
    assert e_w0`mat eq (e_w0 * e_w0)`mat;
    printf "  Idempotent property: OK\n";

    // Check matrix size (2^6 = 64 for length 6 element)
    assert Nrows(e_w0`mat) eq 2^(#w0_seq);
    printf "  Matrix size %o x %o: OK\n", Nrows(e_w0`mat), Ncols(e_w0`mat);

    // Check rank is positive
    assert Rank(e_w0`mat) gt 0;
    printf "  Rank %o: OK\n", Rank(e_w0`mat);

    printf "Test 4 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 4 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 5: LLDownTo and LLUpFrom
// ============================================================
printf "Test 5: LLDownTo and LLUpFrom...\n";
try
    // Test light leaf from [1,2,1] down to [2] via subexp [0,1,0]
    bsword := [1,2,1];
    subexp := [0,1,0];
    target := [2];

    ll_down := LLDownTo(B, bsword, subexp, target);
    assert ll_down`bsdom eq bsword;
    assert ll_down`bscod eq target;
    printf "  LLDownTo [1,2,1] -> [2]: OK\n";

    ll_up := LLUpFrom(B, bsword, subexp, target);
    assert ll_up`bsdom eq target;
    assert ll_up`bscod eq bsword;
    printf "  LLUpFrom [2] -> [1,2,1]: OK\n";

    // Test with longer word
    bsword2 := [1,2,3,2];
    subexp2 := [1,0,1,0];  // selects [1,3]
    target2 := [1,3];

    ll_down2 := LLDownTo(B, bsword2, subexp2, target2);
    assert ll_down2`bsdom eq bsword2;
    assert ll_down2`bscod eq target2;
    printf "  LLDownTo [1,2,3,2] -> [1,3]: OK\n";

    printf "Test 5 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 5 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Test 6: Clear cache
// ============================================================
printf "Test 6: Clear cache...\n";
try
    // Clear only light leave cache
    ClearLightLeaveCache(IC);
    assert NumberOfCachedLightLeaves(IC) eq 0;
    assert NumberOfCachedIdempotents(IC) gt 0;  // Idempotents still there
    printf "  ClearLightLeaveCache: OK\n";

    // Clear only idempotent cache
    ClearIdempotentCache(IC);
    assert NumberOfCachedIdempotents(IC) eq 0;
    printf "  ClearIdempotentCache: OK\n";

    // Rebuild and clear all
    _ := BuildIdempotent(IC, W![1,2]);
    ClearCache(IC);
    assert NumberOfCachedIdempotents(IC) eq 0;
    assert NumberOfCachedLightLeaves(IC) eq 0;
    printf "  ClearCache: OK\n";

    printf "Test 6 PASSED\n\n";
    n_passed +:= 1;
catch err
    printf "Test 6 FAILED: %o\n\n", err`Object;
    n_failed +:= 1;
end try;

// ============================================================
// Summary
// ============================================================
printf "Results: %o passed, %o failed\n", n_passed, n_failed;
if n_failed eq 0 then
    printf "ALL TESTS PASSED\n";
else
    printf "SOME TESTS FAILED\n";
    if assigned batch then quit 1; end if;
end if;
