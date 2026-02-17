//============================================================================
// Tracetest.m - Trace computations using OptTrace from Trace.m
//
// Each procedure mirrors the corresponding one in idempotent_tests.m,
// but uses OptTrace to compute dimensions via optimized light leaves
// instead of manual partial trace constructions.
//============================================================================
AttachSpec("ASLoc.spec");

//============================================================================
// B2: d = 1, x = 121
//============================================================================
procedure B2_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    cartanMat := CartanMatrix("B2");
    W := CoxeterGroup(GrpFPCox, cartanMat);
    B := BSCategory(CartanMatrix("B2"), W);
    FR := B`FR;

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,2,1];
    xdual_word := [1,2,1];
    z_word := [1];
    root := 3/2*FR.1 + 2*FR.2;
    k := 1;

    // Find all light leaves expressions
    full_word := x_word cat xdual_word;
    z_elt := W ! z_word;
    degree := -k;
    subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
    candidates := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];
    printf "B2: Found %o candidate subexpressions\n", #candidates;

    trace_x := OptTrace(IC, root, x_word, z_word, x_word, k);
    printf "B2: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    printf "B2: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "B2: dim = %o\n", dim;
    else
        printf "B2: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "B2: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// G2: d = 1, x = 12121
//============================================================================
procedure G2_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    cartanMat := CartanMatrix("G2");
    W := CoxeterGroup(GrpFPCox, cartanMat);
    B := BSCategory(CartanMatrix("G2"), W);
    FR := B`FR;

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,2,1,2,1];
    xdual_word := [1,2,1,2,1];
    z_word := [1];
    root := 5*FR.1 + 3*FR.2;
    k := 1;

    full_word := x_word cat xdual_word;
    z_elt := W ! z_word;
    degree := -k;
    subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
    candidates := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];
    printf "G2: Found %o candidate subexpressions\n", #candidates;

    trace_x := OptTrace(IC, root, x_word, z_word, x_word, k);
    printf "G2: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    printf "G2: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "G2: dim = %o\n", dim;
    else
        printf "G2: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "G2: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H3 a-value 1: d = 1, x = 121
//============================================================================
procedure H3_a1_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");
    f := BaseRing(carH3);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,2,1];
    xdual_word := [1,2,1];
    z_word := [1];
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    k := 1;

    full_word := x_word cat xdual_word;
    z_elt := W ! z_word;
    degree := -k;
    subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
    candidates := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];
    printf "H3_a1: Found %o candidate subexpressions\n", #candidates;

    trace_x := OptTrace(IC, root, x_word, z_word, x_word, k);
    printf "H3_a1: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    printf "H3_a1: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "H3_a1: dim = %o\n", dim;
    else
        printf "H3_a1: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H3_a1: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H3 a-value 3: d = 232, x = 232123
//============================================================================
procedure H3_a3_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");
    f := BaseRing(carH3);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [2,3,2,1,2,3];
    xdual_word := [2,3,2,1,2,3];
    z_word := [2,3,2];
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    k := 3;

    full_word := x_word cat xdual_word;
    z_elt := W ! z_word;
    degree := -k;
    subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
    candidates := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];
    printf "H3_a3: Found %o candidate subexpressions\n", #candidates;

    trace_x := OptTrace(IC, root, x_word, z_word, x_word, k);
    printf "H3_a3: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    printf "H3_a3: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_x / trace_d;
        printf "H3_a3: dim = %o\n", dim;
    else
        printf "H3_a3: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H3_a3: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H3 long (a-value 6): d = 12121321213212, x = 1212132121
//============================================================================
procedure H3_long_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH3 := CartanMatrix("H3");
    W := CoxeterGroup(GrpFPCox, "H3");
    f := BaseRing(carH3);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH3;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH3[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,2,1,2,1,3,2,1,2,1];
    xdual_word := [1,2,1,2,1,3,2,1,2,1];
    z_word := [1,2,1,2,1,3,2,1,2,1,3,2,1,2];
    root := (9*f.1+6)/2*FR.1 + (5*f.1+4)*FR.2 + (5*f.1+5)/2*FR.3;
    k := 6;

    //Manual setting of 01-expressions, d,x -> x
    expr_x := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0 ];
    // x,x -> d:
    expr_d :=  [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0 ];

    //trace_x := OptTrace(IC, root, z_word, x_word, x_word, k);
    trace_x := OptTrace(IC, root, z_word, x_word, x_word, k : Exprs := [expr_x]);
    printf "H3_long: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k : Exprs := [expr_d]);
    //trace_d := OptTrace(IC, root, z_word, Reverse(z_word), z_word, k : Exprs := [expr_d]);
    printf "H3_long: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "H3_long: dim = %o\n", dim;
    else
        printf "H3_long: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H3_long: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H4 (a-value 2): d = 13, x = 132143
//============================================================================
procedure H4_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");
    f := BaseRing(carH4);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,3,2,1,4,3];
    xdual_word := [1,3,2,1,4,3];
    z_word := [1,3];
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    k := 2;

    full_word := x_word cat xdual_word;
    z_elt := W ! z_word;
    degree := -k;
    subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
    candidates := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];
    printf "H4: Found %o candidate subexpressions\n", #candidates;

    trace_x := OptTrace(IC, root, x_word, z_word, x_word, k);
    printf "H4: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    printf "H4: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "H4: dim = %o\n", dim;
    else
        printf "H4: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H4: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H4 middle cell 1: d = 232432, x = 2324321234
//============================================================================
procedure H4_middle_1_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");
    f := BaseRing(carH4);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x2_word := [2,3,2,4,3,2,1,2,3,4];
    xdual2_word := [2,3,2,4,3,2,1,2,3,4];
    z_word := [2,3,2,4,3,2];
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    k := 6;

    expr_x2 := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0 ];
    expr_d := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0 ];

    trace_x2 := OptTrace(IC, root, x2_word, z_word, x2_word, k  : Exprs := [expr_x2] );
    printf "H4_middle_1: trace(x2) = %o\n", trace_x2;

    //trace_d := OptTrace(IC, root, x2_word, xdual2_word, z_word, k);
    trace_d := OptTrace(IC, root, x2_word, xdual2_word, z_word, k : Exprs := [expr_d]);
    printf "H4_middle_1: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x2 ne 0 then
        dim := trace_d / trace_x2;
        printf "H4_middle_1: dim of x2 = %o\n", dim;
    else
        printf "H4_middle_1: a trace is zero, cannot compute dimension\n";
    end if;

    x3_word := [2,3,2,4,3,2,1,2,3,4,1,2,3,4];
    xdual3_word := [2,3,2,4,3,2,1,2,3,4,1,2,3,4];

    //Find right expression to make it faster
    expr_x3 := [ 1,1,1,1,1,1,0,0,0,0,0,0,1,1,1,1,1,1,1,1 ];
    expr_d := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0 ];

    //trace_x3 := OptTrace(IC, root, x3_word, z_word, x3_word, k);
    trace_x3 := OptTrace(IC, root, z_word, x3_word, x3_word, k : Exprs := [expr_x3]);
    printf "H4_middle_1: trace(x3) = %o\n", trace_x3;

    //trace_d := OptTrace(IC, root, x3_word, xdual3_word, z_word, k);
    trace_d := OptTrace(IC, root, x3_word, xdual3_word, z_word, k : Exprs := [expr_d]);
    printf "H4_middle_1: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x3 ne 0 then
        dim := trace_x3 / trace_d;
        printf "H4_middle_1: dim of x3 = %o\n", dim;
    else
        printf "H4_middle_1: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H4_middle_1: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H4 middle cell 9: d = 121214, x = 121214342121
//============================================================================
procedure H4_middle_9_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");
    f := BaseRing(carH4);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,2,1,2,1,4,3,4,2,1,2,1];
    xdual_word := [1,2,1,2,1,4,3,4,2,1,2,1];
    z_word := [1,2,1,2,1,4];
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    k := 6;

    //These should be correct
    expr_x :=  [ 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1 ];
    expr_d := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0 ];

    trace_x := OptTrace(IC, root, z_word, x_word, x_word, k:  Exprs := [expr_x]);
    printf "H4_middle_9: trace(x) = %o\n", trace_x;

    //trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k : Exprs := [expr_d]);
    printf "H4_middle_9: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "H4_middle_9: dim = %o\n", dim;
    else
        printf "H4_middle_9: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H4_middle_9: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// H4 middle cell 19: d = 12121321213212
//   x1 = 1212132121, x3 = 1212132121432121
//============================================================================
procedure H4_middle_19_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    carH4 := CartanMatrix("H4");
    W := CoxeterGroup(GrpFPCox, "H4");
    f := BaseRing(carH4);
    FR := RationalFunctionField(f, Rank(W));

    B := New(BSCat);
    B`C := carH4;
    B`W := W;
    B`FR := FR;
    B`FAct := [hom< FR -> FR | [FR.t - carH4[t, s]*FR.s : t in [1..Rank(W)]] > : s in [1..Rank(W)]];
    B`FActionByEltCache := AssociativeArray();
    B`BraidCache := AssociativeArray();

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    z_word := [1,2,1,2,1,3,2,1,2,1,3,2,1,2];
    root := (42*f.1+26)*FR.1 + (51*f.1+33)*FR.2 + (34*f.1+23)*FR.3 + (17*f.1+12)*FR.4;
    k := 6;

    // Trace for x1 = 1212132121. Same as in H3 case
    x1_word := [1,2,1,2,1,3,2,1,2,1];
    xdual1_word := [1,2,1,2,1,3,2,1,2,1];


    expr_x1 := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0 ];
    // x,x -> d:
    expr_d :=  [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0 ];

    trace_x1 := OptTrace(IC, root, z_word, x1_word, x1_word, k : Exprs := [expr_x1]);
    printf "H4_middle_19: trace(x1) = %o\n", trace_x1;

    trace_d := OptTrace(IC, root, x1_word, xdual1_word, z_word, k : Exprs := [expr_d]);

    printf "H4_middle_19: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x1 ne 0 then
        printf "H4_middle_19: dim(x1) = %o\n", trace_d / trace_x1;
    else
        printf "H4_middle_19: x1 trace is zero, cannot compute dimension\n";
    end if;

    // Trace for x3 = 1212132121432121
    x3_word := [1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1];
    xdual3_word := [1,2,1,2,1,3,2,1,2,1,4,3,2,1,2,1];
    expr_x3 := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0, 0,1,1,1,1,1,1 ];
    expr_d := [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 0, 0,
    0, 1, 1, 1, 1, 1, 0 ];

    //trace_x3 := OptTrace(IC, root, z_word, x3_word, x3_word, k);
    trace_x3 := OptTrace(IC, root, x3_word, z_word, x3_word, k : Exprs := [expr_x3]);
    printf "H4_middle_19: trace(x3) = %o\n", trace_x3;

    trace_d := OptTrace(IC, root, x3_word, x3dual_word, z_word k : Exps := [expr_d]);
    printf "H4_middle_19: trace(d) = %o\n", trace_d;


    if trace_d ne 0 and trace_x3 ne 0 then
        printf "H4_middle_19: dim(x3) = %o\n", trace_d / trace_x3;
    else
        printf "H4_middle_19: x3 trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "H4_middle_19: Time = %o, Space = %o\n\n", T, S;
end procedure;

//============================================================================
// F4: d = 1434, x = 14342341, x_dual = 14324341 (reverse)
//============================================================================
procedure F4_trace()
    ResetMaximumMemoryUsage();
    T := Time();

    cartanMat := CartanMatrix("F4");
    W := CoxeterGroup(GrpFPCox, cartanMat);
    B := BSCategory(CartanMatrix("F4"), W);
    FR := B`FR;

    HAlg := IHeckeAlgebra(W);
    C := CanonicalBasis(HAlg);

    act := function(w)
        return FActionByElt(B, w);
    end function;

    IC := CreateOptIdemCollection(B, C, act);

    x_word := [1,3,4,3,2,3,4,1];
    xdual_word := [1,4,3,2,3,4,3,1];
    z_word := [1,3,4,3];
    root := 8*FR.1 + 15*FR.2 + 21*FR.3 + 11*FR.4;
    k := 4;
    //The idempotents created should have the word 13432134, therefore we need different expression

    //expr_x := [1,1,1,1,1,0,1,1,1,0,0,0];

    //expr_d := [1,1,1,1, 0,0,0,0];

    trace_x := OptTrace(IC, root, z_word, x_word, x_word, k );
    //trace_x := OptTrace(IC, root, z_word, x_word, x_word, k : Exprs := [expr_x]);
    printf "F4: trace(x) = %o\n", trace_x;

    trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k);
    //trace_d := OptTrace(IC, root, x_word, xdual_word, z_word, k : Exps := [expr_d]);
    printf "F4: trace(d) = %o\n", trace_d;

    if trace_d ne 0 and trace_x ne 0 then
        dim := trace_d / trace_x;
        printf "F4: dim = %o\n", dim;
    else
        printf "F4: a trace is zero, cannot compute dimension\n";
    end if;

    T := Time(T);
    S := GetMaximumMemoryUsage();
    printf "F4: Time = %o, Space = %o\n\n", T, S;
end procedure;
