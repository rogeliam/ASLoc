//============================================================================
// Trace.m - Optimized Light Leaf for Concatenated Words (Trace Computation)
//
// Provides LLOptTwoDownTo / LLOptTwoUpTo for computing light leaves on
// concatenated words x.y, working entirely in reduced (optimized) coordinates.
//
// LLOptTwoDownTo: reduced_ex ⊗ reduced_ey  -->  reduced_ez
// LLOptTwoUpTo:   reduced_ez  -->  reduced_ex ⊗ reduced_ey   (dual)
//
// OptTrace: Computes trace = sum over subexpressions of
//   LLOptTwoDownTo * Tensor(e_x, rho^k, e_xdual) * LLOptTwoUpTo
// Returns the scalar c such that result = c * e_z`reduced_matrix.
//
// Algorithm for LLOptTwoDownTo:
//   1. Use LLOptDownTo on opt_ex with the x-part of expr.
//      This gives ll_x : reduced_ex -> reduced_xprime (or zero).
//   2. Now expr on x' is all 1s. Process y one letter at a time:
//      Peel last reflection s from wu (via braid_on_opt_idempotent or
//      GetPrefixInclProj) and first reflection t from ey_remaining
//      (via GetSuffixInclProj), exposing the junction B_s ⊗ B_t.
//      Apply the appropriate operation based on decoration:
//        U0: Counit on B_t           -> reduced_wu  ⊗ reduced_ey'
//        U1: absorb B_t into wu      -> reduced_wu·t ⊗ reduced_ey'
//        D0: Mult on B_s ⊗ B_t      -> reduced_wu  ⊗ reduced_ey'
//        D1: Cap on B_s ⊗ B_t       -> reduced_wu' ⊗ reduced_ey'
//      (with braiding when last letter of wu ≠ t in D cases)
//============================================================================

import "IdemCalcOpt.m": braid_on_opt_idempotent, stitch_opt_idempotents;

declare verbose Trace, 3;

//============================================================================
// LLOptTwoDownTo
//============================================================================

intrinsic LLOptTwoDownTo(IC::OptIdemCollection, opt_ex::OptIdempotent,
    opt_ey::OptIdempotent, opt_ez::OptIdempotent,
    expr::SeqEnum[RngIntElt]) -> Any
{Optimized light leaf going down on the concatenated word [x, y],
 from reduced_ex ⊗ reduced_ey to reduced_ez.

 expr has length #Eltseq(x) + #Eltseq(y).
 Returns a StdMor in reduced form (or zero).}

    B := IC`B;
    W := IC`W;
    act := IC`act;

    x_seq := GetPrefixWord(opt_ex);
    y_seq := GetSuffixWord(opt_ey);
    nx := #x_seq;
    ny := #y_seq;

    require #expr eq nx + ny:
        "Expression length", #expr, "must match #x + #y =", nx + ny;

    expr_x := expr[1..nx];
    expr_y := expr[nx+1..nx+ny];

    vprintf Trace, 1: "LLOptTwoDownTo: x=%o, y=%o, z=%o, expr=%o\n",
        x_seq, y_seq, Eltseq(opt_ez`element), expr;

    // Step 1: Compute the light leaf on the x-part.
    // Determine x': the element that expr_x evaluates to on word x.
    xprime := Id(W);
    for i := 1 to nx do
        if expr_x[i] eq 1 then
            xprime := xprime * W.x_seq[i];
        end if;
    end for;
    opt_xprime := BuildOptIdempotent(IC, xprime);

    ll_x := LLOptDownTo(IC, opt_ex, opt_xprime, expr_x);

    // If ll_x is zero, the whole thing is zero.
    if IsZero(ll_x) then
        vprintf Trace, 2: "LLOptTwoDownTo: x-part is zero, returning zero\n";
        return 0;
    end if;

    // Step 2: Process the y-part step by step.
    // leaf accumulates the map: reduced_xprime ⊗ reduced_ey -> current state
    // wu tracks the left factor element (starts at x').
    //
    // At each step j, the current state is reduced_wu ⊗ reduced_ey_cur
    // where ey_cur = y[j..ny].
    // We build a step_map: reduced_wu ⊗ reduced_ey_cur -> reduced_wu_new ⊗ reduced_ey_rest
    // and compose: leaf := step_map * leaf.
    //
    // After all steps, leaf maps reduced_xprime ⊗ reduced_ey -> reduced_ez.
    // Final result = leaf * (ll_x ⊗ id_ey).

    wu := xprime;
    // leaf will accumulate the map:
    //   reduced_xprime ⊗ reduced_ey -> reduced_wu_final (= reduced_ez)
    // Built step by step: leaf := step * leaf at each iteration.

    for j := 1 to ny do
        si := y_seq[j];  // current letter from y
        ei := expr_y[j];
        going_up := Length(wu * W.si) gt Length(wu);

        opt_wu := BuildOptIdempotent(IC, wu);
        wu_seq := Eltseq(wu);

        // Current ey_cur = y[j..ny], its first letter is si
        ey_cur := W ! y_seq[j..ny];
        opt_ey_cur := BuildOptIdempotent(IC, ey_cur);

        // Peel first reflection from ey_cur:
        // GetSuffixInclProj(IC, opt_ey_cur, 1):
        //   proj_ey: B_si ⊗ reduced_ey_rest -> reduced_ey_cur  (collapse)
        //   incl_ey: reduced_ey_cur -> B_si ⊗ reduced_ey_rest  (expand)
        proj_ey, incl_ey := GetSuffixInclProj(IC, opt_ey_cur, 1);

        vprintf Trace, 2: "  Step j=%o: si=%o, ei=%o, wu=%o, going_up=%o\n",
            j, si, ei, wu, going_up;

        if going_up then
            // wu * si is longer: si is an ascent of wu.
            // We don't need to peel from wu, only from ey.
            if ei eq 0 then
                // U0: Counit on B_si.
                // Map: reduced_wu ⊗ reduced_ey_cur
                //   -> (via id_wu ⊗ incl_ey) reduced_wu ⊗ B_si ⊗ reduced_ey_rest
                //   -> (via id_wu ⊗ Counit(si) ⊗ id_ey_rest) reduced_wu ⊗ reduced_ey_rest
                vprintf Trace, 2: "    U0: Counit at si=%o\n", si;
                if j lt ny then
                    ey_rest := W ! y_seq[j+1..ny];
                    opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                    step := Tensor(act, opt_wu`reduced_matrix, Tensor(act, Counit(B, si)`stdmor, opt_ey_rest`reduced_matrix)) * Tensor(act, opt_wu`reduced_matrix, incl_ey);
                else
                    step := Tensor(act, opt_wu`reduced_matrix, Counit(B, si)`stdmor) * Tensor(act, opt_wu`reduced_matrix, incl_ey);
                end if;
                // wu unchanged
            else
                // U1: absorb si into wu. wu -> wu * si.
                // Map: reduced_wu ⊗ reduced_ey_cur
                //   -> (via id_wu ⊗ proj_ey) reduced_wu ⊗ B_si ⊗ reduced_ey_rest
                //   -> (via incl_wu_si ⊗ id_ey_rest) reduced_{wu·si} ⊗ reduced_ey_rest
                // where incl_wu_si = get_proj_at_si (proj goes B_si ⊗ ... -> reduced_{wu·si})
                vprintf Trace, 2: "    U1: absorb si=%o into wu\n", si;
                wusi := wu * W.si;
                opt_wusi := BuildOptIdempotent(IC, wusi);
                pu := GetProjAtSi(IC, opt_wusi, si);
                // pu: reduced_wu ⊗ B_si -> reduced_{wu·si}
                if j lt ny then
                    ey_rest := W ! y_seq[j+1..ny];
                    opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                    step := Tensor(act, pu, opt_ey_rest`reduced_matrix) * Tensor(act, opt_wu`reduced_matrix, incl_ey);
                else
                    step := pu * Tensor(act, opt_wu`reduced_matrix, incl_ey);
                end if;
                wu := wusi;
            end if;
        else
            // wu * si is shorter: si is a descent of wu.
            // We peel last reflection from wu AND first from ey.
            wu_seq := Eltseq(wu);

            if wu_seq[#wu_seq] eq si then
                // Last letter of wu matches si: no braiding needed.
                pu_wu, iu_wu := GetPrefixInclProj(IC, opt_wu, #wu_seq);
                // pu_wu: reduced_wu -> reduced_wu' ⊗ B_si
                // iu_wu: reduced_wu' ⊗ B_si -> reduced_wu
                opt_wu_short := BuildOptIdempotent(IC, W ! wu_seq[1..#wu_seq-1]);

                if ei eq 0 then
                    // D0: Mult on B_si ⊗ B_si.
                    // Map: reduced_wu ⊗ reduced_ey_cur
                    //   -> (via pu_wu ⊗ proj_ey) reduced_wu' ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via id_wu' ⊗ Mult(si) ⊗ id_ey_rest) reduced_wu' ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via iu_wu ⊗ id_ey_rest) reduced_wu ⊗ reduced_ey_rest
                    vprintf Trace, 2: "    D0: Mult at si=%o (no braid)\n", si;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        step := Tensor(act, pu_wu, id_ey_rest) * Tensor(act, opt_wu_short`reduced_matrix, Tensor(act, Mult(B, si)`stdmor, id_ey_rest)) *    Tensor(act, iu_wu, incl_ey);
                    else
                         step := pu_wu * Tensor(act, opt_wu_short`reduced_matrix, Mult(B, si)`stdmor) * Tensor(act, iu_wu, incl_ey);
                    end if;
                    // wu unchanged
                else
                    // D1: Cap on B_si ⊗ B_si.
                    // Map: reduced_wu ⊗ reduced_ey_cur
                    //   -> (via pu_wu ⊗ proj_ey) reduced_wu' ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via id_wu' ⊗ Cap(si) ⊗ id_ey_rest) reduced_wu' ⊗ reduced_ey_rest
                    vprintf Trace, 2: "    D1: Cap at si=%o (no braid)\n", si;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        step := Tensor(act, opt_wu_short`reduced_matrix, id_ey_rest) * Tensor(act, opt_wu_short`reduced_matrix, Tensor(act, Cap(B, si)`stdmor, id_ey_rest)) *  Tensor(act, iu_wu, incl_ey);
                    else
                        step := opt_wu_short`reduced_matrix *  Tensor(act, opt_wu_short`reduced_matrix, Cap(B, si)`stdmor) * Tensor(act, iu_wu, incl_ey);
                    end if;
                    wu := wu * W.si;  // D1: wu shrinks (wu' = wu[1..n-1], then wu = wu·si shorter)
                end if;
            else
                // Last letter of wu ≠ si: need to braid wu to end with si.
                ey_braid, z, braidmap, braidmapinv := braid_on_opt_idempotent(IC, opt_wu, si);
                // braidmap: reduced_wu -> reduced_ey_braid ⊗ BS(z)  where z ends with si
                // braidmapinv: reduced_ey_braid ⊗ BS(z) -> reduced_wu
                z_prefix := z[1..#z-1];

                if ei eq 0 then
                    // D-braid-0: Mult on B_si ⊗ B_si after braiding.
                    // Map: reduced_wu ⊗ reduced_ey_cur
                    //   -> (via braidmap ⊗ proj_ey) reduced_ey_braid ⊗ BS(z) ⊗ B_si ⊗ reduced_ey_rest
                    //      (z ends with si, so BS(z) = BS(z_prefix) ⊗ B_si)
                    //   -> (via id ⊗ Mult(si) ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via braidmapinv ⊗ id) reduced_wu ⊗ reduced_ey_rest
                    vprintf Trace, 2: "    D0-braid: Mult at si=%o (braided z=%o)\n", si, z;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        mult_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Tensor(act, Mult(B, si)`stdmor, id_ey_rest)));
                        step := Tensor(act, braidmapinv, id_ey_rest) * mult_mid * Tensor(act, braidmap, incl_ey);
                    else
                        mult_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Mult(B, si)`stdmor));
                        step := braidmapinv * mult_mid * Tensor(act, braidmap, incl_ey);
                    end if;
                    // wu unchanged
                else
                    // D-braid-1: Cap on B_si ⊗ B_si after braiding, then stitch.
                    // Map: reduced_wu ⊗ reduced_ey_cur
                    //   -> (via braidmap ⊗ proj_ey) reduced_ey_braid ⊗ BS(z_prefix) ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via id ⊗ Cap(si) ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ reduced_ey_rest
                    //   -> (via stitch ⊗ id) reduced_{wu·si} ⊗ reduced_ey_rest
                    vprintf Trace, 2: "    D1-braid: Cap at si=%o (braided z=%o)\n", si, z;
                    wusi := wu * W.si;
                    opt_wusi := BuildOptIdempotent(IC, wusi);
                    stitch, _ := stitch_opt_idempotents(IC, ey_braid, z_prefix, opt_wusi, []);
                    // stitch: reduced_ey_braid ⊗ BS(z_prefix) -> reduced_{wu·si}

                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        cap_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Tensor(act, Cap(B, si)`stdmor, id_ey_rest)));
                        step := Tensor(act, stitch, id_ey_rest) * cap_mid * Tensor(act, braidmap, incl_ey);
                    else
                        cap_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Cap(B, si)`stdmor));
                        step := stitch * cap_mid * Tensor(act, braidmap, incl_ey);
                    end if;
                    wu := wusi;
                end if;
            end if;
        end if;

        // Compose: if this is the first step, leaf = step
        // otherwise, leaf = step * leaf
        if j eq 1 then
            leaf := step;
        else
            leaf := step * leaf;
        end if;

        vprintf Trace, 3: "    leaf size: %o x %o\n", Nrows(leaf`mat), Ncols(leaf`mat);
    end for;

    // Final result: leaf * (ll_x ⊗ id_ey)
    // leaf : reduced_xprime ⊗ reduced_ey -> reduced_ez
    // ll_x ⊗ id_ey : reduced_ex ⊗ reduced_ey -> reduced_xprime ⊗ reduced_ey
    result := leaf * Tensor(act, ll_x, opt_ey`reduced_matrix);

    vprintf Trace, 1: "LLOptTwoDownTo done: result %o x %o\n", Nrows(result`mat), Ncols(result`mat);
    return result;
end intrinsic;

//============================================================================
// LLOptTwoUpTo (dual)
//============================================================================

intrinsic LLOptTwoUpTo(IC::OptIdemCollection, opt_ex::OptIdempotent,
    opt_ey::OptIdempotent, opt_ez::OptIdempotent,
    expr::SeqEnum[RngIntElt]) -> Any
{Optimized light leaf going up on the concatenated word [x, y],
 from reduced_ez to reduced_ex ⊗ reduced_ey.
 Dual of LLOptTwoDownTo.

 expr has length #Eltseq(x) + #Eltseq(y).
 Returns a StdMor in reduced form (or zero).}

    B := IC`B;
    W := IC`W;
    act := IC`act;

    x_seq := GetPrefixWord(opt_ex);
    y_seq := GetSuffixWord(opt_ey);
    nx := #x_seq;
    ny := #y_seq;

    require #expr eq nx + ny:
        "Expression length", #expr, "must match #x + #y =", nx + ny;

    expr_x := expr[1..nx];
    expr_y := expr[nx+1..nx+ny];

    vprintf Trace, 1: "LLOptTwoUpTo: x=%o, y=%o, z=%o, expr=%o\n",
        x_seq, y_seq, Eltseq(opt_ez`element), expr;

    // Step 1: Compute the light leaf on the x-part.
    // Determine x': the element that expr_x evaluates to on word x.
    xprime := Id(W);
    for i := 1 to nx do
        if expr_x[i] eq 1 then
            xprime := xprime * W.x_seq[i];
        end if;
    end for;
    opt_xprime := BuildOptIdempotent(IC, xprime);

    ll_x := LLOptUpTo(IC, opt_ex, opt_xprime, expr_x);

    // If ll_x is zero, the whole thing is zero.
    if IsZero(ll_x) then
        vprintf Trace, 2: "LLOptTwoUpTo: x-part is zero, returning zero\n";
        return 0;
    end if;

    // Step 2: Process the y-part step by step.
    // leaf accumulates the map: reduced_ez -> reduced_xprime ⊗ reduced_ey
    // wu tracks the left factor element (starts at x').
    //
    // At each step j, the current state domain is reduced_wu ⊗ reduced_ey_cur
    // where ey_cur = y[j..ny].
    // We build a step_map with domain reduced_wu_new ⊗ reduced_ey_rest
    // and compose: leaf := leaf * step (compose on the right).
    //
    // After all steps, leaf maps reduced_ez -> reduced_xprime ⊗ reduced_ey.
    // Final result = (ll_x ⊗ id_ey) * leaf.

    wu := xprime;
    // leaf will accumulate the map:
    //   reduced_ez -> reduced_xprime ⊗ reduced_ey
    // Built step by step: leaf := leaf * step at each iteration.

    for j := 1 to ny do
        si := y_seq[j];  // current letter from y
        ei := expr_y[j];
        going_up := Length(wu * W.si) gt Length(wu);

        opt_wu := BuildOptIdempotent(IC, wu);
        wu_seq := Eltseq(wu);

        // Current ey_cur = y[j..ny], its first letter is si
        ey_cur := W ! y_seq[j..ny];
        opt_ey_cur := BuildOptIdempotent(IC, ey_cur);

        // Peel first reflection from ey_cur:
        // GetSuffixInclProj(IC, opt_ey_cur, 1):
        //   proj_ey: B_si ⊗ reduced_ey_rest -> reduced_ey_cur  (collapse)
        //   incl_ey: reduced_ey_cur -> B_si ⊗ reduced_ey_rest  (expand)
        proj_ey, incl_ey := GetSuffixInclProj(IC, opt_ey_cur, 1);

        vprintf Trace, 2: "  Step j=%o: si=%o, ei=%o, wu=%o, going_up=%o\n",
            j, si, ei, wu, going_up;

        if going_up then
            // wu * si is longer: si is an ascent of wu.
            // We don't need to peel from wu, only from ey.
            if ei eq 0 then
                // U0 dual: Unit on B_si (dual of Counit).
                // Map: reduced_wu ⊗ reduced_ey_rest
                //   -> (via id_wu ⊗ Unit(si) ⊗ id_ey_rest) reduced_wu ⊗ B_si ⊗ reduced_ey_rest
                //   -> (via id_wu ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                vprintf Trace, 2: "    U0: Unit at si=%o\n", si;
                if j lt ny then
                    ey_rest := W ! y_seq[j+1..ny];
                    opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                    step := Tensor(act, opt_wu`reduced_matrix, proj_ey) * Tensor(act, opt_wu`reduced_matrix, Tensor(act, Unit(B, si)`stdmor, opt_ey_rest`reduced_matrix));
                else
                    step := Tensor(act, opt_wu`reduced_matrix, incl_ey) * Tensor(act, opt_wu`reduced_matrix, Unit(B, si)`stdmor);
                end if;
                // wu unchanged
            else
                // U1 dual: split si out of wu. wu -> wu * si (dual direction).
                // Map: reduced_{wu·si} ⊗ reduced_ey_rest
                //   -> (via incl_wu_si ⊗ id_ey_rest) reduced_wu ⊗ B_si ⊗ reduced_ey_rest
                //   -> (via id_wu ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                // where incl_wu_si = get_incl_at_si (incl goes reduced_{wu·si} -> reduced_wu ⊗ B_si)
                vprintf Trace, 2: "    U1: split si=%o from wu\n", si;
                wusi := wu * W.si;
                opt_wusi := BuildOptIdempotent(IC, wusi);
                iu := GetInclAtSi(IC, opt_wusi, si);
                // iu: reduced_{wu·si} -> reduced_wu ⊗ B_si
                if j lt ny then
                    ey_rest := W ! y_seq[j+1..ny];
                    opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                    step := Tensor(act, opt_wu`reduced_matrix, proj_ey) * Tensor(act, iu, opt_ey_rest`reduced_matrix);
                else
                    step := Tensor(act, opt_wu`reduced_matrix, proj_ey) * iu;
                end if;
                wu := wusi;
            end if;
        else
            // wu * si is shorter: si is a descent of wu.
            // We peel last reflection from wu AND first from ey.
            wu_seq := Eltseq(wu);

            if wu_seq[#wu_seq] eq si then
                // Last letter of wu matches si: no braiding needed.
                pu_wu, iu_wu := GetPrefixInclProj(IC, opt_wu, #wu_seq);
                // pu_wu: reduced_wu -> reduced_wu' ⊗ B_si
                // iu_wu: reduced_wu' ⊗ B_si -> reduced_wu
                opt_wu_short := BuildOptIdempotent(IC, W ! wu_seq[1..#wu_seq-1]);

                if ei eq 0 then
                    // D0 dual: Comult on B_si ⊗ B_si (dual of Mult).
                    // Map: reduced_wu ⊗ reduced_ey_rest
                    //   -> (via iu_wu ⊗ id_ey_rest) reduced_wu' ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via id_wu' ⊗ Comult(si) ⊗ id_ey_rest) reduced_wu' ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via pu_wu ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                    vprintf Trace, 2: "    D0: Comult at si=%o (no braid)\n", si;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        step := Tensor(act, pu_wu, proj_ey) * Tensor(act, opt_wu_short`reduced_matrix, Tensor(act, Comult(B, si)`stdmor, id_ey_rest)) * Tensor(act, iu_wu, id_ey_rest);
                    else
                        step := Tensor(act, pu_wu, proj_ey) * Tensor(act, opt_wu_short`reduced_matrix, Comult(B, si)`stdmor) *
                            iu_wu;
                    end if;
                    // wu unchanged
                else
                    // D1 dual: Cup on B_si ⊗ B_si (dual of Cap).
                    // Map: reduced_wu ⊗ reduced_ey_rest
                    //   -> (via id_wu' ⊗ Cup(si) ⊗ id_ey_rest) reduced_wu' ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via pu_wu ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                    vprintf Trace, 2: "    D1: Cup at si=%o (no braid)\n", si;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        step := Tensor(act, pu_wu, proj_ey) * Tensor(act, opt_wu_short`reduced_matrix, Tensor(act, Cup(B, si)`stdmor, id_ey_rest)) * Tensor(act, opt_wu_short`reduced_matrix, id_ey_rest);
                    else
                        step := Tensor(act, pu_wu, proj_ey) * Tensor(act, opt_wu_short`reduced_matrix, Cup(B, si)`stdmor) * opt_wu_short`reduced_matrix;
                    end if;
                    wu := wu * W.si;  // D1: wu shrinks (wu' = wu[1..n-1], then wu = wu·si shorter)
                end if;
            else
                // Last letter of wu ≠ si: need to braid wu to end with si.
                ey_braid, z, braidmap, braidmapinv := braid_on_opt_idempotent(IC, opt_wu, si);
                // braidmap: reduced_wu -> reduced_ey_braid ⊗ BS(z)  where z ends with si
                // braidmapinv: reduced_ey_braid ⊗ BS(z) -> reduced_wu
                z_prefix := z[1..#z-1];

                if ei eq 0 then
                    // D-braid-0 dual: Comult on B_si ⊗ B_si after braiding (dual of Mult).
                    // Map: reduced_wu ⊗ reduced_ey_rest
                    //   -> (via braidmapinv ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via id ⊗ Comult(si) ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //      (z ends with si, so BS(z) = BS(z_prefix) ⊗ B_si)
                    //   -> (via braidmap ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                    vprintf Trace, 2: "    D0-braid: Comult at si=%o (braided z=%o)\n", si, z;
                    bsi := BSId(B, [si])`stdmor;
                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        comult_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Tensor(act, Comult(B, si)`stdmor, id_ey_rest)));
                        step := Tensor(act, braidmapinv, proj_ey) * comult_mid * Tensor(act, braidmap, id_ey_rest);
                    else
                        comult_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Comult(B, si)`stdmor));
                        step := Tensor(act, braidmapinv, incl_ey) * comult_mid * braidmap;
                    end if;
                    // wu unchanged
                else
                    // D-braid-1 dual: Cup on B_si ⊗ B_si after braiding, then stitch (dual of Cap).
                    // Map: reduced_wu ⊗ reduced_ey_rest
                    //   -> (via stitch_up ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ reduced_ey_rest
                    //   -> (via id ⊗ Cup(si) ⊗ id) reduced_ey_braid ⊗ BS(z_prefix) ⊗ B_si ⊗ B_si ⊗ reduced_ey_rest
                    //   -> (via braidmap ⊗ incl_ey) reduced_wu ⊗ reduced_ey_cur
                    vprintf Trace, 2: "    D1-braid: Cup at si=%o (braided z=%o)\n", si, z;
                    wusi := wu * W.si;
                    opt_wusi := BuildOptIdempotent(IC, wusi);
                    _, stitch_up := stitch_opt_idempotents(IC, opt_wusi, [], ey_braid, z_prefix);
                    // stitch_up: reduced_{wu·si} -> reduced_ey_braid ⊗ BS(z_prefix)

                    if j lt ny then
                        ey_rest := W ! y_seq[j+1..ny];
                        opt_ey_rest := BuildOptIdempotent(IC, ey_rest);
                        id_ey_rest := opt_ey_rest`reduced_matrix;
                        cup_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Tensor(act, Cup(B, si)`stdmor, id_ey_rest)));
                        step := Tensor(act, braidmapinv, proj_ey) * cup_mid * Tensor(act, stitch_up, id_ey_rest);
                    else
                        cup_mid := Tensor(act, ey_braid`reduced_matrix, Tensor(act, BSId(B, z_prefix)`stdmor, Cup(B, si)`stdmor));
                        step := Tensor(act, braidmapinv, incl_ey) * cup_mid * stitch_up;
                    end if;
                    wu := wusi;
                end if;
            end if;
        end if;

        // Compose: if this is the first step, leaf = step
        // otherwise, leaf = leaf * step (compose on the right for dual)
        if j eq 1 then
            leaf := step;
        else
            leaf := leaf * step;
        end if;

        vprintf Trace, 3: "    leaf size: %o x %o\n", Nrows(leaf`mat), Ncols(leaf`mat);
    end for;

    // Final result: (ll_x ⊗ id_ey) * leaf
    // leaf : reduced_ez -> reduced_xprime ⊗ reduced_ey
    // ll_x ⊗ id_ey : reduced_xprime ⊗ reduced_ey -> reduced_ex ⊗ reduced_ey
    result := Tensor(act, ll_x, opt_ey`reduced_matrix) * leaf;

    vprintf Trace, 1: "LLOptTwoUpTo done: result %o x %o\n",
        Nrows(result`mat), Ncols(result`mat);
    return result;
end intrinsic;

//============================================================================
// OptTrace
//============================================================================

intrinsic OptTrace(IC::OptIdemCollection, rho::RngElt,
    x_word::SeqEnum[RngIntElt], xdual_word::SeqEnum[RngIntElt],
    z_word::SeqEnum[RngIntElt], k::RngIntElt
    : Exprs := []) -> Any
{Compute the trace of rho^k on the cell defined by x, x_dual, z.

 If Exprs is provided (non-empty), uses those subexpressions directly.
 Otherwise, finds all subexpressions of [x, x_dual] evaluating to z
 with degree = -k.

 For each subexpression computes
   LLOptTwoDownTo(e_x, e_xdual, e_z, expr)
     * Tensor(act, e_x, rho^k * e_xdual)
     * LLOptTwoUpTo(e_x, e_xdual, e_z, expr)
 Each non-zero result should be a scalar multiple of e_z`reduced_matrix.
 Returns the sum of those scalars.}

    W := IC`W;
    act := IC`act;

    x_elt := W ! x_word;
    xdual_elt := W ! xdual_word;
    z_elt := W ! z_word;

    opt_ex := BuildOptIdempotent(IC, x_elt);
    opt_exdual := BuildOptIdempotent(IC, xdual_elt);
    opt_ez := BuildOptIdempotent(IC, z_elt);

    // Use the actual words from the idempotent construction.
    // LLOptTwoDownTo uses prefix_word for x and suffix_word for xdual,
    // so subexpressions must be found on these actual words.
    x_actual := GetPrefixWord(opt_ex);
    xdual_actual := GetSuffixWord(opt_exdual);
    z_actual := GetPrefixWord(opt_ez);

    if #Exprs gt 0 then
        subexps := Exprs;
        vprintf Trace, 1: "OptTrace: x=%o, xdual=%o, z=%o, k=%o\n",
            x_actual, xdual_actual, z_actual, k;
        vprintf Trace, 1: "  Using %o provided subexpressions\n", #subexps;
    else
        // Find subexpressions evaluating to z
        full_word := x_actual cat xdual_actual;
        degree := -k;
        subexps := SubexpressionsEvaluatingTo(W, full_word, z_elt);
        subexps := [e : e in subexps | DeodharDefect(W, full_word, e) eq degree];

        vprintf Trace, 1: "OptTrace: x=%o, xdual=%o, z=%o, k=%o\n",
            x_actual, xdual_actual, z_actual, k;
        vprintf Trace, 1: "  Found %o subexpressions with degree %o\n", #subexps, degree;

        require #subexps gt 0:
            "No subexpressions found for word", full_word, "evaluating to",
            z_actual, "with degree", degree;
    end if;

    // The middle term: Tensor(act, e_x`reduced_matrix, rho^k * e_xdual`reduced_matrix)
    middle := Tensor(act, opt_ex`reduced_matrix, rho^k * opt_exdual`reduced_matrix);

    // Reference entry for extracting the scalar
    result_scalar := opt_ez`reduced_matrix`mat[1,1];

    found := false;

    for idx := 1 to #subexps do
        expr := subexps[idx];
        vprintf Trace, 2: "  Subexpression %o/%o: %o\n", idx, #subexps, expr;

        ll_down := LLOptTwoDownTo(IC, opt_ex, opt_exdual, opt_ez, expr);
        if Type(ll_down) eq RngIntElt and ll_down eq 0 then
            vprintf Trace, 2: "    -> zero (down)\n";
            continue;
        end if;

        ll_up := LLOptTwoUpTo(IC, opt_ex, opt_exdual, opt_ez, expr);
        if Type(ll_up) eq RngIntElt and ll_up eq 0 then
            vprintf Trace, 2: "    -> zero (up)\n";
            continue;
        end if;

        // Compute: ll_down * middle * ll_up
        // ll_down: reduced_ex ⊗ reduced_exdual -> reduced_ez
        // middle:  reduced_ex ⊗ reduced_exdual -> reduced_ex ⊗ reduced_exdual (scalar mult)
        // ll_up:   reduced_ez -> reduced_ex ⊗ reduced_exdual
        trace_term := ll_down * middle * ll_up;

        // Extract scalar: trace_term should be c * ez_mat
        c := trace_term`mat[1,1] / opt_ez`reduced_matrix`mat[1,1];

        vprintf Trace, 2: "    -> scalar = %o\n", c;

        if not found then
            result_scalar := c;
            found := true;
        else
            result_scalar +:= c;
        end if;
    end for;

    if not found then
        vprintf Trace, 1: "OptTrace: all subexpressions gave zero\n";
        return 0;
    end if;

    vprintf Trace, 1: "OptTrace: result = %o\n", result_scalar;
    return result_scalar;
end intrinsic;
