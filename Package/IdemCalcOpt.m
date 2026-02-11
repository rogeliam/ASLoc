//============================================================================
// IdemCalcOpt.m - Optimized Idempotent Calculation with Reduced Storage
// We again compute idempotents, as in IdemCalc.m; however we drastically
// reduce the size of the matrix in each step. This gives a considerable speed up
// TODO: Refer to explanation in Paper 2.
//============================================================================

import "StdCat.m": StdMorConstruct;
import "IdemCalcHelpers.m": find_all_light_leaves_expressions,
    find_smaller_elements_in_product,
    find_braid_morphism;
import "IdemCalcOptHelpers.m": PushRecursion, PopRecursion, PrintLLCheck,
    ClearLLLine, SetLightLeafTime;

//============================================================================
// Type Declarations
//============================================================================

declare type OptIdempotent;
declare attributes OptIdempotent:
    element,                // GrpFPCoxElt: The Coxeter group element
    reduced_matrix,         // StdMor: The reduced matrix (small!)

    // Prefix inclusions/projections (building from RIGHT)
    // B_sts is only a 6x6 matrix. While BS(sts) is a 8x8
    // With these inclusions we go back and forth.
    // I.e. prefix_incl[3] would embed B_sts into B_st x B_s, so a 8x6 matrix
    // prefix_incl[k] = inclusion from the k-th letter
    // prefix_incl[1] = full inclusion to word of length n
    prefix_incl,            // AssocArray: prefix_incl[k] = inclusion map at step k
    prefix_proj,            // AssocArray: prefix_proj[k] = projection map at step k
    prefix_word,            // SeqEnum[RngIntElt]: reduced word built from right
                            // For x = s1·s2·s3 built as (s1·s2)·s3, prefix_word = [s1, s2, s3]

    // Suffix inclusions/projections (building from LEFT)
    //Similar idea: suffix_incl[1] maps B_sts into B_s x B_ts
    // suffix_incl[k] = inclusion till k-th letter from left
    // suffix_incl[n] = identity to full length
    suffix_incl,            // AssocArray: suffix_incl[k] = inclusion map at step k
    suffix_proj,            // AssocArray: suffix_proj[k] = projection map at step k
    suffix_word,            // SeqEnum[RngIntElt]: reduced word built from left
                            // For x = t·z, suffix_word = [t] cat suffix_word(z)

    // Track how far we have computed
    min_prefix_computed,    // RngIntElt: Minimum k computed
    max_suffix_computed;    // RngIntElt: Maximum k computed

intrinsic Print(opt::OptIdempotent)
{Print an optimized idempotent}
    printf "Optimized idempotent for %o", opt`element;
end intrinsic;

declare type OptIdemCollection;
declare attributes OptIdemCollection:
    B,                      // The BSCat
    W,                      // The Coxeter group
    act,                    // The action function
    CanBasis,               // The canonical basis
    IdempotentCache,        // Cache for OptIdempotent objects
    LightLeaveCache,        // Cache for reduced light leaves
    // Progress tracking. Only for nicer printing
    ShowProgress,           // BoolElt: Whether to show progress
    RecursionStack,         // SeqEnum: Stack of [element, length] being computed
    LastLightLeafTime,      // FldReElt: Time spent on last light leaf computation
    TotalLightLeafTime,     // FldReElt: Total time spent on light leaves
    UseOptLL;               // BoolElt: Use LLOptDownTo/LLOptUpTo instead of standard LLDownTo/LLUpFrom

//============================================================================
// Constructor and Basic Operations
//============================================================================

intrinsic CreateOptIdemCollection(B::BSCat, C::., act::UserProgram : ShowProgress := false, UseOptLL := false) -> OptIdemCollection
{Create a new optimized idempotent collection}
    IC := New(OptIdemCollection);
    IC`B := B;
    IC`W := B`W;
    IC`act := act;
    IC`CanBasis := C;
    IC`IdempotentCache := AssociativeArray();
    IC`LightLeaveCache := AssociativeArray();
    // Initialize progress tracking
    IC`ShowProgress := ShowProgress;
    IC`RecursionStack := [];
    IC`LastLightLeafTime := 0.0;
    IC`TotalLightLeafTime := 0.0;
    IC`UseOptLL := UseOptLL;
    return IC;
end intrinsic;

intrinsic SetShowProgress(IC::OptIdemCollection, show::BoolElt)
{Enable or disable progress display}
    IC`ShowProgress := show;
end intrinsic;

intrinsic Print(IC::OptIdemCollection)
{Print an optimized idempotent collection}
    printf "Optimized idempotent collection for %o with %o cached idempotents and %o cached light leaves",
        IC`B, #Keys(IC`IdempotentCache), #Keys(IC`LightLeaveCache);
    if IC`TotalLightLeafTime gt 0 then
        printf " (total LL time: %.2os)", IC`TotalLightLeafTime;
    end if;
end intrinsic;

intrinsic ClearCache(IC::OptIdemCollection)
{Clear all caches}
    IC`IdempotentCache := AssociativeArray();
    IC`LightLeaveCache := AssociativeArray();
end intrinsic;

intrinsic ClearIdempotentCache(IC::OptIdemCollection)
{Clear only the idempotent cache}
    IC`IdempotentCache := AssociativeArray();
end intrinsic;

intrinsic ClearLightLeaveCache(IC::OptIdemCollection)
{Clear only the light leave cache}
    IC`LightLeaveCache := AssociativeArray();
end intrinsic;

intrinsic HasCachedIdempotent(IC::OptIdemCollection, x::GrpFPCoxElt) -> BoolElt
{Check if an idempotent is in the cache}
    return IsDefined(IC`IdempotentCache, Eltseq(x));
end intrinsic;

intrinsic GetCachedIdempotent(IC::OptIdemCollection, x::GrpFPCoxElt) -> OptIdempotent
{Get a cached idempotent}
    return IC`IdempotentCache[Eltseq(x)];
end intrinsic;

intrinsic NumberOfCachedIdempotents(IC::OptIdemCollection) -> RngIntElt
{Return the number of cached idempotents}
    return #Keys(IC`IdempotentCache);
end intrinsic;

intrinsic NumberOfCachedLightLeaves(IC::OptIdemCollection) -> RngIntElt
{Return the number of cached light leaves}
    return #Keys(IC`LightLeaveCache);
end intrinsic;

intrinsic CachedIdempotents(IC::OptIdemCollection) -> SeqEnum
{Return the list of cached idempotent elements}
    W := IC`W;
    return [W!k : k in Keys(IC`IdempotentCache)];
end intrinsic;

intrinsic GetReducedMatrix(opt::OptIdempotent) -> StdMor
{Get the reduced matrix from an optimized idempotent}
    return opt`reduced_matrix;
end intrinsic;

intrinsic GetFullIdempotent(IC::OptIdemCollection, opt::OptIdempotent) -> StdMor
{Reconstruct the full idempotent matrix from the optimized (reduced) form.
 This uses the prefix inclusions/projections to expand the reduced matrix.
 WARNING: Do not use this for large elements! The full matrix is 2^n x 2^n
 and will be far too large. Use the reduced_matrix and the Hecke algebra
 character evaluation to verify correctness instead.}
    proj, incl := GetPrefixInclProj(IC, opt, 1);
    return incl * opt`reduced_matrix * proj;
end intrinsic;

//============================================================================
// Forward declarations
//============================================================================

forward build_optimized_idempotent_internal, find_reduced_light_leave, find_reduced_light_leave_left,
    stitch_opt_idempotents;

//============================================================================
// Main Idempotent Construction (Optimized)
//============================================================================

function build_optimized_idempotent_internal(IC, x)
    key := Eltseq(x);

    // Check cache first
    if IsDefined(IC`IdempotentCache, key) then
        vprintf IdemCalcOpt, 2: "Using cached optimized idempotent for %o\n", x;
        return IC`IdempotentCache[key];
    end if;

    B := IC`B;
    W := IC`W;
    act := IC`act;

    seq_x := Eltseq(x);
    len := #seq_x;

    // Push onto recursion stack for progress display
    PushRecursion(IC, x);

    // Base case: length 0 (identity element)
    if len eq 0 then
        vprintf IdemCalcOpt, 2: "Base case: optimized idempotent for identity\n";
        e := BSId(B, [])`stdmor;

        opt := New(OptIdempotent);
        opt`element := x;
        opt`reduced_matrix := e;
        opt`prefix_incl := AssociativeArray();
        opt`prefix_proj := AssociativeArray();
        opt`prefix_word := [];
        opt`suffix_incl := AssociativeArray();
        opt`suffix_proj := AssociativeArray();
        opt`suffix_word := [];

        opt`min_prefix_computed := 1;
        opt`max_suffix_computed := 0;

        IC`IdempotentCache[key] := opt;
        PopRecursion(IC);
        return opt;
    end if;

    // Base case: length 1
    if len eq 1 then
        vprintf IdemCalcOpt, 2: "Base case: optimized idempotent for %o\n", x;
        e := BSId(B, seq_x[1])`stdmor;

        opt := New(OptIdempotent);
        opt`element := x;
        opt`reduced_matrix := e;
        opt`prefix_incl := AssociativeArray();
        opt`prefix_proj := AssociativeArray();
        opt`prefix_word := [seq_x[1]];
        opt`suffix_incl := AssociativeArray();
        opt`suffix_proj := AssociativeArray();
        opt`suffix_word := [seq_x[1]];

        // For length 1: both prefix and suffix at [1] are identity (trivial)
        opt`prefix_incl[1] := e;
        opt`prefix_proj[1] := e;
        opt`suffix_incl[1] := e;
        opt`suffix_proj[1] := e;

        opt`min_prefix_computed := 1;
        opt`max_suffix_computed := 1;

        IC`IdempotentCache[key] := opt;
        PopRecursion(IC);
        return opt;
    end if;

    vprintf IdemCalcOpt, 1: "Computing optimized idempotent of %o (length %o)\n", x, len;

    // ========================================================================
    // PREFIX CONSTRUCTION FROM RIGHT: x = y · s
    // Same construction as for IdemCalc; we have to use additional steps because of the optimizations
    // ========================================================================

    y := W!seq_x[1..len-1];
    s := W![seq_x[len]];

    // Get optimized idempotent for prefix
    opt_ey := build_optimized_idempotent_internal(IC, y);

    // Tensor with s (works on REDUCED form!)
    vprintf IdemCalcOpt, 2: "Computing tensor product opt_ex ⊗ s for x=%o, s=%o\n", y, s;
    fy_s := Tensor(act, opt_ey`reduced_matrix, [Id(W), s]);

    // Find correction terms using canonical basis
    smaller_elems := find_smaller_elements_in_product(W, IC`CanBasis, y, s);
    vprintf IdemCalcOpt, 2: "Found %o smaller elements in support\n", #smaller_elems;

    eys := fy_s;

    for w in smaller_elems do
        vprintf IdemCalcOpt, 3: "Processing correction term for w = %o\n", w;

        // Recursively get optimized idempotent for w
        opt_ew := build_optimized_idempotent_internal(IC, w);

        // Find reduced light leave from (y,s) to w with degree 0
        ll_down_red, ll_up_red := find_reduced_light_leave(IC, opt_ey, y, s,opt_ew, w, 0);

        if not IsZero(ll_down_red) then
            vprintf IdemCalcOpt, 3: "Found non-zero light leave for w = %o\n", w;

            // Compute correction term using REDUCED forms
            dys_w := opt_ew`reduced_matrix * ll_down_red * fy_s;
            uys_w := fy_s * ll_up_red * opt_ew`reduced_matrix;

            byw := dys_w * uys_w;
            kw_ys := byw`mat[1,1] / opt_ew`reduced_matrix`mat[1,1];

            correction := (1/kw_ys) * (uys_w * dys_w);
            eys := eys - correction;
        else
            vprintf IdemCalcOpt, 3: "No non-zero light leave for w = %o\n", w;
        end if;
    end for;

    // DECOMPOSE into new smaller idempotent
    vprintf IdemCalcOpt, 2: "Decomposing idempotent for %o\n", x;
    proj, incl := DecomposeIdem(eys);
    //This is always the identity matrix. Still good to keep around
    eys_reduced := proj * eys * incl;

    // Cache the decomposition as degree-0 light leaves from (y,s) to x
    // proj: (reduced_y ⊗ B_s) → reduced_x  (down)
    // incl: reduced_x → (reduced_y ⊗ B_s)  (up)
    ll_cache_key := <Eltseq(y), Eltseq(s), Eltseq(x), 0>;
    IC`LightLeaveCache[ll_cache_key] := <proj, incl>;

    // Create optimized idempotent
    opt_ex := New(OptIdempotent);
    opt_ex`element := x;
    opt_ex`reduced_matrix := eys_reduced;
    opt_ex`prefix_incl := AssociativeArray();
    opt_ex`prefix_proj := AssociativeArray();
    opt_ex`prefix_word := opt_ey`prefix_word cat [seq_x[len]];
    opt_ex`suffix_incl := AssociativeArray();
    opt_ex`suffix_proj := AssociativeArray();

    // Set prefix_incl[len]: This is the inclusion and projection we just created
    // The reflection used is seq_x[len] (the last letter of x = y · s)
    opt_ex`prefix_incl[len] := incl;
    opt_ex`prefix_proj[len] := proj;

    opt_ex`min_prefix_computed := len;

    // ========================================================================
    // SUFFIX CONSTRUCTION FROM LEFT: x = t · z
    // ========================================================================
    vprintf IdemCalcOpt, 1: "Computing suffix idempotent from left for %o\n", x;

    // Split: x = t · z where t = seq_x[1], z = seq_x[2..len]
    t := W![seq_x[1]];
    z := W!seq_x[2..len];

    // Get optimized idempotent for suffix
    opt_ez := build_optimized_idempotent_internal(IC, z);
    proj_z, incl_z := GetPrefixInclProj(IC, opt_ez, len-1);
    proj_ey, incl_ey := GetSuffixInclProj(IC, opt_ey, 1);


    // Set suffix_incl[1]:
    // The reflection used is seq_x[1] (the first letter, t)
    opt_ex`suffix_incl[1] := Tensor(act, [Id(W), t], proj_z) * Tensor(act, incl_ey, [Id(W), s]) * incl;
    opt_ex`suffix_proj[1] := proj * Tensor(act, proj_ey, [Id(W), s]) * Tensor(act, [Id(W), t], incl_z);
    opt_ex`suffix_word := [seq_x[1]] cat opt_ez`suffix_word;

    opt_ex`max_suffix_computed := 1;

    // Cache and return
    IC`IdempotentCache[key] := opt_ex;
    vprintf IdemCalcOpt, 1: "Finished computing optimized idempotent of %o\n", x;
    PopRecursion(IC);
    return opt_ex;
end function;


//============================================================================
// Prefix/Suffix Inclusion/Projection Retrieval
//============================================================================

intrinsic GetPrefixInclProj(IC::OptIdemCollection, opt::OptIdempotent,
                             k::RngIntElt) -> StdMor, StdMor
{Get or compute prefix inclusion/projection for k-th step.
prefix_incl[k] corresponds to the inclusion where from the k-th letter (word of length n) until n we include.
Returns: proj, incl}

    n := #Eltseq(opt`element);
    require k le n: "k cannot exceed word length";
    require k ge 1: "k must be at least 1";

    // Check if already computed
    if IsDefined(opt`prefix_incl, k) then
        return opt`prefix_proj[k], opt`prefix_incl[k];
    end if;

    act := IC`act;
    W := IC`W;

    // Need to compute it
    // k = n should have been set during construction
    if k eq n then
        error "prefix_incl[n] should have been set during construction";
    end if;

    // Build from previous: prefix_incl[k-1] = prefix_incl[k] of smaller word tensored with next letter
    prev_word := Eltseq(opt`element)[1..n-1];
    opt_prev := build_optimized_idempotent_internal(IC, W!prev_word);
    proj_prev, incl_prev := GetPrefixInclProj(IC, opt_prev, k);
    proj_now, incl_now := GetPrefixInclProj(IC, opt, n);
    s := W ! [Eltseq(opt`element)[n]];

    incl_k := Tensor(act, incl_prev, [Id(W), s]) * incl_now;
    proj_k := proj_now * Tensor(act, proj_prev, [Id(W), s]);

    // Cache
    opt`prefix_incl[k] := incl_k;
    opt`prefix_proj[k] := proj_k;
    opt`min_prefix_computed := Minimum(opt`min_prefix_computed, k);

    return proj_k, incl_k;
end intrinsic;


intrinsic GetSuffixInclProj(IC::OptIdemCollection, opt::OptIdempotent,
                             k::RngIntElt) -> StdMor, StdMor
{Get or compute suffix inclusion/projection for k-th step (from left).
suffix_incl[k] corresponds to adding the k-th letter from the left.
Returns: proj, incl}

    n := #Eltseq(opt`element);
    require k le n: "k cannot exceed word length";
    require k ge 1: "k must be at least 1";

    // Check if already computed
    if IsDefined(opt`suffix_incl, k) then
        return opt`suffix_proj[k], opt`suffix_incl[k];
    end if;

    act := IC`act;
    W := IC`W;

    // k = 1 should have been set during construction
    if k eq 1 then
        error "suffix_incl[1] should have been set during construction";
    end if;

    // Build from previous: We need to get suffix_incl[k-1] from a shorter word
    // For x = word[1..n], split as: t · z where t = word[1], z = word[2..n]
    // suffix_incl[k] = t ⊗ suffix_incl[k-1] of z

    // Get the word z = word[2..n]
    word_seq := Eltseq(opt`element);
    z_seq := word_seq[2..n];
    z := W ! z_seq;

    // Get optimized idempotent for z
    opt_z := build_optimized_idempotent_internal(IC, z);

    // Get suffix_incl[k-1] from z (which has length k-1)
    proj_z, incl_z := GetSuffixInclProj(IC, opt_z, k-1);

    //And current incl/proj
    proj_now, incl_now := GetSuffixInclProj(IC, opt, 1);

    // Tensor with t from left
    t := W ! [word_seq[1]];
    incl_k := Tensor(act, [Id(W), t], incl_z) * incl_now;
    proj_k := proj_now * Tensor(act, [Id(W), t], proj_z);

    // Cache
    opt`suffix_incl[k] := incl_k;
    opt`suffix_proj[k] := proj_k;
    opt`max_suffix_computed := Maximum(opt`max_suffix_computed, k);

    return proj_k, incl_k;
end intrinsic;

intrinsic GetPrefixWord(opt::OptIdempotent) -> SeqEnum[RngIntElt]
{Get the prefix word: the reduced word describing how the idempotent was built from the right.
 For x built as (...((e · s_1) · s_2) ... · s_n), prefix_word = [s_1, ..., s_n].}
    return opt`prefix_word;
end intrinsic;

intrinsic GetSuffixWord(opt::OptIdempotent) -> SeqEnum[RngIntElt]
{Get the suffix word: the reduced word describing how the idempotent was built from the left.
 For x built as (t_1 · (t_2 · (... · e))), suffix_word = [t_1, t_2, ...].}
    return opt`suffix_word;
end intrinsic;

intrinsic BuildOptIdempotent(IC::OptIdemCollection, x::GrpFPCoxElt) -> OptIdempotent
{Build the optimized idempotent for element x, using and updating the cache}
    result := build_optimized_idempotent_internal(IC, x);
    // Print summary if progress was enabled
    if IC`ShowProgress and IC`TotalLightLeafTime gt 0 then
        printf "Done. Total light leaf time: %.2os\n", IC`TotalLightLeafTime;
    end if;
    return result;
end intrinsic;

//============================================================================
// Find and cache reduced light leaves
//============================================================================

function find_reduced_light_leave(IC, opt_ex, x, s, opt_ey, y, degree)
    cache_key := <Eltseq(x), Eltseq(s), Eltseq(y), degree>;

    // Check cache
    if IsDefined(IC`LightLeaveCache, cache_key) then
        vprintf IdemCalcOpt, 3: "Using cached reduced light leave for (%o,%o) -> %o\n", x, s, y;
        cached := IC`LightLeaveCache[cache_key];
        return cached[1], cached[2];
    end if;

    B := IC`B;
    W := IC`W;
    act := IC`act;

    vprintf IdemCalcOpt, 3: "Computing reduced light leave for (%o,%o) -> %o with degree %o\n", x, s, y, degree;

    // Start timing for light leaves
    t_start := Cputime();

    // Find all candidate subexpressions
    candidates := find_all_light_leaves_expressions(W, x, s, y : degree := degree);

    if #candidates eq 0 then
        vprintf IdemCalcOpt, 3: "No candidate light leaves found\n";
        IC`LightLeaveCache[cache_key] := <0, 0>;
        SetLightLeafTime(IC, Cputime(t_start));
        return 0, 0;
    end if;

    x_seq := Eltseq(x);
    s_seq := Eltseq(s);
    full_seq := x_seq cat s_seq;
    y_seq := Eltseq(y);

    if IC`UseOptLL then
        // ============================================================
        // Optimized path: use LLOptDownTo/LLOptUpTo (small matrices)
        // ============================================================

        // Create temporary OptIdempotent for x*s (the source element).
        // At the last step of LLOptDownTo, BuildOptIdempotent(IC, wd*W.si) = x*s.
        // We must have it in the cache to avoid infinite recursion.
        xs := x * s;
        xs_key := Eltseq(xs);
        n_xs := #xs_key;
        s_int := s_seq[1];

        temp_opt := New(OptIdempotent);
        temp_opt`element := xs;
        ey_bs := Tensor(act, opt_ex`reduced_matrix, BSId(B, s_int)`stdmor);
        temp_opt`reduced_matrix := ey_bs;
        temp_opt`prefix_incl := AssociativeArray();
        temp_opt`prefix_proj := AssociativeArray();
        temp_opt`prefix_word := opt_ex`prefix_word cat [s_int];
        temp_opt`suffix_incl := AssociativeArray();
        temp_opt`suffix_proj := AssociativeArray();
        temp_opt`suffix_word := [];
        // prefix decomposition at position n: x*s = x · s
        // incl/proj are identity on reduced_x ⊗ B_s (no decomposition yet)
        temp_opt`prefix_incl[n_xs] := ey_bs;
        temp_opt`prefix_proj[n_xs] := ey_bs;
        temp_opt`min_prefix_computed := n_xs;
        temp_opt`max_suffix_computed := 0;

        // Temporarily cache the partial idempotent
        IC`IdempotentCache[xs_key] := temp_opt;

        for cand in candidates do
            subexp := cand[1];

            PrintLLCheck(IC, full_seq, subexp, y_seq);
            vprintf IdemCalcOpt, 3: "Testing subexpression %o (OptLL)\n", subexp;

            ll_down_red := LLOptDownTo(IC, temp_opt, opt_ey, subexp);
            ll_up_red := LLOptUpTo(IC, temp_opt, opt_ey, subexp);

            ClearLLLine(IC);

            if not IsZero(ll_down_red) then
                vprintf IdemCalcOpt, 3: "Found non-zero reduced light leave (OptLL)\n";
                // Remove temporary cache entry before returning
                Remove(~IC`IdempotentCache, xs_key);
                IC`LightLeaveCache[cache_key] := <ll_down_red, ll_up_red>;
                SetLightLeafTime(IC, Cputime(t_start));
                return ll_down_red, ll_up_red;
            end if;
        end for;

        // Remove temporary cache entry
        Remove(~IC`IdempotentCache, xs_key);
    else
        // ============================================================
        // Standard path: use LLDownTo/LLUpFrom (full-size matrices)
        // ============================================================

        for cand in candidates do
            subexp := cand[1];

            // Show which LL we're checking
            PrintLLCheck(IC, full_seq, subexp, y_seq);

            vprintf IdemCalcOpt, 3: "Testing subexpression %o\n", subexp;

            // Build full-size light leaves
            ll_down_full := LLDownTo(B, full_seq, subexp, y_seq)`stdmor;
            ll_up_full := LLUpFrom(B, full_seq, subexp, y_seq)`stdmor;

            // Reduce: compose with prefix inclusions/projections
            yproj, yincl := GetPrefixInclProj(IC, opt_ey, 1);
            ll_down_full_y := yproj * ll_down_full;
            ll_up_full_y := ll_up_full * yincl;

            xproj, xincl := GetPrefixInclProj(IC, opt_ex, 1);
            ll_down_full_xs_y := ll_down_full_y * Tensor(act, xincl, [Id(W), s]);
            ll_up_full_y_xs := Tensor(act, xproj, [Id(W), s]) * ll_up_full_y;

            // Clear LL line after checking
            ClearLLLine(IC);

            if not IsZero(ll_down_full_xs_y) then
                vprintf IdemCalcOpt, 3: "Found non-zero reduced light leave\n";
                IC`LightLeaveCache[cache_key] := <ll_down_full_xs_y, ll_up_full_y_xs>;
                SetLightLeafTime(IC, Cputime(t_start));
                return ll_down_full_xs_y, ll_up_full_y_xs;
            end if;
        end for;
    end if;

    vprintf IdemCalcOpt, 3: "No non-zero reduced light leaves found\n";
    IC`LightLeaveCache[cache_key] := <0, 0>;
    SetLightLeafTime(IC, Cputime(t_start));
    return 0, 0;
end function;

function find_reduced_light_leave_left(IC, t, opt_ez, z, opt_ey, y, degree)
    cache_key := <Eltseq(t), Eltseq(z), Eltseq(y), degree>;

    // Check cache
    if IsDefined(IC`LightLeaveCache, cache_key) then
        vprintf IdemCalcOpt, 3: "Using cached reduced light leave (left) for (%o,%o) -> %o\n", t, z, y;
        cached := IC`LightLeaveCache[cache_key];
        return cached[1], cached[2];
    end if;

    B := IC`B;
    W := IC`W;
    act := IC`act;

    vprintf IdemCalcOpt, 3: "Computing reduced light leave (left) for (%o,%o) -> %o with degree %o\n", t, z, y, degree;

    // Start timing for light leaves
    t_start := Cputime();

    // Find all candidate subexpressions
    candidates := find_all_light_leaves_expressions(W, t, z, y : degree := degree);

    if #candidates eq 0 then
        vprintf IdemCalcOpt, 3: "No candidate light leaves found (left)\n";
        IC`LightLeaveCache[cache_key] := <0, 0>;
        SetLightLeafTime(IC, Cputime(t_start));
        return 0, 0;
    end if;

    t_seq := Eltseq(t);
    z_seq := Eltseq(z);
    full_seq := t_seq cat z_seq;
    y_seq := Eltseq(y);

    for cand in candidates do
        subexp := cand[1];

        // Show which LL we're checking
        PrintLLCheck(IC, full_seq, subexp, y_seq);

        vprintf IdemCalcOpt, 3: "Testing subexpression %o\n", subexp;

        // Build full-size light leaves
        ll_down_full := LLDownTo(B, full_seq, subexp, y_seq)`stdmor;
        ll_up_full := LLUpFrom(B, full_seq, subexp, y_seq)`stdmor;

        // Get inclusions/projections from suffix
        yproj, yincl := GetSuffixInclProj(IC, opt_ey, #y_seq);
        ll_down_full_y := yproj * ll_down_full;
        ll_up_full_y := ll_up_full * yincl;

        zproj, zincl := GetSuffixInclProj(IC, opt_ez, #z_seq);
        ll_down_full_tz_y := ll_down_full_y * Tensor(act, [Id(W), t], zincl);
        ll_up_full_y_tz := Tensor(act, [Id(W), t], zproj) * ll_up_full_y;

        // Clear LL line after checking
        ClearLLLine(IC);

        if not IsZero(ll_down_full_tz_y) then
            vprintf IdemCalcOpt, 3: "Found non-zero reduced light leave (left)\n";
            IC`LightLeaveCache[cache_key] := <ll_down_full_tz_y, ll_up_full_y_tz>;
            SetLightLeafTime(IC, Cputime(t_start));
            return ll_down_full_tz_y, ll_up_full_y_tz;
        end if;
    end for;

    vprintf IdemCalcOpt, 3: "No non-zero reduced light leaves found (left)\n";
    IC`LightLeaveCache[cache_key] := <0, 0>;
    SetLightLeafTime(IC, Cputime(t_start));
    return 0, 0;
end function;

//============================================================================
// Optimized Light Leaves
//============================================================================

// Braid helpers (package-internal)

function local_braid_up(B, W, word, s)
    braided, moves := BraidToEndWith(W, word, s);
    braid := BSId(B, word);
    for move in moves do
        braid := BraidUp(B, braid`bscod, move[1], move[2]) * braid;
    end for;
    return braid, braided;
end function;

function local_braid_down(B, W, word, s)
    braided, moves := BraidToEndWith(W, word, s);
    braid := BSId(B, word);
    for move in moves do
        braid := braid * BraidDown(B, braid`bsdom, move[1], move[2]);
    end for;
    return braid, braided;
end function;

// braid_on_opt_idempotent
//   map:     factor_x -> factor_prefix ⊗ BS(z)
//   map_inv: factor_prefix ⊗ BS(z) -> factor_x

function braid_on_opt_idempotent(IC, opt_ex, s)
    B := IC`B;
    W := IC`W;
    act := IC`act;
    x_word := Eltseq(opt_ex`element);
    n := #x_word;

    k := 0;
    for i := 1 to n do
        suffix_elt := W ! x_word[n-i+1..n];
        if Length(suffix_elt * W.s) lt Length(suffix_elt) then
            k := i;
            break;
        end if;
    end for;

    split := n - k + 1;
    suffix := x_word[split..n];

    braid_top, z := local_braid_up(B, W, suffix, s);
    braid_bot, _ := local_braid_down(B, W, suffix, s);

    ey := BuildOptIdempotent(IC, W ! x_word[1..split-1]);

    proj_split, incl_split := GetPrefixInclProj(IC, opt_ex, split);

    braid_up_t := Tensor(act, ey`reduced_matrix, braid_top`stdmor);
    braid_down_t := Tensor(act, ey`reduced_matrix, braid_bot`stdmor);

    map := braid_up_t * incl_split;
    map_inv := proj_split * braid_down_t;

    return ey, z, map, map_inv;
end function;

// braid_on_opt_idempotent_down (flipped)
//   map:     factor_prefix ⊗ BS(z) -> factor_x
//   map_inv: factor_x -> factor_prefix ⊗ BS(z)

function braid_on_opt_idempotent_down(IC, opt_ex, s)
    B := IC`B;
    W := IC`W;
    act := IC`act;
    x_word := Eltseq(opt_ex`element);
    n := #x_word;

    k := 0;
    for i := 1 to n do
        suffix_elt := W ! x_word[n-i+1..n];
        if Length(suffix_elt * W.s) lt Length(suffix_elt) then
            k := i;
            break;
        end if;
    end for;

    split := n - k + 1;
    suffix := x_word[split..n];

    braid_bot, z := local_braid_down(B, W, suffix, s);
    braid_top, _ := local_braid_up(B, W, suffix, s);

    ey := BuildOptIdempotent(IC, W ! x_word[1..split-1]);
    //We need to now how ex was build. otherwise we might have wrong endings.
    proj_split, incl_split := GetPrefixInclProj(IC, opt_ex, split);

    braid_down_t := Tensor(act, ey`reduced_matrix, braid_bot`stdmor);
    braid_up_t := Tensor(act, ey`reduced_matrix, braid_top`stdmor);

    map := proj_split * braid_down_t;
    map_inv := braid_up_t * incl_split;

    return ey, z, map, map_inv;
end function;

// stitch_opt_idempotents
// Stitch two factorizations of the same element x:
//   x = y · y_suffix  and  x = z · z_suffix
// Returns: stitch_down, stitch_up where
//   stitch_down: factor_ey ⊗ BS(y_suffix) → reduced_x
//   stitch_up:   reduced_x → factor_ez ⊗ BS(z_suffix)

function stitch_opt_idempotents(IC, opt_ey, y_suffix, opt_ez, z_suffix)
    B := IC`B;
    W := IC`W;
    act := IC`act;

    y := opt_ey`element;
    z := opt_ez`element;

    // Compute x from both paths and verify agreement
    xy := #y_suffix eq 0 select y else y * (W ! y_suffix);
    xz := #z_suffix eq 0 select z else z * (W ! z_suffix);

    assert xy eq xz;
    x := xy;
    x_seq := Eltseq(x);
    n := #x_seq;

    opt_ex := build_optimized_idempotent_internal(IC, x);
    sx := x_seq[n]; // last generator in reduced expression of x

    // ================================================================
    // Base case: both suffixes empty → y = z = x
    // ================================================================
    if #y_suffix eq 0 and #z_suffix eq 0 then
        id_x := opt_ex`reduced_matrix;
        return id_x, id_x;
    end if;

    // ================================================================
    // Case 1: Both suffixes end in sx
    // Peel off the common last letter and recurse.
    // ================================================================
    if #y_suffix gt 0 and #z_suffix gt 0 and
       y_suffix[#y_suffix] eq sx and z_suffix[#z_suffix] eq sx then

        vprintf IdemCalcOpt, 3: "Stitch case 1: both suffixes end in %o\n", sx;

        down_rec, up_rec := stitch_opt_idempotents(IC,
            opt_ey, y_suffix[1..#y_suffix-1],
            opt_ez, z_suffix[1..#z_suffix-1]);

        px, ix := GetPrefixInclProj(IC, opt_ex, n);

        stitch_down := px * Tensor(act, down_rec, BSId(B, sx)`stdmor);
        stitch_up := Tensor(act, up_rec, BSId(B, sx)`stdmor) * ix;

        return stitch_down, stitch_up;
    end if;

    // ================================================================
    // Case 2: Braid both suffixes to end in sx, then recurse
    // ================================================================
    y_can_braid := false;
    z_can_braid := false;

    if #y_suffix gt 0 then
        y_suf_elt := W ! y_suffix;
        y_can_braid := Length(y_suf_elt * W.sx) lt Length(y_suf_elt);
    end if;

    if #z_suffix gt 0 then
        z_suf_elt := W ! z_suffix;
        z_can_braid := Length(z_suf_elt * W.sx) lt Length(z_suf_elt);
    end if;

    if y_can_braid and z_can_braid then
        vprintf IdemCalcOpt, 3: "Stitch case 2: braiding both suffixes to end in %o\n", sx;

        braid_y_up, y_braided := local_braid_up(B, W, y_suffix, sx);
        braid_y_down, _ := local_braid_down(B, W, y_suffix, sx);

        braid_z_up, z_braided := local_braid_up(B, W, z_suffix, sx);
        braid_z_down, _ := local_braid_down(B, W, z_suffix, sx);

        // Both braided suffixes now end in sx → recursive call hits Case 1
        down_braided, up_braided := stitch_opt_idempotents(IC,
            opt_ey, y_braided,
            opt_ez, z_braided);

        // Compose with braid maps
        // down: factor_ey ⊗ BS(y_suffix) --braid_y--> factor_ey ⊗ BS(y_braided) --down--> reduced_x
        stitch_down := down_braided * Tensor(act, opt_ey`reduced_matrix, braid_y_up`stdmor);
        // up: reduced_x --up--> factor_ez ⊗ BS(z_braided) --braid_z_back--> factor_ez ⊗ BS(z_suffix)
        stitch_up := Tensor(act, opt_ez`reduced_matrix, braid_z_down`stdmor) * up_braided;

        return stitch_down, stitch_up;
    end if;

    // ================================================================
    // Case 3: One suffix is empty (the other is non-empty but can't braid)
    // Use braid_on_opt_idempotent_down to decompose opt_ex at the
    // last letter of the non-empty suffix, then recurse.
    // ================================================================

    if #y_suffix eq 0 then
        // y = x, stitch_down = identity, need stitch_up: reduced_x → factor_ez ⊗ BS(z_suffix)
        vprintf IdemCalcOpt, 3: "Stitch case 3a: y_suffix empty, decomposing at z_suffix end\n";

        last_ref := z_suffix[#z_suffix];
        ey_split, z_split, map_down, map_up := braid_on_opt_idempotent_down(IC, opt_ex, last_ref);
        // map_down: ey_split ⊗ BS(z_split) → reduced_x (z_split ends in last_ref)
        // map_up:   reduced_x → ey_split ⊗ BS(z_split)

        stitch_down := opt_ex`reduced_matrix; // identity on reduced_x

        if ey_split`element eq z and z_split eq z_suffix then
            // Direct match — no further stitching needed
            return stitch_down, map_up;
        end if;

        // Recurse: stitch the prefix parts (with last_ref peeled off)
        z_split_shorter := z_split[1..#z_split-1];
        z_suffix_shorter := z_suffix[1..#z_suffix-1];
        inner_down, inner_up := stitch_opt_idempotents(IC,
            ey_split, z_split_shorter,
            opt_ez, z_suffix_shorter);
        // inner_down: ey_split ⊗ BS(z_split') → reduced_wd
        // inner_up:   reduced_wd → ez ⊗ BS(z_suffix')

        // Compose: reduced_x → ey_split ⊗ BS(z_split) → reduced_wd ⊗ B_ref → ez ⊗ BS(z_suffix)
        stitch_up := Tensor(act, inner_up, BSId(B, last_ref)`stdmor)
                   * Tensor(act, inner_down, BSId(B, last_ref)`stdmor)
                   * map_up;

        return stitch_down, stitch_up;
    end if;

    if #z_suffix eq 0 then
        // z = x, stitch_up = identity, need stitch_down: factor_ey ⊗ BS(y_suffix) → reduced_x
        vprintf IdemCalcOpt, 3: "Stitch case 3b: z_suffix empty, decomposing at y_suffix end\n";

        last_ref := y_suffix[#y_suffix];
        ey_split, z_split, map_down, map_up := braid_on_opt_idempotent_down(IC, opt_ex, last_ref);
        // map_down: ey_split ⊗ BS(z_split) → reduced_x (z_split ends in last_ref)
        // map_up:   reduced_x → ey_split ⊗ BS(z_split)

        stitch_up := opt_ex`reduced_matrix; // identity on reduced_x

        if ey_split`element eq y and z_split eq y_suffix then
            // Direct match
            return map_down, stitch_up;
        end if;

        // Recurse: stitch the prefix parts (with last_ref peeled off)
        z_split_shorter := z_split[1..#z_split-1];
        y_suffix_shorter := y_suffix[1..#y_suffix-1];
        inner_down, inner_up := stitch_opt_idempotents(IC,
            opt_ey, y_suffix_shorter,
            ey_split, z_split_shorter);
        // inner_down: ey ⊗ BS(y_suffix') → reduced_wd
        // inner_up:   reduced_wd → ey_split ⊗ BS(z_split')

        // Compose: ey ⊗ BS(y_suffix) → reduced_wd ⊗ B_ref → ey_split ⊗ BS(z_split) → reduced_x
        stitch_down := map_down
                     * Tensor(act, inner_up, BSId(B, last_ref)`stdmor)
                     * Tensor(act, inner_down, BSId(B, last_ref)`stdmor);

        return stitch_down, stitch_up;
    end if;

    // ================================================================
    // General case: both suffixes non-empty but neither can braid to sx.
    // Peel the last letter off y (or z) into its suffix and recurse.
    // This shortens the prefix and lengthens the suffix until we hit
    // a case above (braid, common ending, or one side empty).
    // ================================================================

    y_seq := Eltseq(y);
    z_seq := Eltseq(z);
    n_y := #y_seq;
    n_z := #z_seq;

    // Peel from the longer prefix (arbitrary tie-break: prefer y)
    if n_y ge n_z then
        vprintf IdemCalcOpt, 3: "Stitch general: peeling last letter of y=%o into y_suffix\n", y;
        ref_y := y_seq[n_y];
        py, iy := GetPrefixInclProj(IC, opt_ey, n_y);
        opt_ey_short := build_optimized_idempotent_internal(IC, W ! y_seq[1..n_y-1]);
        y_suffix_ext := [ref_y] cat y_suffix;

        // down_rec: factor_{ey_short} ⊗ BS(y_suffix_ext) → reduced_x
        // up_rec:   reduced_x → factor_{ez} ⊗ BS(z_suffix)
        down_rec, up_rec := stitch_opt_idempotents(IC,
            opt_ey_short, y_suffix_ext,
            opt_ez, z_suffix);

        // iy: reduced_y → reduced_{ey_short} ⊗ B_{ref_y}
        // So iy ⊗ Id(BS(y_suffix)) maps factor_ey ⊗ BS(y_suffix) → factor_{ey_short} ⊗ B_{ref_y} ⊗ BS(y_suffix)
        bs_ysuf := #y_suffix eq 0 select BSId(B, [])`stdmor else BSId(B, y_suffix)`stdmor;
        stitch_down := down_rec * Tensor(act, iy, bs_ysuf);
        // up_rec already maps to factor_ez ⊗ BS(z_suffix), no wrapping needed
        stitch_up := up_rec;

        return stitch_down, stitch_up;
    else
        vprintf IdemCalcOpt, 3: "Stitch general: peeling last letter of z=%o into z_suffix\n", z;
        ref_z := z_seq[n_z];
        pz, iz := GetPrefixInclProj(IC, opt_ez, n_z);
        opt_ez_short := build_optimized_idempotent_internal(IC, W ! z_seq[1..n_z-1]);
        z_suffix_ext := [ref_z] cat z_suffix;

        // down_rec: factor_{ey} ⊗ BS(y_suffix) → reduced_x
        // up_rec:   reduced_x → factor_{ez_short} ⊗ BS(z_suffix_ext)
        down_rec, up_rec := stitch_opt_idempotents(IC,
            opt_ey, y_suffix,
            opt_ez_short, z_suffix_ext);

        // iz: reduced_z → reduced_{ez_short} ⊗ B_{ref_z}
        // pz: reduced_{ez_short} ⊗ B_{ref_z} → reduced_z
        // So pz ⊗ Id(BS(z_suffix)) maps factor_{ez_short} ⊗ B_{ref_z} ⊗ BS(z_suffix) → factor_ez ⊗ BS(z_suffix)
        bs_zsuf := #z_suffix eq 0 select BSId(B, [])`stdmor else BSId(B, z_suffix)`stdmor;
        // down_rec already maps from factor_ey ⊗ BS(y_suffix), no wrapping needed
        stitch_down := down_rec;
        stitch_up := Tensor(act, pz, bs_zsuf) * up_rec;

        return stitch_down, stitch_up;
    end if;
end function;

// Helper: get inclusion that decomposes at a specific reflection si
// Returns incl: reduced_x → reduced_{x·si} ⊗ B_si
// (si must be a right descent of x)
function get_incl_at_si(IC, opt_x, si)
    n := #Eltseq(opt_x`element);
    pw := opt_x`prefix_word;
    if pw[n] eq si then
        _, ix := GetPrefixInclProj(IC, opt_x, n);
        return ix;
    end if;
    W := IC`W;
    opt_y := BuildOptIdempotent(IC, opt_x`element * W.si);
    _, incl := stitch_opt_idempotents(IC, opt_x, [], opt_y, [si]);
    return incl;
end function;

// Helper: get projection that decomposes at a specific reflection si
// Returns proj: reduced_{x·si} ⊗ B_si → reduced_x
// (si must be a right descent of x)
function get_proj_at_si(IC, opt_x, si)
    n := #Eltseq(opt_x`element);
    pw := opt_x`prefix_word;
    if pw[n] eq si then
        px, _ := GetPrefixInclProj(IC, opt_x, n);
        return px;
    end if;
    W := IC`W;
    opt_y := BuildOptIdempotent(IC, opt_x`element * W.si);
    proj, _ := stitch_opt_idempotents(IC, opt_y, [si], opt_x, []);
    return proj;
end function;

intrinsic GetInclAtSi(IC::OptIdemCollection, opt_x::OptIdempotent, si::RngIntElt) -> StdMor
{Get inclusion that decomposes at reflection si, a right descent of x}
    return get_incl_at_si(IC, opt_x, si);
end intrinsic;

intrinsic GetProjAtSi(IC::OptIdemCollection, opt_x::OptIdempotent, si::RngIntElt) -> StdMor
{Get projection that decomposes at reflection si, a right descent of x}
    return get_proj_at_si(IC, opt_x, si);
end intrinsic;

//============================================================================
// LLOptDownTo / LLOptUpTo intrinsics
//============================================================================

intrinsic LLOptDownTo(IC::OptIdemCollection, opt_ex::OptIdempotent, opt_ey::OptIdempotent, expr::SeqEnum[RngIntElt]) -> Any
{Optimized light leaf going down, from BS(opt_ex) to BS(opt_ey) with subexpression expr.
 Returns a StdMor in reduced form.}
    B := IC`B;
    W := IC`W;
    act := IC`act;

    bsword := GetPrefixWord(opt_ex);
    subexp := expr;

    vprintf IdemCalcOpt, 1: "LLOptDownTo: x=%o, y=%o, expr=%o\n", opt_ex`element, opt_ey`element, expr;

    wd := Id(W);
    wu := Id(W);
    leaf := BSId(B, [])`stdmor;

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];

        vprintf IdemCalcOpt, 2: "  Step %o: si=%o, ei=%o, wu=%o, wd=%o\n", i, si, ei, wu, wd;

        opt_wu := BuildOptIdempotent(IC, wu);
        opt_wdsi := BuildOptIdempotent(IC, wd * W.si);

        if Length(wu * W.si) gt Length(wu) then
            if ei eq 0 then
                vprintf IdemCalcOpt, 2: "    Case U0 (ascent, ei=0): counit at si=%o\n", si;
                id := get_incl_at_si(IC, opt_wdsi, si);
                leaf := Tensor(act, leaf, Counit(B, si)`stdmor) * id;
                wd := wd * W.si;
            else
                vprintf IdemCalcOpt, 2: "    Case U1 (ascent, ei=1): tensor with si=%o\n", si;
                opt_wusi := BuildOptIdempotent(IC, wu * W.si);
                id := get_incl_at_si(IC, opt_wdsi, si);
                pu := get_proj_at_si(IC, opt_wusi, si);
                leaf := pu * Tensor(act, leaf, BSId(B, si)`stdmor) * id;
                wu := wu * W.si;
                wd := wd * W.si;
            end if;
        else
            wu_seq := Eltseq(wu);

            if wu_seq[#wu_seq] eq si then
                vprintf IdemCalcOpt, 2: "    Case D (descent, last letter matches si=%o)\n", si;
                id := get_incl_at_si(IC, opt_wdsi, si);
                pu, iu := GetPrefixInclProj(IC, opt_wu, #wu_seq);
                opt_y := BuildOptIdempotent(IC, W ! wu_seq[1..#wu_seq-1]);

                if ei eq 0 then
                    vprintf IdemCalcOpt, 2: "      D0: mult at si=%o\n", si;
                    leaf := pu * Tensor(act, opt_y`reduced_matrix, Mult(B, si)`stdmor) * Tensor(act, iu * leaf, BSId(B, si)`stdmor) * id;
                    wd := wd * W.si;
                else
                    vprintf IdemCalcOpt, 2: "      D1: cap at si=%o\n", si;
                    leaf := Tensor(act, opt_y`reduced_matrix, Cap(B, si)`stdmor) * Tensor(act, iu * leaf, BSId(B, si)`stdmor) * id;
                    wu := wu * W.si;
                    wd := wd * W.si;
                end if;
            else
                vprintf IdemCalcOpt, 2: "    Case D-braid (descent, need braid for si=%o, wu=%o)\n", si, wu;
                ey, z, braidmap, braidmapinv := braid_on_opt_idempotent(IC, opt_wu, si);
                vprintf IdemCalcOpt, 3: "      Braid: ey=%o, z=%o\n", ey`element, z;
                id := get_incl_at_si(IC, opt_wdsi, si);
                if ei eq 0 then
                    vprintf IdemCalcOpt, 2: "      D-braid-0: mult at si=%o\n", si;
                    toppart := braidmapinv * Tensor(act, ey`reduced_matrix, Tensor(act, BSId(B, z[1..#z-1])`stdmor, Mult(B, si)`stdmor)) * Tensor(act, braidmap, BSId(B, si)`stdmor);
                    leaf := toppart * Tensor(act, leaf, BSId(B, si)`stdmor) * id;
                    wd := wd * W.si;
                else
                    vprintf IdemCalcOpt, 2: "      D-braid-1: cap at si=%o, stitching\n", si;
                    wusi := wu * W.si;
                    opt_wusi := BuildOptIdempotent(IC, wusi);
                    z_prime := z[1..#z-1];

                    cap_step := Tensor(act, ey`reduced_matrix, Tensor(act, BSId(B, z_prime)`stdmor, Cap(B, si)`stdmor));
                    stitch, _ := stitch_opt_idempotents(IC, ey, z_prime, opt_wusi, []);

                    toppart := stitch * cap_step * Tensor(act, braidmap, BSId(B, si)`stdmor);
                    leaf := toppart * Tensor(act, leaf, BSId(B, si)`stdmor) * id;
                    wu := wusi;
                    wd := wd * W.si;
                end if;
            end if;
        end if;
        vprintf IdemCalcOpt, 3: "    leaf size: %o x %o\n", Nrows(leaf`mat), Ncols(leaf`mat);
    end for;

    vprintf IdemCalcOpt, 1: "LLOptDownTo done: result %o x %o\n", Nrows(leaf`mat), Ncols(leaf`mat);
    return leaf;
end intrinsic;

intrinsic LLOptUpTo(IC::OptIdemCollection, opt_ex::OptIdempotent, opt_ey::OptIdempotent, expr::SeqEnum[RngIntElt]) -> Any
{Optimized light leaf going up, from BS(opt_ey) to BS(opt_ex) with subexpression expr.
 Dual of LLOptDownTo. Returns a StdMor in reduced form.}
    B := IC`B;
    W := IC`W;
    act := IC`act;

    bsword := GetPrefixWord(opt_ex);
    subexp := expr;

    wd := Id(W);
    wu := Id(W);
    leaf := BSId(B, [])`stdmor;

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];

        opt_wu := BuildOptIdempotent(IC, wu);
        opt_wd := BuildOptIdempotent(IC, wd);
        opt_wdsi := BuildOptIdempotent(IC, wd * W.si);

        if Length(wu * W.si) gt Length(wu) then
            if ei eq 0 then
                pd := get_proj_at_si(IC, opt_wdsi, si);
                leaf := pd * Tensor(act, leaf, Unit(B, si)`stdmor);
                wd := wd * W.si;
            else
                opt_wusi := BuildOptIdempotent(IC, wu * W.si);
                pd := get_proj_at_si(IC, opt_wdsi, si);
                iu := get_incl_at_si(IC, opt_wusi, si);
                leaf := pd * Tensor(act, leaf, BSId(B, si)`stdmor) * iu;
                wu := wu * W.si;
                wd := wd * W.si;
            end if;
        else
            wu_seq := Eltseq(wu);
            pd := get_proj_at_si(IC, opt_wdsi, si);

            if wu_seq[#wu_seq] eq si then
                pu, iu := GetPrefixInclProj(IC, opt_wu, #wu_seq);
                opt_y := BuildOptIdempotent(IC, W ! wu_seq[1..#wu_seq-1]);

                if ei eq 0 then
                    leaf := pd * Tensor(act, leaf * pu, BSId(B, si)`stdmor) * Tensor(act, opt_y`reduced_matrix, Comult(B, si)`stdmor) * iu;
                    wd := wd * W.si;
                else
                    leaf := pd * Tensor(act, leaf * pu, BSId(B, si)`stdmor) * Tensor(act, opt_y`reduced_matrix, Cup(B, si)`stdmor);
                    wu := wu * W.si;
                    wd := wd * W.si;
                end if;
            else
                ey, z, braidmap, braidmapinv := braid_on_opt_idempotent(IC, opt_wu, si);
                if ei eq 0 then
                    botpart := Tensor(act, braidmapinv, BSId(B, si)`stdmor) * Tensor(act, ey`reduced_matrix, Tensor(act, BSId(B, z[1..#z-1])`stdmor, Comult(B, si)`stdmor)) * braidmap;
                    leaf := pd * Tensor(act, leaf, BSId(B, si)`stdmor) * botpart;
                    wd := wd * W.si;
                else
                    wusi := wu * W.si;
                    opt_wusi := BuildOptIdempotent(IC, wusi);
                    z_prime := z[1..#z-1];

                    cup_step := Tensor(act, ey`reduced_matrix, Tensor(act, BSId(B, z_prime)`stdmor, Cup(B, si)`stdmor));

                    _, stitch_up := stitch_opt_idempotents(IC, opt_wusi, [], ey, z_prime);
                    botpart := Tensor(act, braidmapinv, BSId(B, si)`stdmor) * cup_step * stitch_up;
                    leaf := pd * Tensor(act, leaf, BSId(B, si)`stdmor) * botpart;
                    wu := wusi;
                    wd := wd * W.si;
                end if;
            end if;
        end if;
    end for;

    return leaf;
end intrinsic;
