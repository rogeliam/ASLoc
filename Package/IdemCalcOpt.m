//============================================================================
// IdemCalcOpt.m - Optimized Idempotent Calculation with Reduced Storage
// We again compute idempotents, as in IdemCalc.m; however we drastically
// reduce the size of the matrix in each step. This gives a considerable speed up
// TODO: Refer to explanation in Paper 2.
//============================================================================

import "StdCat.m": StdMorConstruct;
import "IdemCalcHelpers.m": find_all_light_leaves_expressions,
    find_smaller_elements_in_product;
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
    prefix_incl,            // AssocArray: prefix_incl[k] for k = 1,2,...,n
    prefix_proj,            // AssocArray: prefix_proj[k] for k = 1,2,...,n

    // Suffix inclusions/projections (building from LEFT)
    //Similar idea: suffix_incl[1] maps B_sts into B_s x B_ts
    // suffix_incl[k] = inclusion till k-th letter from left
    // suffix_incl[n] = identity to full length
    suffix_incl,            // AssocArray: suffix_incl[k] for k = 1,2,...,n
    suffix_proj,            // AssocArray: suffix_proj[k] for k = 1,2,...,n

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
    TotalLightLeafTime;     // FldReElt: Total time spent on light leaves

//============================================================================
// Constructor and Basic Operations
//============================================================================

intrinsic CreateOptIdemCollection(B::BSCat, C::., act::UserProgram : ShowProgress := false) -> OptIdemCollection
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

forward build_optimized_idempotent_internal, find_reduced_light_leave, find_reduced_light_leave_left;

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

    // Base case: length 1
    if len eq 1 then
        vprintf IdemCalcOpt, 2: "Base case: optimized idempotent for %o\n", x;
        e := BSId(B, seq_x[1])`stdmor;

        opt := New(OptIdempotent);
        opt`element := x;
        opt`reduced_matrix := e;
        opt`prefix_incl := AssociativeArray();
        opt`prefix_proj := AssociativeArray();
        opt`suffix_incl := AssociativeArray();
        opt`suffix_proj := AssociativeArray();

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
    opt_ex`suffix_incl := AssociativeArray();
    opt_ex`suffix_proj := AssociativeArray();

    // Set prefix_incl[len]: This is the inclusion and projection we just created
    opt_ex`prefix_incl[len] := incl;
    opt_ex`prefix_proj[len] := proj ;

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
    opt_ex`suffix_incl[1] := Tensor(act, [Id(W), t], proj_z) * Tensor(act, incl_ey, [Id(W), s]) * incl;
    opt_ex`suffix_proj[1] := proj * Tensor(act, proj_ey, [Id(W), s]) * Tensor(act, [Id(W), t], incl_z);

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
Returns: incl, proj}

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
Returns: incl, proj}

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
