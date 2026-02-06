//============================================================================
// IdemCalc.m - Idempotent Calculation Package
//
// This package provides tools for computing idempotents in the diagrammatic
// Hecke category using caching and the functionalities from ASLoc.
// This follows the notation from [ERT]: https://arxiv.org/pdf/2507.10061.
// We refer to the equations (TODO: When new version appears check if numbers are the same)
//============================================================================

// Import the standard category morphism constructor
import "StdCat.m": StdMorConstruct;

// Import helper functions for braid morphisms, subexpression enumeration, and KL products
import "IdemCalcHelpers.m": make_braid_up, make_braid_down, make_top_end_with,
    make_bot_end_with, make_top_word, make_bot_word, find_braid_morphism,
    find_braid_morphism_bot, find_all_light_leaves_expressions,
    find_smaller_elements_in_product;

// Verbose output declaration
declare verbose IdemCalc, 3;

//============================================================================
// Type Declaration
//============================================================================

declare type IdemCollection;
declare attributes IdemCollection:
    B,                  // The BSCat
    W,                  // The Coxeter group
    act,                // The action function; needed to form tensor products
    HAlg,               // The Hecke algebra
    CanBasis,           // The canonical basis
    IdempotentCache,    // Cache for idempotents
    LightLeaveCache;    // Cache for light leaves

//============================================================================
// Constructor and Basic Operations
//============================================================================

intrinsic CreateIdemCollection(B::BSCat, C::., act::UserProgram) -> IdemCollection
{Create a new idempotent collection for category B with canonical basis C and action function act}
    IC := New(IdemCollection);
    IC`B := B;
    IC`W := B`W;
    IC`act := act;
    IC`CanBasis := C;
    IC`IdempotentCache := AssociativeArray();
    IC`LightLeaveCache := AssociativeArray();
    return IC;
end intrinsic;

intrinsic Print(IC::IdemCollection)
{Print an idempotent collection}
    printf "Idempotent collection for %o with %o cached idempotents and %o cached light leaves",
        IC`B, #Keys(IC`IdempotentCache), #Keys(IC`LightLeaveCache);
end intrinsic;

intrinsic ClearCache(IC::IdemCollection)
{Clear all caches in the idempotent collection}
    IC`IdempotentCache := AssociativeArray();
    IC`LightLeaveCache := AssociativeArray();
end intrinsic;

intrinsic ClearIdempotentCache(IC::IdemCollection)
{Clear only the idempotent cache}
    IC`IdempotentCache := AssociativeArray();
end intrinsic;

intrinsic ClearLightLeaveCache(IC::IdemCollection)
{Clear only the light leave cache}
    IC`LightLeaveCache := AssociativeArray();
end intrinsic;

intrinsic GetCachedIdempotent(IC::IdemCollection, x::GrpFPCoxElt) -> BSMor
{Get a cached idempotent if it exists, error otherwise}
    key := Eltseq(x);
    require IsDefined(IC`IdempotentCache, key): "Idempotent not in cache for", x;
    return IC`IdempotentCache[key];
end intrinsic;

intrinsic HasCachedIdempotent(IC::IdemCollection, x::GrpFPCoxElt) -> BoolElt
{Check if an idempotent is in the cache}
    return IsDefined(IC`IdempotentCache, Eltseq(x));
end intrinsic;

intrinsic CachedIdempotents(IC::IdemCollection) -> SeqEnum
{Return a sequence of all elements for which idempotents are cached}
    return [IC`W ! key : key in Keys(IC`IdempotentCache)];
end intrinsic;

intrinsic NumberOfCachedIdempotents(IC::IdemCollection) -> RngIntElt
{Return the number of cached idempotents}
    return #Keys(IC`IdempotentCache);
end intrinsic;

intrinsic NumberOfCachedLightLeaves(IC::IdemCollection) -> RngIntElt
{Return the number of cached light leave pairs}
    return #Keys(IC`LightLeaveCache);
end intrinsic;

//============================================================================
// Find non-zero light leave composition
// Given two reduced expressions, x,y; The Morphism space HOM_(BS(x),BS(y))
// contains al light leaves. However, composing with the idempotents corresponding
// to x and y might return zero. Here, we do a brute force check which
// light leaves still live in Hom(B_x,B_y)
//============================================================================

function find_nonzero_light_leave(B, act, idempotent_x, x, s, idempotent_y, y : degree := 0)
    W := B`W;
    results := [];

    candidates := find_all_light_leaves_expressions(W, x, s, y : degree := degree);

    x_seq := Eltseq(x);
    s_seq := Eltseq(s);
    full_seq := x_seq cat s_seq;
    y_seq := Eltseq(y);

    for cand in candidates do
        seq := cand[1];
        deg := cand[2];

        // Use the function that handles braiding internally to match y_seq
        ll_down := LLDownTo(B, full_seq, seq, y_seq)`stdmor;

        // Now compose - domains/codomains are guaranteed to match
        composition := idempotent_y * ll_down * Tensor(act, idempotent_x, [Id(W), s]);

        if not IsZero(composition) then
            Append(~results, <seq, composition>);
        end if;
    end for;

    return results;
end function;

//============================================================================
// Find and cache light leaves. We store light leaves that we need to construct idempotents
// If we need a map again, either it is stored and returned here, or we create a new one
//============================================================================

function find_cached_light_leaves_internal(IC, idempotent_x, x, s, idempotent_y, y, degree)
    cache_key := <Eltseq(x), Eltseq(s), Eltseq(y), degree>;

    // Check cache
    if IsDefined(IC`LightLeaveCache, cache_key) then
        vprintf IdemCalc, 3: "Using cached light leaves for (%o,%o) -> %o\n", x, s, y;
        cached := IC`LightLeaveCache[cache_key];
        return cached[1], cached[2];
    end if;

    B := IC`B;
    W := IC`W;
    act := IC`act;

    vprintf IdemCalc, 3: "Computing light leaves for (%o,%o) -> %o with degree %o\n", x, s, y, degree;

    // Compute using find_nonzero_light_leave
    results := find_nonzero_light_leave(B, act, idempotent_x, x, s, idempotent_y, y : degree := degree);

    if #results eq 0 then
        vprintf IdemCalc, 3: "No non-zero light leaves found\n";
        IC`LightLeaveCache[cache_key] := <0, 0>;
        return 0, 0;
    end if;

    // Found non-zero light leave - take first one
    seq := results[1][1];  // Binary sequence

    // Build full sequence
    x_seq := Eltseq(x);
    s_seq := Eltseq(s);
    full_seq := x_seq cat s_seq;
    y_seq := Eltseq(y);

    // Compute down and up maps with correct target/source
    ll_down := LLDownTo(B, full_seq, seq, y_seq)`stdmor;
    ll_up := LLUpFrom(B, full_seq, seq, y_seq)`stdmor;

    // Cache and return
    IC`LightLeaveCache[cache_key] := <ll_down, ll_up>;
    vprintf IdemCalc, 3: "Cached light leaves\n";
    return ll_down, ll_up;
end function;

//============================================================================
// Build idempotent recursively with caching
//
// For x = [s1, ..., sn] we first build the idempotent for x_prefix := [s1].
// Then, inductively, given the idempotent for x_prefix = [s1, ..., si], we check
// how C_{x_prefix} * C_{s_{i+1}} decomposes in the Kazhdan-Lusztig basis, find
// the appropriate light leaves from B_{x_prefix} tensor B_{s_{i+1}} to the
// summands B_z, and construct the next idempotent.
// This is basically section 4.1 of [ERT25]
//============================================================================

function build_idempotent_internal(IC, x)
    key := Eltseq(x);

    // Check cache first
    if IsDefined(IC`IdempotentCache, key) then
        vprintf IdemCalc, 2: "Using cached idempotent for %o\n", x;
        return IC`IdempotentCache[key];
    end if;

    B := IC`B;
    W := IC`W;
    act := IC`act;

    seq_x := Eltseq(x);
    len := #seq_x;

    // Base case: length 1
    // BS(s) = B_s. So there is nothing to do
    if len eq 1 then
        vprintf IdemCalc, 2: "Base case: idempotent of simple reflection %o\n", x;
        e := BSId(B, seq_x[1])`stdmor;
        IC`IdempotentCache[key] := e;
        return e;
    end if;

    vprintf IdemCalc, 1: "Computing idempotent of %o (length %o)\n", x, len;

    // Recursive case: build idempotent for first len-1 elements
    x_prefix := W!seq_x[1..len-1];
    s := W![seq_x[len]];

    // Get idempotent for prefix (this will use cache or recurse)
    idempotent_prefix := build_idempotent_internal(IC, x_prefix);

    // Compute tensor with s
    vprintf IdemCalc, 2: "Computing tensor product e_prefix tensor id_s for x=%o, s=%o\n", x_prefix, s;
    fx_s := Tensor(act, idempotent_prefix, [Id(W), s]);

    // Find elements y < xs appearing in C_x * C_s
    smaller_elems := find_smaller_elements_in_product(W, IC`CanBasis, x_prefix, s);
    vprintf IdemCalc, 2: "Found %o smaller elements in support\n", #smaller_elems;

    //This is only the first term in Equation (4D.22)
    idempotent_xs := fx_s;

    //Now we loop over all smaller y occuring, also see (4D.22)
    for y in smaller_elems do
        vprintf IdemCalc, 3: "Processing correction term for y = %o\n", y;

        // Recursively get idempotent for y
        idempotent_y := build_idempotent_internal(IC, y);

        // Find non-zero light leave from (x,s) to y with degree 0
        // These are the maps p, i from (4D.3) and (4D.4). Since in this code here we do not have (4A.3)
        ll_down, ll_up := find_cached_light_leaves_internal(IC, idempotent_prefix, x_prefix, s, idempotent_y, y, 0);

        if not IsZero(ll_down) then  // Found non-zero light leave
            vprintf IdemCalc, 3: "Found non-zero light leave for y = %o\n", y;

            // Compute down and up maps with proper braiding
            // This is the left side of the local intersection form, see (4D.8)
            dxs_y := idempotent_y * ll_down * fx_s;
            uxs_y := fx_s * ll_up * idempotent_y;

            // Compute coefficient
            bxy := dxs_y * uxs_y;
            ky_xs := bxy`mat[1,1] / idempotent_y`mat[1,1];

            // Subtract this correction term directly
            // This is (4D.14) from Theorem 4D.12. The idempotent is constructed
            correction_term := (1/ky_xs) * (uxs_y * dxs_y);
            idempotent_xs`mat := idempotent_xs`mat - correction_term`mat;
        else
            vprintf IdemCalc, 3: "No non-zero light leave for y = %o\n", y;
        end if;
    end for;

    // Cache and return
    IC`IdempotentCache[key] := idempotent_xs;
    vprintf IdemCalc, 1: "Finished computing idempotent of %o\n", x;
    return idempotent_xs;
end function;

intrinsic BuildIdempotent(IC::IdemCollection, x::GrpFPCoxElt) -> StdMor
{Build the idempotent for element x, using and updating the cache}
    return build_idempotent_internal(IC, x);
end intrinsic;
