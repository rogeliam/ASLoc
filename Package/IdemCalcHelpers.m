//============================================================================
// IdemCalcHelpers.m - Helper Functions for Idempotent Calculations
//
// This file contains utility functions for braid morphisms and subexpression
// enumeration used by IdemCalc.m
//============================================================================

//============================================================================
// Braid Construction Functions
//============================================================================

//make the top end in s
function make_braid_up(B, W, bsseq, s)
    ending, moves := BraidToEndWith(W, bsseq, s);
    braid := BSId(B, bsseq);
    for move in moves do
        braid := BraidUp(B, braid`bscod, move[1], move[2]) * braid;
    end for;
    return braid;
end function;

//make bottom end with s
function make_braid_down(B, W, bsseq, s)
    ending, moves := BraidToEndWith(W, bsseq, s);
    braid := BSId(B, bsseq);
    for move in moves do
        braid := braid * BraidDown(B, braid`bsdom, move[1], move[2]);
    end for;
    return braid;
end function;

//Apply the fucntions above to a fixed morphism
function make_top_end_with(B, W, mor, s)
    if mor`bscod[#mor`bscod] ne s then
        return make_braid_up(B, W, mor`bscod, s) * mor;
    end if;
    return mor;
end function;

//Apply the fucntions above to a fixed morphism
function make_bot_end_with(B, W, mor, s)
    if mor`bsdom[#mor`bsdom] ne s then
        return mor * make_braid_down(B, W, mor`bsdom, s);
    end if;
    return mor;
end function;

//Now make w end in the word x. I.e. a recursion on the ending in s
function make_top_word(B, W, w, x)
    assert #w eq #x;
    result := BSId(B, w);

    for i in Reverse([1..#x]) do
        f := make_top_end_with(B, W, BSId(B, result`bscod[1..i]), x[i]);
        result := (f cat BSId(B, x[i+1..#x])) * result;
    end for;

    return result;
end function;

//same for the bottom
function make_bot_word(B, W, w, x)
    assert #w eq #x;
    result := BSId(B, w);

    for i in Reverse([1..#x]) do
        f := make_bot_end_with(B, W, BSId(B, result`bsdom[1..i]), x[i]);
        result := result * (f cat BSId(B, x[i+1..#x]));
    end for;

    return result;
end function;

function find_braid_morphism(B, W, x, y)
    if #x ne #y then
        error "Sequences must have the same length";
    end if;

    if W!x ne W!y then
        error "Sequences are not braid equivalent (represent different elements)";
    end if;

    return make_top_word(B, W, x, y);
end function;

function find_braid_morphism_bot(B, W, x, y)
    if #x ne #y then
        error "Sequences must have the same length";
    end if;

    if W!x ne W!y then
        error "Sequences are not braid equivalent (represent different elements)";
    end if;

    return make_bot_word(B, W, x, y);
end function;

//============================================================================
// Kazhdan-Lusztig Product Helpers
//============================================================================

// Given C_x * C_s, find all elements smaller than x*s in the support.
// Returns a sequence of elements y < xs that appear in the KL product.
function find_smaller_elements_in_product(W, C, x, s)
    product := C.Eltseq(x) * C.Eltseq(s);
    xs := x * s;

    smaller_elems := [];
    for term in Support(product) do
        elem := W ! Eltseq(term);
        if elem ne xs then
            Append(~smaller_elems, elem);
        end if;
    end for;

    return smaller_elems;
end function;

//============================================================================
// Standard Light Leaves with Target Matching
//============================================================================
// The light leave from ALSoc doesnt allow for final braid moves in the end, so we build it ourselfs
intrinsic LLDownTo(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt],
                             target_seq::SeqEnum[RngIntElt]) -> BSMor
{Returns the light-leaf from BS(bsword) down to BS(target_seq), where target_seq is a specific
 reduced expression for the element bsword^subexp. The function computes the light leave and
 applies necessary braid moves to ensure the codomain matches target_seq.}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    W := B`W;

    // Build the light leave normally
    w := W.0;
    leaf := BSId(B, []);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Counit(B, si)   // U0
                  else leaf cat [si];           // U1
        else
            // D0 or D1. We might need to apply some braid moves.
            leaf := make_top_end_with(B, W, leaf, si);

            if ei eq 0 then // D0
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Mult(B, si),
                    leaf cat [si]
                ];
            else // D1
                leaf := &*[
                    leaf`bscod[1..#leaf`bscod-1] cat Cap(B, si),
                    leaf cat [si]
                ];
            end if;
        end if;

        w := w * (W.si)^ei;
    end for;

    // Now leaf`bscod is the actual Bott-Samelson sequence we ended up with
    actual_seq := leaf`bscod;

    // Verify that actual_seq and target_seq represent the same element
    require W!actual_seq eq W!target_seq:
        "Actual codomain", actual_seq, "and requested target", target_seq,
        "represent different elements";
    require #actual_seq eq #target_seq:
        "Sequences have different lengths";

    // Apply braid to change codomain from actual_seq to target_seq
    if actual_seq ne target_seq then
        braid := find_braid_morphism(B, W, actual_seq, target_seq);
        leaf := braid * leaf;
    end if;

    return leaf;
end intrinsic;

intrinsic LLUpFrom(B::BSCat, bsword::SeqEnum[RngIntElt], subexp::SeqEnum[RngIntElt],
                             source_seq::SeqEnum[RngIntElt]) -> BSMor
{Returns the light-leaf from BS(source_seq) up to BS(bsword), where source_seq is a specific
 reduced expression for the element bsword^subexp. The function computes the light leave and
 applies necessary braid moves to ensure the domain matches source_seq.}
    require #bsword eq #subexp: "Length", #bsword, "of bsword must agree with length", #subexp, "of 0-1 sequence.";
    require forall{s : s in subexp | s eq 0 or s eq 1}: "Subexp must be a 0-1 sequence.";

    W := B`W;

    // Build the light leave normally
    w := W.0;
    leaf := BSId(B, []);

    for i := 1 to #bsword do
        si := bsword[i];
        ei := subexp[i];
        if #(w * W.si) gt #w then
            leaf := ei eq 0
                select leaf cat Unit(B, si)     // U0
                  else leaf cat [si];           // U1
        else
            // D0 or D1. We might need to apply some braid moves.
            _, moves := BraidToEndWith(W, leaf`bsdom, si);
            braid := BSId(B, leaf`bsdom);
            for move in moves do
                braid := braid * BraidDown(B, braid`bsdom, move[1], move[2]);
            end for;
            leaf := leaf * braid;

            if ei eq 0 then // D0
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Comult(B, si)
                ];
            else // D1
                leaf := &*[
                    leaf cat [si],
                    leaf`bsdom[1..#leaf`bsdom-1] cat Cup(B, si)
                ];
            end if;
        end if;

        w := w * (W.si)^ei;
    end for;

    // Now leaf`bsdom is the actual Bott-Samelson sequence we ended up with
    actual_seq := leaf`bsdom;

    // Verify that actual_seq and source_seq represent the same element
    require W!actual_seq eq W!source_seq:
        "Actual domain", actual_seq, "and requested source", source_seq,
        "represent different elements";
    require #actual_seq eq #source_seq:
        "Sequences have different lengths";

    // Apply braid to change domain from actual_seq to source_seq
    if actual_seq ne source_seq then
        braid := find_braid_morphism_bot(B, W, actual_seq, source_seq);
        leaf := leaf * braid;
    end if;

    return leaf;
end intrinsic;

//============================================================================
// Subexpression Enumeration
//============================================================================

// Finds all subexpressions of (x_seq cat w_seq) that represent element y
// with the specified degree.
// WARNING: This uses brute-force enumeration over all 2^n subexpressions.
// For long words,we may need to optimize
function find_all_light_leaves_expressions(W, x, w, y : degree := 0)
    x_seq := Eltseq(x);
    w_seq := Eltseq(w);
    n := #x_seq + #w_seq;
    results := [];

    // Enumerate all 2^n subexpressions (O(2^n) complexity)
    for i in [0..2^n - 1] do
        bits := [];
        temp := i;
        for j in [1..n] do
            Append(~bits, temp mod 2);
            temp := temp div 2;
        end for;

        full_word := x_seq cat w_seq;

        subword := [];
        for j in [1..n] do
            if bits[j] eq 1 then
                Append(~subword, full_word[j]);
            end if;
        end for;

        if W!subword eq y then
            u := Id(W);
            d := 0;
            for j in [1..n] do
                w_j := full_word[j];
                if bits[j] eq 1 then
                    u := u * W![w_j];
                end if;
                if bits[j] eq 0 then
                    if Length(u) lt Length(u * W![w_j]) then
                        d := d + 1;
                    else
                        d := d - 1;
                    end if;
                end if;
            end for;

            if d eq degree then
                Append(~results, <bits, d>);
            end if;
        end if;
    end for;

    return results;
end function;
