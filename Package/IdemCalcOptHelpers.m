//============================================================================
// IdemCalcOptHelpers.m - Progress display helpers for IdemCalcOpt
//============================================================================

// Verbose output declaration
declare verbose IdemCalcOpt, 3;

//============================================================================
// Progress Display Functions
//============================================================================

// ANSI escape codes for cursor control - using CodeToString for escape char
// ESC[A = move cursor up one line
// ESC[2K = clear entire line

function SeqToCompactStr(seq)
    // Format sequence without spaces: [1,2,3] instead of [ 1, 2, 3 ]
    if #seq eq 0 then
        return "[]";
    end if;
    s := "[";
    for i := 1 to #seq do
        s := s cat Sprintf("%o", seq[i]);
        if i lt #seq then
            s := s cat ",";
        end if;
    end for;
    s := s cat "]";
    return s;
end function;

function SubexpToStr(subexp)
    // Format 01 subexpression compactly as string of 0s and 1s
    s := "";
    for i := 1 to #subexp do
        s := s cat Sprintf("%o", subexp[i]);
    end for;
    return s;
end function;

procedure ClearLine()
    // ESC = ASCII 27, then [A to move up, [2K to clear line
    esc := CodeToString(27);
    printf "%o[A%o[2K", esc, esc;
end procedure;

procedure PrintTreeLine(IC, depth, seq, len)
    // Print a single line of the tree with proper indentation
    indent := "";
    for i := 1 to depth-1 do
        indent := indent cat "   ";
    end for;

    if depth gt 1 then
        prefix := "|-> ";
    else
        prefix := "";
    end if;

    // Format sequence compactly
    seq_str := SeqToCompactStr(seq);
    max_seq_len := 40;
    if #seq_str gt max_seq_len then
        seq_str := seq_str[1..max_seq_len-3] cat "...";
    end if;

    line := Sprintf("%o%oComputing %o (len %o)", indent, prefix, seq_str, len);

    // Add LL timing if available
    if IC`LastLightLeafTime gt 0.1 then
        line := line cat Sprintf(" [LL: %.1os]", IC`LastLightLeafTime);
    end if;

    printf "%o\n", line;
end procedure;

procedure PrintLLCheck(IC, word_seq, subexp, target_seq)
    // Print which light leaf we're checking at the bottom
    if not IC`ShowProgress then
        return;
    end if;

    depth := #IC`RecursionStack;
    indent := "";
    for i := 1 to depth do
        indent := indent cat "   ";
    end for;

    // Format sequences compactly
    word_str := SeqToCompactStr(word_seq);
    subexp_str := SubexpToStr(subexp);

    if #word_str gt 30 then
        word_str := word_str[1..27] cat "...";
    end if;

    printf "%o    LL: %o (%o)\n", indent, word_str, subexp_str;
end procedure;

procedure ClearLLLine(IC)
    // Clear the LL line when done checking
    if IC`ShowProgress then
        ClearLine();
    end if;
end procedure;

procedure PushRecursion(IC, x)
    if IC`ShowProgress then
        seq := Eltseq(x);
        len := #seq;
        Append(~IC`RecursionStack, <x, len>);
        depth := #IC`RecursionStack;
        PrintTreeLine(IC, depth, seq, len);
    end if;
end procedure;

procedure PopRecursion(IC)
    if IC`ShowProgress and #IC`RecursionStack gt 0 then
        // Move cursor up and clear the line we're leaving
        ClearLine();
        Remove(~IC`RecursionStack, #IC`RecursionStack);
    end if;
end procedure;

procedure SetLightLeafTime(IC, t)
    IC`LastLightLeafTime := t;
    IC`TotalLightLeafTime := IC`TotalLightLeafTime + t;
end procedure;

