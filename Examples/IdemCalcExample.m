// Load ASLoc
AttachSpec("ASLoc.spec");

// Set up the category
W := CoxeterGroup(GrpFPCox, "A3");
Cartan := CartanMatrix("A3");
B := BSCategory(Cartan, W);
HAlg := IHeckeAlgebra(W);
H := StandardBasis(HAlg);
C := CanonicalBasis(HAlg);

// Define the action
act := function(w)
    return FActionByElt(B, w);
end function;

// Create the idempotent collection
IC := CreateIdemCollection(B, C, act);

// Enable verbose output if desired
SetVerbose("IdemCalc", 3);  // Level 1: main progress, Level 2: more details, Level 3: everything


// Build idempotents
x := LongestElement(W);
ex := BuildIdempotent(IC, x);

// Check cache status
print "Number of cached idempotents:", NumberOfCachedIdempotents(IC);
print "Number of cached light leaves:", NumberOfCachedLightLeaves(IC);
print "Cached elements:", CachedIdempotents(IC);

// Get specific cached idempotent
if HasCachedIdempotent(IC, W![1,2,1,3]) then
    e1213 := GetCachedIdempotent(IC, W![1,2,1,3]);
end if;

// Clear caches if needed
// ClearLightLeaveCache(IC);
// ClearIdempotentCache(IC);
// ClearCache(IC);
