/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Assembly.BlueprintSchur
public import LeanPool.RegtsSevenster.RS.Novel.Skein.LoopExample
public import LeanPool.RegtsSevenster.RS.TheoremConverse

/-!
# Blueprint: the converse audit

The third part of the axiom audit: the chord diagram of a boundary
pairing, the super Gram identity, the interface lift, and the
converse itself.  The prose between pins says what each step
contributes; read `Blueprint.lean` first for the forward direction.
-/

/-! ### Chords of the boundary pairing

A subset's boundary flags pair up into chords; the involution
that records them, extended by the identity off the used labels,
is what the Koszul sign is read from.
-/

/- Upstream audit output: 'RS.EdgeSubset.pathMatch_eq_pairing_of_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/

-- Boundary flags carry distinct labels, so a subset has at most as
-- many as the interface has labels.  With the parity above, one label
-- leaves the boundary unused and forces a surviving state into the
-- even sector.

-- A matching state's odd labels are in bijection with the subset's
-- boundary flags, so there is an even number of them -- which is
-- exactly what the Koszul sign's exponent is handed.

-- The out-end test asks for an odd colour, so an everywhere-even state
-- is its own twist and carries no sign: there the conjugated kernel is
-- the plain Koszul kernel at the raw states.

-- So the Koszul sign is read off the chord diagram: at a matching
-- state it is (-1) to the number of chords of the very diagram the cut
-- signs are computed from.

-- Crossing asks for a strict interleaving, so a chord with equal ends
-- crosses nothing and nothing crosses it: an involution extended by
-- the identity off a subset has the crossing count of its genuine
-- chords alone.

-- Chords pair up the labels a subset uses; extending by the identity
-- off those labels gives an involution of the whole interface, whose
-- genuine chords are the subset's and whose fixed points are the
-- unused labels.  This is what the restriction transports apply to.

/- Upstream audit output: 'RS.EdgeSubset.boundaryFlag_chordInv' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chordInv_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chordInv_invol' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chordInv_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/

-- At a used label the two chord descriptions coincide -- the
-- involution's chord is the sorted pair the diagram records -- and at
-- an unused one the involution's chord is degenerate, hence inert.

/- Upstream audit output: 'RS.EdgeSubset.boundaryLabel_boundaryFlag' depends on axioms: [propext, Classical.choice, Quot.sound] -/

-- The cycle data is permutation-theoretic and reads no order, so
-- conjugating both involutions by a bijection carries the walk, its
-- return time and its label set across, and the cycle count is
-- unchanged.

/-! ### The Gram identity

The connection matrix of a parameter with a super Gram
factorization has bounded rank, which is the converse's engine.
-/

/- Upstream audit output: 'RS.converse_of_superGram' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.converse_of_superGramIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.exists_sum_sum_superForm_tFull' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.exists_sum_sum_superForm_tensorTermAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The interface lift

Transition data carried up the gluing interface one cut at a time
and back down: the lift, the two glue branches, and the round
trip on directions and on the matching.
-/

/- Upstream audit output: 'RS.EdgeSubset.sign_composition_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.chainDir_pushData_alternates' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.edgeSum_closeBase_eq_pairAgreeValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.liftData' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.glueDataOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.glueDataClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.match_unglue_glueDataOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.isOut_unglue_glueDataOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.match_unglue_glueDataClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.isOut_unglue_glueDataClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.edgeTermAt_pushData_colourSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### The base sum and the converse

The subset sum over the composition's base, its independence of
the free bits, and the theorems of record.
-/

/- Upstream audit output: 'RS.EdgeSubset.summandSum_bits_indep' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.baseSumBitsOf_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.baseSumIsClosure_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.EdgeSubset.superGramIdentity' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_converse' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.regts_sevenster_quant_roundtrip' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/-! ### Definition 5, evaluated

The paper's worked example: the loop graph against the functional
whose mixed partition function is the characteristic polynomial.
Its value `θ − 2` fixes the loop's two incidences, the Eulerian
condition, the circuit sign and the `η`-convention all at once;
adjoining a free circle sends the same functional to `0`, which
fixes the loop/free-circle distinction.
-/

/- Upstream audit output: 'RS.mixedPartition_loopGraph' depends on axioms: [propext, Classical.choice, Quot.sound] -/

/- Upstream audit output: 'RS.mixedPartition_loopGraphCircle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
