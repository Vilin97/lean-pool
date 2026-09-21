/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafAssembly
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.DoubledAnchorChecks

/-!
# Marked leaf checkers: domination, multiplicity residuals, legged and pointed leaves

The generic row-proof checker in this directory validates a leaf against the
five closed-face rows `W1`–`W5` plus the degree row `W7`.  A leaf that also
carries a **mark** — a distinguished core vertex at which the divisor must
dominate, or at which a residual must be read with multiplicity greater than
one — needs two more executable rows, and a leaf carrying **two** marks (a
"legged" leaf, in the vocabulary of the once- and twice-marked programmes)
needs one more table per mark.

Those rows were written privately, one copy per marked programme, on top of a
private duplicate of this checker.  They are generic: nothing below mentions a
genus, a row, or a marked-graph existence statement.  They belong here, beside
the checker they extend, so that the checker's namespace stays self-contained
in its own directory.

## What is here, and what deliberately is not

* the four **leaf checkers**, assembled from the two doubled-anchor rows in
  `Utilities/Subdivision/DoubledAnchorChecks.lean`:
  `Witness.leggedLeafChecks`, `Witness.pointedLeafChecks`,
  `RichWitness.pointedLeafChecks`, `RichWitness.richLeggedLeafChecks`;
* `RichWitness.richDivisor_rank_ge_one`, the strong-separator half of
  `richLeaf_sound` stated for the divisor rather than for `BNExists`, because a
  legged leaf needs the divisor itself.

**Not here, by design:** the soundness theorems that consume these rows —
`effective_degenerateDivisor_sub_smul_one_chip`,
`class_mult_balance_nonnegative`,
`winnable_sub_smul_one_chip_degenerateCoreVertex` and the marked-completion
bridges.  They are heavier, they are consumed only by the marked programmes,
and promoting them would buy nothing here.  They stay in
`MarkedGraphs/Certificate/DegenerateDoubledAnchor.lean`, which imports this
file.

## Why the checkers and not just the definitions

`Witness` and `RichWitness` are the structures declared in this directory.
Dot notation resolves `w.leggedLeafChecks` in the namespace of `w`'s type, so a
checker written elsewhere is invisible to `w.leggedLeafChecks` however the
file is imported.  Keeping these four here is what lets the marked programmes
consume the row-proof checker without maintaining a second copy of it.
-/

namespace Utilities.Subdivision.ClosedRowProof

open Utilities
open Utilities.Certificate
open Utilities.Certificate.ExplicitPotential
open Utilities.Certificate.ContractionForestCensusGeneral

variable {m n p : ℕ}

/-! ## Compact marked leaves -/

/-- **The legged leaf checker.**  `Witness.leafChecks` plus the goal's two
extra rows: W7's domination at the first mark (`chips` chips) and the
`(comp x …)` plan's W5 at multiplicity `mult` at the second.

Both extra rows are point-independent tests on the certificate's own core
divisor, so an emitter discharges them by `decide`. -/
def Witness.leggedLeafChecks (w : Witness) (m : ℕ)
    (core : ExplicitPotential.Core n p) (Γ : Context) (degree : ℤ)
    (mark attachment : Fin n) (chips mult : ℤ) : Bool :=
  w.leafChecks m core Γ degree &&
  (leafCertificate m core w).dominatesMarkCheck mark chips &&
  (leafCertificate m core w).multResidualCheck mult attachment

/-- Compact pointed checker: the ordinary rank-one leaf plus the same plan at
the marked core vertex checked with multiplicity `mult`. -/
def Witness.pointedLeafChecks (w : Witness) (M : ℕ)
    (core : ExplicitPotential.Core n p) (Γ : Context) (degree : ℤ)
    (mark : Fin n) (mult : ℤ) : Bool :=
  w.leafChecks M core Γ degree &&
    (leafCertificate M core w).multResidualCheck mult mark

/-! ## Rich marked leaves -/

namespace RichWitness

/-- **The rich divisor has rank at least one**, by the strong separator over
the `n` rank anchors.  This is `richLeaf_sound`'s second half, kept as its own
statement because a marked leaf needs the divisor and not just `BNExists`. -/
theorem richDivisor_rank_ge_one (core : ExplicitPotential.Core n p)
    (w : RichWitness) (Γ : Context) (hn : 0 < n)
    (x : List ℤ) (hx : Γ.Holds x)
    (hConnected : core.connectedCheck = true)
    (hW1 : w.w1Checks core Γ = true) (hW2 : w.w2Checks core Γ = true)
    (hW3 : w.w3Checks core = true) (hW4 : w.w4Checks core Γ = true)
    (hW5 : w.w5Checks core = true)
    (ℓ : Fin p → ℕ) (hCoord : ∀ e : Fin p, eval (coordForm e.val) x = (ℓ e : ℤ))
    (hForest : IsForest core (zeroSet ℓ))
    (hNotLoopy : ¬ IsLoopy core (zeroSet ℓ)) (fallback : Fin n) :
    rank (censusSpec core hn ℓ hForest hNotLoopy).graph
      (w.richDivisor (censusSpec core hn ℓ hForest hNotLoopy) fallback x) ≥ 1 := by
  classical
  set d := censusSpec core hn ℓ hForest hNotLoopy with hd
  apply StrongSeparator.rank_ge_one_of_strongSeparatorCertificate
    (Utilities.Certificate.DegenerateSpec.DegSpec.graph_connected_of_coreConnected d
      ((ExplicitPotential.Core.connectedCheck_eq_true_iff core).mp hConnected))
    (ExplicitPotential.Certificate.degenerateCoreVertices_nonempty d)
    (Utilities.Certificate.DegenerateSpec.DegSpec.strongSeparatorCertificate d)
  intro coreVertex hCoreVertex
  obtain ⟨anchor, -, rfl⟩ := Finset.mem_image.mp hCoreVertex
  have hW5m : ∀ v : Fin n, 0 ≤ w.w5MultResidual core 1 anchor.val v.val :=
    fun v => w.w5Residual_nonneg_of_w5Checks core hW5 anchor v
  have := w.richDivisor_winnable_sub_smul core Γ hn x hx hW1 hW2 hW3 hW4 ℓ
    hCoord hForest hNotLoopy fallback 1 anchor hW5m
  simpa [Utilities.Certificate.StrongSeparator.Reaches,
    one_smul] using this

/-- Rich pointed checker.  The ordinary W1--W5 leaf supplies rank one; one
additional W5 table reads the marked plan with multiplicity `mult`. -/
def pointedLeafChecks (w : RichWitness) (M : ℕ)
    (core : ExplicitPotential.Core n p) (Γ : Context) (degree : ℤ)
    (mark : Fin n) (mult : ℤ) : Bool :=
  w.richLeafChecks M core Γ degree && w.w5MultChecks core mult mark.val

/-- **The legged rich leaf checker.**  `richLeafChecks` plus one W5 table per
mark, at the mark's own multiplicity.

There is deliberately no W7 domination row: the first mark's obligation is
supplied as winnability by its own W5 table.  Compare
`Witness.leggedLeafChecks`, which does carry a domination row because the
compact leaf's divisor is available pointwise. -/
def richLeggedLeafChecks (w : RichWitness) (M : ℕ)
    (core : ExplicitPotential.Core n p) (Γ : Context) (degree : ℤ)
    (mark attachment : Fin n) (chips mult : ℤ) : Bool :=
  w.richLeafChecks M core Γ degree &&
  w.w5MultChecks core chips mark.val &&
  w.w5MultChecks core mult attachment.val

end RichWitness

end Utilities.Subdivision.ClosedRowProof
