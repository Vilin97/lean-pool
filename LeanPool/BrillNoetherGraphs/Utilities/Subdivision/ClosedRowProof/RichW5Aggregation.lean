/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.ClosedRowProof.RichLeafSound

/-!
# W5 aggregation on a contracted core class

W5 is checked before zero-length core edges are contracted, one original core
vertex at a time.  This small lemma is the purely algebraic part of its
closed-face use: any actual endpoint contributions which dominate W5's
conservative tail/head minima remain effective after summing an entire
contraction class.  It deliberately contains no raw-chip decoding; that
geometry supplies the two domination hypotheses at the call site.

It is deliberately based on `RichLeafSound` rather than on the final assembly
module, so that `RichLeafFullSound.richLeaf_sound` can consume it; the
`hTail`/`hHead` hypotheses are produced by `RichChipBridge`.
-/

@[expose] public section

namespace Utilities.Subdivision.ClosedRowProof

open Utilities

open MarkedGraphs.Certificate
open Utilities.Certificate

namespace RichWitness

variable {n p : ℕ}

/-- The actual residual at an original core vertex, parameterized by the
tail/head endpoint contributions furnished by the closed-face geometry. -/
def w5ActualResidual (w : RichWitness) (core : ExplicitPotential.Core n p)
    (mult : ℤ) (a : Fin n) (tail head : Fin p → ℤ) (v : Fin n) : ℤ :=
  w.divisorCore.getD v.val 0 - (if v.val == a.val then mult else 0) +
    (List.finRange p).foldl (fun z e => z +
      (if (core.tail e).val == v.val then tail e else 0) +
        (if (core.head e).val == v.val then head e else 0)) 0

/-- W5's Boolean table exposes a nonnegative residual at every original core
vertex. -/
theorem w5Residual_nonneg_of_w5Checks (w : RichWitness)
    (core : ExplicitPotential.Core n p) (hW5 : w.w5Checks core = true)
    (a v : Fin n) :
    0 ≤ w.w5Residual core a.val v.val := by
  simp only [w5Checks, ExplicitPotential.allFin_eq_true_iff,
    decide_eq_true_eq] at hW5
  exact hW5 a v

/-- If the actual endpoint contributions dominate W5's conservative minima,
then every original-core residual is effective. -/
theorem w5ActualResidual_nonneg (w : RichWitness)
    (core : ExplicitPotential.Core n p) (mult : ℤ)
    (a : Fin n) (tail head : Fin p → ℤ)
    (hTail : ∀ e, w.tailContribution a.val e.val ≤ tail e)
    (hHead : ∀ e, w.headContribution a.val e.val ≤ head e)
    (v : Fin n) (hbase : 0 ≤ w.w5MultResidual core mult a.val v.val) :
    0 ≤ w.w5ActualResidual core mult a tail head v := by
  unfold w5MultResidual at hbase
  unfold w5ActualResidual
  let checkedStep : ℤ → Fin p → ℤ := fun z e => z +
    (if (core.tail e).val == v.val then w.tailContribution a.val e.val else 0) +
      (if (core.head e).val == v.val then w.headContribution a.val e.val else 0)
  let actualStep : ℤ → Fin p → ℤ := fun z e => z +
    (if (core.tail e).val == v.val then tail e else 0) +
      (if (core.head e).val == v.val then head e else 0)
  have hFold : ∀ (es : List (Fin p)) (z₁ z₂ : ℤ), z₁ ≤ z₂ →
      es.foldl checkedStep z₁ ≤ es.foldl actualStep z₂ := by
    intro es
    induction es with
    | nil => intro z₁ z₂ hz; exact hz
    | cons e es ih =>
        intro z₁ z₂ hz
        simp only [List.foldl_cons]
        have hTail' :
            (if (core.tail e).val == v.val then w.tailContribution a.val e.val else 0) ≤
              (if (core.tail e).val == v.val then tail e else 0) := by
          split <;> simp_all
        have hHead' :
            (if (core.head e).val == v.val then w.headContribution a.val e.val else 0) ≤
              (if (core.head e).val == v.val then head e else 0) := by
          split <;> simp_all
        have hstep : checkedStep z₁ e ≤ actualStep z₂ e := by
          dsimp [actualStep, checkedStep]
          omega
        exact ih (checkedStep z₁ e) (actualStep z₂ e) hstep
  have hContrib : (List.finRange p).foldl checkedStep 0 ≤
      (List.finRange p).foldl actualStep 0 := hFold _ _ _ (le_refl 0)
  have hbase' : 0 ≤ w.divisorCore.getD v.val 0 -
      (if v.val == a.val then mult else 0) +
      (List.finRange p).foldl checkedStep 0 := by
    simpa [checkedStep] using hbase
  change 0 ≤ w.divisorCore.getD v.val 0 -
    (if v.val == a.val then mult else 0) +
    (List.finRange p).foldl actualStep 0
  exact hbase'.trans (add_le_add_right hContrib _)

/-- W5 survives contraction: summing the actual residuals over an arbitrary
quotient-core class is nonnegative.  The class is written using the exact
fiber that `richCoreDivisor` and the piecewise-script core formula use. -/
theorem w5ActualResidual_class_nonneg
    (d : Utilities.Certificate.DegenerateSpec.DegSpec n p)
    (w : RichWitness) (core : ExplicitPotential.Core n p) (mult : ℤ)
    (a : Fin n)
    (hbase : ∀ v : Fin n, 0 ≤ w.w5MultResidual core mult a.val v.val)
    (tail head : Fin p → ℤ)
    (hTail : ∀ e, w.tailContribution a.val e.val ≤ tail e)
    (hHead : ∀ e, w.headContribution a.val e.val ≤ head e)
    (vertex : Fin n) :
    0 ≤ ∑ v ∈ Finset.univ.filter (fun v : Fin n => d.rep v = d.rep vertex),
      w.w5ActualResidual core mult a tail head v := by
  apply Finset.sum_nonneg
  intro v hv
  exact w.w5ActualResidual_nonneg core mult a tail head hTail hHead v (hbase v)

end RichWitness

end Utilities.Subdivision.ClosedRowProof
