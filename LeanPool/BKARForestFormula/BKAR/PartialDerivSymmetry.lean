/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders
import LeanPool.BKARForestFormula.BKAR.Smoothness

/-! # Symmetry of mixed partial derivatives

Under the global smoothness hypothesis `BKARContDiff`, coordinate partial
derivatives on the edge-coupling space commute.  Consequently
`mixedPartialList` is invariant under permutations of its edge list and,
for any enumeration of a forest's edge set, agrees with the unordered
forest mixed partial `mixedPartial`.  This order-independence is what lets
the order-by-order expansion be regrouped into the order-free integrand of
the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

open scoped ContDiff

namespace BKAR

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace BKARContDiff

variable {ρ : (Edge V → ℝ) → ℝ}

/--
Under the global BKAR smoothness hypothesis, coordinate partial derivatives
commute pointwise. This is the analytic order-independence ingredient needed
to replace recursive ordered-sector mixed partials by the order-free forest
mixed partial.
-/
theorem partialDeriv_comm_apply
    (hρ : BKARContDiff ρ) (e f : Edge V) (x : Edge V → ℝ) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) x =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) x := by
  have hpf :
      BKAR.partialDeriv f ρ =
        fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := by
    funext y
    exact partialDeriv_of_hasFDerivAt f
      ((hρ.differentiableAt y).hasFDerivAt)
  have hpe :
      BKAR.partialDeriv e ρ =
        fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    funext y
    exact partialDeriv_of_hasFDerivAt e
      ((hρ.differentiableAt y).hasFDerivAt)
  have hdiffF :
      DifferentiableAt ℝ (BKAR.partialDeriv f ρ) x :=
    ((hρ.partialDeriv f).differentiableAt x)
  have hdiffE :
      DifferentiableAt ℝ (BKAR.partialDeriv e ρ) x :=
    ((hρ.partialDeriv e).differentiableAt x)
  have hc :
      DifferentiableAt ℝ
        (fun y : Edge V → ℝ =>
          (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ)) x :=
    (hρ.fderiv_contDiff.differentiable (by simp)).differentiableAt
  have hconstF :
      DifferentiableAt ℝ (fun _ : Edge V → ℝ => edgeBasis f) x :=
    differentiableAt_const _
  have hconstE :
      DifferentiableAt ℝ (fun _ : Edge V → ℝ => edgeBasis e) x :=
    differentiableAt_const _
  have hclmF :=
    fderiv_clm_apply
      (𝕜 := ℝ)
      (c := fun y : Edge V → ℝ =>
        (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ))
      (u := fun _ : Edge V → ℝ => edgeBasis f)
      (x := x) hc hconstF
  have hclmE :=
    fderiv_clm_apply
      (𝕜 := ℝ)
      (c := fun y : Edge V → ℝ =>
        (fderiv ℝ ρ y : (Edge V → ℝ) →L[ℝ] ℝ))
      (u := fun _ : Edge V → ℝ => edgeBasis e)
      (x := x) hc hconstE
  have hleft :
      fderiv ℝ (BKAR.partialDeriv f ρ) x (edgeBasis e) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := by
    rw [hpf, hclmF]
    simp [fderiv_fun_const]
  have hright :
      fderiv ℝ (BKAR.partialDeriv e ρ) x (edgeBasis f) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    rw [hpe, hclmE]
    simp [fderiv_fun_const]
  have hsymm :
      (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) =
        (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := by
    exact
      ((hρ.contDiff.contDiffAt (x := x)).isSymmSndFDerivAt
        (n := (∞ : WithTop ℕ∞))
        (by simp only [minSmoothness_of_isRCLikeNormedField]
            exact WithTop.coe_le_coe.mpr le_top)).eq
          (edgeBasis e) (edgeBasis f)
  calc
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) x
        = fderiv ℝ (BKAR.partialDeriv f ρ) x (edgeBasis e) := by
          exact partialDeriv_of_hasFDerivAt e hdiffF.hasFDerivAt
    _ = (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis e) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis f) := hleft
    _ = (fderiv ℝ (fderiv ℝ ρ) x
          (edgeBasis f) : (Edge V → ℝ) →L[ℝ] ℝ) (edgeBasis e) := hsymm
    _ = fderiv ℝ (BKAR.partialDeriv e ρ) x (edgeBasis f) := hright.symm
    _ = BKAR.partialDeriv f (BKAR.partialDeriv e ρ) x := by
          exact (partialDeriv_of_hasFDerivAt f hdiffE.hasFDerivAt).symm

theorem partialDeriv_comm
    (hρ : BKARContDiff ρ) (e f : Edge V) :
    BKAR.partialDeriv e (BKAR.partialDeriv f ρ) =
      BKAR.partialDeriv f (BKAR.partialDeriv e ρ) := by
  funext x
  exact hρ.partialDeriv_comm_apply e f x

theorem mixedPartialList_cons_cons_comm
    (hρ : BKARContDiff ρ) (e f : Edge V) (es : List (Edge V)) :
    BKAR.mixedPartialList (e :: f :: es) ρ =
      BKAR.mixedPartialList (f :: e :: es) ρ := by
  exact (hρ.mixedPartialList es).partialDeriv_comm e f

/--
Mixed partials along two permuted edge lists agree under `BKARContDiff`.
This is the global analytic bridge from canonical-order expressions to the
unordered forest-edge derivative in the final cube contribution.
-/
theorem mixedPartialList_eq_of_perm
    {es₁ es₂ : List (Edge V)} (hperm : es₁.Perm es₂)
    (hρ : BKARContDiff ρ) :
    BKAR.mixedPartialList es₁ ρ =
      BKAR.mixedPartialList es₂ ρ := by
  induction hperm generalizing ρ with
  | nil =>
      rfl
  | cons e hperm ih =>
      change BKAR.partialDeriv e
          (BKAR.mixedPartialList _ ρ) =
        BKAR.partialDeriv e
          (BKAR.mixedPartialList _ ρ)
      rw [ih hρ]
  | swap e f es =>
      exact (hρ.mixedPartialList_cons_cons_comm e f es).symm
  | trans _ _ ih₁ ih₂ =>
      exact (ih₁ hρ).trans (ih₂ hρ)

end BKARContDiff

namespace Forest

variable (F : Forest V)
variable {ρ : (Edge V → ℝ) → ℝ}

theorem mixedPartial_eq_mixedPartialList_of_mem_edgeOrders
    {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (hρ : BKARContDiff ρ) :
    F.mixedPartial ρ = BKAR.mixedPartialList order.reverse ρ := by
  have hperm : F.edges.toList.Perm order.reverse := by
    rw [List.perm_reverse]
    exact ((F.mem_edgeOrders_iff).mp horder).symm
  exact hρ.mixedPartialList_eq_of_perm hperm

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
