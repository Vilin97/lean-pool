/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.ExtendedWeakL1Combinators
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleOperator

/-!
# Passing finite truncation-radius estimates to a genuine frozen block

Krause--Lacey's sparse theorem is applied first to finite, everywhere-finite
maxima of sharp truncations.  This file proves the exact limiting step which
recovers the paper's supremum over every positive truncation radius without
losing the uniform weak constant.  The limit uses the fixed countable dense
family already proved to recover the full real-radius supremum.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryMiddleFiniteRadiusLimit

open ExtendedWeakL1Combinators KaltonPaperApplication
open LacunaryMiddleOperator LacunaryMiddleRange
open QuadraticHilbertMaximalMeasurable


noncomputable section

/-- The frozen quadratic-Hilbert block with the truncation radii restricted
to one finite subset of the fixed countable dense family. -/
def finiteRadiusFrozenBlockHilbertMaxEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ)
    (s : Finset densePositiveRadii) (x : ℝ) : ENNReal :=
  (Q B τ).sup fun m ↦ s.sup fun ε ↦
    ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
      (frozenBlockInput A f k B c τ) x‖ₑ

/-- Finite radius sets form a pointwise directed family: two approximants
are both dominated by the approximant on their union. -/
theorem directed_finiteRadiusFrozenBlockHilbertMaxEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) :
    Directed (fun F G : ℝ → ENNReal ↦ ∀ x, F x ≤ G x)
      (fun s : Finset densePositiveRadii ↦
        finiteRadiusFrozenBlockHilbertMaxEnorm A f k B c τ s) := by
  classical
  intro s t
  refine ⟨s ∪ t, ?_, ?_⟩
  · intro x
    unfold finiteRadiusFrozenBlockHilbertMaxEnorm
    apply Finset.sup_le
    intro m hm
    exact (Finset.sup_mono Finset.subset_union_left).trans
      (Finset.le_sup (s := Q B τ)
        (f := fun n ↦ (s ∪ t).sup fun ε ↦
          ‖quadraticHilbertTrunc (dyadicModulation n) ε.1.1
            (frozenBlockInput A f k B c τ) x‖ₑ) hm)
  · intro x
    unfold finiteRadiusFrozenBlockHilbertMaxEnorm
    apply Finset.sup_le
    intro m hm
    exact (Finset.sup_mono Finset.subset_union_right).trans
      (Finset.le_sup (s := Q B τ)
        (f := fun n ↦ (s ∪ t).sup fun ε ↦
          ‖quadraticHilbertTrunc (dyadicModulation n) ε.1.1
            (frozenBlockInput A f k B c τ) x‖ₑ) hm)

/-- The directed supremum of the finite-radius frozen blocks is exactly the
genuine finite-modulation block with every positive real truncation radius. -/
theorem iSup_finiteRadiusFrozenBlockHilbertMaxEnorm_eq
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ) (x : ℝ) :
    (⨆ s : Finset densePositiveRadii,
      finiteRadiusFrozenBlockHilbertMaxEnorm A f k B c τ s x) =
        frozenBlockHilbertMaxEnorm A f k B c τ x := by
  classical
  have hinput : Integrable (frozenBlockInput A f k B c τ) :=
    integrable_frozenBlockInput hf hfi hAk B c τ
  apply le_antisymm
  · apply iSup_le
    intro s
    unfold finiteRadiusFrozenBlockHilbertMaxEnorm frozenBlockHilbertMaxEnorm
    apply Finset.sup_le
    intro m hm
    apply Finset.sup_le
    intro ε hε
    have hradius :
        ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
            (frozenBlockInput A f k B c τ) x‖ₑ ≤
          quadraticHilbertMaximalTruncation (dyadicModulation m)
            (frozenBlockInput A f k B c τ) x := by
      unfold quadraticHilbertMaximalTruncation
      exact le_iSup (fun δ : {δ : ℝ // 0 < δ} ↦
        ‖quadraticHilbertTrunc (dyadicModulation m) δ.1
          (frozenBlockInput A f k B c τ) x‖ₑ) ε.1
    exact hradius.trans (Finset.le_sup (s := Q B τ)
      (f := fun n ↦ quadraticHilbertMaximalTruncation (dyadicModulation n)
        (frozenBlockInput A f k B c τ) x) hm)
  · unfold frozenBlockHilbertMaxEnorm
    apply Finset.sup_le
    intro m hm
    rw [← countableQuadraticHilbertMaximalTruncation_eq
      (dyadicModulation m) hinput x]
    unfold countableQuadraticHilbertMaximalTruncation
    apply iSup_le
    intro ε
    apply le_iSup_of_le ({ε} : Finset densePositiveRadii)
    change
      ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
          (frozenBlockInput A f k B c τ) x‖ₑ ≤
        (Q B τ).sup fun n ↦
          ({ε} : Finset densePositiveRadii).sup fun δ ↦
            ‖quadraticHilbertTrunc (dyadicModulation n) δ.1.1
              (frozenBlockInput A f k B c τ) x‖ₑ
    calc
      ‖quadraticHilbertTrunc (dyadicModulation m) ε.1.1
          (frozenBlockInput A f k B c τ) x‖ₑ ≤
          ({ε} : Finset densePositiveRadii).sup fun δ ↦
            ‖quadraticHilbertTrunc (dyadicModulation m) δ.1.1
              (frozenBlockInput A f k B c τ) x‖ₑ :=
        Finset.le_sup (s := ({ε} : Finset densePositiveRadii))
          (f := fun δ ↦ ‖quadraticHilbertTrunc (dyadicModulation m) δ.1.1
            (frozenBlockInput A f k B c τ) x‖ₑ) (Finset.mem_singleton_self ε)
      _ ≤ (Q B τ).sup fun n ↦
          ({ε} : Finset densePositiveRadii).sup fun δ ↦
            ‖quadraticHilbertTrunc (dyadicModulation n) δ.1.1
              (frozenBlockInput A f k B c τ) x‖ₑ :=
        Finset.le_sup (s := Q B τ) (f := fun n ↦
          ({ε} : Finset densePositiveRadii).sup fun δ ↦
            ‖quadraticHilbertTrunc (dyadicModulation n) δ.1.1
              (frozenBlockInput A f k B c τ) x‖ₑ) hm

/-- A weak estimate uniform over all finite truncation-radius subsets passes
to the exact all-radius frozen block with no constant loss. -/
theorem hasExtendedWeakL1Bound_frozenBlockHilbertMaxEnorm_of_finiteRadii
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ)
    {mu : Measure ℝ} {C : ℝ}
    (hfinite : ∀ s : Finset densePositiveRadii,
      HasExtendedWeakL1Bound mu C
        (finiteRadiusFrozenBlockHilbertMaxEnorm A f k B c τ s)) :
    HasExtendedWeakL1Bound mu C
      (frozenBlockHilbertMaxEnorm A f k B c τ) := by
  let _ := countable_densePositiveRadii.toEncodable
  rw [← funext (iSup_finiteRadiusFrozenBlockHilbertMaxEnorm_eq
    hf hfi hAk B c τ)]
  exact ExtendedWeakL1Combinators.hasExtendedWeakL1Bound_iSup_of_directed
    (directed_finiteRadiusFrozenBlockHilbertMaxEnorm A f k B c τ) hfinite


end
end LacunaryMiddleFiniteRadiusLimit
end QuadraticCarleson
