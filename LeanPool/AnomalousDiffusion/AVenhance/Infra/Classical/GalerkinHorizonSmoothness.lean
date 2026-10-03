/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothWordEquation
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Closed-slab smoothness criteria for mixed time/spatial derivative families. -/

@[expose] public section

noncomputable section

open Set Homogenization

namespace AVenhance.Infra.Classical

/-- Two compatible one-sided derivatives determine the ordinary derivative. -/
theorem classicalHasDerivAt_of_within_Iic_Ici
    {f : ℝ → ℝ} {f' x : ℝ}
    (hleft : HasDerivWithinAt f f' (Iic x) x)
    (hright : HasDerivWithinAt f f' (Ici x) x) :
    HasDerivAt f f' x := by
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have h := (hasDerivWithinAt_iff_tendsto_slope).mp hleft
    simpa using h
  · have h := (hasDerivWithinAt_iff_tendsto_slope).mp hright
    simpa using h

/-- The full derivative map for a spatial word: its time component is the equation right-hand side,
and its spatial components are the coordinate derivatives. -/
def classicalSpatialWordDerivativeLinearMap
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) :
    (ℝ × Vec 2) →L[ℝ] ℝ :=
  (ContinuousLinearMap.toSpanSingleton ℝ (q w p)).coprod
    (∑ i : Fin 2, f (i :: w) p •
      (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))

/-- A continuous spatial-word family is smooth to every finite order once each word has its
equation and coordinate derivatives, and the equation right-hand sides inherit finite regularity
from the word family. -/
theorem classicalSpatialWordFamily_contDiffOn
    (S : Set (ℝ × Vec 2)) (hS : UniqueDiffOn ℝ S)
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (hcontinuous : ∀ w, ContinuousOn (f w) S)
    (hderivative : ∀ w p, p ∈ S → HasFDerivWithinAt (f w)
      (classicalSpatialWordDerivativeLinearMap f q w p) S p)
    (hRhsRegular : ∀ k : ℕ,
      (∀ w, ContDiffOn ℝ (k : WithTop ℕ∞) (f w) S) →
      ∀ w, ContDiffOn ℝ (k : WithTop ℕ∞) (q w) S) :
    ∀ w, ContDiffOn ℝ (⊤ : ℕ∞) (f w) S := by
  have hfinite : ∀ k : ℕ, ∀ w,
      ContDiffOn ℝ (k : WithTop ℕ∞) (f w) S := by
    intro k
    induction k with
    | zero =>
        intro w
        change ContDiffOn ℝ (0 : WithTop ℕ∞) (f w) S
        rw [contDiffOn_zero]
        exact hcontinuous w
    | succ k ih =>
        intro w
        change ContDiffOn ℝ ((k : WithTop ℕ∞) + 1) (f w) S
        rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hS]
        refine ⟨?_, classicalSpatialWordDerivativeLinearMap f q w, ?_, ?_⟩
        · intro hk
          simp at hk
        · let A : ℝ × Vec 2 → ℝ →L[ℝ] ℝ := fun p =>
            ContinuousLinearMap.toSpanSingleton ℝ (q w p)
          let B : ℝ × Vec 2 → Vec 2 →L[ℝ] ℝ := fun p =>
            ∑ i : Fin 2, f (i :: w) p •
              (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)
          have hq := hRhsRegular k ih w
          have hA : ContDiffOn ℝ (k : WithTop ℕ∞) A S := by
            change ContDiffOn ℝ (k : WithTop ℕ∞)
              (fun p => ContinuousLinearMap.toSpanSingleton ℝ (q w p)) S
            exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E :=
                ℝ)).contDiff.comp_contDiffOn hq
          have hBterm (i : Fin 2) : ContDiffOn ℝ (k : WithTop ℕ∞)
              (fun p => f (i :: w) p •
                (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) S := by
            exact (ih (i :: w)).smul contDiffOn_const
          have hB : ContDiffOn ℝ (k : WithTop ℕ∞) B S := by
            apply ContDiffOn.sum
            intro i hi
            exact hBterm i
          have hpair : ContDiffOn ℝ (k : WithTop ℕ∞) (fun p => (A p, B p)) S :=
            hA.prodMk hB
          change ContDiffOn ℝ (k : WithTop ℕ∞)
            (fun p => (A p).coprod (B p)) S
          exact (ContinuousLinearMap.coprodEquivL (𝕜 := ℝ) (E := ℝ)
            (F := Vec 2) (G := ℝ) ℝ).contDiff.comp_contDiffOn hpair
        · intro p hp
          exact hderivative w p hp
  intro w
  rw [contDiffOn_infty]
  exact fun k => hfinite k w

end AVenhance.Infra.Classical

end
