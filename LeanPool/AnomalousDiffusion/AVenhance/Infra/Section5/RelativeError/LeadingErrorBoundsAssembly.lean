/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsError
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorBoundsL2Ioi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.LeadingErrorAlgebraContinuity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordDiffusion

/-! # `L²_{t,x}` bound for the leading-gradient error in terms of the temperature norms

Given the pointwise bound `ansatz_error_component_le`, the continuity of the gradient norms of
`T`, `∂_p T` and `HTilde_m` on `[0,∞) × ℝ²` and the scalar `L²` triangle inequality, this module
    proves

`‖∇θTilde_m - F∇T‖_{L²} ≤ 2 (P ‖∇T‖ + Q (‖∇∂₀T‖ + ‖∇∂₁T‖) + ‖∇HTilde_m‖)`

with `P = 20 e c + ε_m c · 16 (2^16 ε_{m-1}⁻¹)`, `Q = 4 ε_m c`, `e = ε_{m-1}^{2δ}`,
`c = a_m ε_m²/κ_m`. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff

noncomputable section

namespace AVenhance.Infra.Section5.RelativeError

open AVenhance AVenhance.Infra.Section5

/-- Joint continuity of `∇_x F` on `(0,∞) × ℝ²` for `F` of class `C²` there. -/
theorem continuousOn_spaceGrad_of_contDiffOn_two {F : ℝ → Vec 2 → ℝ}
    (hF : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => F p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (i : Fin 2) :
    ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (F p.1) p.2 i)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := by
  have hs : UniqueDiffOn ℝ (Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set (Vec 2))) :=
    UniqueDiffOn.prod (uniqueDiffOn_Ioi 0) uniqueDiffOn_univ
  have h : ContinuousOn (fun r : ℝ × Vec 2 =>
      fderivWithin ℝ (fun q : ℝ × Vec 2 => F q.1 q.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) r
        (0, basisVec i)) (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    (hF.continuousOn_fderivWithin hs (by norm_num)).clm_apply continuousOn_const
  refine h.congr ?_
  rintro ⟨t, x⟩ ⟨ht, -⟩
  exact Integration.spaceGrad_slice_eq (F := fun q : ℝ × Vec 2 => F q.1 q.2)
    (s := Set.Ioi (0 : ℝ) ×ˢ Set.univ) t x (fun y => ⟨ht, trivial⟩)
    (hF.differentiableOn (by norm_num) (t, x) ⟨ht, trivial⟩) i

variable {β : ℝ} {I : Ingredients β} {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- The `L²_{t,x}` bound for the leading-gradient error in terms of the temperature norms. -/
theorem sqrt_leadingErr_le (hΦ : IsStreamSeq I Φ) {m : ℕ} (hm : 2 ≤ m) {κm : ℝ} (hκ : 0 < κm)
    {T : ℝ → Vec 2 → ℝ}
    (hT : ContDiffOn ℝ ∞ (fun p : ℝ × Vec 2 => T p.1 p.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTs : ∀ t, 0 < t → ContDiff ℝ ∞ (T t))
    (hH2 : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.Hm hΦ m κm T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hHs : ∀ t, 0 < t → ContDiff ℝ ∞ (I.Hm hΦ m κm T t)) :
    Real.sqrt (spaceTimeGradNormSq (fun s x =>
        spaceGrad (I.ansatz hΦ m κm T s) x - LeftToShow.leadingGrad I hΦ m κm T s x)) ≤
      2 * ((20 * epsilon β I.Λ (m - 1) ^ (2 * delta β) *
              (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) +
            epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm) *
              (16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹))) *
            Real.sqrt (spaceTimeGradNormSq (fun s x => spaceGrad (T s) x)) +
          (4 * epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
            Real.sqrt (spaceTimeGradNormSq
              (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [0] (T s)))) +
          (4 * epsilon β I.Λ m * (a β I.Λ m * epsilon β I.Λ m ^ 2 / κm)) *
            Real.sqrt (spaceTimeGradNormSq
              (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [1] (T s)))) +
          Real.sqrt (spaceTimeGradNormSq (fun s x =>
            spaceGrad (I.Hm hΦ m κm T s) x))) := by
  set c : ℝ := a β I.Λ m * epsilon β I.Λ m ^ 2 / κm with hc
  set e : ℝ := epsilon β I.Λ (m - 1) ^ (2 * delta β) with he
  set em : ℝ := epsilon β I.Λ m with hem
  have hc0 : 0 ≤ c := by
    have := a_nonneg' I m
    positivity
  have he0 : 0 ≤ e := (Real.rpow_pos_of_pos (epsilon_pos' I _) _).le
  have hem0 : 0 ≤ em := (epsilon_pos' I m).le
  set P : ℝ := 20 * e * c + em * c * (16 * (2 ^ 16 * (epsilon β I.Λ (m - 1))⁻¹)) with hP
  set Q : ℝ := 4 * em * c with hQ
  have hP0 : 0 ≤ P := by
    have := (epsilon_pos' I (m - 1)).le
    positivity
  have hQ0 : 0 ≤ Q := by positivity
  -- continuity of the gradient-norm functions (`∇HTilde_m` only on the open half space)
  have cT : ContinuousOn (fun p : ℝ × Vec 2 => Real.sqrt (vecNormSq (spaceGrad (T p.1) p.2)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_sqrt_vecNormSq fun i => continuousOn_spaceGrad_joint hT i
  have cW (q : Fin 2) : ContinuousOn (fun p : ℝ × Vec 2 =>
      Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [q] (T p.1)) p.2)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    continuousOn_sqrt_vecNormSq fun i => continuousOn_spaceHess_joint hT i q
  have cH : ∀ i, ContinuousOn (fun p : ℝ × Vec 2 => spaceGrad (I.Hm hΦ m κm T p.1) p.2 i)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) := continuousOn_spaceGrad_of_contDiffOn_two hH2
  -- the dominating function for the remainder fields (everything but `∇HTilde_m`)
  have hcont : ContinuousOn (fun p : ℝ × Vec 2 =>
      P * Real.sqrt (vecNormSq (spaceGrad (T p.1) p.2)) +
      Q * Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T p.1)) p.2)) +
      Q * Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T p.1)) p.2)))
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) :=
    ((continuousOn_const.mul cT).add (continuousOn_const.mul (cW 0))).add
      (continuousOn_const.mul (cW 1))
  have hdom := sqrt_spaceTimeGradNormSq_le_of_sub_component_le
    (F := fun s x => spaceGrad (I.ansatz hΦ m κm T s) x - LeftToShow.leadingGrad I hΦ m κm T s x)
    (G := fun s x => spaceGrad (I.Hm hΦ m κm T s) x)
    (B := fun p => P * Real.sqrt (vecNormSq (spaceGrad (T p.1) p.2)) +
      Q * Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T p.1)) p.2)) +
      Q * Real.sqrt (vecNormSq (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T p.1)) p.2)))
    hcont cH ?_
  · have hsum := sqrt_setIntegral_sq_three_le (c₁ := P) (c₂ := Q) (c₃ := Q) hP0 hQ0 hQ0
      (f₁ := fun p : ℝ × Vec 2 => Real.sqrt (vecNormSq (spaceGrad (T p.1) p.2)))
      (f₂ := fun p : ℝ × Vec 2 => Real.sqrt (vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [0] (T p.1)) p.2)))
      (f₃ := fun p : ℝ × Vec 2 => Real.sqrt (vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [1] (T p.1)) p.2)))
      cT (cW 0) (cW 1)
    rw [integral_sqrt_vecNormSq_sq (fun s x => spaceGrad (T s) x),
      integral_sqrt_vecNormSq_sq (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [0] (T s))),
      integral_sqrt_vecNormSq_sq (fun s => spaceGrad (Infra.Section4.iterateSpatialWord [1] (T s)))]
      at hsum
    refine hdom.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    linarith
  · intro t ht x i
    have hTt := hTs t ht.1
    have hHt := ((hHs t ht.1).differentiable (by simp)) x
    have hg : ∀ p, |spaceGrad (T t) x p| ≤ Real.sqrt (vecNormSq (spaceGrad (T t) x)) :=
      fun p => abs_apply_le_sqrt_vecNormSq _ p
    have hh : ∀ i p, |spaceHess (T t) x i p| ≤ Real.sqrt (vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x)) :=
      fun i p => abs_apply_le_sqrt_vecNormSq
        (spaceGrad (Infra.Section4.iterateSpatialWord [p] (T t)) x) i
    have key := ansatz_error_sub_Hm_component_le hΦ hm hκ hTt x hHt hg hh i
    refine key.trans_eq ?_
    simp only [hP, hQ, hc, he, hem]
    ring

end AVenhance.Infra.Section5.RelativeError
