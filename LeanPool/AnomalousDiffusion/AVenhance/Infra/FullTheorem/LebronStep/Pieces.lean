/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzL2
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.HMinusMeasurable
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsClassicalSol

/-! # `L²` bookkeeping for Lemma r.LeBron

Triangle inequalities for continuous slices and slice continuity of classical solutions. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem

open AVenhance

/-- Triangle inequality for a difference of continuous functions. -/
theorem sqrt_l2NormSq_sub_le {f g : Vec 2 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    Real.sqrt (l2NormSq (fun x => f x - g x)) ≤ Real.sqrt (l2NormSq f) + Real.sqrt (l2NormSq g) :=
        by
  have h := Infra.Section5.Integration.sqrt_l2NormSq_add_le_of_continuous (f := f) (g := fun x =>
      -g x) hf hg.neg
  have e : l2NormSq (fun x => -g x) = l2NormSq g := by simp [l2NormSq]
  rw [e] at h
  simpa [sub_eq_add_neg] using h

/-- Time slices of a classical solution are continuous (at times `t ≥ 0`). -/
theorem IsClassicalSol.continuous_slice {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ}
    (h : IsClassicalSol b κ F θ₀ θ) {t : ℝ} (ht : 0 ≤ t) : Continuous (θ t) := by
  have hc := h.1.continuousOn
  refine continuousOn_univ.mp ?_
  have hmap : Continuous (fun x : Vec 2 => (t, x)) := continuous_const.prodMk continuous_id
  exact hc.comp hmap.continuousOn (fun x _ => ⟨ht, Set.mem_univ x⟩)

/-- The sup and the `1/4`-Hölder bounds of the difference `θm - θprev` from the pieces. -/
theorem difference_bounds {θm θprev : ℝ → Vec 2 → ℝ}
    (hcm : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (θm t))
    (hcp : ∀ t ∈ Set.Icc (0 : ℝ) 1, Continuous (θprev t)) {A Sm Sp : ℝ}
    (hsup : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θprev t x)) ≤ A)
    (hm : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θm t x - θm s x)) ≤ Sm * |t - s| ^ ((1 : ℝ) / 4))
    (hp : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => θprev t x - θprev s x)) ≤ Sp * |t - s| ^ ((1 : ℝ) / 4))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Real.sqrt (l2NormSq (fun x => (θm t x - θprev t x) - (θm s x - θprev s x))) ≤ 2 * A ∧
    Real.sqrt (l2NormSq (fun x => (θm t x - θprev t x) - (θm s x - θprev s x))) ≤
      (Sm + Sp) * |t - s| ^ ((1 : ℝ) / 4) := by
  constructor
  · have h := sqrt_l2NormSq_sub_le (f := fun x => θm t x - θprev t x)
      (g := fun x => θm s x - θprev s x) ((hcm t ht).sub (hcp t ht)) ((hcm s hs).sub (hcp s hs))
    have h1 := hsup t ht
    have h2 := hsup s hs
    linarith
  · have e : (fun x => (θm t x - θprev t x) - (θm s x - θprev s x)) =
        fun x => (θm t x - θm s x) - (θprev t x - θprev s x) := by
      funext x; ring
    rw [e]
    have h := sqrt_l2NormSq_sub_le (f := fun x => θm t x - θm s x)
      (g := fun x => θprev t x - θprev s x) ((hcm t ht).sub (hcm s hs)) ((hcp t ht).sub (hcp s hs))
    have h1 := hm s hs t ht
    have h2 := hp s hs t ht
    linarith

end AVenhance.Infra.FullTheorem
