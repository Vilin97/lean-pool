/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Form

/-! # Representation

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

/-- Finite window representation, valid for either polynomial specialization. -/
theorem coarseCoeffWindow_eq_sum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
    (hm : 1 ≤ m) (κ a b t : ℝ) (x : Vec 2) :
    coarseCoeffWindow I hΦ m κ a b t x =
      ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset,
        I.hatXiML m l t • coarseCoeffPolynomial a b κ
          (I.Kmat κ m t) (I.flowGrad hΦ m l t x) := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  have ht (g : ℤ → CoarseMatrix) :
      (∑' l : ℤ, I.hatXiML m l t • g l) = ∑ l ∈ S, I.hatXiML m l t • g l := by
    apply tsum_eq_sum
    intro l hl
    have hz : I.hatXiML m l t = 0 := by
      by_contra hn
      exact hl ((Set.Finite.mem_toFinset _).mpr hn)
    rw [hz, zero_smul]
  rw [coarseCoeffWindow, ht, ht]
  simp only [coarseCoeffPolynomial, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, Finset.mul_sum, Matrix.mul_smul, smul_smul]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro l _ <;> rw [mul_comm]

/-- A single tsum of a matrix polynomial: the structural form from the plan. -/
theorem coarseCoeffWindow_eq_tsum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) {m : ℕ}
    (hm : 1 ≤ m) (κ a b t : ℝ) (x : Vec 2) :
    coarseCoeffWindow I hΦ m κ a b t x =
      ∑' l : ℤ, I.hatXiML m l t • coarseCoeffPolynomial a b κ
        (I.Kmat κ m t) (I.flowGrad hΦ m l t x) := by
  rw [coarseCoeffWindow_eq_sum I hΦ hm]
  symm
  apply tsum_eq_sum
  intro l hl
  have hz : I.hatXiML m l t = 0 := by
    by_contra hn
    exact hl ((Set.Finite.mem_toFinset _).mpr hn)
  rw [hz, zero_smul]

theorem CoarseCoeffForm.periodic {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ} {m : ℕ} {κ : ℝ}
    {s : ℝ → Vec 2 → CoarseMatrix} (hs : CoarseCoeffForm I hΦ m κ s)
    (t : ℝ) (hp : ∀ l, IsZ2Periodic (I.flowGrad hΦ m l t)) :
    IsZ2Periodic (s t) := by
  obtain ⟨a, b, _, _, he⟩ := hs.window_form
  intro k x
  rw [he, he]
  unfold coarseCoeffWindow
  have hF : ∀ l, I.flowGrad hΦ m l t (x + latticeShift k) = I.flowGrad hΦ m l t x :=
    fun l => hp l k x
  have hlin : (∑' l : ℤ, I.hatXiML m l t • (I.flowGrad hΦ m l t (x + latticeShift k) - 1)) =
      ∑' l : ℤ, I.hatXiML m l t • (I.flowGrad hΦ m l t x - 1) :=
    tsum_congr fun l => by rw [hF l]
  have hquad : (∑' l : ℤ, I.hatXiML m l t •
      (((I.flowGrad hΦ m l t (x + latticeShift k)).transpose - 1) *
        (I.Kmat κ m t - κ • (1 : CoarseMatrix)) * I.flowGrad hΦ m l t (x + latticeShift k))) =
      ∑' l : ℤ, I.hatXiML m l t •
      (((I.flowGrad hΦ m l t x).transpose - 1) *
        (I.Kmat κ m t - κ • (1 : CoarseMatrix)) * I.flowGrad hΦ m l t x) :=
    tsum_congr fun l => by rw [hF l]
  rw [hlin, hquad]

end AVenhance.Infra.Section4
