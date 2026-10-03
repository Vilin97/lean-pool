/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.Candidate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.HmBaseFluxIdentity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences

/-! LeftJacobian the left-Jacobian form: the Piola coefficient identity.

`K + s⁺ = Σ_l ξ̂_l [κ F_l + F_lᵀ (K - κ) F_l]` for a generic matrix `K` (no scalar
structure), and its action on `∇T`. -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- A `ξ̂`-weighted `tsum` is the finite sum over the support of `ξ̂`. -/
theorem tsum_hatXiML_smul_eq_sum {α : Type*} [AddCommMonoid α] [TopologicalSpace α]
    [Module ℝ α] (m : ℕ) (hm : 1 ≤ m) (t : ℝ) (f : ℤ → α) :
    ∑' l : ℤ, I.hatXiML m l t • f l =
      ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset, I.hatXiML m l t • f l := by
  apply tsum_eq_sum
  intro l hl
  have hz : I.hatXiML m l t = 0 := by
    by_contra hn
    exact hl ((I.hatXiML_support_finite hm t).mem_toFinset.mpr hn)
  simp [hz]

/-- The `ξ̂` weights sum to one over their finite support. -/
theorem sum_hatXiML_support (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ∑ l ∈ (I.hatXiML_support_finite hm t).toFinset, I.hatXiML m l t = 1 := by
  have h := tsum_hatXiML_smul_eq_sum I m hm t (fun _ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [← h]
  exact Infra.Ingredients.hatXiML_partition I hm t

/-- The matrix identity behind the Piola flux: `K + K(F - 1) + (Fᵀ - 1)(K - κ)F
= κF + Fᵀ(K - κ)F`. -/
theorem piola_matrix_identity (K F : Matrix (Fin 2) (Fin 2) ℝ) (κ : ℝ) :
    K + K * (F - 1) + (F.transpose - 1) * (K - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * F =
      κ • F + F.transpose * (K - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * F := by
  simp only [mul_sub, sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  abel

theorem Kmat_add_sMatPlus_eq_coarseFluxPlus (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm t : ℝ) (x : Vec 2) :
    I.Kmat κm m t + sMatPlus I hΦ m κm t x = coarseFluxPlus I hΦ m κm t x := by
  set S := (I.hatXiML_support_finite hm t).toFinset with hS
  have hw := sum_hatXiML_support I m hm t
  have h1 := tsum_hatXiML_smul_eq_sum I m hm t (fun l => I.flowGrad hΦ m l t x - 1)
  have h2 := tsum_hatXiML_smul_eq_sum I m hm t (fun l =>
    ((I.flowGrad hΦ m l t x).transpose - 1) *
        (I.Kmat κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * I.flowGrad hΦ m l t x)
  have h3 := tsum_hatXiML_smul_eq_sum I m hm t (fun l =>
    κm • I.flowGrad hΦ m l t x + (I.flowGrad hΦ m l t x).transpose *
        (I.Kmat κm m t - κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * I.flowGrad hΦ m l t x)
  unfold sMatPlus coarseFluxPlus
  rw [h1, h2, h3]
  have hK : I.Kmat κm m t = ∑ l ∈ S, I.hatXiML m l t • I.Kmat κm m t := by
    rw [← Finset.sum_smul, hw, one_smul]
  rw [show I.Kmat κm m t + (_ + _) = (∑ l ∈ S, I.hatXiML m l t • I.Kmat κm m t) + (_ + _) from by
      rw [← hK]]
  rw [Finset.mul_sum]
  simp only [Matrix.mul_smul]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← smul_add, ← smul_add]
  congr 1
  rw [← add_assoc]
  exact piola_matrix_identity _ _ _

theorem Kmat_add_sMatPlus_mulVec (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm t : ℝ) (x : Vec 2) (T : ℝ → Vec 2 → ℝ) :
    (I.Kmat κm m t + sMatPlus I hΦ m κm t x).mulVec (spaceGrad (T t) x) =
      ∑' l : ℤ, I.hatXiML m l t • ((κm • I.flowGrad hΦ m l t x +
        (I.flowGrad hΦ m l t x).transpose * (I.Kmat κm m t - κm • 1) *
          I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)) := by
  rw [Kmat_add_sMatPlus_eq_coarseFluxPlus I hΦ m hm κm t x, coarseFluxPlus,
    tsum_hatXiML_smul_eq_sum I m hm t, tsum_hatXiML_smul_eq_sum I m hm t,
    Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec]

end AVenhance.Infra.Section5.LeftJacobian

end
