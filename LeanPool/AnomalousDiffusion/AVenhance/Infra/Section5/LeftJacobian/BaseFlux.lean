/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.PiolaFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenHmTelescope

/-!: the candidate base flux `Σ_n A⁺_{n,0} q_{n,0}` and the order-zero
endpoint of the `H_m` telescope (the corrected-form analogue of `HmBaseFluxIdentity`). -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- One `(n, l)` term of the base flux: contracting `F_{ji} (F ∇T)_k` against `q_{jk}`
gives `(Fᵀ q F ∇T)_i`, the `j` of `F_{ji}` contracting with the row of `q`. -/
theorem base_term_contraction (L ξ : ℝ) (W q : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2)
    (i : Fin 2) :
    ∑ j : Fin 2, ∑ k : Fin 2,
      (-L * (ξ * (W j i * ∑ p : Fin 2, W k p * g p))) * q j k =
    -(ξ * L * (W.transpose.mulVec (q.mulVec (W.mulVec g))) i) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Fin.sum_univ_two]
  ring

theorem sum_comm_fin_fin_finset {α : Type*} (S : Finset α) (f : Fin 2 → Fin 2 → α → ℝ) :
    ∑ j : Fin 2, ∑ k : Fin 2, ∑ l ∈ S, f j k l = ∑ l ∈ S, ∑ j : Fin 2, ∑ k : Fin 2, f j k l := by
  calc ∑ j : Fin 2, ∑ k : Fin 2, ∑ l ∈ S, f j k l
      = ∑ j : Fin 2, ∑ l ∈ S, ∑ k : Fin 2, f j k l :=
        Finset.sum_congr rfl (fun j _ => Finset.sum_comm)
    _ = _ := Finset.sum_comm

theorem amnrBasePlus_qMNR_sum (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    (fun i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
      amnrBasePlus I hΦ m κm n T t x i j k * I.qMNR κm m n 0 t j k) =
    -(∑' l : ℤ, I.hatXiML m l t •
      ((I.flowGrad hΦ m l t x).transpose.mulVec
        ((I.Jhat κm m t - I.Kmat κm m t).mulVec
          ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))) := by
  funext i
  set S := (I.hatXiML_support_finite hm t).toFinset with hS
  have hflow : ∀ j k : Fin 2, (∑' l : ℤ, I.hatXiML m l t *
      (I.flowGrad hΦ m l t x j i * ∑ p : Fin 2, I.flowGrad hΦ m l t x k p * spaceGrad (T t) x p)) =
      ∑ l ∈ S, I.hatXiML m l t *
      (I.flowGrad hΦ m l t x j i * ∑ p : Fin 2, I.flowGrad hΦ m l t x k p * spaceGrad (T t) x p)
          := by
    intro j k
    exact tsum_hatXiML_smul_eq_sum I m hm t (α := ℝ) _
  have hrhs := tsum_hatXiML_smul_eq_sum I m hm t (α := Vec 2) (fun l =>
    (I.flowGrad hΦ m l t x).transpose.mulVec
        ((I.Jhat κm m t - I.Kmat κm m t).mulVec
          ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))
  rw [hrhs, Jhat_sub_Kmat_eq_LMN_qMNR_zero I m κm t]
  have hL : ∀ n : ℕ, ∑ j : Fin 2, ∑ k : Fin 2,
      amnrBasePlus I hΦ m κm n T t x i j k * I.qMNR κm m n 0 t j k =
      ∑ l ∈ S, -(I.hatXiML m l t * I.LMN κm m n t *
        ((I.flowGrad hΦ m l t x).transpose.mulVec
          ((I.qMNR κm m n 0 t).mulVec ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)))) i) :=
              by
    intro n
    simp only [amnrBasePlus]
    simp only [hflow]
    have hgen : ∀ (j k : Fin 2), (-I.LMN κm m n t * ∑ l ∈ S, I.hatXiML m l t *
        (I.flowGrad hΦ m l t x j i * ∑ p : Fin 2, I.flowGrad hΦ m l t x k p *
          spaceGrad (T t) x p)) * I.qMNR κm m n 0 t j k =
        ∑ l ∈ S, (-I.LMN κm m n t * (I.hatXiML m l t *
        (I.flowGrad hΦ m l t x j i * ∑ p : Fin 2, I.flowGrad hΦ m l t x k p *
          spaceGrad (T t) x p))) * I.qMNR κm m n 0 t j k := by
      intro j k
      rw [Finset.mul_sum, Finset.sum_mul]
    simp only [hgen]
    rw [sum_comm_fin_fin_finset]
    apply Finset.sum_congr rfl
    intro l _
    rw [← base_term_contraction (I.LMN κm m n t) (I.hatXiML m l t)
      (I.flowGrad hΦ m l t x) (I.qMNR κm m n 0 t) (spaceGrad (T t) x) i]
  simp only [hL]
  rw [Finset.sum_comm]
  simp only [Matrix.sum_mulVec, Matrix.smul_mulVec, Matrix.mulVec_sum, Matrix.mulVec_smul,
    Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem vecDiv_neg_eq {V : Vec 2 → Vec 2} (x : Vec 2) :
    vecDiv (fun y => -V y) x = -vecDiv V x := by
  simp [vecDiv, spaceGrad]

/-- The order-zero endpoint of the `H_m` telescope under the corrected-form base tensor
(the base, `Amnr_zero_eq_amnrBasePlus`): the negative divergence of
`Σ_l ξ̂_l F_lᵀ (JHat - K) F_l ∇T`. -/
theorem variantA_hmEndpoint_zero (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    hmEndpoint I hΦ m κm T 0 t x =
      -vecDiv (fun y => ∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t y).transpose.mulVec
          ((I.Jhat κm m t - I.Kmat κm m t).mulVec
            ((I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y))))) x := by
  unfold hmEndpoint
  simp only [Amnr_zero_eq_amnrBasePlus]
  rw [← vecDiv_neg_eq]
  congr 1
  funext y
  exact amnrBasePlus_qMNR_sum I hΦ m hm κm T t y

end AVenhance.Infra.Section5.LeftJacobian

end
