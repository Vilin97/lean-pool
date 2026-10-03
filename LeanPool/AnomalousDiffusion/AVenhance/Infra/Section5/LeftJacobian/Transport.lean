/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.BaseFlux
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.LeftJacobian.HatXiWindow
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.OddSupportTsum
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.MovingFluxEnergy

/-! LeftJacobian the left-Jacobian form: the coarse transport flux `V_tr` (LeftJacobian-variantA
    (34)), its
decomposition against `K + s⁺` and the base flux, and the exact transition dichotomy
(LeftJacobian-variantA (35)). -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.LeftJacobian

open AVenhance AVenhance.Infra.Section5

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

/-- Per-window vector identity: adding the `Fᵀ(JHat-K)F g` correction to `(κF + Fᵀ(K-κ)F) g`
trades `K` for `𝒥` (flux) at the price of `Fᵀ(JHat - 𝒥)F g`. -/
theorem transport_window_identity (κ : ℝ) (K J C F : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2) :
    (κ • F + F.transpose * (K - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * F).mulVec g +
      F.transpose.mulVec ((J - K).mulVec (F.mulVec g)) =
    (κ • F + F.transpose * (C - κ • (1 : Matrix (Fin 2) (Fin 2) ℝ)) * F).mulVec g +
      F.transpose.mulVec ((J - C).mulVec (F.mulVec g)) := by
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.mul_sub, Matrix.sub_mul,
    ← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
  abel

/-- LeftJacobian-variantA (34)–(35), pointwise: `(K + s⁺)∇T + Σ_l ξ̂_l Fᵀ(JHat - K)F∇T` equals
`V_tr` plus the first summand of `d⁺` (`sourceErrorDPlus`). Composes with
`Kmat_add_sMatPlus_mulVec` and `amnrBasePlus_qMNR_sum`. -/
theorem transport_decomposition (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    (I.Kmat κm m t + sMatPlus I hΦ m κm t x).mulVec (spaceGrad (T t) x) +
      ∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).transpose.mulVec
          ((I.Jhat κm m t - I.Kmat κm m t).mulVec
            ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)))) =
    transportFluxPlus I hΦ m κm T t x +
      ∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).transpose.mulVec
          ((I.Jhat κm m t - I.flux κm m t).mulVec
            ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x)))) := by
  rw [Kmat_add_sMatPlus_mulVec I hΦ m hm κm t x T, transportFluxPlus]
  simp only [tsum_hatXiML_smul_eq_sum I m hm t]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  rw [← smul_add, ← smul_add, transport_window_identity κm (I.Kmat κm m t)
    (I.Jhat κm m t) (I.flux κm m t)]

/-- `sourceErrorDPlus` is its first (transport-correction) summand plus the terminal
`A_{Jcut} q_{Jcut}` tail. -/
theorem sourceErrorDPlus_eq (hΦ : IsStreamSeq I Φ) (m : ℕ) (κm : ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (x : Vec 2) :
    sourceErrorDPlus I hΦ m κm T t x =
      (∑' l : ℤ, I.hatXiML m l t •
        ((I.flowGrad hΦ m l t x).transpose.mulVec
          ((I.Jhat κm m t - I.flux κm m t).mulVec
            ((I.flowGrad hΦ m l t x).mulVec (spaceGrad (T t) x))))) +
      (fun i => ∑ n ∈ Finset.range (Nstar β), ∑ j : Fin 2, ∑ k : Fin 2,
        I.Amnr hΦ m κm n T (Jcut β) t x i j k *
          I.qMNR κm m n (Jcut β) t j k) := rfl

/-- The odd transition weights sum to one over their finite support. -/
theorem sum_xiMK_odd_support (m : ℕ) (hm : 1 ≤ m) (t : ℝ) :
    ∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
      I.xiMK m q.1 t = 1 := by
  have h := xiMK_odd_tsum_eq_subtype_support_sum I m hm t (fun _ => (1 : ℝ))
  simp only [smul_eq_mul, mul_one] at h
  rw [← h]
  exact AVenhance.Infra.Section3.xiMK_odd_partition I hm t

theorem Transport.xFlowInv_right_inverse_at' (hΦ : IsStreamSeq I Φ) (m : ℕ) (l : ℤ)
    (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x := by
  let b := streamVel (Φ (m - 1))
  let F := flow b (hΦ.adm_pred m).vel_continuous
    (hΦ.adm_pred m).vel_lipschitz
  have hF : IsFlow b F := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change F t (F s x t) s = x
  calc
    F t (F s x t) s = F t x t :=
      Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t
    _ = x := hF.1 x t

/-- `G_l = F_l ∇T` for `T t` of class `C¹`. -/
theorem G_eq_flowGrad_mulVec_of_contDiff (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ 1 (T t)) (l : ℤ) (y : Vec 2) :
    G I hΦ m T l t y = (I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y) :=
  G_eq_flowGrad_mulVec I hΦ m T l t y
    (hT.differentiable (by norm_num) y).hasFDerivAt
    ((xFlow_spatial_contDiff_two I hΦ m l t).differentiable
      (by norm_num) (I.xFlowInv hΦ m l t y)).hasFDerivAt
    (Transport.xFlowInv_right_inverse_at' I hΦ m l t y)

/-- `(κ F + Fᵀ P F) g = (κ I + Fᵀ P)(F g)`. -/
theorem piola_form_mulVec (κ : ℝ) (P F : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2) :
    (κ • F + F.transpose * P * F).mulVec g =
      (κ • (1 : Matrix (Fin 2) (Fin 2) ℝ) + F.transpose * P).mulVec (F.mulVec g) := by
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec]

theorem transportFluxPlus_eq_selected (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m)
    (κm : ℝ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (hT : ContDiff ℝ 1 (T t)) (y : Vec 2) :
    transportFluxPlus I hΦ m κm T t y =
      (∑ q ∈ (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset,
        I.xiMK m q.1 t • ((κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (flowGradK I hΦ m q.1 t y).transpose * (I.flux κm m t - κm • 1)).mulVec
            (G I hΦ m T (lIdx β I.Λ m q.1) t y))) +
      r46Flux I hΦ m κm T t y := by
  classical
  set P : Matrix (Fin 2) (Fin 2) ℝ := I.flux κm m t - κm • 1 with hP
  set U := (AVenhance.Infra.Section3.xiMK_odd_support_finite I hm t).toFinset with hU
  have hterm : ∀ l : ℤ, ((κm • I.flowGrad hΦ m l t y + (I.flowGrad hΦ m l t y).transpose * P *
      I.flowGrad hΦ m l t y).mulVec (spaceGrad (T t) y)) =
      (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) + (I.flowGrad hΦ m l t y).transpose * P).mulVec
        (G I hΦ m T l t y) := by
    intro l
    rw [piola_form_mulVec, G_eq_flowGrad_mulVec_of_contDiff I hΦ m T t hT l y]
  have hTr : transportFluxPlus I hΦ m κm T t y =
      ∑' l : ℤ, I.hatXiML m l t • ((κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (I.flowGrad hΦ m l t y).transpose * P).mulVec (G I hΦ m T l t y)) := by
    unfold transportFluxPlus
    exact tsum_congr (fun l => by rw [hterm l])
  by_cases hz : ∃ l : ℤ, I.hatZetaML m l t ≠ 0
  · obtain ⟨l, hl⟩ := hz
    have hone := hatXiML_eq_one_of_hatZeta_ne_zero I m hm l t hl
    have hzero : ∀ j : ℤ, j ≠ l → I.hatXiML m j t = 0 :=
      fun j hj => hatXiML_eq_zero_of_ne_refresh I m hm l j t hl hj
    rw [hTr, tsum_eq_single l (fun j hj => by rw [hzero j hj]; simp), hone, one_smul]
    have hr : r46Flux I hΦ m κm T t y = 0 :=
      congrFun (r46Flux_eq_zero_of_hatZeta_ne_zero I hΦ m hm κm T l t hl) y
    rw [hr, add_zero]
    have hsel : ∀ q ∈ U, I.xiMK m q.1 t • ((κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
        (flowGradK I hΦ m q.1 t y).transpose * P).mulVec
          (G I hΦ m T (lIdx β I.Λ m q.1) t y)) =
        I.xiMK m q.1 t • ((κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
          (I.flowGrad hΦ m l t y).transpose * P).mulVec (G I hΦ m T l t y)) := by
      intro q hq
      have hξ : I.xiMK m q.1 t ≠ 0 := (Set.Finite.mem_toFinset _).mp hq
      have hk := lIdx_eq_of_hatZeta_xiMK_ne_zero I m hm l q.1 t hl hξ
      simp only [flowGradK, hk]
    rw [Finset.sum_congr rfl hsel, ← Finset.sum_smul, sum_xiMK_odd_support I m hm t, one_smul]
  · replace hz : ∀ l : ℤ, I.hatZetaML m l t = 0 := fun l => not_not.mp (not_exists.mp hz l)
    have hflux : I.flux κm m t = κm • (1 : Matrix (Fin 2) (Fin 2) ℝ) :=
      flux_eq_kappa_of_hatZeta_zero I m hm κm t hz
    have hP0 : P = 0 := by rw [hP, hflux, sub_self]
    have hmul (v : Vec 2) : (κm • (1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec v = κm • v := by
      rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [hP0, Matrix.mul_zero, add_zero, hmul] at hTr ⊢
    have hr : r46Flux I hΦ m κm T t y = κm • (Gbar I hΦ m T t y -
        ∑ q ∈ U, I.xiMK m q.1 t • G I hΦ m T (lIdx β I.Λ m q.1) t y) := by
      unfold r46Flux
      rw [hflux, hmul,
        xiMK_odd_tsum_eq_subtype_support_sum I m hm t
          (fun q => Gbar I hΦ m T t y - G I hΦ m T (lIdx β I.Λ m q.1) t y)]
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
        sum_xiMK_odd_support I m hm t, one_smul]
      rfl
    rw [hr, hTr, tsum_hatXiML_smul_eq_sum I m hm t, Gbar_eq_finite_support I hΦ m hm T t y]
    simp only [smul_comm _ κm, ← Finset.smul_sum, smul_sub]
    abel

end AVenhance.Infra.Section5.LeftJacobian

end
