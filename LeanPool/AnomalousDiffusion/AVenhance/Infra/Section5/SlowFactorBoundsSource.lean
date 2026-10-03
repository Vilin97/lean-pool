/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.SlowFactorBoundsComposition
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.GradientChain
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FrozenFlowRegularity

/-! Identification of the four slow-factor estimates with the actual selected
flow and the derivative-row matrix convention. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open MeasureTheory Homogenization AVenhance AVenhance.FaaDiBruno
open AVenhance.Infra.Section4 AVenhance.Infra.Ergodic AVenhance.Infra.Torus
namespace AVenhance.Infra.Section5

theorem slowFactorG_eq_mulVec (B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : Vec 2 → ℝ) (j : Fin 2) :
    slowFactorG B T j = fun x => (B x).mulVec (spaceGrad T x) j := by
  funext x
  simp only [slowFactorG, Finset.sum_apply, Pi.mul_apply, Matrix.mulVec, dotProduct]
  rfl

theorem slowFactorDiv_eq_vecDiv (B : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (T : Vec 2 → ℝ) :
    slowFactorDiv B T = vecDiv (fun x => (B x).mulVec (spaceGrad T x)) := by
  funext x
  unfold slowFactorDiv vecDiv
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [slowFactorG_eq_mulVec]
  rfl

theorem slowFactorGradDiv_eq_gradDiv (B : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (T : ℝ → Vec 2 → ℝ) (t : ℝ) (i : Fin 2) :
    slowFactorGradDiv (B t) (T t) i =
      fun x => gradDiv (fun s y => (B s y).mulVec (spaceGrad (T s) y)) t x i := by
  unfold slowFactorGradDiv
  rw [slowFactorDiv_eq_vecDiv]
  rfl

theorem SlowFactorBoundsSource.slowFactor_xFlow_right_inverse {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (l : ℤ) (t : ℝ) (x : Vec 2) :
    I.xFlow hΦ m l t (I.xFlowInv hΦ m l t x) = x := by
  let b := streamVel (Φ (m - 1))
  let F := flow b (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  have hF : IsFlow b F := flow_isFlow b
    (hΦ.adm_pred m).vel_continuous (hΦ.adm_pred m).vel_lipschitz
  let s := (l : ℝ) * tauPP β I.Λ m
  change F t (F s x t) s = x
  rw [Infra.Flow.flow_group_law b (hΦ.adm_pred m).vel_lipschitz hF x t s t]
  exact hF.1 x t

/-- Exact pullback-gradient identity for the selected flow, proved rather
than included as an analytic premise. -/
theorem slowFactorG_eq_actual_G {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (T : ℝ → Vec 2 → ℝ) (l : ℤ) (t : ℝ)
    (hT : ContDiff ℝ ∞ (T t)) (j : Fin 2) :
    slowFactorG (I.flowGrad hΦ m l t) (T t) j = fun x => G I hΦ m T l t x j := by
  rw [slowFactorG_eq_mulVec]
  funext x
  have hh := G_eq_flowGrad_mulVec I hΦ m T l t x
    ((hT.differentiable (by simp) x).hasFDerivAt)
    (((xFlow_spatial_contDiff_two I hΦ m l t).differentiable (by norm_num) _).hasFDerivAt)
    (SlowFactorBoundsSource.slowFactor_xFlow_right_inverse I hΦ m l t x)
  exact (congrFun hh j).symm

theorem slowFactorH_eq_actual_gradG {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)
    (T : ℝ → Vec 2 → ℝ) (l : ℤ) (t : ℝ)
    (hT : ContDiff ℝ ∞ (T t)) (i j : Fin 2) :
    slowFactorH (I.flowGrad hΦ m l t) (T t) i j = fun x => gradG I hΦ m T l t x i j := by
  unfold slowFactorH
  rw [slowFactorG_eq_actual_G I hΦ m T l t hT j]
  rfl

/-- e.fg.choice.1 with the actual l_k, including the K+s coefficient. -/
def section5SlowChoice1 {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) (t : ℝ) (j : Fin 2) (x : Vec 2) : ℝ :=
  I.xiMK m k t * ((flowGradK I hΦ m k t x).mulVec
    (gradDiv (fun s y => (I.Kmat κ m s + I.sMat hΦ m κ s y).mulVec
      (spaceGrad (T s) y)) t x)) j

/-- Cutoff-weighted Hessian slow factor for the Section 5 temperature estimate. -/
def section5SlowChoice2 {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) (t : ℝ) (a j : Fin 2) (x : Vec 2) : ℝ :=
  I.xiMK m k t * κ * ∑ i : Fin 2,
    (gradMatrix (I.xFlowInv hΦ m (lIdx β I.Λ m k) t) x - 1) i a *
      gradG I hΦ m T (lIdx β I.Λ m k) t x i j

/-- Choice 3 uses the transpose required by the push-forward convention. -/
def section5SlowChoice3 {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) (t : ℝ) (a j : Fin 2) (x : Vec 2) : ℝ :=
  I.xiMK m k t * ∑ i : Fin 2,
    (1 - (flowGradK I hΦ m k t x).transpose) i a *
      gradG I hΦ m T (lIdx β I.Λ m k) t x i j

theorem section5SlowChoice1_eq {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ)
    (k : ℤ) (t : ℝ) (j : Fin 2) :
    section5SlowChoice1 I hΦ m κ T k t j =
      slowFactorChoice1 (I.xiMK m k t) (I.flowGrad hΦ m (lIdx β I.Λ m k) t)
        (fun x => I.Kmat κ m t + I.sMat hΦ m κ t x) (T t) j := by
  unfold section5SlowChoice1 slowFactorChoice1 flowGradK
  have he (i : Fin 2) := slowFactorGradDiv_eq_gradDiv
    (fun s y => I.Kmat κ m s + I.sMat hΦ m κ s y) T t i
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.mul_apply, he,
    Matrix.mulVec, dotProduct]

end AVenhance.Infra.Section5
