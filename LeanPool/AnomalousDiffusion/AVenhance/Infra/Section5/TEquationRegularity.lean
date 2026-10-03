/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Regularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.ClassicalRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.FlowGradientRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.TEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.LocalFinite
public import Mathlib.Analysis.Matrix.Normed

/-! Discharge the pointwise spatial differentiability inputs to the
last-iterate transport equation. -/

@[expose] public section

open Homogenization
open scoped ContDiff Matrix.Norms.Elementwise

noncomputable section

namespace AVenhance.Infra.Section5

open AVenhance

variable {β : ℝ} (I : Ingredients β) {Φ : ℕ → ℝ → Vec 2 → ℝ}

theorem TEquationRegularity.sMat_spatial_contDiff_one
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm : ℝ) (t : ℝ) :
    ContDiff ℝ 1 (fun x => I.sMat hΦ m κm t x) := by
  exact (Infra.Section4.sMat_coarseCoeffForm I hΦ m κm).spatial_contDiff hm t
    (fun l => flowGrad_spatial_contDiff_one I hΦ m l t)

/-- The final iterate equation with its spatial differentiability
inputs derived from the classical iterate hypotheses and cutoff support. -/
theorem final_iterate_transport_eq_of_classical
    (hΦ : IsStreamSeq I Φ) (m : ℕ) (hm : 1 ≤ m) (κm κprev : ℝ)
    (θ₀ : Vec 2 → ℝ) (θprev : ℝ → Vec 2 → ℝ)
    (T : ℕ → ℝ → Vec 2 → ℝ)
    (hT : Ingredients.IsTIterates I hΦ m κm κprev θ₀ θprev T)
    {t : ℝ} {x : Vec 2} (ht : 0 < t) :
    deriv (fun s => T (Nstar β) s x) t +
      vecDot (streamVel (Φ (m - 1)) t x)
        (spaceGrad (T (Nstar β) t) x) =
      vecDiv (fun y =>
        (I.Kmat κm m t + I.sMat hΦ m κm t y).mulVec
          (spaceGrad (T (Nstar β) t) y) +
        iterateError I hΦ m κm κprev T t y) x := by
  have hN1 : 1 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  have hN2 : 2 ≤ Nstar β := by
    have h := AVenhance.Infra.Ingredients.Nstar_ge_256 I.one_lt_beta I.beta_lt
    omega
  rcases hT with ⟨hzero, hstep⟩
  have hprevClass : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev (T (Nstar β - 2))) θ₀
      (T (Nstar β - 1)) := by
    exact hstep (Nstar β - 1) (by omega) (by omega)
  have hlastClass : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev (T (Nstar β - 1))) θ₀
      (T (Nstar β)) := by
    exact hstep (Nstar β) hN1 le_rfl
  have hprevSmooth : ContDiff ℝ ∞ (T (Nstar β - 1) t) :=
    classicalSol_space_contDiff_of_nonneg hprevClass (le_of_lt ht)
  have hlastGrad : ContDiff ℝ ∞ (spaceGrad (T (Nstar β) t)) :=
    classicalSol_spaceGrad_contDiff_of_nonneg hlastClass (le_of_lt ht)
  have hsmat : ContDiff ℝ 1 (fun y => I.sMat hΦ m κm t y) :=
    TEquationRegularity.sMat_spatial_contDiff_one I hΦ m hm κm t
  let M : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ := fun y =>
    I.Kmat κm m t - κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) +
      I.sMat hΦ m κm t y
  have hM : ContDiff ℝ 1 M := by
    dsimp [M]
    exact (contDiff_const.sub contDiff_const).add hsmat
  have hMentry (i j : Fin 2) : ContDiff ℝ 1 (fun y => M y i j) :=
    contDiff_pi.1 (contDiff_pi.1 hM i) j
  have hprevGradSmooth : ContDiff ℝ ∞
      (spaceGrad (T (Nstar β - 1) t)) :=
    classicalSol_spaceGrad_contDiff_of_nonneg hprevClass (le_of_lt ht)
  have hprevGradEntry (j : Fin 2) :
      ContDiff ℝ 1 (fun y => spaceGrad (T (Nstar β - 1) t) y j) :=
    (contDiff_pi.1 hprevGradSmooth j).of_le (by norm_num)
  have hU (i : Fin 2) : ContDiff ℝ 1 (fun y =>
      (M y).mulVec (spaceGrad (T (Nstar β - 1) t) y) i) := by
    change ContDiff ℝ 1 (fun y =>
      ∑ j : Fin 2, M y i j * spaceGrad (T (Nstar β - 1) t) y j)
    apply ContDiff.sum
    intro j hj
    exact (hMentry i j).mul (hprevGradEntry j)
  have hA : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun y => (M y).mulVec (spaceGrad (T (Nstar β - 1) t) y) i) x := by
    intro i
    exact (hU i).differentiable (by norm_num) |>.differentiableAt
  have hgrad : ∀ i : Fin 2, DifferentiableAt ℝ
      (fun y => spaceGrad (T (Nstar β) t) y i) x := by
    intro i
    exact (contDiff_pi.1 hlastGrad i).differentiable (by norm_num) |>.differentiableAt
  exact final_iterate_transport_eq I hΦ m κm κprev θ₀ θprev T
    ⟨hzero, hstep⟩ hA hgrad ht

end AVenhance.Infra.Section5

end
