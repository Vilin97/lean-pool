/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.TIterateSmooth
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesDiffusion
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowGlobalJointSmoothness
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.Amnr.FlowSpatialPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Terms.R46FluxEstimate

/-! Regularity of the `R46` flux when its temperature is an actual T iterate.

At each fixed time the cutoff sums are finite.  The flow-pulled gradients are
smooth and periodic because the actual flow and inverse are jointly smooth and
lattice equivariant.
-/

@[expose] public section

noncomputable section
open Homogenization

namespace AVenhance.Infra.Section5

open AVenhance

theorem R46IteratesRegularity.r46_G_contDiff {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hflow : ContDiff ℝ (⊤ : ℕ∞) (I.xFlow hΦ m l t) :=
    (Infra.Section4.amnr_xFlow_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)))
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact hT.comp hflow
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f) :=
    Infra.Section4.iterate_gradient_smooth hf
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (I.xFlowInv hΦ m l t) :=
    (Infra.Section4.amnr_xFlowInv_joint_contDiff_infty I hΦ m l).comp
      (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)))
  change ContDiff ℝ (⊤ : ℕ∞) (spaceGrad f ∘ I.xFlowInv hΦ m l t)
  exact hgrad.comp hinv

theorem R46IteratesRegularity.r46_G_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (T : ℝ → Vec 2 → ℝ) (t : ℝ) (l : ℤ)
    (hT : IsZ2Periodic (T t)) (hTsmooth : ContDiff ℝ 1 (T t)) :
    IsZ2Periodic (G I hΦ m T l t) := by
  let f : Vec 2 → ℝ := fun y => T t (I.xFlow hΦ m l t y)
  have hflowper := Infra.Section4.amnr_xFlow_lattice_equivariant I hΦ m l t
  have hinvper := Infra.Section4.amnr_xFlowInv_lattice_equivariant I hΦ m l t
  have hfper : IsZ2Periodic f := by
    intro k x
    dsimp [f]
    rw [hflowper k x]
    exact hT k (I.xFlow hΦ m l t x)
  have hflow : ContDiff ℝ 1 (I.xFlow hΦ m l t) := by
    exact ((Infra.Section4.amnr_xFlow_joint_contDiff_infty I hΦ m l).of_le
      (by simp)).comp (by fun_prop : ContDiff ℝ 1 (fun x : Vec 2 => (t, x)))
  have hf : ContDiff ℝ 1 f := hTsmooth.comp hflow
  have hgradper := Infra.Section4.iterate_gradient_periodic hf hfper
  intro k x
  change spaceGrad f (I.xFlowInv hΦ m l t (x + latticeShift k)) =
    spaceGrad f (I.xFlowInv hΦ m l t x)
  rw [hinvper k x]
  exact hgradper k _

theorem R46IteratesRegularity.r46_flux_contDiff_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (hT : ContDiff ℝ (⊤ : ℕ∞) (T t)) :
    ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm T t) := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hG (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (G I hΦ m T l t) :=
    R46IteratesRegularity.r46_G_contDiff I hΦ m T t l hT
  have hbar : ContDiff ℝ (⊤ : ℕ∞) (Gbar I hΦ m T t) := by
    have heq : Gbar I hΦ m T t = fun x =>
        ∑ l ∈ S, I.hatXiML m l t • G I hΦ m T l t x := by
      funext x
      exact Gbar_eq_finite_support I hΦ m hm T t x
    rw [heq]
    apply ContDiff.sum
    intro l hl
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.hatXiML m l t)).smul (hG l)
  have hdefect (k : {k : ℤ // Odd k}) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) :=
    hbar.sub (hG _)
  let D : Vec 2 → Vec 2 := fun x =>
    ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x)
  have hDsum : D = fun x => ∑ k ∈ U, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    funext x
    apply tsum_eq_sum
    intro k hk
    have hξ : I.xiMK m k.1 t = 0 := by
      by_contra hξ
      exact hk ((Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hξ)
    simp [hξ]
  have hD : ContDiff ℝ (⊤ : ℕ∞) D := by
    rw [hDsum]
    apply ContDiff.sum
    intro k hk
    exact (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
      (fun _ : Vec 2 => I.xiMK m k.1 t)).smul (hdefect k)
  have hlin : ContDiff ℝ (⊤ : ℕ∞)
      (fun v : Vec 2 => (I.flux κm m t).mulVec v) := by
    apply contDiff_pi.2
    intro i
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun v : Vec 2 => ∑ j : Fin 2, I.flux κm m t i j * v j)
    apply ContDiff.sum
    intro j hj
    have hv : ContDiff ℝ (⊤ : ℕ∞) (fun v : Vec 2 => v j) := by fun_prop
    exact contDiff_const.mul hv
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => (I.flux κm m t).mulVec (D x))
  exact hlin.comp hD

theorem R46IteratesRegularity.r46_flux_periodic_of_slice {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (hm : 1 ≤ m) (κm : ℝ) (T : ℝ → Vec 2 → ℝ)
    (t : ℝ) (hT : IsZ2Periodic (T t)) (hTsmooth : ContDiff ℝ 1 (T t)) :
    IsZ2Periodic (r46Flux I hΦ m κm T t) := by
  classical
  let S := (I.hatXiML_support_finite hm t).toFinset
  let U := (Infra.Section3.xiMK_odd_support_finite I hm t).toFinset
  have hG (l : ℤ) : IsZ2Periodic (G I hΦ m T l t) :=
    R46IteratesRegularity.r46_G_periodic I hΦ m T t l hT hTsmooth
  have hbar : IsZ2Periodic (Gbar I hΦ m T t) := by
    intro k x
    have hL := Gbar_eq_finite_support I hΦ m hm T t x
    have hR := Gbar_eq_finite_support I hΦ m hm T t (x + latticeShift k)
    rw [hL, hR]
    apply Finset.sum_congr rfl
    intro l hl
    rw [hG l k x]
  let D : Vec 2 → Vec 2 := fun x =>
    ∑' k : {k : ℤ // Odd k}, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x)
  have hDsum (x : Vec 2) : D x = ∑ k ∈ U, I.xiMK m k.1 t •
      (Gbar I hΦ m T t x - G I hΦ m T (lIdx β I.Λ m k.1) t x) := by
    dsimp [D]
    apply tsum_eq_sum
    intro k hk
    have hξ : I.xiMK m k.1 t = 0 := by
      by_contra hξ
      exact hk ((Infra.Section3.xiMK_odd_support_finite I hm t).mem_toFinset.mpr hξ)
    simp [hξ]
  have hD : IsZ2Periodic D := by
    intro k x
    rw [hDsum (x + latticeShift k), hDsum x]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hbar k x, hG (lIdx β I.Λ m j.1) k x]
  intro k x
  change (I.flux κm m t).mulVec (D (x + latticeShift k)) =
    (I.flux κm m t).mulVec (D x)
  rw [hD k x]

/-- The `R46` flux of any actual iterate is smooth and periodic at positive
times.  The only iterate bound used is the finite cutoff index constraint. -/
theorem tIterate_r46Flux_regular {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) (κm : ℝ)
    {κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ}
    (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun _ _ => 0) θ₀ θprev)
    {i : ℕ} (hi : i ≤ Nstar β) {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (r46Flux I hΦ m κm (T i) t) ∧
      IsZ2Periodic (r46Flux I hΦ m κm (T i) t) := by
  have hs := Infra.Section4.tIterate_space_contDiff I hΦ hT hθ hi ht.le
  have hp := Infra.Section4.tIterate_periodic I hΦ hT hθ hi ht.le
  exact ⟨R46IteratesRegularity.r46_flux_contDiff_of_slice I hΦ m hm κm (T i) t hs,
    R46IteratesRegularity.r46_flux_periodic_of_slice I hΦ m hm κm (T i) t hp
      (hs.of_le (by simp))⟩

end AVenhance.Infra.Section5
end
