/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesBasic
public import Mathlib.Analysis.Matrix.Normed

/-! Linearity of the forcing, with an explicit regularity premise on
its actual coefficient. No quantitative V or T estimate is assumed. -/

@[expose] public section

noncomputable section
open Homogenization
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open AVenhance

theorem IteratesForcing.gradient_contDiff_one {f : Vec 2 → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (spaceGrad f) := by
  apply contDiff_pi.mpr
  intro i
  have h : ContDiff ℝ 1 (fun p : Vec 2 × Vec 2 => fderiv ℝ f p.1 p.2) :=
    hf.contDiff_fderiv_apply (by norm_num)
  have hm : ContDiff ℝ 1 (fun y : Vec 2 => (y, basisVec i)) := by fun_prop
  exact h.comp hm

theorem IteratesForcing.matrix_gradient_differentiable {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {f : Vec 2 → ℝ} (hA : ContDiff ℝ 1 A) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fun y => (A y).mulVec (spaceGrad f y)) := by
  have hg := IteratesForcing.gradient_contDiff_one hf
  have hc : ContDiff ℝ 1 (fun y => (A y).mulVec (spaceGrad f y)) := by
    apply contDiff_pi.mpr
    intro i
    unfold Matrix.mulVec dotProduct
    apply ContDiff.sum
    intro j _
    exact ((contDiff_pi.mp (contDiff_pi.mp hA i) j).mul (contDiff_pi.mp hg j))
  exact hc.differentiable (by norm_num)

/-- The divergence-form diffusion forcing is linear in its scalar argument. -/
theorem matrix_div_gradient_sub {A : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {f g : Vec 2 → ℝ} (hA : ContDiff ℝ 1 A)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Vec 2) :
    vecDiv (fun y => (A y).mulVec (spaceGrad (fun z => f z - g z) y)) x =
      vecDiv (fun y => (A y).mulVec (spaceGrad f y)) x -
        vecDiv (fun y => (A y).mulVec (spaceGrad g y)) x := by
  have hF := IteratesForcing.matrix_gradient_differentiable hA hf
  have hG := IteratesForcing.matrix_gradient_differentiable hA hg
  have heq : (fun y => (A y).mulVec (spaceGrad (fun z => f z - g z) y)) =
      fun y => (A y).mulVec (spaceGrad f y) - (A y).mulVec (spaceGrad g y) := by
    funext y i
    have hgrad : spaceGrad (fun z => f z - g z) y = spaceGrad f y - spaceGrad g y := by
      funext j
      exact Infra.Section3.spaceGrad_sub j (hf.differentiable (by norm_num) y)
        (hg.differentiable (by norm_num) y)
    rw [hgrad]
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [heq]
  unfold vecDiv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have heval : Differentiable ℝ (fun v : Vec 2 => v i) := differentiable_apply i
  exact Infra.Section3.spaceGrad_sub i (heval.differentiableAt.comp x (hF x))
    (heval.differentiableAt.comp x (hG x))

/-- Linearity for the actual TForcing. The coefficient regularity is
stated explicitly for subsequent discharge from the flow regularity data. -/
theorem TForcing_sub {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    (m : ℕ) (κm κprev : ℝ) {f g : ℝ → Vec 2 → ℝ} (t : ℝ)
    (hA : ContDiff ℝ 1 (fun y => I.Kmat κm m t -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y))
    (hf : ContDiff ℝ 2 (f t)) (hg : ContDiff ℝ 2 (g t)) (x : Vec 2) :
    I.TForcing hΦ m κm κprev (fun s y => f s y - g s y) t x =
      I.TForcing hΦ m κm κprev f t x - I.TForcing hΦ m κm κprev g t x :=
  matrix_div_gradient_sub hA hf hg x

/-- e.Vm-1.i for the actual iterates, including the first step.
The only extra structural input is C¹ regularity of the actual coefficient. -/
theorem increment_classical_forcing {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hA : ∀ t : ℝ, 0 < t → ContDiff ℝ 1 (fun y => I.Kmat κm m t -
      κprev • (1 : Matrix (Fin 2) (Fin 2) ℝ) + I.sMat hΦ m κm t y))
    (i : ℕ) (hi : i + 1 ≤ Nstar β) :
    IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev (iterateIncrement T i))
      (fun _ => 0) (iterateIncrement T (i + 1)) := by
  cases i with
  | zero =>
    simpa only [iterateIncrement_zero, hT.1] using first_increment_classical I hΦ hT hθ hi
  | succ i =>
    have hc := later_increment_classical I hΦ hT i (by omega)
    refine ⟨hc.1, hc.2.1, hc.2.2.1, ?_⟩
    intro t ht x
    have hs (r : ℕ) (hr : 1 ≤ r) (hrN : r ≤ Nstar β) : ContDiff ℝ 2 (T r t) := by
      have hu := hT.2 r hr hrN
      have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
      have hh := hu.1.comp_contDiff hm (fun y => ⟨ht.le, Set.mem_univ y⟩)
      exact hh.of_le (by simp)
    have hpde := hc.2.2.2 t ht x
    simp only [iterateIncrement_succ]
    rw [TForcing_sub I hΦ m κm κprev t (hA t ht)
        (hs (i + 1) (by omega) (by omega))]
    · simpa only [iterateIncrement_succ, Nat.add_assoc] using hpde
    · cases i with
      | zero =>
        rw [hT.1]
        have hm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (t, y)) := by fun_prop
        exact (hθ.1.comp_contDiff hm (fun y => ⟨ht.le, Set.mem_univ y⟩)).of_le (by simp)
      | succ i => exact hs (i + 1) (by omega) (by omega)

end AVenhance.Infra.Section4
