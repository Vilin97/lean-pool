/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.IsTIterates
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section4.Jcut
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaPeriodicity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.ParabolicMaximum

/-! Actual iterates: periodicity, increment equations and telescoping.
These are structural prerequisites, not the quantitative V estimates. -/

@[expose] public section

noncomputable section
open Homogenization Filter
open scoped Topology
namespace AVenhance.Infra.Section4
open AVenhance

/-- The increments in e.T.minus.theta.m-1, including V⁰ = θprev. -/
def iterateIncrement (T : ℕ → ℝ → Vec 2 → ℝ) (i : ℕ) : ℝ → Vec 2 → ℝ :=
  if i = 0 then T 0 else fun t x => T i t x - T (i - 1) t x

@[simp] theorem iterateIncrement_zero (T : ℕ → ℝ → Vec 2 → ℝ) :
    iterateIncrement T 0 = T 0 := by simp only [iterateIncrement, ite_true]

@[simp] theorem iterateIncrement_succ (T : ℕ → ℝ → Vec 2 → ℝ) (i : ℕ) :
    iterateIncrement T (i + 1) = fun t x => T (i + 1) t x - T i t x := by
  simp only [iterateIncrement, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ite_false, Nat.add_sub_cancel]

/-- Telescoping identity for the actual increment definition. -/
theorem iterate_eq_sum_increments (T : ℕ → ℝ → Vec 2 → ℝ) (N : ℕ) (t : ℝ) (x : Vec 2) :
    T N t x = ∑ i ∈ Finset.range (N + 1), iterateIncrement T i t x := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, iterateIncrement_succ, ← ih]
    ring

/-- e.T.minus.theta.m-1 with the base iterate, without assuming estimates. -/
theorem iterate_sub_theta_eq_sum {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (N : ℕ) (t : ℝ) (x : Vec 2) :
    T N t x - θprev t x = ∑ i ∈ Finset.range N, iterateIncrement T (i + 1) t x := by
  induction N with
  | zero => simp only [hT.1, Finset.range_zero, Finset.sum_empty, sub_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, iterateIncrement_succ, ← ih]
    ring

/-- e.Tm-1.i#periodic, including the theta base case. -/
theorem iterates_periodic {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : ∀ t : ℝ, 0 ≤ t → IsZ2Periodic (θprev t))
    {i : ℕ} (hi : i ≤ Nstar β) {t : ℝ} (ht : 0 ≤ t) : IsZ2Periodic (T i t) := by
  by_cases hzero : i = 0
  · rw [hzero, hT.1]
    exact hθ t ht
  · exact (hT.2 i (by omega) hi).2.1 t ht

theorem IteratesBasic.classical_space_smooth {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol b κ F θ₀ u) {t : ℝ} (ht : 0 ≤ t) :
    ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => (t, x)) := by fun_prop
  exact hu.1.comp_contDiff hmap (fun x => ⟨ht, Set.mem_univ x⟩)

theorem IteratesBasic.classical_time_differentiable {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F : ℝ → Vec 2 → ℝ} {θ₀ : Vec 2 → ℝ} {u : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol b κ F θ₀ u) {t : ℝ} (ht : 0 < t) (x : Vec 2) :
    DifferentiableAt ℝ (fun s => u s x) t := by
  have hc := hu.1.contDiffAt
    (prod_mem_nhds (Ici_mem_nhds ht) (Filter.univ_mem : Set.univ ∈ nhds x))
  have hmap : ContDiffAt ℝ (⊤ : ℕ∞) (fun s : ℝ => (s, x)) t := by fun_prop
  exact (hc.comp t hmap).differentiableAt (by simp)

/-- Subtracting two actual classical solutions gives the difference equation.
No energy or increment estimate is assumed. -/
theorem classicalSol_sub {b : ℝ → Vec 2 → Vec 2} {κ : ℝ}
    {F G : ℝ → Vec 2 → ℝ} {u₀ v₀ : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol b κ F u₀ u) (hv : IsClassicalSol b κ G v₀ v) :
    IsClassicalSol b κ (fun t x => F t x - G t x) (fun x => u₀ x - v₀ x)
      (fun t x => u t x - v t x) := by
  refine ⟨hu.1.sub hv.1, ?_, ?_, ?_⟩
  · intro t ht k x
    dsimp only
    rw [hu.2.1 t ht k x, hv.2.1 t ht k x]
  · intro x
    dsimp only
    rw [hu.2.2.1 x, hv.2.2.1 x]
  · intro t ht x
    have hsU := IteratesBasic.classical_space_smooth hu ht.le
    have hsV := IteratesBasic.classical_space_smooth hv ht.le
    have hg : spaceGrad (fun y => u t y - v t y) x = spaceGrad (u t) x - spaceGrad (v t) x := by
      funext i
      exact Infra.Section3.spaceGrad_sub i (hsU.differentiable (by simp) x)
        (hsV.differentiable (by simp) x)
    unfold advDiffOp
    rw [deriv_fun_sub (IteratesBasic.classical_time_differentiable hu ht x)
      (IteratesBasic.classical_time_differentiable hv ht x),
      Infra.Section3.spaceLap_sub (hsU.of_le (by simp)) (hsV.of_le (by simp)), hg]
    have hpU := hu.2.2.2 t ht x
    have hpV := hv.2.2.2 t ht x
    unfold advDiffOp at hpU hpV
    simp only [vecDot, Pi.sub_apply, Finset.sum_sub_distrib, mul_sub]
    simp only [vecDot] at hpU hpV
    linear_combination hpU - hpV

/-- The first positive increment solves the forced equation with zero data. -/
theorem first_increment_classical {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (hθ : IsClassicalSol (streamVel (Φ (m - 1))) κprev (fun _ _ => 0) θ₀ θprev)
    (hN : 1 ≤ Nstar β) :
    IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (I.TForcing hΦ m κm κprev θprev) (fun _ => 0) (iterateIncrement T 1) := by
  have h := classicalSol_sub (hT.2 1 le_rfl hN) hθ
  simpa only [Nat.sub_self, hT.1, sub_zero, sub_self, iterateIncrement_succ] using h

/-- Each later increment solves the actual difference of consecutive forcing terms, with zero
    initial data. -/
theorem later_increment_classical {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} {κm κprev : ℝ} {θ₀ : Vec 2 → ℝ} {θprev : ℝ → Vec 2 → ℝ}
    {T : ℕ → ℝ → Vec 2 → ℝ} (hT : I.IsTIterates hΦ m κm κprev θ₀ θprev T)
    (i : ℕ) (hi : i + 2 ≤ Nstar β) :
    IsClassicalSol (streamVel (Φ (m - 1))) κprev
      (fun t x => I.TForcing hΦ m κm κprev (T (i + 1)) t x -
        I.TForcing hΦ m κm κprev (T i) t x)
      (fun _ => 0) (iterateIncrement T (i + 2)) := by
  have h := classicalSol_sub (hT.2 (i + 2) (by omega) hi)
    (hT.2 (i + 1) (by omega) (by omega))
  simpa only [show i + 2 - 1 = i + 1 by omega, Nat.add_sub_cancel,
    sub_self, show i + 2 = (i + 1) + 1 by omega, iterateIncrement_succ] using h

/-- The corrected Jcut does not exceed the actual iteration budget. -/
theorem Jcut_le_iteration_budget (β : ℝ) : Jcut β ≤ Nstar β := by
  unfold Jcut
  omega

end AVenhance.Infra.Section4
