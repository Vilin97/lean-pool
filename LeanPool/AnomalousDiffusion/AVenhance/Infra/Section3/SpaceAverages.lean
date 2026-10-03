/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section3.TimeMemorySymmetry
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Shear.OneDimensional
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.FrozenBridge
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Slicing
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Section3.SpaceAvg
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! Exact averages of the integer-frequency trigonometric modes in §3. -/

@[expose] public section

noncomputable section

open MeasureTheory
open intervalIntegral
open Homogenization

namespace AVenhance.Infra.Section3

theorem SpaceAverages.sin_square_periodic_one :
    Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x) ^ 2) 1 := by
  intro x
  change Real.sin (2 * Real.pi * (x + 1)) ^ 2 = Real.sin (2 * Real.pi * x) ^ 2
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  rw [Real.sin_add_two_pi]

theorem SpaceAverages.sin_periodic_one :
    Function.Periodic (fun x : ℝ => Real.sin (2 * Real.pi * x)) 1 := by
  intro x
  change Real.sin (2 * Real.pi * (x + 1)) = Real.sin (2 * Real.pi * x)
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  rw [Real.sin_add_two_pi]

/-- The square of an integer-frequency sine has unit-cell mean `1/2`. -/
theorem intervalAverage_sin_square_nat (n : ℕ) (hn : 0 < n) :
    (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (n : ℝ) * x) ^ 2) = 1 / 2 := by
  let g : ℝ → ℝ := fun y => Real.sin (2 * Real.pi * y) ^ 2
  have hperiod := SpaceAverages.sin_square_periodic_one
  have hinterval : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    exact (by fun_prop : Continuous g).intervalIntegrable a b
  have hwhole := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) (0 : ℝ) hinterval
  have hwhole' : (∫ y in (0 : ℝ)..(n : ℝ), g y) =
      (n : ℝ) * (∫ y in (0 : ℝ)..1, g y) := by
    simpa [g, zsmul_eq_mul] using hwhole
  have hbase : (∫ y in (0 : ℝ)..1, g y) = 1 / 2 := by
    simpa [g, AVenhance.Infra.Shear.cellAverage] using
      AVenhance.Infra.Shear.average_sin_sq
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (f := fun x : ℝ => (n : ℝ) * x)
    (f' := fun _ : ℝ => (n : ℝ))
    (g := g) (a := (0 : ℝ)) (b := 1)
    (by
      intro x hx
      simpa using (hasDerivAt_const_mul (n : ℝ)))
    (by fun_prop)
    (by fun_prop)
  have hsub' :
      (∫ x in (0 : ℝ)..1, g ((n : ℝ) * x) * (n : ℝ)) =
        ∫ y in (0 : ℝ)..(n : ℝ), g y := by
    simpa using hsub
  have hmul : (n : ℝ) *
      (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (n : ℝ) * x) ^ 2) =
        (n : ℝ) * (1 / 2) := by
    calc
      _ = ∫ x in (0 : ℝ)..1, g ((n : ℝ) * x) * (n : ℝ) := by
        rw [intervalIntegral.integral_mul_const]
        rw [show (fun x : ℝ => g ((n : ℝ) * x)) =
            (fun x => Real.sin (2 * Real.pi * (n : ℝ) * x) ^ 2) by
          funext x
          simp [g, mul_assoc]]
        ring
      _ = ∫ y in (0 : ℝ)..(n : ℝ), g y := hsub'
      _ = (n : ℝ) * (∫ y in (0 : ℝ)..1, g y) := hwhole'
      _ = (n : ℝ) * (1 / 2) := by rw [hbase]
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  exact (mul_left_cancel₀ hnR hmul)

/-- An integer-frequency sine has zero unit-cell mean. -/
theorem intervalAverage_sin_nat (n : ℕ) :
    (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (n : ℝ) * x)) = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · let g : ℝ → ℝ := fun y => Real.sin (2 * Real.pi * y)
    have hperiod := SpaceAverages.sin_periodic_one
    have hinterval : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
      intro a b
      exact (by fun_prop : Continuous g).intervalIntegrable a b
    have hwhole := hperiod.intervalIntegral_add_zsmul_eq (n : ℤ) (0 : ℝ) hinterval
    have hwhole' : (∫ y in (0 : ℝ)..(n : ℝ), g y) =
        (n : ℝ) * (∫ y in (0 : ℝ)..1, g y) := by
      simpa [g, zsmul_eq_mul] using hwhole
    have hbase : (∫ y in (0 : ℝ)..1, g y) = 0 := by
      simp [g]
    have hsub := intervalIntegral.integral_comp_mul_deriv
      (f := fun x : ℝ => (n : ℝ) * x)
      (f' := fun _ : ℝ => (n : ℝ))
      (g := g) (a := (0 : ℝ)) (b := 1)
      (by
        intro x hx
        simpa using (hasDerivAt_const_mul (n : ℝ)))
      (by fun_prop)
      (by fun_prop)
    have hsub' :
        (∫ x in (0 : ℝ)..1, g ((n : ℝ) * x) * (n : ℝ)) =
          ∫ y in (0 : ℝ)..(n : ℝ), g y := by
      simpa using hsub
    have hzero : (n : ℝ) *
        (∫ x in (0 : ℝ)..1, Real.sin (2 * Real.pi * (n : ℝ) * x)) = 0 := by
      calc
        _ = ∫ x in (0 : ℝ)..1, g ((n : ℝ) * x) * (n : ℝ) := by
          rw [intervalIntegral.integral_mul_const]
          rw [show (fun x : ℝ => g ((n : ℝ) * x)) =
              (fun x => Real.sin (2 * Real.pi * (n : ℝ) * x)) by
            funext x
            simp [g, mul_assoc]]
          ring
        _ = ∫ y in (0 : ℝ)..(n : ℝ), g y := hsub'
        _ = (n : ℝ) * (∫ y in (0 : ℝ)..1, g y) := hwhole'
        _ = 0 := by rw [hbase, mul_zero]
    have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    exact mul_left_cancel₀ hnR (by simpa using hzero)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def SpaceAverages.closedUnitSquare : Set (Vec 2) :=
  Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1

theorem SpaceAverages.continuous_coord_integrableOn_unitCell {F : ℝ → ℝ}
    (hF : Continuous F) (i : Fin 2) :
    IntegrableOn (fun x : Vec 2 => F (x i))
      (AVenhance.Infra.Torus.unitCell 2) := by
  have hcompact : IsCompact SpaceAverages.closedUnitSquare := by
    simpa [SpaceAverages.closedUnitSquare] using
      (isCompact_univ_pi fun _ : Fin 2 => isCompact_Icc)
  have hsubset : AVenhance.Infra.Torus.unitCell 2 ⊆ SpaceAverages.closedUnitSquare := by
    intro x hx
    simp only [AVenhance.Infra.Torus.unitCell,
      AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq] at hx
    simp only [SpaceAverages.closedUnitSquare, Set.mem_pi]
    intro j _hj
    exact ⟨le_of_lt (hx j).1, by simpa only [zero_add] using (hx j).2⟩
  have hcont : Continuous (fun x : Vec 2 => F (x i)) :=
    hF.comp (continuous_apply i)
  exact hcont.continuousOn.integrableOn_compact hcompact |>.mono_set hsubset

/-- A coordinate-only continuous function averages to its one-dimensional
unit-interval integral on the spatial cell. -/
theorem spaceAvg_coordIntegral {F : ℝ → ℝ} (hF : Continuous F) (i : Fin 2) :
    AVenhance.spaceAvg (fun x : Vec 2 => F (x i)) =
      ∫ t in (0 : ℝ)..1, F t := by
  unfold AVenhance.spaceAvg
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  rw [AVenhance.Infra.Torus.integral_unitCell2_peel_coord i
    (SpaceAverages.continuous_coord_integrableOn_unitCell hF i)]
  have hpoint (z : Vec 1) :
      (∫ t in Set.Ioc (0 : ℝ) 1,
        F ((i.insertNth (α := fun _ : Fin 2 => ℝ) t z) i)) =
        ∫ t in Set.Ioc (0 : ℝ) 1, F t := by
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp
  rw [show (fun z : Vec 1 =>
      ∫ t in Set.Ioc (0 : ℝ) 1,
        F ((i.insertNth (α := fun _ : Fin 2 => ℝ) t z) i)) =
      fun _ => ∫ t in Set.Ioc (0 : ℝ) 1, F t by
        funext z
        exact hpoint z]
  have hmeasure : (volume : Measure (Vec 1))
      (AVenhance.Infra.Torus.unitCell 1) = 1 := by
    have hcell : AVenhance.Infra.Torus.unitCell 1 =
        Set.pi Set.univ (fun _ : Fin 1 => Set.Ioc (0 : ℝ) 1) := by
      ext x
      simp [AVenhance.Infra.Torus.unitCell,
        AVenhance.Infra.Torus.unitCellAt, Set.pi]
    rw [hcell, volume_pi_pi]
    simp
  rw [setIntegral_const]
  change ((volume : Measure (Vec 1))
    (AVenhance.Infra.Torus.unitCell 1)).toReal •
      (∫ t in Set.Ioc (0 : ℝ) 1, F t) = _
  rw [hmeasure]
  norm_num
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]

/-- At every positive scale the reciprocal cell length is the integer used
to define `epsilon`. -/
theorem epsilon_inv_eq_ceil {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) :
    (epsilon β I.Λ m)⁻¹ =
      (⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℝ) := by
  have hm0 : m ≠ 0 := by omega
  simp [epsilon, hm0]

theorem SpaceAverages.epsilon_frequency_pos {β : ℝ} (I : Ingredients β) {m : ℕ} :
    0 < ⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ := by
  have hΛnat : 0 < I.Λ := by
    have := I.two_pow_seven_le
    omega
  have hΛ : 0 < (I.Λ : ℝ) := by exact_mod_cast hΛnat
  apply Nat.ceil_pos.mpr
  exact Real.rpow_pos_of_pos hΛ _

/-- The frequency `1/epsilon_m` is a positive integer, so its sine
and squared sine have the expected spatial averages. -/
theorem spaceAvg_sin_square_epsilon {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (i : Fin 2) :
    AVenhance.spaceAvg (fun x : Vec 2 =>
      Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x i) ^ 2) = 1 / 2 := by
  rw [epsilon_inv_eq_ceil I hm]
  rw [spaceAvg_coordIntegral (F := fun t : ℝ => Real.sin (2 * Real.pi *
    (⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℝ) * t) ^ 2) (by fun_prop) i]
  exact intervalAverage_sin_square_nat _ (SpaceAverages.epsilon_frequency_pos I)

theorem spaceAvg_sin_epsilon {β : ℝ} (I : Ingredients β) {m : ℕ}
    (hm : 1 ≤ m) (i : Fin 2) :
    AVenhance.spaceAvg (fun x : Vec 2 =>
      Real.sin (2 * Real.pi * (epsilon β I.Λ m)⁻¹ * x i)) = 0 := by
  rw [epsilon_inv_eq_ceil I hm]
  rw [spaceAvg_coordIntegral (F := fun t : ℝ => Real.sin (2 * Real.pi *
    (⌈(I.Λ : ℝ) ^ (q β ^ m / (q β - 1))⌉₊ : ℝ) * t)) (by fun_prop) i]
  exact intervalAverage_sin_nat _

end AVenhance.Infra.Section3
