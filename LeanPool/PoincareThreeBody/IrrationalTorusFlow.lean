/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
import Mathlib.Topology.Instances.Irrational
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.FunProp

/-!
# Irrational rotating flows on the two-torus

The rotating Kepler frequency has the form `(ω, -1)`.  When `ω` is irrational, its flow is dense
on the angle torus.  This file proves directly that a continuous invariant of that flow is
constant, using irrational rotations on a circle.
-/

namespace LeanPool.PoincareThreeBody

open Set

/-- The circle with the natural angular period `2π`. -/
abbrev AngleCircle := Real.Angle

/-- The two Delaunay angles. -/
abbrev AngleTorus := AngleCircle × AngleCircle

/-- Translation by the rotating Kepler frequency `(ω, -1)` on the angle torus. -/
noncomputable def rotatingAngleFlow (ω time : ℝ) (angle : AngleTorus) : AngleTorus :=
  (angle.1 + ((ω * time : ℝ) : AngleCircle), angle.2 - ((time : ℝ) : AngleCircle))

lemma rotatingAngleFlow_zero (ω : ℝ) (angle : AngleTorus) :
    rotatingAngleFlow ω 0 angle = angle := by
  simp [rotatingAngleFlow]

lemma rotatingAngleFlow_add (ω first second : ℝ) (angle : AngleTorus) :
    rotatingAngleFlow ω (first + second) angle =
      rotatingAngleFlow ω second (rotatingAngleFlow ω first angle) := by
  apply Prod.ext
  · change angle.1 + ((ω * (first + second) : ℝ) : AngleCircle) =
      (angle.1 + ((ω * first : ℝ) : AngleCircle)) +
        ((ω * second : ℝ) : AngleCircle)
    rw [mul_add, Real.Angle.coe_add]
    abel
  · change angle.2 - (((first + second : ℝ) : AngleCircle)) =
      (angle.2 - ((first : ℝ) : AngleCircle)) - ((second : ℝ) : AngleCircle)
    rw [Real.Angle.coe_add]
    abel

/-- On an irrational rotating Kepler torus, fixing the second angle and advancing through whole
rotating periods gives a dense set of first angles. -/
theorem denseRange_firstAngle_wholePeriods {ω : ℝ} (hω : Irrational ω) :
    DenseRange (fun n : ℤ ↦ (n • ((2 * Real.pi * ω : ℝ) : AngleCircle))) := by
  change DenseRange (fun n : ℤ ↦
    (n • ((2 * Real.pi * ω : ℝ) : AddCircle (2 * Real.pi))))
  rw [AddCircle.denseRange_zsmul_coe_iff]
  convert hω using 1
  field_simp [Real.pi_ne_zero]

/-- A continuous function invariant under the rotating flow is independent of the first angle
when the Kepler frequency is irrational. -/
theorem eq_of_same_second_of_rotatingAngleFlow_invariant
    {ω : ℝ} (hω : Irrational ω) {f : AngleTorus → ℝ} (hf : Continuous f)
    (hinvariant : ∀ angle time, f (rotatingAngleFlow ω time angle) = f angle)
    (first second fixedSecond : AngleCircle) :
    f (first, fixedSecond) = f (second, fixedSecond) := by
  let fiber : AngleCircle → ℝ := fun shift ↦ f (first + shift, fixedSecond)
  have hfiber : Continuous fiber := by
    dsimp only [fiber]
    fun_prop
  have hdense : DenseRange
      (fun n : ℤ ↦ n • ((2 * Real.pi * ω : ℝ) : AngleCircle)) :=
    denseRange_firstAngle_wholePeriods hω
  have hfiberDense : ∀ n : ℤ,
      fiber (n • ((2 * Real.pi * ω : ℝ) : AngleCircle)) = fiber 0 := by
    intro n
    have hflow := hinvariant (first, fixedSecond) (2 * Real.pi * n)
    have hstate : rotatingAngleFlow ω (2 * Real.pi * n) (first, fixedSecond) =
        (first + n • ((2 * Real.pi * ω : ℝ) : AngleCircle), fixedSecond) := by
      apply Prod.ext
      · dsimp [rotatingAngleFlow]
        congr 1
        rw [← Real.Angle.coe_zsmul]
        congr 1
        simp [zsmul_eq_mul]
        ring
      · dsimp [rotatingAngleFlow]
        have hmultiple : 2 * Real.pi * (n : ℝ) = n • (2 * Real.pi : ℝ) := by
          simp [zsmul_eq_mul]
          ring
        rw [hmultiple, Real.Angle.coe_zsmul, Real.Angle.coe_two_pi, smul_zero]
        abel
    rw [hstate] at hflow
    simpa [fiber] using hflow
  have hfiberConstant : fiber = fun _ ↦ fiber 0 := by
    apply hfiber.ext_on hdense continuous_const
    intro shift hshift
    rcases hshift with ⟨n, rfl⟩
    exact hfiberDense n
  have hsurjective : Function.Surjective (fun shift : AngleCircle ↦ first + shift) := by
    intro target
    exact ⟨target - first, by abel⟩
  obtain ⟨shift, hshift⟩ := hsurjective second
  have hvalue := congrFun hfiberConstant shift
  dsimp only [fiber] at hvalue
  simpa [hshift] using hvalue.symm

/-- A continuous invariant of an irrational rotating Kepler flow is constant on the entire
two-torus. -/
theorem eq_of_rotatingAngleFlow_invariant
    {ω : ℝ} (hω : Irrational ω) {f : AngleTorus → ℝ} (hf : Continuous f)
    (hinvariant : ∀ angle time, f (rotatingAngleFlow ω time angle) = f angle)
    (first second : AngleTorus) : f first = f second := by
  obtain ⟨time, htime⟩ : ∃ time : ℝ, (time : AngleCircle) = first.2 - second.2 :=
    QuotientAddGroup.mk_surjective (first.2 - second.2)
  have hflow := hinvariant first time
  have hsecond : (rotatingAngleFlow ω time first).2 = second.2 := by
    simp only [rotatingAngleFlow]
    rw [htime]
    abel
  calc
    f first = f (rotatingAngleFlow ω time first) := hflow.symm
    _ = f second := by
      have hsame := eq_of_same_second_of_rotatingAngleFlow_invariant hω hf hinvariant
        (rotatingAngleFlow ω time first).1 second.1 second.2
      calc
        f (rotatingAngleFlow ω time first) =
            f ((rotatingAngleFlow ω time first).1, second.2) := by
          congr 1
          exact Prod.ext rfl hsecond
        _ = f second := by simpa only [Prod.eta] using hsame

/-- Extensional form: every continuous invariant of an irrational rotating flow is a constant
function. -/
theorem rotatingAngleFlow_invariant_eq_const
    {ω : ℝ} (hω : Irrational ω) {f : AngleTorus → ℝ} (hf : Continuous f)
    (hinvariant : ∀ angle time, f (rotatingAngleFlow ω time angle) = f angle)
    (base : AngleTorus) : f = fun _ ↦ f base := by
  funext angle
  exact eq_of_rotatingAngleFlow_invariant hω hf hinvariant angle base

/-- For a jointly continuous family of invariants, angle-independence on the dense irrational
frequencies extends to every frequency. -/
theorem eq_of_continuous_family_rotatingAngleFlow_invariant
    {f : ℝ × AngleTorus → ℝ} (hf : Continuous f)
    (hinvariant : ∀ ω angle time,
      f (ω, rotatingAngleFlow ω time angle) = f (ω, angle))
    (ω : ℝ) (first second : AngleTorus) :
    f (ω, first) = f (ω, second) := by
  have hfirst : Continuous (fun frequency ↦ f (frequency, first)) := by
    exact hf.comp (continuous_id.prodMk continuous_const)
  have hsecond : Continuous (fun frequency ↦ f (frequency, second)) := by
    exact hf.comp (continuous_id.prodMk continuous_const)
  have heq : (fun frequency ↦ f (frequency, first)) =
      fun frequency ↦ f (frequency, second) := by
    apply hfirst.ext_on dense_irrational hsecond
    intro frequency hfrequency
    exact eq_of_rotatingAngleFlow_invariant hfrequency
      (hf.comp (continuous_const.prodMk continuous_id))
      (fun angle time ↦ hinvariant frequency angle time) first second
  exact congrFun heq ω

/-- Extensional form of angle-independence for a continuous family of rotating-flow invariants. -/
theorem continuous_family_rotatingAngleFlow_invariant_eq_base
    {f : ℝ × AngleTorus → ℝ} (hf : Continuous f)
    (hinvariant : ∀ ω angle time,
      f (ω, rotatingAngleFlow ω time angle) = f (ω, angle))
    (base : AngleTorus) :
    f = fun state ↦ f (state.1, base) := by
  funext state
  exact eq_of_continuous_family_rotatingAngleFlow_invariant hf hinvariant
    state.1 state.2 base

end LeanPool.PoincareThreeBody
