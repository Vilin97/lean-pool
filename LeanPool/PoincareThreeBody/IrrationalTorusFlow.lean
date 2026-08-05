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

/-- A continuous periodic real function descends continuously to the corresponding additive
circle. -/
theorem Function.Periodic.continuous_lift
    {f : ℝ → ℝ} {period : ℝ} (hperiodic : Function.Periodic f period)
    (hcontinuous : Continuous f) :
    Continuous hperiodic.lift := by
  apply isQuotientMap_quotient_mk'.continuous_iff.mpr
  convert hcontinuous using 1
  funext argument
  exact hperiodic.lift_coe argument

/-- A continuous real function with an ordinary period and an incommensurable second period is
constant. -/
theorem eq_of_continuous_two_periods_of_irrational_ratio
    {f : ℝ → ℝ} {period shift : ℝ}
    (hcontinuous : Continuous f) (hperiod : Function.Periodic f period)
    (hshift : Function.Periodic f shift) (hirrational : Irrational (shift / period))
    (first second : ℝ) : f first = f second := by
  let descended : AddCircle period → ℝ := hperiod.lift
  let fiber : AddCircle period → ℝ := fun displacement ↦
    descended ((first : AddCircle period) + displacement)
  have hdescended : Continuous descended :=
    Function.Periodic.continuous_lift hperiod hcontinuous
  have hfiber : Continuous fiber := by
    dsimp only [fiber]
    fun_prop
  have hdense : DenseRange (fun n : ℤ ↦ n • ((shift : ℝ) : AddCircle period)) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr hirrational
  have hfiberDense : ∀ n : ℤ,
      fiber (n • ((shift : ℝ) : AddCircle period)) = fiber 0 := by
    intro n
    simp only [fiber, descended, ← AddCircle.coe_zsmul, ← AddCircle.coe_add,
      Function.Periodic.lift_coe, add_zero]
    simpa [add_comm] using hshift.zsmul n first
  have hfiberConstant : fiber = fun _ ↦ fiber 0 := by
    apply hfiber.ext_on hdense continuous_const
    intro displacement hdisplacement
    rcases hdisplacement with ⟨n, rfl⟩
    exact hfiberDense n
  have hvalue := congrFun hfiberConstant
    (((second : AddCircle period) - (first : AddCircle period)))
  have hcircle : (first : AddCircle period) +
      ((second : AddCircle period) - (first : AddCircle period)) = second := by
    abel
  dsimp only [fiber] at hvalue
  rw [hcircle] at hvalue
  simp only [descended, Function.Periodic.lift_coe, add_zero] at hvalue
  exact hvalue.symm

/-- Real-lift form of the irrational two-torus argument: a continuous function, periodic in both
angles and invariant under `(ω, -1)` translation, is constant when `ω` is irrational. -/
theorem eq_of_continuous_periodic_rotatingFlow_invariant
    {ω : ℝ} (hω : Irrational ω) {f : ℝ × ℝ → ℝ} (hf : Continuous f)
    (hmeanPeriod : ∀ mean periapsis,
      f (mean + 2 * Real.pi, periapsis) = f (mean, periapsis))
    (hperiapsisPeriod : ∀ mean periapsis,
      f (mean, periapsis + 2 * Real.pi) = f (mean, periapsis))
    (hinvariant : ∀ mean periapsis time,
      f (mean + ω * time, periapsis - time) = f (mean, periapsis))
    (first second : ℝ × ℝ) : f first = f second := by
  have hsameSecond : ∀ firstMean secondMean periapsis,
      f (firstMean, periapsis) = f (secondMean, periapsis) := by
    intro firstMean secondMean periapsis
    let meanFiber : ℝ → ℝ := fun mean ↦ f (mean, periapsis)
    have hcontinuous : Continuous meanFiber :=
      hf.comp (continuous_id.prodMk continuous_const)
    have hperiod : Function.Periodic meanFiber (2 * Real.pi) :=
      fun mean ↦ hmeanPeriod mean periapsis
    have hshift : Function.Periodic meanFiber (2 * Real.pi * ω) := by
      intro mean
      have hflow := hinvariant mean periapsis (2 * Real.pi)
      have hperi := hperiapsisPeriod (mean + ω * (2 * Real.pi))
        (periapsis - 2 * Real.pi)
      have hreturn : f (mean + ω * (2 * Real.pi), periapsis - 2 * Real.pi) =
          f (mean + ω * (2 * Real.pi), periapsis) := by
        simpa only [sub_add_cancel] using hperi.symm
      change f (mean + 2 * Real.pi * ω, periapsis) = f (mean, periapsis)
      rw [show mean + 2 * Real.pi * ω = mean + ω * (2 * Real.pi) by ring,
        ← hreturn]
      exact hflow
    have hratio : Irrational ((2 * Real.pi * ω) / (2 * Real.pi)) := by
      convert hω using 1
      field_simp [Real.pi_ne_zero]
    exact eq_of_continuous_two_periods_of_irrational_ratio
      hcontinuous hperiod hshift hratio firstMean secondMean
  obtain ⟨time, htime⟩ : ∃ time : ℝ, first.2 - time = second.2 :=
    ⟨first.2 - second.2, by ring⟩
  calc
    f first = f (first.1 + ω * time, first.2 - time) :=
      (hinvariant first.1 first.2 time).symm
    _ = f (second.1, first.2 - time) :=
      hsameSecond (first.1 + ω * time) second.1 (first.2 - time)
    _ = f second := by rw [htime]

end LeanPool.PoincareThreeBody
