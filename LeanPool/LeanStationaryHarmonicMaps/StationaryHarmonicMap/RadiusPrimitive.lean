/-
Copyright (c) 2026 Wei Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wei Wang
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.Order.IsLocallyClosed
import LeanPool.LeanStationaryHarmonicMaps.StationaryHarmonicMap.RadiusAnalysis

/-!
# Radius primitive formulas

This module contains primitive, increment, annulus, and interval-indicator
forms of the radius derivative calculus.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology BigOperators ENNReal

namespace LeanStationaryHarmonicMaps
namespace StationaryHarmonicMap

/-- Primitive form of the radius calculus: on every subinterval of `(0, R0)`,
both ball-energy functions are equal to their interval primitive of the stated
derivative.  This is the exact one-dimensional FTC statement extracted from
coarea/radius differentiation. -/
def WeakEnergyRadiusPrimitiveFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallEnergy Du (0 : Domain n))) volume a b ∧
    EqOn
      (weakBallEnergy Du (0 : Domain n))
      (fun r : ℝ =>
        weakBallEnergy Du (0 : Domain n) a +
          ∫ rho in a..r, deriv (weakBallEnergy Du (0 : Domain n)) rho)
      (uIcc a b)) ∧
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallRadialEnergy Du (0 : Domain n))) volume a b ∧
    EqOn
      (weakBallRadialEnergy Du (0 : Domain n))
      (fun r : ℝ =>
        weakBallRadialEnergy Du (0 : Domain n) a +
          ∫ rho in a..r, deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)
      (uIcc a b))

/-- Increment form of the radius calculus: the two ball-energy functions satisfy
the fundamental theorem of calculus on every subinterval of `[0, R0]`. -/
def WeakEnergyRadiusIncrementFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallEnergy Du (0 : Domain n))) volume a b ∧
      weakBallEnergy Du (0 : Domain n) b -
          weakBallEnergy Du (0 : Domain n) a
        =
      ∫ rho in a..b, deriv (weakBallEnergy Du (0 : Domain n)) rho) ∧
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallRadialEnergy Du (0 : Domain n))) volume a b ∧
      weakBallRadialEnergy Du (0 : Domain n) b -
          weakBallRadialEnergy Du (0 : Domain n) a
        =
      ∫ rho in a..b, deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)

/-- Interval integrability of the two radius derivatives on every subinterval
of `[0, R0]`. -/
def WeakEnergyRadiusDerivativeIntegrability {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallEnergy Du (0 : Domain n))) volume a b) ∧
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
    IntervalIntegrable (deriv (weakBallRadialEnergy Du (0 : Domain n))) volume a b)

/-- Absolute continuity of the two radius functions supplies the interval
integrability of their derivatives on all subintervals of `[0, R0]`. -/
theorem weakEnergyRadiusDerivativeIntegrability_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    WeakEnergyRadiusDerivativeIntegrability Du R0 := by
  constructor
  · intro a b ha hab hb
    exact (hac.1 ha hab hb).intervalIntegrable_deriv
  · intro a b ha hab hb
    exact (hac.2 ha hab hb).intervalIntegrable_deriv

/-- Absolute continuity of the energy radius function gives local
integrability of the energy itself on the open radius interval. -/
theorem weakBallEnergy_locallyIntegrableOn_Ioo_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    LocallyIntegrableOn
      (fun rho : ℝ => weakBallEnergy Du (0 : Domain n) rho)
      (Ioo (0 : ℝ) R0) volume := by
  intro x hx
  let a : ℝ := x / 2
  let b : ℝ := (x + R0) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (le_of_lt hx.1) (by norm_num)
  have hxa : a < x := by
    dsimp [a]
    nlinarith [hx.1]
  have hxb : x < b := by
    dsimp [b]
    nlinarith [hx.2]
  have hab : a ≤ b := le_of_lt (hxa.trans hxb)
  have hbR : b ≤ R0 := by
    dsimp [b]
    nlinarith [hx.2]
  have hnhds : Ioo a b ∈ 𝓝[Ioo (0 : ℝ) R0] x :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hxa, hxb⟩)
  refine ⟨Ioo a b, hnhds, ?_⟩
  have hEac :
      AbsolutelyContinuousOnInterval
        (weakBallEnergy Du (0 : Domain n)) a b :=
    hac.1 ha0 hab hbR
  have hE_intvl :
      IntervalIntegrable
        (weakBallEnergy Du (0 : Domain n)) volume a b :=
    hEac.continuousOn.intervalIntegrable
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hE_intvl

/-- Absolute continuity of the energy radius function gives local
integrability of its a.e. derivative on the open radius interval. -/
theorem locallyIntegrableOn_deriv_weakBallEnergy_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    LocallyIntegrableOn
      (fun rho : ℝ => deriv (weakBallEnergy Du (0 : Domain n)) rho)
      (Ioo (0 : ℝ) R0) volume := by
  intro x hx
  let a : ℝ := x / 2
  let b : ℝ := (x + R0) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (le_of_lt hx.1) (by norm_num)
  have hxa : a < x := by
    dsimp [a]
    nlinarith [hx.1]
  have hxb : x < b := by
    dsimp [b]
    nlinarith [hx.2]
  have hab : a ≤ b := le_of_lt (hxa.trans hxb)
  have hbR : b ≤ R0 := by
    dsimp [b]
    nlinarith [hx.2]
  have hnhds : Ioo a b ∈ 𝓝[Ioo (0 : ℝ) R0] x :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hxa, hxb⟩)
  refine ⟨Ioo a b, hnhds, ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
    ((weakEnergyRadiusDerivativeIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac).1 ha0 hab hbR)

/-- Absolute continuity of the radial-energy radius function gives local
integrability of its a.e. derivative on the open radius interval. -/
theorem locallyIntegrableOn_deriv_weakBallRadialEnergy_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    LocallyIntegrableOn
      (fun rho : ℝ => deriv (weakBallRadialEnergy Du (0 : Domain n)) rho)
      (Ioo (0 : ℝ) R0) volume := by
  intro x hx
  let a : ℝ := x / 2
  let b : ℝ := (x + R0) / 2
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (le_of_lt hx.1) (by norm_num)
  have hxa : a < x := by
    dsimp [a]
    nlinarith [hx.1]
  have hxb : x < b := by
    dsimp [b]
    nlinarith [hx.2]
  have hab : a ≤ b := le_of_lt (hxa.trans hxb)
  have hbR : b ≤ R0 := by
    dsimp [b]
    nlinarith [hx.2]
  have hnhds : Ioo a b ∈ 𝓝[Ioo (0 : ℝ) R0] x :=
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ⟨hxa, hxb⟩)
  refine ⟨Ioo a b, hnhds, ?_⟩
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp
    ((weakEnergyRadiusDerivativeIntegrability_of_radius_ac
      (n := n) (m := m) (Du := Du) (R0 := R0) hac).2 ha0 hab hbR)

/-- The sharp-cutoff defect is locally integrable once the two radius energy
functions are absolutely continuous on compact subintervals of `[0, R0]`. -/
theorem weakSharpCutoffDefect_locallyIntegrableOn_of_radius_ac {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hac : WeakEnergyAbsolutelyContinuousOnRadii Du R0) :
    LocallyIntegrableOn
      (fun rho : ℝ => weakSharpCutoffDefect Du (0 : Domain n) rho)
      (Ioo (0 : ℝ) R0) volume := by
  let s : Set ℝ := Ioo (0 : ℝ) R0
  let E : ℝ → ℝ := weakBallEnergy Du (0 : Domain n)
  let Q : ℝ → ℝ := weakBallRadialEnergy Du (0 : Domain n)
  have hs_locallyClosed : IsLocallyClosed s := by
    simpa [s] using (isLocallyClosed_Ioo : IsLocallyClosed (Ioo (0 : ℝ) R0))
  have hE_loc : LocallyIntegrableOn E s volume := by
    simpa [E, s] using
      weakBallEnergy_locallyIntegrableOn_Ioo_of_radius_ac
        (n := n) (m := m) (Du := Du) (R0 := R0) hac
  have hE_deriv_loc :
      LocallyIntegrableOn (fun rho : ℝ => deriv E rho) s volume := by
    simpa [E, s] using
      locallyIntegrableOn_deriv_weakBallEnergy_of_radius_ac
        (n := n) (m := m) (Du := Du) (R0 := R0) hac
  have hQ_deriv_loc :
      LocallyIntegrableOn (fun rho : ℝ => deriv Q rho) s volume := by
    simpa [Q, s] using
      locallyIntegrableOn_deriv_weakBallRadialEnergy_of_radius_ac
        (n := n) (m := m) (Du := Du) (R0 := R0) hac
  have hconst_cont :
      ContinuousOn (fun _ : ℝ => (n : ℝ) - 2) s := by
    fun_prop
  have hid_cont : ContinuousOn (fun rho : ℝ => rho) s := by
    fun_prop
  have htwo_cont : ContinuousOn (fun rho : ℝ => (2 : ℝ) * rho) s := by
    fun_prop
  have hmain :
      LocallyIntegrableOn
        (fun rho : ℝ => ((n : ℝ) - 2) * E rho - rho * deriv E rho
          + (2 * rho) * deriv Q rho)
        s volume := by
    have htermE :
        LocallyIntegrableOn
          (fun rho : ℝ => ((n : ℝ) - 2) * E rho) s volume :=
      MeasureTheory.LocallyIntegrableOn.continuousOn_mul
        hE_loc hconst_cont hs_locallyClosed
    have htermEderiv :
        LocallyIntegrableOn
          (fun rho : ℝ => rho * deriv E rho) s volume :=
      MeasureTheory.LocallyIntegrableOn.continuousOn_mul
        hE_deriv_loc hid_cont hs_locallyClosed
    have htermQderiv :
        LocallyIntegrableOn
          (fun rho : ℝ => (2 * rho) * deriv Q rho) s volume :=
      MeasureTheory.LocallyIntegrableOn.continuousOn_mul
        hQ_deriv_loc htwo_cont hs_locallyClosed
    exact (htermE.sub htermEderiv).add htermQderiv
  simpa [weakSharpCutoffDefect, E, Q, s, mul_assoc] using hmain

/-- The primitive/FTC radius package contains the derivative integrability
field, so it can be projected out when needed by lower-level constructors. -/
theorem weakEnergyRadiusDerivativeIntegrability_of_radiusPrimitive {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hprim : WeakEnergyRadiusPrimitiveFormula Du R0) :
    WeakEnergyRadiusDerivativeIntegrability Du R0 := by
  constructor
  · intro a b ha hab hb
    exact (hprim.1 ha hab hb).1
  · intro a b ha hab hb
    exact (hprim.2 ha hab hb).1

/-- The increment/FTC radius package contains the derivative integrability
field, so it can be projected out when needed by lower-level constructors. -/
theorem weakEnergyRadiusDerivativeIntegrability_of_radiusIncrement {n m : ℕ}
    {Du : Domain n → Gradient n m} {R0 : ℝ}
    (hinc : WeakEnergyRadiusIncrementFormula Du R0) :
    WeakEnergyRadiusDerivativeIntegrability Du R0 := by
  constructor
  · intro a b ha hab hb
    exact (hinc.1 ha hab hb).1
  · intro a b ha hab hb
    exact (hinc.2 ha hab hb).1

/-- Annulus form of the ball-energy increments.  The open annulus is enough:
the missing boundary spheres are null in the eventual geometric proof. -/
def WeakEnergyAnnulusFormula {n m : ℕ}
    (Du : Domain n → Gradient n m) (R0 : ℝ) : Prop :=
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
      weakBallEnergy Du (0 : Domain n) b -
          weakBallEnergy Du (0 : Domain n) a
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
          weakEnergyDensity Du x) ∧
  (∀ {a b : ℝ}, 0 ≤ a → a ≤ b → b ≤ R0 →
      weakBallRadialEnergy Du (0 : Domain n) b -
          weakBallRadialEnergy Du (0 : Domain n) a
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ *
          weakRadialEnergyDensity Du (0 : Domain n) x)

/-- The open annulus `B_b \ closedBall_a` differs from `B_b \ B_a` only by the
inner sphere.  In positive dimension that sphere has zero Lebesgue measure. -/
theorem ball_diff_closedBall_ae_eq_ball_diff_ball {n : ℕ} [NeZero n]
    {a b : ℝ} :
    (Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a)
      =ᵐ[volume]
    (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) := by
  apply ae_eq_set.mpr
  constructor
  · have hsub :
        (Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a) \
            (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a)
          ⊆ (∅ : Set (Domain n)) := by
        intro x hx
        rcases hx with ⟨⟨hxb, hxclosed⟩, hxnot⟩
        exact hxnot ⟨hxb, fun hxball => hxclosed (Metric.ball_subset_closedBall hxball)⟩
    exact measure_mono_null hsub (by simp)
  · have hsub :
        (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) \
            (Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a)
          ⊆ Metric.sphere (0 : Domain n) a := by
        intro x hx
        rcases hx with ⟨⟨hxb, hxball⟩, hxnot⟩
        have hxclosed : x ∈ Metric.closedBall (0 : Domain n) a := by
          by_contra hxc
          exact hxnot ⟨hxb, hxc⟩
        have hxmem : x ∈ Metric.closedBall (0 : Domain n) a \ Metric.ball (0 : Domain n) a :=
          ⟨hxclosed, hxball⟩
        simpa [Metric.closedBall_sdiff_ball] using hxmem
    exact measure_mono_null hsub
      (by simpa using
        (Measure.addHaar_sphere (volume : Measure (Domain n)) (0 : Domain n) a))

/-- Integrating a radial indicator over a containing ball realizes the energy
increment between the two open balls. -/
theorem ball_annulus_indicator_integral_eq_energy_diff {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ}
    (hab : a ≤ b) (hb : b ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) b) volume) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
      =
    (∫ x in Metric.ball (0 : Domain n) b, f x)
      - (∫ x in Metric.ball (0 : Domain n) a, f x) := by
  let ann : Set (Domain n) := {x | ‖x‖ ∈ Ioo a b}
  have hann_meas : MeasurableSet ann := by
    exact (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hset :
      Metric.ball (0 : Domain n) R0 ∩ ann =
        Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨_hR0, hxann⟩
      exact ⟨by simpa [Metric.mem_ball, dist_eq_norm, ann] using hxann.2,
        by
          intro hxclosed
          have hle : ‖x‖ ≤ a := by
            simpa [Metric.mem_closedBall, dist_eq_norm] using hxclosed
          exact (not_le_of_gt hxann.1) hle⟩
    · intro hx
      rcases hx with ⟨hxb, hxclosed⟩
      have hxnorm_lt_b : ‖x‖ < b := by
        simpa [Metric.mem_ball, dist_eq_norm] using hxb
      have hxann_left : a < ‖x‖ := by
        by_contra hnot
        have hle : ‖x‖ ≤ a := le_of_not_gt hnot
        exact hxclosed (by simpa [Metric.mem_closedBall, dist_eq_norm] using hle)
      exact ⟨by
          have hxnorm_lt_R0 : ‖x‖ < R0 := lt_of_lt_of_le hxnorm_lt_b hb
          simpa [Metric.mem_ball, dist_eq_norm] using hxnorm_lt_R0,
        ⟨hxann_left, hxnorm_lt_b⟩⟩
  have hclosed_ae :
      (Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a)
        =ᵐ[volume]
      (Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a) :=
    ball_diff_closedBall_ae_eq_ball_diff_ball (n := n) (a := a) (b := b)
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
        =
      ∫ x in Metric.ball (0 : Domain n) R0, ann.indicator f x := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x _hx
        change (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x =
          ann.indicator f x
        by_cases hxann : ‖x‖ ∈ Ioo a b
        · have hxann' : x ∈ ann := by
            simpa [ann] using hxann
          rw [Set.indicator_of_mem hxann, Set.indicator_of_mem hxann']
          simp
        · have hxann' : x ∉ ann := by
            simpa [ann] using hxann
          rw [Set.indicator_of_notMem hxann, Set.indicator_of_notMem hxann']
          simp
    _ =
      ∫ x in Metric.ball (0 : Domain n) R0 ∩ ann, f x := by
        rw [setIntegral_indicator hann_meas]
    _ =
      ∫ x in Metric.ball (0 : Domain n) b \ Metric.closedBall (0 : Domain n) a, f x := by
        rw [hset]
    _ =
      ∫ x in Metric.ball (0 : Domain n) b \ Metric.ball (0 : Domain n) a, f x :=
        setIntegral_congr_set hclosed_ae
    _ =
      (∫ x in Metric.ball (0 : Domain n) b, f x)
        - (∫ x in Metric.ball (0 : Domain n) a, f x) := by
        rw [setIntegral_sdiff measurableSet_ball hf (Metric.ball_subset_ball hab)]

/-- The radial signed pushforward of `f dx` on the ambient ball, evaluated on
an interval of radii, is the corresponding ball-integral increment. -/
theorem radialVectorMeasure_apply_Ioo_eq_ballIntegral_sub {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ}
    (hab : a ≤ b) (hb : b ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume) :
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => ‖x‖)) (Ioo a b)
      =
    (∫ x in Metric.ball (0 : Domain n) b, f x)
      - (∫ x in Metric.ball (0 : Domain n) a, f x) := by
  let ann : Set (Domain n) := {x | ‖x‖ ∈ Ioo a b}
  have hann_meas : MeasurableSet ann := by
    exact (isOpen_Ioo.preimage continuous_norm).measurableSet
  have hf_b : IntegrableOn f (Metric.ball (0 : Domain n) b) volume :=
    hf.mono_set (Metric.ball_subset_ball hb)
  have hpush :
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
          (fun x : Domain n => ‖x‖)) (Ioo a b)
        =
      ∫ x in ann, f x ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
    simpa [ann] using
      radialVectorMeasure_apply
        (n := n) (f := f) (R0 := R0) (s := Ioo a b) hf measurableSet_Ioo
  have hann_indicator :
      (∫ x in ann, f x ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x := by
    calc
      (∫ x in ann, f x ∂(volume.restrict (Metric.ball (0 : Domain n) R0)))
          =
        ∫ x, ann.indicator f x
          ∂(volume.restrict (Metric.ball (0 : Domain n) R0)) := by
          rw [integral_indicator hann_meas]
      _ =
        ∫ x in Metric.ball (0 : Domain n) R0, ann.indicator f x := rfl
      _ =
        ∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x := by
          apply setIntegral_congr_fun measurableSet_ball
          intro x _hx
          change ann.indicator f x =
            (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x
          by_cases hxann : ‖x‖ ∈ Ioo a b
          · have hxann' : x ∈ ann := by
              simpa [ann] using hxann
            rw [Set.indicator_of_mem hxann', Set.indicator_of_mem hxann]
            simp
          · have hxann' : x ∉ ann := by
              simpa [ann] using hxann
            rw [Set.indicator_of_notMem hxann', Set.indicator_of_notMem hxann]
            simp
  calc
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => ‖x‖)) (Ioo a b)
        =
      ∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x := by
        rw [hpush, hann_indicator]
    _ =
      (∫ x in Metric.ball (0 : Domain n) b, f x)
        - (∫ x in Metric.ball (0 : Domain n) a, f x) :=
      ball_annulus_indicator_integral_eq_energy_diff
        (n := n) (f := f) (a := a) (b := b) (R0 := R0)
        hab hb hf_b

/-- If the ball-integral radius function is absolutely continuous, then the
radial signed pushforward of `f dx` on `(a, b)` is the integral of the a.e.
radius derivative over `[a, b]`. -/
theorem radialVectorMeasure_apply_Ioo_eq_integral_deriv_ballIntegral
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => ‖x‖)) (Ioo a b)
      =
    ∫ rho in a..b,
      deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hpush :
      (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
          (fun x : Domain n => ‖x‖)) (Ioo a b)
        =
      F b - F a := by
    simpa [F] using
      radialVectorMeasure_apply_Ioo_eq_ballIntegral_sub
        (n := n) (f := f) (a := a) (b := b) (R0 := R0)
        hab hb hf
  have hFTC :
      ∫ rho in a..b, deriv F rho = F b - F a :=
    (hac ha hab hb).integral_deriv_eq_sub
  calc
    (((volume.restrict (Metric.ball (0 : Domain n) R0)).withDensityᵥ f).map
        (fun x : Domain n => ‖x‖)) (Ioo a b)
        =
      F b - F a := hpush
    _ =
      ∫ rho in a..b, deriv F rho := hFTC.symm

/-- The ball-integral radius derivative formula for interval-indicator
weights.  This is the interval/simple-function core of the remaining extension
to all bounded measurable radius weights. -/
theorem ballIntegralRadiusDerivativeFormulaForIndicator_Ioo
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho *
        deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hf_b : IntegrableOn f (Metric.ball (0 : Domain n) b) volume :=
    hf.mono_set (Metric.ball_subset_ball hb)
  have hleft :
      (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
        =
      F b - F a := by
    simpa [F] using
      ball_annulus_indicator_integral_eq_energy_diff
        (n := n) (f := f) (a := a) (b := b) (R0 := R0)
        hab hb hf_b
  have hright :
      (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * deriv F rho)
        =
      ∫ rho in a..b, deriv F rho :=
    integral_Ioo_zero_radius_indicator_Ioo_eq_intervalIntegral
      (f := deriv F) ha hab hb
  have hFTC :
      ∫ rho in a..b, deriv F rho = F b - F a :=
    (hac ha hab hb).integral_deriv_eq_sub
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
        =
      F b - F a := hleft
    _ =
      ∫ rho in a..b, deriv F rho := hFTC.symm
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * deriv F rho) :=
      hright.symm

/-- The interval-indicator radius derivative formula, with a scalar coefficient
in front of the interval indicator. -/
theorem ballIntegralRadiusDerivativeFormulaForIndicatorConst_Ioo
    {n : ℕ} [NeZero n]
    {f : Domain n → ℝ} {a b R0 k : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ R0)
    (hf : IntegrableOn f (Metric.ball (0 : Domain n) R0) volume)
    (hac : BallIntegralRadiusAbsolutelyContinuous f R0) :
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖ * f x)
      =
    (∫ rho in Ioo (0 : ℝ) R0,
      (Ioo a b).indicator (fun _ : ℝ => k) rho *
        deriv (fun r : ℝ => ∫ x in Metric.ball (0 : Domain n) r, f x) rho) := by
  let F : ℝ → ℝ := fun r : ℝ =>
    ∫ x in Metric.ball (0 : Domain n) r, f x
  have hone :
      (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x)
        =
      (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * deriv F rho) := by
    exact ballIntegralRadiusDerivativeFormulaForIndicator_Ioo
      (n := n) (f := f) (a := a) (b := b) (R0 := R0)
      ha hab hb hf hac
  have hleft :
      (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖ * f x)
        =
      k * (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_ball
    intro x _hx
    by_cases hx : ‖x‖ ∈ Ioo a b
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hright :
      (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => k) rho * deriv F rho)
        =
      k * (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * deriv F rho) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioo
    intro rho _hrho
    by_cases hrho : rho ∈ Ioo a b
    · simp [Set.indicator_of_mem hrho]
    · simp [Set.indicator_of_notMem hrho]
  calc
    (∫ x in Metric.ball (0 : Domain n) R0,
        (Ioo a b).indicator (fun _ : ℝ => k) ‖x‖ * f x)
        =
      k * (∫ x in Metric.ball (0 : Domain n) R0,
          (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) ‖x‖ * f x) := hleft
    _ =
      k * (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => (1 : ℝ)) rho * deriv F rho) := by
      rw [hone]
    _ =
      (∫ rho in Ioo (0 : ℝ) R0,
        (Ioo a b).indicator (fun _ : ℝ => k) rho * deriv F rho) :=
      hright.symm

end StationaryHarmonicMap
end LeanStationaryHarmonicMaps

end
