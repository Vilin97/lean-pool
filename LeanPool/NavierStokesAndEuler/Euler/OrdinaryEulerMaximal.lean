/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLifespan
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerLimit
import LeanPool.NavierStokesAndEuler.Euler.MeanClassicalConstraints

/-! One actual Euler field on the half-open maximal interval. Values are
chosen on intermediate horizons, and genuine Euler uniqueness removes
the dependence on that choice. No continuation criterion is assumed. -/

@[expose] public section


noncomputable section

namespace EulerOrdinarySobolev.FiniteLifespan

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerMeanSolenoidal EulerMeanClassical
open scoped Topology ContDiff

variable {A : SmoothL2Field Space} (L : FiniteLifespan A)

/-- Time: an abbreviation for `Ico (0 : ℝ) L.duration`. -/
abbrev Time : Type := Ico (0 : ℝ) L.duration

/-- Initial time, given by `⟨0,le_rfl,L.duration_pos⟩`. -/
def initialTime : L.Time := ⟨0,le_rfl,L.duration_pos⟩

/-- Intermediate horizon, given by `((t : ℝ)+L.duration)/2`. -/
def intermediateHorizon (t : L.Time) : ℝ := ((t : ℝ)+L.duration)/2

theorem intermediateHorizon_pos (t : L.Time) : 0 < L.intermediateHorizon t := by
  have ht := t.property.1
  have hL := L.duration_pos
  dsimp [intermediateHorizon]
  linarith

theorem time_lt_intermediateHorizon (t : L.Time) :
    (t : ℝ) < L.intermediateHorizon t := by
  have ht := t.property.2
  dsimp [intermediateHorizon]
  linarith

theorem intermediateHorizon_lt (t : L.Time) : L.intermediateHorizon t < L.duration := by
  have ht := t.property.2
  dsimp [intermediateHorizon]
  linarith

/-- Intermediate time, given by `⟨t,t.property.1,(L.time_lt_intermediateHorizon t).le⟩`. -/
def intermediateTime (t : L.Time) : Icc (0 : ℝ) (L.intermediateHorizon t) :=
  ⟨t,t.property.1,(L.time_lt_intermediateHorizon t).le⟩

/-- Shorter time, given by `⟨t,t.property.1,t.property.2.trans_lt hSL⟩`. -/
def shorterTime (S : ℝ) (hSL : S < L.duration) (t : Icc (0 : ℝ) S) : L.Time :=
  ⟨t,t.property.1,t.property.2.trans_lt hSL⟩

/-- Maximal field, given by `(L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos
t) (L.intermediateHorizon_lt t)).velocity (L.intermediateTime t)`. -/
def maximalField (t : L.Time) : SmoothL2Field Space :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).velocity (L.intermediateTime t)

/-- Maximal pressure field as an element of `SmoothL2Field Space`. -/
def maximalPressureField (t : L.Time) : SmoothL2Field Space :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).pressureForce (L.intermediateTime t)

theorem maximalFields_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalField (L.shorterTime S hSL t)=(L.evolution S hS hSL).velocity t ∧
      L.maximalPressureField (L.shorterTime S hSL t) =
        (L.evolution S hS hSL).pressureForce t := by
  let u := L.shorterTime S hSL t
  let M := L.intermediateHorizon u
  by_cases hSM : S ≤ M
  · exact L.evolution_agrees S M hS (L.intermediateHorizon_pos u) hSL
      (L.intermediateHorizon_lt u) hSM t
  · have hMS : M ≤ S := (lt_of_not_ge hSM).le
    have h := L.evolution_agrees M S (L.intermediateHorizon_pos u) hS
      (L.intermediateHorizon_lt u) hSL hMS (L.intermediateTime u)
    exact ⟨h.1.symm,h.2.symm⟩

theorem maximalField_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalField (L.shorterTime S hSL t)=(L.evolution S hS hSL).velocity t :=
  (L.maximalFields_eq_evolution S hS hSL t).1

theorem maximalPressureField_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalPressureField (L.shorterTime S hSL t)=(L.evolution S hS hSL).pressureForce t :=
  (L.maximalFields_eq_evolution S hS hSL t).2

/-- Continuous restrictions on all shorter initial intervals determine a
continuous curve on the actual half-open lifespan. -/
theorem continuous_of_shorter_restrictions {E : Type*} [TopologicalSpace E]
    (f : L.Time → E)
    (hf : ∀ S (_hS : 0 < S) (hSL : S < L.duration),
      Continuous (fun t : Icc (0 : ℝ) S => f (L.shorterTime S hSL t))) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let M := L.intermediateHorizon t
  have hM : 0 < M := L.intermediateHorizon_pos t
  have hML : M < L.duration := L.intermediateHorizon_lt t
  have hg : Continuous (fun s : L.Time =>
      f (L.shorterTime M hML (projIcc 0 M hM.le (s : ℝ)))) :=
    (hf M hM hML).comp (continuous_projIcc.comp continuous_subtype_val)
  apply hg.continuousAt.congr_of_eventuallyEq
  have hn : ∀ᶠ s : L.Time in 𝓝 t, (s : ℝ) < M :=
    continuous_subtype_val.continuousAt (Iio_mem_nhds (L.time_lt_intermediateHorizon t))
  filter_upwards [hn] with s hs
  rw [projIcc_of_mem hM.le ⟨s.property.1,hs.le⟩]
  rfl

theorem maximalField_jet_continuous (n : ℕ) :
    Continuous (fun t : L.Time => (L.maximalField t).jetLp n) := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  have he : (fun t : Icc (0 : ℝ) S =>
      (L.maximalField (L.shorterTime S hSL t)).jetLp n) =
      (fun t => ((L.evolution S hS hSL).velocity t).jetLp n) := by
    funext t
    rw [L.maximalField_eq_evolution S hS hSL t]
  rw [he]
  exact (L.evolution S hS hSL).velocity_continuous n

theorem maximalPressureField_jet_continuous (n : ℕ) :
    Continuous (fun t : L.Time => (L.maximalPressureField t).jetLp n) := by
  apply L.continuous_of_shorter_restrictions
  intro S hS hSL
  have he : (fun t : Icc (0 : ℝ) S =>
      (L.maximalPressureField (L.shorterTime S hSL t)).jetLp n) =
      (fun t => ((L.evolution S hS hSL).pressureForce t).jetLp n) := by
    funext t
    rw [L.maximalPressureField_eq_evolution S hS hSL t]
  rw [he]
  exact (L.evolution S hS hSL).pressure_continuous n

theorem maximalField_initial : L.maximalField L.initialTime=A :=
  L.evolution_initial (L.intermediateHorizon L.initialTime)
    (L.intermediateHorizon_pos L.initialTime) (L.intermediateHorizon_lt L.initialTime)

theorem maximalField_solenoidal (t : L.Time) : (L.maximalField t).toLp ∈ solenoidalSpace :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).solenoidal (L.intermediateTime t)

theorem maximalPressureField_gradient (t : L.Time) :
    (L.maximalPressureField t).toLp ∈ gradientSpace :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).gradient (L.intermediateTime t)

/-- Maximal velocity, given by `(L.maximalField t).field`. -/
def maximalVelocity (t : L.Time) : Space → Space := (L.maximalField t).field

/-- Maximal pressure, given by `EulerCanonicalGraphPotential.radialPotential
(L.maximalPressureField t).field`. -/
def maximalPressure (t : L.Time) : Space → ℝ :=
  EulerCanonicalGraphPotential.radialPotential (L.maximalPressureField t).field

theorem maximalVelocity_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalVelocity (L.shorterTime S hSL t)=((L.evolution S hS hSL).velocity t).field := by
  exact congrArg SmoothL2Field.field (L.maximalField_eq_evolution S hS hSL t)

theorem maximalPressure_eq_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : Icc (0 : ℝ) S) :
    L.maximalPressure (L.shorterTime S hSL t)=(L.evolution S hS hSL).scalarPressure t := by
  simp only [maximalPressure,Evolution.scalarPressure,
    L.maximalPressureField_eq_evolution S hS hSL t]

theorem maximalVelocity_initial : L.maximalVelocity L.initialTime=A.field :=
  congrArg SmoothL2Field.field L.maximalField_initial

theorem maximalVelocity_smooth (t : L.Time) : ContDiff ℝ ∞ (L.maximalVelocity t) :=
  (L.maximalField t).smooth

theorem maximalVelocity_joint_continuous :
    Continuous (fun z : L.Time × Space => L.maximalVelocity z.1 z.2) := by
  have h : Continuous (fun z : L.Time × Space =>
      EulerMeanSobolevBoundedField.finiteField (L.maximalField z.1)) :=
    (EulerMeanSobolevBoundedField.continuous_finiteField L.maximalField
      L.maximalField_jet_continuous).comp continuous_fst
  simpa only [EulerMeanSobolevBoundedField.finiteField_apply,maximalVelocity] using
    h.eval continuous_snd

theorem maximalPressureField_joint_continuous :
    Continuous (fun z : L.Time × Space => (L.maximalPressureField z.1).field z.2) := by
  have h : Continuous (fun z : L.Time × Space =>
      EulerMeanSobolevBoundedField.finiteField (L.maximalPressureField z.1)) :=
    (EulerMeanSobolevBoundedField.continuous_finiteField L.maximalPressureField
      L.maximalPressureField_jet_continuous).comp continuous_fst
  simpa only [EulerMeanSobolevBoundedField.finiteField_apply] using h.eval continuous_snd

theorem maximalVelocity_divergence (t : L.Time) (x : Space) :
    divergence (L.maximalVelocity t) x=0 :=
  solenoidal_representative_divergence _ (L.maximalField_solenoidal t) _
    (L.maximalField t).smooth (L.maximalField t).toLp_ae x

theorem maximalPressure_spec (t : L.Time) :
    ContDiff ℝ ∞ (L.maximalPressure t) ∧ L.maximalPressure t 0=0 ∧
      ∀ x, _root_.gradient (L.maximalPressure t) x=(L.maximalPressureField t).field x :=
  (L.evolution (L.intermediateHorizon t) (L.intermediateHorizon_pos t)
    (L.intermediateHorizon_lt t)).scalarPressure_spec (L.intermediateTime t)

/-- Every compact initial subinterval is exactly an actual Euler evolution,
with both its velocity and its pressure force equal to the maximal fields. -/
theorem maximal_restriction_is_evolution (S : ℝ) (hS : 0 < S) (hSL : S < L.duration) :
    ∃ U : Evolution S hS.le,
      U.velocity=(fun t => L.maximalField (L.shorterTime S hSL t)) ∧
      U.pressureForce=(fun t => L.maximalPressureField (L.shorterTime S hSL t)) ∧
      U.velocity ⟨0,le_rfl,hS.le⟩=A :=
  ⟨L.evolution S hS hSL,
    funext (fun t => (L.maximalField_eq_evolution S hS hSL t).symm),
    funext (fun t => (L.maximalPressureField_eq_evolution S hS hSL t).symm),
    L.evolution_initial S hS hSL⟩

theorem maximalVelocity_time_law (S : ℝ) (hS : 0 < S) (hSL : S < L.duration)
    (t : ℝ) (ht : t ∈ Ioo 0 S) (x : Space) :
    HasDerivAt (fun r => L.maximalVelocity
      (L.shorterTime S hSL (projIcc 0 S hS.le r)) x)
      (-fderiv ℝ (L.maximalVelocity (L.shorterTime S hSL ⟨t,ht.1.le,ht.2.le⟩)) x
        (L.maximalVelocity (L.shorterTime S hSL ⟨t,ht.1.le,ht.2.le⟩) x) -
        _root_.gradient (L.maximalPressure (L.shorterTime S hSL ⟨t,ht.1.le,ht.2.le⟩)) x) t := by
  rw [(L.maximalPressure_spec (L.shorterTime S hSL ⟨t,ht.1.le,ht.2.le⟩)).2.2 x,
    L.maximalPressureField_eq_evolution S hS hSL]
  simpa only [L.maximalVelocity_eq_evolution S hS hSL] using
    (L.evolution S hS hSL).time_law t ht x

end EulerOrdinarySobolev.FiniteLifespan
