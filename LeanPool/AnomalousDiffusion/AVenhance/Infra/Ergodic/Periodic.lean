/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import Mathlib.Analysis.Fourier.AddCircleMulti

/-! # Periodicity for functions on Euclidean space

This local predicate records invariance under the integer lattice.  The
ergodic lemmas use it for scalar functions on `Vec d`.
-/

@[expose] public section

namespace AVenhance.Infra.Ergodic

open MeasureTheory

noncomputable section

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraErgodicPeriodicMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩

local instance avInfraErgodicPeriodicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance avInfraErgodicPeriodicIsProbabilityMeasure3 : IsProbabilityMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A function on `Vec d` is `ℤ^d`-periodic when it is invariant under every
integer lattice translation. -/
def IsZPeriodic {d : ℕ} {α : Type*} (f : Homogenization.Vec d → α) : Prop :=
  ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    f (x + fun i => (k i : ℝ)) = f x

/-- The Euclidean vector represented by an integer lattice vector. -/
def latticeVector {d : ℕ} (k : Fin d → ℤ) : Homogenization.Vec d :=
  fun i => (k i : ℝ)

/-- In dimension two, the local ergodic periodicity predicate agrees with
the campaign carrier. -/
theorem isZPeriodic_iff_isZ2Periodic {α : Type*} (f : Homogenization.Vec 2 → α) :
    IsZPeriodic f ↔ AVenhance.IsZ2Periodic f := by
  constructor
  · intro hf k x
    exact hf x k
  · intro hf x k
    exact hf k x

/-- Invariance under translations in `N⁻¹ℤ^d`. -/
def IsFastPeriodic {d : ℕ} (N : ℕ) (f : Homogenization.Vec d → ℝ) : Prop :=
  ∀ (x : Homogenization.Vec d) (k : Fin d → ℤ),
    f (x + fun i => (k i : ℝ) / (N : ℝ)) = f x

theorem IsFastPeriodic.isZPeriodic {d : ℕ} {N : ℕ} {f : Homogenization.Vec d → ℝ}
    (hN : 0 < N) (hf : IsFastPeriodic N f) : IsZPeriodic f := by
  intro x k
  have hscale : (fun i => (((N : ℤ) * k i : ℤ) : ℝ) / (N : ℝ)) =
      (fun i => (k i : ℝ)) := by
    funext i
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    simp only [Int.cast_mul, Int.cast_natCast]
    field_simp
  simpa only [hscale] using hf x (fun i => (N : ℤ) * k i)

/-- The unit torus with coordinates indexed by `Fin d`. -/
abbrev UnitTorus (d : ℕ) := UnitAddTorus (Fin d)

/-- The half-open unit cell used to compute spatial averages. -/
def unitCellSet (d : ℕ) : Set (Homogenization.Vec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

/-- The representative in `(0,1]^d` of a point on the unit torus. -/
def unitCellRepresentative {d : ℕ} (x : UnitTorus d) : Homogenization.Vec d :=
  (UnitAddTorus.measurableEquivPiIoc (ι := Fin d) (fun _ => (0 : ℝ)) x).val

/-- Translation by one fast period in coordinate `i` on the unit torus. -/
def fastTorusShift {d : ℕ} (N : ℕ) (i : Fin d) : UnitTorus d :=
  fun j => ((if j = i then (1 : ℝ) / (N : ℝ) else 0) : UnitAddCircle)

/-- Translation by the reciprocal frequency in one coordinate direction. -/
def Periodic.fastRealShift {d : ℕ} (N : ℕ) (i : Fin d) : Homogenization.Vec d :=
  fun j => if j = i then (1 : ℝ) / (N : ℝ) else 0

/-- The function on the torus obtained by evaluating a Euclidean function at
the canonical unit-cell representative. For a `IsZPeriodic` function this
representative is immaterial up to the usual boundary identifications. -/
def torusFunction {d : ℕ} {α : Type*} (f : Homogenization.Vec d → α)
    (x : UnitTorus d) : α :=
  f (unitCellRepresentative x)

theorem Periodic.unitCellRepresentative_add_fastTorusShift
    {d N : ℕ} (hN : 0 < N) (i : Fin d) (x : UnitTorus d) :
    ∃ k : Fin d → ℤ,
      unitCellRepresentative (x + fastTorusShift N i) =
        unitCellRepresentative x + fun j =>
          (((if j = i then (1 : ℤ) else 0) + (N : ℤ) * k j : ℤ) : ℝ) / (N : ℝ) := by
  classical
  let y := unitCellRepresentative x
  let z := unitCellRepresentative (x + fastTorusShift N i)
  have hcoord : ∀ j : Fin d, (z j : UnitAddCircle) =
      (y j + Periodic.fastRealShift N i j : ℝ) := by
    intro j
    by_cases hji : j = i <;>
      simp [z, y, unitCellRepresentative, fastTorusShift, Periodic.fastRealShift, hji]
  have hcoords : ∀ j : Fin d, ∃ m : ℤ,
      z j = y j + Periodic.fastRealShift N i j + (m : ℝ) := by
    intro j
    have hzero : ((z j - (y j + Periodic.fastRealShift N i j) : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub, hcoord j]
      simp
    obtain ⟨m, hm⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
    refine ⟨m, ?_⟩
    have hm' : (m : ℝ) = z j - (y j + Periodic.fastRealShift N i j) := by
      simpa [zsmul_eq_mul] using hm
    linarith
  choose k hk using hcoords
  refine ⟨k, ?_⟩
  funext j
  change z j = y j +
    ((((if j = i then (1 : ℤ) else 0) + (N : ℤ) * k j : ℤ) : ℝ) / (N : ℝ))
  rw [hk j]
  by_cases hji : j = i
  · subst j
    simp [Periodic.fastRealShift]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp
    ring
  · simp [Periodic.fastRealShift, hji]
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    field_simp

theorem torusFunction_add_fastTorusShift_eq
    {d N : ℕ} {f : Homogenization.Vec d → ℝ} (hN : 0 < N)
    (hf : IsFastPeriodic N f) (i : Fin d) (x : UnitTorus d) :
    torusFunction f (x + fastTorusShift N i) = torusFunction f x := by
  obtain ⟨k, hk⟩ := Periodic.unitCellRepresentative_add_fastTorusShift hN i x
  rw [torusFunction, hk]
  let q : Fin d → ℤ := fun j => if j = i then 1 else 0
  change f (unitCellRepresentative x + fun j =>
    (((q j + (N : ℤ) * k j : ℤ) : ℤ) : ℝ) / (N : ℝ)) = _
  exact hf (unitCellRepresentative x) (fun j => q j + (N : ℤ) * k j)

/-- The normalized average of a Euclidean function over the unit torus,
computed using its canonical representative in `(0,1]^d`. -/
def cellAverage {d : ℕ} (f : Homogenization.Vec d → ℝ) : ℝ :=
  ∫ x : UnitTorus d, torusFunction f x

@[simp]
theorem cellAverage_const {d : ℕ} (c : ℝ) :
    cellAverage (fun _ : Homogenization.Vec d => c) = c := by
  simp [cellAverage, torusFunction]

theorem cellAverage_eq_torus_integral {d : ℕ} (f : Homogenization.Vec d → ℝ) :
    cellAverage f = ∫ x : UnitTorus d, torusFunction f x := rfl

theorem cellAverage_eq_unitCellIntegral {d : ℕ}
    {f : Homogenization.Vec d → ℝ} :
    cellAverage f = ∫ x in unitCellSet d, f x := by
  unfold cellAverage
  change (∫ x : UnitAddTorus (Fin d), torusFunction f x) = _
  calc
    _ = ∫ (x : Fin d → ℝ) in
        {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1},
        torusFunction f (fun i => (x i : UnitAddCircle)) := by
          simpa using (UnitAddTorus.integral_preimage
            (fun x => torusFunction f x) (fun _ : Fin d => (0 : ℝ)))
    _ = ∫ x in unitCellSet d, f x := by
      apply setIntegral_congr_fun
        (MeasurableSet.univ_pi' fun _ => measurableSet_Ioc)
      intro x hx
      have hrep : unitCellRepresentative (fun i => (x i : UnitAddCircle)) = x := by
        funext i
        have hxi : x i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1) := by
          simpa using hx i
        simpa [unitCellRepresentative] using
          AddCircle.equivIoc_coe_of_mem (p := (1 : ℝ)) (a := (0 : ℝ)) hxi
      change f (unitCellRepresentative (fun i => (x i : UnitAddCircle))) = f x
      exact congrArg f hrep

end

end AVenhance.Infra.Ergodic
