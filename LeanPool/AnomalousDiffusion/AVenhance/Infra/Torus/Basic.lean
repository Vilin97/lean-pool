/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.IsZ2Periodic
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.UnitCube

/-! Basic measurable and periodic infrastructure for the unit torus. -/

@[expose] public section

noncomputable section

open MeasureTheory Set

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraTorusBasicMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusBasicMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusBasicIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Torus

open Homogenization

/-- A translated half-open fundamental cell `(aᵢ,aᵢ+1]^d`. -/
def unitCellAt (d : ℕ) (a : Fin d → ℝ) : Set (Vec d) :=
  {x | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)}

/-- The half-open fundamental cell `(0,1]^d`. This convention matches
`UnitAddTorus.measurableEquivPiIoc` and gives an exact fundamental domain. -/
def unitCell (d : ℕ) : Set (Vec d) := unitCellAt d (fun _ => 0)

theorem measurableSet_unitCellAt (d : ℕ) (a : Fin d → ℝ) :
    MeasurableSet (unitCellAt d a) := by
  simpa [unitCellAt] using MeasurableSet.univ_pi'
    (fun i => (measurableSet_Ioc : MeasurableSet (Set.Ioc (a i) (a i + 1))))

theorem measurableSet_unitCell (d : ℕ) : MeasurableSet (unitCell d) := by
  rw [unitCell]
  exact measurableSet_unitCellAt d (fun _ => 0)

/-- The integer vector `k`, viewed as a real vector. -/
def intVector {d : ℕ} (k : Fin d → ℤ) : Vec d := fun i => (k i : ℝ)

/-- A function is `ℤ^d`-periodic if integer translations leave it unchanged. -/
def IsZdPeriodic {d : ℕ} {α : Type*} (f : Vec d → α) : Prop :=
  ∀ k : Fin d → ℤ, ∀ x : Vec d, f (x + intVector k) = f x

/-- In dimension two, the generic periodicity predicate agrees with the paper carrier. -/
theorem isZdPeriodic_iff_frozen {α : Type*} (f : Vec 2 → α) :
    IsZdPeriodic f ↔ AVenhance.IsZ2Periodic f := by
  constructor
  · intro h n x
    exact h n x
  · intro h n x
    exact h n x

/-- The open and half-open unit cells agree almost everywhere for Lebesgue measure. -/
theorem unitCell_ae_eq_unitCube :
    unitCell 2 =ᵐ[(volume : Measure (Vec 2))] AVenhance.unitCube := by
  have h₁ :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Ioo (0 : ℝ) 1) =ᵐ[volume]
        Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1 := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioo_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ)))
  have h₂ :
      (Set.pi Set.univ fun _ : Fin 2 => Set.Icc (0 : ℝ) 1) =ᵐ[volume]
        (Set.pi Set.univ fun _ : Fin 2 => Set.Ioc (0 : ℝ) 1) := by
    simpa [volume_pi] using
      (Measure.univ_pi_Ioc_ae_eq_Icc (f := fun _ : Fin 2 => (0 : ℝ))
        (g := fun _ : Fin 2 => (1 : ℝ))).symm
  simpa [unitCell, unitCellAt, AVenhance.unitCube, Set.pi] using (h₁.trans h₂).symm

/-- Set integrals over the generic half-open cell and the open square agree. -/
theorem integral_unitCell_eq_unitCube {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → E) :
    ∫ x in unitCell 2, f x = ∫ x in AVenhance.unitCube, f x := by
  exact setIntegral_congr_set unitCell_ae_eq_unitCube

/-- The quotient map from Euclidean coordinates to the unit additive torus. -/
def toUnitTorus (d : ℕ) (x : Vec d) : UnitAddTorus (Fin d) :=
  fun i => (x i : UnitAddCircle)

/-- The representative of a torus point in the half-open cell `(0,1]^d`. -/
def unitTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) : Vec d :=
  fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (x i)).1 : ℝ)

/-- Transfer a Euclidean function to the torus by taking its canonical cell representative. -/
def periodicToTorus {d : ℕ} {α : Type*}
    (f : Vec d → α) : UnitAddTorus (Fin d) → α :=
  fun x => f (unitTorusRepresentative d x)

/-- Pull a torus function back to a function on Euclidean coordinates. -/
def fromUnitTorus {d : ℕ} {α : Type*}
    (f : UnitAddTorus (Fin d) → α) : Vec d → α :=
  fun x => f (toUnitTorus d x)

@[simp]
theorem unitTorusRepresentative_toUnitTorus (d : ℕ) (x : Vec d) :
    unitTorusRepresentative d (toUnitTorus d x) =
      fun i => ((AddCircle.equivIoc (1 : ℝ) 0 (x i : UnitAddCircle)).1 : ℝ) := rfl

theorem unitTorusRepresentative_eq_of_mem_unitCell {d : ℕ} {x : Vec d}
    (hx : x ∈ unitCell d) : unitTorusRepresentative d (toUnitTorus d x) = x := by
  funext i
  have hi : x i ∈ Set.Ioc (0 : ℝ) (0 + 1) := hx i
  have h := AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) (x := x i) hi
  exact congrArg Subtype.val h

theorem Basic.representative_int_translate {d : ℕ} (x : Vec d) :
    ∃ k : Fin d → ℤ, unitTorusRepresentative d (toUnitTorus d x) = x + intVector k := by
  classical
  have hi : ∀ i : Fin d, ∃ k : ℤ,
      (k : ℝ) = unitTorusRepresentative d (toUnitTorus d x) i - x i := by
    intro i
    have hclass :
        ((unitTorusRepresentative d (toUnitTorus d x) i - x i : ℝ) : UnitAddCircle) = 0 := by
      rw [AddCircle.coe_sub]
      simp [unitTorusRepresentative, toUnitTorus]
    rw [AddCircle.coe_eq_zero_iff] at hclass
    obtain ⟨k, hk⟩ := hclass
    refine ⟨k, ?_⟩
    simpa only [zsmul_eq_mul, mul_one] using hk
  let k : Fin d → ℤ := fun i => Classical.choose (hi i)
  refine ⟨k, ?_⟩
  funext i
  have hk := Classical.choose_spec (hi i)
  dsimp [k, intVector]
  calc
    unitTorusRepresentative d (toUnitTorus d x) i =
        x i + (unitTorusRepresentative d (toUnitTorus d x) i - x i) := by ring
    _ = x i + (k i : ℝ) := by rw [← hk]

/-- Transferring a periodic function to the torus and pulling it back recovers it. -/
theorem fromUnitTorus_periodicToTorus {d : ℕ} {α : Type*}
    {f : Vec d → α} (hf : IsZdPeriodic f) :
    fromUnitTorus (periodicToTorus f) = f := by
  funext x
  obtain ⟨k, hk⟩ := Basic.representative_int_translate x
  rw [fromUnitTorus, periodicToTorus, hk, hf k x]

/-- Pulling back a torus function always gives a `ℤ^d`-periodic function. -/
theorem isZdPeriodic_fromUnitTorus {d : ℕ} {α : Type*} (f : UnitAddTorus (Fin d) → α)
    : IsZdPeriodic (fromUnitTorus f) := by
  intro k x
  unfold fromUnitTorus
  congr 1
  funext i
  change ((x i + (k i : ℝ) : ℝ) : UnitAddCircle) = (x i : UnitAddCircle)
  rw [AddCircle.coe_add]
  have hk : ((k i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k i, by simp⟩
  rw [hk, add_zero]

/-- A torus point is recovered from the canonical representative of that point. -/
@[simp]
theorem toUnitTorus_unitTorusRepresentative (d : ℕ) (x : UnitAddTorus (Fin d)) :
    toUnitTorus d (unitTorusRepresentative d x) = x := by
  funext i
  change ((AddCircle.equivIoc (1 : ℝ) 0 (x i)).1 : UnitAddCircle) = x i
  exact AddCircle.coe_equivIoc

/-- Pulling back the transfer of a torus function gives the original torus function. -/
@[simp]
theorem periodicToTorus_fromUnitTorus {d : ℕ} {α : Type*}
    (f : UnitAddTorus (Fin d) → α) : periodicToTorus (fromUnitTorus f) = f := by
  funext x
  change f (toUnitTorus d (unitTorusRepresentative d x)) = f x
  rw [toUnitTorus_unitTorusRepresentative]

/-- Integration on the torus agrees with integration of the pullback over a translated unit cell.
The cell is half-open, as in Mathlib's fundamental-domain measure equivalence. -/
theorem integral_fromUnitTorus_eq_unitCellAt {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : UnitAddTorus (Fin d) → E) (a : Fin d → ℝ) :
    ∫ x : UnitAddTorus (Fin d), f x = ∫ x in unitCellAt d a, fromUnitTorus f x := by
  change ∫ x : UnitAddTorus (Fin d), f x =
    ∫ x in {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (a i) (a i + 1)},
      f (fun i => (x i : UnitAddCircle))
  exact UnitAddTorus.integral_preimage (d := Fin d) f a

/-- Integration on the torus agrees with integration of the periodic transfer on the unit cell. -/
theorem integral_periodicToTorus_eq_unitCell {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : Vec d → E) :
    ∫ x : UnitAddTorus (Fin d), periodicToTorus f x = ∫ x in unitCell d, f x := by
  calc
    ∫ x : UnitAddTorus (Fin d), periodicToTorus f x =
        ∫ x in unitCellAt d (fun _ => 0), fromUnitTorus (periodicToTorus f) x :=
      integral_fromUnitTorus_eq_unitCellAt (periodicToTorus f) (fun _ => 0)
    _ = ∫ x in unitCell d, fromUnitTorus (periodicToTorus f) x := rfl
    _ = ∫ x in unitCell d, f x := by
      apply setIntegral_congr_ae (measurableSet_unitCell d)
      filter_upwards with x hx
      have hrep : unitTorusRepresentative d (toUnitTorus d x) = x :=
        unitTorusRepresentative_eq_of_mem_unitCell hx
      simp [fromUnitTorus, periodicToTorus, hrep]

/-- Integrals of a periodic function over any translated half-open unit cell agree. -/
theorem integral_periodic_unitCellAt_eq {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Vec d → E}
    (hf : IsZdPeriodic f) (a : Fin d → ℝ) :
    ∫ x in unitCellAt d a, f x =
      ∫ x in unitCell d, f x := by
  calc
    ∫ x in unitCellAt d a, f x =
        ∫ x in unitCellAt d a,
          fromUnitTorus (periodicToTorus f) x := by
            apply setIntegral_congr_fun (measurableSet_unitCellAt d a)
            intro x hx
            exact congrFun (fromUnitTorus_periodicToTorus hf) x |>.symm
    _ = ∫ x : UnitAddTorus (Fin d), periodicToTorus f x :=
      (integral_fromUnitTorus_eq_unitCellAt (periodicToTorus f) a).symm
    _ = ∫ x in unitCell d, f x := integral_periodicToTorus_eq_unitCell f

end AVenhance.Infra.Torus
