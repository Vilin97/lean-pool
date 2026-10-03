/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Torus.Basic

/-! Fourier coefficients and Parseval on the unit torus and its Euclidean cell. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance avInfraTorusFourierMeasureSpace1 : MeasureSpace UnitAddCircle :=
    ⟨AddCircle.haarAddCircle⟩
local instance avInfraTorusFourierMeasureIsAddHaarMeasure2 : Measure.IsAddHaarMeasure (volume :
    Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance avInfraTorusFourierIsProbabilityMeasure3 : IsProbabilityMeasure (volume : Measure
    UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Torus

/-- The `L²` space on the unit torus. -/
abbrev TorusL2 (d : ℕ) := Lp ℂ 2 (volume : Measure (UnitAddTorus (Fin d)))

/-- The periodic Euclidean representative of an `L²` torus function. -/
def periodicL2Representative {d : ℕ} (f : TorusL2 d) : Vec d → ℂ :=
  fromUnitTorus (fun x => f x)

/-- The `k`th Fourier coefficient of a torus `L²` function, using Mathlib's `mFourierCoeff`. -/
def periodicL2FourierCoeff {d : ℕ} (f : TorusL2 d) (k : Fin d → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (fun x => f x) k

/-- Parseval's identity for a periodic `L²` function, integrated over the Euclidean unit cell. -/
theorem hasSum_sq_periodicL2FourierCoeff {d : ℕ} (f : TorusL2 d) :
    HasSum (fun k : Fin d → ℤ => ‖periodicL2FourierCoeff f k‖ ^ 2)
      (∫ x in unitCell d, ‖periodicL2Representative f x‖ ^ 2) := by
  have hcell :
      (∫ x : UnitAddTorus (Fin d), ‖f x‖ ^ 2) =
        ∫ x in unitCell d, ‖periodicL2Representative f x‖ ^ 2 := by
    calc
      _ = ∫ x in unitCell d, fromUnitTorus (fun y : UnitAddTorus (Fin d) => ‖f y‖ ^ 2) x := by
        simpa [unitCell] using
          (integral_fromUnitTorus_eq_unitCellAt
            (fun y : UnitAddTorus (Fin d) => ‖f y‖ ^ 2) (fun _ => 0))
      _ = ∫ x in unitCell d, ‖periodicL2Representative f x‖ ^ 2 := rfl
  convert UnitAddTorus.hasSum_sq_mFourierCoeff f using 1
  · rfl
  · exact hcell.symm

end AVenhance.Infra.Torus
