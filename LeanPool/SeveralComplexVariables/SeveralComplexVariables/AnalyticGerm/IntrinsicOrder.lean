/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Rename
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.Order

/-!
# Coordinate-independent order of analytic germs

`inCoordinates` transports a germ to a finite coordinate space. `orderInCoordinates` is
independent of the continuous complex-linear coordinates, so `intrinsicOrder` defines total
order on every finite-dimensional complex normed space, including zero-dimensional spaces. The
coordinate Taylor implementation remains in `Order`. `finiteIndexTaylorSeries` supplies a Taylor
series indexed by any finite coordinate type.

## Main definitions

* `inCoordinates`: Express a germ in continuous complex-linear coordinates, by pulling back the
  inverse map.
* `orderInCoordinates`: The total order computed in a chosen system of continuous linear
  coordinates.
* `intrinsicOrder`: Total order of an analytic germ on a finite-dimensional complex normed space.
* `finiteIndexTaylorSeries`: Taylor series with variables indexed by an arbitrary finite coordinate
  type.

## Main results

* `intrinsicOrder_eq_orderInCoordinates`: Intrinsic order can be computed using any continuous
  complex-linear coordinate system.
* `intrinsicOrder_eq_order`: Intrinsic order agrees with the original order on finite coordinate
  spaces.
* `intrinsicOrder_mul`: Intrinsic order is additive under multiplication.
* `intrinsicOrder_eq_top_iff`: A germ has infinite intrinsic order exactly when it is zero.
-/

public noncomputable section
open Filter
open scoped Topology
namespace SeveralComplexVariables.AnalyticGerm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E} {n m : ℕ}

/-- Express a germ in continuous complex-linear coordinates, by pulling back the inverse map. -/
def inCoordinates (L : E ≃L[ℂ] (Fin n → ℂ)) (x : E) :
    AnalyticGerm ℂ x ≃ₐ[ℂ] AnalyticGerm ℂ (L x) :=
  pullbackEquivOfEq L.symm.toHomeomorph (L x)
    (L.symm.toContinuousLinearMap.analyticAt _) (L.toContinuousLinearMap.analyticAt _)
    (L.symm_apply_apply x)

/-- A represented germ in coordinates is represented by composition with the inverse map. -/
theorem inCoordinates_ofAnalyticAt (L : E ≃L[ℂ] (Fin n → ℂ))
    (f : E → ℂ) (hf : AnalyticAt ℂ f x) :
    inCoordinates L x (ofAnalyticAt f hf) =
      ofAnalyticAt (f ∘ L.symm)
        (hf.comp_of_eq (L.symm.toContinuousLinearMap.analyticAt _) (L.symm_apply_apply x)) :=
  pullbackEquivOfEq_ofAnalyticAt _ _ _ _ _ _ _

/-- The total order computed in a chosen system of continuous linear coordinates. -/
@[expose] def orderInCoordinates (L : E ≃L[ℂ] (Fin n → ℂ)) (f : AnalyticGerm ℂ x) : ℕ∞ :=
  order (inCoordinates L x f)

/-- Comparing two coordinate systems cannot lower the computed order. -/
private theorem orderInCoordinates_le (L : E ≃L[ℂ] (Fin n → ℂ))
    (M : E ≃L[ℂ] (Fin m → ℂ)) (f : AnalyticGerm ℂ x) :
    orderInCoordinates L f ≤ orderInCoordinates M f := by
  obtain ⟨f, hf, rfl⟩ := exists_rep f
  let e := M.symm.trans L
  have ha : AnalyticAt ℂ (f ∘ L.symm) (e (M x)) := by
    simpa [e] using hf.comp_of_eq (L.symm.toContinuousLinearMap.analyticAt (L x))
      (L.symm_apply_apply x)
  have h := order_le_order_pullback e (e.toContinuousLinearMap.analyticAt (M x))
    (ofAnalyticAt (f ∘ L.symm) ha)
  change (holomorphicTaylorSeries (f ∘ L.symm) (e (M x))).order ≤
    (holomorphicTaylorSeries ((f ∘ L.symm) ∘ e) (M x)).order at h
  unfold orderInCoordinates
  rw [inCoordinates_ofAnalyticAt L f hf, inCoordinates_ofAnalyticAt M f hf]
  simpa only [order, taylorSeries_ofAnalyticAt, e, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.symm_apply_apply, Function.comp_def] using h

/-- Total order is independent of the chosen continuous complex-linear coordinates. -/
theorem orderInCoordinates_eq (L : E ≃L[ℂ] (Fin n → ℂ))
    (M : E ≃L[ℂ] (Fin m → ℂ)) (f : AnalyticGerm ℂ x) :
    orderInCoordinates L f = orderInCoordinates M f :=
  le_antisymm (orderInCoordinates_le L M f) (orderInCoordinates_le M L f)

variable [FiniteDimensional ℂ E]

/-- Total order of an analytic germ on a finite-dimensional complex normed space. The chosen basis
in the implementation does not affect its value. -/
@[expose] def intrinsicOrder (f : AnalyticGerm ℂ x) : ℕ∞ :=
  orderInCoordinates (Module.finBasis ℂ E).equivFunL f

/-- Intrinsic order can be computed using any continuous complex-linear coordinate system. -/
theorem intrinsicOrder_eq_orderInCoordinates (L : E ≃L[ℂ] (Fin n → ℂ))
    (f : AnalyticGerm ℂ x) : intrinsicOrder f = orderInCoordinates L f :=
  orderInCoordinates_eq _ _ f

/-- Intrinsic order agrees with the original order on finite coordinate spaces. -/
@[simp] theorem intrinsicOrder_eq_order {x : Fin n → ℂ} (f : AnalyticGerm ℂ x) :
    intrinsicOrder f = order f := by
  rw [intrinsicOrder_eq_orderInCoordinates (ContinuousLinearEquiv.refl ℂ (Fin n → ℂ))]
  obtain ⟨g, hg, rfl⟩ := exists_rep f
  unfold orderInCoordinates
  rw [inCoordinates_ofAnalyticAt _ g hg]
  rfl

/-- A germ has infinite intrinsic order exactly when it is zero. -/
@[simp] theorem intrinsicOrder_eq_top_iff (f : AnalyticGerm ℂ x) :
    intrinsicOrder f = ⊤ ↔ f = 0 := by
  rw [intrinsicOrder, orderInCoordinates, order_eq_top_iff]
  exact (inCoordinates (Module.finBasis ℂ E).equivFunL x).map_eq_zero_iff

/-- Intrinsic order is additive under multiplication. -/
theorem intrinsicOrder_mul (f g : AnalyticGerm ℂ x) :
    intrinsicOrder (f * g) = intrinsicOrder f + intrinsicOrder g := by
  simp only [intrinsicOrder, orderInCoordinates, map_mul, order_mul]

/-- Cancellation can only raise the intrinsic order of a sum. -/
theorem min_intrinsicOrder_le_intrinsicOrder_add (f g : AnalyticGerm ℂ x) :
    min (intrinsicOrder f) (intrinsicOrder g) ≤ intrinsicOrder (f + g) := by
  simpa only [intrinsicOrder, orderInCoordinates, map_add] using
    min_order_le_order_add (inCoordinates (Module.finBasis ℂ E).equivFunL x f)
      (inCoordinates (Module.finBasis ℂ E).equivFunL x g)

/-- Taylor series with variables indexed by an arbitrary finite coordinate type. A finite
enumeration is used for the ordered derivative implementation, then the formal variables are
renamed back to the original coordinate type. -/
def finiteIndexTaylorSeries {ι : Type*} [Fintype ι] {x : ι → ℂ}
    (f : AnalyticGerm ℂ x) : MvPowerSeries ι ℂ :=
  MvPowerSeries.renameEquiv ℂ (Fintype.equivFin ι).symm
    (taylorSeries (inCoordinates
      (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Fin (Fintype.card ι) => ℂ)
        (Fintype.equivFin ι)) x f))

end SeveralComplexVariables.AnalyticGerm
end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
