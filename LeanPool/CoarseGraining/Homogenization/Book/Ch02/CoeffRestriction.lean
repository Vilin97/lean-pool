/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.MultiscaleEllipticity

/-! # Coeff Restriction -/

@[expose] public section

namespace Homogenization
namespace Book.Ch02

noncomputable section

namespace CoeffOn

/-- The literal restriction of one coefficient representative to a subcube.

Unlike a coefficient-family compatibility witness, this keeps the same raw
representative and transports only its a.e. data to the smaller cube. -/
noncomputable def restrictToSubcube {d : ℕ} {Q R : TriadicCube d}
    (a : CoeffOn (cubeDomain Q)) (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    CoeffOn (cubeDomain R) where
  toCoeffField := a.toCoeffField
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    intro i j
    have hmeas := (a.aeStronglyMeasurable i j).mono_measure
      (MeasureTheory.Measure.restrict_mono hRQ le_rfl)
    apply hmeas.congr
    filter_upwards [MeasureTheory.ae_restrict_mem
      (measurableSet_openCubeSet R)] with x hx
    simp [restrictCoeffField, hx, hRQ hx]
  aeElliptic :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset hRQ a.aeElliptic

@[simp] theorem restrictToSubcube_toCoeffField {d : ℕ}
    {Q R : TriadicCube d} (a : CoeffOn (cubeDomain Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    (a.restrictToSubcube hRQ).toCoeffField = a.toCoeffField := rfl

theorem restrictToSubcube_restrictsTo {d : ℕ} {Q R : TriadicCube d}
    (a : CoeffOn (cubeDomain Q)) (hRQ : openCubeSet R ⊆ openCubeSet Q) :
    RestrictsTo a (a.restrictToSubcube hRQ) := Filter.EventuallyEq.rfl

theorem restrictToSubcube_trans_aeeq {d : ℕ} {Q R S : TriadicCube d}
    (a : CoeffOn (cubeDomain Q))
    (hRQ : openCubeSet R ⊆ openCubeSet Q)
    (hSR : openCubeSet S ⊆ openCubeSet R) :
    AEEq ((a.restrictToSubcube hRQ).restrictToSubcube hSR)
      (a.restrictToSubcube (hSR.trans hRQ)) := Filter.EventuallyEq.rfl

end CoeffOn

end

end Book.Ch02
end Homogenization
