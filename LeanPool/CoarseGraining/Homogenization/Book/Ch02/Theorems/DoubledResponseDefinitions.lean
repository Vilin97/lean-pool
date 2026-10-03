/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMuDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.ExistenceDefinitions

/-! # Doubled Response Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

namespace DoubledField

theorem SameAE.refl {d : ℕ} {U : Domain d} (X : DoubledField d) :
    SameAE (U := U) X X :=
  ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

theorem SameAE.symm {d : ℕ} {U : Domain d} {X Y : DoubledField d}
    (hXY : SameAE (U := U) X Y) :
    SameAE (U := U) Y X :=
  ⟨hXY.1.symm, hXY.2.symm⟩

theorem SameAE.trans {d : ℕ} {U : Domain d} {X Y Z : DoubledField d}
    (hXY : SameAE (U := U) X Y) (hYZ : SameAE (U := U) Y Z) :
    SameAE (U := U) X Z :=
  ⟨hXY.1.trans hYZ.1, hXY.2.trans hYZ.2⟩

theorem SameAE.add {d : ℕ} {U : Domain d} {X1 X2 Y1 Y2 : DoubledField d}
    (hX : SameAE (U := U) X1 X2) (hY : SameAE (U := U) Y1 Y2) :
    SameAE (U := U) (X1 + Y1) (X2 + Y2) := by
  constructor
  · filter_upwards [hX.1, hY.1] with x hx hy
    change (X1.potential + Y1.potential) x = (X2.potential + Y2.potential) x
    simp [hx, hy]
  · filter_upwards [hX.2, hY.2] with x hx hy
    change (X1.flux + Y1.flux) x = (X2.flux + Y2.flux) x
    simp [hx, hy]

theorem SameAE.smul {d : ℕ} {U : Domain d} (c : ℝ)
    {X Y : DoubledField d} (hXY : SameAE (U := U) X Y) :
    SameAE (U := U) (c • X) (c • Y) := by
  constructor
  · filter_upwards [hXY.1] with x hx
    change (c • X.potential) x = (c • Y.potential) x
    simp [hx]
  · filter_upwards [hXY.2] with x hx
    change (c • X.flux) x = (c • Y.flux) x
    simp [hx]

end DoubledField

theorem doubledResponseIntegrand_ae_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (P Q : BlockVec d) (X : DoubledField d) :
    doubledResponseIntegrand U a P Q X
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        doubledResponseIntegrand U b P Q X :=
  (blockMatrixField_ae_eq_ofAEEq h).mono fun x hx => by
    simp [doubledResponseIntegrand, blockEnergyDensityAt, hx]

theorem doubledResponseValue_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (P Q : BlockVec d) (X : DoubledField d) :
    doubledResponseValue U a P Q X = doubledResponseValue U b P Q X := by
  unfold doubledResponseValue average
  congr 1
  exact MeasureTheory.integral_congr_ae
    (doubledResponseIntegrand_ae_eq_ofAEEq h P Q X)

namespace IsDoubledResponseField

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {X : DoubledField d}
    (hX : IsDoubledResponseField U a X) :
    IsDoubledResponseField U b X := by
  refine ⟨hX.1, ?_⟩
  intro Y hY
  calc
    ∫ x in (U : Set (Vec d)),
        doubledBlockPairingIntegrand U b Y X x ∂MeasureTheory.volume =
      ∫ x in (U : Set (Vec d)),
        doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume := by
        exact MeasureTheory.integral_congr_ae
          (doubledBlockPairingIntegrand_ae_eq_ofAEEq h Y X).symm
    _ = 0 := hX.2 Y hY

end IsDoubledResponseField

theorem doubledResponseValueSet_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (P Q : BlockVec d) :
    doubledResponseValueSet U a P Q = doubledResponseValueSet U b P Q := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX.ofAEEq h, by simp [doubledResponseValue_eq_ofAEEq h P Q X]⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX.ofAEEq h.symm, by simp [doubledResponseValue_eq_ofAEEq h P Q X]⟩

theorem doubledResponseJ_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (P Q : BlockVec d) :
    doubledResponseJ U a P Q = doubledResponseJ U b P Q := by
  unfold doubledResponseJ
  rw [doubledResponseValueSet_eq_ofAEEq h P Q]

namespace IsDoubledResponseMaximizer

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {P Q : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledResponseMaximizer U a P Q X) :
    IsDoubledResponseMaximizer U b P Q X := by
  refine ⟨hX.1.ofAEEq h, ?_⟩
  intro Y hY
  have hYa : IsDoubledResponseField U a Y := hY.ofAEEq h.symm
  simpa [doubledResponseValue_eq_ofAEEq h P Q Y,
    doubledResponseValue_eq_ofAEEq h P Q X] using hX.2 Y hYa

end IsDoubledResponseMaximizer

/-- Public theorem package for
`l.block.response.functional.basic.definitions`.

The canonical public theorem proving this package is `doubledResponseTheory`
in `DoubledResponse.lean`. -/
structure DoubledResponseTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop where
  response_space_by_solutions :
    ∀ X : DoubledField d,
      IsDoubledResponseField U a X ↔
        ∃ v : Solution U a, ∃ vStar : Solution U a.transpose,
          DoubledField.SameAE (U := U) X (doubledFieldOfSolutions a v vStar)
  doubled_response_by_scalar :
    ∀ p pStar q qStar : Vec d,
      doubledResponseJ U a (p, q) (qStar, pStar) =
        (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
          (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q)
  scalar_maximizers_give_doubled_maximizer :
    ∀ p pStar q qStar : Vec d,
      ∀ v : Solution U a, ∀ vStar : Solution U a.transpose,
        IsResponseMaximizer U a (p - pStar) (qStar - q) v →
          IsResponseMaximizer U a.transpose (pStar + p) (qStar + q) vStar →
            IsDoubledResponseMaximizer U a (p, q) (qStar, pStar)
              (doubledFieldOfScalarMaximizers a v vStar)
  maximizer_exists :
    ∀ P Q : BlockVec d, DoubledResponseMaximizerExists U a P Q
  maximizer_unique_ae :
    ∀ P Q : BlockVec d, ∀ X Y : DoubledField d,
      IsDoubledResponseMaximizer U a P Q X →
        IsDoubledResponseMaximizer U a P Q Y →
          DoubledField.SameAE (U := U) X Y
  maximizer_add_sameAE :
    ∀ P1 Q1 P2 Q2 : BlockVec d, ∀ X12 X1 X2 : DoubledField d,
      IsDoubledResponseMaximizer U a (P1 + P2) (Q1 + Q2) X12 →
        IsDoubledResponseMaximizer U a P1 Q1 X1 →
          IsDoubledResponseMaximizer U a P2 Q2 X2 →
            DoubledField.SameAE (U := U) X12 (X1 + X2)
  maximizer_smul_sameAE :
    ∀ c : ℝ, ∀ P Q : BlockVec d, ∀ Xc X : DoubledField d,
      IsDoubledResponseMaximizer U a (c • P) (c • Q) Xc →
        IsDoubledResponseMaximizer U a P Q X →
          DoubledField.SameAE (U := U) Xc (c • X)
  first_variation :
    ∀ P Q : BlockVec d, ∀ S T : DoubledField d,
      IsDoubledResponseMaximizer U a P Q S →
        IsDoubledResponseField U a T →
          average U
              (fun x =>
                blockVecDot Q (T.eval x) -
                  blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))) =
            average U
              (fun x =>
                blockVecDot (T.eval x)
                  (blockMatVecMul (blockMatrixField a x) (S.eval x)))

namespace DoubledResponseTheory

/-- Accessor for the scalar splitting of doubled response
`e.block.J.by.J.Jstar.basic.definitions`. -/
theorem doubledResponseJ_eq_scalar {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (h : DoubledResponseTheory U a) (p pStar q qStar : Vec d) :
    doubledResponseJ U a (p, q) (qStar, pStar) =
      (1 / 2 : ℝ) * responseJ U a (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * responseJ U a.transpose (pStar + p) (qStar + q) :=
  h.doubled_response_by_scalar p pStar q qStar

end DoubledResponseTheory

end

end Ch02
end Book
end Homogenization
