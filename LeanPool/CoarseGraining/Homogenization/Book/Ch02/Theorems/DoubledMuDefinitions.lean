/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.DoubledResponse

/-! # Doubled Mu Definitions -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

theorem blockMatrixField_ae_eq_ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) :
    blockMatrixField a =ᵐ[volumeMeasureOn (U : Set (Vec d))] blockMatrixField b :=
  h.mono fun x hx => by
    simp [blockMatrixField, hx]

theorem blockEnergyDensityAt_ae_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (P : BlockVec d) :
    (fun x => blockEnergyDensityAt a P x)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        fun x => blockEnergyDensityAt b P x :=
  (blockMatrixField_ae_eq_ofAEEq h).mono fun x hx => by
    simp [blockEnergyDensityAt, hx]

theorem doubledBlockPairingIntegrand_ae_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (Y X : DoubledField d) :
    doubledBlockPairingIntegrand U a Y X
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        doubledBlockPairingIntegrand U b Y X :=
  (blockMatrixField_ae_eq_ofAEEq h).mono fun x hx => by
    simp [doubledBlockPairingIntegrand, hx]

theorem doubledMuValue_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (X : DoubledField d) :
    doubledMuValue U a X = doubledMuValue U b X := by
  unfold doubledMuValue average
  congr 1
  exact MeasureTheory.integral_congr_ae <|
    (blockMatrixField_ae_eq_ofAEEq h).mono fun x hx => by
      simp [blockEnergyDensityAt, hx]

theorem doubledMuValueSet_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (P : BlockVec d) :
    doubledMuValueSet U a P = doubledMuValueSet U b P := by
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, by simp [doubledMuValue_eq_ofAEEq h X]⟩
  · rintro ⟨X, hX, rfl⟩
    exact ⟨X, hX, by simp [doubledMuValue_eq_ofAEEq h X]⟩

theorem doubledMu_eq_ofAEEq {d : ℕ} {U : Domain d}
    {a b : CoeffOn U} (h : CoeffOn.AEEq a b) (P : BlockVec d) :
    doubledMu U a P = doubledMu U b P := by
  unfold doubledMu
  rw [doubledMuValueSet_eq_ofAEEq h P]

namespace IsDoubledMuMinimizer

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) {P : BlockVec d} {X : DoubledField d}
    (hX : IsDoubledMuMinimizer U a P X) :
    IsDoubledMuMinimizer U b P X := by
  refine ⟨hX.1, ?_⟩
  intro Y hY
  simpa [doubledMuValue_eq_ofAEEq h X, doubledMuValue_eq_ofAEEq h Y] using
    hX.2 Y hY

end IsDoubledMuMinimizer

/-- Public theorem package for the variational quantity
`e.def.block.mu.basic.definitions` and the coarse block matrix definition
`e.def.block.coarse.matrix.basic.definitions`.

The canonical public theorem proving this package is `doubledMuTheory` in
`DoubledMu.lean`. -/
structure DoubledMuTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) : Prop where
  minimizer_exists :
    ∀ P : BlockVec d, ∃ X : DoubledField d, IsDoubledMuMinimizer U a P X
  minimizer_unique_ae :
    ∀ P : BlockVec d, ∀ X Y : DoubledField d,
      IsDoubledMuMinimizer U a P X →
        IsDoubledMuMinimizer U a P Y →
          DoubledField.SameAE (U := U) X Y
  mu_quadratic :
    ∀ P : BlockVec d,
      doubledMu U a P =
        (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P)
  minimizer_first_variation :
    ∀ P : BlockVec d, ∀ X : DoubledField d,
      IsDoubledMuMinimizer U a P X →
        ∀ Y : DoubledField d, IsDoubledTestField U Y →
          ∫ x in (U : Set (Vec d)),
              doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume = 0

namespace DoubledMuTheory

theorem ofAEEq {d : ℕ} {U : Domain d} {a b : CoeffOn U}
    (h : CoeffOn.AEEq a b) (hTheory : DoubledMuTheory U a) :
    DoubledMuTheory U b where
  minimizer_exists := by
    intro P
    rcases hTheory.minimizer_exists P with ⟨X, hX⟩
    exact ⟨X, hX.ofAEEq h⟩
  minimizer_unique_ae := by
    intro P X Y hX hY
    exact hTheory.minimizer_unique_ae P X Y (hX.ofAEEq h.symm) (hY.ofAEEq h.symm)
  mu_quadratic := by
    intro P
    calc
      doubledMu U b P = doubledMu U a P := (doubledMu_eq_ofAEEq h P).symm
      _ =
          (1 / 2 : ℝ) *
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
        hTheory.mu_quadratic P
      _ =
          (1 / 2 : ℝ) *
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U b) P) := by
        rw [coarseBlockMatrix_eq_ofAEEq h]
  minimizer_first_variation := by
    intro P X hX Y hY
    have hXa : IsDoubledMuMinimizer U a P X := hX.ofAEEq h.symm
    have hFirst := hTheory.minimizer_first_variation P X hXa Y hY
    calc
      ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U b Y X x ∂MeasureTheory.volume =
        ∫ x in (U : Set (Vec d)),
          doubledBlockPairingIntegrand U a Y X x ∂MeasureTheory.volume := by
          exact MeasureTheory.integral_congr_ae
            (doubledBlockPairingIntegrand_ae_eq_ofAEEq h Y X).symm
      _ = 0 := hFirst

/-- Accessor for the public quadratic formula defining the coarse block matrix. -/
theorem doubledMu_eq_coarseBlockMatrix {d : ℕ} {U : Domain d} {a : CoeffOn U}
    (h : DoubledMuTheory U a) (P : BlockVec d) :
    doubledMu U a P =
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (coarseBlockMatrix U a) P) :=
  h.mu_quadratic P

end DoubledMuTheory

end

end Ch02
end Book
end Homogenization
