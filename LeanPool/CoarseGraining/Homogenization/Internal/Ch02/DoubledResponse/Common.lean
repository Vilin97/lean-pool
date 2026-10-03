/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponseDefinitions
public import LeanPool.CoarseGraining.Homogenization.Book.Ch01.Theorems.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Existence
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.BlockMatrixField
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.FirstVariation
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientLinearity
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientUniqueness
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives

/-! # Common -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

/-!
# Common Doubled-Response Helpers

This file is split mechanically out of `Internal.Ch02.DoubledResponse`.
-/

def blockStateOfDoubled {d : ℕ} (X : DoubledField d) : BlockState d :=
  { potential := X.potential
    flux := X.flux }

def doubledFieldOfBlockState {d : ℕ} (X : BlockState d) : DoubledField d :=
  { potential := X.potential
    flux := X.flux }

theorem doubledField_ext {d : ℕ} {X Y : DoubledField d}
    (hpot : X.potential = Y.potential) (hflux : X.flux = Y.flux) :
    X = Y := by
  cases X
  cases Y
  cases hpot
  cases hflux
  rfl

theorem doubledSameAE_symm {d : ℕ} {U : Domain d} {X Y : DoubledField d}
    (hXY : DoubledField.SameAE (U := U) X Y) :
    DoubledField.SameAE (U := U) Y X :=
  ⟨hXY.1.symm, hXY.2.symm⟩

theorem doubledSameAE_refl {d : ℕ} {U : Domain d} (X : DoubledField d) :
    DoubledField.SameAE (U := U) X X :=
  ⟨Filter.EventuallyEq.rfl, Filter.EventuallyEq.rfl⟩

theorem doubledSameAE_trans {d : ℕ} {U : Domain d} {X Y Z : DoubledField d}
    (hXY : DoubledField.SameAE (U := U) X Y)
    (hYZ : DoubledField.SameAE (U := U) Y Z) :
    DoubledField.SameAE (U := U) X Z :=
  ⟨hXY.1.trans hYZ.1, hXY.2.trans hYZ.2⟩

theorem doubledSameAE_add {d : ℕ} {U : Domain d}
    {X1 X2 Y1 Y2 : DoubledField d}
    (hX : DoubledField.SameAE (U := U) X1 X2)
    (hY : DoubledField.SameAE (U := U) Y1 Y2) :
    DoubledField.SameAE (U := U) (X1 + Y1) (X2 + Y2) := by
  constructor
  · filter_upwards [hX.1, hY.1] with x hx hy
    change (X1.potential + Y1.potential) x = (X2.potential + Y2.potential) x
    simp [hx, hy]
  · filter_upwards [hX.2, hY.2] with x hx hy
    change (X1.flux + Y1.flux) x = (X2.flux + Y2.flux) x
    simp [hx, hy]

theorem doubledSameAE_smul {d : ℕ} {U : Domain d} (c : ℝ)
    {X Y : DoubledField d} (hXY : DoubledField.SameAE (U := U) X Y) :
    DoubledField.SameAE (U := U) (c • X) (c • Y) := by
  constructor
  · filter_upwards [hXY.1] with x hx
    change (c • X.potential) x = (c • Y.potential) x
    simp [hx]
  · filter_upwards [hXY.2] with x hx
    change (c • X.flux) x = (c • Y.flux) x
    simp [hx]

theorem doubledFieldOfSolutions_sameAE_ofAEEq {d : ℕ}
    {U : Domain d} {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    DoubledField.SameAE (U := U)
      (doubledFieldOfSolutions a v vStar)
      (doubledFieldOfSolutions b (Solution.ofAEEq h v)
        (Solution.ofAEEq h.transpose vStar)) := by
  constructor
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [h] with x hx
    simp [doubledFieldOfSolutions, CoeffOn.transpose_apply, hx]

theorem doubledFieldOfScalarMaximizers_sameAE_ofAEEq {d : ℕ}
    {U : Domain d} {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    DoubledField.SameAE (U := U)
      (doubledFieldOfScalarMaximizers a v vStar)
      (doubledFieldOfScalarMaximizers b (Solution.ofAEEq h v)
        (Solution.ofAEEq h.transpose vStar)) :=
  doubledSameAE_smul (1 / 2 : ℝ)
    (doubledFieldOfSolutions_sameAE_ofAEEq h v vStar)

noncomputable def solutionSMul {d : ℕ} (U : Domain d) (a : CoeffOn U)
    (c : ℝ) (u : Solution U a) : Solution U a :=
  { toH1 := c • u.toH1
    isHarmonic := by
      simpa using! isAHarmonicGradient_smul u.isHarmonic c }

noncomputable def doubledResponseFirstVariationLeft {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d)
    (T : DoubledField d) : Vec d → ℝ :=
  fun x =>
    blockVecDot Q (T.eval x) -
      blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))

noncomputable def doubledResponseFirstVariationRight {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (S T : DoubledField d) : Vec d → ℝ :=
  fun x =>
    blockVecDot (T.eval x)
      (blockMatVecMul (blockMatrixField a x) (S.eval x))

theorem average_eq_of_average_sub_eq_zero {d : ℕ}
    (U : Domain d) {f g : Vec d → ℝ}
    (hf : MeasureTheory.IntegrableOn f (U : Set (Vec d)))
    (hg : MeasureTheory.IntegrableOn g (U : Set (Vec d)))
    (hzero : average U (fun x => f x - g x) = 0) :
    average U f = average U g := by
  change volumeAverage (U : Set (Vec d)) f = volumeAverage (U : Set (Vec d)) g
  change volumeAverage (U : Set (Vec d)) (f - g) = 0 at hzero
  have hsub :
      volumeAverage (U : Set (Vec d)) (f - g) =
        volumeAverage (U : Set (Vec d)) f - volumeAverage (U : Set (Vec d)) g :=
    volumeAverage_sub hf hg
  rw [hsub] at hzero
  linarith

theorem doubledResponseFirstVariationLeft_average_eq_of_sameAE {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (P Q : BlockVec d)
    {T T' : DoubledField d}
    (hTT' : DoubledField.SameAE (U := U) T T') :
    average U (doubledResponseFirstVariationLeft U a P Q T) =
      average U (doubledResponseFirstVariationLeft U a P Q T') := by
  unfold average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hTT'.1, hTT'.2] with x hpot hflux
  simp [doubledResponseFirstVariationLeft, DoubledField.eval, hpot, hflux]

theorem doubledResponseFirstVariationRight_average_eq_of_sameAE {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {S S' T T' : DoubledField d}
    (hSS' : DoubledField.SameAE (U := U) S S')
    (hTT' : DoubledField.SameAE (U := U) T T') :
    average U (doubledResponseFirstVariationRight U a S T) =
      average U (doubledResponseFirstVariationRight U a S' T') := by
  unfold average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hSS'.1, hSS'.2, hTT'.1, hTT'.2] with x hSpot hSflux hTpot hTflux
  simp [doubledResponseFirstVariationRight, DoubledField.eval, hSpot, hSflux, hTpot, hTflux]

theorem doubledResponseFirstVariationLeft_average_eq_ofAEEq {d : ℕ}
    {U : Domain d} {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (P Q : BlockVec d) (T : DoubledField d) :
    average U (doubledResponseFirstVariationLeft U a P Q T) =
      average U (doubledResponseFirstVariationLeft U b P Q T) := by
  unfold average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [blockMatrixField_ae_eq_ofAEEq h] with x hx
  simp [doubledResponseFirstVariationLeft, hx]

theorem doubledResponseFirstVariationRight_average_eq_ofAEEq {d : ℕ}
    {U : Domain d} {a b : CoeffOn U} (h : CoeffOn.AEEq a b)
    (S T : DoubledField d) :
    average U (doubledResponseFirstVariationRight U a S T) =
      average U (doubledResponseFirstVariationRight U b S T) := by
  unfold average
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards [blockMatrixField_ae_eq_ofAEEq h] with x hx
  simp [doubledResponseFirstVariationRight, hx]

theorem doubledFieldOfSolutions_solutionSMul_half_eq_pairHalf {d : ℕ}
    (U : Domain d) (a : CoeffOn U) (u : Solution U a)
    (vStar : Solution U a.transpose) :
    doubledFieldOfSolutions a (solutionSMul U a (1 / 2 : ℝ) u)
        (solutionSMul U a.transpose (1 / 2 : ℝ) vStar) =
      doubledFieldOfBlockState
        (blockResponsePairHalfState a.toCoeffField u vStar) := by
  apply doubledField_ext
  · funext x
    change
      (1 / 2 : ℝ) • u.toH1.grad x + (1 / 2 : ℝ) • vStar.toH1.grad x =
        ((1 / 2 : ℝ) • (fun x => u.toH1.grad x + vStar.toH1.grad x)) x
    simp [Pi.smul_apply, smul_add]
  · funext x
    change
      matVecMul (a.toCoeffField x) ((1 / 2 : ℝ) • u.toH1.grad x) -
          matVecMul (a.transpose.toCoeffField x) ((1 / 2 : ℝ) • vStar.toH1.grad x) =
        ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (u.toH1.grad x) -
              matVecMul (matTranspose (a.toCoeffField x)) (vStar.toH1.grad x))) x
    simp [CoeffOn.transpose_apply, Pi.smul_apply, matVecMul_smul, sub_eq_add_neg,
      smul_add, smul_neg]

theorem blockStateOfDoubled_scalarMaximizers_eq_pairHalf {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (v : Solution U a) (vStar : Solution U a.transpose) :
    blockStateOfDoubled (doubledFieldOfScalarMaximizers a v vStar) =
      blockResponsePairHalfState a.toCoeffField v vStar := by
  apply BlockState.ext
  · funext x
    change
      ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x)) x =
        ((1 / 2 : ℝ) • (fun x => v.toH1.grad x + vStar.toH1.grad x)) x
    rfl
  · funext x
    change
      ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (a.transpose.toCoeffField x) (vStar.toH1.grad x))) x =
        ((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x) (v.toH1.grad x) -
              matVecMul (matTranspose (a.toCoeffField x)) (vStar.toH1.grad x))) x
    simp [CoeffOn.transpose_apply]

theorem blockStateOfDoubled_solutions_eq_pairHalf_two {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (w : Solution U a) (z : Solution U a.transpose) :
    blockStateOfDoubled (doubledFieldOfSolutions a w z) =
      blockResponsePairHalfState a.toCoeffField
        (solutionSMul U a (2 : ℝ) w)
        (solutionSMul U a.transpose (2 : ℝ) z) := by
  apply BlockState.ext
  · funext x
    ext i
    change
      (w.toH1.grad x + z.toH1.grad x) i =
        (((1 / 2 : ℝ) •
          (fun x =>
            (solutionSMul U a (2 : ℝ) w).toH1.grad x +
              (solutionSMul U a.transpose (2 : ℝ) z).toH1.grad x)) x) i
    simp [solutionSMul, Pi.smul_apply]
    ring
  · funext x
    ext i
    change
      (matVecMul (a.toCoeffField x) (w.toH1.grad x) -
          matVecMul (a.transpose.toCoeffField x) (z.toH1.grad x)) i =
        (((1 / 2 : ℝ) •
          (fun x =>
            matVecMul (a.toCoeffField x)
                ((solutionSMul U a (2 : ℝ) w).toH1.grad x) -
              matVecMul (matTranspose (a.toCoeffField x))
                ((solutionSMul U a.transpose (2 : ℝ) z).toH1.grad x))) x) i
    simp [CoeffOn.transpose_apply, solutionSMul, Pi.smul_apply, matVecMul_smul,
      sub_eq_add_neg]
    ring

end BookCh02

end

end Ch02
end Internal
end Homogenization
