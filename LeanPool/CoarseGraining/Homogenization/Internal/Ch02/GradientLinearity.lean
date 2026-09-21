/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.GradientLinearityDefinitions
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.FirstVariation
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientUniqueness

/-! # Gradient Linearity -/

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem scalarFirstVariationIntegrand_addOfIntegrable {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d)
    (p1 q1 p2 q2 : Vec d) (v1 v2 w : AHarmonicFunction a U)
    (hv1_int : weakFluxIntegrable U a v1)
    (hv2_int : weakFluxIntegrable U a v2) :
    scalarFirstVariationIntegrand U a (p1 + p2) (q1 + q2)
        (AHarmonicFunction.addOfIntegrable v1 v2 hv1_int hv2_int) w =
      scalarFirstVariationIntegrand U a p1 q1 v1 w +
        scalarFirstVariationIntegrand U a p2 q2 v2 w := by
  funext x
  simp [scalarFirstVariationIntegrand, matVecMul_add, vecDot_add_left,
    vecDot_add_right, sub_eq_add_neg]
  ring

private theorem scalarFirstVariationIntegrand_smul_solution {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d)
    (c : ℝ) (p q : Vec d) (v w : AHarmonicFunction a U) :
    scalarFirstVariationIntegrand U a (c • p) (c • q) (c • v) w =
      c • scalarFirstVariationIntegrand U a p q v w := by
  funext x
  simp [scalarFirstVariationIntegrand, matVecMul_smul, vecDot_smul_left,
    vecDot_smul_right, smul_eq_mul]
  ring

theorem addOfIntegrable_isResponseMaximizer_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p1 q1 p2 q2 : Vec d) (v1 v2 : Solution U a)
    (h1 : Book.Ch02.IsResponseMaximizer U a p1 q1 v1)
    (h2 : Book.Ch02.IsResponseMaximizer U a p2 q2 v2) :
    let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    Homogenization.IsResponseMaximizer (U : Set (Vec d)) (p1 + p2) (q1 + q2)
      a.toCoeffField (AHarmonicFunction.addOfIntegrable v1 v2 (hInt.weakFlux v1)
        (hInt.weakFlux v2)) := by
  intro hInt
  apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
    (U : Set (Vec d)) a.toCoeffField hEll
  intro w
  let hFirst := responseFirstVariationTheory_of_isEllipticFieldOn U a hEll
  have hzero1 := hFirst.first_variation p1 q1 v1 h1 w
  have hzero2 := hFirst.first_variation p2 q2 v2 h2 w
  change
    volumeAverage (U : Set (Vec d))
      (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField p1 q1 v1 w) = 0
    at hzero1
  change
    volumeAverage (U : Set (Vec d))
      (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField p2 q2 v2 w) = 0
    at hzero2
  rw [scalarFirstVariationIntegrand_addOfIntegrable
    (U : Set (Vec d)) a.toCoeffField p1 q1 p2 q2 v1 v2 w
    (hInt.weakFlux v1) (hInt.weakFlux v2)]
  rw [volumeAverage_add (hInt.firstVariation p1 q1 v1 w)
    (hInt.firstVariation p2 q2 v2 w)]
  rw [hzero1, hzero2]
  ring

private theorem smul_isResponseMaximizer_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (c : ℝ) (p q : Vec d) (v : Solution U a)
    (hv : Book.Ch02.IsResponseMaximizer U a p q v) :
    Homogenization.IsResponseMaximizer (U : Set (Vec d)) (c • p) (c • q)
      a.toCoeffField (c • v) := by
  apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
    (U : Set (Vec d)) a.toCoeffField hEll
  intro w
  let hFirst := responseFirstVariationTheory_of_isEllipticFieldOn U a hEll
  have hzero := hFirst.first_variation p q v hv w
  change
    volumeAverage (U : Set (Vec d))
      (scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField p q v w) = 0
    at hzero
  rw [scalarFirstVariationIntegrand_smul_solution
    (U : Set (Vec d)) a.toCoeffField c p q v w]
  rw [volumeAverage_smul]
  rw [hzero, mul_zero]

/-- Internal pointwise-coefficient gradient-linearity theorem. -/
theorem responseGradientLinearityTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseGradientLinearityTheory U a where
  add_gradient := by
    intro p1 q1 p2 q2 v12 v1 v2 h12 h1 h2
    let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
      ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
    let vsum : Solution U a :=
      AHarmonicFunction.addOfIntegrable v1 v2 (hInt.weakFlux v1) (hInt.weakFlux v2)
    have hsum :
        Book.Ch02.IsResponseMaximizer U a (p1 + p2) (q1 + q2) vsum := by
      simpa [vsum, hInt] using!
        addOfIntegrable_isResponseMaximizer_of_isEllipticFieldOn
          U a hEll p1 q1 p2 q2 v1 v2 h1 h2
    have hUnique := responseGradientUniquenessTheory_of_isEllipticFieldOn U a hEll
    have hsame := hUnique.unique_gradient (p1 + p2) (q1 + q2) v12 vsum h12 hsum
    simpa [vsum, AHarmonicFunction.grad_addOfIntegrable] using! hsame
  smul_gradient := by
    intro c p q vc v hc hv
    let vscaled : Solution U a := c • v
    have hscaled : Book.Ch02.IsResponseMaximizer U a (c • p) (c • q) vscaled := by
      exact smul_isResponseMaximizer_of_isEllipticFieldOn U a hEll c p q v hv
    have hUnique := responseGradientUniquenessTheory_of_isEllipticFieldOn U a hEll
    have hsame := hUnique.unique_gradient (c • p) (c • q) vc vscaled hc hscaled
    simpa [vscaled, AHarmonicFunction.grad_smul] using! hsame

/-- Note-facing Chapter 2 gradient linearity from the public a.e. coefficient
interface. -/
theorem responseGradientLinearityTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseGradientLinearityTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : ResponseGradientLinearityTheory U b :=
    responseGradientLinearityTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseGradientLinearityTheory.ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
