/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.QuadraticityDefinitions
public import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.GradientLinearity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas.BasicVariation

/-! # Quadraticity -/

@[expose] public section

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem responseJ_zero_zero_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseJ (U : Set (Vec d)) 0 0 a.toCoeffField = 0 := by
  have hmax0 :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) 0 0 a.toCoeffField
        (0 : AHarmonicFunction a.toCoeffField (U : Set (Vec d))) := by
    apply isResponseMaximizer_of_firstVariation_eq_zero_of_isEllipticFieldOn
      (U : Set (Vec d)) a.toCoeffField hEll
    intro w
    rw [show
        scalarFirstVariationIntegrand (U : Set (Vec d)) a.toCoeffField 0 0
            (0 : AHarmonicFunction a.toCoeffField (U : Set (Vec d))) w = 0 by
          funext x
          simp [scalarFirstVariationIntegrand, matVecMul_zero, vecDot_zero_left,
            vecDot_zero_right]]
    exact volumeAverage_zero (U : Set (Vec d))
  have hJ :=
    responseJ_eq_of_isResponseMaximizer (U : Set (Vec d)) 0 0 a.toCoeffField hmax0
  rw [hJ]
  simp [scalarResponseIntegrand_zero]

private theorem scalarVariationEnergyIntegrand_addOfIntegrable {d : ℕ}
    (a : CoeffField d) {U : Set (Vec d)}
    (u v : AHarmonicFunction a U)
    (hu_int : weakFluxIntegrable U a u)
    (hv_int : weakFluxIntegrable U a v) :
    scalarVariationEnergyIntegrand a
        (AHarmonicFunction.addOfIntegrable u v hu_int hv_int) =
      scalarVariationEnergyIntegrand a u + scalarVariationEnergyIntegrand a v +
        (2 : ℝ) •
          (fun x => vecDot (v.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
  funext x
  have hsymm :
      vecDot (u.toH1.grad x) (matVecMul (symmPart (a x)) (v.toH1.grad x)) =
        vecDot (v.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x)) := by
    simpa using vecDot_matVecMul_symmPart_comm (a x) (u.toH1.grad x) (v.toH1.grad x)
  unfold scalarVariationEnergyIntegrand
  rw [AHarmonicFunction.grad_addOfIntegrable]
  simp [matVecMul_add, vecDot_add_left, vecDot_add_right, smul_eq_mul, hsymm]
  ring

private theorem volumeAverage_scalarVariationEnergyIntegrand_addOfIntegrable {d : ℕ}
    (U : Set (Vec d)) (a : CoeffField d) (hInt : ResponseLinearIntegrabilityData U a)
    (u v : AHarmonicFunction a U) :
    volumeAverage U (scalarVariationEnergyIntegrand a
        (AHarmonicFunction.addOfIntegrable u v (hInt.weakFlux u) (hInt.weakFlux v))) =
      volumeAverage U (scalarVariationEnergyIntegrand a u) +
        volumeAverage U (scalarVariationEnergyIntegrand a v) +
          2 * volumeAverage U
            (fun x => vecDot (v.toH1.grad x) (matVecMul (symmPart (a x)) (u.toH1.grad x))) := by
  rw [scalarVariationEnergyIntegrand_addOfIntegrable a u v (hInt.weakFlux u) (hInt.weakFlux v)]
  have hsum :
      MeasureTheory.IntegrableOn
        (scalarVariationEnergyIntegrand a u + scalarVariationEnergyIntegrand a v) U := by
    simpa [MeasureTheory.IntegrableOn] using
      (hInt.energy u).integrable.add (hInt.energy v).integrable
  rw [volumeAverage_add hsum]
  · rw [volumeAverage_add (hInt.energy u) (hInt.energy v)]
    rw [volumeAverage_smul]
  · simpa [MeasureTheory.IntegrableOn] using (hInt.cross u v).integrable.smul (2 : ℝ)

theorem responseJ_smul_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (c : ℝ) (p q : Vec d) :
    responseJ U a (c • p) (c • q) = c ^ 2 * responseJ U a p q := by
  rw [book_responseJ_eq_ResponseJ U a (c • p) (c • q)]
  rw [book_responseJ_eq_ResponseJ U a p q]
  by_cases hc : c = 0
  · subst c
    simp [responseJ_zero_zero_of_isEllipticFieldOn U a hEll]
  · exact responseJ_homogeneous (U : Set (Vec d)) p q a.toCoeffField hc

theorem responseJ_parallelogram_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    (p1 q1 p2 q2 : Vec d) :
    responseJ U a (p1 + p2) (q1 + q2) +
        responseJ U a (p1 - p2) (q1 - q2) =
      2 * responseJ U a p1 q1 + 2 * responseJ U a p2 q2 := by
  rw [book_responseJ_eq_ResponseJ U a (p1 + p2) (q1 + q2)]
  rw [book_responseJ_eq_ResponseJ U a (p1 - p2) (q1 - q2)]
  rw [book_responseJ_eq_ResponseJ U a p1 q1]
  rw [book_responseJ_eq_ResponseJ U a p2 q2]
  let hInt : ResponseLinearIntegrabilityData (U : Set (Vec d)) a.toCoeffField :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll
  let hExist : ResponseExistenceTheory U a :=
    responseExistenceTheory_of_isEllipticFieldOn U a hEll
  let v1 : Solution U a := (canonicalMaximizer hExist p1 q1).toSolution
  let v2 : Solution U a := (canonicalMaximizer hExist p2 q2).toSolution
  let vsum : Solution U a :=
    AHarmonicFunction.addOfIntegrable v1 v2 (hInt.weakFlux v1) (hInt.weakFlux v2)
  have hmax1 : Book.Ch02.IsResponseMaximizer U a p1 q1 v1 := by
    simpa [v1] using canonicalMaximizer_isMaximizer hExist p1 q1
  have hmax2 : Book.Ch02.IsResponseMaximizer U a p2 q2 v2 := by
    simpa [v2] using canonicalMaximizer_isMaximizer hExist p2 q2
  have hsum :
      Homogenization.IsResponseMaximizer (U : Set (Vec d)) (p1 + p2) (q1 + q2)
        a.toCoeffField vsum := by
    simpa [vsum, hInt] using
      addOfIntegrable_isResponseMaximizer_of_isEllipticFieldOn
        U a hEll p1 q1 p2 q2 v1 v2 hmax1 hmax2
  have hJplus :
      ResponseJ (U : Set (Vec d)) (p1 + p2) (q1 + q2) a.toCoeffField =
        (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField vsum) :=
    responseJ_energy_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField (p1 + p2) (q1 + q2) vsum hsum
      (hInt.weakFlux vsum) (hInt.response (p1 + p2) (q1 + q2) vsum)
      (hInt.firstVariation (p1 + p2) (q1 + q2) vsum vsum) (hInt.energy vsum)
  have hJ1 :
      ResponseJ (U : Set (Vec d)) p1 q1 a.toCoeffField =
        (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField v1) :=
    responseJ_energy_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField p1 q1 v1 hmax1
      (hInt.weakFlux v1) (hInt.response p1 q1 v1)
      (hInt.firstVariation p1 q1 v1 v1) (hInt.energy v1)
  have hJ2 :
      ResponseJ (U : Set (Vec d)) p2 q2 a.toCoeffField =
        (1 / 2 : ℝ) * volumeAverage (U : Set (Vec d))
          (scalarVariationEnergyIntegrand a.toCoeffField v2) :=
    responseJ_energy_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField p2 q2 v2 hmax2
      (hInt.weakFlux v2) (hInt.response p2 q2 v2)
      (hInt.firstVariation p2 q2 v2 v2) (hInt.energy v2)
  have hsplit :
      volumeAverage (U : Set (Vec d)) (scalarVariationEnergyIntegrand a.toCoeffField vsum) =
        volumeAverage (U : Set (Vec d)) (scalarVariationEnergyIntegrand a.toCoeffField v1) +
          volumeAverage (U : Set (Vec d)) (scalarVariationEnergyIntegrand a.toCoeffField v2) +
            2 * volumeAverage (U : Set (Vec d))
              (fun x =>
                vecDot (v2.toH1.grad x) (matVecMul (symmPart (a.toCoeffField x))
                  (v1.toH1.grad x))) := by
    simpa [vsum] using
      volumeAverage_scalarVariationEnergyIntegrand_addOfIntegrable
        (U : Set (Vec d)) a.toCoeffField hInt v1 v2
  have hpol :
      volumeAverage (U : Set (Vec d))
          (fun x =>
            vecDot (v2.toH1.grad x) (matVecMul (symmPart (a.toCoeffField x))
              (v1.toH1.grad x))) =
        ResponseJ (U : Set (Vec d)) p1 q1 a.toCoeffField +
          ResponseJ (U : Set (Vec d)) p2 q2 a.toCoeffField -
            ResponseJ (U : Set (Vec d)) (p1 - p2) (q1 - q2) a.toCoeffField :=
    basic_cg_identities_polarization_of_isResponseMaximizer
      (U : Set (Vec d)) a.toCoeffField p1 q1 p2 q2 hInt v1 v2 hmax1 hmax2
  nlinarith [hJplus, hJ1, hJ2, hsplit, hpol]

/-- Internal pointwise-coefficient quadraticity theorem. -/
theorem responseQuadraticTheory_of_isEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField) :
    ResponseQuadraticTheory U a where
  responseJ_smul := responseJ_smul_of_isEllipticFieldOn U a hEll
  responseJ_parallelogram := responseJ_parallelogram_of_isEllipticFieldOn U a hEll

/-- Note-facing Chapter 2 quadraticity from the public a.e. coefficient
interface. No public pointwise representative or integrability package is
exposed. -/
theorem responseQuadraticTheory {d : ℕ} (U : Domain d) (a : CoeffOn U) :
    ResponseQuadraticTheory U a := by
  let b : CoeffOn U := pointwiseCoeffOn U a
  have hEll :
      IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
    simpa [b] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hb : ResponseQuadraticTheory U b :=
    responseQuadraticTheory_of_isEllipticFieldOn U b hEll
  have hba : CoeffOn.AEEq b a := by
    simpa [b] using pointwiseCoeffOn_ae_eq U a
  exact ResponseQuadraticTheory.ofAEEq hba hb

end BookCh02

end

end Ch02
end Internal
end Homogenization
