/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.EnergyDensities

/-! # Densities -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section53
namespace JUpperBoundWeakNorms

/-!
# AdditivityDensities

Additivity-cross densities and pointwise elliptic estimates.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal BigOperators

noncomputable section

/-- Quadratic algebra behind the child additivity-cross term. -/
theorem half_quad_eq_additivity_cross_add_half_quad
    {d : ℕ} (A : Mat d) (top child : Vec d) :
    (1 / 2 : ℝ) * vecDot top (matVecMul (symmPart A) top) =
      ((1 / 2 : ℝ) *
          vecDot (top - child) (matVecMul (symmPart A) (top - child)) +
        vecDot (top - child) (matVecMul (symmPart A) child)) +
        (1 / 2 : ℝ) * vecDot child (matVecMul (symmPart A) child) := by
  have hcomm :
      vecDot child (matVecMul (symmPart A) top) =
        vecDot top (matVecMul (symmPart A) child) := by
    simpa using vecDot_matVecMul_symmPart_comm A child top
  simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left,
    vecDot_add_right, vecDot_neg_left, vecDot_neg_right, hcomm]
  ring

/-- Concrete child-cube cross density for a deterministic coefficient family. -/
noncomputable def childAdditivityCrossDensityOnFamilyOnCube {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) : Vec d → ℝ :=
  fun x =>
    let topGrad := canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x
    let childGrad := canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
    let A := (a.coeffOn R).toCoeffField x
    (1 / 2 : ℝ) *
        vecDot (topGrad - childGrad)
          (matVecMul (symmPart A) (topGrad - childGrad)) +
      vecDot (topGrad - childGrad) (matVecMul (symmPart A) childGrad)

/-- Concrete additivity-cross term over all depth-`j` children. -/
noncomputable def concreteAdditivityCrossTermOnFamilyAtDepth {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d)
    (j : ℕ) (φ : Vec d → ℝ) (p q : Vec d) : ℝ :=
  additivityCrossTermOnCubeAtDepth Q j φ fun R =>
    cubeAverage R (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)

/-- Unweighted average of child responses for a deterministic triadic
coefficient family. -/
noncomputable def childResponseJAverageOnFamilyAtDepth {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (p q : Vec d) : ℝ :=
  descendantsAverage Q j fun R =>
    Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q

/-- Deterministic child-minus-parent response defect for a triadic coefficient
family. -/
noncomputable def responseJPartitionDefectOnFamilyAtDepth {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (j : ℕ)
    (p q : Vec d) : ℝ :=
  childResponseJAverageOnFamilyAtDepth a Q j p q -
    Ch02.responseJ (Ch02.cubeDomain Q) (a.coeffOn Q) p q

/-- The local half-energy of the top-minus-child gradient difference on one
child cube. -/
noncomputable def additivityDiffHalfEnergyDensityOnFamilyOnCube {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) : Vec d → ℝ :=
  fun x =>
    let diff :=
      canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
        canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
    let A := (a.coeffOn R).toCoeffField x
    (1 / 2 : ℝ) * vecDot diff (matVecMul (symmPart A) diff)

/-- The local half-energy of the top-plus-child gradient sum on one child
cube. -/
noncomputable def additivitySumHalfEnergyDensityOnFamilyOnCube {d : ℕ}
    (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) : Vec d → ℝ :=
  fun x =>
    let topGrad := canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x
    let childGrad := canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
    let A := (a.coeffOn R).toCoeffField x
    (1 / 2 : ℝ) *
      vecDot (topGrad + childGrad) (matVecMul (symmPart A) (topGrad + childGrad))

/-- The concrete child additivity-cross density is locally integrable. -/
theorem childAdditivityCrossDensityOnFamilyOnCube_integrableOn
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    IntegrableOn (childAdditivityCrossDensityOnFamilyOnCube a Q R p q)
      (cubeSet R) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    let : Fact (volume (cubeSet R) < ⊤) := ⟨volume_cubeSet_lt_top R⟩
    change IsFiniteMeasure (volume.restrict (cubeSet R))
    infer_instance
  let topGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q
  let childGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube R (a.coeffOn R) p q
  let coeff : CoeffField d := (a.coeffOn R).toCoeffField
  have hTop : MemVectorL2 (cubeSet R) topGrad := by
    simpa [topGrad, canonicalMaximizerGradientOnCube] using!
      (Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
        (Q := Q) (R := R) (j := j)
        (canonicalMaximizerSolutionOnCube Q (a.coeffOn Q) p q).toH1 hR)
  have hChild : MemVectorL2 (cubeSet R) childGrad := by
    have h :=
      (Ch03.publicH1ToCubeSet
        (Q := R) (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q).toH1).grad_memVectorL2
    simpa [childGrad, canonicalMaximizerGradientOnCube, Ch03.publicH1ToCubeSet_grad] using! h
  have hDiff : MemVectorL2 (cubeSet R) (fun x => topGrad x - childGrad x) := by
    simpa using! hTop.sub hChild
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) coeff := by
    simpa [coeff, Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) coeff :=
    hEllOpen.cubeSet_of_openCubeSet
  have hSymmDiff :
      MemVectorL2 (cubeSet R)
        (fun x => matVecMul (symmPart (coeff x)) (topGrad x - childGrad x)) :=
    IsAEEllipticFieldOn.memVectorL2_matVecMul_symmPart hEll hDiff
  have hSymmChild :
      MemVectorL2 (cubeSet R)
        (fun x => matVecMul (symmPart (coeff x)) (childGrad x)) :=
    IsAEEllipticFieldOn.memVectorL2_matVecMul_symmPart hEll hChild
  have hQuad :
      IntegrableOn
        (fun x => vecDot (topGrad x - childGrad x)
          (matVecMul (symmPart (coeff x)) (topGrad x - childGrad x)))
        (cubeSet R) volume :=
    integrableOn_vecDot_of_memVectorL2 hDiff hSymmDiff
  have hCross :
      IntegrableOn
        (fun x => vecDot (topGrad x - childGrad x)
          (matVecMul (symmPart (coeff x)) (childGrad x)))
        (cubeSet R) volume :=
    integrableOn_vecDot_of_memVectorL2 hDiff hSymmChild
  have hSum :
      IntegrableOn
        (fun x =>
          (1 / 2 : ℝ) *
              vecDot (topGrad x - childGrad x)
                (matVecMul (symmPart (coeff x)) (topGrad x - childGrad x)) +
            vecDot (topGrad x - childGrad x)
              (matVecMul (symmPart (coeff x)) (childGrad x)))
        (cubeSet R) volume :=
    (hQuad.const_mul (1 / 2 : ℝ)).add hCross
  show
    IntegrableOn
      (fun x =>
        (1 / 2 : ℝ) *
            vecDot
              (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
                canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
              (matVecMul (symmPart ((a.coeffOn R).toCoeffField x))
                (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
                  canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)) +
          vecDot
            (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
              canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
            (matVecMul (symmPart ((a.coeffOn R).toCoeffField x))
              (canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)))
      (cubeSet R) volume
  simpa [childAdditivityCrossDensityOnFamilyOnCube, topGrad, childGrad, coeff] using hSum

/-- The concrete child additivity-cross density is the manuscript
`1/2 (top-child) · a_s (top+child)` density. -/
theorem childAdditivityCrossDensityOnFamilyOnCube_eq_half_diff_dot_symmPart_sum
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d) (x : Vec d) :
    childAdditivityCrossDensityOnFamilyOnCube a Q R p q x =
      (1 / 2 : ℝ) *
        vecDot
          (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
            canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
          (matVecMul (symmPart ((a.coeffOn R).toCoeffField x))
            (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x +
              canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)) := by
  let topGrad := canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x
  let childGrad := canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
  let A := (a.coeffOn R).toCoeffField x
  have htop : topGrad = (topGrad - childGrad) + childGrad := by
    ext i
    simp
  have hcomm :
      vecDot (topGrad - childGrad) (matVecMul (symmPart A) topGrad) =
        vecDot (topGrad - childGrad)
            (matVecMul (symmPart A) (topGrad - childGrad)) +
          vecDot (topGrad - childGrad) (matVecMul (symmPart A) childGrad) := by
    calc
      vecDot (topGrad - childGrad) (matVecMul (symmPart A) topGrad)
          =
        vecDot (topGrad - childGrad)
          (matVecMul (symmPart A) ((topGrad - childGrad) + childGrad)) := by
            conv_lhs =>
              arg 2
              arg 2
              rw [htop]
      _ =
        vecDot (topGrad - childGrad)
            (matVecMul (symmPart A) (topGrad - childGrad)) +
          vecDot (topGrad - childGrad) (matVecMul (symmPart A) childGrad) := by
            rw [matVecMul_add, vecDot_add_right]
  simp [childAdditivityCrossDensityOnFamilyOnCube, topGrad, childGrad, A,
    matVecMul_add, vecDot_add_right, hcomm]
  ring

/-- Pointwise Cauchy for the symmetric coefficient energy. -/
theorem abs_half_vecDot_matVecMul_symmPart_le_sqrt_half_quad_mul_sqrt_half_quad_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (ξ η : Vec d) :
    |(1 / 2 : ℝ) * vecDot ξ (matVecMul (symmPart A) η)| ≤
      Real.sqrt ((1 / 2 : ℝ) * vecDot ξ (matVecMul (symmPart A) ξ)) *
        Real.sqrt ((1 / 2 : ℝ) * vecDot η (matVecMul (symmPart A) η)) := by
  let X : ℝ := vecDot ξ (matVecMul (symmPart A) ξ)
  let Y : ℝ := vecDot η (matVecMul (symmPart A) η)
  let Z : ℝ := vecDot ξ (matVecMul (symmPart A) η)
  have hsq : Z ^ 2 ≤ X * Y := by
    simpa [X, Y, Z] using
      sq_vecDot_matVecMul_symmPart_le_of_isEllipticMatrix hA ξ η
  have hX_nonneg : 0 ≤ X := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hA ξ
    have hnorm : 0 ≤ vecNormSq ξ := vecNormSq_nonneg ξ
    have hlam_pos : 0 < lam := hA.1
    nlinarith
  have hY_nonneg : 0 ≤ Y := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hA η
    have hnorm : 0 ≤ vecNormSq η := vecNormSq_nonneg η
    have hlam_pos : 0 < lam := hA.1
    nlinarith
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have hleft_sq :
      |(1 / 2 : ℝ) * Z| ^ 2 = ((1 / 2 : ℝ) ^ 2) * Z ^ 2 := by
    rw [sq_abs]
    ring
  have hright_sq :
      (Real.sqrt ((1 / 2 : ℝ) * X) * Real.sqrt ((1 / 2 : ℝ) * Y)) ^ 2 =
        ((1 / 2 : ℝ) * X) * ((1 / 2 : ℝ) * Y) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hhalf_nonneg hX_nonneg),
      Real.sq_sqrt (mul_nonneg hhalf_nonneg hY_nonneg)]
  have hsq_abs :
      |(1 / 2 : ℝ) * Z| ^ 2 ≤
        (Real.sqrt ((1 / 2 : ℝ) * X) * Real.sqrt ((1 / 2 : ℝ) * Y)) ^ 2 := by
    rw [hleft_sq, hright_sq]
    nlinarith
  have hright_nonneg :
      0 ≤ Real.sqrt ((1 / 2 : ℝ) * X) *
        Real.sqrt ((1 / 2 : ℝ) * Y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  simpa [X, Y, Z] using abs_le_of_sq_le_sq hsq_abs hright_nonneg

/-- Pointwise local Cauchy estimate for the concrete child additivity-cross
density. -/
theorem abs_childAdditivityCrossDensityOnFamilyOnCube_le_sqrt_diff_mul_sqrt_sum_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} (a : Ch02.TriadicCoeffFamily d)
    (Q R : TriadicCube d) (p q : Vec d) (x : Vec d)
    (hEll : IsEllipticMatrix lam Lam ((a.coeffOn R).toCoeffField x)) :
    |childAdditivityCrossDensityOnFamilyOnCube a Q R p q x| ≤
      Real.sqrt (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q x) *
        Real.sqrt (additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q x) := by
  rw [childAdditivityCrossDensityOnFamilyOnCube_eq_half_diff_dot_symmPart_sum]
  simpa [additivityDiffHalfEnergyDensityOnFamilyOnCube,
    additivitySumHalfEnergyDensityOnFamilyOnCube] using
    abs_half_vecDot_matVecMul_symmPart_le_sqrt_half_quad_mul_sqrt_half_quad_of_isEllipticMatrix
      hEll
      (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
        canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
      (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x +
        canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)

/-- The local difference half-energy density is nonnegative at elliptic points. -/
theorem additivityDiffHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} (a : Ch02.TriadicCoeffFamily d)
    (Q R : TriadicCube d) (p q : Vec d) (x : Vec d)
    (hEll : IsEllipticMatrix lam Lam ((a.coeffOn R).toCoeffField x)) :
    0 ≤ additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q x := by
  let diff :=
    canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
      canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
  have hquad :
      0 ≤ vecDot diff
        (matVecMul (symmPart ((a.coeffOn R).toCoeffField x)) diff) := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hEll diff
    have hnorm : 0 ≤ vecNormSq diff := vecNormSq_nonneg diff
    have hlam_pos : 0 < lam := hEll.1
    nlinarith
  simpa [additivityDiffHalfEnergyDensityOnFamilyOnCube, diff] using
    mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hquad

/-- The local sum half-energy density is nonnegative at elliptic points. -/
theorem additivitySumHalfEnergyDensityOnFamilyOnCube_nonneg_of_isEllipticMatrix
    {d : ℕ} {lam Lam : ℝ} (a : Ch02.TriadicCoeffFamily d)
    (Q R : TriadicCube d) (p q : Vec d) (x : Vec d)
    (hEll : IsEllipticMatrix lam Lam ((a.coeffOn R).toCoeffField x)) :
    0 ≤ additivitySumHalfEnergyDensityOnFamilyOnCube a Q R p q x := by
  let sumGrad :=
    canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x +
      canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
  have hquad :
      0 ≤ vecDot sumGrad
        (matVecMul (symmPart ((a.coeffOn R).toCoeffField x)) sumGrad) := by
    have hlower := lowerBound_symmPart_of_isEllipticMatrix hEll sumGrad
    have hnorm : 0 ≤ vecNormSq sumGrad := vecNormSq_nonneg sumGrad
    have hlam_pos : 0 < lam := hEll.1
    nlinarith
  simpa [additivitySumHalfEnergyDensityOnFamilyOnCube, sumGrad] using
    mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hquad

/-- The local difference half-energy density is locally integrable. -/
theorem additivityDiffHalfEnergyDensityOnFamilyOnCube_integrableOn
    {d : ℕ} [NeZero d] (a : Ch02.TriadicCoeffFamily d)
    (Q : TriadicCube d) {R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (p q : Vec d) :
    IntegrableOn (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)
      (cubeSet R) volume := by
  let : IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    let : Fact (volume (cubeSet R) < ⊤) := ⟨volume_cubeSet_lt_top R⟩
    change IsFiniteMeasure (volume.restrict (cubeSet R))
    infer_instance
  let topGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q
  let childGrad : Vec d → Vec d :=
    canonicalMaximizerGradientOnCube R (a.coeffOn R) p q
  let coeff : CoeffField d := (a.coeffOn R).toCoeffField
  have hTop : MemVectorL2 (cubeSet R) topGrad := by
    simpa [topGrad, canonicalMaximizerGradientOnCube] using!
      (Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
        (Q := Q) (R := R) (j := j)
        (canonicalMaximizerSolutionOnCube Q (a.coeffOn Q) p q).toH1 hR)
  have hChild : MemVectorL2 (cubeSet R) childGrad := by
    have h :=
      (Ch03.publicH1ToCubeSet
        (Q := R) (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q).toH1).grad_memVectorL2
    simpa [childGrad, canonicalMaximizerGradientOnCube, Ch03.publicH1ToCubeSet_grad] using! h
  have hDiff : MemVectorL2 (cubeSet R) (fun x => topGrad x - childGrad x) := by
    simpa using! hTop.sub hChild
  have hEllOpen :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (openCubeSet R) coeff := by
    simpa [coeff, Ch02.cubeDomain_coe] using
      (ch02_coeffOn_isAEEllipticFieldOn (a.coeffOn R))
  have hEll :
      IsAEEllipticFieldOn (a.coeffOn R).lam (a.coeffOn R).Lam
        (cubeSet R) coeff :=
    hEllOpen.cubeSet_of_openCubeSet
  have hSymmDiff :
      MemVectorL2 (cubeSet R)
        (fun x => matVecMul (symmPart (coeff x)) (topGrad x - childGrad x)) :=
    IsAEEllipticFieldOn.memVectorL2_matVecMul_symmPart hEll hDiff
  have hQuad :
      IntegrableOn
        (fun x => vecDot (topGrad x - childGrad x)
          (matVecMul (symmPart (coeff x)) (topGrad x - childGrad x)))
        (cubeSet R) volume :=
    integrableOn_vecDot_of_memVectorL2 hDiff hSymmDiff
  show IntegrableOn
    (fun x =>
      (1 / 2 : ℝ) *
        vecDot
          (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
            canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)
          (matVecMul (symmPart ((a.coeffOn R).toCoeffField x))
            (canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x -
              canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x)))
      (cubeSet R) volume
  simpa [additivityDiffHalfEnergyDensityOnFamilyOnCube, topGrad, childGrad, coeff] using!
    hQuad.const_mul (1 / 2 : ℝ)

/-! ### Difference energy and the response partition defect -/

/--
One-cube second variation in the concrete Section 5.3 notation.  If a child
cube solution has the parent gradient, then the local difference half-energy is
the gap between the child canonical response and that solution's response
value.
-/
theorem cubeAverage_additivityDiffHalfEnergyDensityOnFamilyOnCube_eq_responseJOnCube_sub_responseValue_of_grad_eq
    {d : ℕ} (a : Ch02.TriadicCoeffFamily d) (Q R : TriadicCube d)
    (p q : Vec d)
    (w : Ch02.Solution (Ch02.cubeDomain R) (a.coeffOn R))
    (hgrad : w.toH1.grad =
      canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q) :
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q) =
      Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q -
        Ch02.responseValue (Ch02.cubeDomain R) (a.coeffOn R) p q w := by
  have hmax :
      Ch02.IsResponseMaximizer (Ch02.cubeDomain R) (a.coeffOn R) p q
        (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q) := by
    simpa [canonicalMaximizerSolutionOnCube] using
      Ch02.canonicalMaximizer_isMaximizer
        (Ch02.responseExistenceTheory (Ch02.cubeDomain R) (a.coeffOn R)) p q
  have hsecond :=
    Ch02.secondVariation_eq_of_isResponseMaximizer hmax w
  have henergy :
      Ch02.secondVariationEnergyValue (Ch02.cubeDomain R) (a.coeffOn R)
          (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q) w =
        cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q) := by
    unfold Ch02.secondVariationEnergyValue
    rw [ch02_average_cubeDomain_eq_cubeAverage]
    congr 1
    funext x
    have hw :
        w.toH1.grad x = canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x := by
      rw [hgrad]
    let topGrad : Vec d := canonicalMaximizerGradientOnCube Q (a.coeffOn Q) p q x
    let childGrad : Vec d := canonicalMaximizerGradientOnCube R (a.coeffOn R) p q x
    let A : Mat d := (a.coeffOn R).toCoeffField x
    have hdiff : childGrad - topGrad = -(topGrad - childGrad) := by
      ext i
      simp [topGrad, childGrad]
    have hquad_same :
        vecDot (childGrad - topGrad)
            (matVecMul (symmPart A) (childGrad - topGrad)) =
          vecDot (topGrad - childGrad)
            (matVecMul (symmPart A) (topGrad - childGrad)) := by
      calc
        vecDot (childGrad - topGrad)
            (matVecMul (symmPart A) (childGrad - topGrad))
            =
          vecDot (-(topGrad - childGrad))
            (matVecMul (symmPart A) (-(topGrad - childGrad))) := by
              rw [hdiff]
        _ =
          vecDot (topGrad - childGrad)
            (matVecMul (symmPart A) (topGrad - childGrad)) := by
              rw [matVecMul_neg, vecDot_neg_right, vecDot_neg_left, neg_neg]
    calc
      (1 / 2 : ℝ) *
          vecDot
            ((canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q).toH1.grad x -
              w.toH1.grad x)
            (matVecMul
              (symmPart ((a.coeffOn R).toCoeffField x))
              ((canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q).toH1.grad x -
                w.toH1.grad x))
          =
        (1 / 2 : ℝ) *
          vecDot (childGrad - topGrad)
            (matVecMul (symmPart A) (childGrad - topGrad)) := by
            simp [childGrad, topGrad, A, canonicalMaximizerGradientOnCube, hw]
      _ =
        (1 / 2 : ℝ) *
          vecDot (topGrad - childGrad)
            (matVecMul (symmPart A) (topGrad - childGrad)) := by
            rw [hquad_same]
      _ = additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q x := by
            simp [additivityDiffHalfEnergyDensityOnFamilyOnCube,
              topGrad, childGrad, A]
  calc
    cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube a Q R p q)
        =
          Ch02.secondVariationEnergyValue (Ch02.cubeDomain R) (a.coeffOn R)
            (canonicalMaximizerSolutionOnCube R (a.coeffOn R) p q) w :=
          henergy.symm
    _ =
        Ch02.responseJ (Ch02.cubeDomain R) (a.coeffOn R) p q -
          Ch02.responseValue (Ch02.cubeDomain R) (a.coeffOn R) p q w := by
          exact hsecond.symm

@[simp] theorem h1Function_restrict_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVopen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVopen hVU).grad = u.grad :=
  rfl

end

end JUpperBoundWeakNorms
end Section53
end Ch05
end Book
end Homogenization
