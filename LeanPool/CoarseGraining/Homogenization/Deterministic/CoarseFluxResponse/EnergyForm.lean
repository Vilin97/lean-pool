/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.PrivateLemmas
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincare.Setup.UniformBounds

/-! # Energy Form -/

namespace Homogenization

noncomputable section

open scoped BigOperators MatrixOrder Pointwise


/-- Single-cube response-control theorem for the actual flux defect measured
against the natural `symmPart a0` energy form. -/
theorem cubeAverageFluxDefect_energyForm_le_normalizedBlockResponseMax_mul_energyAverage_of_scalarCanonicalMaximizer
    {d : ℕ} [NeZero d] (R : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    {lam Lam lam0 Lam0 : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet R) a)
    (ha0 : IsEllipticMatrix lam0 Lam0 a0)
    (w : AHarmonicFunction a (cubeSet R))
    (v : ScalarCanonicalMaximizer (cubeSet R)
      (-matVecMul ((symmPart a0)⁻¹)
        (cubeAverageVec R
          (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))
      (-matVecMul (matTranspose a0)
        (matVecMul ((symmPart a0)⁻¹)
          (cubeAverageVec R
            (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))) a) :
    vecDot
        (cubeAverageVec R
          (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)))
        (matVecMul ((symmPart a0)⁻¹)
          (cubeAverageVec R
            (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))
      ≤
      ((4 : ℝ) * normalizedBlockResponseMax R a a0) *
        cubeAverage R (scalarVariationEnergyIntegrand a w) := by
  let := isFiniteMeasureVolumeMeasureOnCubeSet R
  let defect : Vec d → Vec d :=
    fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)
  let D : Vec d := cubeAverageVec R defect
  let ξ : Vec d := matVecMul ((symmPart a0)⁻¹) D
  let P : BlockVec d := (0, D)
  let Q0 : BlockVec d := blockMatVecMul (blockMatrixOfCoeff a0) P
  have hsdet : IsUnit (symmPart a0).det := isUnit_det_symmPart_of_isEllipticMatrix ha0
  have hsξ : matVecMul (symmPart a0) ξ = D := by
    dsimp [ξ]
    rw [matVecMul_mul, Matrix.mul_nonsing_inv _ hsdet]
    funext i
    simp [matVecMul, Matrix.one_apply]
  have hQ0snd : Q0.2 = ξ := by
    change (blockMatVecMul (blockMatrixOfCoeff a0) ((0 : Vec d), D)).2 = ξ
    rw [blockMatVecMul_blockMatrixOfCoeff_snd]
    simp [ξ, matVecMul_zero]
  have hQ0fst : Q0.1 = matVecMul (skewPart a0) ξ := by
    change (blockMatVecMul (blockMatrixOfCoeff a0) ((0 : Vec d), D)).1 =
      matVecMul (skewPart a0) ξ
    rw [blockMatVecMul_blockMatrixOfCoeff_fst]
    simp [ξ, matVecMul_zero]
  have hsplit : a0 = symmPart a0 + skewPart a0 := by
    ext i j
    simp [symmPart, skewPart, sub_eq_add_neg]
    ring
  have hsplitT : matTranspose a0 = symmPart a0 - skewPart a0 := by
    ext i j
    simp [symmPart, skewPart, matTranspose, sub_eq_add_neg]
    ring
  have hresp_le :
      ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a ≤
        (2 : ℝ) * BlockJ (cubeSet R) P Q0 a := by
    have hvol : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
      rw [volume_cubeSet_toReal]
      exact (cubeVolume_pos R).ne'
    have hblock :
        BlockJ (cubeSet R) P Q0 a =
          (1 / 2 : ℝ) * ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a +
            (1 / 2 : ℝ) *
              ResponseJ (cubeSet R) (ξ) (matVecMul a0 ξ)
                (Homogenization.adjointCoeffField a) := by
      have hq :
          Q0.1 - D = -matVecMul (matTranspose a0) ξ := by
        rw [hQ0fst]
        rw [show D = matVecMul (symmPart a0) ξ by simpa using hsξ.symm]
        rw [hsplitT]
        ext i
        simp [matVecMul, sub_eq_add_neg]
        have hsum :
            ∑ x, (symmPart a0 i x + -skewPart a0 i x) * ξ x =
              ∑ x, symmPart a0 i x * ξ x + ∑ x, (-skewPart a0 i x) * ξ x := by
          calc
            ∑ x, (symmPart a0 i x + -skewPart a0 i x) * ξ x =
                ∑ x, (symmPart a0 i x * ξ x + (-skewPart a0 i x) * ξ x) := by
                  refine Finset.sum_congr rfl ?_
                  intro x hx
                  ring
            _ = ∑ x, symmPart a0 i x * ξ x + ∑ x, (-skewPart a0 i x) * ξ x := by
                  rw [Finset.sum_add_distrib]
        rw [hsum]
        have hnegSkew :
            -(∑ x, -skewPart a0 i x * ξ x) = ∑ x, skewPart a0 i x * ξ x := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro x hx
          ring
        calc
          ∑ j, skewPart a0 i j * ξ j + -∑ j, symmPart a0 i j * ξ j =
              -∑ j, symmPart a0 i j * ξ j + -(∑ j, -skewPart a0 i j * ξ j) := by
                rw [hnegSkew]
                ring
          _ = -(∑ x, symmPart a0 i x * ξ x + ∑ x, -skewPart a0 i x * ξ x) := by
                ring
      have hqa :
          Q0.1 + D = matVecMul a0 ξ := by
        rw [hQ0fst]
        rw [show D = matVecMul (symmPart a0) ξ by simpa using hsξ.symm]
        rw [hsplit]
        ext i
        simp [symmPart, skewPart, matVecMul, sub_eq_add_neg]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro x hx
        ring
      rw [show Q0 = (Q0.1, ξ) by ext <;> simp [hQ0snd]]
      change BlockJ (cubeSet R) ((0 : Vec d), D) (Q0.1, ξ) a =
          (1 / 2 : ℝ) * ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a +
            (1 / 2 : ℝ) *
              ResponseJ (cubeSet R) ξ (matVecMul a0 ξ) (Homogenization.adjointCoeffField a)
      rw [blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
        (a := a) (U := cubeSet R) (measurableSet_cubeSet R) hEll hvol
        (p := 0) (pStar := ξ) (q := D) (qStar := Q0.1)]
      simp [hq, hqa]
    have hadj_nonneg :
        0 ≤ ResponseJ (cubeSet R) ξ (matVecMul a0 ξ) (Homogenization.adjointCoeffField a) :=
      responseJ_nonneg (cubeSet R) ξ (matVecMul a0 ξ) (Homogenization.adjointCoeffField a)
    linarith [hblock, hadj_nonneg]
  have hblock_le :
      BlockJ (cubeSet R) P Q0 a ≤ normalizedBlockResponseMax R a a0 *
        vecDot D ξ := by
    have hquadratic :
        blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) = vecDot D ξ := by
      dsimp [P, ξ]
      rw [blockMatrixOfCoeff_quadratic_eq]
      simp [vecDot_zero_left, matVecMul_zero]
    calc
      BlockJ (cubeSet R) P Q0 a
          ≤ normalizedBlockResponseMax R a a0 *
              blockVecDot P (blockMatVecMul (blockMatrixOfCoeff a0) P) := by
                simpa [Q0] using
                  blockJ_le_normalizedBlockResponseMax_mul_blockQuadratic_of_isEllipticMatrix
                    R a a0 hEll ha0 P
      _ = normalizedBlockResponseMax R a a0 * vecDot D ξ := by rw [hquadratic]
  have hlin :
      (vecDot D ξ) ^ 2 ≤
        cubeAverage R (scalarVariationEnergyIntegrand a w) *
          (2 * ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a) := by
    let avgGrad : Vec d := fun i => volumeAverage (cubeSet R) (fun x => w.toH1.grad x i)
    let avgFlux : Vec d :=
      fun i => volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i)
    have hraw :=
      ScalarCanonicalMaximizer.linearResponseSq
        (U := cubeSet R) (a := a) (p := -ξ) (q := -matVecMul (matTranspose a0) ξ)
        (lam := lam) (Lam := Lam) v hEll
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w
    have havgGrad :
        cubeAverageVec R (fun x => w.toH1.grad x) = avgGrad := by
      funext i
      simp [avgGrad, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
    have havgFlux :
        cubeAverageVec R (fun x => matVecMul (a x) (w.toH1.grad x)) = avgFlux := by
      funext i
      simp [avgFlux, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
    have hD :
        D = avgFlux - matVecMul a0 avgGrad := by
      ext i
      have hgradCoord :
          ∀ j : Fin d, MeasureTheory.IntegrableOn (fun x => w.toH1.grad x j) (cubeSet R) := by
        intro j
        exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 w.toH1.grad_memVectorL2 j
      have hfluxMem :
          MemVectorL2 (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x)) :=
        memVectorL2_matVecMul_of_isEllipticFieldOn hEll w.toH1.grad_memVectorL2
      have hfluxCoord :
          ∀ j : Fin d,
            MeasureTheory.IntegrableOn
              (fun x => matVecMul (a x) (w.toH1.grad x) j) (cubeSet R) := by
        intro j
        exact CorrectionFieldData.integrableOn_coord_of_memVectorL2 hfluxMem j
      have hA0avg :
          volumeAverage (cubeSet R) (fun x => matVecMul a0 (w.toH1.grad x) i) =
            matVecMul a0 avgGrad i := by
        calc
          volumeAverage (cubeSet R) (fun x => matVecMul a0 (w.toH1.grad x) i)
              = ∑ j, volumeAverage (cubeSet R) (fun x => a0 i j * w.toH1.grad x j) := by
                  rw [show (fun x => matVecMul a0 (w.toH1.grad x) i) =
                      fun x => ∑ j, a0 i j * w.toH1.grad x j by
                        funext x
                        simp [matVecMul]]
                  exact volumeAverage_sum (U := cubeSet R) Finset.univ
                    (fun j x => a0 i j * w.toH1.grad x j)
                    (fun j hj => (hgradCoord j).const_mul (a0 i j))
          _ = ∑ j, a0 i j * volumeAverage (cubeSet R) (fun x => w.toH1.grad x j) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                rw [show (fun x => a0 i j * w.toH1.grad x j) =
                    (a0 i j) • fun x => w.toH1.grad x j by
                      funext x
                      simp]
                rw [volumeAverage_smul]
          _ = matVecMul a0 avgGrad i := by
                simp [avgGrad, matVecMul]
      calc
        D i = volumeAverage (cubeSet R) (fun x => defect x i) := by
          simp [D, cubeAverageVec, volumeAverage_cubeSet_eq_cubeAverage]
        _ = volumeAverage (cubeSet R) (fun x => matVecMul (a x) (w.toH1.grad x) i) -
              volumeAverage (cubeSet R) (fun x => matVecMul a0 (w.toH1.grad x) i) := by
                apply volumeAverage_sub (hfluxCoord i)
                have hsum :
                    MeasureTheory.IntegrableOn
                      (fun x => ∑ j, a0 i j * w.toH1.grad x j) (cubeSet R) := by
                    refine MeasureTheory.integrable_finsetSum Finset.univ ?_
                    intro j hj
                    exact (hgradCoord j).const_mul (a0 i j)
                simpa [defect, matVecMul] using hsum
        _ = avgFlux i - volumeAverage (cubeSet R) (fun x => matVecMul a0 (w.toH1.grad x) i) := by
            simp [avgFlux]
        _ = avgFlux i - matVecMul a0 avgGrad i := by
            rw [hA0avg]
    have hleft :
        volumeAverage (cubeSet R) (fun x => vecDot (-matVecMul (matTranspose a0) ξ) (w.toH1.grad x)) -
            volumeAverage (cubeSet R) (fun x => vecDot (-ξ) (matVecMul (a x) (w.toH1.grad x))) =
          vecDot D ξ := by
      have hpair :=
        basic_cg_identities_average_pairing_eq_vecDot_average_gradient_sub_average_flux
          (cubeSet R) a (-ξ) (-matVecMul (matTranspose a0) ξ)
          (ResponseLinearIntegrabilityData.of_isEllipticFieldOn hEll) w
      calc
        volumeAverage (cubeSet R) (fun x => vecDot (-matVecMul (matTranspose a0) ξ) (w.toH1.grad x)) -
            volumeAverage (cubeSet R) (fun x => vecDot (-ξ) (matVecMul (a x) (w.toH1.grad x))) =
            vecDot (-matVecMul (matTranspose a0) ξ) avgGrad - vecDot (-ξ) avgFlux := by
              simpa [avgGrad, avgFlux] using hpair
        _ = -vecDot (matVecMul a0 avgGrad) ξ + vecDot ξ avgFlux := by
              rw [vecDot_neg_left, vecDot_neg_left]
              rw [vecDot_comm (matVecMul (matTranspose a0) ξ) avgGrad]
              rw [vecDot_matVecMul_transpose avgGrad ξ a0]
              ring
        _ = vecDot ξ avgFlux - vecDot ξ (matVecMul a0 avgGrad) := by
              rw [vecDot_comm (matVecMul a0 avgGrad) ξ]
              ring
        _ = vecDot ξ (avgFlux - matVecMul a0 avgGrad) := by
              simp [sub_eq_add_neg, vecDot_add_right, vecDot_neg_right]
        _ = vecDot ξ D := by rw [hD]
        _ = vecDot D ξ := by rw [vecDot_comm]
    have hleft' :
        cubeAverage R (fun x => vecDot (-matVecMul (matTranspose a0) ξ) (w.toH1.grad x)) -
            cubeAverage R (fun x => vecDot (-ξ) (matVecMul (a x) (w.toH1.grad x))) =
          vecDot D ξ := by
      simpa [volumeAverage_cubeSet_eq_cubeAverage] using hleft
    have hraw' :
        (cubeAverage R (fun x => vecDot (-matVecMul (matTranspose a0) ξ) (w.toH1.grad x)) -
            cubeAverage R (fun x => vecDot (-ξ) (matVecMul (a x) (w.toH1.grad x)))) ^ 2 ≤
          cubeAverage R (scalarVariationEnergyIntegrand a w) *
            (2 * ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a) := by
      simpa [volumeAverage_cubeSet_eq_cubeAverage] using hraw
    have hleft_sq :
        (vecDot D ξ) ^ 2 =
          (cubeAverage R (fun x => vecDot (-matVecMul (matTranspose a0) ξ) (w.toH1.grad x)) -
            cubeAverage R (fun x => vecDot (-ξ) (matVecMul (a x) (w.toH1.grad x)))) ^ 2 := by
      rw [hleft']
    rw [hleft_sq]
    exact hraw'
  have ht_nonneg :
      0 ≤ vecDot D ξ := by
    have hlower := lowerBound_symmPartInv_of_isEllipticMatrix ha0 D
    rcases ha0 with ⟨hlam0_pos, hlam0Lam0, -, -⟩
    have hLam0_pos : 0 < Lam0 := lt_of_lt_of_le hlam0_pos hlam0Lam0
    have hcoeff_nonneg : 0 ≤ lam0 * (Lam0⁻¹ * Lam0⁻¹) := by
      positivity
    have hterm_nonneg : 0 ≤ (lam0 * (Lam0⁻¹ * Lam0⁻¹)) * vecNormSq D := by
      exact mul_nonneg hcoeff_nonneg (vecNormSq_nonneg D)
    simpa [ξ, D] using (le_trans hterm_nonneg hlower)
  by_cases ht : vecDot D ξ = 0
  · rw [ht]
    have henergy_nonneg : 0 ≤ cubeAverage R (scalarVariationEnergyIntegrand a w) := by
      simpa [volumeAverage_cubeSet_eq_cubeAverage] using
        (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
          (U := cubeSet R) a hEll w)
    nlinarith [normalizedBlockResponseMax_nonneg R a a0, henergy_nonneg]
  · have ht_pos : 0 < vecDot D ξ := lt_of_le_of_ne ht_nonneg (by simpa [eq_comm] using ht)
    have hresp_scaled :
        (2 : ℝ) * ResponseJ (cubeSet R) (-ξ) (-matVecMul (matTranspose a0) ξ) a ≤
          (4 : ℝ) * normalizedBlockResponseMax R a a0 * vecDot D ξ := by
      nlinarith [hresp_le, hblock_le]
    have henergy_nonneg :
        0 ≤ cubeAverage R (scalarVariationEnergyIntegrand a w) := by
      simpa [volumeAverage_cubeSet_eq_cubeAverage] using
        (volumeAverage_scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn
          (U := cubeSet R) a hEll w)
    have hsq :
        (vecDot D ξ) ^ 2 ≤
          cubeAverage R (scalarVariationEnergyIntegrand a w) *
            ((4 : ℝ) * normalizedBlockResponseMax R a a0 * vecDot D ξ) := by
      exact le_trans hlin <| mul_le_mul_of_nonneg_left hresp_scaled henergy_nonneg
    nlinarith [hsq]

/-- Descendant-local Chapter-3 witness package for the actual flux defect
relative to the constant matrix `a0`. -/
def DescendantScalarCanonicalFluxDefectData {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) (defect : Vec d → Vec d)
    (energy : Vec d → ℝ) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    ∃ lam, ∃ Lam, ∃ w : AHarmonicFunction a (cubeSet R),
      IsEllipticFieldOn lam Lam (cubeSet R) a ∧
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul ((symmPart a0)⁻¹) (cubeAverageVec R defect))
          (-matVecMul (matTranspose a0)
            (matVecMul ((symmPart a0)⁻¹) (cubeAverageVec R defect))) a) ∧
      (∀ x ∈ cubeSet R,
        defect x = matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)) ∧
      (∀ x ∈ cubeSet R, energy x = scalarVariationEnergyIntegrand a w x)

/-- Descendant-local Chapter-3 witness package for the actual flux defect of a
single global harmonic field on `cubeSet Q`. Each descendant comes with a
local harmonic witness whose gradient agrees with the global field on that
cube and which carries the needed scalar canonical maximizer. -/
def DescendantScalarCanonicalFluxDefectAHarmonicData {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) (a0 : Mat d) (u : AHarmonicFunction a (cubeSet Q)) : Prop :=
  ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
    ∃ lam, ∃ Lam, ∃ w : AHarmonicFunction a (cubeSet R),
      IsEllipticFieldOn lam Lam (cubeSet R) a ∧
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul ((symmPart a0)⁻¹)
            (cubeAverageVec R
              (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))
          (-matVecMul (matTranspose a0)
            (matVecMul ((symmPart a0)⁻¹)
              (cubeAverageVec R
                (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))) a) ∧
      (∀ x ∈ cubeSet R, w.toH1.grad x = u.toH1.grad x)

theorem descendantScalarCanonicalFluxDefectData_of_aHarmonicData {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d)
    (u : AHarmonicFunction a (cubeSet Q))
    (hdesc : DescendantScalarCanonicalFluxDefectAHarmonicData Q a a0 u) :
    DescendantScalarCanonicalFluxDefectData Q a a0
      (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (scalarVariationEnergyIntegrand a u) := by
  intro j R hR
  rcases hdesc j R hR with
    ⟨lam, Lam, w, hEll, hv, hgrad⟩
  have hdefect :
      ∀ x ∈ cubeSet R,
        matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x) =
          matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x) := by
    intro x hx
    simp [hgrad x hx]
  have henergy :
      ∀ x ∈ cubeSet R,
        scalarVariationEnergyIntegrand a u x = scalarVariationEnergyIntegrand a w x := by
    intro x hx
    simp [scalarVariationEnergyIntegrand, hgrad x hx]
  have hv' :
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul ((symmPart a0)⁻¹)
            (cubeAverageVec R
              (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))))
          (-matVecMul (matTranspose a0)
            (matVecMul ((symmPart a0)⁻¹)
              (cubeAverageVec R
                (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))))) a) := by
    rcases hv with ⟨v⟩
    have hdefectavg :
        cubeAverageVec R
            (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x)) =
          cubeAverageVec R
            (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)) :=
      cubeAverageVec_eq_of_eq_on_cubeSet hdefect
    refine ⟨?_⟩
    simpa [hdefectavg] using v
  exact ⟨lam, Lam, w, hEll, hv', hdefect, henergy⟩

/-- Every descendant cube of a global harmonic field on `cubeSet Q` carries the
scalar canonical maximizer needed for the flux-defect argument. -/
theorem descendantScalarCanonicalFluxDefectAHarmonicData_of_aHarmonicFunction
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q)) :
    DescendantScalarCanonicalFluxDefectAHarmonicData Q a a0 u := by
  intro j R hR
  have hEllR :
      IsEllipticFieldOn lam Lam (cubeSet R) a :=
    hEll.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtDepth hR)
  let w : AHarmonicFunction a (cubeSet R) := u.restrictToSubcube hEll hR
  have hne : Set.Nonempty (cubeSet R) := by
    refine ⟨cubeCenter R, openCubeSet_subset_cubeSet R ?_⟩
    rw [← ball_cubeCenter_eq_openCubeSet]
    simpa [Metric.mem_ball] using cubeRadius_pos R
  let : Fact (MeasureTheory.volume (cubeSet R) < ⊤) := by
    refine ⟨?_⟩
    simpa using volume_cubeSet_lt_top R
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (cubeSet R)) := by
    change MeasureTheory.IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet R))
    infer_instance
  have hv :
      Nonempty
        (ScalarCanonicalMaximizer (cubeSet R)
          (-matVecMul ((symmPart a0)⁻¹)
            (cubeAverageVec R
              (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x))))
          (-matVecMul (matTranspose a0)
            (matVecMul ((symmPart a0)⁻¹)
              (cubeAverageVec R
                (fun x => matVecMul (a x) (w.toH1.grad x) - matVecMul a0 (w.toH1.grad x)))))
          a) := by
    exact
      ScalarCanonicalMaximizer.nonempty_of_hodgeConverseCriterion_of_isEllipticFieldOn
        (U := cubeSet R) (a := a) hne
        (hodgeConverseCriterion_cubeSet_triadicCube R) hEllR _ _
  refine ⟨lam, Lam, w, hEllR, hv, ?_⟩
  intro x hx
  simp [w]

/-- Direct descendant-local flux-defect witness package for one harmonic field
on `cubeSet Q`, with no separate scalar-canonical assumptions. -/
theorem descendantScalarCanonicalFluxDefectData_of_aHarmonicFunction
    {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) (a0 : Mat d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (u : AHarmonicFunction a (cubeSet Q)) :
    DescendantScalarCanonicalFluxDefectData Q a a0
      (fun x => matVecMul (a x) (u.toH1.grad x) - matVecMul a0 (u.toH1.grad x))
      (scalarVariationEnergyIntegrand a u) := by
  exact
    descendantScalarCanonicalFluxDefectData_of_aHarmonicData
      (Q := Q) (a := a) (a0 := a0) (u := u)
      (descendantScalarCanonicalFluxDefectAHarmonicData_of_aHarmonicFunction
        (Q := Q) (a := a) (a0 := a0) hEll u)


end

end Homogenization
