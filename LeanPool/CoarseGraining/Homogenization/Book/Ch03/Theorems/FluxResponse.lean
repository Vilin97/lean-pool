/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Definitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError
import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseFluxResponse.Response
import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakNormInterfaces.AECongruence

/-! # Flux Response -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Section 3.1.3: Coarse-grained flux-response estimate

This file proves the public statement of
`l.coarse.grained.flux.response.deterministic.theory`.

## Audit tag

Claim: prove and package the Book-facing coarse-grained flux-response estimate
from the deterministic response identities.

Downstream target: Chapter 3 public theorem aggregation and RHS flux-response
extensions.  This file should keep one `CoarseFluxResponseTheory` surface and
avoid compatibility constructor families.
-/

noncomputable section

private theorem scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_old
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1) F =
      Homogenization.cubeBesovNegativeVectorSeminorm Q s F := by
  simp [scaleNormalizedNegativeBesovVectorNorm, negativeBesovVectorPartialNormFinite,
    negativeBesovVectorDepthSeminorm, negativeBesovVectorDepthAverage,
    Homogenization.cubeBesovNegativeVectorSeminorm,
    Homogenization.cubeBesovNegativeVectorPartialSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthSeminorm,
    Homogenization.cubeBesovNegativeVectorDepthAverage]

private theorem old_blockJ_cube_eq_book_doubled {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k)
    (P Q' : BlockVec d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    BlockJ (cubeSet R) P Q' A =
      Ch02.doubledResponseJ (Ch02.cubeDomain R) (a.coeffOn R) P Q' := by
  intro A
  let := isFiniteMeasureVolumeMeasureOnCubeSet R
  have hsubOpen : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  let aRpw : Ch02.CoeffOn (Ch02.cubeDomain R) :=
    Ch02.pointwiseCoeffOnRestrict (a.coeffOn Q) hsubOpen
  have haeeq : Ch02.CoeffOn.AEEq (a.coeffOn R) aRpw := by
    simpa [aRpw] using
      Ch02.coeffOn_descendant_aeeq_pointwiseCoeffOnRestrict (a := a) hk hR
  have hEllQ : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet Q) A := by
    simpa [A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet Q (a.coeffOn Q)
  have hEllR : IsEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam (cubeSet R) A :=
    hEllQ.mono (measurableSet_cubeSet R) (cubeSet_subset_of_mem_descendantsAtScale hk hR)
  have hvolR : (MeasureTheory.volume (cubeSet R)).toReal ≠ 0 := by
    rw [volume_cubeSet_toReal]
    exact (cubeVolume_pos R).ne'
  have hbook_scalar_pw :=
    (Ch02.doubledResponseTheory (Ch02.cubeDomain R) aRpw).doubledResponseJ_eq_scalar
      P.1 Q'.2 P.2 Q'.1
  calc
    BlockJ (cubeSet R) P Q' A =
        (1 / 2 : ℝ) * ResponseJ (cubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) A +
          (1 / 2 : ℝ) * ResponseJ (cubeSet R) (Q'.2 + P.1) (Q'.1 + P.2)
            (adjointCoeffField A) := by
          exact blockJ_eq_half_responseJ_adjoint_sum_of_isEllipticFieldOn
            (a := A) (U := cubeSet R) (measurableSet_cubeSet R) hEllR hvolR
            (p := P.1) (pStar := Q'.2) (q := P.2) (qStar := Q'.1)
    _ = (1 / 2 : ℝ) * ResponseJ (openCubeSet R) (P.1 - Q'.2) (Q'.1 - P.2) A +
          (1 / 2 : ℝ) * ResponseJ (openCubeSet R) (Q'.2 + P.1) (Q'.1 + P.2)
            (adjointCoeffField A) := by
          rw [ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R,
            ResponseJ_cubeSet_eq_openCubeSet_of_triadicCube R]
    _ = (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain R) aRpw
            (P.1 - Q'.2) (Q'.1 - P.2) +
          (1 / 2 : ℝ) * Ch02.responseJ (Ch02.cubeDomain R) aRpw.transpose
            (Q'.2 + P.1) (Q'.1 + P.2) := by
          rw [Internal.Ch02.book_responseJ_eq_ResponseJ,
            Internal.Ch02.book_responseJ_eq_ResponseJ]
          rfl
    _ = Ch02.doubledResponseJ (Ch02.cubeDomain R) aRpw P Q' := by
          exact hbook_scalar_pw.symm
    _ = Ch02.doubledResponseJ (Ch02.cubeDomain R) (a.coeffOn R) P Q' := by
          rw [Ch02.doubledResponseJ_eq_ofAEEq haeeq P Q']

private theorem old_normalizedBlockResponseValueSet_eq_book {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Homogenization.normalizedBlockResponseValueSet R A a0 =
      Ch02.normalizedBlockResponseValueSet R a a0 := by
  intro A
  ext m
  constructor
  · rintro ⟨e, he, hm⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [Ch02.fullBlockVecNormSq, Homogenization.fullBlockVecNormSq] using he
    · have hbridge := old_blockJ_cube_eq_book_doubled (a := a) (Q := Q) (R := R)
        (k := k) hk hR
        (ofFullBlockVec (Matrix.mulVec (Homogenization.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Homogenization.constantFullBlockMatrixSqrt a0) e))
      simpa [A, Ch02.constantFullBlockMatrixInvSqrt, Homogenization.constantFullBlockMatrixInvSqrt,
        Ch02.constantFullBlockMatrixSqrt, Homogenization.constantFullBlockMatrixSqrt,
        Ch02.constantFullBlockMatrix, Homogenization.constantFullBlockMatrix,
        Ch02.constantBlockMatrix, Homogenization.blockMatrixOfCoeff] using hm.trans hbridge
  · rintro ⟨e, he, hm⟩
    refine ⟨e, ?_, ?_⟩
    · simpa [Ch02.fullBlockVecNormSq, Homogenization.fullBlockVecNormSq] using he
    · have hbridge := old_blockJ_cube_eq_book_doubled (a := a) (Q := Q) (R := R)
        (k := k) hk hR
        (ofFullBlockVec (Matrix.mulVec (Homogenization.constantFullBlockMatrixInvSqrt a0) e))
        (ofFullBlockVec (Matrix.mulVec (Homogenization.constantFullBlockMatrixSqrt a0) e))
      simpa [A, Ch02.constantFullBlockMatrixInvSqrt, Homogenization.constantFullBlockMatrixInvSqrt,
        Ch02.constantFullBlockMatrixSqrt, Homogenization.constantFullBlockMatrixSqrt,
        Ch02.constantFullBlockMatrix, Homogenization.constantFullBlockMatrix,
        Ch02.constantBlockMatrix, Homogenization.blockMatrixOfCoeff] using hm.trans hbridge.symm

private theorem old_normalizedBlockResponseMax_eq_book {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) {Q R : TriadicCube d} {k : ℤ}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) (a0 : Mat d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Homogenization.normalizedBlockResponseMax R A a0 =
      Ch02.normalizedBlockResponseMax R a a0 := by
  intro A
  unfold Homogenization.normalizedBlockResponseMax Ch02.normalizedBlockResponseMax
  rw [old_normalizedBlockResponseValueSet_eq_book (a := a) (Q := Q) (R := R) (k := k) hk hR a0]

private theorem old_maxDescendantNormalizedBlockResponseAtScale_eq_book {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a0 : Mat d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Homogenization.maxDescendantNormalizedBlockResponseAtScale Q k A a0 =
      Ch02.maxDescendantNormalizedBlockResponseAtScale Q k a a0 := by
  intro A
  unfold Homogenization.maxDescendantNormalizedBlockResponseAtScale
    Ch02.maxDescendantNormalizedBlockResponseAtScale
  rw [Ch02.finsetSupReal_eq_finsetSsup]
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, (old_normalizedBlockResponseMax_eq_book
      (a := a) (Q := Q) (R := R) (k := k) hk hR a0).symm⟩
  · rintro ⟨R, hR, rfl⟩
    exact ⟨R, hR, old_normalizedBlockResponseMax_eq_book
      (a := a) (Q := Q) (R := R) (k := k) hk hR a0⟩

private theorem old_scaleResponseAtScale_infinity_eq_book {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) {k : ℤ}
    (hk : k ≤ Q.scale) (a0 : Mat d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Homogenization.scaleResponseAtScale Q k Homogenization.MultiscaleExponent.infinity A a0 =
      Ch02.scaleResponseAtScale Q k .infinity a a0 := by
  intro A
  rw [Homogenization.scaleResponseAtScale_infinity_eq, Ch02.scaleResponseAtScale_infinity_eq,
    old_maxDescendantNormalizedBlockResponseAtScale_eq_book (a := a) Q hk a0]

private theorem old_homogenizationErrorOnCube_infinity_one_eq_book {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (s : ℝ) (a0 : Mat d) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Homogenization.HomogenizationErrorOnCube Q s Homogenization.MultiscaleExponent.infinity
        (Homogenization.MultiscaleExponent.finite 1) A a0 =
      Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 := by
  intro A
  rw [Homogenization.homogenizationErrorOnCube_infinity_one_eq_tsum,
    Ch02.homogenizationErrorOnCube_infinity_one_eq_tsum]
  apply tsum_congr
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [← Ch02.geometricWeight_eq_old]
  rw [old_scaleResponseAtScale_infinity_eq_book (a := a) Q hk a0]

private theorem old_homogenizationErrorOnCube_infinity_one_terms_summable
    {d : ℕ} [NeZero d]
    (a : Ch02.TriadicCoeffFamily d) (Q : TriadicCube d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    let A : CoeffField d :=
      Internal.Ch02.BookCh02.pointwiseCoeffField (Ch02.cubeDomain Q) (a.coeffOn Q)
    Summable fun n : ℕ =>
      Homogenization.geometricWeight s 1 n *
        Homogenization.scaleResponseAtScale Q (Q.scale - (n : ℤ))
          Homogenization.MultiscaleExponent.infinity A a0 := by
  intro A
  have hbook := Ch02.summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 hs
  refine hbook.congr ?_
  intro n
  have hk : Q.scale - (n : ℤ) ≤ Q.scale :=
    sub_le_self _ (by exact_mod_cast Nat.zero_le n)
  rw [Ch02.geometricWeight_eq_old]
  rw [old_scaleResponseAtScale_infinity_eq_book (a := a) Q hk a0]

private theorem sqrt_matNorm_le_dim_mul_constantCoeffMatrixNormHalf {d : ℕ} [NeZero d]
    (a0 : ConstantCoeffMatrix d) :
    Real.sqrt (Homogenization.matNorm a0.matrix) ≤
      (d : ℝ) * constantCoeffMatrixNormHalf a0 := by
  have hop_nonneg : 0 ≤ Ch02.matrixNorm a0.matrix := by
    simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
      Ch02.matrixOperatorNorm_nonneg a0.matrix
  have hmat_le :
      Homogenization.matNorm a0.matrix ≤ (d : ℝ) * Ch02.matrixNorm a0.matrix :=
    Ch02.matNorm_le_dim_mul_matrixNorm a0.matrix
  have hsqrts :
      Real.sqrt (Homogenization.matNorm a0.matrix) ≤
        Real.sqrt ((d : ℝ) * Ch02.matrixNorm a0.matrix) :=
    Real.sqrt_le_sqrt hmat_le
  have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hd_one : 1 ≤ (d : ℝ) := by
    norm_num [Nat.one_le_iff_ne_zero, NeZero.ne d]
  have hM_sq :
      constantCoeffMatrixNormHalf a0 ^ 2 = Ch02.matrixNorm a0.matrix := by
    simpa [constantCoeffMatrixNormHalf, Real.sqrt_eq_rpow] using
      Real.sq_sqrt hop_nonneg
  have hright_nonneg :
      0 ≤ (d : ℝ) * constantCoeffMatrixNormHalf a0 :=
    mul_nonneg hd_nonneg (Real.rpow_nonneg hop_nonneg _)
  have hsq :
      Real.sqrt ((d : ℝ) * Ch02.matrixNorm a0.matrix) ^ 2 ≤
        ((d : ℝ) * constantCoeffMatrixNormHalf a0) ^ 2 := by
    rw [Real.sq_sqrt (mul_nonneg hd_nonneg hop_nonneg), mul_pow, hM_sq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hd_one) hop_nonneg]
  exact hsqrts.trans
    ((sq_le_sq₀ (Real.sqrt_nonneg _) hright_nonneg).mp hsq)

private theorem sqrt_four_mul_matNorm_le_two_mul_dim_mul_constantCoeffMatrixNormHalf {d : ℕ}
    [NeZero d]
    (a0 : ConstantCoeffMatrix d) :
    Real.sqrt ((4 : ℝ) * Homogenization.matNorm a0.matrix) ≤
      2 * ((d : ℝ) * constantCoeffMatrixNormHalf a0) := by
  have hroot_four : Real.sqrt (4 : ℝ) = 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num : 0 ≤ (4 : ℝ))
      (by norm_num : 0 ≤ (2 : ℝ))]
    norm_num
  calc
    Real.sqrt ((4 : ℝ) * Homogenization.matNorm a0.matrix) =
        Real.sqrt (4 : ℝ) * Real.sqrt (Homogenization.matNorm a0.matrix) := by
          rw [Real.sqrt_mul (by norm_num : 0 ≤ (4 : ℝ))]
    _ = 2 * Real.sqrt (Homogenization.matNorm a0.matrix) := by
          rw [hroot_four]
    _ ≤ 2 * ((d : ℝ) * constantCoeffMatrixNormHalf a0) :=
          mul_le_mul_of_nonneg_left
            (sqrt_matNorm_le_dim_mul_constantCoeffMatrixNormHalf a0)
            (by norm_num)

/-- Public theorem package for the coarse-grained flux-response estimate. -/
structure CoarseFluxResponseTheory (d : ℕ) [NeZero d] : Prop where
  exists_constant :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
        (a0 : ConstantCoeffMatrix d) (u : CubeSolution Q a),
        0 < s → s ≤ 1 →
          scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1)
              (solutionFluxDefectField Q a a0 u) ≤
            coarseFluxResponseRHS C Q a a0 s u

/-- Fully proved coarse-grained flux-response estimate. -/
theorem coarseFluxResponse_negativeBesov_le {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffFamily d)
    {s : ℝ} (a0 : ConstantCoeffMatrix d) (u : CubeSolution Q a)
    (hs : 0 < s) (hsle : s ≤ 1) :
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1)
        (solutionFluxDefectField Q a a0 u) ≤
      coarseFluxResponseRHS (10 * (d : ℝ)) Q a a0 s u := by
  let U : Ch02.Domain d := Ch02.cubeDomain Q
  let aQ : Ch02.CoeffOn U := a.coeffOn Q
  let ap : Ch02.CoeffOn U := Internal.Ch02.BookCh02.pointwiseCoeffOn U aQ
  let A : CoeffField d := Internal.Ch02.BookCh02.pointwiseCoeffField U aQ
  have haeeq_ap_a : Ch02.CoeffOn.AEEq ap aQ := by
    simpa [ap] using Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U aQ
  have haeeq_a_ap : Ch02.CoeffOn.AEEq aQ ap := haeeq_ap_a.symm
  let uPw : Ch02.Solution U ap := Ch02.Solution.ofAEEq haeeq_a_ap u
  let uOpen : AHarmonicFunction A (openCubeSet Q) := by
    simpa [U, ap, A] using! uPw
  let uCube : AHarmonicFunction A (cubeSet Q) := uOpen.toCubeSet
  let oldDefect : Vec d → Vec d :=
    fun x => matVecMul (A x) (uCube.toH1.grad x) -
      matVecMul a0.matrix (uCube.toH1.grad x)
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand A uCube x
  have hEll : IsEllipticFieldOn aQ.lam aQ.Lam (cubeSet Q) A := by
    simpa [U, aQ, A] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet Q aQ
  have hsum :
      Summable fun n : ℕ =>
        Homogenization.geometricWeight s 1 n *
          Homogenization.scaleResponseAtScale Q (Q.scale - (n : ℤ))
            Homogenization.MultiscaleExponent.infinity A a0.matrix := by
    simpa [A, U, aQ] using
      old_homogenizationErrorOnCube_infinity_one_terms_summable
        (a := a) Q a0.matrix hs
  have hraw :
      cubeBesovNegativeVectorSeminorm Q s oldDefect ≤
        (Homogenization.geometricDiscount s 1)⁻¹ *
          Homogenization.HomogenizationErrorOnCube Q s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite 1) A a0.matrix *
          (Real.sqrt ((4 : ℝ) * Homogenization.matNorm a0.matrix) *
            Real.sqrt (cubeAverage Q energy)) := by
    have hraw0 :=
      Homogenization.coarseFluxResponse_qone_of_aHarmonicFunction
        Q A a0.matrix s hs hEll a0.elliptic a0.isSymm uCube hsum
    simpa [oldDefect, energy] using hraw0
  have henergy_eq :
      cubeAverage Q energy =
        Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
    have henergy_fun :
        energy = Ch02.variationEnergyIntegrand U ap uPw := by
      have hgrad : uCube.toH1.grad = uPw.toH1.grad :=
        AHarmonicFunction.grad_toCubeSet uOpen
      funext x
      simp only [energy, scalarVariationEnergyIntegrand, Ch02.variationEnergyIntegrand,
        hgrad, U, ap, A, Internal.Ch02.BookCh02.pointwiseCoeffOn]
    have hcube_pw :
        cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := by
      calc
        cubeAverage Q energy = volumeAverage (cubeSet Q) energy := by
          rw [volumeAverage_cubeSet_eq_cubeAverage]
        _ = volumeAverage (openCubeSet Q) energy :=
          ScalarCanonicalMaximizer.volumeAverage_cubeSet_eq_openCubeSet_of_triadicCube Q energy
        _ = Ch02.average U (Ch02.variationEnergyIntegrand U ap uPw) := by
          rw [henergy_fun]
          exact (Internal.Ch02.book_average_eq_volumeAverage U
            (Ch02.variationEnergyIntegrand U ap uPw)).symm
    calc
      cubeAverage Q energy = Ch02.variationEnergyValue U ap uPw := hcube_pw
      _ = Ch02.variationEnergyValue U aQ u := by
        simpa [uPw] using Ch02.variationEnergyValue_ofAEEq haeeq_a_ap u
      _ = Ch02.variationEnergyValue (Ch02.cubeDomain Q) (a.coeffOn Q) u := by
        rfl
  have hA_ae_open :
      A =ᵐ[volumeMeasureOn (openCubeSet Q)] (a.coeffOn Q).toCoeffField := by
    simpa [A, U, aQ, volumeMeasureOn] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U aQ
  have hA_ae_cube :
      A =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)] (a.coeffOn Q).toCoeffField := by
    simpa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet Q]
      using hA_ae_open
  have hdefect_ae :
      oldDefect =ᵐ[MeasureTheory.volume.restrict (cubeSet Q)]
        solutionFluxDefectField Q a a0 u := by
    have hgrad : uCube.toH1.grad = u.toH1.grad :=
      AHarmonicFunction.grad_toCubeSet uOpen
    exact hA_ae_cube.mono fun x hx => by
      simp only [oldDefect, solutionFluxDefectField, hgrad, hx,
        sub_eq_add_neg, add_matVecMul, neg_matVecMul]
  have hdefect_norm_eq :
      cubeBesovNegativeVectorSeminorm Q s oldDefect =
        cubeBesovNegativeVectorSeminorm Q s (solutionFluxDefectField Q a a0 u) :=
    Homogenization.cubeBesovNegativeVectorSeminorm_eq_of_ae_eq_on_cubeSet s hdefect_ae
  let G : ℝ := (Homogenization.geometricDiscount s 1)⁻¹
  let H : ℝ := Ch02.HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0.matrix
  let M : ℝ := constantCoeffMatrixNormHalf a0
  let E : ℝ := solutionEnergyNorm Q a u
  have hH_eq :
      Homogenization.HomogenizationErrorOnCube Q s
          Homogenization.MultiscaleExponent.infinity
          (Homogenization.MultiscaleExponent.finite 1) A a0.matrix = H := by
    simpa [H, A, U, aQ] using
      old_homogenizationErrorOnCube_infinity_one_eq_book
        (a := a) Q s a0.matrix
  have hH_nonneg : 0 ≤ H := by
    simpa [H] using Ch02.HomogenizationErrorOnCube_infinity_one_nonneg Q a a0.matrix hs
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, constantCoeffMatrixNormHalf]
    exact Real.rpow_nonneg
      (by
        simpa [Ch02.matrixNorm_eq_matrixOperatorNorm] using
          Ch02.matrixOperatorNorm_nonneg a0.matrix) _
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, solutionEnergyNorm]
    exact Real.sqrt_nonneg _
  have hG_le : G ≤ 5 * s⁻¹ := by
    simpa [G, Ch02.geometricDiscount_eq_old] using
      Ch02.inv_geometricDiscount_le_five_inv (s := s) (p := 1) hs hsle
        (by norm_num : (1 : ℝ) ≤ 1)
  have hcoef : G * (2 * M * E) ≤ (10 * s⁻¹) * M * E := by
    have hME_nonneg : 0 ≤ 2 * M * E := by
      exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hM_nonneg) hE_nonneg
    calc
      G * (2 * M * E) ≤ (5 * s⁻¹) * (2 * M * E) :=
        mul_le_mul_of_nonneg_right hG_le hME_nonneg
      _ = (10 * s⁻¹) * M * E := by ring
  have hcoef_dim :
      G * (2 * ((d : ℝ) * M) * E) ≤
        (10 * (d : ℝ) * s⁻¹) * M * E := by
    have hME_nonneg : 0 ≤ 2 * ((d : ℝ) * M) * E := by
      exact mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (2 : ℝ))
          (mul_nonneg (Nat.cast_nonneg d) hM_nonneg)) hE_nonneg
    calc
      G * (2 * ((d : ℝ) * M) * E) ≤
          (5 * s⁻¹) * (2 * ((d : ℝ) * M) * E) :=
        mul_le_mul_of_nonneg_right hG_le hME_nonneg
      _ = (10 * (d : ℝ) * s⁻¹) * M * E := by ring
  have hrhs_old_le_public :
      G * H * (2 * ((d : ℝ) * M) * E) ≤
        (10 * (d : ℝ)) * s⁻¹ * M * E * H := by
    calc
      G * H * (2 * ((d : ℝ) * M) * E) =
          (G * (2 * ((d : ℝ) * M) * E)) * H := by ring
      _ ≤ ((10 * (d : ℝ) * s⁻¹) * M * E) * H :=
        mul_le_mul_of_nonneg_right hcoef_dim hH_nonneg
      _ = (10 * (d : ℝ)) * s⁻¹ * M * E * H := by ring
  calc
    scaleNormalizedNegativeBesovVectorNorm Q s (.finite 1)
        (solutionFluxDefectField Q a a0 u)
        = cubeBesovNegativeVectorSeminorm Q s (solutionFluxDefectField Q a a0 u) :=
          scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_old Q s
            (solutionFluxDefectField Q a a0 u)
    _ = cubeBesovNegativeVectorSeminorm Q s oldDefect := hdefect_norm_eq.symm
    _ ≤ (Homogenization.geometricDiscount s 1)⁻¹ *
          Homogenization.HomogenizationErrorOnCube Q s
            Homogenization.MultiscaleExponent.infinity
            (Homogenization.MultiscaleExponent.finite 1) A a0.matrix *
          (Real.sqrt ((4 : ℝ) * Homogenization.matNorm a0.matrix) *
            Real.sqrt (cubeAverage Q energy)) := hraw
    _ ≤ G * H * (2 * ((d : ℝ) * M) * E) := by
          rw [hH_eq, henergy_eq]
          have hsqrt :
              Real.sqrt ((4 : ℝ) * Homogenization.matNorm a0.matrix) * E ≤
                (2 * ((d : ℝ) * M)) * E :=
            mul_le_mul_of_nonneg_right
              (sqrt_four_mul_matNorm_le_two_mul_dim_mul_constantCoeffMatrixNormHalf a0)
              hE_nonneg
          have hGH_nonneg : 0 ≤ G * H := by
            have hG_nonneg : 0 ≤ G := by
              dsimp [G]
              exact inv_nonneg.mpr
                (Homogenization.geometricDiscount_pos (by simpa using hs)).le
            exact mul_nonneg hG_nonneg hH_nonneg
          exact mul_le_mul_of_nonneg_left (by simpa [mul_assoc] using! hsqrt) hGH_nonneg
    _ ≤ (10 * (d : ℝ)) * s⁻¹ * M * E * H := hrhs_old_le_public
    _ = coarseFluxResponseRHS (10 * (d : ℝ)) Q a a0 s u := by
          dsimp [coarseFluxResponseRHS, H, M, E]

/-- Fully proved public coarse-grained flux-response theorem package. -/
theorem coarseFluxResponseTheory {d : ℕ} [NeZero d] :
    CoarseFluxResponseTheory d := by
  refine ⟨?_⟩
  refine ⟨10 * (d : ℝ), ?_, ?_⟩
  · exact mul_pos (by norm_num)
      (by exact_mod_cast Nat.pos_iff_ne_zero.mpr (NeZero.ne d))
  intro Q a s a0 u hs hsle
  exact coarseFluxResponse_negativeBesov_le (Q := Q) (a := a) (a0 := a0) (u := u) hs hsle

end

end Ch03
end Book
end Homogenization
