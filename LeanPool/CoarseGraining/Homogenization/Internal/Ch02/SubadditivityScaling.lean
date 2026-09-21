/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.SubadditivityScalingDefinitions
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.MatrixPositivity
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.MatrixExtraction
import LeanPool.CoarseGraining.Homogenization.Internal.Ch02.Representatives
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Subadditivity
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.Homogeneity

/-! # Subadditivity Scaling -/

open scoped BigOperators

namespace Homogenization
namespace Internal
namespace Ch02

noncomputable section

namespace BookCh02

open Book.Ch02

private theorem isEllipticMatrix_smul {d : ℕ} {lam Lam c : ℝ}
    {A : Mat d} (hc : 0 < c) (hA : IsEllipticMatrix lam Lam A) :
    IsEllipticMatrix (c * lam) (c * Lam) (c • A) := by
  rcases hA with ⟨hlam, hlamLam, hlower, hupper⟩
  have hLam : 0 < Lam := lt_of_lt_of_le hlam hlamLam
  have hdet : IsUnit A.det :=
    isUnit_det_of_isEllipticMatrix ⟨hlam, hlamLam, hlower, hupper⟩
  refine ⟨mul_pos hc hlam, mul_le_mul_of_nonneg_left hlamLam (le_of_lt hc), ?_, ?_⟩
  · intro ξ
    rw [smul_matVecMul, vecDot_smul_right]
    have hmul := mul_le_mul_of_nonneg_left (hlower ξ) (le_of_lt hc)
    nlinarith
  · intro ξ
    have hcne : c ≠ 0 := hc.ne'
    have hinv :
        ((c • A)⁻¹ : Mat d) = c⁻¹ • A⁻¹ := by
      rw [nonsing_inv_smul c hcne hdet]
    rw [hinv, smul_matVecMul, vecDot_smul_right]
    have hcinv_nonneg : 0 ≤ c⁻¹ := by positivity
    have hmul := mul_le_mul_of_nonneg_left (hupper ξ) hcinv_nonneg
    have hleft :
        (c * Lam)⁻¹ * vecNormSq ξ =
          c⁻¹ * (Lam⁻¹ * vecNormSq ξ) := by
      field_simp [hcne, hLam.ne']
    rw [hleft]
    exact hmul

private theorem isEllipticFieldOn_smul {d : ℕ} {lam Lam c : ℝ}
    {U : Set (Vec d)} {a : CoeffField d}
    (hc : 0 < c) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsEllipticFieldOn (c * lam) (c * Lam) U (c • a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hmeas := hEll.1.const_smul c
    convert hmeas using 1
    funext x i j
    by_cases hx : x ∈ U <;> simp [hx]
  · intro x hx
    exact isEllipticMatrix_smul hc (hEll.2 x hx)

/-- Turn an old pointwise elliptic field on a Book domain into a public
`CoeffOn`. This is only an internal bridge from old proof engines to the
a.e.-native public surface. -/
private noncomputable def coeffOnOfIsEllipticFieldOn {d : ℕ}
    (U : Domain d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (U : Set (Vec d)) a) : CoeffOn U where
  toCoeffField := a
  lam := lam
  Lam := Lam
  lam_pos := (hEll.2 (Classical.choose U.nonempty)
    (Classical.choose_spec U.nonempty)).1
  lam_le_Lam := (hEll.2 (Classical.choose U.nonempty)
    (Classical.choose_spec U.nonempty)).2.1
  aeStronglyMeasurable := by
    intro i j
    have hentry :
        Measurable fun x : Vec d =>
          restrictCoeffField (U : Set (Vec d)) a x i j := by
      classical
      have hij := (measurable_pi_iff.1 (measurable_pi_iff.1 hEll.1 i) j)
      have heq :
          (fun x : Vec d => restrictCoeffField (U : Set (Vec d)) a x i j)
            = fun x : Vec d => if x ∈ U.carrier then a x i j else 0 := by
        funext x
        by_cases hx : x ∈ U.carrier <;> simp [restrictCoeffField, hx]
      rw [heq]
      exact hij
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards [MeasureTheory.ae_restrict_mem U.measurableSet] with x hx
    exact hEll.2 x hx

private theorem scaled_pointwise_aeeq {d : ℕ} (U : Domain d)
    (a b : CoeffOn U) {c : ℝ} (hscaled : CoeffOn.AEScaled c a b) :
    let ap : CoeffOn U := pointwiseCoeffOn U a
    b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x => c • ap.toCoeffField x := by
  intro ap
  have hap : ap.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))] a.toCoeffField := by
    simpa [ap] using! pointwiseCoeffOn_ae_eq U a
  exact hscaled.trans <| hap.symm.mono fun x hx => by
    simp [hx]

private theorem responseJ_homogeneous_public {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {c : ℝ} (hc : 0 < c)
    {b : CoeffOn U} (hscaled : CoeffOn.AEScaled c a b) (p q : Vec d) :
    responseJ U b p q =
      responseJ U a ((Real.sqrt c) • p) ((Real.sqrt c)⁻¹ • q) := by
  let ap : CoeffOn U := pointwiseCoeffOn U a
  have hEllAp :
      IsEllipticFieldOn ap.lam ap.Lam (U : Set (Vec d)) ap.toCoeffField := by
    simpa [ap] using pointwiseCoeffOn_isEllipticFieldOn U a
  let cap : CoeffOn U :=
    coeffOnOfIsEllipticFieldOn U (c • ap.toCoeffField)
      (isEllipticFieldOn_smul hc hEllAp)
  have hbcap : CoeffOn.AEEq b cap := by
    simpa [cap] using! scaled_pointwise_aeeq U a b hscaled
  have hapa : CoeffOn.AEEq ap a := by
    simpa [ap] using pointwiseCoeffOn_ae_eq U a
  calc
    responseJ U b p q = responseJ U cap p q := responseJ_eq_ofAEEq hbcap p q
    _ = ResponseJ (U : Set (Vec d)) p q (c • ap.toCoeffField) := by
          rw [book_responseJ_eq_ResponseJ U cap p q]
          rfl
    _ = ResponseJ (U : Set (Vec d)) ((Real.sqrt c) • p)
          ((Real.sqrt c)⁻¹ • q) ap.toCoeffField := by
          exact responseJ_homogeneous_coeffField (U : Set (Vec d)) p q
            ap.toCoeffField hc
    _ = responseJ U ap ((Real.sqrt c) • p) ((Real.sqrt c)⁻¹ • q) := by
          rw [book_responseJ_eq_ResponseJ U ap ((Real.sqrt c) • p)
            ((Real.sqrt c)⁻¹ • q)]
    _ = responseJ U a ((Real.sqrt c) • p) ((Real.sqrt c)⁻¹ • q) := by
          rw [responseJ_eq_ofAEEq hapa ((Real.sqrt c) • p) ((Real.sqrt c)⁻¹ • q)]

private theorem oldCanonicalData_of_pointwiseCoeffOn {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U) :
    ∃ sigma0 : Mat d,
      IsSigmaStarCoarse (U : Set (Vec d)) (pointwiseCoeffOn U a).toCoeffField
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField) ∧
      IsKappaCoarse (U : Set (Vec d)) (pointwiseCoeffOn U a).toCoeffField
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField) ∧
      IsSigmaCoarse (U : Set (Vec d)) (pointwiseCoeffOn U a).toCoeffField
        sigma0
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField)
        (Homogenization.kappaCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField) ∧
      IsUnit
        (Homogenization.sigmaStarCoarse (U : Set (Vec d))
          (pointwiseCoeffOn U a).toCoeffField).det := by
  let ap : CoeffOn U := pointwiseCoeffOn U a
  have hEllAp :
      IsEllipticFieldOn ap.lam ap.Lam (U : Set (Vec d)) ap.toCoeffField := by
    simpa [ap] using pointwiseCoeffOn_isEllipticFieldOn U a
  let hvol : 0 < (MeasureTheory.volume (U : Set (Vec d))).toReal :=
    domain_volume_pos U
  rcases
      exists_oldCanonicalMatrixData_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) U.isDomain hEllAp hvol with
    ⟨R, sigma0, compat, _hA, _hSInv, hS, hK, hSigma, _hSigmaCanonical⟩
  have hdet : IsUnit
      (Homogenization.sigmaStarCoarse (U : Set (Vec d)) ap.toCoeffField).det := by
    exact
      isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
        (U := (U : Set (Vec d))) (a := ap.toCoeffField) R U.isDomain hEllAp hvol
        compat hS
  exact ⟨sigma0, by simpa [ap] using hS, by simpa [ap] using hK,
    by simpa [ap] using hSigma, by simpa [ap] using hdet⟩

private theorem coarse_matrices_homogeneous_public_of_neZero {d : ℕ} [NeZero d]
    (U : Domain d) (a : CoeffOn U) {c : ℝ} (hc : 0 < c)
    {b : CoeffOn U} (hscaled : CoeffOn.AEScaled c a b) :
    Book.Ch02.sigmaCoarse U b = c • Book.Ch02.sigmaCoarse U a ∧
      Book.Ch02.sigmaStarCoarse U b = c • Book.Ch02.sigmaStarCoarse U a ∧
      Book.Ch02.kappaCoarse U b = c • Book.Ch02.kappaCoarse U a := by
  let ap : CoeffOn U := pointwiseCoeffOn U a
  have hEllAp :
      IsEllipticFieldOn ap.lam ap.Lam (U : Set (Vec d)) ap.toCoeffField := by
    simpa [ap] using pointwiseCoeffOn_isEllipticFieldOn U a
  let cap : CoeffOn U :=
    coeffOnOfIsEllipticFieldOn U (c • ap.toCoeffField)
      (isEllipticFieldOn_smul hc hEllAp)
  have hbcap : CoeffOn.AEEq b cap := by
    simpa [cap] using! scaled_pointwise_aeeq U a b hscaled
  have hapa : CoeffOn.AEEq ap a := by
    simpa [ap] using pointwiseCoeffOn_ae_eq U a
  rcases oldCanonicalData_of_pointwiseCoeffOn U a with
    ⟨sigma0, hS, hK, hSigma, hdet⟩
  have hOld :=
    cg_matrices_homogeneous_coeffField
      (U : Set (Vec d)) ap.toCoeffField hS hK hSigma hdet hc
  rcases hOld with ⟨hSigmaOld, hStarOld, hKappaOld⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      Book.Ch02.sigmaCoarse U b =
          Book.Ch02.sigmaCoarse U cap := sigmaCoarse_eq_ofAEEq hbcap
      _ = Homogenization.sigmaCoarse (U : Set (Vec d)) (c • ap.toCoeffField) := by
            simpa [cap] using! book_sigmaCoarse_eq_sigmaCoarse U cap
      _ = c • Homogenization.sigmaCoarse (U : Set (Vec d)) ap.toCoeffField :=
            hSigmaOld
      _ = c • Book.Ch02.sigmaCoarse U ap := by
            rw [book_sigmaCoarse_eq_sigmaCoarse U ap]
      _ = c • Book.Ch02.sigmaCoarse U a := by
            rw [sigmaCoarse_eq_ofAEEq hapa]
  · calc
      Book.Ch02.sigmaStarCoarse U b =
          Book.Ch02.sigmaStarCoarse U cap := sigmaStarCoarse_eq_ofAEEq hbcap
      _ = Homogenization.sigmaStarCoarse (U : Set (Vec d)) (c • ap.toCoeffField) := by
            simpa [cap] using! book_sigmaStarCoarse_eq_sigmaStarCoarse U cap
      _ = c • Homogenization.sigmaStarCoarse (U : Set (Vec d)) ap.toCoeffField :=
            hStarOld
      _ = c • Book.Ch02.sigmaStarCoarse U ap := by
            rw [book_sigmaStarCoarse_eq_sigmaStarCoarse U ap]
      _ = c • Book.Ch02.sigmaStarCoarse U a := by
            rw [sigmaStarCoarse_eq_ofAEEq hapa]
  · calc
      Book.Ch02.kappaCoarse U b =
          Book.Ch02.kappaCoarse U cap := kappaCoarse_eq_ofAEEq hbcap
      _ = Homogenization.kappaCoarse (U : Set (Vec d)) (c • ap.toCoeffField) := by
            simpa [cap] using! book_kappaCoarse_eq_kappaCoarse U cap
      _ = c • Homogenization.kappaCoarse (U : Set (Vec d)) ap.toCoeffField :=
            hKappaOld
      _ = c • Book.Ch02.kappaCoarse U ap := by
            rw [book_kappaCoarse_eq_kappaCoarse U ap]
      _ = c • Book.Ch02.kappaCoarse U a := by
            rw [kappaCoarse_eq_ofAEEq hapa]

private theorem coarse_matrices_homogeneous_public {d : ℕ}
    (U : Domain d) (a : CoeffOn U) {c : ℝ} (hc : 0 < c)
    {b : CoeffOn U} (hscaled : CoeffOn.AEScaled c a b) :
    Book.Ch02.sigmaCoarse U b = c • Book.Ch02.sigmaCoarse U a ∧
      Book.Ch02.sigmaStarCoarse U b = c • Book.Ch02.sigmaStarCoarse U a ∧
      Book.Ch02.kappaCoarse U b = c • Book.Ch02.kappaCoarse U a := by
  by_cases hd : d = 0
  · subst d
    refine ⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · let : NeZero d := ⟨hd⟩
    exact coarse_matrices_homogeneous_public_of_neZero U a hc hscaled

private theorem responseJ_subadditive_public {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ∀ (P : DomainPartition U) (aCell : ∀ i : P.Cell, CoeffOn (P.cell i)),
      (∀ i : P.Cell, CoeffOn.RestrictsTo a (aCell i)) →
      ∀ p q : Vec d,
        responseJ U a p q ≤
          P.weightedAverage fun i => responseJ (P.cell i) (aCell i) p q := by
  intro P aCell hCell p q
  classical
  let : Fintype P.Cell := P.instFintype
  rcases P.triadic_realization with ⟨root, depth, hU, e, hcell⟩
  let ap : CoeffOn U := pointwiseCoeffOn U a
  have hEllAp :
      IsEllipticFieldOn ap.lam ap.Lam (U : Set (Vec d)) ap.toCoeffField := by
    simpa [ap] using pointwiseCoeffOn_isEllipticFieldOn U a
  have hEllRoot :
      IsEllipticFieldOn ap.lam ap.Lam (openCubeSet root) ap.toCoeffField := by
    simpa [hU] using hEllAp
  have hapa : CoeffOn.AEEq ap a := by
    simpa [ap] using pointwiseCoeffOn_ae_eq U a
  have hOld :
      ResponseJ (openCubeSet root) p q ap.toCoeffField ≤
        descendantsAverage root depth
          (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField) :=
    responseJ_subadditive_openCubeSet_descendantsAtDepth_of_isEllipticFieldOn
      depth root ap.toCoeffField hEllRoot p q
  have hLeft :
      responseJ U a p q =
        ResponseJ (openCubeSet root) p q ap.toCoeffField := by
    calc
      responseJ U a p q = responseJ U ap p q := by
            rw [responseJ_eq_ofAEEq hapa p q]
      _ = ResponseJ (U : Set (Vec d)) p q ap.toCoeffField := by
            rw [book_responseJ_eq_ResponseJ U ap p q]
      _ = ResponseJ (openCubeSet root) p q ap.toCoeffField := by
            rw [hU]
  have hRespCell :
      ∀ i : P.Cell,
        responseJ (P.cell i) (aCell i) p q =
          ResponseJ (openCubeSet ((e i).1)) p q ap.toCoeffField := by
    intro i
    have hsub : (P.cell i : Set (Vec d)) ⊆ (U : Set (Vec d)) :=
      P.cell_subset_parent i
    have hEllCell :
        IsEllipticFieldOn ap.lam ap.Lam (P.cell i : Set (Vec d))
          ap.toCoeffField :=
      IsEllipticFieldOn.mono hEllAp (P.cell i).measurableSet hsub
    let apCell : CoeffOn (P.cell i) :=
      coeffOnOfIsEllipticFieldOn (P.cell i) ap.toCoeffField hEllCell
    have hapaCell :
        ap.toCoeffField =ᵐ[volumeMeasureOn (P.cell i : Set (Vec d))]
          a.toCoeffField := by
      simpa [volumeMeasureOn] using!
        (MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub
          (by simpa [volumeMeasureOn, ap] using! pointwiseCoeffOn_ae_eq U a))
    have hAPCell : CoeffOn.AEEq apCell (aCell i) := by
      exact hapaCell.trans (hCell i).symm
    calc
      responseJ (P.cell i) (aCell i) p q =
          responseJ (P.cell i) apCell p q := by
            rw [responseJ_eq_ofAEEq hAPCell p q]
      _ = ResponseJ (P.cell i : Set (Vec d)) p q ap.toCoeffField := by
            rw [book_responseJ_eq_ResponseJ (P.cell i) apCell p q]
            rfl
      _ = ResponseJ (openCubeSet ((e i).1)) p q ap.toCoeffField := by
            rw [(hcell i).1]
  have hWeighted :
      P.weightedAverage (fun i => responseJ (P.cell i) (aCell i) p q) =
        descendantsAverage root depth
          (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField) := by
    let D := descendantsAtDepth root depth
    have hcard : Fintype.card P.Cell = D.card := by
      calc
        Fintype.card P.Cell = Fintype.card {R : TriadicCube d // R ∈ D} :=
          Fintype.card_congr e
        _ = D.card := by
          simp [D]
    have hsumSubtype :
        (∑ s : {R : TriadicCube d // R ∈ D},
            ResponseJ (openCubeSet s.1) p q ap.toCoeffField) =
          D.sum (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField) := by
      simpa using
        (Finset.sum_attach D
          (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField))
    have hsumEquiv :
        (∑ i : P.Cell, ResponseJ (openCubeSet ((e i).1)) p q ap.toCoeffField) =
          ∑ s : {R : TriadicCube d // R ∈ D},
            ResponseJ (openCubeSet s.1) p q ap.toCoeffField :=
      Fintype.sum_equiv e _ _ fun _ => rfl
    unfold DomainPartition.weightedAverage descendantsAverage
    calc
      ∑ i : P.Cell, P.weight i * responseJ (P.cell i) (aCell i) p q
          = ∑ i : P.Cell,
              ((Fintype.card P.Cell : ℝ)⁻¹) *
                ResponseJ (openCubeSet ((e i).1)) p q ap.toCoeffField := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [(hcell i).2, hRespCell i]
      _ = (D.card : ℝ)⁻¹ *
            ∑ i : P.Cell,
              ResponseJ (openCubeSet ((e i).1)) p q ap.toCoeffField := by
            rw [hcard]
            rw [Finset.mul_sum]
      _ = (D.card : ℝ)⁻¹ *
            ∑ s : {R : TriadicCube d // R ∈ D},
              ResponseJ (openCubeSet s.1) p q ap.toCoeffField := by
            rw [hsumEquiv]
      _ = (D.card : ℝ)⁻¹ *
            D.sum (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField) := by
            rw [hsumSubtype]
  calc
    responseJ U a p q =
        ResponseJ (openCubeSet root) p q ap.toCoeffField := hLeft
    _ ≤ descendantsAverage root depth
          (fun R => ResponseJ (openCubeSet R) p q ap.toCoeffField) := hOld
    _ = P.weightedAverage
          (fun i => responseJ (P.cell i) (aCell i) p q) := hWeighted.symm

theorem responseSubadditivityAndScalingTheory {d : ℕ}
    (U : Domain d) (a : CoeffOn U) :
    ResponseSubadditivityAndScalingTheory U a := by
  refine
    { responseJ_subadditive := ?_
      responseJ_homogeneous := ?_
      sigma_homogeneous := ?_
      sigmaStar_homogeneous := ?_
      kappa_homogeneous := ?_ }
  · exact responseJ_subadditive_public U a
  · intro c hc b hscaled p q
    exact responseJ_homogeneous_public U a hc hscaled p q
  · intro c hc b hscaled
    exact (coarse_matrices_homogeneous_public U a hc hscaled).1
  · intro c hc b hscaled
    exact (coarse_matrices_homogeneous_public U a hc hscaled).2.1
  · intro c hc b hscaled
    exact (coarse_matrices_homogeneous_public U a hc hscaled).2.2

end BookCh02

end

end Ch02
end Internal
end Homogenization
