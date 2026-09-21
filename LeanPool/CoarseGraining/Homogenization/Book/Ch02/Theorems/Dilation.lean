/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Dilation
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledMu
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.DoubledResponse
import LeanPool.CoarseGraining.Homogenization.Book.Ch02.Theorems.HomogenizationError

/-! # Dilation -/

open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius Pointwise ENNReal

namespace Homogenization
namespace Book
namespace Ch02

noncomputable section

/-- A cube dilated by `3^k` and then by `3^{-k}` returns to itself. -/
theorem dilateCube_neg_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    dilateCube (-k) (dilateCube k Q) = Q := by
  cases Q
  simp [dilateCube]

/-- A cube dilated by `3^{-k}` and then by `3^k` returns to itself. -/
theorem dilateCube_dilateCube_neg {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    dilateCube k (dilateCube (-k) Q) = Q := by
  cases Q
  simp [dilateCube]

/-- Normalizing a cube by dilation through `-Q.scale` gives a scale-zero cube. -/
@[simp] theorem dilateCube_neg_scale_scale {d : ℕ} (Q : TriadicCube d) :
    (dilateCube (-Q.scale) Q).scale = 0 := by
  simp [dilateCube]

/-- Dilation by `3 ^ k` maps points of a triadic cube into points of the
dilated triadic cube. -/
theorem dilateVec_mem_openCubeSet_dilateCube {d : ℕ} (k : ℤ)
    {Q : TriadicCube d} {x : Vec d} (hx : x ∈ openCubeSet Q) :
    dilateVec k x ∈ openCubeSet (dilateCube k Q) := by
  intro i
  let r : ℝ := triadicDilationFactor k
  have hr : 0 < r := by
    dsimp [r]
    exact triadicDilationFactor_pos k
  have hxi := hx i
  constructor
  · have hmul := mul_lt_mul_of_pos_left hxi.1 hr
    simpa [dilateVec, cubeScaleFactor_dilateCube,
      r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      using hmul
  · have hmul := mul_lt_mul_of_pos_left hxi.2 hr
    simpa [dilateVec, cubeScaleFactor_dilateCube,
      r, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
      using hmul

/-- Dilation by `3^{-k}` is the inverse of dilation by `3^k`. -/
theorem dilateVec_neg_dilateVec {d : ℕ} (k : ℤ) (x : Vec d) :
    dilateVec (-k) (dilateVec k x) = x := by
  ext i
  simp [dilateVec, triadicDilationFactor, smul_eq_mul, zpow_neg]
  field_simp [zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)]

/-- Dilation by `3^k` is the inverse of dilation by `3^{-k}`. -/
theorem dilateVec_dilateVec_neg {d : ℕ} (k : ℤ) (x : Vec d) :
    dilateVec k (dilateVec (-k) x) = x := by
  ext i
  simp [dilateVec, triadicDilationFactor, smul_eq_mul, zpow_neg]
  field_simp [zpow_ne_zero k (by norm_num : (3 : ℝ) ≠ 0)]

/-- Undilating preserves cube containment relations. -/
theorem openCubeSet_undilate_subset_of_subset {d : ℕ} (k : ℤ)
    {Q R : TriadicCube d} (hsub : openCubeSet R ⊆ openCubeSet Q) :
    openCubeSet (dilateCube (-k) R) ⊆ openCubeSet (dilateCube (-k) Q) := by
  intro x hx
  have hxR0 : dilateVec k x ∈ openCubeSet (dilateCube k (dilateCube (-k) R)) :=
    dilateVec_mem_openCubeSet_dilateCube k hx
  have hxR : dilateVec k x ∈ openCubeSet R := by
    simpa [dilateCube_dilateCube_neg] using hxR0
  have hxQ : dilateVec k x ∈ openCubeSet Q := hsub hxR
  have hxQ0 :
      dilateVec (-k) (dilateVec k x) ∈ openCubeSet (dilateCube (-k) Q) :=
    dilateVec_mem_openCubeSet_dilateCube (-k) hxQ
  simpa [dilateVec_neg_dilateVec] using hxQ0

/-- Pull an a.e. coefficient-field equality forward to the dilated cube. -/
theorem eventuallyEq_comp_undilate_of_ae_eq {d : ℕ} (k : ℤ)
    {Q : TriadicCube d} {f g : Vec d → Mat d}
    (hfg : f =ᵐ[volumeMeasureOn (openCubeSet Q)] g) :
    (fun x : Vec d => f (undilateVec k x))
      =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
    fun x => g (undilateVec k x) := by
  let r : ℝ := triadicDilationFactor k
  have hr : 0 < r := by
    simpa [r] using triadicDilationFactor_pos k
  have hpre : r⁻¹ • openCubeSet (dilateCube k Q) = openCubeSet Q := by
    rw [openCubeSet_dilateCube k Q]
    ext x
    simp [r, triadicDilationFactor_ne_zero k]
  have hmap :
      MeasureTheory.Measure.map (fun x : Vec d => undilateVec k x)
          (volumeMeasureOn (openCubeSet (dilateCube k Q))) =
        ENNReal.ofReal (((r⁻¹) ^ d)⁻¹) •
          volumeMeasureOn (openCubeSet Q) := by
    have h :=
      Homogenization.map_smul_volume_restrict (d := d) (a := r⁻¹)
        (inv_pos.mpr hr) (openCubeSet (dilateCube k Q))
    simpa [volumeMeasureOn, undilateVec, r, hpre] using h
  have hfgMap :
      f =ᵐ[MeasureTheory.Measure.map (fun x : Vec d => undilateVec k x)
        (volumeMeasureOn (openCubeSet (dilateCube k Q)))] g := by
    rw [hmap]
    exact
      MeasureTheory.Measure.AbsolutelyContinuous.ae_eq
        MeasureTheory.Measure.smul_absolutelyContinuous hfg
  exact MeasureTheory.ae_of_ae_map (measurable_const_smul _).aemeasurable hfgMap

namespace CoeffOn

/-- A concrete public coefficient object on a dilated cube.

The representative is chosen via the pointwise-good representative of the
source coefficient object, but the public relation below records only the
intended a.e. pullback relation. -/
noncomputable def dilate {d : ℕ} (k : ℤ) {Q : TriadicCube d}
    (a : CoeffOn (cubeDomain Q)) :
    CoeffOn (cubeDomain (dilateCube k Q)) where
  toCoeffField :=
    dilateCoeffField k
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (cubeDomain Q) a)
  lam := a.lam
  Lam := a.Lam
  lam_pos := a.lam_pos
  lam_le_Lam := a.lam_le_Lam
  aeStronglyMeasurable := by
    classical
    intro i j
    have hcoeff : Measurable fun x : Vec d =>
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) a (undilateVec k x) i j := by
      have hbase : Measurable fun y : Vec d =>
          Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Q) a y i j := by
        exact
          (measurable_pi_iff.1
            (measurable_pi_iff.1
              (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_measurable
                (cubeDomain Q) a) i) j)
      exact hbase.comp (measurable_const_smul _)
    have hentry : Measurable fun x : Vec d =>
        restrictCoeffField (openCubeSet (dilateCube k Q))
          (dilateCoeffField k
            (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
              (cubeDomain Q) a)) x i j := by
      have hite :
          Measurable fun x : Vec d =>
            if x ∈ openCubeSet (dilateCube k Q) then
              Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
                (cubeDomain Q) a (undilateVec k x) i j
            else 0 :=
        Measurable.ite (measurableSet_openCubeSet (dilateCube k Q))
          hcoeff measurable_const
      convert hite using 1
      funext x
      by_cases hx : x ∈ openCubeSet (dilateCube k Q) <;>
        simp [restrictCoeffField, dilateCoeffField, hx]
    exact hentry.aestronglyMeasurable
  aeElliptic := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem
        (measurableSet_openCubeSet (dilateCube k Q))] with x hx
    have hxopen : x ∈ openCubeSet (dilateCube k Q) := by simpa using hx
    have hxpre : undilateVec k x ∈ openCubeSet Q := by
      rw [openCubeSet_dilateCube k Q] at hxopen
      rcases hxopen with ⟨y, hy, hxy⟩
      subst x
      simpa [undilateVec, smul_smul, triadicDilationFactor_ne_zero k] using hy
    exact
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) a).2 (undilateVec k x) hxpre

/-- The concrete dilated coefficient object is a public a.e. cube dilation. -/
theorem dilate_isCubeDilation {d : ℕ} (k : ℤ) {Q : TriadicCube d}
    (a : CoeffOn (cubeDomain Q)) :
    IsCubeDilation k a (dilate k a) := by
  refine ⟨rfl, rfl, ?_⟩
  let r : ℝ := triadicDilationFactor k
  have hr : 0 < r := by
    simpa [r] using triadicDilationFactor_pos k
  have hpre : r⁻¹ • openCubeSet (dilateCube k Q) = openCubeSet Q := by
    rw [openCubeSet_dilateCube k Q]
    ext x
    simp [r, triadicDilationFactor_ne_zero k]
  have hmap :
      MeasureTheory.Measure.map (fun x : Vec d => undilateVec k x)
          (volumeMeasureOn (openCubeSet (dilateCube k Q))) =
        ENNReal.ofReal (((r⁻¹) ^ d)⁻¹) •
          volumeMeasureOn (openCubeSet Q) := by
    have h :=
      Homogenization.map_smul_volume_restrict (d := d) (a := r⁻¹)
        (inv_pos.mpr hr) (openCubeSet (dilateCube k Q))
    simpa [volumeMeasureOn, undilateVec, r, hpre] using h
  have hpoint :
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) a
        =ᵐ[volumeMeasureOn (openCubeSet Q)] a.toCoeffField := by
    simpa using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (cubeDomain Q) a
  have hpointMap :
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) a
        =ᵐ[MeasureTheory.Measure.map (fun x : Vec d => undilateVec k x)
          (volumeMeasureOn (openCubeSet (dilateCube k Q)))] a.toCoeffField := by
    rw [hmap]
    exact
      MeasureTheory.Measure.AbsolutelyContinuous.ae_eq
        MeasureTheory.Measure.smul_absolutelyContinuous hpoint
  have hpull :
      (fun x : Vec d =>
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) a (undilateVec k x))
        =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      fun x => a.toCoeffField (undilateVec k x) :=
    MeasureTheory.ae_of_ae_map (measurable_const_smul _).aemeasurable hpointMap
  exact hpull.mono fun x hx => by
    simp [dilate, dilateCoeffField, hx]

/-- Dilation preserves public a.e. restriction of coefficient objects. -/
theorem dilate_restrictsTo {d : ℕ} (k : ℤ) {Q R : TriadicCube d}
    {aQ : CoeffOn (cubeDomain Q)} {aR : CoeffOn (cubeDomain R)}
    (hsub : openCubeSet R ⊆ openCubeSet Q)
    (h : RestrictsTo aQ aR) :
    RestrictsTo (dilate k aQ) (dilate k aR) := by
  have hpointR :
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain R) aR
        =ᵐ[volumeMeasureOn (openCubeSet R)] aR.toCoeffField := by
    simpa using
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
        (cubeDomain R) aR
  have hpointQ_on_R :
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) aQ
        =ᵐ[volumeMeasureOn (openCubeSet R)] aQ.toCoeffField := by
    exact
      MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub
        (by
          simpa using!
            Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
              (cubeDomain Q) aQ)
  have hsource :
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain R) aR
        =ᵐ[volumeMeasureOn (openCubeSet R)]
      Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) aQ :=
    hpointR.trans (h.trans hpointQ_on_R.symm)
  have hpull := eventuallyEq_comp_undilate_of_ae_eq k hsource
  exact hpull.mono fun x hx => by
    simp [dilate, dilateCoeffField, hx]

end CoeffOn

namespace TriadicCoeffFamily

/-- The coefficient object assigned to a target cube by the dilated coefficient
family.  The source cube is the undilated target cube. -/
noncomputable def dilatedCoeffOnAt {d : ℕ} (k : ℤ)
    (a : TriadicCoeffFamily d) (R : TriadicCube d) :
    CoeffOn (cubeDomain R) where
  toCoeffField :=
    dilateCoeffField k
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
        (cubeDomain (dilateCube (-k) R))
        (a.coeffOn (dilateCube (-k) R)))
  lam := (a.coeffOn (dilateCube (-k) R)).lam
  Lam := (a.coeffOn (dilateCube (-k) R)).Lam
  lam_pos := (a.coeffOn (dilateCube (-k) R)).lam_pos
  lam_le_Lam := (a.coeffOn (dilateCube (-k) R)).lam_le_Lam
  aeStronglyMeasurable := by
    classical
    intro i j
    let Q : TriadicCube d := dilateCube (-k) R
    have hcoeff : Measurable fun x : Vec d =>
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
          (cubeDomain Q) (a.coeffOn Q) (undilateVec k x) i j := by
      have hbase : Measurable fun y : Vec d =>
          Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Q) (a.coeffOn Q) y i j := by
        exact
          (measurable_pi_iff.1
            (measurable_pi_iff.1
              (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_measurable
                (cubeDomain Q) (a.coeffOn Q)) i) j)
      exact hbase.comp (measurable_const_smul _)
    have hentry : Measurable fun x : Vec d =>
        restrictCoeffField (openCubeSet R)
          (dilateCoeffField k
            (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
              (cubeDomain Q) (a.coeffOn Q))) x i j := by
      have hite :
          Measurable fun x : Vec d =>
            if x ∈ openCubeSet R then
              Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
                (cubeDomain Q) (a.coeffOn Q) (undilateVec k x) i j
            else 0 :=
        Measurable.ite (measurableSet_openCubeSet R) hcoeff measurable_const
      convert hite using 1
      funext x
      by_cases hx : x ∈ openCubeSet R <;>
        simp [restrictCoeffField, dilateCoeffField, Q, hx]
    simpa [Q] using hentry.aestronglyMeasurable
  aeElliptic := by
    let Q : TriadicCube d := dilateCube (-k) R
    have hRQ : dilateCube k Q = R := by
      simpa [Q] using dilateCube_dilateCube_neg k R
    filter_upwards
      [MeasureTheory.ae_restrict_mem (measurableSet_openCubeSet R)] with x hx
    have hxopenR : x ∈ openCubeSet R := by simpa using hx
    have hxopen : x ∈ openCubeSet (dilateCube k Q) := by
      simpa [hRQ] using hxopenR
    have hxpre : undilateVec k x ∈ openCubeSet Q := by
      rw [openCubeSet_dilateCube k Q] at hxopen
      rcases hxopen with ⟨y, hy, hxy⟩
      subst x
      simpa [undilateVec, smul_smul, triadicDilationFactor_ne_zero k] using hy
    exact
      (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn
        (cubeDomain Q) (a.coeffOn Q)).2 (undilateVec k x) hxpre

/-- The public coefficient-family dilation by `3^k`. -/
noncomputable def dilate {d : ℕ} (k : ℤ)
    (a : TriadicCoeffFamily d) : TriadicCoeffFamily d where
  coeffOn := dilatedCoeffOnAt k a
  restrictsTo_of_subset := by
    intro Q R hsub
    let Qs : TriadicCube d := dilateCube (-k) Q
    let Rs : TriadicCube d := dilateCube (-k) R
    have hsub_source : openCubeSet Rs ⊆ openCubeSet Qs := by
      simpa [Qs, Rs] using openCubeSet_undilate_subset_of_subset k hsub
    have hrest : CoeffOn.RestrictsTo (a.coeffOn Qs) (a.coeffOn Rs) :=
      a.restrictsTo_of_subset hsub_source
    have hpointR :
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Rs) (a.coeffOn Rs)
          =ᵐ[volumeMeasureOn (openCubeSet Rs)] (a.coeffOn Rs).toCoeffField := by
      simpa using
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
          (cubeDomain Rs) (a.coeffOn Rs)
    have hpointQ_on_R :
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Qs) (a.coeffOn Qs)
          =ᵐ[volumeMeasureOn (openCubeSet Rs)] (a.coeffOn Qs).toCoeffField := by
      exact
        MeasureTheory.ae_restrict_of_ae_restrict_of_subset hsub_source
          (by
            simpa using!
              Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
                (cubeDomain Qs) (a.coeffOn Qs))
    have hsource :
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Rs) (a.coeffOn Rs)
          =ᵐ[volumeMeasureOn (openCubeSet Rs)]
        Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Qs) (a.coeffOn Qs) :=
      hpointR.trans (hrest.trans hpointQ_on_R.symm)
    have hpull := eventuallyEq_comp_undilate_of_ae_eq k hsource
    simpa [dilatedCoeffOnAt, Qs, Rs, dilateCube_dilateCube_neg,
      dilateCoeffField] using! hpull

/-- The concrete coefficient-family dilation satisfies the public dilation
relation. -/
theorem isDilation_dilate {d : ℕ} (k : ℤ) (a : TriadicCoeffFamily d) :
    IsDilation k a (dilate k a) := by
  intro Q
  let Qsrc : TriadicCube d := dilateCube (-k) (dilateCube k Q)
  have hsrc : Qsrc = Q := by
    simpa [Qsrc] using dilateCube_neg_dilateCube k Q
  refine ⟨?_, ?_, ?_⟩
  · change (a.coeffOn Qsrc).lam = (a.coeffOn Q).lam
    rw [hsrc]
  · change (a.coeffOn Qsrc).Lam = (a.coeffOn Q).Lam
    rw [hsrc]
  · change
      dilateCoeffField k
          (Homogenization.Internal.Ch02.BookCh02.pointwiseCoeffField
            (cubeDomain Qsrc) (a.coeffOn Qsrc))
        =ᵐ[volumeMeasureOn (openCubeSet (dilateCube k Q))]
      dilateCoeffField k (a.coeffOn Q).toCoeffField
    rw [hsrc]
    exact (CoeffOn.dilate_isCubeDilation k (a.coeffOn Q)).coeff_ae_eq

end TriadicCoeffFamily

/-- The coarse doubled block matrix is invariant under public cube dilation. -/
theorem coarseBlockMatrix_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) :
    coarseBlockMatrix (cubeDomain (dilateCube k Q)) b =
      coarseBlockMatrix (cubeDomain Q) a := by
  simp [coarseBlockMatrix, blockMatrixOfCoarseMatrices, coarseMatrices_dilate hCoeff]

/-- The doubled Dirichlet energy `mu` is invariant under public cube dilation. -/
theorem doubledMu_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (P : BlockVec d) :
    doubledMu (cubeDomain (dilateCube k Q)) b P =
      doubledMu (cubeDomain Q) a P := by
  calc
    doubledMu (cubeDomain (dilateCube k Q)) b P =
        (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeDomain (dilateCube k Q)) b) P) := by
        exact (doubledMuTheory (cubeDomain (dilateCube k Q)) b).doubledMu_eq_coarseBlockMatrix P
    _ =
        (1 / 2 : ℝ) * blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeDomain Q) a) P) := by
        rw [coarseBlockMatrix_dilate hCoeff]
    _ = doubledMu (cubeDomain Q) a P := by
        exact ((doubledMuTheory (cubeDomain Q) a).doubledMu_eq_coarseBlockMatrix P).symm

/-- The doubled response `Jbold` is invariant under public cube dilation. -/
theorem doubledResponseJ_dilate {d : ℕ} {k : ℤ} {Q : TriadicCube d}
    {a : CoeffOn (cubeDomain Q)}
    {b : CoeffOn (cubeDomain (dilateCube k Q))}
    (hCoeff : CoeffOn.IsCubeDilation k a b) (P R : BlockVec d) :
    doubledResponseJ (cubeDomain (dilateCube k Q)) b P R =
      doubledResponseJ (cubeDomain Q) a P R := by
  rcases P with ⟨p, q⟩
  rcases R with ⟨qStar, pStar⟩
  calc
    doubledResponseJ (cubeDomain (dilateCube k Q)) b (p, q) (qStar, pStar) =
        (1 / 2 : ℝ) * responseJ (cubeDomain (dilateCube k Q)) b
          (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * responseJ (cubeDomain (dilateCube k Q)) b.transpose
          (pStar + p) (qStar + q) := by
        exact (doubledResponseTheory (cubeDomain (dilateCube k Q)) b).doubledResponseJ_eq_scalar
          p pStar q qStar
    _ =
        (1 / 2 : ℝ) * responseJ (cubeDomain Q) a
          (p - pStar) (qStar - q) +
        (1 / 2 : ℝ) * responseJ (cubeDomain Q) a.transpose
          (pStar + p) (qStar + q) := by
        rw [responseJ_dilate hCoeff, responseJ_dilate hCoeff.transpose]
    _ = doubledResponseJ (cubeDomain Q) a (p, q) (qStar, pStar) := by
        exact ((doubledResponseTheory (cubeDomain Q) a).doubledResponseJ_eq_scalar
          p pStar q qStar).symm

/-- Dilation of triadic cubes is injective. -/
theorem dilateCube_injective {d : ℕ} (k : ℤ) :
    Function.Injective (dilateCube k : TriadicCube d → TriadicCube d) := by
  intro Q R hQR
  cases Q with
  | mk Qscale Qindex =>
      cases R with
      | mk Rscale Rindex =>
          have hscale : Qscale + k = Rscale + k :=
            congrArg TriadicCube.scale hQR
          have hscale' : Qscale = Rscale := add_right_cancel hscale
          have hindex : Qindex = Rindex := by
            funext i
            exact congrArg (fun S : TriadicCube d => S.index i) hQR
          cases hscale'
          cases hindex
          rfl

/-- Children commute with dilation by `3^k`. -/
theorem childCubes_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    childCubes (dilateCube k Q) = (childCubes Q).image (dilateCube k) := by
  classical
  ext R
  constructor
  · intro hR
    rcases mem_childCubes_iff.mp hR with ⟨digits, rfl⟩
    let S : TriadicCube d :=
      { scale := Q.scale - 1
        index := fun i => 3 * Q.index i + (digits i : ℤ) - 1 }
    refine Finset.mem_image.mpr ⟨S, ?_, ?_⟩
    · exact mem_childCubes_iff.mpr ⟨digits, rfl⟩
    · apply congrArg₂ TriadicCube.mk
      · simp [S, dilateCube]
        omega
      · funext i
        simp [S, dilateCube]
  · intro hR
    rcases Finset.mem_image.mp hR with ⟨S, hS, rfl⟩
    rcases mem_childCubes_iff.mp hS with ⟨digits, rfl⟩
    exact mem_childCubes_iff.mpr ⟨digits, by
      apply congrArg₂ TriadicCube.mk
      · simp [dilateCube]
        omega
      · funext i
        simp [dilateCube]⟩

/-- Descendants at fixed depth commute with dilation by `3^k`. -/
theorem descendantsAtDepth_dilateCube {d : ℕ} (k : ℤ) (Q : TriadicCube d) :
    ∀ n : ℕ,
      descendantsAtDepth (dilateCube k Q) n =
        (descendantsAtDepth Q n).image (dilateCube k)
  | 0 => by
      simp [descendantsAtDepth]
  | n + 1 => by
      rw [descendantsAtDepth_succ,
        descendantsAtDepth_dilateCube k Q n,
        descendantsAtDepth_succ]
      rw [Finset.image_biUnion, Finset.biUnion_image]
      apply Finset.biUnion_congr rfl
      intro R _hR
      rw [childCubes_dilateCube]

/-- Descendants at scale `n` commute with dilation, with scale shifted by `k`. -/
theorem descendantsAtScale_dilateCube {d : ℕ} (k n : ℤ) (Q : TriadicCube d) :
    descendantsAtScale (dilateCube k Q) (n + k) =
      (descendantsAtScale Q n).image (dilateCube k) := by
  classical
  by_cases hn : n ≤ Q.scale
  · have hn' : n + k ≤ (dilateCube k Q).scale := by
      simp [dilateCube]
      omega
    have hdepth :
        Int.toNat ((dilateCube k Q).scale - (n + k)) =
          Int.toNat (Q.scale - n) := by
      simp [dilateCube]
    rw [descendantsAtScale_eq_descendantsAtDepth (dilateCube k Q) hn',
      descendantsAtScale_eq_descendantsAtDepth Q hn, hdepth,
      descendantsAtDepth_dilateCube]
  · have hnlt : Q.scale < n := lt_of_not_ge hn
    have hnlt' : (dilateCube k Q).scale < n + k := by
      simp [dilateCube]
      omega
    rw [descendantsAtScale_eq_empty (dilateCube k Q) hnlt',
      descendantsAtScale_eq_empty Q hnlt]
    simp

/-- One-cube upper coarse-matrix norm is dilation invariant. -/
theorem coarseBMatrixNorm_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) :
    coarseBMatrixNorm (dilateCube k Q) b = coarseBMatrixNorm Q a := by
  unfold coarseBMatrixNorm
  rw [bCoarse_dilate (h Q)]

/-- One-cube lower coarse-matrix norm is dilation invariant. -/
theorem coarseSigmaStarInvMatrixNorm_dilate {d : ℕ} {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) :
    coarseSigmaStarInvMatrixNorm (dilateCube k Q) b =
      coarseSigmaStarInvMatrixNorm Q a := by
  unfold coarseSigmaStarInvMatrixNorm
  rw [sigmaStarInvCoarse_dilate (h Q)]

/-- The descendant maximum of `|b|` is dilation invariant, with scale shift. -/
theorem maxDescendantBMatrixNormAtScale_dilate {d : ℕ} {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (n : ℤ) :
    maxDescendantBMatrixNormAtScale (dilateCube k Q) (n + k) b =
      maxDescendantBMatrixNormAtScale Q n a := by
  unfold maxDescendantBMatrixNormAtScale
  rw [descendantsAtScale_dilateCube k n Q]
  exact finsetSupReal_image _ _ _ _ fun R _hR => coarseBMatrixNorm_dilate h R

/-- The descendant maximum of `|sigma_*^{-1}|` is dilation invariant. -/
theorem maxDescendantSigmaStarInvMatrixNormAtScale_dilate {d : ℕ} {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (n : ℤ) :
    maxDescendantSigmaStarInvMatrixNormAtScale (dilateCube k Q) (n + k) b =
      maxDescendantSigmaStarInvMatrixNormAtScale Q n a := by
  unfold maxDescendantSigmaStarInvMatrixNormAtScale
  rw [descendantsAtScale_dilateCube k n Q]
  exact finsetSupReal_image _ _ _ _ fun R _hR =>
    coarseSigmaStarInvMatrixNorm_dilate h R

theorem LambdaSqFinite_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (s q : ℝ) :
    LambdaSqFinite (dilateCube k Q) s q b = LambdaSqFinite Q s q a := by
  unfold LambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (2 / q))
  apply tsum_congr
  intro n
  have hscale :
      (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
    simp [dilateCube]
    omega
  have hmax := maxDescendantBMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
  rw [hscale]
  exact congrArg (fun x => geometricWeight s q n * Real.rpow x (q / 2)) hmax

theorem lambdaSqFinite_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (s q : ℝ) :
    lambdaSqFinite (dilateCube k Q) s q b = lambdaSqFinite Q s q a := by
  unfold lambdaSqFinite
  apply congrArg (fun S : ℝ => Real.rpow S (-(2 / q)))
  apply tsum_congr
  intro n
  have hscale :
      (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
    simp [dilateCube]
    omega
  have hmax :=
    maxDescendantSigmaStarInvMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
  rw [hscale]
  exact congrArg (fun x => geometricWeight s q n * Real.rpow x (q / 2)) hmax

theorem LambdaSqInfinity_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (s : ℝ) :
    LambdaSqInfinity (dilateCube k Q) s b = LambdaSqInfinity Q s a := by
  unfold LambdaSqInfinity
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hscale :
        (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
      simp [dilateCube]
      omega
    have hmax := maxDescendantBMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
    rw [hscale]
    exact congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hscale :
        (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
      simp [dilateCube]
      omega
    have hmax := maxDescendantBMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
    rw [hscale]
    exact congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax.symm

theorem lambdaSqInfinity_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (s : ℝ) :
    lambdaSqInfinity (dilateCube k Q) s b = lambdaSqInfinity Q s a := by
  unfold lambdaSqInfinity
  apply congrArg (fun S : ℝ => S⁻¹)
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hscale :
        (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
      simp [dilateCube]
      omega
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
    rw [hscale]
    exact congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax
  · rintro ⟨n, rfl⟩
    refine ⟨n, ?_⟩
    have hscale :
        (dilateCube k Q).scale - (n : ℤ) = (Q.scale - (n : ℤ)) + k := by
      simp [dilateCube]
      omega
    have hmax :=
      maxDescendantSigmaStarInvMatrixNormAtScale_dilate h Q (Q.scale - (n : ℤ))
    rw [hscale]
    exact congrArg (fun x => Real.rpow (3 : ℝ) (-2 * s * (n : ℝ)) * x) hmax.symm

/-- Coarse upper ellipticity is dilation invariant. -/
theorem LambdaSq_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (s : ℝ) (q : MultiscaleExponent) :
    LambdaSq (dilateCube k Q) s q b = LambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact LambdaSqFinite_dilate h Q s q
  | infinity =>
      exact LambdaSqInfinity_dilate h Q s

/-- Coarse lower ellipticity is dilation invariant. -/
theorem lambdaSq_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (s : ℝ) (q : MultiscaleExponent) :
    lambdaSq (dilateCube k Q) s q b = lambdaSq Q s q a := by
  cases q with
  | finite q =>
      exact lambdaSqFinite_dilate h Q s q
  | infinity =>
      exact lambdaSqInfinity_dilate h Q s

theorem LambdaS_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (s : ℝ) :
    LambdaS (dilateCube k Q) s b = LambdaS Q s a := by
  exact LambdaSq_dilate h Q s (.finite 1)

theorem lambdaS_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (s : ℝ) :
    lambdaS (dilateCube k Q) s b = lambdaS Q s a := by
  exact lambdaSq_dilate h Q s (.finite 1)

theorem ThetaRatio_dilate {d : ℕ} {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (s t : ℝ) :
    ThetaRatio (dilateCube k Q) s t b = ThetaRatio Q s t a := by
  unfold ThetaRatio
  rw [LambdaS_dilate h Q s, lambdaS_dilate h Q t]

theorem maxDescendantUpperEllipticityAtScale_dilate {d : ℕ} {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (q : MultiscaleExponent) :
    maxDescendantUpperEllipticityAtScale (dilateCube k Q) (n + k) s q b =
      maxDescendantUpperEllipticityAtScale Q n s q a := by
  unfold maxDescendantUpperEllipticityAtScale
  rw [descendantsAtScale_dilateCube k n Q]
  exact finsetSupReal_image _ _ _ _ fun R _hR => LambdaSq_dilate h R s q

theorem maxDescendantLowerEllipticityInvAtScale_dilate {d : ℕ} {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (q : MultiscaleExponent) :
    maxDescendantLowerEllipticityInvAtScale (dilateCube k Q) (n + k) s q b =
      maxDescendantLowerEllipticityInvAtScale Q n s q a := by
  unfold maxDescendantLowerEllipticityInvAtScale
  rw [descendantsAtScale_dilateCube k n Q]
  exact finsetSupReal_image _ _ _ _ fun R _hR => by
    rw [lambdaSq_dilate h R s q]

theorem normalizedBlockResponseValueSet_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (a0 : Mat d) :
    normalizedBlockResponseValueSet (dilateCube k Q) b a0 =
      normalizedBlockResponseValueSet Q a a0 := by
  ext m
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [doubledResponseJ_dilate (h Q)]⟩
  · rintro ⟨e, he, rfl⟩
    exact ⟨e, he, by rw [doubledResponseJ_dilate (h Q)]⟩

theorem normalizedBlockResponseMax_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d) (a0 : Mat d) :
    normalizedBlockResponseMax (dilateCube k Q) b a0 =
      normalizedBlockResponseMax Q a a0 := by
  unfold normalizedBlockResponseMax
  rw [normalizedBlockResponseValueSet_dilate h Q a0]

theorem maxDescendantNormalizedBlockResponseAtScale_dilate {d : ℕ} [NeZero d]
    {k : ℤ} {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (a0 : Mat d) :
    maxDescendantNormalizedBlockResponseAtScale (dilateCube k Q) (n + k) b a0 =
      maxDescendantNormalizedBlockResponseAtScale Q n a a0 := by
  unfold maxDescendantNormalizedBlockResponseAtScale
  rw [descendantsAtScale_dilateCube k n Q]
  exact finsetSupReal_image _ _ _ _ fun R _hR =>
    normalizedBlockResponseMax_dilate h R a0

theorem scaleResponseAtScale_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (p : MultiscaleExponent) (a0 : Mat d) :
    scaleResponseAtScale (dilateCube k Q) (n + k) p b a0 =
      scaleResponseAtScale Q n p a a0 := by
  cases p with
  | finite p =>
      unfold scaleResponseAtScale
      rw [descendantsAtScale_dilateCube k n Q]
      refine congrArg (fun x : ℝ => Real.rpow x (1 / p)) ?_
      refine finsetAverageReal_image _ _ (dilateCube_injective k).injOn _ _ ?_
      intro R _hR
      exact congrArg (fun x : ℝ => Real.rpow x (p / 2))
        (normalizedBlockResponseMax_dilate h R a0)
  | infinity =>
      unfold scaleResponseAtScale
      exact congrArg (fun x : ℝ => Real.rpow x (1 / 2))
        (maxDescendantNormalizedBlockResponseAtScale_dilate h Q n a0)

theorem HomogenizationErrorFinite_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (p : MultiscaleExponent) (q : ℝ) (a0 : Mat d) :
    HomogenizationErrorFinite (dilateCube k Q) (n + k) s p q b a0 =
      HomogenizationErrorFinite Q n s p q a a0 := by
  unfold HomogenizationErrorFinite
  congr 1
  apply tsum_congr
  intro l
  have hscale : (n + k) - (l : ℤ) = (n - (l : ℤ)) + k := by
    omega
  have hresp := scaleResponseAtScale_dilate h Q (n - (l : ℤ)) p a0
  simpa [hscale] using
    congrArg (fun x => geometricWeight s q l * Real.rpow x q) hresp

theorem HomogenizationErrorInfinity_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (p : MultiscaleExponent) (a0 : Mat d) :
    HomogenizationErrorInfinity (dilateCube k Q) (n + k) s p b a0 =
      HomogenizationErrorInfinity Q n s p a a0 := by
  unfold HomogenizationErrorInfinity
  refine congrArg sSup ?_
  ext M
  constructor
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    have hscale : (n + k) - (l : ℤ) = (n - (l : ℤ)) + k := by
      omega
    have hresp := scaleResponseAtScale_dilate h Q (n - (l : ℤ)) p a0
    simpa [hscale] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-s * (l : ℝ)) * x) hresp
  · rintro ⟨l, rfl⟩
    refine ⟨l, ?_⟩
    have hscale : (n + k) - (l : ℤ) = (n - (l : ℤ)) + k := by
      omega
    have hresp := scaleResponseAtScale_dilate h Q (n - (l : ℤ)) p a0
    simpa [hscale] using
      congrArg (fun x => Real.rpow (3 : ℝ) (-s * (l : ℝ)) * x) hresp.symm

theorem HomogenizationError_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (n : ℤ) (s : ℝ) (p q : MultiscaleExponent) (a0 : Mat d) :
    HomogenizationError (dilateCube k Q) (n + k) s p q b a0 =
      HomogenizationError Q n s p q a a0 := by
  cases q with
  | finite q =>
      exact HomogenizationErrorFinite_dilate h Q n s p q a0
  | infinity =>
      exact HomogenizationErrorInfinity_dilate h Q n s p a0

theorem HomogenizationErrorOnCube_dilate {d : ℕ} [NeZero d] {k : ℤ}
    {a b : TriadicCoeffFamily d}
    (h : TriadicCoeffFamily.IsDilation k a b) (Q : TriadicCube d)
    (s : ℝ) (p q : MultiscaleExponent) (a0 : Mat d) :
    HomogenizationErrorOnCube (dilateCube k Q) s p q b a0 =
      HomogenizationErrorOnCube Q s p q a a0 := by
  unfold HomogenizationErrorOnCube
  simpa [dilateCube] using HomogenizationError_dilate h Q Q.scale s p q a0

/-- Proved one-cube dilation theorem package. -/
theorem cubeDilationTheory (d : ℕ) : CubeDilationTheory d where
  solution_dilation_exists := by
    intro k Q a b hCoeff u
    exact ⟨Solution.dilate hCoeff u⟩
  responseValue_dilate := by
    intro k Q a b hCoeff u v hDilation p q
    exact responseValue_dilate_of_isCubeDilation hCoeff hDilation p q
  variationEnergyValue_dilate := by
    intro k Q a b hCoeff u v hDilation
    exact variationEnergyValue_dilate_of_isCubeDilation hCoeff hDilation
  averageGradient_dilate := by
    intro k Q a b hCoeff u v hDilation
    exact averageGradient_dilate_of_isCubeDilation hCoeff hDilation
  averageFlux_dilate := by
    intro k Q a b hCoeff u v hDilation
    exact averageFlux_dilate_of_isCubeDilation hCoeff hDilation
  responseJ_dilate := by
    intro k Q a b hCoeff p q
    exact responseJ_dilate hCoeff p q
  doubledMu_dilate := by
    intro k Q a b hCoeff P
    exact doubledMu_dilate hCoeff P
  doubledResponseJ_dilate := by
    intro k Q a b hCoeff P R
    exact doubledResponseJ_dilate hCoeff P R
  sigmaCoarse_dilate := by
    intro k Q a b hCoeff
    exact sigmaCoarse_dilate hCoeff
  sigmaStarInvCoarse_dilate := by
    intro k Q a b hCoeff
    exact sigmaStarInvCoarse_dilate hCoeff
  sigmaStarCoarse_dilate := by
    intro k Q a b hCoeff
    exact sigmaStarCoarse_dilate hCoeff
  kappaCoarse_dilate := by
    intro k Q a b hCoeff
    exact kappaCoarse_dilate hCoeff
  coarseMatrices_dilate := by
    intro k Q a b hCoeff
    exact coarseMatrices_dilate hCoeff
  bCoarse_dilate := by
    intro k Q a b hCoeff
    exact bCoarse_dilate hCoeff
  aCoarse_dilate := by
    intro k Q a b hCoeff
    exact aCoarse_dilate hCoeff
  aStarCoarse_dilate := by
    intro k Q a b hCoeff
    exact aStarCoarse_dilate hCoeff

/-- Proved Chapter 2.5 multiscale dilation theorem package. -/
theorem multiscaleDilationTheory (d : ℕ) [NeZero d] :
    MultiscaleDilationTheory d where
  coarseBMatrixNorm_dilate := by
    intro k a b h Q
    exact coarseBMatrixNorm_dilate h Q
  coarseSigmaStarInvMatrixNorm_dilate := by
    intro k a b h Q
    exact coarseSigmaStarInvMatrixNorm_dilate h Q
  maxDescendantBMatrixNormAtScale_dilate := by
    intro k a b h Q n
    exact maxDescendantBMatrixNormAtScale_dilate h Q n
  maxDescendantSigmaStarInvMatrixNormAtScale_dilate := by
    intro k a b h Q n
    exact maxDescendantSigmaStarInvMatrixNormAtScale_dilate h Q n
  LambdaSq_dilate := by
    intro k a b h Q s q
    exact LambdaSq_dilate h Q s q
  lambdaSq_dilate := by
    intro k a b h Q s q
    exact lambdaSq_dilate h Q s q
  LambdaS_dilate := by
    intro k a b h Q s
    exact LambdaS_dilate h Q s
  lambdaS_dilate := by
    intro k a b h Q s
    exact lambdaS_dilate h Q s
  ThetaRatio_dilate := by
    intro k a b h Q s t
    exact ThetaRatio_dilate h Q s t
  maxDescendantUpperEllipticityAtScale_dilate := by
    intro k a b h Q n s q
    exact maxDescendantUpperEllipticityAtScale_dilate h Q n s q
  maxDescendantLowerEllipticityInvAtScale_dilate := by
    intro k a b h Q n s q
    exact maxDescendantLowerEllipticityInvAtScale_dilate h Q n s q
  normalizedBlockResponseMax_dilate := by
    intro k a b h Q a0
    exact normalizedBlockResponseMax_dilate h Q a0
  maxDescendantNormalizedBlockResponseAtScale_dilate := by
    intro k a b h Q n a0
    exact maxDescendantNormalizedBlockResponseAtScale_dilate h Q n a0
  scaleResponseAtScale_dilate := by
    intro k a b h Q n p a0
    exact scaleResponseAtScale_dilate h Q n p a0
  HomogenizationError_dilate := by
    intro k a b h Q n s p q a0
    exact HomogenizationError_dilate h Q n s p q a0
  HomogenizationErrorOnCube_dilate := by
    intro k a b h Q s p q a0
    exact HomogenizationErrorOnCube_dilate h Q s p q a0

/-- Aggregate proved public dilation theorem package. -/
theorem dilationTheory (d : ℕ) [NeZero d] : DilationTheory d where
  cube := cubeDilationTheory d
  multiscale := multiscaleDilationTheory d

end

end Ch02
end Book
end Homogenization
