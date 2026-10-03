/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.MultiscaleQuantities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockResponse
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.StarredSubadditivity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Subadditivity
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.Translation
public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge

/-! # Basic -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped Matrix.Norms.Frobenius
open scoped MatrixOrder

/-!
# Foundational lemmas for multiscale deterministic quantities

This file collects the shared helper lemmas and the first structural wrappers
used by the later `MultiscaleQuantitiesBasic` submodules.
-/

def OpenCubeDeterministicCoarseData {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : Prop :=
  ∃ sigma sigmaStar kappa,
    IsCoarseBlockMatrix (openCubeSet Q) a
      (deterministicCoarseBlockMatrix (openCubeSet Q) a) ∧
    IsSigmaStarCoarse (openCubeSet Q) a sigmaStar ∧
    IsKappaCoarse (openCubeSet Q) a sigmaStar kappa ∧
    IsSigmaCoarse (openCubeSet Q) a sigma sigmaStar kappa ∧
    IsUnit sigmaStar.det

def OpenCubeDescendantDeterministicCoarseData {d : ℕ} (Q : TriadicCube d)
    (a : CoeffField d) : Prop :=
  ∀ l ≤ Q.scale, ∀ R ∈ descendantsAtScale Q l,
    OpenCubeDeterministicCoarseData R a

theorem OpenCubeDescendantDeterministicCoarseData.self {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDescendantDeterministicCoarseData Q a) :
    OpenCubeDeterministicCoarseData Q a := by
  exact hData Q.scale le_rfl Q (by simp [descendantsAtScale_self])

/-- Standalone quadratic formula for `ResponseJ` on a triadic open cube, packaged
from the canonical deterministic coarse-data witness. This is the theorem
surface intended for downstream deterministic and probabilistic chapters that
should not need to unpack the individual coarse witnesses by hand. -/
theorem responseJ_formula_coarseBlockMatrix_openCubeSet_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerRight q) -
        vecDot p q -
        vecDot q (matVecMul (coarseBlockMatrix (openCubeSet Q) a).lowerLeft p) +
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact basic_cg_identities_responseJ_formula_coarseBlockMatrix_of_isSigmaCoarse
    (openCubeSet Q) a hA hS hK hSigma hdet p q

/-- Canonical coarse-variable version of the standalone quadratic `ResponseJ`
formula on a triadic open cube. This is a note-facing reformulation of
`responseJ_formula_coarseBlockMatrix_openCubeSet_of_deterministicCoarseData`. -/
theorem responseJ_formula_canonical_openCubeSet_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) (p q : Vec d) :
    ResponseJ (openCubeSet Q) p q a =
      (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a) q) - vecDot p q +
        vecDot q
          (matVecMul (sigmaStarInvCoarse (openCubeSet Q) a)
            (matVecMul (kappaCoarse (openCubeSet Q) a) p)) +
        (1 / 2 : ℝ) * vecDot p
          (matVecMul
            (bCoarse
              (sigmaCoarse (openCubeSet Q) a)
              (sigmaStarCoarse (openCubeSet Q) a)
              (kappaCoarse (openCubeSet Q) a)) p) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact basic_cg_identities_responseJ_formula_canonical_of_isSigmaCoarse
    (openCubeSet Q) a hS hK hSigma hdet p q

/-- Coarse-block `q = 0` quadratic formula for `ResponseJ` on a triadic open
cube, with all deterministic coarse witnesses discharged by
`OpenCubeDeterministicCoarseData`. -/
theorem responseJ_zero_formula_coarseBlockMatrix_openCubeSet_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) (p : Vec d) :
    ResponseJ (openCubeSet Q) p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul (coarseBlockMatrix (openCubeSet Q) a).upperLeft p) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact basic_cg_identities_responseJ_zero_formula_coarseBlockMatrix_of_isSigmaCoarse
    (openCubeSet Q) a hA hS hK hSigma hdet p

/-- Canonical `q = 0` quadratic formula for `ResponseJ` on a triadic open cube,
with all deterministic coarse witnesses discharged by
`OpenCubeDeterministicCoarseData`. -/
theorem responseJ_zero_formula_canonical_openCubeSet_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) (p : Vec d) :
    ResponseJ (openCubeSet Q) p 0 a =
      (1 / 2 : ℝ) * vecDot p
        (matVecMul
          (bCoarse
            (sigmaCoarse (openCubeSet Q) a)
            (sigmaStarCoarse (openCubeSet Q) a)
            (kappaCoarse (openCubeSet Q) a)) p) := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact basic_cg_identities_responseJ_zero_formula_canonical_of_isSigmaCoarse
    (openCubeSet Q) a hS hK hSigma hdet p

theorem fullBlockVecNormSq_nonneg {d : ℕ} (x : FullBlockVec d) :
    0 ≤ fullBlockVecNormSq x := by
  unfold fullBlockVecNormSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem matNormSq_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matNormSq A := by
  unfold matNormSq
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (A i j)

theorem matNorm_nonneg {d : ℕ} (A : Mat d) :
    0 ≤ matNorm A := by
  unfold matNorm
  exact Real.sqrt_nonneg _

theorem matNorm_eq_norm {d : ℕ} (A : Mat d) :
    matNorm A = ‖A‖ := by
  rw [matNorm, Real.sqrt_eq_rpow]
  simpa [matNormSq, Real.norm_eq_abs, Real.rpow_natCast, sq_abs] using
    (Matrix.frobenius_norm_def A).symm

theorem norm_descendantsAverageMat_le_descendantsAverage_norm {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    ‖descendantsAverageMat Q j F‖ ≤ descendantsAverage Q j (fun R => ‖F R‖) := by
  classical
  let D := descendantsAtDepth Q j
  let c : ℝ := (D.card : ℝ)⁻¹
  have havg :
      descendantsAverageMat Q j F = c • D.sum F := by
    ext i k
    rw [Matrix.smul_apply, Matrix.sum_apply]
    simp [descendantsAverageMat, descendantsAverage, D, c]
  have hc_nonneg : 0 ≤ c := by
    positivity
  calc
    ‖descendantsAverageMat Q j F‖ = ‖c • D.sum F‖ := by
      rw [havg]
    _ = |c| * ‖D.sum F‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ |c| * D.sum (fun R => ‖F R‖) := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (abs_nonneg _)
    _ = c * D.sum (fun R => ‖F R‖) := by
      rw [abs_of_nonneg hc_nonneg]
    _ = descendantsAverage Q j (fun R => ‖F R‖) := by
      simp [descendantsAverage, D, c]

theorem matNorm_descendantsAverageMat_le_descendantsAverage_matNorm {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    matNorm (descendantsAverageMat Q j F) ≤ descendantsAverage Q j (fun R => matNorm (F R)) := by
  simpa [matNorm_eq_norm] using
    norm_descendantsAverageMat_le_descendantsAverage_norm Q j F

@[simp] theorem finsetAverage_singleton {α : Type*} (a : α) (f : α → ℝ) :
    finsetAverage ({a} : Finset α) f = f a := by
  unfold finsetAverage
  simp

@[simp] theorem finsetSsup_singleton {α : Type*} (a : α) (f : α → ℝ) :
    finsetSsup ({a} : Finset α) f = f a := by
  unfold finsetSsup
  simp

theorem finsetAverage_le_finsetSsup {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) :
    finsetAverage s f ≤ finsetSsup s f := by
  classical
  have hBdd : BddAbove (f '' (↑s : Set α)) := by
    exact ((Set.toFinite _).image f).bddAbove
  unfold finsetAverage finsetSsup
  have hsum :
      s.sum f ≤ s.sum (fun _ => sSup (f '' (↑s : Set α))) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    exact le_csSup hBdd ⟨a, ha, rfl⟩
  have hcard : ((s.card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hs)
  calc
    (↑s.card)⁻¹ * s.sum f ≤ (↑s.card)⁻¹ * s.sum (fun _ => sSup (f '' (↑s : Set α))) := by
      refine mul_le_mul_of_nonneg_left hsum ?_
      positivity
    _ = (↑s.card : ℝ)⁻¹ * ((↑s.card : ℝ) * sSup (f '' (↑s : Set α))) := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (((↑s.card : ℝ)⁻¹) * (↑s.card : ℝ)) * sSup (f '' (↑s : Set α)) := by ring
    _ = sSup (f '' (↑s : Set α)) := by
      rw [inv_mul_cancel₀ hcard, one_mul]

theorem descendantsAverage_le_finsetSsup {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : TriadicCube d → ℝ) :
    descendantsAverage Q j f ≤ finsetSsup (descendantsAtDepth Q j) f := by
  exact finsetAverage_le_finsetSsup (descendantsAtDepth Q j)
    (descendantsAtDepth_nonempty Q j) f

theorem matNorm_descendantsAverageMat_le_finsetSsup_matNorm {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → Mat d) :
    matNorm (descendantsAverageMat Q j F) ≤
      finsetSsup (descendantsAtDepth Q j) (fun R => matNorm (F R)) := by
  calc
    matNorm (descendantsAverageMat Q j F)
      ≤ descendantsAverage Q j (fun R => matNorm (F R)) := by
          exact matNorm_descendantsAverageMat_le_descendantsAverage_matNorm Q j F
    _ ≤ finsetSsup (descendantsAtDepth Q j) (fun R => matNorm (F R)) := by
          exact descendantsAverage_le_finsetSsup Q j (fun R => matNorm (F R))

theorem sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar) :
    (sigmaStarInvCoarse U a).PosSemidef := by
  have hInv :
      IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) :=
    isSigmaStarInvCoarse_sigmaStarInvCoarse
      ⟨sigmaStar⁻¹, isSigmaStarInvCoarse_of_isSigmaStarCoarse hS⟩
  rcases hInv with ⟨hSymm, hResp⟩
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hSymm
  · intro q
    have hRespNonneg : 0 ≤ ResponseJ U 0 q a := responseJ_nonneg U 0 q a
    have hQuad :
        0 ≤ vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
      nlinarith [hRespNonneg, hResp q]
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hQuad

theorem bCoarse_posSemidef_of_isSigmaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa) :
    (bCoarse sigma sigmaStar kappa).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · have hSymm : (bCoarse sigma sigmaStar kappa).IsSymm :=
      bCoarse_isSymm_of_isSigmaCoarse hS hSigma
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hSymm
  · intro p
    have hRespNonneg : 0 ≤ ResponseJ U p 0 a := responseJ_nonneg U p 0 a
    have hQuad :
        0 ≤ vecDot p (matVecMul (bCoarse sigma sigmaStar kappa) p) := by
      nlinarith [hRespNonneg, responseJ_zero_eq_half_bCoarse_of_isSigmaCoarse hSigma p]
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hQuad

theorem bCoarse_canonical_posSemidef_of_isSigmaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    (bCoarse (sigmaCoarse U a) (sigmaStarCoarse U a) (kappaCoarse U a)).PosSemidef := by
  rw [sigmaCoarse_eq_of_isSigmaCoarse hS hK hSigma hdet,
    eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet,
    eq_kappaCoarse_of_isKappaCoarse hS hK hdet]
  exact bCoarse_posSemidef_of_isSigmaCoarse hS hSigma

theorem coarseBlockMatrix_upperLeft_posSemidef_of_isSigmaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    ((coarseBlockMatrix U a).upperLeft).PosSemidef := by
  rw [coarseBlockMatrix_upperLeft_eq_bCoarse_of_isCoarseBlockMatrix hA hS hK hSigma hdet]
  exact bCoarse_posSemidef_of_isSigmaCoarse hS hSigma

theorem coarseBlockMatrix_lowerRight_posSemidef_of_isSigmaCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix U a (deterministicCoarseBlockMatrix U a))
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hK : IsKappaCoarse U a sigmaStar kappa)
    (hSigma : IsSigmaCoarse U a sigma sigmaStar kappa)
    (hdet : IsUnit sigmaStar.det) :
    ((coarseBlockMatrix U a).lowerRight).PosSemidef := by
  rw [coarseBlockMatrix_lowerRight_eq_sigmaStar_inv_of_isCoarseBlockMatrix hA hS hK hSigma hdet]
  simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using
    sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse (U := U) (a := a) hS

/-- Positive semidefiniteness of the canonical `sigmaStarInvCoarse` matrix on
an open triadic cube, with the sigma-star coarse witness hidden inside
`OpenCubeDeterministicCoarseData`. -/
theorem sigmaStarInvCoarse_openCubeSet_posSemidef_of_deterministicCoarseData {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) :
    (sigmaStarInvCoarse (openCubeSet Q) a).PosSemidef := by
  rcases hData with ⟨_, sigmaStar, _, _, hS, _, _, _⟩
  exact sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse
    (U := openCubeSet Q) (a := a) hS

/-- Positive semidefiniteness of the canonical `bCoarse` matrix on an open
triadic cube, with the raw sigma/kappa/coarse witnesses hidden inside
`OpenCubeDeterministicCoarseData`. -/
theorem bCoarse_canonical_openCubeSet_posSemidef_of_deterministicCoarseData {d : ℕ}
    {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) :
    (bCoarse
      (sigmaCoarse (openCubeSet Q) a)
      (sigmaStarCoarse (openCubeSet Q) a)
      (kappaCoarse (openCubeSet Q) a)).PosSemidef := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact bCoarse_canonical_posSemidef_of_isSigmaCoarse
    (U := openCubeSet Q) (a := a) hS hK hSigma hdet

/-- Positive semidefiniteness of the upper-left deterministic coarse block on
an open triadic cube, with all raw deterministic coarse witnesses hidden inside
`OpenCubeDeterministicCoarseData`. -/
theorem coarseBlockMatrix_upperLeft_openCubeSet_posSemidef_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) :
    ((coarseBlockMatrix (openCubeSet Q) a).upperLeft).PosSemidef := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact coarseBlockMatrix_upperLeft_posSemidef_of_isSigmaCoarse
    (U := openCubeSet Q) (a := a) hA hS hK hSigma hdet

/-- Positive semidefiniteness of the lower-right deterministic coarse block on
an open triadic cube, with all raw deterministic coarse witnesses hidden inside
`OpenCubeDeterministicCoarseData`. -/
theorem coarseBlockMatrix_lowerRight_openCubeSet_posSemidef_of_deterministicCoarseData
    {d : ℕ} {Q : TriadicCube d} {a : CoeffField d}
    (hData : OpenCubeDeterministicCoarseData Q a) :
    ((coarseBlockMatrix (openCubeSet Q) a).lowerRight).PosSemidef := by
  rcases hData with ⟨sigma, sigmaStar, kappa, hA, hS, hK, hSigma, hdet⟩
  exact coarseBlockMatrix_lowerRight_posSemidef_of_isSigmaCoarse
    (U := openCubeSet Q) (a := a) hA hS hK hSigma hdet

theorem coarseBlockMatrix_cubeSet_eq_openCubeSet_of_triadicCube {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (a : CoeffField d) :
    coarseBlockMatrix (cubeSet Q) a = coarseBlockMatrix (openCubeSet Q) a := by
  let z : Vec d := fun i => (Q.index i : ℝ) * cubeScaleFactor Q
  have hcube :
      cubeSet Q = translateSet z (cubeSet (originCube d Q.scale)) := by
    cases Q with
    | mk scale index =>
        apply Set.ext
        intro x
        rw [mem_translateSet_iff_sub_mem]
        constructor
        · intro hx i
          simpa [z, cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm, add_mul] using hx i
        · intro hx i
          simpa [z, cubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm, add_mul] using hx i
  have hopen :
      openCubeSet Q = translateSet z (openCubeSet (originCube d Q.scale)) := by
    cases Q with
    | mk scale index =>
        apply Set.ext
        intro x
        rw [mem_translateSet_iff_sub_mem]
        constructor
        · intro hx i
          simpa [z, openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm, add_mul] using hx i
        · intro hx i
          simpa [z, openCubeSet, originCube, cubeScaleFactor, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm, add_mul] using hx i
  calc
    coarseBlockMatrix (cubeSet Q) a
        = coarseBlockMatrix (translateSet z (cubeSet (originCube d Q.scale))) a := by
            rw [hcube]
    _ = coarseBlockMatrix (cubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
          exact coarseBlockMatrix_translateSet_eq_translateCoeffField z
            (cubeSet (originCube d Q.scale)) a
    _ = coarseBlockMatrix (openCubeSet (originCube d Q.scale)) (translateCoeffField z a) := by
          exact coarseBlockMatrix_cubeSet_originCube_eq_openCubeSet
            (d := d) (n := Q.scale) (a := translateCoeffField z a)
    _ = coarseBlockMatrix (translateSet z (openCubeSet (originCube d Q.scale))) a := by
          symm
          exact coarseBlockMatrix_translateSet_eq_translateCoeffField z
            (openCubeSet (originCube d Q.scale)) a
    _ = coarseBlockMatrix (openCubeSet Q) a := by
          rw [hopen]

theorem descendantsAverageMat_posSemidef {d : ℕ}
    {Q : TriadicCube d} {j : ℕ} {F : TriadicCube d → Mat d}
    (hF : ∀ R ∈ descendantsAtDepth Q j, (F R).PosSemidef) :
    (descendantsAverageMat Q j F).PosSemidef := by
  classical
  let D := descendantsAtDepth Q j
  let c : ℝ := (D.card : ℝ)⁻¹
  have hsum : (D.sum F).PosSemidef := by
    simpa [D] using (Matrix.posSemidef_sum (s := D) (x := F) hF)
  have hc : 0 ≤ c := by
    positivity
  have havg :
      descendantsAverageMat Q j F = c • D.sum F := by
    ext i k
    rw [Matrix.smul_apply, Matrix.sum_apply]
    simp [descendantsAverageMat, descendantsAverage, D, c]
  rw [havg]
  exact hsum.smul hc

theorem matNormSq_eq_trace_transpose_mul {d : ℕ} (A : Mat d) :
    matNormSq A = Matrix.trace (A.transpose * A) := by
  rw [Matrix.trace_mul_comm]
  simpa [matNormSq, pow_two] using (Matrix.sum_hadamard_eq (A := A) (B := A))

theorem matNormSq_eq_trace_mul_transpose {d : ℕ} (A : Mat d) :
    matNormSq A = Matrix.trace (A * A.transpose) := by
  rw [matNormSq_eq_trace_transpose_mul, Matrix.trace_mul_comm]

theorem matNormSq_eq_trace_mul_self_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) :
    matNormSq A = Matrix.trace (A * A) := by
  rw [matNormSq_eq_trace_mul_transpose]
  have hAT : A.transpose = A := by
    simpa [Matrix.IsSymm] using hA
  rw [hAT]

theorem matNormSq_eq_trace_pow_two_of_isSymm {d : ℕ} {A : Mat d}
    (hA : A.IsSymm) :
    matNormSq A = Matrix.trace (A ^ 2) := by
  simpa [pow_two] using matNormSq_eq_trace_mul_self_of_isSymm hA

theorem matLoewnerLE_sub_posSemidef_of_posSemidef {d : ℕ}
    {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    (B - A).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hB.isHermitian.sub hA.isHermitian) ?_
  intro x
  change 0 ≤ dotProduct x (Matrix.mulVec (B - A) x)
  rw [Matrix.sub_mulVec, dotProduct_sub]
  have hAB' :
      (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec A x) ≤
        (1 / 2 : ℝ) * dotProduct x (Matrix.mulVec B x) := by
    simpa [vecDot, matVecMul] using! hAB x
  nlinarith

theorem matNormSq_le_of_matLoewnerLE_of_posSemidef {d : ℕ}
    {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matNormSq A ≤ matNormSq B := by
  let D : Mat d := B - A
  have hAh : A.IsHermitian := hA.isHermitian
  have hBh : B.IsHermitian := hB.isHermitian
  have hAsymm : A.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hAh
  have hBsymm : B.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hBh
  have hD : D.PosSemidef := by
    dsimp [D]
    exact matLoewnerLE_sub_posSemidef_of_posSemidef hA hB hAB
  let C : Mat d := CFC.sqrt D
  have hCpsd : C.PosSemidef := by
    dsimp [C]
    exact (Matrix.nonneg_iff_posSemidef (A := CFC.sqrt D)).mp (CFC.sqrt_nonneg D)
  have hDsq : C ^ 2 = D := by
    dsimp [C]
    simpa using CFC.sq_sqrt D hD.nonneg
  have hCsymm : C.IsSymm := by
    simpa [Matrix.IsHermitian, Matrix.IsSymm] using hCpsd.isHermitian
  have hCAD : (C * A * C).PosSemidef := by
    have hCACt : (C * A * C.transpose).PosSemidef := by
      simpa [Matrix.mul_assoc] using hA.mul_mul_conjTranspose_same C
    have hCt : C.transpose = C := by
      simpa [Matrix.IsSymm] using hCsymm
    simpa [hCt, Matrix.mul_assoc] using hCACt
  have htraceAD :
      Matrix.trace (A * D) = Matrix.trace (C * A * C) := by
    calc
      Matrix.trace (A * D) = Matrix.trace (A * (C ^ 2)) := by rw [hDsq]
      _ = Matrix.trace (C * A * C) := by
        simpa [pow_two, Matrix.mul_assoc] using (Matrix.trace_mul_cycle A C C)
  have hAD_nonneg : 0 ≤ Matrix.trace (A * D) := by
    rw [htraceAD]
    exact hCAD.trace_nonneg
  have hDA_nonneg : 0 ≤ Matrix.trace (D * A) := by
    rw [Matrix.trace_mul_comm]
    exact hAD_nonneg
  have hDsq_nonneg : 0 ≤ Matrix.trace (D ^ 2) := by
    simpa using (hD.pow 2).trace_nonneg
  have hB_eq : A + D = B := by
    ext i j
    dsimp [D]
    ring
  have htrace_expand :
      Matrix.trace (B ^ 2) =
        Matrix.trace (A ^ 2) + Matrix.trace (A * D) + Matrix.trace (D * A) + Matrix.trace (D ^ 2) := by
    calc
      Matrix.trace (B ^ 2) = Matrix.trace ((A + D) ^ 2) := by rw [← hB_eq]
      _ = Matrix.trace (A ^ 2 + A * D + (D * A + D ^ 2)) := by
        congr 1
        simp [pow_two, Matrix.add_mul, Matrix.mul_add, add_assoc]
        abel_nf
      _ = Matrix.trace (A ^ 2 + A * D) + Matrix.trace (D * A + D ^ 2) := by
        rw [Matrix.trace_add]
      _ = (Matrix.trace (A ^ 2) + Matrix.trace (A * D)) +
            (Matrix.trace (D * A) + Matrix.trace (D ^ 2)) := by
        rw [Matrix.trace_add, Matrix.trace_add]
      _ = Matrix.trace (A ^ 2) + Matrix.trace (A * D) + Matrix.trace (D * A) + Matrix.trace (D ^ 2) := by
        ac_rfl
  have hextra_nonneg :
      0 ≤ Matrix.trace (A * D) + Matrix.trace (D * A) + Matrix.trace (D ^ 2) := by
    refine add_nonneg (add_nonneg hAD_nonneg hDA_nonneg) hDsq_nonneg
  have htrace_le : Matrix.trace (A ^ 2) ≤ Matrix.trace (B ^ 2) := by
    rw [htrace_expand]
    linarith
  rw [matNormSq_eq_trace_pow_two_of_isSymm hAsymm, matNormSq_eq_trace_pow_two_of_isSymm hBsymm]
  exact htrace_le

theorem matNorm_le_of_matLoewnerLE_of_posSemidef {d : ℕ}
    {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : MatLoewnerLE A B) :
    matNorm A ≤ matNorm B := by
  unfold matNorm
  exact Real.sqrt_le_sqrt (matNormSq_le_of_matLoewnerLE_of_posSemidef hA hB hAB)

@[simp] theorem geometricDiscount_one_eq (s : ℝ) :
    geometricDiscount s 1 = 1 - Real.rpow (3 : ℝ) (-s) := by
  unfold geometricDiscount
  simp

@[simp] theorem geometricWeight_one_eq (s : ℝ) (n : ℕ) :
    geometricWeight s 1 n =
      geometricDiscount s 1 * Real.rpow (3 : ℝ) (-s * (n : ℝ)) := by
  unfold geometricWeight
  have hexp : -s * (1 : ℝ) * (n : ℝ) = -s * (n : ℝ) := by ring
  rw [hexp]


end

end Homogenization
