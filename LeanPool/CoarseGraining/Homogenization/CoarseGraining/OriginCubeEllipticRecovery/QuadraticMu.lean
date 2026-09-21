/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Existence

/-!
# Origin-cube elliptic recovery -- quadraticity of Mu on the centered cube

Private sigmaStarCoarse / volumeAverage helpers, quadraticity of Mu on the
centered open cube packaged from recovery data, existence of coarse block
matrices, and the HasOriginCubeResponseJ\{Block,PureFlux,PureGradient\}QuadraticDataAtScale
structures and their construction from hasQuadraticMu.
-/

namespace Homogenization


theorem isSigmaStarCoarse_sigmaStarCoarse_of_isSigmaStarInvCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hSInv : IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a))
    (hdetInv : IsUnit (sigmaStarInvCoarse U a).det) :
    IsSigmaStarCoarse U a (sigmaStarCoarse U a) := by
  refine ⟨?_, ?_⟩
  · unfold sigmaStarCoarse
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    have hT := Matrix.transpose_nonsing_inv (A := sigmaStarInvCoarse U a)
    simpa [hSInv.1.eq] using congrFun (congrFun hT i) j
  · intro q
    have hresp := hSInv.2 q
    unfold sigmaStarCoarse
    rw [Matrix.nonsing_inv_nonsing_inv _ hdetInv]
    simpa using hresp

theorem
    isKappaCoarse_kappaCoarse_of_isSigmaStarInvKappaCoarse_of_isUnit_det_sigmaStarInvCoarse
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hM : IsSigmaStarInvKappaCoarse U a (sigmaStarInvKappaCoarse U a))
    (hdetInv : IsUnit (sigmaStarInvCoarse U a).det) :
    IsKappaCoarse U a (sigmaStarCoarse U a) (kappaCoarse U a) := by
  intro p q
  rw [hM p q]
  unfold kappaCoarse sigmaStarCoarse
  rw [show ((sigmaStarInvCoarse U a)⁻¹)⁻¹ = sigmaStarInvCoarse U a by
    exact Matrix.nonsing_inv_nonsing_inv _ hdetInv]
  let A : Mat d := sigmaStarInvCoarse U a
  let M : Mat d := sigmaStarInvKappaCoarse U a
  have hprod :
      matVecMul (A * (A⁻¹ * M)) p = matVecMul M p := by
    calc
      matVecMul (A * (A⁻¹ * M)) p = matVecMul ((A * A⁻¹) * M) p := by
        rw [Matrix.mul_assoc]
      _ = matVecMul M p := by
        rw [Matrix.mul_nonsing_inv A (by simpa [A] using hdetInv)]
        simp
  simpa [A, M, matVecMul_mul] using congrArg (fun w => vecDot q w) hprod.symm

theorem
    isSigmaStarInvKappaCoarse_neg_coarseBlockMatrix_lowerLeft_of_exact_slices
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
    (hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar)
    (hMuRespQ : ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a)
    (hMuRespP : ∀ p : Vec d, Mu U (p, 0) a = ResponseJ U p 0 a)
    (hResp :
      ∀ p q : Vec d,
        ResponseJ U p q a = Mu U (-p, q) a - vecDot p q) :
    IsSigmaStarInvKappaCoarse U a (-(coarseBlockMatrix U a).lowerLeft) := by
  have hA : IsCoarseBlockMatrix U a (coarseBlockMatrix U a) :=
    isCoarseBlockMatrix_coarseBlockMatrix hex
  intro p q
  have hMuPQ :
      Mu U (-p, q) a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
          vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
    have hraw := hA.2 (-p, q)
    calc
      Mu U (-p, q) a
          = (1 / 2 : ℝ) * blockVecDot (-p, q)
              (blockMatVecMul (coarseBlockMatrix U a) (-p, q)) := hraw
      _ =
          (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) -
            vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) +
            (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
              simpa using
                magic_half_blockVecDot_neg_left_of_isSymmetricBlockMat hA.1 p q
  have hMuP0 :
      Mu U (p, 0) a =
        (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
    calc
      Mu U (p, 0) a
          = (1 / 2 : ℝ) * blockVecDot (p, 0)
              (blockMatVecMul (coarseBlockMatrix U a) (p, 0)) := hA.2 (p, 0)
      _ =
          (1 / 2 : ℝ) * vecDot p (matVecMul (coarseBlockMatrix U a).upperLeft p) := by
            simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
  have hMu0Q :
      Mu U (0, q) a =
        (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) := by
    calc
      Mu U (0, q) a
          = (1 / 2 : ℝ) * blockVecDot (0, q)
              (blockMatVecMul (coarseBlockMatrix U a) (0, q)) := hA.2 (0, q)
      _ =
          (1 / 2 : ℝ) * vecDot q (matVecMul (coarseBlockMatrix U a).lowerRight q) := by
            simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
  have hmain :
      ResponseJ U p q a - ResponseJ U p 0 a - ResponseJ U 0 q a + vecDot p q =
        -vecDot q (matVecMul (coarseBlockMatrix U a).lowerLeft p) := by
    rw [hResp p q, ← hMuRespP p, ← hMuRespQ q, hMuPQ, hMuP0, hMu0Q]
    ring
  simpa [neg_matVecMul, vecDot_neg_right] using hmain

theorem volumeAverage_le_volumeAverage_of_le_on
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {f g : Vec d → ℝ}
    (hU : MeasurableSet U)
    (hf : MeasureTheory.IntegrableOn f U)
    (hg : MeasureTheory.IntegrableOn g U)
    (hfg : ∀ x ∈ U, f x ≤ g x) :
    volumeAverage U f ≤ volumeAverage U g := by
  have hnonneg :
      0 ≤ volumeAverage U (fun x => g x - f x) := by
    apply volumeAverage_nonneg_of_nonneg_on hU
    intro x hx
    exact sub_nonneg.mpr (hfg x hx)
  have hsub :
      volumeAverage U (fun x => g x - f x) =
        volumeAverage U g - volumeAverage U f := by
    simpa using! (volumeAverage_sub hg hf : volumeAverage U (g - f) = _)
  linarith

theorem vecNormSq_volumeAverage_le_volumeAverage_vecNormSq
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : MeasurableSet U) (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    vecNormSq (fun i => volumeAverage U (fun x => f x i)) ≤
      volumeAverage U (fun x => vecNormSq (f x)) := by
  let avg : Vec d := fun i => volumeAverage U (fun x => f x i)
  have hcoord : ∀ i, MeasureTheory.IntegrableOn (fun x => f x i) U := by
    intro i
    simpa [vecDot, Pi.single_apply] using
      (integrableOn_vecDot_of_memVectorL2 hf
        (memVectorL2_const (U := U) (Pi.single i 1)))
  have hdotInt : MeasureTheory.IntegrableOn (fun x => vecDot (f x) avg) U := by
    exact integrableOn_vecDot_of_memVectorL2 hf (memVectorL2_const (U := U) avg)
  have hsqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (f x)) U := by
    simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hf hf
  have hhalfInt :
      MeasureTheory.IntegrableOn ((1 / 2 : ℝ) • fun x => vecNormSq (f x)) U := by
    simpa [smul_eq_mul] using! hsqInt.integrable.smul (1 / 2 : ℝ)
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => (1 / 2 : ℝ) * vecNormSq avg) U := by
    exact MeasureTheory.integrable_const _
  have havgDot :
      volumeAverage U (fun x => vecDot (f x) avg) = vecNormSq avg := by
    calc
      volumeAverage U (fun x => vecDot (f x) avg)
          = vecDot (fun i => volumeAverage U (fun x => f x i)) avg := by
              exact volumeAverage_vecDot_right f avg hcoord
      _ = vecNormSq avg := by
              simp [avg, vecNormSq]
  have hnonneg :
      ∀ x ∈ U,
        0 ≤ (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg + (1 / 2 : ℝ) * vecNormSq avg := by
    intro x hx
    have hsq : 0 ≤ vecNormSq (f x - avg) := vecNormSq_nonneg (f x - avg)
    have hident :
        (1 / 2 : ℝ) * vecNormSq (f x - avg) =
          (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg + (1 / 2 : ℝ) * vecNormSq avg := by
      rw [show f x - avg = f x + (-avg) by simp [sub_eq_add_neg]]
      simp [vecNormSq, vecDot_add_right, vecDot_neg_right, vecDot_comm]
      ring_nf
    nlinarith [hsq, hident]
  have havgNonneg :
      0 ≤
        volumeAverage U
          (fun x =>
            (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg +
              (1 / 2 : ℝ) * vecNormSq avg) := by
    exact volumeAverage_nonneg_of_nonneg_on hU hnonneg
  have havgExpand :
      volumeAverage U
          (fun x =>
            (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg +
              (1 / 2 : ℝ) * vecNormSq avg) =
        (1 / 2 : ℝ) * volumeAverage U (fun x => vecNormSq (f x)) -
          volumeAverage U (fun x => vecDot (f x) avg) +
          (1 / 2 : ℝ) * vecNormSq avg := by
    have hsubInt :
        MeasureTheory.IntegrableOn
          (((1 / 2 : ℝ) • fun x => vecNormSq (f x)) - fun x => vecDot (f x) avg) U := by
      exact hhalfInt.sub hdotInt
    have hfun :
        (fun x =>
          (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg +
            (1 / 2 : ℝ) * vecNormSq avg) =
        ((((1 / 2 : ℝ) • fun x => vecNormSq (f x)) - fun x => vecDot (f x) avg) +
          fun _ : Vec d => (1 / 2 : ℝ) * vecNormSq avg) := by
      funext x
      simp [smul_eq_mul, sub_eq_add_neg, add_assoc]
    calc
      volumeAverage U
          (fun x =>
            (1 / 2 : ℝ) * vecNormSq (f x) - vecDot (f x) avg +
              (1 / 2 : ℝ) * vecNormSq avg)
          =
        volumeAverage U
          ((((1 / 2 : ℝ) • fun x => vecNormSq (f x)) - fun x => vecDot (f x) avg) +
            fun _ : Vec d => (1 / 2 : ℝ) * vecNormSq avg) := by
              rw [hfun]
      _ =
        volumeAverage U
          (((1 / 2 : ℝ) • fun x => vecNormSq (f x)) - fun x => vecDot (f x) avg) +
          volumeAverage U (fun _ : Vec d => (1 / 2 : ℝ) * vecNormSq avg) := by
            rw [volumeAverage_add hsubInt hconstInt]
      _ =
        volumeAverage U ((1 / 2 : ℝ) • fun x => vecNormSq (f x)) -
          volumeAverage U (fun x => vecDot (f x) avg) +
          volumeAverage U (fun _ : Vec d => (1 / 2 : ℝ) * vecNormSq avg) := by
            rw [volumeAverage_sub hhalfInt hdotInt]
      _ =
        (1 / 2 : ℝ) * volumeAverage U (fun x => vecNormSq (f x)) -
          volumeAverage U (fun x => vecDot (f x) avg) +
          (1 / 2 : ℝ) * vecNormSq avg := by
            rw [volumeAverage_smul, volumeAverage_const hvol]
  nlinarith [havgNonneg, havgExpand, havgDot]

/--
Deterministic quadratic well-posedness of `Mu` on the centered open cube,
obtained from the packaged recovery-plus-ellipticity data.
-/
theorem hasQuadraticMu_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a) :
    HasQuadraticMu (openCubeSet (originCube d n)) a := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  rcases hData with ⟨hEll, hCompat⟩
  simpa [U] using
    (PotentialSolenoidalL2RecoveryData.hasQuadraticMuOfIsEllipticFieldOn
      (R := R) (a := a) hEll
      (hvol := volume_openCubeSet_originCube_toReal_pos (d := d) n) hCompat)

/--
Deterministic existence of the coarse block matrix on the centered open cube,
obtained from the packaged recovery-plus-ellipticity data.
-/
theorem exists_coarseBlockMatrix_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a) :
    ∃ Abar : BlockMat d, IsCoarseBlockMatrix (openCubeSet (originCube d n)) a Abar := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  rcases hData with ⟨hEll, hCompat⟩
  simpa [U] using
    (PotentialSolenoidalL2RecoveryData.exists_coarseBlockMatrixOfIsEllipticFieldOn
      (R := R) (a := a) hEll
      (hvol := volume_openCubeSet_originCube_toReal_pos (d := d) n) hCompat)

/--
Minimal deterministic input for the response-side block-quadratic lane on the
origin cube at scale `m` and all of its scale-`n` descendants.

This is the weakest bundled package currently needed to feed the deterministic
`responseJ_blockQuadratic` subadditivity machinery behind the annealed
block/starred monotonicity theorem family.
-/
structure HasOriginCubeResponseJBlockQuadraticDataAtScale
    {d : ℕ} (n m : ℤ) (lam Lam : ℝ) (a : CoeffField d) : Prop where
  hEll :
    IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a
  hRespQ :
    ∀ p q : Vec d,
      ResponseJ (openCubeSet (originCube d m)) p q a =
        (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a) (-p, q)) -
        vecDot p q
  hRespDesc :
    ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ p q : Vec d,
      ResponseJ (openCubeSet R) p q a =
        (1 / 2 : ℝ) * blockVecDot (-p, q)
          (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
        vecDot p q

/--
If `Mu` is quadratic on the coarse open cube and its scale-`n` descendants,
then the full mixed response identity
`ResponseJ(U;p,q,a) = Mu(U;(-p,q),a) - p·q` upgrades directly to the public
response-side block-quadratic package.
-/
theorem hasOriginCubeResponseJBlockQuadraticDataAtScale_of_hasQuadraticMu_of_responseJ_eq_mu_neg_left_sub_vecDot
    {d : ℕ} {n m : ℤ} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a)
    (hQuadQ : HasQuadraticMu (openCubeSet (originCube d m)) a)
    (hRespQ :
      ∀ p q : Vec d,
        ResponseJ (openCubeSet (originCube d m)) p q a =
          Mu (openCubeSet (originCube d m)) (-p, q) a - vecDot p q)
    (hQuadDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, HasQuadraticMu (openCubeSet R) a)
    (hRespDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ p q : Vec d,
        ResponseJ (openCubeSet R) p q a = Mu (openCubeSet R) (-p, q) a - vecDot p q) :
    HasOriginCubeResponseJBlockQuadraticDataAtScale (d := d) n m lam Lam a := by
  refine ⟨hEll, ?_, ?_⟩
  · intro p q
    calc
      ResponseJ (openCubeSet (originCube d m)) p q a
          = Mu (openCubeSet (originCube d m)) (-p, q) a - vecDot p q := hRespQ p q
      _ =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a) (-p, q)) -
          vecDot p q := by
            rw [Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hQuadQ (-p, q)]
  · intro R hR p q
    calc
      ResponseJ (openCubeSet R) p q a
          = Mu (openCubeSet R) (-p, q) a - vecDot p q := hRespDesc R hR p q
      _ =
          (1 / 2 : ℝ) * blockVecDot (-p, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (-p, q)) -
          vecDot p q := by
            rw [Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu (hQuadDesc R hR) (-p, q)]

/--
Minimal deterministic input for the scalar `\sigma_*^{-1}` monotonicity lane
on the origin cube at scale `m` and all of its scale-`n` descendants.

Unlike `HasOriginCubeResponseJBlockQuadraticDataAtScale`, this package only
asks for the pure-flux slice `ResponseJ(U; 0, q)` to match the lower-right
quadratic form of the coarse block matrix.
-/
structure HasOriginCubeResponseJPureFluxQuadraticDataAtScale
    {d : ℕ} (n m : ℤ) (lam Lam : ℝ) (a : CoeffField d) : Prop where
  hEll :
    IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a
  hRespQ :
    ∀ q : Vec d,
      ResponseJ (openCubeSet (originCube d m)) 0 q a =
        (1 / 2 : ℝ) * vecDot q
          (matVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a).lowerRight q)
  hRespDesc :
    ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ q : Vec d,
      ResponseJ (openCubeSet R) 0 q a =
        (1 / 2 : ℝ) * vecDot q
          (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight q)

/--
Minimal deterministic input for the scalar `B` monotonicity lane on the origin
cube at scale `m` and all of its scale-`n` descendants.

This keeps only the pure-gradient slice `ResponseJ(U; p, 0)`, which is enough
for the upper-left scalar observable but does not carry the full block
quadratic response package.
-/
structure HasOriginCubeResponseJPureGradientQuadraticDataAtScale
    {d : ℕ} (n m : ℤ) (lam Lam : ℝ) (a : CoeffField d) : Prop where
  hEll :
    IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a
  hRespP :
    ∀ p : Vec d,
      ResponseJ (openCubeSet (originCube d m)) p 0 a =
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a).upperLeft p)
  hRespDesc :
    ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ p : Vec d,
      ResponseJ (openCubeSet R) p 0 a =
        (1 / 2 : ℝ) * vecDot p
          (matVecMul (coarseBlockMatrix (openCubeSet R) a).upperLeft p)

/--
If `Mu` is already known to be quadratic on the coarse open cube and its
scale-`n` descendants, then the exact pure-flux identities
`Mu(U; (0, q), a) = ResponseJ(U; 0, q, a)` upgrade directly to the public
response-side `\sigma_*^{-1}` slice package.
-/
theorem hasOriginCubeResponseJPureFluxQuadraticDataAtScale_of_hasQuadraticMu_of_mu_zero_right_eq_responseJ_zero
    {d : ℕ} {n m : ℤ} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a)
    (hQuadQ : HasQuadraticMu (openCubeSet (originCube d m)) a)
    (hMuRespQ :
      ∀ q : Vec d,
        Mu (openCubeSet (originCube d m)) (0, q) a =
          ResponseJ (openCubeSet (originCube d m)) 0 q a)
    (hQuadDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, HasQuadraticMu (openCubeSet R) a)
    (hMuRespDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ q : Vec d,
        Mu (openCubeSet R) (0, q) a = ResponseJ (openCubeSet R) 0 q a) :
    HasOriginCubeResponseJPureFluxQuadraticDataAtScale (d := d) n m lam Lam a := by
  refine ⟨hEll, ?_, ?_⟩
  · intro q
    calc
      ResponseJ (openCubeSet (originCube d m)) 0 q a
        = Mu (openCubeSet (originCube d m)) (0, q) a := (hMuRespQ q).symm
      _ = (1 / 2 : ℝ) *
          blockVecDot (0, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a) (0, q)) := by
          simpa using Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hQuadQ (0, q)
      _ = (1 / 2 : ℝ) * vecDot q
          (matVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a).lowerRight q) := by
          simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
  · intro R hR q
    calc
      ResponseJ (openCubeSet R) 0 q a
        = Mu (openCubeSet R) (0, q) a := (hMuRespDesc R hR q).symm
      _ = (1 / 2 : ℝ) *
          blockVecDot (0, q)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (0, q)) := by
          simpa using Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu (hQuadDesc R hR)
            (0, q)
      _ = (1 / 2 : ℝ) * vecDot q
          (matVecMul (coarseBlockMatrix (openCubeSet R) a).lowerRight q) := by
          simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]

/--
If `Mu` is already known to be quadratic on the coarse open cube and its
scale-`n` descendants, then the exact pure-gradient identities
`Mu(U; (p, 0), a) = ResponseJ(U; p, 0, a)` upgrade directly to the public
response-side `B` slice package.
-/
theorem hasOriginCubeResponseJPureGradientQuadraticDataAtScale_of_hasQuadraticMu_of_mu_left_zero_eq_responseJ_zero
    {d : ℕ} {n m : ℤ} {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a)
    (hQuadQ : HasQuadraticMu (openCubeSet (originCube d m)) a)
    (hMuRespQ :
      ∀ p : Vec d,
        Mu (openCubeSet (originCube d m)) (p, 0) a =
          ResponseJ (openCubeSet (originCube d m)) p 0 a)
    (hQuadDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, HasQuadraticMu (openCubeSet R) a)
    (hMuRespDesc :
      ∀ R ∈ descendantsAtScale (originCube d m) n, ∀ p : Vec d,
        Mu (openCubeSet R) (p, 0) a = ResponseJ (openCubeSet R) p 0 a) :
    HasOriginCubeResponseJPureGradientQuadraticDataAtScale (d := d) n m lam Lam a := by
  refine ⟨hEll, ?_, ?_⟩
  · intro p
    calc
      ResponseJ (openCubeSet (originCube d m)) p 0 a
        = Mu (openCubeSet (originCube d m)) (p, 0) a := (hMuRespQ p).symm
      _ = (1 / 2 : ℝ) *
          blockVecDot (p, 0)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a) (p, 0)) := by
          simpa using Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu hQuadQ (p, 0)
      _ = (1 / 2 : ℝ) * vecDot p
          (matVecMul (coarseBlockMatrix (openCubeSet (originCube d m)) a).upperLeft p) := by
          simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]
  · intro R hR p
    calc
      ResponseJ (openCubeSet R) p 0 a
        = Mu (openCubeSet R) (p, 0) a := (hMuRespDesc R hR p).symm
      _ = (1 / 2 : ℝ) *
          blockVecDot (p, 0)
            (blockMatVecMul (coarseBlockMatrix (openCubeSet R) a) (p, 0)) := by
          simpa using Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu (hQuadDesc R hR)
            (p, 0)
      _ = (1 / 2 : ℝ) * vecDot p
          (matVecMul (coarseBlockMatrix (openCubeSet R) a).upperLeft p) := by
          simp [blockMatVecMul, blockVecDot, matVecMul_zero, vecDot_zero_left]

end Homogenization
