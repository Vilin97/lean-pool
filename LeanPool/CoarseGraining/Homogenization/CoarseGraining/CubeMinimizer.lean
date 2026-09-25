/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeOpenBridge
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuAdmissibility
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Cube Minimizer -/

@[expose] public section

namespace Homogenization

/-!
# Cube minimizer well-posedness (Proposition 2.2, part)

Formalization of the coarse block minimizer well-posedness on a triadic cube
`originCube d m` against the coarse-graining surface of this development.

The half-open observable and the open-cube variational problem coincide, since
`Mu (cubeSet Q) P a = Mu (openCubeSet Q) P a` holds unconditionally
(`Mu_cubeSet_eq_openCubeSet_of_triadicCube`).  We therefore work against the
pointwise hypothesis `IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a` and
transport every open-cube recovery fact to the half-open cube.

Public deliverables (all on `U = cubeSet (originCube d m)`):

* `exists_cubeBlockMinimizer` — a `Mu`-admissible minimizer `Z_P` realizing the
  energy and lying in the block response space (item (a); the response-space
  conjunct carries the Euler orthogonality (c));
* `cubeBlockMinimizer_euler_orthogonality` — the Euler orthogonality integral
  (item (c));
* `cubeBlockMinimizer_ae_unique` — a.e. uniqueness of the minimizer (item (b));
* `hasQuadraticMu_cube` — quadraticity of `Mu` (item (d));
* `mu_eq_half_coarseBlockMatrix_cube` — `Mu = ½ P·A P` (item (e));
* `isBlockTestOn_sub_of_isBlockMuAdmissible` — the componentwise difference of
  two `Mu`-admissible states for the same `P` is a block test state (load-bearing
  for the `Y = Z̃ − Z` composition used downstream).

All fields are `Vec d = Fin d → ℝ` valued; no `EuclideanSpace`.
-/

noncomputable section

variable {d : ℕ} [NeZero d] {m : ℤ} {Θ : ℝ} {a : CoeffField d}

/-! ## Difference of two admissible states is a block test state -/

omit [NeZero d] in
/-- The componentwise difference `X − X'` of two `Mu`-admissible block states
for the same parameter `P` is a block test state: its potential part is
zero-trace and its flux part is zero-normal-trace.  This is the algebraic
closure the downstream stability lemmas need in order to feed `Y = Z̃ − Z` into
the Euler orthogonality of a minimizer. -/
theorem isBlockTestOn_sub_of_isBlockMuAdmissible
    {U : Set (Vec d)} {P : BlockVec d} {X X' : BlockState d}
    (hX : IsBlockMuAdmissible U P X) (hX' : IsBlockMuAdmissible U P X') :
    IsBlockTestOn U
      { potential := fun x => X.potential x - X'.potential x
        flux := fun x => X.flux x - X'.flux x } := by
  refine ⟨?_, ?_⟩
  · -- potential part: (X.pot − P.1) + (−1)·(X'.pot − P.1) = X.pot − X'.pot
    have hpot :
        IsPotentialZeroTraceOn U
          ((fun x => X.potential x - P.1) + (-1 : ℝ) • (fun x => X'.potential x - P.1)) :=
      isPotentialZeroTraceOn_add hX.isPotentialZeroTrace
        (isPotentialZeroTraceOn_smul hX'.isPotentialZeroTrace (-1))
    have hfun :
        ((fun x => X.potential x - P.1) + (-1 : ℝ) • (fun x => X'.potential x - P.1)) =
          (fun x => X.potential x - X'.potential x) := by
      funext x
      simp [Pi.add_apply, sub_eq_add_neg]
    rw [hfun] at hpot
    exact hpot
  · -- flux part: same combination, with L² integrability for the normal-trace add
    have hmem₁ : MemVectorL2 U (fun x => X.flux x - P.2) := hX.fluxCorrection_memL2
    have hmem₂ : MemVectorL2 U ((-1 : ℝ) • fun x => X'.flux x - P.2) :=
      hX'.fluxCorrection_memL2.const_smul (-1)
    have hsol :
        IsSolenoidalZeroNormalTraceOn U
          ((fun x => X.flux x - P.2) + (-1 : ℝ) • (fun x => X'.flux x - P.2)) :=
      isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 hmem₁ hmem₂
        hX.isSolenoidalZeroNormalTrace
        (isSolenoidalZeroNormalTraceOn_smul hX'.isSolenoidalZeroNormalTrace (-1))
    have hfun :
        ((fun x => X.flux x - P.2) + (-1 : ℝ) • (fun x => X'.flux x - P.2)) =
          (fun x => X.flux x - X'.flux x) := by
      funext x
      simp [Pi.add_apply, sub_eq_add_neg]
    rw [hfun] at hsol
    exact hsol

/-! ## Open-cube recovery core -/

omit [NeZero d] in
/-- Finite-measure instance for the centered open cube. -/
private theorem isFiniteMeasure_volumeMeasureOn_openCubeSet_originCube (m : ℤ) :
    MeasureTheory.IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) := by
  let : Fact (MeasureTheory.volume (openCubeSet (originCube d m)) < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) m⟩
  change MeasureTheory.IsFiniteMeasure
    (MeasureTheory.volume.restrict (openCubeSet (originCube d m)))
  infer_instance

/-- Existence of a `Mu`-admissible energy-realizing minimizer in the block
response space, on the centered **open** cube, from pointwise ellipticity.  This
is the analytic heart; the half-open version is a transport of this. -/
private theorem exists_openCube_minimizer
    (hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a) (P : BlockVec d) :
    ∃ Z : BlockState d,
      IsBlockMuAdmissible (openCubeSet (originCube d m)) P Z ∧
        Mu (openCubeSet (originCube d m)) P a =
          blockEnergyAverage (openCubeSet (originCube d m)) a Z ∧
        BlockResponseSpace a (openCubeSet (originCube d m)) Z := by
  classical
  let := isFiniteMeasure_volumeMeasureOn_openCubeSet_originCube (d := d) m
  obtain ⟨R, hData⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := 1) (Lam := Θ) m a hEllO
  obtain ⟨hEllR, hCompat⟩ := hData
  set hvol := volume_openCubeSet_originCube_toReal_pos (d := d) m with hvoldef
  set system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR hvol with hsystem
  let family := R.toLinearMuMinimizerFamily system hCompat
  refine ⟨family.field P, family.admissible P, family.realizes P, ?_⟩
  have hConv : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  exact
    R.toMuCorrectionSpaceRecoveryData.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      system hConv hEllR hvol.ne' P

/-! ## Public deliverables on the half-open cube -/

/-- **(a)** Existence of a `Mu`-admissible minimizer `Z_P` on the half-open
triadic cube, realizing the energy and lying in the block response space.  The
`BlockResponseSpace` conjunct is exactly the Euler orthogonality (c). -/
theorem exists_cubeBlockMinimizer
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    ∃ Z : BlockState d,
      IsBlockMuAdmissible (cubeSet (originCube d m)) P Z ∧
        Mu (cubeSet (originCube d m)) P a =
          blockEnergyAverage (cubeSet (originCube d m)) a Z ∧
        BlockResponseSpace a (cubeSet (originCube d m)) Z := by
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a :=
    hEll.mono (measurableSet_openCubeSet (originCube d m))
      (openCubeSet_subset_cubeSet (originCube d m))
  obtain ⟨Z, hAdm, hEnergy, hResp⟩ := exists_openCube_minimizer (d := d) hEllO P
  refine ⟨Z, ?_, ?_, ?_⟩
  · exact (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).2 hAdm
  · rw [Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P a, hEnergy]
    unfold blockEnergyAverage
    exact
      (volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) m
        (blockEnergyDensity a Z)).symm
  · exact (blockResponseSpace_cubeSet_originCube_iff_openCubeSet).2 hResp

omit [NeZero d] in
/-- **(c)** Euler orthogonality of the coarse block minimizer: for every
admissible block test perturbation `Y`, the pairing of `Y` against
`𝐁 Z = blockCoeffField a · Z` integrates to zero. -/
theorem cubeBlockMinimizer_euler_orthogonality
    {Z : BlockState d} (hResp : BlockResponseSpace a (cubeSet (originCube d m)) Z)
    {Y : BlockState d} (hY : IsBlockTestOn (cubeSet (originCube d m)) Y) :
    ∫ x in cubeSet (originCube d m),
        blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (Z.eval x))
          ∂MeasureTheory.volume = 0 :=
  hResp.2.2 Y hY

omit [NeZero d] in
/-- The `Y = Z̃ − Z` instantiation of Euler orthogonality used downstream:
the difference of two admissible states for the same `P` is a valid test
perturbation, so it pairs to zero against `𝐁 Z` for a minimizer `Z`. -/
theorem cubeBlockMinimizer_euler_orthogonality_sub
    {P : BlockVec d} {Z X X' : BlockState d}
    (hResp : BlockResponseSpace a (cubeSet (originCube d m)) Z)
    (hX : IsBlockMuAdmissible (cubeSet (originCube d m)) P X)
    (hX' : IsBlockMuAdmissible (cubeSet (originCube d m)) P X') :
    ∫ x in cubeSet (originCube d m),
        blockVecDot ((X.eval x) - (X'.eval x))
          (blockMatVecMul (blockCoeffField a x) (Z.eval x))
          ∂MeasureTheory.volume = 0 := by
  have hY :
      IsBlockTestOn (cubeSet (originCube d m))
        { potential := fun x => X.potential x - X'.potential x
          flux := fun x => X.flux x - X'.flux x } :=
    isBlockTestOn_sub_of_isBlockMuAdmissible hX hX'
  have h := cubeBlockMinimizer_euler_orthogonality (Z := Z) hResp hY
  refine Eq.trans ?_ h
  apply MeasureTheory.setIntegral_congr_fun (measurableSet_cubeSet _)
  intro x _
  rfl

/-- **(d)** Quadraticity of `Mu` on the half-open triadic cube. -/
theorem hasQuadraticMu_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) :
    HasQuadraticMu (cubeSet (originCube d m)) a := by
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a :=
    hEll.mono (measurableSet_openCubeSet (originCube d m))
      (openCubeSet_subset_cubeSet (originCube d m))
  obtain ⟨R, hData⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := 1) (Lam := Θ) m a hEllO
  have hQuadO : HasQuadraticMu (openCubeSet (originCube d m)) a :=
    hasQuadraticMu_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData R hData
  exact (hasQuadraticMu_cubeSet_iff_openCubeSet_of_triadicCube (originCube d m)).2 hQuadO

/-- **(e)** The note-faithful quadratic representation
`Mu (U; P, a) = ½ P·𝐀(U; a) P` on the half-open triadic cube. -/
theorem mu_eq_half_coarseBlockMatrix_cube
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) (P : BlockVec d) :
    Mu (cubeSet (originCube d m)) P a =
      (1 / 2 : ℝ) *
        blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P) :=
  Mu_eq_half_blockVecDot_coarseBlockMatrix_of_hasQuadraticMu (hasQuadraticMu_cube hEll) P

/-! ## Uniqueness -/

omit [NeZero d] in
/-- Any admissible block state that realizes the energy minimum on the centered
open cube maps to the canonical Hilbert minimizer.  This is the strict-convexity
core of a.e. uniqueness: the recovery data identifies `Mu` with the Hilbert
minimizer value, and the affine minimizer is unique in `L²`. -/
private theorem toHilbert_eq_minimizerMap_of_admissible_energy_eq
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d m)))
    {lam Lam : ℝ} (hEllR : IsEllipticFieldOn lam Lam (openCubeSet (originCube d m)) a)
    (hCompat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR
          (volume_openCubeSet_originCube_toReal_pos (d := d) m)))
    {P : BlockVec d} {W : BlockState d}
    (hW : IsBlockMuAdmissible (openCubeSet (originCube d m)) P W)
    (hWmin :
      blockEnergyAverage (openCubeSet (originCube d m)) a W =
        Mu (openCubeSet (originCube d m)) P a) :
    letI := isFiniteMeasure_volumeMeasureOn_openCubeSet_originCube (d := d) m
    toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hW.memBlockL2_eval =
      (R.toMuHilbertRealization
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR
          (volume_openCubeSet_originCube_toReal_pos (d := d) m))).minimizerMap P := by
  let := isFiniteMeasure_volumeMeasureOn_openCubeSet_originCube (d := d) m
  set hvol := volume_openCubeSet_originCube_toReal_pos (d := d) m with hvoldef
  set system := R.toMuOperatorSystemDataOfIsEllipticFieldOn hEllR hvol with hsystem
  set H := R.toMuHilbertRealization system with hH
  have hWmemBlock : MemBlockL2 (openCubeSet (originCube d m)) W.eval := hW.memBlockL2_eval
  -- the admissible correction lands in the correction subspace
  have hcorr :
      (hW.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 ∈
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace :=
    R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
      (hW.toCorrectionFieldDataOfAdmissible).potential_memL2
      (hW.toCorrectionFieldDataOfAdmissible).flux_memL2
      (hW.toCorrectionFieldDataOfAdmissible).isPotentialZeroTrace
      (hW.toCorrectionFieldDataOfAdmissible).isSolenoidalZeroNormalTrace
  have hconst_add :
      toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hWmemBlock =
        blockVecToHilbertBlockL2Const (U := openCubeSet (originCube d m)) P +
          (hW.toCorrectionFieldDataOfAdmissible).toHilbertBlockL2 :=
    hW.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
  have hcorr_mem :
      toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hWmemBlock -
          H.constantField P ∈ H.correctionSpace.correctionSpace := by
    rw [hconst_add]
    simpa [H, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
      MuOperatorSystemData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcorr
  -- the energy of the competitor equals the minimizer value
  have hqe :
      quadraticEnergy (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hWmemBlock) =
        blockEnergyAverage (openCubeSet (originCube d m)) a W :=
    system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState hWmemBlock
  have hEB :
      H.energyBilin = energyBilinOfOperator system.toMuOperatorRealization.operator := by
    simp [H, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
      MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator]
  have hle :
      quadraticEnergy H.energyBilin
          (toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hWmemBlock) ≤
        H.muCandidate P := by
    rw [hEB, hqe, hWmin, hCompat.mu_eq_muCandidate P]
  exact
    H.eq_minimizerMap_of_quadraticEnergy_le_muCandidate P
      (toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hWmemBlock)
      hcorr_mem hle

/-- **(b)** A.e. uniqueness of the coarse block minimizer: any two `Mu`-admissible
states that both realize the minimum energy for the same parameter `P` agree
almost everywhere (as evaluations) on the half-open triadic cube. -/
theorem cubeBlockMinimizer_ae_unique
    (hEll : IsEllipticFieldOn 1 Θ (cubeSet (originCube d m)) a) {P : BlockVec d}
    {Z Z' : BlockState d}
    (hZ : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z)
    (hZ' : IsBlockMuAdmissible (cubeSet (originCube d m)) P Z')
    (hZe : Mu (cubeSet (originCube d m)) P a =
      blockEnergyAverage (cubeSet (originCube d m)) a Z)
    (hZ'e : Mu (cubeSet (originCube d m)) P a =
      blockEnergyAverage (cubeSet (originCube d m)) a Z') :
    (fun x => Z.eval x) =ᵐ[volumeMeasureOn (cubeSet (originCube d m))]
      (fun x => Z'.eval x) := by
  classical
  let := isFiniteMeasure_volumeMeasureOn_openCubeSet_originCube (d := d) m
  -- transport hypotheses to the open cube
  have hEllO : IsEllipticFieldOn 1 Θ (openCubeSet (originCube d m)) a :=
    hEll.mono (measurableSet_openCubeSet (originCube d m))
      (openCubeSet_subset_cubeSet (originCube d m))
  have hZO : IsBlockMuAdmissible (openCubeSet (originCube d m)) P Z :=
    (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).1 hZ
  have hZ'O : IsBlockMuAdmissible (openCubeSet (originCube d m)) P Z' :=
    (isBlockMuAdmissible_cubeSet_originCube_iff_openCubeSet).1 hZ'
  have henergyTransport :
      ∀ W : BlockState d,
        blockEnergyAverage (cubeSet (originCube d m)) a W =
          blockEnergyAverage (openCubeSet (originCube d m)) a W := by
    intro W
    unfold blockEnergyAverage
    exact volumeAverage_cubeSet_originCube_eq_openCubeSet (d := d) m (blockEnergyDensity a W)
  have hZminO :
      blockEnergyAverage (openCubeSet (originCube d m)) a Z =
        Mu (openCubeSet (originCube d m)) P a := by
    rw [← henergyTransport Z, ← hZe, Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P a]
  have hZ'minO :
      blockEnergyAverage (openCubeSet (originCube d m)) a Z' =
        Mu (openCubeSet (originCube d m)) P a := by
    rw [← henergyTransport Z', ← hZ'e, Mu_cubeSet_originCube_eq_openCubeSet (d := d) m P a]
  -- recovery data
  obtain ⟨R, hData⟩ :=
    openCubeOriginEllipticRecoveryExistence (d := d) (lam := 1) (Lam := Θ) m a hEllO
  obtain ⟨hEllR, hCompat⟩ := hData
  -- both minimizers map to the canonical Hilbert minimizer
  have hZmap :
      toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZO.memBlockL2_eval =
        toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZ'O.memBlockL2_eval := by
    rw [toHilbert_eq_minimizerMap_of_admissible_energy_eq (d := d) R hEllR hCompat hZO hZminO,
      toHilbert_eq_minimizerMap_of_admissible_energy_eq (d := d) R hEllR hCompat hZ'O hZ'minO]
  -- unfold Lp equality to a.e. equality of evaluations
  have hcoeZ :
      toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZO.memBlockL2_eval =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        hilbertifyBlockField Z.eval :=
    coeFn_toHilbertBlockL2OfBlockField hZO.memBlockL2_eval
  have hcoeZ' :
      toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZ'O.memBlockL2_eval =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        hilbertifyBlockField Z'.eval :=
    coeFn_toHilbertBlockL2OfBlockField hZ'O.memBlockL2_eval
  have hcoeEq :
      (⇑(toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZO.memBlockL2_eval)) =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        (⇑(toHilbertBlockL2OfBlockField (U := openCubeSet (originCube d m)) hZ'O.memBlockL2_eval)) := by
    rw [hZmap]
  have hHilEq :
      hilbertifyBlockField Z.eval =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        hilbertifyBlockField Z'.eval :=
    (hcoeZ.symm.trans hcoeEq).trans hcoeZ'
  have hOpen :
      (fun x => Z.eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d m))]
        (fun x => Z'.eval x) := by
    filter_upwards [hHilEq] with x hx
    have := congrArg HilbertBlockVec.toBlockVec hx
    simpa [hilbertifyBlockField, HilbertBlockVec.toBlockVec_ofBlockVec] using this
  -- transfer the a.e. statement across the null cube boundary
  rw [show volumeMeasureOn (cubeSet (originCube d m)) =
        volumeMeasureOn (openCubeSet (originCube d m)) from
      volume_restrict_cubeSet_originCube_eq_volume_restrict_openCubeSet_originCube (d := d) m]
  exact hOpen

end

end Homogenization
