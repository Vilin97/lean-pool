/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MagicIdentities.MuOrdering.Identities
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecoveryBlockResponse
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.HodgeCubeBridge

/-! # Sigma Star Pos Def -/

@[expose] public section

namespace Homogenization

noncomputable section

private theorem volumeAverage_le_volumeAverage_of_le_on_local
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

private theorem vecNormSq_volumeAverage_le_volumeAverage_vecNormSq_local
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

/-!
# MuOrdering -- sigmaStar / sigmaStarInv positive-definiteness wrappers

Positive-definiteness lemmas for `sigmaStarInvCoarse` and `sigmaStarCoarse`
under `IsSigmaStarCoarse`, the elliptic field plus `HodgeConverseCriterion` /
`IsOpenBoundedConvexDomain` bridges, and the corresponding `IsUnit` /
determinant wrappers.
-/

theorem sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (sigmaStarInvCoarse U a).PosDef := by
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  let Rc : MuCorrectionSpaceRecoveryData U := R.toMuCorrectionSpaceRecoveryData
  have hex : ∃ Abar : BlockMat d, IsCoarseBlockMatrix U a Abar :=
    R.exists_coarseBlockMatrixOfIsEllipticFieldOn hEll hvol compat
  have hMuResp :
      ∀ q : Vec d, Mu U (0, q) a = ResponseJ U 0 q a := by
    intro q
    exact
      Rc.mu_zero_right_eq_responseJ_zero_of_isEllipticFieldOn_of_hodgeConverseCriterion
        system hU hEll hHodge hvol.ne' compat.mu_eq_muCandidate q
  have hSInvLower :
      IsSigmaStarInvCoarse U a (coarseBlockMatrix U a).lowerRight := by
    exact
      isSigmaStarInvCoarse_coarseBlockMatrix_lowerRight_of_mu_zero_right_eq_responseJ_zero
        (U := U) (a := a) hex hMuResp
  have hSInv :
      IsSigmaStarInvCoarse U a (sigmaStarInvCoarse U a) := by
    exact isSigmaStarInvCoarse_sigmaStarInvCoarse
      ⟨(coarseBlockMatrix U a).lowerRight, hSInvLower⟩
  have hlam_pos : 0 < lam :=
    MuCoeffOperatorData.lam_pos_of_isEllipticFieldOn (U := U) (a := a) hEll hvol
  have hden_pos : 0 < 1 + 2 * Lam ^ 2 := by
    nlinarith [sq_nonneg Lam]
  have hcoeff_half_pos : 0 < lam / (2 * (1 + 2 * Lam ^ 2)) := by
    have hden2_pos : 0 < 2 * (1 + 2 * Lam ^ 2) := by positivity
    exact div_pos hlam_pos hden2_pos
  have hcoeff_half_nonneg : 0 ≤ lam / (2 * (1 + 2 * Lam ^ 2)) := by
    positivity
  have hquad_pos :
      ∀ q : Vec d, q ≠ 0 → 0 < vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
    intro q hq
    let Xq : BlockState d := Rc.recoveredField system (0, q)
    have hAdm : IsBlockMuAdmissible U (0, q) Xq := by
      simpa [Xq] using Rc.recoveredField_admissible system (0, q)
    have hFluxDiff : MemVectorL2 U (fun x => Xq.flux x - q) :=
      hAdm.fluxCorrection_memL2
    have hFlux : MemVectorL2 U Xq.flux := by
      have hconst : MemVectorL2 U (fun _ : Vec d => q) :=
        MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := q)
      have hsum :
          MemVectorL2 U ((fun x => Xq.flux x - q) + fun _ : Vec d => q) :=
        hFluxDiff.add hconst
      have hEq : ((fun x => Xq.flux x - q) + fun _ : Vec d => q) = Xq.flux := by
        funext x
        simp [Xq, sub_eq_add_neg, add_comm]
      rw [hEq] at hsum
      exact hsum
    have hFluxSqInt : MeasureTheory.IntegrableOn (fun x => vecNormSq (Xq.flux x)) U := by
      simpa [vecNormSq] using integrableOn_vecDot_of_memVectorL2 hFlux hFlux
    have hEnergyInt :
        MeasureTheory.IntegrableOn (blockEnergyDensity a Xq) U := by
      exact blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn
        (Rc.recoveredField_memBlockL2 system (0, q)) hEll
    have hFluxAvg :
        (fun i => volumeAverage U (fun x => Xq.flux x i)) = q := by
      simpa [Xq] using
        congrArg Prod.snd
          (Rc.recoveredField_average_state_of_isSobolevRegularDomain system hU hvol.ne' (0, q))
    have hJensen :
        vecNormSq q ≤ volumeAverage U (fun x => vecNormSq (Xq.flux x)) := by
      have hraw :=
        vecNormSq_volumeAverage_le_volumeAverage_vecNormSq_local
          (U := U)
          (hU := measurableSet_of_isEllipticFieldOn hEll)
          (hvol := hvol.ne')
          hFlux
      rw [hFluxAvg] at hraw
      exact hraw
    have hpoint :
        ∀ x ∈ U,
          (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x) ≤
            blockEnergyDensity a Xq x := by
      intro x hx
      have hcoer :=
        blockMatrixOfCoeff_coercive_of_isEllipticMatrix (hEll.2 x hx) (Xq.eval x)
      have hcoeff_nonneg : 0 ≤ lam / (1 + 2 * Lam ^ 2) := by positivity
      have hflux_le_block :
          vecNormSq (Xq.flux x) ≤ blockVecDot (Xq.eval x) (Xq.eval x) := by
        change vecNormSq (Xq.flux x) ≤ vecNormSq (Xq.potential x) + vecNormSq (Xq.flux x)
        exact le_add_of_nonneg_left (vecNormSq_nonneg (Xq.potential x))
      have hflux_scaled :
          (lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x) ≤
            (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (Xq.eval x) (Xq.eval x) := by
        exact mul_le_mul_of_nonneg_left hflux_le_block hcoeff_nonneg
      have hcoer' :
          (lam / (1 + 2 * Lam ^ 2)) * blockVecDot (Xq.eval x) (Xq.eval x) ≤
            2 * blockEnergyDensity a Xq x := by
        simpa [blockEnergyDensity, Xq] using! hcoer
      have hchain :
          (lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x) ≤
            2 * blockEnergyDensity a Xq x := le_trans hflux_scaled hcoer'
      have hhalf :=
        mul_le_mul_of_nonneg_left hchain (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      have hleft :
          (1 / 2 : ℝ) * ((lam / (1 + 2 * Lam ^ 2)) * vecNormSq (Xq.flux x)) =
            (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x) := by
        field_simp [hden_pos.ne']
      have hright :
          (1 / 2 : ℝ) * (2 * blockEnergyDensity a Xq x) = blockEnergyDensity a Xq x := by
        ring
      rw [hleft, hright] at hhalf
      exact hhalf
    have hEnergyLower :
        (lam / (2 * (1 + 2 * Lam ^ 2))) *
            volumeAverage U (fun x => vecNormSq (Xq.flux x)) ≤
          blockEnergyAverage U a Xq := by
      calc
        (lam / (2 * (1 + 2 * Lam ^ 2))) * volumeAverage U (fun x => vecNormSq (Xq.flux x)) =
          volumeAverage U
            (fun x => (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq (Xq.flux x)) := by
              symm
              simpa [smul_eq_mul] using!
                (volumeAverage_smul U (lam / (2 * (1 + 2 * Lam ^ 2)))
                  (fun x => vecNormSq (Xq.flux x)))
        _ ≤ volumeAverage U (blockEnergyDensity a Xq) := by
              exact volumeAverage_le_volumeAverage_of_le_on_local
                (U := U)
                (hU := measurableSet_of_isEllipticFieldOn hEll)
                (hf := by
                  simpa [smul_eq_mul] using!
                    hFluxSqInt.smul (lam / (2 * (1 + 2 * Lam ^ 2))))
                (hg := hEnergyInt)
                hpoint
        _ = blockEnergyAverage U a Xq := rfl
    have hEnergyRec :
        blockEnergyAverage U a Xq = Mu U (0, q) a := by
      simpa [Xq] using
        Rc.recoveredField_blockEnergyAverage_eq_mu system compat.mu_eq_muCandidate (0, q)
    have hMain :
        (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q ≤
          (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := by
      have hscaledJensen :
          (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q ≤
            (lam / (2 * (1 + 2 * Lam ^ 2))) *
              volumeAverage U (fun x => vecNormSq (Xq.flux x)) := by
        exact mul_le_mul_of_nonneg_left hJensen hcoeff_half_nonneg
      calc
        (lam / (2 * (1 + 2 * Lam ^ 2))) * vecNormSq q ≤
            (lam / (2 * (1 + 2 * Lam ^ 2))) *
              volumeAverage U (fun x => vecNormSq (Xq.flux x)) := hscaledJensen
        _ ≤ blockEnergyAverage U a Xq := hEnergyLower
        _ = Mu U (0, q) a := hEnergyRec
        _ = ResponseJ U 0 q a := hMuResp q
        _ = (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) := hSInv.2 q
    have hqnorm_ne : vecNormSq q ≠ 0 := by
      intro hqnorm
      exact hq (vecNormSq_eq_zero hqnorm)
    have hqnorm_pos : 0 < vecNormSq q := by
      exact lt_of_le_of_ne (vecNormSq_nonneg q) (by simpa [eq_comm] using hqnorm_ne)
    have hhalf_pos :
        0 < (1 / 2 : ℝ) * vecDot q (matVecMul (sigmaStarInvCoarse U a) q) :=
      lt_of_lt_of_le (mul_pos hcoeff_half_pos hqnorm_pos) hMain
    nlinarith
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.IsHermitian, Matrix.IsSymm] using hSInv.1
  · intro q hq
    simpa [dotProduct, Matrix.mulVec, vecDot, matVecMul] using hquad_pos q hq

theorem isUnit_det_sigmaStarInvCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    IsUnit (sigmaStarInvCoarse U a).det := by
  exact
    (Matrix.isUnit_iff_isUnit_det (A := sigmaStarInvCoarse U a)).mp
      ((sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
        (U := U) (a := a) R hU hEll hHodge hvol compat).isUnit)

theorem isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    IsUnit sigmaStar.det := by
  have hInvPos :
      (sigmaStarInvCoarse U a).PosDef :=
    sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat
  have hSigmaInvPos : sigmaStar⁻¹.PosDef := by
    simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using hInvPos
  have hSigmaPos : sigmaStar.PosDef :=
    (Matrix.posDef_inv_iff (M := sigmaStar)).mp hSigmaInvPos
  exact (Matrix.isUnit_iff_isUnit_det (A := sigmaStar)).mp hSigmaPos.isUnit

theorem sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol)) :
    (sigmaStarInvCoarse U a).PosDef :=
  sigmaStarInvCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat

theorem isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    IsUnit sigmaStar.det :=
  isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
    hvol compat hS

theorem sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse_local {d : ℕ}
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

theorem sigmaStarInvCoarse_posDef_of_isSigmaStarCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    (sigmaStarInvCoarse U a).PosDef := by
  have hSemidef :
      (sigmaStarInvCoarse U a).PosSemidef :=
    sigmaStarInvCoarse_posSemidef_of_isSigmaStarCoarse_local (U := U) (a := a) hS
  have hInvDet : IsUnit (sigmaStarInvCoarse U a).det := by
    simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using
      (Matrix.isUnit_nonsing_inv_det (A := sigmaStar) hdet)
  have hInvUnit : IsUnit (sigmaStarInvCoarse U a) :=
    (Matrix.isUnit_iff_isUnit_det (A := sigmaStarInvCoarse U a)).2 hInvDet
  exact (Matrix.PosSemidef.posDef_iff_isUnit hSemidef).2 hInvUnit

theorem sigmaStarCoarse_posDef_of_isSigmaStarCoarse {d : ℕ}
    {U : Set (Vec d)} {a : CoeffField d} {sigmaStar : Mat d}
    (hS : IsSigmaStarCoarse U a sigmaStar)
    (hdet : IsUnit sigmaStar.det) :
    (sigmaStarCoarse U a).PosDef := by
  have hInvPos :
      (sigmaStarInvCoarse U a).PosDef :=
    sigmaStarInvCoarse_posDef_of_isSigmaStarCoarse (U := U) (a := a) hS hdet
  have hSigmaInvPos : sigmaStar⁻¹.PosDef := by
    simpa [sigmaStarInvCoarse_eq_inv_of_isSigmaStarCoarse hS] using hInvPos
  have hSigmaPos : sigmaStar.PosDef :=
    (Matrix.posDef_inv_iff (M := sigmaStar)).mp hSigmaInvPos
  simpa [eq_sigmaStarCoarse_of_isSigmaStarCoarse hS hdet] using hSigmaPos

theorem sigmaStarCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hU : IsSobolevRegularDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    (sigmaStarCoarse U a).PosDef := by
  have hdet :
      IsUnit sigmaStar.det :=
    isUnit_det_of_isSigmaStarCoarse_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hU hEll hHodge hvol compat hS
  exact sigmaStarCoarse_posDef_of_isSigmaStarCoarse (U := U) (a := a) hS hdet

theorem sigmaStarCoarse_posDef_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (R : PotentialSolenoidalL2RecoveryData U)
    (hConv : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : 0 < (MeasureTheory.volume U).toReal)
    (compat :
      PotentialSolenoidalL2RecoveryData.MuRecoveryCompatibilityData (a := a) R
        (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol))
    {sigmaStar : Mat d} (hS : IsSigmaStarCoarse U a sigmaStar) :
    (sigmaStarCoarse U a).PosDef := by
  exact
    sigmaStarCoarse_posDef_of_isEllipticFieldOn_of_hodgeConverseCriterion
      (U := U) (a := a) R hConv.isSobolevRegularDomain hEll
      (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv)
      hvol compat hS

end

end Homogenization
