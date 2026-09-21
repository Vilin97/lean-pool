/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceBasic

/-! # Correction Space Solenoidal -/

namespace Homogenization

noncomputable section

/-!
# Mu correction-space recovery -- solenoidal / potential / responseSpace

upperImage isSolenoidalOn plus the lowerImage / upperImage memVectorL2,
isPotential, and responseSpace membership theorems, both for the
zero_right slice and in full form, under IsEllipticFieldOn.
-/

namespace MuCorrectionSpaceRecoveryData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

theorem recoveredField_upperImage_isSolenoidalOn_zero_right
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    IsSolenoidalOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).1) := by
  intro φ
  have hzero :=
    R.integral_blockPairingIntegrand_correction_eq_zero
      system
      (P := (0, q))
      (f := φ.toH1Function.grad)
      (g := 0)
      φ.toH1Function.grad_memVectorL2
      (MeasureTheory.MemLp.zero : MemVectorL2 U (0 : Vec d → Vec d))
      φ.isPotentialZeroTraceOn
      (isSolenoidalZeroNormalTraceOn_zero (U := U))
      hvol
  simpa [blockPairingIntegrand, BlockState.eval, blockVecDot, vecDot_comm,
    vecDot_zero_left, vecDot_zero_right] using hzero

theorem recoveredField_lowerImage_memVectorL2_zero_right_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d) :
    MemVectorL2 U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).2) := by
  have hAdm := R.recoveredField_admissible system (0, q)
  have hPot :
      MemVectorL2 U (R.recoveredField system (0, q)).potential := by
    simpa using hAdm.1
  have hFluxDiff :
      MemVectorL2 U (fun x => (R.recoveredField system (0, q)).flux x - q) :=
    hAdm.2.2.1
  have hFlux :
      MemVectorL2 U (R.recoveredField system (0, q)).flux := by
    have hconst : MemVectorL2 U (fun _ : Vec d => q) :=
      MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := q)
    have hsum :
        MemVectorL2 U
          ((fun x => (R.recoveredField system (0, q)).flux x - q) + fun _ : Vec d => q) :=
      hFluxDiff.add hconst
    have hEq :
        ((fun x => (R.recoveredField system (0, q)).flux x - q) + fun _ : Vec d => q) =
          (R.recoveredField system (0, q)).flux := by
      funext x
      simp [sub_eq_add_neg, add_comm]
    rw [hEq] at hsum
    exact hsum
  have hSkewPot :
      MemVectorL2 U
        (fun x => matVecMul (skewPart (a x)) ((R.recoveredField system (0, q)).potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hPot
  have hShift :
      MemVectorL2 U
        (fun x =>
          (R.recoveredField system (0, q)).flux x -
            matVecMul (skewPart (a x)) ((R.recoveredField system (0, q)).potential x)) := by
    simpa [sub_eq_add_neg] using! hFlux.sub hSkewPot
  have hInv :
      MemVectorL2 U
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            ((R.recoveredField system (0, q)).flux x -
              matVecMul (skewPart (a x)) ((R.recoveredField system (0, q)).potential x))) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hShift
  have hEq :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).2) =
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            ((R.recoveredField system (0, q)).flux x -
              matVecMul (skewPart (a x)) ((R.recoveredField system (0, q)).potential x))) := by
    funext x
    simpa [BlockState.eval, blockCoeffField] using
      (blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x)
        (p := (R.recoveredField system (0, q)).potential x)
        (q := (R.recoveredField system (0, q)).flux x))
  simpa [hEq] using hInv

theorem recoveredField_upperImage_memVectorL2_zero_right_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (q : Vec d) :
    MemVectorL2 U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).1) := by
  have hAdm := R.recoveredField_admissible system (0, q)
  have hPot :
      MemVectorL2 U (R.recoveredField system (0, q)).potential := by
    simpa using hAdm.1
  have hLower :
      MemVectorL2 U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system (0, q)).eval x)).2) :=
    R.recoveredField_lowerImage_memVectorL2_zero_right_of_isEllipticFieldOn system hEll q
  have hSymmPot :
      MemVectorL2 U
        (fun x =>
          matVecMul (symmPart (a x)) ((R.recoveredField system (0, q)).potential x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hPot
  have hSkewLower :
      MemVectorL2 U
        (fun x =>
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x)
              ((R.recoveredField system (0, q)).eval x)).2)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hLower
  have hUpper' :
      MemVectorL2 U
        (fun x =>
          matVecMul (symmPart (a x)) ((R.recoveredField system (0, q)).potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((R.recoveredField system (0, q)).eval x)).2)) := by
    simpa [Pi.add_apply] using! hSymmPot.add hSkewLower
  have hEq :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).1) =
        (fun x =>
          matVecMul (symmPart (a x)) ((R.recoveredField system (0, q)).potential x) +
            matVecMul (skewPart (a x))
                ((blockMatVecMul (blockCoeffField a x)
                  ((R.recoveredField system (0, q)).eval x)).2)) := by
    funext x
    have hsnd :
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).2 =
          matVecMul ((symmPart (a x))⁻¹)
            ((R.recoveredField system (0, q)).flux x -
              matVecMul (skewPart (a x))
                ((R.recoveredField system (0, q)).potential x)) := by
      simpa [BlockState.eval, blockCoeffField] using
        (blockMatVecMul_blockMatrixOfCoeff_snd
          (A := a x)
          (p := (R.recoveredField system (0, q)).potential x)
          (q := (R.recoveredField system (0, q)).flux x))
    calc
      (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).1 =
          matVecMul (symmPart (a x)) ((R.recoveredField system (0, q)).potential x) +
            matVecMul (skewPart (a x))
              (matVecMul ((symmPart (a x))⁻¹)
                ((R.recoveredField system (0, q)).flux x -
                  matVecMul (skewPart (a x))
                    ((R.recoveredField system (0, q)).potential x))) := by
              simpa [BlockState.eval, blockCoeffField] using
                (blockMatVecMul_blockMatrixOfCoeff_fst
                  (A := a x)
                  (p := (R.recoveredField system (0, q)).potential x)
                  (q := (R.recoveredField system (0, q)).flux x))
      _ = matVecMul (symmPart (a x)) ((R.recoveredField system (0, q)).potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockCoeffField a x)
                ((R.recoveredField system (0, q)).eval x)).2) := by
              rw [hsnd]
  simpa [hEq] using hUpper'

theorem recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    IsPotentialOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).2) := by
  refine
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      hHodge
      (R.recoveredField_lowerImage_memVectorL2_zero_right_of_isEllipticFieldOn system hEll q)
      ?_
  intro g hg hsol
  have hzero :=
    R.integral_blockPairingIntegrand_correction_eq_zero
      system
      (P := (0, q))
      (f := 0)
      (g := g)
      (MeasureTheory.MemLp.zero : MemVectorL2 U (0 : Vec d → Vec d))
      hg
      (isPotentialZeroTraceOn_zero (U := U))
      hsol
      hvol
  simpa [blockPairingIntegrand, BlockState.eval, blockVecDot, vecDot_zero_left] using hzero

/-- Convex-domain version of the zero-right lower-image potential recovery. -/
theorem recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    IsPotentialOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system (0, q)).eval x)).2) :=
  R.recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hEll (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv) hvol q

theorem recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    BlockResponseSpace a U (R.recoveredField system (0, q)) := by
  let X : BlockState d := R.recoveredField system (0, q)
  have hAdm : IsBlockMuAdmissible U (0, q) X :=
    R.recoveredField_admissible system (0, q)
  have hUpperSol :
      IsSolenoidalOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) :=
    R.recoveredField_upperImage_isSolenoidalOn_zero_right system hvol q
  have hLowerPot :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) :=
    R.recoveredField_lowerImage_isPotential_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
      system hEll hHodge hvol q
  have hFluxSol :
      IsSolenoidalOn U X.flux := by
    have hdiffMem :
        MemVectorL2 U (fun x => X.flux x - q) := hAdm.2.2.1
    have hconstMem : MemVectorL2 U (fun _ : Vec d => q) :=
      MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := q)
    have hsum :
        IsSolenoidalOn U ((fun x => X.flux x - q) + fun _ : Vec d => q) :=
      isSolenoidalOn_add_of_memVectorL2
        hdiffMem
        hconstMem
        hAdm.2.2.2.isSolenoidalOn
        (IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain hU hvol q)
    have hEq : ((fun x => X.flux x - q) + fun _ : Vec d => q) = X.flux := by
      funext x
      simp [X, sub_eq_add_neg, add_comm]
    rw [hEq] at hsum
    exact hsum
  refine ⟨?_, hFluxSol, ?_⟩
  · show IsBlockPotentialOn U X
    unfold IsBlockPotentialOn
    simpa using hAdm.2.1.isPotentialOn
  intro Y hY
  rcases hY with ⟨hYpot, hYflux⟩
  rcases hYpot with ⟨φ, hφ⟩
  let upper : Vec d → Vec d := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
  let lower : Vec d → Vec d := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hYpotL2 : MemVectorL2 U Y.potential := by
    simpa [hφ] using φ.toH1Function.grad_memVectorL2
  have hUpperL2 : MemVectorL2 U upper := by
    simpa [upper, X] using
      R.recoveredField_upperImage_memVectorL2_zero_right_of_isEllipticFieldOn system hEll q
  have hTerm1Int :
      MeasureTheory.IntegrableOn (fun x => vecDot (Y.potential x) (upper x)) U :=
    integrableOn_vecDot_of_memVectorL2 hYpotL2 hUpperL2
  have hTerm1Zero :
      ∫ x in U, vecDot (Y.potential x) (upper x) ∂MeasureTheory.volume = 0 := by
    have hzero := hUpperSol φ
    simpa [upper, hφ, vecDot_comm] using hzero
  have hTerm2Zero :
      ∫ x in U, vecDot (Y.flux x) (lower x) ∂MeasureTheory.volume = 0 := by
    rcases hLowerPot with ⟨u, hu⟩
    have hzero := hYflux u
    simpa [lower, hu] using hzero
  have hrewrite :
      ∫ x in U,
          blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
            ∂MeasureTheory.volume =
        ∫ x in U, vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)
          ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [upper, lower, BlockState.eval, blockVecDot]
  rw [hrewrite]
  by_cases hTerm2Int :
      MeasureTheory.IntegrableOn (fun x => vecDot (Y.flux x) (lower x)) U
  · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hTerm1Zero, hTerm2Zero]
    simp
  · have hSumNotInt :
        ¬MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)) U := by
      intro hSumInt
      exact hTerm2Int
        ((MeasureTheory.integrable_add_iff_integrable_right'
            (μ := MeasureTheory.volume.restrict U) hTerm1Int).mp hSumInt)
    rw [MeasureTheory.integral_undef hSumNotInt]

theorem recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    [HasHodgeConverse U]
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    BlockResponseSpace a U (R.recoveredField system (0, q)) :=
  R.recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hU hEll (HasHodgeConverse.hodgeConverseCriterion (U := U)) hvol q

/-- Convex-domain recovery wrapper for the zero-right response-space witness.
This is the preferred Chapter-2-facing surface when the domain is known to be
bounded open convex: no abstract `HasHodgeConverse` package is required. -/
theorem recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    BlockResponseSpace a U (R.recoveredField system (0, q)) :=
  R.recoveredField_mem_responseSpace_zero_right_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv) hvol q

theorem recoveredField_upperImage_isSolenoidalOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    IsSolenoidalOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system P).eval x)).1) := by
  intro φ
  have hzero :=
    R.integral_blockPairingIntegrand_correction_eq_zero
      system
      (P := P)
      (f := φ.toH1Function.grad)
      (g := 0)
      φ.toH1Function.grad_memVectorL2
      (MeasureTheory.MemLp.zero : MemVectorL2 U (0 : Vec d → Vec d))
      φ.isPotentialZeroTraceOn
      (isSolenoidalZeroNormalTraceOn_zero (U := U))
      hvol
  simpa [blockPairingIntegrand, BlockState.eval, blockVecDot, vecDot_comm,
    vecDot_zero_left, vecDot_zero_right] using hzero

theorem recoveredField_lowerImage_memVectorL2_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (P : BlockVec d) :
    MemVectorL2 U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system P).eval x)).2) := by
  let X : BlockState d := R.recoveredField system P
  have hAdm : IsBlockMuAdmissible U P X := by
    simpa [X] using R.recoveredField_admissible system P
  have hPotDiff : MemVectorL2 U (fun x => X.potential x - P.1) :=
    hAdm.1
  have hPotConst : MemVectorL2 U (fun _ : Vec d => P.1) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := P.1)
  have hPotSum :
      MemVectorL2 U ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) :=
    hPotDiff.add hPotConst
  have hPotEq :
      ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) = X.potential := by
    funext x
    ext i
    simp [sub_eq_add_neg, add_assoc]
  have hPot : MemVectorL2 U X.potential := by
    simpa [hPotEq] using hPotSum
  have hFluxDiff : MemVectorL2 U (fun x => X.flux x - P.2) :=
    hAdm.2.2.1
  have hFluxConst : MemVectorL2 U (fun _ : Vec d => P.2) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := P.2)
  have hFluxSum :
      MemVectorL2 U ((fun x => X.flux x - P.2) + fun _ : Vec d => P.2) :=
    hFluxDiff.add hFluxConst
  have hFluxEq :
      ((fun x => X.flux x - P.2) + fun _ : Vec d => P.2) = X.flux := by
    funext x
    ext i
    simp [sub_eq_add_neg, add_assoc]
  have hFlux : MemVectorL2 U X.flux := by
    simpa [hFluxEq] using hFluxSum
  have hSkewPot :
      MemVectorL2 U
        (fun x => matVecMul (skewPart (a x)) (X.potential x)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hPot
  have hShift :
      MemVectorL2 U
        (fun x => X.flux x -
          matVecMul (skewPart (a x)) (X.potential x)) := by
    simpa [sub_eq_add_neg] using! hFlux.sub hSkewPot
  have hInv :
      MemVectorL2 U
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) :=
    memVectorL2_matVecMul_symmPartInv_of_isEllipticFieldOn hEll hShift
  have hEq :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) =
        (fun x =>
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) := by
    funext x
    simpa [BlockState.eval, blockCoeffField] using
      (blockMatVecMul_blockMatrixOfCoeff_snd
        (A := a x)
        (p := X.potential x)
        (q := X.flux x))
  simpa [X, hEq] using hInv

theorem recoveredField_upperImage_memVectorL2_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (P : BlockVec d) :
    MemVectorL2 U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system P).eval x)).1) := by
  let X : BlockState d := R.recoveredField system P
  have hAdm : IsBlockMuAdmissible U P X := by
    simpa [X] using R.recoveredField_admissible system P
  have hPotDiff : MemVectorL2 U (fun x => X.potential x - P.1) :=
    hAdm.1
  have hPotConst : MemVectorL2 U (fun _ : Vec d => P.1) :=
    MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := P.1)
  have hPotSum :
      MemVectorL2 U ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) :=
    hPotDiff.add hPotConst
  have hPotEq :
      ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) = X.potential := by
    funext x
    ext i
    simp [sub_eq_add_neg, add_assoc]
  have hPot : MemVectorL2 U X.potential := by
    simpa [hPotEq] using hPotSum
  have hLower :
      MemVectorL2 U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x)
            ((R.recoveredField system P).eval x)).2) :=
    R.recoveredField_lowerImage_memVectorL2_of_isEllipticFieldOn system hEll P
  have hLowerX :
      MemVectorL2 U
        (fun x =>
          (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    simpa [X] using hLower
  have hSymmPot :
      MemVectorL2 U
        (fun x => matVecMul (symmPart (a x)) (X.potential x)) :=
    memVectorL2_matVecMul_symmPart_of_isEllipticFieldOn hEll hPot
  have hSkewLower :
      MemVectorL2 U
        (fun x =>
          matVecMul (skewPart (a x))
            ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) :=
    memVectorL2_matVecMul_skewPart_of_isEllipticFieldOn hEll hLowerX
  have hUpper' :
      MemVectorL2 U
        (fun x =>
          matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
    simpa [Pi.add_apply] using! hSymmPot.add hSkewLower
  have hEq :
      (fun x =>
        (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) =
        (fun x =>
          matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2)) := by
    funext x
    have hsnd :
        (blockMatVecMul (blockCoeffField a x) (X.eval x)).2 =
          matVecMul ((symmPart (a x))⁻¹)
            (X.flux x - matVecMul (skewPart (a x)) (X.potential x)) := by
      simpa [BlockState.eval, blockCoeffField] using
        (blockMatVecMul_blockMatrixOfCoeff_snd
          (A := a x)
          (p := X.potential x)
          (q := X.flux x))
    calc
      (blockMatVecMul (blockCoeffField a x) (X.eval x)).1 =
          matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              (matVecMul ((symmPart (a x))⁻¹)
                (X.flux x - matVecMul (skewPart (a x)) (X.potential x))) := by
              simpa [BlockState.eval, blockCoeffField] using
                (blockMatVecMul_blockMatrixOfCoeff_fst
                  (A := a x)
                  (p := X.potential x)
                  (q := X.flux x))
      _ = matVecMul (symmPart (a x)) (X.potential x) +
            matVecMul (skewPart (a x))
              ((blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
              rw [hsnd]
  simpa [X, hEq] using hUpper'

theorem recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    IsPotentialOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system P).eval x)).2) := by
  refine
    IsPotentialOn.of_orthogonal_to_solenoidalZeroNormalTrace_of_memVectorL2_of_hodgeConverseCriterion
      hHodge
      (R.recoveredField_lowerImage_memVectorL2_of_isEllipticFieldOn system hEll P)
      ?_
  intro g hg hsol
  have hzero :=
    R.integral_blockPairingIntegrand_correction_eq_zero
      system
      (P := P)
      (f := 0)
      (g := g)
      (MeasureTheory.MemLp.zero : MemVectorL2 U (0 : Vec d → Vec d))
      hg
      (isPotentialZeroTraceOn_zero (U := U))
      hsol
      hvol
  simpa [blockPairingIntegrand, BlockState.eval, blockVecDot, vecDot_zero_left] using hzero

/-- Convex-domain version of the lower-image potential recovery. -/
theorem recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    IsPotentialOn U
      (fun x =>
        (blockMatVecMul (blockCoeffField a x)
          ((R.recoveredField system P).eval x)).2) :=
  R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hEll (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv) hvol P

theorem recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_hodgeConverseCriterion
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hHodge : HodgeConverseCriterion U)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    BlockResponseSpace a U (R.recoveredField system P) := by
  let X : BlockState d := R.recoveredField system P
  have hAdm : IsBlockMuAdmissible U P X := by
    simpa [X] using R.recoveredField_admissible system P
  have hUpperSol :
      IsSolenoidalOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).1) := by
    simpa [X] using R.recoveredField_upperImage_isSolenoidalOn system hvol P
  have hLowerPot :
      IsPotentialOn U
        (fun x => (blockMatVecMul (blockCoeffField a x) (X.eval x)).2) := by
    simpa [X] using
      R.recoveredField_lowerImage_isPotential_of_isEllipticFieldOn_of_hodgeConverseCriterion
        system hEll hHodge hvol P
  have hFluxSol : IsSolenoidalOn U X.flux := by
    have hdiffMem : MemVectorL2 U (fun x => X.flux x - P.2) :=
      hAdm.2.2.1
    have hconstMem : MemVectorL2 U (fun _ : Vec d => P.2) :=
      MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := P.2)
    have hsum :
        IsSolenoidalOn U ((fun x => X.flux x - P.2) + fun _ : Vec d => P.2) :=
      isSolenoidalOn_add_of_memVectorL2
        hdiffMem
        hconstMem
        hAdm.2.2.2.isSolenoidalOn
        (IsSolenoidalOn.const_isSolenoidalOn_of_isSobolevRegularDomain hU hvol P.2)
    have hEq : ((fun x => X.flux x - P.2) + fun _ : Vec d => P.2) = X.flux := by
      funext x
      ext i
      simp [sub_eq_add_neg, add_assoc]
    rw [hEq] at hsum
    exact hsum
  refine ⟨?_, hFluxSol, ?_⟩
  · have hCorrPot : IsPotentialOn U (fun x => X.potential x - P.1) :=
      hAdm.2.1.isPotentialOn
    have hConstPot : IsPotentialOn U (fun _ : Vec d => P.1) :=
      (H1Function.affineOnIsSobolevRegularDomain hU P.1).isPotentialOn
    have hsum :
        IsPotentialOn U ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) :=
      isPotentialOn_add hCorrPot hConstPot
    have hEq : ((fun x => X.potential x - P.1) + fun _ : Vec d => P.1) = X.potential := by
      funext x
      ext i
      simp [sub_eq_add_neg, add_assoc]
    simpa [IsBlockPotentialOn, hEq] using hsum
  intro Y hY
  rcases hY with ⟨hYpot, hYflux⟩
  rcases hYpot with ⟨φ, hφ⟩
  let upper : Vec d → Vec d := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).1
  let lower : Vec d → Vec d := fun x =>
    (blockMatVecMul (blockCoeffField a x) (X.eval x)).2
  have hYpotL2 : MemVectorL2 U Y.potential := by
    simpa [hφ] using φ.toH1Function.grad_memVectorL2
  have hUpperL2 : MemVectorL2 U upper := by
    simpa [upper, X] using
      R.recoveredField_upperImage_memVectorL2_of_isEllipticFieldOn system hEll P
  have hTerm1Int :
      MeasureTheory.IntegrableOn (fun x => vecDot (Y.potential x) (upper x)) U :=
    integrableOn_vecDot_of_memVectorL2 hYpotL2 hUpperL2
  have hTerm1Zero :
      ∫ x in U, vecDot (Y.potential x) (upper x) ∂MeasureTheory.volume = 0 := by
    have hzero := hUpperSol φ
    simpa [upper, hφ, vecDot_comm] using hzero
  have hTerm2Zero :
      ∫ x in U, vecDot (Y.flux x) (lower x) ∂MeasureTheory.volume = 0 := by
    rcases hLowerPot with ⟨u, hu⟩
    have hzero := hYflux u
    simpa [lower, hu] using hzero
  have hrewrite :
      ∫ x in U,
          blockVecDot (Y.eval x) (blockMatVecMul (blockCoeffField a x) (X.eval x))
            ∂MeasureTheory.volume =
        ∫ x in U, vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)
          ∂MeasureTheory.volume := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    simp [upper, lower, BlockState.eval, blockVecDot]
  rw [hrewrite]
  by_cases hTerm2Int :
      MeasureTheory.IntegrableOn (fun x => vecDot (Y.flux x) (lower x)) U
  · rw [MeasureTheory.integral_add hTerm1Int hTerm2Int, hTerm1Zero, hTerm2Zero]
    simp
  · have hSumNotInt :
        ¬MeasureTheory.IntegrableOn
          (fun x => vecDot (Y.potential x) (upper x) + vecDot (Y.flux x) (lower x)) U := by
      intro hSumInt
      exact hTerm2Int
        ((MeasureTheory.integrable_add_iff_integrable_right'
            (μ := MeasureTheory.volume.restrict U) hTerm1Int).mp hSumInt)
    rw [MeasureTheory.integral_undef hSumNotInt]

theorem recoveredField_mem_responseSpace_of_isEllipticFieldOn
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hU : IsSobolevRegularDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    [HasHodgeConverse U]
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    BlockResponseSpace a U (R.recoveredField system P) :=
  R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hU hEll (HasHodgeConverse.hodgeConverseCriterion (U := U)) hvol P

/-- Convex-domain recovery wrapper for the full block response-space witness.
This keeps the concrete bounded-open-convex Hodge theorem visible at the
public recovery surface. -/
theorem recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (hConv : IsOpenBoundedConvexDomain U)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (P : BlockVec d) :
    BlockResponseSpace a U (R.recoveredField system P) :=
  R.recoveredField_mem_responseSpace_of_isEllipticFieldOn_of_hodgeConverseCriterion
    system hConv.isSobolevRegularDomain hEll
    (hodgeConverseCriterion_of_isOpenBoundedConvexDomain (U := U) hConv) hvol P

end MuCorrectionSpaceRecoveryData

end

end Homogenization
