/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Translate

/-!
# Origin-cube elliptic recovery -- lower bound and exact slice equalities

The long mu_ge_vecDot_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
packaging, together with the pure-flux and pure-gradient slice equalities
feeding DeterministicCoarseData.
-/

@[expose] public section

namespace Homogenization

/--
Lower bound `Mu` against the scalar product on the centered open cube,
packaged directly from deterministic recovery-plus-ellipticity data.
-/
theorem mu_ge_vecDot_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
  rcases hData with ⟨hEll, hCompat⟩
  exact
    PotentialSolenoidalL2RecoveryData.mu_ge_vecDot_openCubeSet_originCubeOfIsEllipticFieldOn
      (R := R) (a := a) (hEll := hEll) (compat := hCompat) P

/--
On the centered open cube, the zero-right recovered response-space witness can
be split into a primal/adjoint scalar half-pair at the level of averaged block
response integrands.

This exposes the existing deterministic pair-half reconstruction directly from
`HasOpenCubeEllipticRecoveryData`, without yet claiming the sharper exact slice
identity `Mu(U; (0,q), a) = ResponseJ(U; 0, q, a)`.
-/
theorem
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (q0 : Vec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        (fun x =>
          (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
            fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)).eval x := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let hCube : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_openCubeSet (originCube d n)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using hCube.isFiniteMeasure_restrict_volume
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 :=
    (volume_openCubeSet_originCube_toReal_pos (d := d) n).ne'
  simpa [U, system] using
    (R.toMuCorrectionSpaceRecoveryData).exists_blockResponsePairHalfState_ae_eq_recoveredField_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) system hCube hEll hvol q0

theorem
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_isEllipticFieldOn_of_blockVec
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (P : BlockVec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        (fun x =>
          (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
            fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P).eval x := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let hCube : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_openCubeSet (originCube d n)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using hCube.isFiniteMeasure_restrict_volume
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 :=
    (volume_openCubeSet_originCube_toReal_pos (d := d) n).ne'
  simpa [U, system] using
    (R.toMuCorrectionSpaceRecoveryData).exists_blockResponsePairHalfState_ae_eq_recoveredField_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) system hCube hEll hvol P

theorem
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q0 : Vec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn
        (Classical.choose hData)
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        (fun x =>
          (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
            fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)).eval x := by
  rcases hData with ⟨hEll, _hCompat⟩
  simpa using
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_isEllipticFieldOn
      (R := R) (a := a) hEll q0

theorem
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_blockVec
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (P : BlockVec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn
        (Classical.choose hData)
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        (fun x =>
          (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
            fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P).eval x := by
  rcases hData with ⟨hEll, _hCompat⟩
  simpa using
    exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_isEllipticFieldOn_of_blockVec
      (R := R) (a := a) hEll P

theorem
    exists_recoveredField_scalarHalfPair_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q0 : Vec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn
        (Classical.choose hData)
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        ((fun x =>
          (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
            fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)).eval x) ∧
        ∀ p pStar q qStar : Vec d,
          volumeAverage (openCubeSet (originCube d n))
              (blockResponseIntegrand a (p, q) (qStar, pStar)
                ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
            (1 / 2 : ℝ) *
                volumeAverage (openCubeSet (originCube d n))
                  (scalarResponseIntegrand
                    (openCubeSet (originCube d n)) a (p - pStar) (qStar - q) u) +
              (1 / 2 : ℝ) *
                volumeAverage (openCubeSet (originCube d n))
                  (scalarResponseIntegrand
                    (openCubeSet (originCube d n)) (Homogenization.adjointCoeffField a)
                    (pStar + p) (qStar + q) v) := by
  rcases hData with ⟨hEll, _hCompat⟩
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let hCube : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_openCubeSet (originCube d n)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using hCube.isFiniteMeasure_restrict_volume
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  rcases
      exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_isEllipticFieldOn
        (R := R) (a := a) hEll q0 with
    ⟨u, v, hEq⟩
  have hSplit :
      ∀ p pStar q qStar : Vec d,
        volumeAverage U
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
          (1 / 2 : ℝ) *
              volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
    intro p pStar q qStar
    have hIntegrandEq :
        blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v) =ᵐ[volumeMeasureOn U]
          blockResponseIntegrand a (p, q) (qStar, pStar)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)) := by
      filter_upwards [hEq] with x hx
      simpa [blockResponseIntegrand, blockEnergyDensity] using congrArg
        (fun z => -(1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z)
          - blockVecDot (p, q) (blockMatVecMul (blockCoeffField a x) z) +
            blockVecDot (qStar, pStar) z) hx
    have hAvgEq :
        volumeAverage U
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
          volumeAverage U
            (blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v)) := by
      unfold volumeAverage
      congr 1
      exact MeasureTheory.integral_congr_ae hIntegrandEq.symm
    calc
      volumeAverage U
          (blockResponseIntegrand a (p, q) (qStar, pStar)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
        volumeAverage U
          (blockResponseIntegrand a (p, q) (qStar, pStar) (blockResponsePairHalfState a u v)) := hAvgEq
      _ = (1 / 2 : ℝ) * volumeAverage U (scalarResponseIntegrand U a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage U
                (scalarResponseIntegrand U (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
            exact
              volumeAverage_blockResponseIntegrand_pair_half_eq_scalarResponse_sum_of_isEllipticFieldOn
                (a := a) hCube.1.measurableSet hEll p pStar q qStar u v
  exact ⟨u, v, hEq, by simpa [U, system] using hSplit⟩

/--
Sigma-free pure-flux coupling handoff on the centered open cube.

Once a recovered primal/adjoint half-pair is known to satisfy the primal scalar
Euler-Lagrange identity for `ResponseJ(U; 0, q0, a)`, the recovery energy and
zero state-pairing identities identify the pure-flux slice of `Mu` with the
scalar response value. The remaining bridge is therefore exactly the derivation
of the `hPairFirst` first-variation clause from recovery data.
-/
theorem
    mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_exists_recovered_pair_firstVariation_eq_zero
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q0 : Vec d)
    (hPairFirst :
      let system :=
        R.toMuOperatorSystemDataOfIsEllipticFieldOn
          (Classical.choose hData)
          (volume_openCubeSet_originCube_toReal_pos (d := d) n)
      ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
        ∃ v :
            AHarmonicFunction (Homogenization.adjointCoeffField a)
              (openCubeSet (originCube d n)),
          ((fun x =>
            (blockResponsePairHalfState a u v).eval x) =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
              fun x => ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)).eval x) ∧
          ∀ w : AHarmonicFunction a (openCubeSet (originCube d n)),
            volumeAverage (openCubeSet (originCube d n))
              (scalarFirstVariationIntegrand
                (openCubeSet (originCube d n)) a 0 q0 u w) = 0) :
    Mu (openCubeSet (originCube d n)) (0, q0) a =
      ResponseJ (openCubeSet (originCube d n)) 0 q0 a := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  rcases hData with ⟨hEll, hCompat⟩
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  rcases hPairFirst with ⟨u, v, hEq, hfirst⟩
  let Xrec : BlockState d :=
    (R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (0, q0) a := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_blockEnergyAverage_eq_mu
        system hCompat.mu_eq_muCandidate (0, q0)
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = 0 := by
    have h :=
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_average_pairing_openCubeSet_originCube
        system (0, q0)
    simpa [U, Xrec, vecDot_zero_left] using h
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U 0 q0 a := by
    simpa [U, Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_zero_of_pairingAverage_eq_zero_of_firstVariation_eq_zero
        (a := a) (measurableSet_openCubeSet (originCube d n)) hEll q0 u v hPair hfirst
  calc
    Mu (openCubeSet (originCube d n)) (0, q0) a = Mu U (0, q0) a := by rfl
    _ = blockEnergyAverage U a Xrec := hEnergyRec.symm
    _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
    _ = ResponseJ U 0 q0 a := hCouple
    _ = ResponseJ (openCubeSet (originCube d n)) 0 q0 a := by rfl

/--
Pure-flux exact slice on the centered open cube from recovery data alone.

This removes the temporary explicit first-variation hypothesis from the
sigma-free coupling handoff: recovery admissibility of the `\mu` minimizer and
the recovered half-pair reconstruction imply the primal scalar Euler-Lagrange
identity needed by the deterministic coupling lemma.
-/
theorem
    mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q0 : Vec d) :
    Mu (openCubeSet (originCube d n)) (0, q0) a =
      ResponseJ (openCubeSet (originCube d n)) 0 q0 a := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  let hEll : IsEllipticFieldOn lam Lam U a := Classical.choose hData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  rcases
      exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
        (R := R) (a := a) hData q0 with
    ⟨u, v, hEq⟩
  let Xrec : BlockState d :=
    (R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0)
  have hAdm : IsBlockMuAdmissible U (0, q0) Xrec := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system (0, q0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a 0 q0 u w) = 0 := by
    simpa [U, Xrec] using
      scalarFirstVariation_zero_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := measurableSet_openCubeSet (originCube d n))
        hEll q0 u v Xrec hEq hAdm
  refine
    mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_exists_recovered_pair_firstVariation_eq_zero
      (R := R) (a := a) hData q0 ?_
  exact ⟨u, v, hEq, hfirst⟩

/--
Pure-gradient exact slice on the centered open cube from recovery data alone.

The recovered half-pair gives the scalar first variation at `(-p0,0)`; the
deterministic coupling lemma then uses quadratic homogeneity of `ResponseJ` to
return the note-facing slice `ResponseJ(U; p0, 0, a)`.
-/
theorem
    mu_left_zero_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (p0 : Vec d) :
    Mu (openCubeSet (originCube d n)) (p0, 0) a =
      ResponseJ (openCubeSet (originCube d n)) p0 0 a := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  let hEll : IsEllipticFieldOn lam Lam U a := Classical.choose hData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  rcases
      exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_blockVec
        (R := R) (a := a) hData (p0, 0) with
    ⟨u, v, hEq⟩
  let Xrec : BlockState d :=
    (R.toMuCorrectionSpaceRecoveryData).recoveredField system (p0, 0)
  have hAdm : IsBlockMuAdmissible U (p0, 0) Xrec := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system (p0, 0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a (-p0) 0 u w) = 0 := by
    simpa [U, Xrec] using
      scalarFirstVariation_neg_left_zero_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := measurableSet_openCubeSet (originCube d n))
        hEll p0 u v Xrec hEq hAdm
  rcases hData with ⟨_hEllData, hCompat⟩
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (p0, 0) a := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_blockEnergyAverage_eq_mu
        system hCompat.mu_eq_muCandidate (p0, 0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = 0 := by
    have h :=
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_average_pairing_openCubeSet_originCube
        system (p0, 0)
    simpa [U, Xrec, vecDot_zero_right] using h
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = 0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U p0 0 a := by
    simpa [U, Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_left_zero_of_pairingAverage_eq_zero_of_firstVariation_neg_left_zero
        (a := a) hEll p0 u v hPair hfirst
  calc
    Mu (openCubeSet (originCube d n)) (p0, 0) a = Mu U (p0, 0) a := by rfl
    _ = blockEnergyAverage U a Xrec := hEnergyRec.symm
    _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
    _ = ResponseJ U p0 0 a := hCouple
    _ = ResponseJ (openCubeSet (originCube d n)) p0 0 a := by rfl

/--
Full mixed response slice on the centered open cube from recovery data alone.

For the recovered field at block datum `(-p,q)`, the average state-pairing is
`-p·q`. The deterministic half-pair coupling therefore identifies the block
energy with `ResponseJ(U;p,q,a) + p·q`, which is exactly the mixed-term
identity needed for the full response-side block-quadratic package.
-/
theorem
    responseJ_eq_mu_neg_left_sub_vecDot_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (p0 q0 : Vec d) :
    ResponseJ (openCubeSet (originCube d n)) p0 q0 a =
      Mu (openCubeSet (originCube d n)) (-p0, q0) a - vecDot p0 q0 := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let : Fact (MeasureTheory.volume U < ⊤) :=
    ⟨volume_openCubeSet_originCube_lt_top (d := d) n⟩
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n)).isFiniteMeasure_restrict_volume
  let hEll : IsEllipticFieldOn lam Lam U a := Classical.choose hData
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  rcases
      exists_blockResponsePairHalfState_ae_eq_recoveredField_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_blockVec
        (R := R) (a := a) hData (-p0, q0) with
    ⟨u, v, hEq⟩
  let Xrec : BlockState d :=
    (R.toMuCorrectionSpaceRecoveryData).recoveredField system (-p0, q0)
  have hAdm : IsBlockMuAdmissible U (-p0, q0) Xrec := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system (-p0, q0)
  have hfirst :
      ∀ w : AHarmonicFunction a U,
        volumeAverage U (scalarFirstVariationIntegrand U a p0 q0 u w) = 0 := by
    simpa [U, Xrec] using
      scalarFirstVariation_neg_left_right_of_ae_eq_blockResponsePairHalfState_of_isBlockMuAdmissible
        (a := a) (U := U) (hU := measurableSet_openCubeSet (originCube d n))
        hEll (-p0) q0 u v Xrec hEq hAdm
  rcases hData with ⟨_hEllData, hCompat⟩
  have hEnergyRec :
      blockEnergyAverage U a Xrec = Mu U (-p0, q0) a := by
    simpa [U, system, Xrec] using
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_blockEnergyAverage_eq_mu
        system hCompat.mu_eq_muCandidate (-p0, q0)
  let Xpair : BlockState d := blockResponsePairHalfState a u v
  have hEnergyEq :
      blockEnergyAverage U a Xpair = blockEnergyAverage U a Xrec := by
    unfold blockEnergyAverage volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, blockEnergyDensity] using
      congrArg
        (fun z =>
          (1 / 2 : ℝ) * blockVecDot z (blockMatVecMul (blockCoeffField a x) z))
        hx
  have hPairEq :
      volumeAverage U
          (fun x => vecDot (Xpair.potential x) (Xpair.flux x)) =
        volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) := by
    unfold volumeAverage
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hEq] with x hx
    simpa [Xpair, Xrec, BlockState.eval] using
      congrArg (fun z : BlockVec d => vecDot z.1 z.2) hx
  have hPairRec :
      volumeAverage U
          (fun x => vecDot (Xrec.potential x) (Xrec.flux x)) = -vecDot p0 q0 := by
    have h :=
      (R.toMuCorrectionSpaceRecoveryData).recoveredField_average_pairing_openCubeSet_originCube
        system (-p0, q0)
    simpa [U, Xrec, vecDot_neg_left] using h
  have hPair :
      volumeAverage U
          (fun x =>
            vecDot ((blockResponsePairHalfState a u v).potential x)
              ((blockResponsePairHalfState a u v).flux x)) = -vecDot p0 q0 := by
    simpa [Xpair] using hPairEq.trans hPairRec
  have hCouple :
      blockEnergyAverage U a Xpair = ResponseJ U p0 q0 a - (-vecDot p0 q0) := by
    simpa [U, Xpair] using
      blockEnergyAverage_blockResponsePairHalfState_eq_responseJ_sub_pairing_of_pairingAverage_eq_of_firstVariation_eq_zero
        (a := a) hEll p0 q0 u v (-vecDot p0 q0) hPair hfirst
  have hMu :
      Mu U (-p0, q0) a = ResponseJ U p0 q0 a + vecDot p0 q0 := by
    calc
      Mu U (-p0, q0) a = blockEnergyAverage U a Xrec := hEnergyRec.symm
      _ = blockEnergyAverage U a Xpair := hEnergyEq.symm
      _ = ResponseJ U p0 q0 a - (-vecDot p0 q0) := hCouple
      _ = ResponseJ U p0 q0 a + vecDot p0 q0 := by ring
  calc
    ResponseJ (openCubeSet (originCube d n)) p0 q0 a = ResponseJ U p0 q0 a := by rfl
    _ = Mu U (-p0, q0) a - vecDot p0 q0 := by linarith
    _ = Mu (openCubeSet (originCube d n)) (-p0, q0) a - vecDot p0 q0 := by rfl

theorem
    recoveredField_volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_openCubeSet_originCube_of_isEllipticFieldOn
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (q0 p pStar q qStar : Vec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        volumeAverage (openCubeSet (originCube d n))
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
          (1 / 2 : ℝ) *
              volumeAverage (openCubeSet (originCube d n))
                (scalarResponseIntegrand
                  (openCubeSet (originCube d n)) a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage (openCubeSet (originCube d n))
                (scalarResponseIntegrand
                  (openCubeSet (originCube d n)) (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  let hCube : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_openCubeSet (originCube d n)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using hCube.isFiniteMeasure_restrict_volume
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn
      hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 :=
    (volume_openCubeSet_originCube_toReal_pos (d := d) n).ne'
  simpa [U, system] using
    (R.toMuCorrectionSpaceRecoveryData).volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_recoveredField_zero_right_of_isEllipticFieldOn_of_isOpenBoundedConvexDomain
      (a := a) system hCube hEll hvol q0 p pStar q qStar

theorem
    recoveredField_volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
    {d : ℕ} {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    (q0 p pStar q qStar : Vec d) :
    let system :=
      R.toMuOperatorSystemDataOfIsEllipticFieldOn
        (Classical.choose hData)
        (volume_openCubeSet_originCube_toReal_pos (d := d) n)
    ∃ u : AHarmonicFunction a (openCubeSet (originCube d n)),
      ∃ v :
          AHarmonicFunction (Homogenization.adjointCoeffField a)
            (openCubeSet (originCube d n)),
        volumeAverage (openCubeSet (originCube d n))
            (blockResponseIntegrand a (p, q) (qStar, pStar)
              ((R.toMuCorrectionSpaceRecoveryData).recoveredField system (0, q0))) =
          (1 / 2 : ℝ) *
              volumeAverage (openCubeSet (originCube d n))
                (scalarResponseIntegrand
                  (openCubeSet (originCube d n)) a (p - pStar) (qStar - q) u) +
            (1 / 2 : ℝ) *
              volumeAverage (openCubeSet (originCube d n))
                (scalarResponseIntegrand
                  (openCubeSet (originCube d n)) (Homogenization.adjointCoeffField a)
                  (pStar + p) (qStar + q) v) := by
  rcases hData with ⟨hEll, _hCompat⟩
  simpa using
    recoveredField_volumeAverage_blockResponseIntegrand_eq_scalarResponse_sum_openCubeSet_originCube_of_isEllipticFieldOn
      (R := R) (a := a) hEll q0 p pStar q qStar

/--
Exact pure-flux slice equality on the centered open cube, packaged from
deterministic recovery-plus-ellipticity data together with the current
deterministic coarse block/sigma data.
-/
theorem
    mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (q : Vec d) :
    Mu (openCubeSet (originCube d n)) (0, q) a =
      ResponseJ (openCubeSet (originCube d n)) 0 q a := by
  let _ := hA
  let _ := hS
  let _ := hK
  let _ := hSigma
  exact
    mu_zero_right_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      (R := R) (a := a) hData q

/--
Exact pure-gradient slice equality on the centered open cube, packaged from
deterministic recovery-plus-ellipticity data together with the current
deterministic coarse block/sigma data.
-/
theorem
    mu_left_zero_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData_of_isSigmaCoarse
    {d : ℕ} [NeZero d] {n : ℤ}
    (R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)))
    {lam Lam : ℝ} {a : CoeffField d}
    (hData : HasOpenCubeEllipticRecoveryData (d := d) n R (lam := lam) (Lam := Lam) a)
    {sigma sigmaStar kappa : Mat d}
    (hA : IsCoarseBlockMatrix (openCubeSet (originCube d n)) a
      (deterministicCoarseBlockMatrix (openCubeSet (originCube d n)) a))
    (hS : IsSigmaStarCoarse (openCubeSet (originCube d n)) a sigmaStar)
    (hK : IsKappaCoarse (openCubeSet (originCube d n)) a sigmaStar kappa)
    (hSigma : IsSigmaCoarse (openCubeSet (originCube d n)) a sigma sigmaStar kappa)
    (p : Vec d) :
    Mu (openCubeSet (originCube d n)) (p, 0) a =
      ResponseJ (openCubeSet (originCube d n)) p 0 a := by
  let _ := hA
  let _ := hS
  let _ := hK
  let _ := hSigma
  exact
    mu_left_zero_eq_responseJ_zero_openCubeSet_originCube_of_hasOpenCubeEllipticRecoveryData
      (R := R) (a := a) hData p

end Homogenization
