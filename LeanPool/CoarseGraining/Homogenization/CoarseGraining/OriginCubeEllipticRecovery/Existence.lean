/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.OriginCubeEllipticRecovery.Setup
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Realization

/-!
# Origin-cube elliptic recovery -- uniform existence hypothesis

Formulates OpenCubeOriginEllipticRecoveryExistence, carries the long translate-
coefficient-field ellipticity helper, and derives origin-cube recovery data
from a potentialZeroTraceClosureRealization input under IsEllipticFieldOn.
-/

namespace Homogenization


/--
Uniform origin-cube recovery existence for elliptic coefficient fields.

This is the remaining upstream existence hypothesis needed to remove the
explicit descendant-family burden from the public deterministic coarse
Poincare theorems. Once this is available, the descendant family is produced
automatically by translation.
-/
def OpenCubeOriginEllipticRecoveryExistence {d : ℕ} (lam Lam : ℝ) : Prop :=
  ∀ (n : ℤ) (a : CoeffField d),
    IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a →
      ∃ R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)),
        HasOpenCubeEllipticRecoveryData (d := d) n R
          (lam := lam) (Lam := Lam) a

/--
Reduce origin-cube recovery existence to the single hard compatibility field
`Mu = muCandidate`.

After `muRecoveryCompatibilityData_of_isEllipticFieldOn_of_mu_eq_muCandidate`,
the pairing-integrability side of `HasOpenCubeEllipticRecoveryData` is
automatic. So the genuine remaining upstream task is exactly to produce a
representative-level recovery package whose Hilbert minimizer value agrees
with `Mu`.
-/
theorem
    openCubeOriginEllipticRecoveryExistence_of_exists_recoveryData_of_mu_eq_muCandidate
    {d : ℕ} {lam Lam : ℝ}
    (hMu :
      ∀ (n : ℤ) (a : CoeffField d),
        ∀ hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a,
          ∃ R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)),
            ∀ P : BlockVec d,
              Mu (openCubeSet (originCube d n)) P a =
                ((R.toMuHilbertRealization
                  (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
                    (volume_openCubeSet_originCube_toReal_pos (d := d) n))).muCandidate P)) :
    OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam := by
  intro n a hEll
  rcases hMu n a hEll with ⟨R, hmu⟩
  refine ⟨R, ?_⟩
  exact
    hasOpenCubeEllipticRecoveryData_of_isEllipticFieldOn_of_mu_eq_muCandidate
      (d := d) n R hEll hmu

private theorem isEllipticFieldOn_translateCoeffField_of_translateSet
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d} (z : Vec d)
    (hEll : IsEllipticFieldOn lam Lam (translateSet z U) a) :
    IsEllipticFieldOn lam Lam U (translateCoeffField z a) := by
  classical
  refine ⟨?_, ?_⟩
  · have hshift : Measurable (fun x : Vec d => x + z) :=
      (continuous_id.add continuous_const).measurable
    have hcomp :
        Measurable (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) :=
      hEll.1.comp hshift
    have hEq :
        (fun x i j => if x + z ∈ translateSet z U then a (x + z) i j else 0) =
          (fun x i j => if x ∈ U then translateCoeffField z a x i j else 0) := by
      funext x i j
      have hadd_sub : x + z - z = x := by
        ext k
        simp [sub_eq_add_neg, add_assoc]
      by_cases hx : x ∈ U
      · have hxt : x + z ∈ translateSet z U := by
          rw [mem_translateSet_iff_sub_mem, hadd_sub]
          exact hx
        simp [hx, hxt]
        rfl
      · have hxt : x + z ∉ translateSet z U := by
          intro hmem
          rw [mem_translateSet_iff_sub_mem] at hmem
          rw [hadd_sub] at hmem
          exact hx hmem
        simp [hx, hxt]
    simpa [hEq] using hcomp
  · intro x hx
    have hxt : x + z ∈ translateSet z U := by
      have hadd_sub : x + z - z = x := by
        ext k
        simp [sub_eq_add_neg, add_assoc]
      rw [mem_translateSet_iff_sub_mem, hadd_sub]
      exact hx
    exact hEll.2 (x + z) hxt

/--
Reduce the descendant recovery-family burden for coarse Poincare to one
origin-cube existence theorem.

This is the first cleanup bridge toward removing
`OpenCubeDescendantEllipticRecoveryFamily` from the public cube-level
Poincare theorems: once recovery existence is proved on each origin open cube,
this theorem automatically produces the descendant family needed downstream.
-/
theorem
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_of_originCubeRecoveryExistence
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) := by
  intro l hl R hR
  let z : Vec d := fun i => (R.index i : ℝ) * cubeScaleFactor R
  have hsub : openCubeSet R ⊆ cubeSet Q := by
    intro x hx
    exact cubeSet_subset_of_mem_descendantsAtScale hl hR (openCubeSet_subset_cubeSet _ hx)
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (isOpen_openCubeSet R).measurableSet hsub
  have hEllOrigin :
      IsEllipticFieldOn lam Lam (openCubeSet (originCube d R.scale))
        (translateCoeffField z a) := by
    have htranslate :
        IsEllipticFieldOn lam Lam
          (translateSet z (openCubeSet (originCube d R.scale))) a := by
      simpa [z, openCubeSet_eq_translateSet_originCube_of_triadicCube R] using! hEllR
    exact isEllipticFieldOn_translateCoeffField_of_translateSet
      (U := openCubeSet (originCube d R.scale)) (a := a) z htranslate
  simpa [z] using hOrigin R.scale (translateCoeffField z a) hEllOrigin

/--
Open-cube variant of the descendant recovery-family constructor.

This is the a.e.-ellipticity-facing form used downstream in Chapter 5: the law
data gives ellipticity on the open target cube almost surely, and every open
descendant lies inside that open target cube.
-/
theorem
    openCubeDescendantEllipticRecoveryFamily_of_isEllipticFieldOn_openCubeSet_of_originCubeRecoveryExistence
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam) :
    OpenCubeDescendantEllipticRecoveryFamily Q a (lam := lam) (Lam := Lam) := by
  intro l hl R hR
  let z : Vec d := fun i => (R.index i : ℝ) * cubeScaleFactor R
  have hsub : openCubeSet R ⊆ openCubeSet Q :=
    openCubeSet_subset_of_mem_descendantsAtScale hl hR
  have hEllR : IsEllipticFieldOn lam Lam (openCubeSet R) a :=
    hEll.mono (isOpen_openCubeSet R).measurableSet hsub
  have hEllOrigin :
      IsEllipticFieldOn lam Lam (openCubeSet (originCube d R.scale))
        (translateCoeffField z a) := by
    have htranslate :
        IsEllipticFieldOn lam Lam
          (translateSet z (openCubeSet (originCube d R.scale))) a := by
      simpa [z, openCubeSet_eq_translateSet_originCube_of_triadicCube R] using! hEllR
    exact isEllipticFieldOn_translateCoeffField_of_translateSet
      (U := openCubeSet (originCube d R.scale)) (a := a) z htranslate
  simpa [z] using hOrigin R.scale (translateCoeffField z a) hEllOrigin

/--
On the centered open cube, the canonical closure-based recovery package
realizes the Hilbert minimizer value `muCandidate`, provided we can upgrade
closed potential-zero-trace membership to honest zero-trace representatives.

This isolates the remaining upstream Sobolev burden behind the exact closed
zero-trace potential realization needed by the recovery construction, rather
than the more opaque packaged assumption `OpenCubeOriginEllipticRecoveryExistence`.
-/
theorem
    exists_recoveryData_of_mu_eq_muCandidate_openCubeSet_originCube_of_isEllipticFieldOn_of_potentialZeroTraceClosureRealization
    {d : ℕ} (n : ℤ) {lam Lam : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (hRealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
        (openCubeSet (originCube d n))) :
    ∃ R : PotentialSolenoidalL2RecoveryData (openCubeSet (originCube d n)),
      ∀ P : BlockVec d,
        Mu (openCubeSet (originCube d n)) P a =
          ((R.toMuHilbertRealization
            (R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
              (volume_openCubeSet_originCube_toReal_pos (d := d) n))).muCandidate P) := by
  let U : Set (Vec d) := openCubeSet (originCube d n)
  have hCube : IsOpenBoundedConvexDomain U := by
    simpa [U] using isOpenBoundedConvexDomain_openCubeSet (originCube d n)
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn, U] using hCube.isFiniteMeasure_restrict_volume
  let R : PotentialSolenoidalL2RecoveryData U :=
    potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
      (U := U) hRealize
  have hvol : (MeasureTheory.volume U).toReal ≠ 0 :=
    (volume_openCubeSet_originCube_toReal_pos (d := d) n).ne'
  let system : MuOperatorSystemData U a :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
      (volume_openCubeSet_originCube_toReal_pos (d := d) n)
  refine ⟨R, ?_⟩
  intro P
  have hCandidateLe :
      ∀ X : BlockState d, IsBlockMuAdmissible U P X →
        (R.toMuHilbertRealization system).muCandidate P ≤ blockEnergyAverage U a X := by
    intro X hX
    let Y : CorrectionFieldData U := hX.toCorrectionFieldDataOfAdmissible
    have hXmemBlock : MemBlockL2 U X.eval := hX.memBlockL2_eval
    have hpot : MemVectorL2 U X.potential := by
      simpa [BlockState.eval] using memVectorL2_fst_of_memBlockL2 (U := U) hXmemBlock
    have hflux : MemVectorL2 U X.flux := by
      simpa [BlockState.eval] using memVectorL2_snd_of_memBlockL2 (U := U) hXmemBlock
    have hcorr :
        Y.toHilbertBlockL2 ∈ R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.correctionSpace := by
      exact
        R.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData.mem_correctionSpace
          Y.potential_memL2 Y.flux_memL2 Y.isPotentialZeroTrace Y.isSolenoidalZeroNormalTrace
    have hconst_add :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock =
          blockVecToHilbertBlockL2Const (U := U) P + Y.toHilbertBlockL2 := by
      simpa [Y] using hX.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add
    have hcorr_mem :
        toHilbertBlockL2OfBlockField (U := U) hXmemBlock -
            (R.toMuHilbertRealization system).constantField P ∈
          (R.toMuHilbertRealization system).correctionSpace.correctionSpace := by
      rw [hconst_add]
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hcorr
    have hMin :
        (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := by
      simpa [R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization,
        MuOperatorSystemData.toMuHilbertRealization,
        MuOperatorRealization.toMuHilbertRealization, MuHilbertRealization.ofOperator] using
        (R.toMuHilbertRealization system).muCandidate_le_quadraticEnergy P
          (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) hcorr_mem
    calc
      (R.toMuHilbertRealization system).muCandidate P ≤
          quadraticEnergy
            (energyBilinOfOperator system.toMuOperatorRealization.operator)
            (toHilbertBlockL2OfBlockField (U := U) hXmemBlock) := hMin
      _ = blockEnergyAverage U a X := by
            exact
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := X) hXmemBlock
  have hrecEnergy :
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P) =
        (R.toMuHilbertRealization system).muCandidate P := by
    let H : MuHilbertRealization U a := R.toMuHilbertRealization system
    have hminim :
        toHilbertBlockL2OfBlockField (U := U)
            ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P) =
          H.minimizerMap P := by
      simpa [H, R, system, PotentialSolenoidalL2RecoveryData.toMuHilbertRealization] using!
        (R.toMuCorrectionSpaceRecoveryData).recoveredField_minimizer_eq system P
    calc
      blockEnergyAverage U a ((R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
          = quadraticEnergy
              (energyBilinOfOperator system.toMuOperatorRealization.operator)
              (toHilbertBlockL2OfBlockField (U := U)
                ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)) := by
                symm
                exact
                  system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                    (X := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P)
                    ((R.toMuCorrectionSpaceRecoveryData).recoveredField_memBlockL2 system P)
      _ = quadraticEnergy H.energyBilin (H.minimizerMap P) := by
            rw [hminim]
            rfl
      _ = H.muCandidate P := by
            rfl
      _ = (R.toMuHilbertRealization system).muCandidate P := by
            rfl
  have hBddBelow : BddBelow (muValueSet U P a) := by
    refine ⟨vecDot P.1 P.2, ?_⟩
    intro m hm
    rcases hm with ⟨X, hX, rfl⟩
    exact
      hX.blockEnergyAverage_ge_vecDot_of_integral_eq_zero_of_isEllipticFieldOn
        (a := a)
        (hX.toBlockMuIntegrabilityDataOfIsEllipticFieldOn (a := a) hEll)
        hEll
        (by
          simpa [sub_eq_add_neg] using
            (IsPotentialZeroTraceOn.integral_eq_zero hX.isPotentialZeroTrace))
        (by
          simpa [sub_eq_add_neg] using
            (IsSolenoidalZeroNormalTraceOn.integral_eq_zero hCube.isSobolevRegularDomain
              hX.isSolenoidalZeroNormalTrace))
        hvol
  have hUpper :
      Mu U P a ≤ (R.toMuHilbertRealization system).muCandidate P := by
    let Xrec : BlockState d := (R.toMuCorrectionSpaceRecoveryData).recoveredField system P
    have hAdm : IsBlockMuAdmissible U P Xrec := by
      simpa [Xrec] using (R.toMuCorrectionSpaceRecoveryData).recoveredField_admissible system P
    calc
      Mu U P a ≤ blockEnergyAverage U a Xrec := by
        exact csInf_le hBddBelow (muValueSet_mem hAdm)
      _ = (R.toMuHilbertRealization system).muCandidate P := hrecEnergy
  have hLower :
      (R.toMuHilbertRealization system).muCandidate P ≤ Mu U P a := by
    apply le_Mu_of_forall_isBlockMuAdmissible
    intro X hX
    exact hCandidateLe X hX
  exact le_antisymm hUpper hLower

/--
Origin-cube zero-trace potential closure realization.

This is the remaining Sobolev/closed-range input needed by the origin-cube
elliptic recovery theorem: every vector field in the closed zero-trace
potential subspace on a centered open cube has an actual `H¹₀` potential.
-/
def OpenCubePotentialZeroTraceClosureRealization (d : ℕ) : Prop :=
  ∀ n : ℤ,
    PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization
      (openCubeSet (originCube d n))

/--
The packaged origin-cube recovery existence hypothesis follows from the
explicit zero-trace potential closure-realization theorem on each centered
open cube.

This re-expresses the remaining Chapter 3 cleanup burden in the precise
Sobolev language: once the canonical closed zero-trace potential space is known
to have actual `H¹₀` representatives on origin cubes, the public coarse
Poincare theorem surface no longer needs to mention
`OpenCubeOriginEllipticRecoveryExistence` as an independent package.
-/
theorem openCubeOriginEllipticRecoveryExistence_of_potentialZeroTraceClosureRealization
    {d : ℕ} {lam Lam : ℝ}
    (hRealize : OpenCubePotentialZeroTraceClosureRealization d) :
    OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam := by
  apply openCubeOriginEllipticRecoveryExistence_of_exists_recoveryData_of_mu_eq_muCandidate
  intro n a hEll
  exact
    exists_recoveryData_of_mu_eq_muCandidate_openCubeSet_originCube_of_isEllipticFieldOn_of_potentialZeroTraceClosureRealization
      (d := d) n hEll (hRealize n)

/--
The origin-cube zero-trace potential closure realization hypothesis is a
theorem on every positive dimension, discharged by
`PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain`.
-/
theorem openCubePotentialZeroTraceClosureRealization
    {d : ℕ} [NeZero d] : OpenCubePotentialZeroTraceClosureRealization d :=
  fun n =>
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
      (isOpenBoundedConvexDomain_openCubeSet (originCube d n))

/-- Unconditional origin-cube elliptic recovery existence on every positive
dimension. -/
theorem openCubeOriginEllipticRecoveryExistence
    {d : ℕ} [NeZero d] {lam Lam : ℝ} :
    OpenCubeOriginEllipticRecoveryExistence (d := d) lam Lam :=
  openCubeOriginEllipticRecoveryExistence_of_potentialZeroTraceClosureRealization
    openCubePotentialZeroTraceClosureRealization

end Homogenization
