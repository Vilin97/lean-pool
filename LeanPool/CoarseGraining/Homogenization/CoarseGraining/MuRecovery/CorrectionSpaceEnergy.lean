/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuRecovery.CorrectionSpaceSolenoidal
public import Mathlib.Topology.Bases

/-! # Correction Space Energy -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Mu correction-space recovery -- block-energy and mu lower bound

recoveredField_blockEnergyAverage_eq_mu plus its >= vecDot variants
(general, openCubeSet, cubeSet) and the mu_ge_vecDot theorems on origin
cubes.
-/

namespace MuCorrectionSpaceRecoveryData

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

theorem quadraticEnergy_const_add_eq_blockEnergyAverage_affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    quadraticEnergy
        (energyBilinOfOperator system.toMuOperatorRealization.operator)
        (blockVecToHilbertBlockL2Const (U := U) P + Y) =
      blockEnergyAverage U a (R.affineField P Y) := by
  rw [← R.affineField_hilbert_eq_const_add P Y]
  exact
    system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
      (X := R.affineField P Y)
      (hX := R.affineField_memBlockL2 P Y)

theorem muCandidate_le_blockEnergyAverage_affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d)
    (Y : R.correctionSpace.toSubmodule) :
    (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate P ≤
      blockEnergyAverage U a (R.affineField P Y) := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  have hY :
      blockVecToHilbertBlockL2Const (U := U) P + Y - H.constantField P ∈
        H.correctionSpace.correctionSpace := by
    have hY' : (Y : HilbertBlockL2 U) ∈ H.correctionSpace.correctionSpace := Y.property
    have hconst : H.constantField P = blockVecToHilbertBlockL2Const (U := U) P := rfl
    have hsum :
        blockVecToHilbertBlockL2Const (U := U) P + (Y : HilbertBlockL2 U) - H.constantField P =
          (Y : HilbertBlockL2 U) := by
      rw [hconst]
      abel
    rw [hsum]
    exact hY'
  have hMin :
      H.muCandidate P ≤
        quadraticEnergy
          (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (blockVecToHilbertBlockL2Const (U := U) P + Y) := by
    simpa [H] using! H.muCandidate_le_quadraticEnergy P
      (blockVecToHilbertBlockL2Const (U := U) P + Y) hY
  calc
    H.muCandidate P ≤
        quadraticEnergy
          (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (blockVecToHilbertBlockL2Const (U := U) P + Y) := hMin
    _ = blockEnergyAverage U a (R.affineField P Y) :=
      R.quadraticEnergy_const_add_eq_blockEnergyAverage_affineField system P Y

theorem blockEnergyAverage_affineField_correctionPart_eq_muCandidate
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    blockEnergyAverage U a (R.affineField P (R.correctionPart system P)) =
      (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate P := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  rw [R.affineField_correctionPart system P]
  calc
    blockEnergyAverage U a (R.recoveredField system P)
      =
        quadraticEnergy
          (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (toHilbertBlockL2OfBlockField (U := U) (R.recoveredField_memBlockL2 system P)) := by
            symm
            exact
              system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
                (X := R.recoveredField system P)
                (hX := R.recoveredField_memBlockL2 system P)
    _ = quadraticEnergy H.energyBilin (H.minimizerMap P) := by
          rw [R.recoveredField_minimizer_eq system P]
          rfl
    _ = H.muCandidate P := by
          rfl

theorem muCandidate_eq_sInf_blockEnergyAverage_affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate P =
      sInf (Set.range
        (fun Y : R.correctionSpace.toSubmodule => blockEnergyAverage U a (R.affineField P Y))) := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  let s : Set ℝ := Set.range
    (fun Y : R.correctionSpace.toSubmodule => blockEnergyAverage U a (R.affineField P Y))
  have hs_nonempty : s.Nonempty := by
    refine ⟨blockEnergyAverage U a (R.affineField P (R.correctionPart system P)), ?_⟩
    exact ⟨R.correctionPart system P, rfl⟩
  have h_lower : ∀ m ∈ s, H.muCandidate P ≤ m := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    simpa [H] using R.muCandidate_le_blockEnergyAverage_affineField system P Y
  have hs_bddBelow : BddBelow s := ⟨H.muCandidate P, h_lower⟩
  apply le_antisymm
  · exact le_csInf hs_nonempty h_lower
  · calc
      sInf s ≤ blockEnergyAverage U a (R.affineField P (R.correctionPart system P)) := by
        exact csInf_le hs_bddBelow ⟨R.correctionPart system P, rfl⟩
      _ = H.muCandidate P := by
            simpa [H] using R.blockEnergyAverage_affineField_correctionPart_eq_muCandidate system P

theorem continuous_blockEnergyAverage_affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    Continuous fun Y : R.correctionSpace.toSubmodule =>
      blockEnergyAverage U a (R.affineField P Y) := by
  let f : R.correctionSpace.toSubmodule → ℝ := fun Y =>
    quadraticEnergy
      (energyBilinOfOperator system.toMuOperatorRealization.operator)
      (blockVecToHilbertBlockL2Const (U := U) P + Y)
  have hf : Continuous f := by
    apply (quadraticEnergy_continuous
      (energyBilinOfOperator system.toMuOperatorRealization.operator)).comp
    simpa [f] using! (continuous_const.add continuous_subtype_val)
  convert hf using 1
  funext Y
  exact (R.quadraticEnergy_const_add_eq_blockEnergyAverage_affineField system P Y).symm

theorem muCandidate_eq_sInf_blockEnergyAverage_affineField_denseSeq
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate P =
      sInf (Set.range
        (fun n : ℕ =>
          blockEnergyAverage U a
            (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)))) := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  let f : ↥R.correctionSpace → ℝ := fun Y =>
    blockEnergyAverage U a (R.affineField P Y)
  let s : Set ℝ := Set.range
    (fun n : ℕ => f (TopologicalSpace.denseSeq ↥R.correctionSpace n))
  let t : Set ℝ := Set.range f
  have hs_nonempty : s.Nonempty := by
    refine ⟨f (TopologicalSpace.denseSeq ↥R.correctionSpace 0), ?_⟩
    exact ⟨0, rfl⟩
  have hs_subset : s ⊆ t := by
    rintro x ⟨n, rfl⟩
    exact ⟨TopologicalSpace.denseSeq ↥R.correctionSpace n, rfl⟩
  have h_dense :
      Dense (Set.range (TopologicalSpace.denseSeq ↥R.correctionSpace)) := by
    rw [dense_iff_closure_eq]
    exact (TopologicalSpace.denseRange_denseSeq ↥R.correctionSpace).closure_range
  have h_image_eq :
      f '' Set.range (TopologicalSpace.denseSeq ↥R.correctionSpace) = s := by
    ext x
    constructor
    · rintro ⟨Y, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨TopologicalSpace.denseSeq ↥R.correctionSpace n, ⟨n, rfl⟩, rfl⟩
  have ht_subset_closure : t ⊆ closure s := by
    rw [← h_image_eq]
    simpa [f, t] using!
      (R.continuous_blockEnergyAverage_affineField system P).range_subset_closure_image_dense h_dense
  have ht_nonempty : t.Nonempty := by
    refine ⟨f (R.correctionPart system P), ?_⟩
    exact ⟨R.correctionPart system P, rfl⟩
  have h_lower : ∀ m ∈ t, H.muCandidate P ≤ m := by
    intro m hm
    rcases hm with ⟨Y, rfl⟩
    simpa [H, f] using R.muCandidate_le_blockEnergyAverage_affineField system P Y
  have ht_bddBelow : BddBelow t := ⟨H.muCandidate P, h_lower⟩
  have ht_isGLB : IsGLB t (H.muCandidate P) := by
    rw [R.muCandidate_eq_sInf_blockEnergyAverage_affineField system P]
    exact isGLB_csInf ht_nonempty ht_bddBelow
  have hs_isGLB : IsGLB s (H.muCandidate P) :=
    (isGLB_iff_of_subset_of_subset_closure hs_subset ht_subset_closure).2 ht_isGLB
  symm
  exact hs_isGLB.csInf_eq hs_nonempty

theorem muCandidate_eq_iInf_blockEnergyAverage_affineField_denseSeq
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : MuOperatorSystemData U a)
    (P : BlockVec d) :
    (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate P =
      ⨅ n : ℕ,
        blockEnergyAverage U a
          (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) := by
  rw [R.muCandidate_eq_sInf_blockEnergyAverage_affineField_denseSeq system P, sInf_range]

theorem Mu_eq_sInf_blockEnergyAverage_affineField_denseSeq
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    Mu U P a =
      sInf (Set.range
        (fun n : ℕ =>
          blockEnergyAverage U a
            (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)))) := by
  rw [mu_eq_muCandidate P]
  exact R.muCandidate_eq_sInf_blockEnergyAverage_affineField_denseSeq system P

theorem Mu_eq_iInf_blockEnergyAverage_affineField_denseSeq
    (R : MuCorrectionSpaceRecoveryData U)
    [TopologicalSpace.SeparableSpace ↥R.correctionSpace]
    (system : MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    Mu U P a =
      ⨅ n : ℕ,
        blockEnergyAverage U a
          (R.affineField P (TopologicalSpace.denseSeq ↥R.correctionSpace n)) := by
  rw [R.Mu_eq_sInf_blockEnergyAverage_affineField_denseSeq system mu_eq_muCandidate P, sInf_range]

theorem Mu_eq_sInf_blockEnergyAverage_affineField
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    Mu U P a =
      sInf (Set.range
        (fun Y : R.correctionSpace.toSubmodule => blockEnergyAverage U a (R.affineField P Y))) := by
  rw [mu_eq_muCandidate P]
  exact R.muCandidate_eq_sInf_blockEnergyAverage_affineField system P

theorem recoveredField_blockEnergyAverage_eq_mu
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    blockEnergyAverage U a (R.recoveredField system P) = Mu U P a := by
  let H : MuHilbertRealization U a :=
    system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData
  symm
  calc
    Mu U P a = H.muCandidate P :=
      mu_eq_muCandidate P
    _ = quadraticEnergy
          (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (H.minimizerMap P) := by
          rfl
    _ = quadraticEnergy
          (energyBilinOfOperator system.toMuOperatorRealization.operator)
          (toHilbertBlockL2OfBlockField (R.recoveredField_memBlockL2 system P)) := by
          rw [← R.recoveredField_minimizer_eq system P]
    _ = blockEnergyAverage U a (R.recoveredField system P) := by
          exact system.toMuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState
            (X := R.recoveredField system P)
            (hX := R.recoveredField_memBlockL2 system P)

theorem recoveredField_blockEnergyAverage_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q)) U)
    (pairingDiagIntegrable :
      ∀ P : BlockVec d,
        MeasureTheory.IntegrableOn
          (fun x => vecDot ((R.recoveredField system P).potential x)
            ((R.recoveredField system P).flux x)) U)
    (pairingAverage :
      ∀ P : BlockVec d,
        volumeAverage U
          (fun x => vecDot ((R.recoveredField system P).potential x)
            ((R.recoveredField system P).flux x)) =
          vecDot P.1 P.2)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ blockEnergyAverage U a (R.recoveredField system P) := by
  let X : BlockState d := R.recoveredField system P
  have hEnergyInt : MeasureTheory.IntegrableOn (blockEnergyDensity a X) U := by
    have hself := pairingIntegrable P P
    have hEq :
        blockEnergyDensity a X =
          fun x => (1 / 2 : ℝ) * blockPairingIntegrand a X X x := by
      funext x
      simp [blockEnergyDensity, blockPairingIntegrand]
    rw [hEq]
    simpa [MeasureTheory.IntegrableOn, smul_eq_mul] using hself.integrable.const_mul (1 / 2 : ℝ)
  have hPairInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (X.potential x) (X.flux x)) U :=
    pairingDiagIntegrable P
  have hnonneg :
      0 ≤ volumeAverage U
        (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) := by
    unfold volumeAverage
    refine mul_nonneg ?_ ?_
    · exact inv_nonneg.mpr ENNReal.toReal_nonneg
    · apply MeasureTheory.integral_nonneg_of_ae
      exact (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx =>
          sub_nonneg.mpr (blockEnergyDensity_ge_vecDot_of_isEllipticFieldOn hEll X hx))
  have hdiff :
      volumeAverage U
          (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) =
        blockEnergyAverage U a X - vecDot P.1 P.2 := by
    calc
      volumeAverage U
          (fun x => blockEnergyDensity a X x - vecDot (X.potential x) (X.flux x)) =
        volumeAverage U (blockEnergyDensity a X) -
          volumeAverage U (fun x => vecDot (X.potential x) (X.flux x)) := by
            unfold volumeAverage
            rw [MeasureTheory.integral_sub hEnergyInt hPairInt]
            ring
      _ = blockEnergyAverage U a X - vecDot P.1 P.2 := by
            rw [pairingAverage P]
            simp [blockEnergyAverage]
  rw [hdiff] at hnonneg
  linarith

theorem mu_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q)) U)
    (pairingDiagIntegrable :
      ∀ P : BlockVec d,
        MeasureTheory.IntegrableOn
          (fun x => vecDot ((R.recoveredField system P).potential x)
            ((R.recoveredField system P).flux x)) U)
    (pairingAverage :
      ∀ P : BlockVec d,
        volumeAverage U
          (fun x => vecDot ((R.recoveredField system P).potential x)
            ((R.recoveredField system P).flux x)) =
          vecDot P.1 P.2)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu U P a := by
  calc
    vecDot P.1 P.2 ≤ blockEnergyAverage U a (R.recoveredField system P) :=
      R.recoveredField_blockEnergyAverage_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
        system hEll pairingIntegrable pairingDiagIntegrable pairingAverage P
    _ = Mu U P a :=
      R.recoveredField_blockEnergyAverage_eq_mu system mu_eq_muCandidate P

theorem mu_ge_vecDot_of_isEllipticFieldOn_of_integral_eq_zero
    (R : MuCorrectionSpaceRecoveryData U)
    (system : MuOperatorSystemData U a)
    {lam Lam : ℝ} (hEll : IsEllipticFieldOn lam Lam U a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q)) U)
    (hpotZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).potential x i
          ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      ∀ P : BlockVec d,
        (fun i => ∫ x in U, (R.recoveredCorrectionField system P).flux x i
          ∂MeasureTheory.volume) = 0)
    (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu U P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu U P a := by
  simpa using
    R.mu_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
      system hEll pairingIntegrable
      (R.recoveredField_integrableOn_pairing_of_integral_eq_zero system)
      (R.recoveredField_average_pairing_of_integral_eq_zero system hpotZero hfluxZero hvol)
      mu_eq_muCandidate P

theorem recoveredField_blockEnergyAverage_ge_vecDot_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (openCubeSet (originCube d n)))
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤
      blockEnergyAverage (openCubeSet (originCube d n)) a (R.recoveredField system P) := by
  simpa using
    R.recoveredField_blockEnergyAverage_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
      system hEll pairingIntegrable
      (fun P =>
        R.recoveredField_integrableOn_pairing_openCubeSet_originCube system P)
      (fun P =>
        R.recoveredField_average_pairing_openCubeSet_originCube system P)
      P

theorem recoveredField_blockEnergyAverage_ge_vecDot_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (cubeSet (originCube d n)))
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤
      blockEnergyAverage (cubeSet (originCube d n)) a (R.recoveredField system P) := by
  simpa using
    R.recoveredField_blockEnergyAverage_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
      system hEll pairingIntegrable
      (fun P =>
        R.recoveredField_integrableOn_pairing_cubeSet_originCube system P)
      (fun P =>
        R.recoveredField_average_pairing_cubeSet_originCube system P)
      P

theorem mu_ge_vecDot_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (openCubeSet (originCube d n)))
    (system : MuOperatorSystemData (openCubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (openCubeSet (originCube d n)))
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu (openCubeSet (originCube d n)) P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu (openCubeSet (originCube d n)) P a := by
  simpa using
    R.mu_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
      system hEll pairingIntegrable
      (fun P =>
        R.recoveredField_integrableOn_pairing_openCubeSet_originCube system P)
      (fun P =>
        R.recoveredField_average_pairing_openCubeSet_originCube system P)
      mu_eq_muCandidate P

theorem mu_ge_vecDot_cubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (R : MuCorrectionSpaceRecoveryData (cubeSet (originCube d n)))
    (system : MuOperatorSystemData (cubeSet (originCube d n)) a)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet (originCube d n)) a)
    (pairingIntegrable :
      ∀ P Q : BlockVec d,
        MeasureTheory.IntegrableOn
          (blockPairingIntegrand a
            (R.recoveredField system P)
            (R.recoveredField system Q))
          (cubeSet (originCube d n)))
    (mu_eq_muCandidate :
      ∀ P : BlockVec d,
        Mu (cubeSet (originCube d n)) P a =
          (system.toMuOperatorRealization.toMuHilbertRealization R.toMuCorrectionSpaceData).muCandidate
            P)
    (P : BlockVec d) :
    vecDot P.1 P.2 ≤ Mu (cubeSet (originCube d n)) P a := by
  simpa using
    R.mu_ge_vecDot_of_isEllipticFieldOn_of_pairingAverage
      system hEll pairingIntegrable
      (fun P =>
        R.recoveredField_integrableOn_pairing_cubeSet_originCube system P)
      (fun P =>
        R.recoveredField_average_pairing_cubeSet_originCube system P)
      mu_eq_muCandidate P


end MuCorrectionSpaceRecoveryData

end

end Homogenization
