/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.CoarseGraining.BlockMatrixProperties
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.MuOperator.CoeffOperator
import LeanPool.CoarseGraining.Homogenization.CoarseGraining.ResponseIdentities.AverageFormulas
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.AffineAverage
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2OriginCubeBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2Recovery

/-! # Setup -/

namespace Homogenization

noncomputable section

/-!
# Mu recovery -- private volume / bounded-domain helpers and data package

Volume positivity / finite lemmas on origin cubes and the MuMinimizerRecoveryData
structure used as the interface between the Hilbert minimizer map and the
note-faithful linear family.
-/

theorem volume_cubeSet_originCube_lt_top_recovery {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (cubeSet (originCube d n)) < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro htop
  have hzero : (MeasureTheory.volume (cubeSet (originCube d n))).toReal = 0 := by
    simp [htop]
  rw [volume_cubeSet_toReal] at hzero
  exact (ne_of_gt (cubeVolume_pos (originCube d n))) hzero

theorem volume_openCubeSet_originCube_lt_top_recovery {d : ℕ} (n : ℤ) :
    MeasureTheory.volume (openCubeSet (originCube d n)) < ⊤ := by
  exact lt_of_le_of_lt
    (MeasureTheory.measure_mono (openCubeSet_subset_cubeSet (originCube d n)))
    (volume_cubeSet_originCube_lt_top_recovery (d := d) n)

theorem volume_cubeSet_originCube_toReal_pos_recovery {d : ℕ} (n : ℤ) :
    0 < (MeasureTheory.volume (cubeSet (originCube d n))).toReal := by
  rw [volume_cubeSet_toReal]
  exact cubeVolume_pos (originCube d n)

theorem volume_openCubeSet_originCube_toReal_pos_recovery {d : ℕ} (n : ℤ) :
    0 < (MeasureTheory.volume (openCubeSet (originCube d n))).toReal := by
  rw [volume_openCubeSet_toReal]
  exact cubeVolume_pos (originCube d n)

theorem isBoundedDomain_openCubeSet_originCube_recovery {d : ℕ} (n : ℤ) :
    IsBoundedDomain (openCubeSet (originCube d n)) := by
  refine ⟨(1 / 2 : ℝ) * (3 : ℝ) ^ n, ?_, ?_⟩
  · have hpow : 0 < (3 : ℝ) ^ n := by
      exact zpow_pos (by norm_num) _
    nlinarith
  · intro x hx i
    rcases (mem_openCubeSet_originCube_iff.mp hx) i with ⟨hlo, hhi⟩
    refine abs_le.2 ?_
    constructor
    · exact le_of_lt (by simpa [neg_mul] using hlo)
    · exact le_of_lt hhi

theorem isBoundedDomain_cubeSet_originCube_recovery {d : ℕ} (n : ℤ) :
    IsBoundedDomain (cubeSet (originCube d n)) := by
  refine ⟨(1 / 2 : ℝ) * (3 : ℝ) ^ n, ?_, ?_⟩
  · have hpow : 0 < (3 : ℝ) ^ n := by
      exact zpow_pos (by norm_num) _
    nlinarith
  · intro x hx i
    rcases (mem_cubeSet_originCube_iff.mp hx) i with ⟨hlo, hhi⟩
    refine abs_le.2 ?_
    constructor
    · simpa [neg_mul] using hlo
    · exact le_of_lt hhi

theorem isSobolevRegularDomain_openCubeSet_originCube_recovery {d : ℕ} (n : ℤ) :
    IsSobolevRegularDomain (openCubeSet (originCube d n)) :=
  ⟨measurableSet_openCubeSet (originCube d n),
    isBoundedDomain_openCubeSet_originCube_recovery (d := d) n⟩

theorem isSobolevRegularDomain_cubeSet_originCube_recovery {d : ℕ} (n : ℤ) :
    IsSobolevRegularDomain (cubeSet (originCube d n)) :=
  ⟨measurableSet_cubeSet (originCube d n),
    isBoundedDomain_cubeSet_originCube_recovery (d := d) n⟩

/-!
This file isolates the remaining bridge from the Hilbert-space doubled `\mu`
problem back to the note-faithful pointwise minimizer family.

The analytic minimization engine already produces a canonical linear map
`P ↦ X_P` in the ambient Hilbert space `L²(U; \R^{2d})`. To recover the
coarse-grained block matrix `\mathbf A(U; a)` from `\mu(U, \cdot; a)`, the
remaining missing input is a representative-level package asserting that these
Hilbert minimizers come from actual block states with the expected admissibility
and energy identities.
-/

section Recovery

variable {d : ℕ} {U : Set (Vec d)} {a : CoeffField d}
/--
Representative-level recovery data for the Hilbert minimizers of the doubled
`\mu` problem.

This package is intentionally theorem-surface only: it records the exact
pointwise witnesses still needed to convert the Hilbert minimizer map into the
note-faithful linear minimizer family used to prove `\exists \mathbf A(U; a)`.
-/
structure MuMinimizerRecoveryData (U : Set (Vec d)) (a : CoeffField d)
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] where
  /-- The deterministic doubled operator package. -/
  system : MuOperatorSystemData U a
  /-- A pointwise block-state representative of the Hilbert minimizer. -/
  field : BlockVec d → BlockState d
  /-- Linearity in the coarse datum. -/
  map_add : ∀ P Q : BlockVec d, field (P + Q) = field P + field Q
  /-- Homogeneity in the coarse datum. -/
  map_smul : ∀ (c : ℝ) (P : BlockVec d), field (c • P) = c • field P
  /-- Each representative is an actual block `L²` field. -/
  mem_blockL2 : ∀ P : BlockVec d, MemBlockL2 U (field P).eval
  /-- The chosen representative agrees with the Hilbert minimizer in `L²`. -/
  minimizer_eq :
    ∀ P : BlockVec d,
      toHilbertBlockL2OfBlockField (mem_blockL2 P) =
        system.toMuHilbertRealization.minimizerMap P
  /-- The representative is admissible for the note's definition of `\mu`. -/
  admissible : ∀ P : BlockVec d, IsBlockMuAdmissible U P (field P)
  /-- Pairing integrability needed for the quadratic-family API. -/
  pairingIntegrable :
    ∀ P Q : BlockVec d,
      MeasureTheory.IntegrableOn (blockPairingIntegrand a (field P) (field Q)) U
  /-- The note's `\mu` agrees with the Hilbert-space minimized energy. -/
  mu_eq_muCandidate :
    ∀ P : BlockVec d, Mu U P a = system.toMuHilbertRealization.muCandidate P

end Recovery

end

end Homogenization
