/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage1E03.Proof
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.Proof
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage4AboveTwoFinalTrial.Proof
import LeanPool.ParameterFreeGradient.V7.Proofs.Stage2Resume.Closure

/-!
# Stage 8: current local-trial runtime dispatch

The selectors in this file are made before a positive instance is supplied.
They depend only on public runtime data and the cached exact observation.
-/

namespace V7.Stage8Main

/-- A below-two local trial selected from the proved existence theorem. -/
noncomputable def belowTrialFor (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) : LocalTrial d :=
  Classical.choose (V7.belowTrial p hp hp2 d eps M D heps hM hD x0 cached)

theorem belowTrialFor_spec (p : ℝ) (hp : 1 < p) (hp2 : p < 2)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) :
    ∀ inst : PositiveInstance p d x0,
      cached.observation = inst.oracle.observe x0 →
      eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0) →
      D ≥ lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M →
      ∃ (report : TrialReport d) (w : BelowTrialWitness p d),
        (belowTrialFor p hp hp2 eps M D heps hM hD x0 cached).Executes
          M D cached inst.oracle report ∧
        TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
        BelowTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
        (report.calls : ℝ) ≤
          4 * Real.sqrt (M * D / ((p - 1) * eps)) + 2 ∧
        (report.calls : ℝ) ≤
          (4 / Real.sqrt (p - 1) + 2) * Real.sqrt (M * D / eps) :=
  Classical.choose_spec (V7.belowTrial p hp hp2 d eps M D heps hM hD x0 cached)

/-- The universal query-bound constant selected for the Euclidean local trial. -/
noncomputable def euclideanConstant : ℝ := Classical.choose V7.euclideanTrial

theorem euclideanConstant_pos : 0 < euclideanConstant :=
  (Classical.choose_spec V7.euclideanTrial).1

private theorem euclideanTrial_exists (eps M D : ℝ)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) :
    ∃ (m n : ℕ) (trial : LocalTrial d),
      m = Nat.ceil (2 * Real.sqrt (M * D / eps)) ∧ n = m ∧
      ∀ inst : PositiveInstance 2 d x0,
      cached.observation = inst.oracle.observe x0 →
      eps < lpNorm 2 (inst.oracle.gradient x0) →
      D ≥ lpNorm 2 (inst.oracle.gradient x0) / M →
      ∃ (report : TrialReport d)
        (phaseA : EuclideanGapData d m) (phaseB : OGMGData d n),
        trial.Executes M D cached inst.oracle report ∧
        TrialCertificate eps 2 M D inst.L inst.R cached inst.oracle report ∧
        EuclideanTrialOperationalContract x0 M D inst report phaseA phaseB ∧
        report.calls ≤ 2 * m + n + 1 ∧
        (report.calls : ℝ) ≤ euclideanConstant * Real.sqrt (M * D / eps) :=
  (Classical.choose_spec V7.euclideanTrial).2 d eps M D heps hM hD x0 cached

/-- The selected horizon of the Euclidean gap-reduction phase. -/
noncomputable def euclideanM (eps M D : ℝ)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) : ℕ :=
  Classical.choose (euclideanTrial_exists eps M D heps hM hD x0 cached)

/-- The selected horizon of the Euclidean OGM-G phase. -/
noncomputable def euclideanN (eps M D : ℝ)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) : ℕ :=
  Classical.choose (Classical.choose_spec
    (euclideanTrial_exists eps M D heps hM hD x0 cached))

/-- A Euclidean local trial selected with its certified two-phase horizons. -/
noncomputable def euclideanTrialFor (eps M D : ℝ)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) : LocalTrial d :=
  Classical.choose (Classical.choose_spec (Classical.choose_spec
    (euclideanTrial_exists eps M D heps hM hD x0 cached)))

theorem euclideanTrialFor_spec (eps M D : ℝ)
    (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) :
    euclideanM eps M D heps hM hD x0 cached =
        Nat.ceil (2 * Real.sqrt (M * D / eps)) ∧
      euclideanN eps M D heps hM hD x0 cached =
        euclideanM eps M D heps hM hD x0 cached ∧
      ∀ inst : PositiveInstance 2 d x0,
      cached.observation = inst.oracle.observe x0 →
      eps < lpNorm 2 (inst.oracle.gradient x0) →
      D ≥ lpNorm 2 (inst.oracle.gradient x0) / M →
      ∃ (report : TrialReport d)
        (phaseA : EuclideanGapData d
          (euclideanM eps M D heps hM hD x0 cached))
        (phaseB : OGMGData d
          (euclideanN eps M D heps hM hD x0 cached)),
        (euclideanTrialFor eps M D heps hM hD x0 cached).Executes
          M D cached inst.oracle report ∧
        TrialCertificate eps 2 M D inst.L inst.R cached inst.oracle report ∧
        EuclideanTrialOperationalContract x0 M D inst report phaseA phaseB ∧
        report.calls ≤
          2 * euclideanM eps M D heps hM hD x0 cached +
            euclideanN eps M D heps hM hD x0 cached + 1 ∧
        (report.calls : ℝ) ≤ euclideanConstant * Real.sqrt (M * D / eps) :=
  ⟨(Classical.choose_spec
      (euclideanTrial_exists eps M D heps hM hD x0 cached)).choose_spec.choose_spec.1,
    (Classical.choose_spec
      (euclideanTrial_exists eps M D heps hM hD x0 cached)).choose_spec.choose_spec.2.1,
    (Classical.choose_spec
      (euclideanTrial_exists eps M D heps hM hD x0 cached)).choose_spec.choose_spec.2.2⟩

/-- The exponent-dependent query-bound constant for an above-two local trial. -/
noncomputable def aboveConstant (p : ℝ) (hp : 2 < p) : ℝ :=
  Classical.choose (V7.aboveTrial p hp)

theorem aboveConstant_pos (p : ℝ) (hp : 2 < p) :
    0 < aboveConstant p hp :=
  (Classical.choose_spec (V7.aboveTrial p hp)).1

private theorem aboveTrial_exists (p : ℝ) (hp : 2 < p)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) :
    ∃ trial : LocalTrial d,
      ∀ inst : PositiveInstance p d x0,
      cached.observation = inst.oracle.observe x0 →
      eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0) →
      D ≥ lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M →
      ∃ (report : TrialReport d) (w : AboveTrialWitness p d),
        trial.Executes M D cached inst.oracle report ∧
        TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
        AboveTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
        (report.calls : ℝ) ≤
          aboveConstant p hp * (M * D / eps) ^ (p / (p + 2)) :=
  (Classical.choose_spec (V7.aboveTrial p hp)).2 d eps M D heps hM hD x0 cached

/-- An above-two local trial selected from the proved existence theorem. -/
noncomputable def aboveTrialFor (p : ℝ) (hp : 2 < p)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) : LocalTrial d :=
  Classical.choose (aboveTrial_exists p hp eps M D heps hM hD x0 cached)

theorem aboveTrialFor_spec (p : ℝ) (hp : 2 < p)
    (eps M D : ℝ) (heps : 0 < eps) (hM : 0 < M) (hD : 0 < D)
    (x0 : Point d) (cached : CachedPair d) :
    ∀ inst : PositiveInstance p d x0,
      cached.observation = inst.oracle.observe x0 →
      eps < lpNorm (conjugateExponent p) (inst.oracle.gradient x0) →
      D ≥ lpNorm (conjugateExponent p) (inst.oracle.gradient x0) / M →
      ∃ (report : TrialReport d) (w : AboveTrialWitness p d),
        (aboveTrialFor p hp eps M D heps hM hD x0 cached).Executes
          M D cached inst.oracle report ∧
        TrialCertificate eps p M D inst.L inst.R cached inst.oracle report ∧
        AboveTrialOperationalContract p eps M D x0 cached inst.oracle report w ∧
        (report.calls : ℝ) ≤
          aboveConstant p hp * (M * D / eps) ^ (p / (p + 2)) :=
  Classical.choose_spec (aboveTrial_exists p hp eps M D heps hM hD x0 cached)

end V7.Stage8Main
