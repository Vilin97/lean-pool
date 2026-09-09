/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage

@[expose] public section

/-!
# Jets of the literal transported native cutoff

The product consists of the padded reference window and the separate Gaussian
slot cutoff. On the analytic patch the window equals one on an ambient
neighborhood, including at the closed transverse endpoints. Its exact germ
therefore transfers the Gaussian clock estimates without assumptions about a
source, correction state, or modal-control output.
-/

noncomputable section

namespace NavierStokes.NativeCutoffJets

open Set Function Filter WeightedClasses
open CommonCoverSolve TorusInverse PrimaryPulseBounds PeriodizedWaveBounds
open scoped Topology ContDiff

variable {Label P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {D : PhaseJetBounds.Domain (Label × ℕ) PhaseCalculus.Slow}
  (F : PhaseConstruction D) (clock : ActualSignedControl.PositiveScale Label)
  (g : Label → ℕ → Geometry)
  (r : Label → ℕ → ℝ) (hr : ∀ l n, 0 < r l n)

/-- The literal cutoff, before placing it in any particular-solve record. -/
noncomputable def literalCutoff (l : Label) (n : ℕ) (k : Frequency)
    (x : P × Plane) : ℝ :=
  (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2)) *
    GaussianTailFlat.slotCutoff (F.L (l,n))
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2)).2

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem literalCutoff_eq_referenceTransport (l : Label) (n : ℕ) (k : Frequency) :
    literalCutoff (P := P) F clock g r hr l n k =
      fun x => ActualGaussianCoverage.referenceCutoff (r l n) (F.L (l,n))
        (hr l n) (F.L_pos (l,n))
          (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
            ((g l n).coordinates k x.2)) := rfl

variable (s : StripData P) (χ : P →L[ℝ] PhaseCalculus.Slow)
  (φ : (Label × ℕ) → PhaseCalculus.Slow →L[ℝ] PhaseCalculus.Slow)

/-- Patch membership supplies the actual closed-core hypothesis of the
reference window's neighborhood theorem. -/
theorem nativeTime_mem_core (l : Label) (n : ℕ) (k : Frequency) {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k x.2) ∈
      (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
        (hr l n) (F.L_pos (l,n))).core := by
  change ((g l n).coordinates k x.2).1 ∈ Icc (-(r l n)) (r l n) ∧
    0 + clock.value l n * ((g l n).coordinates k x.2).2 ∈ Icc 0 (F.L (l,n))
  simp only [zero_add]
  exact And.intro hx.2 (ScaledActualParticularControl.clock_mem F clock
      ⟨hx.1.2.2.1.le, hx.1.2.2.2.le⟩)

/-- This is an ambient germ, obtained from the padded window's exact
cutoff_germ theorem rather than from its value at the boundary point. -/
theorem literalCutoff_gaussian_germ (l : Label) (n : ℕ) (k : Frequency)
    {x : P × Plane}
    (hx : x ∈ ScaledActualParticularControl.patch s F χ φ clock g r l n k) :
    literalCutoff F clock g r hr l n k =ᶠ[𝓝 x]
      fun y => GaussianTailFlat.profile
        (ActualGaussianCoverage.theta F clock l n ((g l n).coordinates k y.2).2) := by
  have hm := nativeTime_mem_core F clock g r hr s χ φ l n k hx
  have hc : Continuous (fun y : P × Plane =>
      CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k y.2)) :=
    (CopySolveCompatibility.nativeTimeMap_continuous _ _).comp
      (((g l n).coordinates_contDiff k).continuous.comp continuous_snd)
  have he := ((ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff_germ hm).comp_tendsto hc.continuousAt
  filter_upwards [he] with y hy
  dsimp only [Function.comp_def] at hy
  change (ActualGaussianCoverage.referenceWindow (r l n) (F.L (l,n))
    (hr l n) (F.L_pos (l,n))).cutoff
      (CopySolveCompatibility.nativeTimeMap 0 (clock.value l n)
        ((g l n).coordinates k y.2)) * _ = _
  rw [hy, one_mul]
  simp only [GaussianTailFlat.slotCutoff, CopySolveCompatibility.nativeTimeMap,
    ActualGaussianCoverage.theta, zero_add]

/-- All finite jets are uniform in the label, band, and lifted copy. The
only quantitative input beyond the primitive phase and clock is the
polynomial bound for the actual affine geometry. -/
theorem literalCutoff_uniformLocalJets {u0 : ℝ}
    (hu0 : 0 < u0) (hu : ∀ l n, F.u (l,n) = u0)
    (hcost : ∃ K : ℝ, 1 ≤ K ∧ ∃ p : ℕ, ∀ l n,
      CommonCoverClass.argumentCost (g l n) ≤ K * s.slow n ^ p) :
    UniformLocalJets (CommonCoverClass.sourceStrip s) (fun _ _ _ => 1) 0
      (ScaledActualParticularControl.patch s F χ φ clock g r)
      (literalCutoff F clock g r hr) := by
  have hj := ActualGaussianCoverage.gaussian_clock_uniform_jets F clock
    (CommonCoverClass.sourceStrip s)
    (ScaledActualParticularControl.patch s F χ φ clock g r) g hu0 hu hcost
  apply ActualSignedControl.uniform_local_congr hj
  intro l n k x _ hx
  exact (literalCutoff_gaussian_germ F clock g r hr s χ φ l n k hx).symm

end NavierStokes.NativeCutoffJets
