/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualGaussianCoverage
import LeanPool.NavierStokesAndEuler.NavierStokes.LabelSupportPreservation

/-!
# Scalar-clock support of the actual particular solve

This support argument uses the literal complex Volterra solve and the
Gaussian-times-padding cutoff. Clock factors only need to be positive
at each band; no uniform range for the complete clock family is assumed.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.ScalarParticularSupport

open Set Function Filter WeightedClasses
open scoped ContDiff Topology BigOperators

section ScalarParticularSupport

open CommonCoverSolve TorusInverse LinearWaveBounds PeriodizedWaveBounds

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (base : WaveCoefficients ((P × ℝ) × Plane))
    (t : ℕ → TangentData (P × ℝ) ProblemStatement.Space)
    (f : ℕ → (P × ℝ) × Plane → HarmonicCalculus.ComplexVector)
    (g : ℕ → Geometry) (r L rate : ℕ → ℝ)
    (hr : ∀ n, 0 < r n) (hL : ∀ n, 0 < L n) (hc : ∀ n, 0 < rate n)

/-- The literal complex Volterra solve and its separately transported
Gaussian/outer cutoff, without uniform bounds on the clock scalars. -/
noncomputable def scalarData : CopyData ((P × ℝ) × Plane) Frequency :=
  complexCopyData base t f g (fun _ => 0) (fun n => L n / rate n)
    (fun n => (div_pos (hL n) (hc n)).le)
    (fun n => ActualGaussianCoverage.nativeCutoff (r n) (L n) (hr n) (hL n) (rate n))

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem scalarData_amplitude (n : ℕ) (k : Frequency) :
    (scalarData base t f g r L rate hr hL hc).amplitude n k =
      ParticularWaveBounds.complexCopyVelocity (t n) (f n) (g n)
        (div_pos (hL n) (hc n)).le k := rfl

omit [NormedAddCommGroup P] [NormedSpace ℝ P] in
theorem scalarData_pressure (n : ℕ) (k : Frequency) :
    (scalarData base t f g r L rate hr hL hc).pressure n k =
      ParticularWaveBounds.complexCopyPressure (t n) (f n) (g n)
        (div_pos (hL n) (hc n)).le k (base.frequency n) := rfl

variable
    (hinj : ∀ n, InjOn TorusAverages.quotientPoint
      ((fun z => (g n).center + (g n).basis z) ''
        ActualGaussianCoverage.outerCell (r n) (L n) (rate n)))

/-- Scalar cells, constructed using `nativeCells`. -/
noncomputable def scalarCells : Cells ((P × ℝ) × Plane) Frequency :=
  nativeCells g (fun n => ActualGaussianCoverage.outerCell (r n) (L n) (rate n))
    (fun _ => ActualGaussianCoverage.outerCell_compact _ _ _) hinj

omit [NormedSpace ℝ P] in
theorem scalarData_cutoff_support (n : ℕ) (k : Frequency) :
    support ((scalarData base t f g r L rate hr hL hc).cutoff n k) ⊆
      (scalarCells g r L rate hinj).carrier n k :=
  native_cutoff_support (g n)
    (ActualGaussianCoverage.nativeCutoff_support (hr n) (hL n) (hc n)) k

variable (U : Set P) (S : ℕ → Set P)
    (hf : ∀ n (x : (P × ℝ) × Plane), x.1.1 ∈ U →
      (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n) →
      f n =ᶠ[𝓝 x] fun _ => 0)

include hf hinj

/-- Outside the source carrier, each padded native cell has a zero
cutoff or a zero whole-path Volterra solve. -/
theorem scalarData_native_zero_alternative (n : ℕ) (k : Frequency)
    {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ U)
    (hk : x ∈ (scalarCells g r L rate hinj).carrier n k)
    (hn : (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
    ((scalarData base t f g r L rate hr hL hc).cutoff n k =ᶠ[𝓝 x] fun _ => 0) ∨
    (((scalarData base t f g r L rate hr hL hc).amplitude n k =ᶠ[𝓝 x] fun _ => 0) ∧
     ((scalarData base t f g r L rate hr hL hc).pressure n k =ᶠ[𝓝 x] fun _ => 0)) := by
  have hk' : (g n).coordinates k x.2 ∈ ActualGaussianCoverage.outerCell (r n) (L n) (rate n) := hk
  by_cases ht : ((g n).coordinates k x.2).2 ∈ Ioo 0 (L n / rate n)
  · have hzero (hpath : ∀ v ∈ Icc 0 (L n / rate n),
        (x.1.1, (g n).path k x.2 v) ∉
          ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
        ((scalarData base t f g r L rate hr hL hc).amplitude n k =ᶠ[𝓝 x] fun _ => 0) ∧
        ((scalarData base t f g r L rate hr hL hc).pressure n k =ᶠ[𝓝 x] fun _ => 0) := by
      rw [scalarData_amplitude, scalarData_pressure]
      exact ⟨ActualGaussianCoverage.complexCopyVelocity_zero_germ _ _ _ _
        (fun v hv => hf n (x.1, (g n).path k x.2 v) hx (hpath v hv)),
        LabelSupportPreservation.complexCopyPressure_zero_germ _ _ _ _ _ ht
        (fun v hv => hf n (x.1, (g n).path k x.2 v) hx (hpath v hv))⟩
    by_cases hp : x.1.1 ∈ S n
    · by_cases hxi : ((g n).coordinates k x.2).1 ∈ Icc (-(r n)) (r n)
      · left
        have htime : ((g n).coordinates k x.2).2 ∉
            Icc ((L n / rate n) / 6) (5 * (L n / rate n) / 6) := by
          intro hv
          apply hn
          exact ⟨hp, mem_iUnion.mpr ⟨k, hxi, hv⟩⟩
        exact (LabelSupportPreservation.nativeCutoff_source_time_zero_germ
          (hr n) (hL n) (hc n) htime).comp_tendsto
            (((g n).coordinates_contDiff k).continuous.comp continuous_snd).continuousAt
      · right
        apply hzero
        intro v hv hh
        obtain ⟨i, hi⟩ := mem_iUnion.mp hh.2
        exact ActualGaussianCoverage.path_sourceCell_excluded (g n) (hr n) (hL n) (hc n)
          (hinj n) hk' hxi v hv i hi
    · right
      exact hzero (fun _ _ hh => hp hh.1)
  · left
    exact (ActualGaussianCoverage.nativeCutoff_time_zero_germ
      (hr n) (hL n) (hc n) ht).comp_tendsto
        (((g n).coordinates_contDiff k).continuous.comp continuous_snd).continuousAt

theorem scalarData_zero_germs (s : StripData ((P × ℝ) × Plane))
    (d : GraphDirections ((P × ℝ) × Plane)) (n : ℕ)
    {x : (P × ℝ) × Plane} (hx : x.1.1 ∈ U)
    (hn : (x.1.1, x.2) ∉ ActualGaussianCoverage.sourceRegion (S n) (g n) (r n) (L n) (rate n)) :
    let a := scalarData base t f g r L rate hr hL hc
    ((a.commonCorrected s d).amplitude n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.common.pressure n =ᶠ[𝓝 x] fun _ => 0) ∧
    (a.globalGaussian d n =ᶠ[𝓝 x] fun _ => 0) := by
  apply LabelSupportPreservation.common_zero_germs_of_native
    (scalarData base t f g r L rate hr hL hc) (scalarCells g r L rate hinj)
    (scalarData_cutoff_support base t f g r L rate hr hL hc hinj) s d (hf n x hx hn)
  intro k hk
  exact scalarData_native_zero_alternative base t f g r L rate hr hL hc hinj U S hf n k hx hk hn

end ScalarParticularSupport

end NavierStokes.ScalarParticularSupport
