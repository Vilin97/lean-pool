/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Continuity.PathModulus
import LeanPool.MarkovProcess.MarkovProcess.Main
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.AllTimeMarginals

/-!
# The continuous-path process as a Kolmogorov process, and its uniform modulus

The intrinsic moment criterion `HasKolmogorovMoments p q M` is a statement about the transition
kernels.  This file transports it to the continuous-path process itself, at *all* nonnegative
real times and with the very same constants: the coordinate process of `continuousProcess P hP x`
is a Kolmogorov process with exponents `p`, `q` and constant `M`, for every starting point `x`.
Rational times come from the identification of the dense-time projection of the process with the
dense-time trajectory; irrational times follow by path continuity and Fatou's lemma, so no Feller
hypothesis and no local compactness are needed.

Combining this with the quantitative chaining estimate of `Continuity/PathModulus.lean` gives the
modulus statement that tightness on path space consumes: for a horizon `T`, an oscillation
tolerance `r` and a mass tolerance `eps` there is one scale `delta > 0` that works simultaneously
at every starting point.

Main results:

* `IsConservative.map_denseRestriction_continuousProcess`, the dense-time projection of the
  process;
* `IsConservative.isKolmogorovProcess_continuousProcess`, the moment bound at all real times;
* `IsConservative.exists_measure_compl_modulusSet_le`, the modulus estimate uniform in the
  starting point.

No tightness, weak continuity, or Hölder-path statement is proved here.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace MarkovProcess

namespace SubMarkovKernelSemigroup

noncomputable section

open IsConservative

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)

/-- The dense-time projection of the continuous-path process is the canonical dense-time
trajectory of `P`. -/
theorem IsConservative.map_denseRestriction_continuousProcess (hK : P.KolmogorovRegular hP) :
    (continuousProcess P hP).map ContinuousPath.denseRestriction =
      denseTimeTrajectory P hP DenseTime.enumeration
        DenseTime.castOrderEmbedding.toEmbedding := by
  unfold IsConservative.continuousProcess IsConservative.continuousPathTrajectory
  exact Kernel.map_denseRestriction_toContinuousPathKernel_of_isKolmogorovCoordinate _ _ hK

/-- The Kolmogorov increment bound for the continuous-path process at rational times. -/
theorem IsConservative.lintegral_edist_continuousProcess_denseTime
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP)
    (x : alpha) (r r' : DenseTime) :
    ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding r))
          (omega (DenseTime.castOrderEmbedding r')) ^ p ∂(continuousProcess P hP x) ≤
      (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding r)
        (DenseTime.castOrderEmbedding r') ^ q := by
  have hcoord : Measurable
      (fun path : DenseTime → alpha ↦ edist (path r) (path r') ^ p) :=
    ((measurable_pi_apply r).edist (measurable_pi_apply r')).pow_const p
  have hmap := congrArg (fun kappa : Kernel alpha (DenseTime → alpha) ↦ kappa x)
    (IsConservative.map_denseRestriction_continuousProcess P hP hK)
  simp only [Kernel.map_apply _ ContinuousPath.measurable_denseRestriction] at hmap
  calc ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding r))
          (omega (DenseTime.castOrderEmbedding r')) ^ p ∂(continuousProcess P hP x)
      = ∫⁻ path, edist (path r) (path r') ^ p
          ∂(((continuousProcess P hP) x).map ContinuousPath.denseRestriction) :=
        (lintegral_map hcoord ContinuousPath.measurable_denseRestriction).symm
    _ = ∫⁻ path, edist (path r) (path r') ^ p
          ∂(denseTimeTrajectory P hP DenseTime.enumeration
            DenseTime.castOrderEmbedding.toEmbedding x) := by rw [hmap]
    _ ≤ (M : ℝ≥0∞) * edist r r' ^ q :=
        (IsConservative.isKolmogorovProcess_denseTimeTrajectory P hP hmom x).kolmogorovCondition
          r r'
    _ = (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding r)
          (DenseTime.castOrderEmbedding r') ^ q := by
        rw [DenseTime.edist_castOrderEmbedding]

/-- **The continuous-path process is a Kolmogorov process with the semigroup's own constants.**
For a conservative Kolmogorov-regular semigroup satisfying the intrinsic moment bound
`HasKolmogorovMoments p q M`, the coordinate process of `continuousProcess P hP x` satisfies the
Kolmogorov increment condition at all pairs of nonnegative real times, with the exponents and the
constant of that bound and uniformly in the starting point `x`.

Rational times are read off the dense-time trajectory; the passage to arbitrary real times uses
only path continuity and Fatou's lemma, so neither the Feller property nor local compactness of
the state space is used. -/
theorem IsConservative.isKolmogorovProcess_continuousProcess
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (hK : P.KolmogorovRegular hP)
    (x : alpha) :
    IsKolmogorovProcess (fun (t : ℝ≥0) (omega : ContinuousPath alpha) ↦ omega t)
      (continuousProcess P hP x) p q M := by
  have hcont : ∀ a b : ℝ≥0,
      Continuous fun omega : ContinuousPath alpha ↦ edist (omega a) (omega b) ^ p := fun a b ↦
    ENNReal.continuous_rpow_const.comp
      ((ContinuousPath.continuous_eval (alpha := alpha) a).edist (ContinuousPath.continuous_eval b))
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun t ↦ ContinuousPath.measurable_coordinateProcess (alpha := alpha) t) ?_ hmom.p_pos
    hmom.q_pos
  intro s t
  obtain ⟨rs, hrs⟩ := exists_denseTime_seq_tendsto s
  obtain ⟨rt, hrt⟩ := exists_denseTime_seq_tendsto t
  have hptwise : ∀ omega : ContinuousPath alpha,
      Tendsto (fun n ↦ edist (omega (DenseTime.castOrderEmbedding (rs n)))
          (omega (DenseTime.castOrderEmbedding (rt n))) ^ p) atTop
        (nhds (edist (omega s) (omega t) ^ p)) := by
    intro omega
    refine ENNReal.continuous_rpow_const.continuousAt.tendsto.comp (Tendsto.edist ?_ ?_)
    · exact (omega.continuous.tendsto s).comp hrs
    · exact (omega.continuous.tendsto t).comp hrt
  have hbound : ∀ n : ℕ, ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding (rs n)))
        (omega (DenseTime.castOrderEmbedding (rt n))) ^ p ∂(continuousProcess P hP x) ≤
      (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding (rs n))
        (DenseTime.castOrderEmbedding (rt n)) ^ q := fun n ↦
    IsConservative.lintegral_edist_continuousProcess_denseTime P hP hmom hK x (rs n) (rt n)
  have hlimit : Tendsto (fun n ↦ (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding (rs n))
      (DenseTime.castOrderEmbedding (rt n)) ^ q) atTop
      (nhds ((M : ℝ≥0∞) * edist s t ^ q)) :=
    ENNReal.Tendsto.const_mul
      (ENNReal.continuous_rpow_const.continuousAt.tendsto.comp (Tendsto.edist hrs hrt))
      (Or.inr ENNReal.coe_ne_top)
  calc ∫⁻ omega, edist (omega s) (omega t) ^ p ∂(continuousProcess P hP x)
      = ∫⁻ omega, liminf (fun n ↦ edist (omega (DenseTime.castOrderEmbedding (rs n)))
          (omega (DenseTime.castOrderEmbedding (rt n))) ^ p) atTop
          ∂(continuousProcess P hP x) := by
        exact lintegral_congr fun omega ↦ ((hptwise omega).liminf_eq).symm
    _ ≤ liminf (fun n ↦ ∫⁻ omega, edist (omega (DenseTime.castOrderEmbedding (rs n)))
          (omega (DenseTime.castOrderEmbedding (rt n))) ^ p ∂(continuousProcess P hP x))
          atTop :=
        lintegral_liminf_le fun n ↦ (hcont _ _).measurable
    _ ≤ liminf (fun n ↦ (M : ℝ≥0∞) * edist (DenseTime.castOrderEmbedding (rs n))
          (DenseTime.castOrderEmbedding (rt n)) ^ q) atTop :=
        liminf_le_liminf (Eventually.of_forall hbound)
    _ = (M : ℝ≥0∞) * edist s t ^ q := hlimit.liminf_eq

/-- **A modulus of continuity uniform in the starting point.**  For a conservative semigroup
satisfying the intrinsic Kolmogorov moment bound, fix a horizon `T`, an oscillation tolerance
`r > 0` and a mass tolerance `eps > 0`.  Then there is a single scale `delta > 0` such that, from
*every* starting point, the process gives mass at most `eps` to the paths that oscillate by more
than `r` at scale `delta` on `[0, T]`.

This is the quantitative form of the Kolmogorov--Chentsov estimate: the constants produced by the
dyadic chaining depend only on `p`, `q`, `M`, the Hölder exponent and the displayed tolerances,
never on the starting point. -/
theorem IsConservative.exists_measure_compl_modulusSet_le
    {p q : ℝ} {M : ℝ≥0} (hmom : P.HasKolmogorovMoments p q M) (T : ℝ≥0) {r : ℝ≥0∞} (hr : 0 < r)
    {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ delta : ℝ≥0∞, 0 < delta ∧ ∀ x : alpha,
      continuousProcess P hP x (ContinuousPath.modulusSet T delta r)ᶜ ≤ eps := by
  obtain ⟨gamma, hgamma, hgammaq⟩ := hmom.exists_holderExponent
  obtain ⟨delta, hdelta, hmu⟩ :=
    ContinuousPath.exists_measure_compl_modulusSet_le (alpha := alpha) (M := M) hmom.p_pos hgamma
      hgammaq T hr heps
  refine ⟨delta, hdelta, fun x ↦ hmu _ ?_⟩
  exact IsConservative.isKolmogorovProcess_continuousProcess P hP hmom
    (KolmogorovRegular.of_hasKolmogorovMoments P hP hmom) x

end

end SubMarkovKernelSemigroup

end MarkovProcess
