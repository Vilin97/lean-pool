/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.SpacetimeEndpoint
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Endpoint limits from actual joint jets and local one-sided extensions

The input is an actual function, smooth on `t < 1`. Its full Frechet jets
vanish jointly at `(1,0)`, and it has an actual smooth local extension near
each other point of the terminal slice. The boundary tensor family and its
local uniform convergence are constructed below.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.JointResidualLimits

open Set Filter
open scoped Topology ContDiff

/-- Space: an abbreviation for `ProblemStatement.Space`. -/
abbrev Space := ProblemStatement.Space
/-- Space time: an abbreviation for `ProblemStatement.SpaceTime`. -/
abbrev SpaceTime := ProblemStatement.SpaceTime

section JointTopology

variable {ι X V : Type*} [TopologicalSpace X] [PseudoMetricSpace V]
  {p : Filter ι} [p.NeBot] {F : ι × X → V} {L : X → V}

/-- Joint convergence to boundary values forces continuity of those values.
No continuity or local-uniform convergence of the boundary map is assumed. -/
theorem continuous_of_joint_limits
    (hlim : ∀ x, Tendsto F (p ×ˢ 𝓝 x) (𝓝 (L x))) : Continuous L := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hh : {q : ι × X | dist (F q) (L x) < ε / 2} ∈ p ×ˢ 𝓝 x :=
    (hlim x).eventually (Metric.ball_mem_nhds (L x) (half_pos hε))
  obtain ⟨U, hU, W, hW, hUW⟩ := Filter.mem_prod_iff.mp hh
  filter_upwards [hW] with y hy
  have hpoint : Tendsto (fun i => F (i, y)) p (𝓝 (L y)) :=
    (hlim y).comp (tendsto_id.prodMk tendsto_const_nhds)
  have hnear : ∀ᶠ i in p, dist (F (i, y)) (L y) < ε / 2 :=
    hpoint.eventually (Metric.ball_mem_nhds (L y) (half_pos hε))
  have hU' : ∀ᶠ i in p, i ∈ U := hU
  obtain ⟨i, hiU, hi⟩ := (hU'.and hnear).exists
  have hix : dist (F (i, y)) (L x) < ε / 2 := hUW ⟨hiU, hy⟩
  calc
    dist (L y) (L x) ≤ dist (L y) (F (i, y)) + dist (F (i, y)) (L x) :=
      dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (by simpa only [dist_comm] using hi) hix
    _ = ε := by ring

/-- Reverse joint-to-local-uniform implication, using the uniform-space
characterization of local uniform convergence. -/
theorem locallyUniform_of_joint_limits
    (hlim : ∀ x, Tendsto F (p ×ˢ 𝓝 x) (𝓝 (L x))) :
    TendstoLocallyUniformly (fun i x => F (i, x)) L p := by
  apply tendstoLocallyUniformly_iff_forall_tendsto.mpr
  intro x
  have hL : Tendsto (fun q : ι × X => L q.2) (p ×ˢ 𝓝 x) (𝓝 (L x)) :=
    ((continuous_of_joint_limits hlim).tendsto x).comp tendsto_snd
  exact (tendsto_right_nhds_uniformity.comp hL).uniformity_trans
    (tendsto_left_nhds_uniformity.comp (hlim x))

end JointTopology

section ActualJets

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A genuine smooth extension on a neighborhood, agreeing with the original
function on the portion of that neighborhood with `t < 1`. -/
structure OneSidedExtension (f : SpaceTime → V) (x : Space) where
  /-- Value of `OneSidedExtension`, of type `SpaceTime → V`. -/
  value : SpaceTime → V
  /-- Domain of `OneSidedExtension`, of type `Set SpaceTime`. -/
  domain : Set SpaceTime
  isOpen : IsOpen domain
  mem : (1, x) ∈ domain
  smooth : ContDiffOn ℝ ∞ value domain
  agrees : EqOn value f (domain ∩ SpacetimeEndpoint.openPast 1)

/-- Away extensions, given by `∀ x : Space, x ≠ 0 → Nonempty (OneSidedExtension f x)`. -/
def AwayExtensions (f : SpaceTime → V) : Prop :=
  ∀ x : Space, x ≠ 0 → Nonempty (OneSidedExtension f x)

/-- Vanishing joint jets, given by `∀ n : ℕ, Tendsto (iteratedFDeriv ℝ n f)
(𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))) (𝓝 0)`. -/
def VanishingJointJets (f : SpaceTime → V) : Prop :=
  ∀ n : ℕ, Tendsto (iteratedFDeriv ℝ n f)
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), (0 : Space))) (𝓝 0)

theorem past_filter (x : Space) :
    𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), x) = (𝓝[<] (1 : ℝ)) ×ˢ 𝓝 x := by
  simp only [SpacetimeEndpoint.openPast, nhdsWithin_prod_eq, nhdsWithin_univ]

theorem OneSidedExtension.eventuallyEq {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) :
    f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)] e.value := by
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (e.isOpen.mem_nhds e.mem)] with z hz he
  exact (e.agrees ⟨he, hz⟩).symm

/-- Local agreement on the open past gives agreement of every actual jet. -/
theorem OneSidedExtension.jets_eventuallyEq {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) (n : ℕ) :
    iteratedFDeriv ℝ n f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)]
      iteratedFDeriv ℝ n e.value := by
  have he := e.eventuallyEq.iteratedFDerivWithin (𝕜 := ℝ) n
  filter_upwards [he, self_mem_nhdsWithin] with z hz hp
  simpa only [iteratedFDerivWithin_of_isOpen n (SpacetimeEndpoint.openPast_isOpen 1) hp] using hz

theorem OneSidedExtension.jet_tendsto {f : SpaceTime → V} {x : Space}
    (e : OneSidedExtension f x) (n : ℕ) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (iteratedFDeriv ℝ n e.value (1, x))) := by
  have hg : ContDiffAt ℝ ∞ e.value (1, x) := e.smooth.contDiffAt (e.isOpen.mem_nhds e.mem)
  have hj : ContDiffAt ℝ 0 (iteratedFDeriv ℝ n e.value) (1, x) :=
    hg.iteratedFDeriv_right (by exact_mod_cast (le_top : 0 + (n : ℕ∞) ≤ ⊤))
  exact (hj.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
    (e.jets_eventuallyEq n).symm

/-- One family of tensors, selected from actual extensions away from zero.
At the origin each tensor is explicitly zero. -/
noncomputable def boundaryLimits (f : SpaceTime → V) (hext : AwayExtensions f)
    (x : Space) : FormalMultilinearSeries ℝ SpaceTime V := by
  classical
  exact if hx : x = 0 then 0 else
    ftaylorSeries ℝ (Classical.choice (hext x hx)).value (1, x)

@[simp] theorem boundaryLimits_zero (f : SpaceTime → V) (hext : AwayExtensions f) (n : ℕ) :
    boundaryLimits f hext 0 n = 0 := by
  simp [boundaryLimits]

theorem boundaryLimits_joint {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) (x : Space) :
    Tendsto (iteratedFDeriv ℝ n f) (𝓝[SpacetimeEndpoint.openPast 1] (1, x))
      (𝓝 (boundaryLimits f hext x n)) := by
  classical
  by_cases hx : x = 0
  · subst x
    simpa only [boundaryLimits_zero] using hzero n
  · simp only [boundaryLimits, dite_eq_right hx]
    exact (Classical.choice (hext x hx)).jet_tendsto n

theorem boundaryLimits_continuous {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) : Continuous (fun x => boundaryLimits f hext x n) := by
  apply continuous_of_joint_limits (p := 𝓝[<] (1 : ℝ))
    (F := iteratedFDeriv ℝ n f)
  intro x
  simpa only [past_filter] using boundaryLimits_joint hzero hext n x

theorem boundaryLimits_locallyUniform {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) :
    TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n f (t, x))
      (fun x => boundaryLimits f hext x n) (𝓝[<] (1 : ℝ)) := by
  apply locallyUniform_of_joint_limits (F := iteratedFDeriv ℝ n f)
  intro x
  simpa only [past_filter] using boundaryLimits_joint hzero hext n x

theorem boundaryLimits_uniformOn_compact {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) (n : ℕ) {K : Set Space} (hK : IsCompact K) :
    TendstoUniformlyOn (fun t x => iteratedFDeriv ℝ n f (t, x))
      (fun x => boundaryLimits f hext x n) (𝓝[<] (1 : ℝ)) K :=
  (tendstoLocallyUniformly_iff_forall_isCompact.mp (boundaryLimits_locallyUniform hzero hext n)) K
      hK

theorem past_filter_neBot (x : Space) :
    (𝓝[SpacetimeEndpoint.openPast 1] ((1 : ℝ), x)).NeBot := by
  rw [past_filter]
  infer_instance

/-- The chosen tensors agree with every actual local extension, so they do
not depend on the choice used to construct the family. -/
theorem boundaryLimits_eq_extension {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (hext : AwayExtensions f) {x : Space} (e : OneSidedExtension f x) (n : ℕ) :
    boundaryLimits f hext x n = iteratedFDeriv ℝ n e.value (1, x) := by
  let := past_filter_neBot x
  exact tendsto_nhds_unique (boundaryLimits_joint hzero hext n x) (e.jet_tendsto n)

theorem boundaryLimits_independent {f : SpaceTime → V} (hzero : VanishingJointJets f)
    (h₁ h₂ : AwayExtensions f) : boundaryLimits f h₁ = boundaryLimits f h₂ := by
  funext x n
  let := past_filter_neBot x
  exact tendsto_nhds_unique (boundaryLimits_joint hzero h₁ n x) (boundaryLimits_joint hzero h₂ n x)

theorem iteratedFDeriv_eqOn_past {f g : SpaceTime → V}
    (h : EqOn f g (SpacetimeEndpoint.openPast 1)) (n : ℕ) :
    EqOn (iteratedFDeriv ℝ n f) (iteratedFDeriv ℝ n g) (SpacetimeEndpoint.openPast 1) := by
  intro z hz
  rw [← iteratedFDerivWithin_of_isOpen n (SpacetimeEndpoint.openPast_isOpen 1) hz,
    ← iteratedFDerivWithin_of_isOpen n (SpacetimeEndpoint.openPast_isOpen 1) hz]
  exact iteratedFDerivWithin_congr h hz n

/-- Values at and after time one, including an arbitrary zero extension,
do not change the boundary family when the past functions agree. -/
theorem boundaryLimits_eq_of_eqOn_past {f g : SpaceTime → V}
    (hf : VanishingJointJets f) (hg : VanishingJointJets g)
    (ef : AwayExtensions f) (eg : AwayExtensions g)
    (h : EqOn f g (SpacetimeEndpoint.openPast 1)) :
    boundaryLimits f ef = boundaryLimits g eg := by
  funext x n
  let := past_filter_neBot x
  have hjet : iteratedFDeriv ℝ n f =ᶠ[𝓝[SpacetimeEndpoint.openPast 1] (1, x)]
      iteratedFDeriv ℝ n g := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact iteratedFDeriv_eqOn_past h n hy
  exact tendsto_nhds_unique ((boundaryLimits_joint hf ef n x).congr' hjet)
    (boundaryLimits_joint hg eg n x)

/-- Actual derivative recurrence on the open past; the jet family is not
independent input data. -/
theorem actual_derivative_recurrence {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1)) (n : ℕ) (z : SpaceTime)
    (hz : z.1 < 1) :
    HasFDerivAt (iteratedFDeriv ℝ n f)
      (iteratedFDeriv ℝ (n + 1) f z).curryLeft z := by
  have hs : ContDiffAt ℝ ∞ f z := hf.contDiffAt
    ((SpacetimeEndpoint.openPast_isOpen 1).mem_nhds ⟨hz, mem_univ z.2⟩)
  have hi : ContDiffAt ℝ 1 (iteratedFDeriv ℝ n f) z :=
    hs.iteratedFDeriv_right (by exact_mod_cast (le_top : 1 + (n : ℕ∞) ≤ ⊤))
  have hd := (hi.differentiableAt (by simp)).hasFDerivAt
  rw [fderiv_iteratedFDeriv] at hd
  exact hd

theorem boundaryLimits_smooth {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) (n : ℕ) :
    ContDiff ℝ ∞ (fun x => boundaryLimits f hext x n) :=
  SpacetimeEndpoint.boundary_tensors_contDiff (J := ftaylorSeries ℝ f)
    (actual_derivative_recurrence hf) (boundaryLimits_locallyUniform hzero hext) n

theorem extendedJets_compatible {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) (n : ℕ)
    (z : SpaceTime) (hz : z ∈ SpacetimeEndpoint.closedPast 1) :
    HasFDerivWithinAt
      (fun y => SpacetimeEndpoint.extendJets 1 (ftaylorSeries ℝ f) (boundaryLimits f hext) y n)
      (SpacetimeEndpoint.extendJets 1 (ftaylorSeries ℝ f) (boundaryLimits f hext) z (n +
          1)).curryLeft
      (SpacetimeEndpoint.closedPast 1) z :=
  SpacetimeEndpoint.extendedJets_hasFDerivWithinAt (J := ftaylorSeries ℝ f)
    (actual_derivative_recurrence hf) (boundaryLimits_locallyUniform hzero hext) n z hz

/-- Spatial differentiation of a boundary tensor is restriction of the next
full spacetime tensor to a spatial first argument. -/
theorem boundaryLimits_hasFDerivAt {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) (n : ℕ) (x : Space) :
    HasFDerivAt (fun y => boundaryLimits f hext y n)
      ((boundaryLimits f hext x (n + 1)).curryLeft.comp (ContinuousLinearMap.inr ℝ ℝ Space)) x := by
  have hd := extendedJets_compatible hf hzero hext n (1, x) ⟨le_refl (1 : ℝ), mem_univ x⟩
  have hi : HasFDerivAt (fun y : Space => ((1 : ℝ), y))
      (ContinuousLinearMap.inr ℝ ℝ Space) x :=
    (hasFDerivAt_const (1 : ℝ) x).prodMk (hasFDerivAt_id x)
  have hc := hd.comp x (hi.hasFDerivWithinAt (s := univ))
    (fun y _ => show ((1 : ℝ), y) ∈ SpacetimeEndpoint.closedPast 1 from
      ⟨le_refl (1 : ℝ), mem_univ y⟩)
  simpa only [Function.comp_def, SpacetimeEndpoint.extendJets, SpacetimeEndpoint.extendTrace_at]
    using hc.hasFDerivAt_of_univ

/-- On `t < 1` this is the original function; on `t ≥ 1` this auxiliary
closed-side extension is constant in time with the constructed boundary trace. -/
noncomputable def extendedResidual (f : SpaceTime → V) (hext : AwayExtensions f) : SpaceTime → V :=
  SpacetimeEndpoint.extendTrace 1 f (fun x => (boundaryLimits f hext x 0).curry0)

theorem extendedResidual_agrees (f : SpaceTime → V) (hext : AwayExtensions f) :
    EqOn (extendedResidual f hext) f (SpacetimeEndpoint.openPast 1) :=
  fun _ hz => SpacetimeEndpoint.extendTrace_of_lt hz.1

theorem extendedResidual_smooth {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) :
    ContDiffOn ℝ ∞ (extendedResidual f hext) (SpacetimeEndpoint.closedPast 1) :=
  SpacetimeEndpoint.contDiffOn_joint_extension (J := ftaylorSeries ℝ f)
    (fun _ _ => rfl) (actual_derivative_recurrence hf) (boundaryLimits_locallyUniform hzero hext)

theorem extendedResidual_boundary_jets {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) (n : ℕ) (x : Space) :
    iteratedFDerivWithin ℝ n (extendedResidual f hext)
      (SpacetimeEndpoint.closedPast 1) (1, x) = boundaryLimits f hext x n :=
  SpacetimeEndpoint.boundary_jets_eq_limits (J := ftaylorSeries ℝ f)
    (fun _ _ => rfl) (actual_derivative_recurrence hf) (boundaryLimits_locallyUniform hzero hext) n
        x

theorem extendedResidual_flat_at_origin {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) (n : ℕ) :
    iteratedFDerivWithin ℝ n (extendedResidual f hext)
      (SpacetimeEndpoint.closedPast 1) ((1 : ℝ), (0 : Space)) = 0 := by
  rw [extendedResidual_boundary_jets hf hzero hext, boundaryLimits_zero]

theorem extendedResidual_unit_periods {f : SpaceTime → V}
    (hzero : VanishingJointJets f) (hext : AwayExtensions f)
    (hperiod : ProblemStatement.UnitSpatialPeriodsOn (Iio (1 : ℝ)) f) :
    ProblemStatement.UnitSpatialPeriodsOn univ (extendedResidual f hext) :=
  SpacetimeEndpoint.unit_periods_joint_extension (J := ftaylorSeries ℝ f)
    (fun _ _ => rfl) (boundaryLimits_locallyUniform hzero hext 0) hperiod

/-- The limit portion of the `CandidateFromLimits` input is constructed
solely from actual joint jet limits and one-sided local extensions. -/
theorem exists_residual_limits {f : SpaceTime → V}
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) :
    ∃ L : Space → FormalMultilinearSeries ℝ SpaceTime V,
      (∀ n : ℕ, L 0 n = 0) ∧
      (∀ n : ℕ, ∀ x : Space, Tendsto (iteratedFDeriv ℝ n f)
        (𝓝[SpacetimeEndpoint.openPast 1] (1, x)) (𝓝 (L x n))) ∧
      (∀ n : ℕ, TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n f (t, x))
        (fun x => L x n) (𝓝[<] (1 : ℝ))) :=
  ⟨boundaryLimits f hext, boundaryLimits_zero f hext,
    boundaryLimits_joint hzero hext, boundaryLimits_locallyUniform hzero hext⟩

/-- Complete endpoint implication, including derived smoothness and exact
compatibility of all boundary tensors. -/
theorem exists_smooth_compatible_limits {f : SpaceTime → V}
    (hf : ContDiffOn ℝ ∞ f (SpacetimeEndpoint.openPast 1))
    (hzero : VanishingJointJets f) (hext : AwayExtensions f) :
    ∃ L : Space → FormalMultilinearSeries ℝ SpaceTime V,
      (∀ n : ℕ, L 0 n = 0) ∧
      (∀ n : ℕ, TendstoLocallyUniformly (fun t x => iteratedFDeriv ℝ n f (t, x))
        (fun x => L x n) (𝓝[<] (1 : ℝ))) ∧
      (∀ n : ℕ, ContDiff ℝ ∞ (fun x => L x n)) ∧
      (∀ n : ℕ, ∀ x : Space, HasFDerivAt (fun y => L y n)
        ((L x (n + 1)).curryLeft.comp (ContinuousLinearMap.inr ℝ ℝ Space)) x) :=
  ⟨boundaryLimits f hext, boundaryLimits_zero f hext,
    boundaryLimits_locallyUniform hzero hext, boundaryLimits_smooth hf hzero hext,
    boundaryLimits_hasFDerivAt hf hzero hext⟩

end ActualJets

end NavierStokes.JointResidualLimits
