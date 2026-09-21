/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.MultipleIntegral

/-!
# Homogeneous chaoses of the selected Hilbert tower

For a pre-Brownian process `B`, the `n`th homogeneous chaos in this file is the closed range of
the selected order-`n` multiple operator.  Its Hilbert-space laws imply that these closed subspaces
are pairwise orthogonal.  The construction is law-level: identifying the operators and ranges
with the classical Wiener--Itô tower additionally requires the Brownian ordered-box link.

The density statement requires a genuine hypothesis on the underlying probability space.  A
pre-Brownian process may be defined on a product space carrying additional independent randomness,
in which case process-generated classical chaoses cannot span all of `L²(P)`.  We therefore record
sigma-generation by `B`
as `IsWienerGenerated B`.  Under that hypothesis, the selected tower gives the Hilbert sum

`L²(P) = ⨁ n, homogeneousChaos hB n`.

The proof combines orthogonality from the preceding rung with two facts.  The Brownian covariance
law gives `L²`-continuity in time, so countably many dense-time coordinates generate the ambient
measure algebra modulo null sets and `L²(P)` is separable.  Sigma-generation also makes the
canonical embedding of
process-measurable `L²` onto ambient `L²`; only under that exhaustion condition does the selected
global simplex tower use its onto branch.  Order zero supplies constants, and
`IsHilbertSum.mkInternal` packages the resulting total orthogonal family.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace Topology symmDiff

noncomputable
section

namespace Malliavin

universe u v u_1 u_2 u_4 u_6

recall Submodule.le_topologicalClosure {R : Type u} {M : Type v} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousConstSMul R M]
    [ContinuousAdd M] (s : Submodule R M) : s ≤ s.topologicalClosure

recall Submodule.topologicalClosure_minimal {R : Type u} {M : Type v} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousConstSMul R M]
    [ContinuousAdd M] (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t

recall MeasurableSpace.comap_process_pi {β : Type u_2} {δ : Type u_4}
    {X : δ → Type u_6} [(a : δ) → MeasurableSpace (X a)] (f : (a : δ) → β → X a) :
    MeasurableSpace.comap (fun b a ↦ f a b) inferInstance =
      ⨆ a, MeasurableSpace.comap (f a) inferInstance

recall MeasureTheory.tendstoInMeasure_of_tendsto_Lp {α : Type u_1} {ι : Type u_2}
    {E : Type u_4} {m : MeasurableSpace α} {μ : Measure α} {p : ENNReal}
    [NormedAddCommGroup E] [hp : Fact (1 ≤ p)] {f : ι → Lp E p μ} {g : Lp E p μ}
    {l : Filter ι} (hfg : Filter.Tendsto f l (𝓝 g)) :
    TendstoInMeasure μ (fun n ↦ f n) l g

recall MeasureTheory.TendstoInMeasure.exists_seq_tendsto_ae {α : Type u_1}
    {E : Type u_4} {m : MeasurableSpace α} {μ : Measure α} [PseudoEMetricSpace E]
    {f : ℕ → α → E} {g : α → E} (hfg : TendstoInMeasure μ f Filter.atTop g) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ x ∂μ,
      Filter.Tendsto (fun i ↦ f (ns i) x) Filter.atTop (𝓝 (g x))

recall MeasureTheory.exists_countable_measureDense {X : Type u_1}
    [m : MeasurableSpace X] (μ : Measure X) [IsSeparable μ] :
    ∃ 𝒜, 𝒜.Countable ∧ μ.MeasureDense 𝒜

recall MeasureTheory.isSeparable_of_sigmaFinite {X : Type u_1}
    [m : MeasurableSpace X] (μ : Measure X) [MeasurableSpace.CountablyGenerated X]
    [SigmaFinite μ] : IsSeparable μ

recall tsum_mem {α : Type u_1} [AddCommMonoid α] [TopologicalSpace α]
    {ι : Type u_4} {S : Type u_6} {s : S} [SetLike S α] [AddSubmonoidClass S α]
    (h_closed : IsClosed (s : Set α)) {f : ι → α} (h : ∀ i, f i ∈ s) :
    ∑' i, f i ∈ s

recall Submodule.isClosed_topologicalClosure {R : Type u} {M : Type v} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousConstSMul R M]
    [ContinuousAdd M] (s : Submodule R M) : IsClosed (s.topologicalClosure : Set M)

universe u₁ u₂ u₃

recall ProbabilityTheory.IsPreBrownianReal.hasLaw_sub {Ω : Type u₁}
    {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ} {P : Measure Ω}
    (hB : IsPreBrownianReal B P) (s t : NNReal) :
    HasLaw (B s - B t) (gaussianReal 0 (nndist (s : ℝ) (t : ℝ))) P

recall ProbabilityTheory.HasGaussianLaw.memLp_two {Ω : Type u₁} {E : Type u₂}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {X : Ω → E} [NormedSpace ℝ E]
    [CompleteSpace E] [SecondCountableTopology E] (hX : HasGaussianLaw X P) :
    MemLp X 2 P

recall ProbabilityTheory.covariance_eq_sub {Ω : Type u₁}
    {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ =
      ∫ x, (X * Y) x ∂μ - (∫ x, X x ∂μ) * ∫ x, Y x ∂μ

recall MeasureTheory.L2.inner_def {α : Type u₁} {E : Type u₂} {𝕜 : Type u₃}
    [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (f g : Lp E 2 μ) :
    inner 𝕜 f g = ∫ a, inner 𝕜 (f a) (g a) ∂μ

recall MeasureTheory.Lp.coeFn_sub {α : Type u₁} {E : Type u₂}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] (f g : Lp E p μ) :
    ((f - g : Lp E p μ) : α → E) =ᵐ[μ] (f : α → E) - (g : α → E)

recall ProbabilityTheory.HasLaw.variance_eq {Ω : Type u₁}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure ℝ}
    {X : Ω → ℝ} (hX : HasLaw X μ P) :
    variance X P = variance id μ

recall ProbabilityTheory.variance_id_gaussianReal {μ : ℝ} {v : NNReal} :
    variance id (gaussianReal μ v) = (v : ℝ)

recall mem_closure_iff_seq_limit {X : Type u₁} [TopologicalSpace X]
    [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔
      ∃ x, (∀ n : ℕ, x n ∈ s) ∧ Filter.Tendsto x Filter.atTop (nhds a)

recall Measurable.limsup {α : Type u₁} {δ : Type u₂} [TopologicalSpace α]
    {mα : MeasurableSpace α} [BorelSpace α] {mδ : MeasurableSpace δ}
    [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    [SecondCountableTopology α] {f : ℕ → δ → α}
    (hf : ∀ i, Measurable (f i)) :
    Measurable fun x ↦ Filter.limsup (fun i ↦ f i x) Filter.atTop

recall MeasureTheory.ae_all_iff {α : Type u₁} {F : Type u₂}
    [FunLike F (Set α) ENNReal] [OuterMeasureClass F α] {μ : F}
    {ι : Sort u₃} [Countable ι] {p : α → ι → Prop} :
    (∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i

recall MeasureTheory.Measure.MeasureDense.approx {X : Type u₁}
    [m : MeasurableSpace X] {μ : Measure X} {𝒜 : Set (Set X)}
    (self : μ.MeasureDense 𝒜) (s : Set X) :
    MeasurableSet s → μ s ≠ ⊤ → ∀ ε : ℝ, 0 < ε →
      ∃ t ∈ 𝒜, μ (symmDiff s t) < ENNReal.ofReal ε

recall MeasureTheory.trim_measurableSet_eq {α : Type u₁}
    {m m0 : MeasurableSpace α} {μ : @Measure α m0} {s : Set α}
    (hm : m ≤ m0) (hs : @MeasurableSet α m s) :
    (μ.trim hm) s = μ s

recall MeasureTheory.Lp.SecondCountableTopology {X : Type u₁} {E : Type u₂}
    [m : MeasurableSpace X] [NormedAddCommGroup E] {μ : Measure X}
    {p : ENNReal} [one_le_p : Fact (1 ≤ p)] [p_ne_top : Fact (p ≠ ⊤)]
    [IsSeparable μ] [TopologicalSpace.SeparableSpace E] :
    SecondCountableTopology (Lp E p μ)

recall HasSum.tsum_eq {α : Type u₁} {β : Type u₂} [AddCommMonoid α]
    [TopologicalSpace α] {L : SummationFilter β} {f : β → α} {a : α}
    [T2Space α] [L.NeBot] (ha : HasSum f a L) : ∑'[L] b, f b = a

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ}

/-- The (not necessarily closed) range of the selected order-`n` multiple operator. -/
def multipleIntegralRange (hB : IsPreBrownianReal B P) (n : ℕ) :
    Submodule ℝ (RandomL2 P) :=
  LinearMap.range (multipleIntegralCLM hB n).toLinearMap

/-- The selected `n`th homogeneous subspace: the closed range of `Iₙ`. -/
def homogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ) :
    ClosedSubmodule ℝ (RandomL2 P) :=
  (multipleIntegralRange hB n).closure

/-- A selected homogeneous subspace is complete because it is closed in `L²(P)`. -/
instance instCompleteSpaceHomogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ) :
    CompleteSpace ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) :=
  (homogeneousChaos hB n).isClosed'.completeSpace_coe

/-- Every output of the selected order-`n` multiple operator belongs to its closed range. -/
theorem multipleIntegralCLM_mem_homogeneousChaos (hB : IsPreBrownianReal B P) (n : ℕ)
    (f : IteratedKernel n) :
    multipleIntegralCLM hB n f ∈ homogeneousChaos hB n := by
  apply Submodule.le_topologicalClosure (multipleIntegralRange hB n)
  exact LinearMap.mem_range_self (multipleIntegralCLM hB n).toLinearMap f

/-- The unclosed ranges of selected operators of distinct orders are orthogonal. -/
theorem multipleIntegralRange_isOrtho (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) : multipleIntegralRange hB m ⟂ multipleIntegralRange hB n := by
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨f, rfl⟩ _ ⟨g, rfl⟩
  exact inner_multipleIntegralCLM_ne hB hmn f g

/-- Distinct selected homogeneous subspaces remain orthogonal after taking closures. -/
theorem homogeneousChaos_isOrtho (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) :
    (homogeneousChaos hB m : Submodule ℝ (RandomL2 P)) ⟂
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)) := by
  change (multipleIntegralRange hB m).topologicalClosure ≤
    (multipleIntegralRange hB n).topologicalClosureᗮ
  rw [Submodule.orthogonal_closure]
  exact Submodule.topologicalClosure_minimal (multipleIntegralRange hB m)
    (multipleIntegralRange_isOrtho hB hmn).le
    (multipleIntegralRange hB n).isClosed_orthogonal

/-- The selected homogeneous subspaces, embedded in `L²(P)`, form an orthogonal family. -/
theorem homogeneousChaos_orthogonalFamily (hB : IsPreBrownianReal B P) :
    OrthogonalFamily ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) := by
  apply OrthogonalFamily.of_pairwise
  intro m n hmn
  exact homogeneousChaos_isOrtho hB hmn

/-- The closed subspace of (almost-everywhere) constant random variables. -/
def constantRandomVariables (P : Measure Ω) [IsFiniteMeasure P] :
    Submodule ℝ (RandomL2 P) :=
  (MeasureTheory.Lp.constL 2 P ℝ : ℝ →L[ℝ] RandomL2 P).range.topologicalClosure

/-- The selected zeroth homogeneous subspace is exactly the subspace of constants. -/
theorem homogeneousChaos_zero_eq_constants (hB : IsPreBrownianReal B P) :
    letI : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
    (homogeneousChaos hB 0 : Submodule ℝ (RandomL2 P)) = constantRandomVariables P := by
  let : IsProbabilityMeasure P := (hB.hasLaw ∅).isProbabilityMeasure
  unfold homogeneousChaos multipleIntegralRange constantRandomVariables
  apply le_antisymm <;> apply Submodule.topologicalClosure_mono
  · rintro x ⟨f, rfl⟩
    refine ⟨∫ t, f t ∂iteratedKernelMeasure 0, ?_⟩
    change Lp.const 2 P _ = multipleIntegralCLM hB 0 f
    apply Lp.ext
    exact (Lp.coeFn_const 2 P _).trans (multipleIntegralCLM_zeroOrder hB f).symm
  · rintro x ⟨c, rfl⟩
    let f : IteratedKernel 0 := Lp.const 2 (iteratedKernelMeasure 0) c
    refine ⟨f, ?_⟩
    change multipleIntegralCLM hB 0 f = Lp.const 2 P c
    apply Lp.ext
    have hfc : (fun t => f t) =ᵐ[iteratedKernelMeasure 0] fun _ => c :=
      Lp.coeFn_const 2 (iteratedKernelMeasure 0) c
    have hint : ∫ t, f t ∂iteratedKernelMeasure 0 = c := by
      rw [integral_congr_ae hfc, integral_const]
      simp only [iteratedKernelMeasure, Measure.pi_empty_univ, Measure.real, ENNReal.toReal_one,
        one_smul]
    have hI := multipleIntegralCLM_zeroOrder hB f
    rw [hint] at hI
    exact hI.trans (Lp.coeFn_const 2 P c).symm

/-! ### Separability of a Brownian-generated probability space -/

/-- The sigma-algebra generated by a fixed countable dense sequence of times. -/
abbrev countableProcessMeasurableSpace (B : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨆ n : ℕ, MeasurableSpace.comap (B (TopologicalSpace.denseSeq ℝ≥0 n)) (borel ℝ)

omit mΩ in
private theorem countableProcessMeasurableSpace_countablyGenerated
    (B : ℝ≥0 → Ω → ℝ) :
    @MeasurableSpace.CountablyGenerated Ω (countableProcessMeasurableSpace B) := by
  rw [countableProcessMeasurableSpace, ← MeasurableSpace.comap_process_pi]
  exact MeasurableSpace.CountablyGenerated.comap _

omit mΩ in
private theorem countableProcessMeasurableSpace_le_processMeasurableSpace
    (B : ℝ≥0 → Ω → ℝ) :
    countableProcessMeasurableSpace B ≤ processMeasurableSpace B := by
  rw [countableProcessMeasurableSpace]
  exact iSup_le fun n ↦ le_iSup (fun t : ℝ≥0 ↦
    MeasurableSpace.comap (B t) (borel ℝ)) (TopologicalSpace.denseSeq ℝ≥0 n)

private def brownianEvalL2 (hB : IsPreBrownianReal B P) (t : ℝ≥0) : RandomL2 P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.toLp (B t)

private theorem brownianEvalL2_dist_sq (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ‖brownianEvalL2 hB s - brownianEvalL2 hB t‖ ^ 2 = nndist (s : ℝ) (t : ℝ) := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hst := (hB.isGaussianProcess.hasGaussianLaw_sub (s := s) (t := t)).memLp_two
  have hmean : ∫ ω, (B s - B t) ω ∂P = 0 := by
    change ∫ ω, (B s ω - B t ω) ∂P = 0
    rw [integral_sub (hB.integrable_eval s) (hB.integrable_eval t),
      hB.integral_eval, hB.integral_eval, sub_zero]
  have hcov := covariance_eq_sub hst hst
  rw [hmean, mul_zero, sub_zero] at hcov
  rw [@norm_sq_eq_re_inner ℝ, L2.inner_def]
  simp only [RCLike.re_to_real, Real.inner_apply]
  have hcoe : (fun ω ↦ (brownianEvalL2 hB s - brownianEvalL2 hB t) ω *
      (brownianEvalL2 hB s - brownianEvalL2 hB t) ω) =ᵐ[P]
      fun ω ↦ (B s ω - B t ω) * (B s ω - B t ω) := by
    filter_upwards [Lp.coeFn_sub (brownianEvalL2 hB s) (brownianEvalL2 hB t),
      MemLp.coeFn_toLp hs, MemLp.coeFn_toLp ht] with ω hsub hsω htω
    change (brownianEvalL2 hB s - brownianEvalL2 hB t) ω =
      brownianEvalL2 hB s ω - brownianEvalL2 hB t ω at hsub
    change brownianEvalL2 hB s ω = B s ω at hsω
    change brownianEvalL2 hB t ω = B t ω at htω
    rw [hsub, hsω, htω]
  rw [integral_congr_ae hcoe]
  calc
    ∫ ω, (B s ω - B t ω) * (B s ω - B t ω) ∂P =
        cov[B s - B t, B s - B t; P] := hcov.symm
    _ = Var[B s - B t; P] := covariance_self hst.aemeasurable
    _ = Var[id; gaussianReal 0 (nndist (s : ℝ) (t : ℝ))] :=
      (hB.hasLaw_sub s t).variance_eq
    _ = nndist (s : ℝ) (t : ℝ) := variance_id_gaussianReal

private theorem brownianEvalL2_dist (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ‖brownianEvalL2 hB s - brownianEvalL2 hB t‖ =
      Real.sqrt (nndist (s : ℝ) (t : ℝ) : ℝ) := by
  have hsqrt : (Real.sqrt (nndist (s : ℝ) (t : ℝ) : ℝ)) ^ 2 =
      (nndist (s : ℝ) (t : ℝ) : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [brownianEvalL2_dist_sq hB s t,
    norm_nonneg (brownianEvalL2 hB s - brownianEvalL2 hB t),
    Real.sqrt_nonneg (nndist (s : ℝ) (t : ℝ) : ℝ)]

private theorem brownianEvalL2_tendsto (hB : IsPreBrownianReal B P)
    {ι : Type*} {l : Filter ι} {u : ι → ℝ≥0} {t : ℝ≥0}
    (hu : Filter.Tendsto u l (𝓝 t)) :
    Filter.Tendsto (fun i ↦ brownianEvalL2 hB (u i)) l (𝓝 (brownianEvalL2 hB t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp_rw [brownianEvalL2_dist]
  have hd : Filter.Tendsto
      (fun i ↦ (nndist ((u i : ℝ≥0) : ℝ) (t : ℝ) : ℝ)) l (𝓝 0) := by
    have hc : Continuous fun s : ℝ≥0 ↦ (nndist (s : ℝ) (t : ℝ) : ℝ) := by fun_prop
    convert (hc.tendsto t).comp hu using 1 <;> simp [Function.comp_def]
  convert (Real.continuous_sqrt.tendsto 0).comp hd using 1 <;>
    simp [Function.comp_def]

private theorem exists_denseTimeApprox (t : ℝ≥0) :
    ∃ k : ℕ → ℕ,
      Filter.Tendsto (fun n ↦ TopologicalSpace.denseSeq ℝ≥0 (k n)) Filter.atTop (𝓝 t) := by
  have ht : t ∈ closure (Set.range (TopologicalSpace.denseSeq ℝ≥0)) := by
    rw [(TopologicalSpace.denseRange_denseSeq ℝ≥0).closure_eq]
    exact Set.mem_univ t
  obtain ⟨q, hq, hqt⟩ := mem_closure_iff_seq_limit.mp ht
  choose k hk using hq
  refine ⟨k, ?_⟩
  convert hqt using 1
  funext n
  exact hk n

omit mΩ in
private theorem measurable_denseTime_eval (B : ℝ≥0 → Ω → ℝ) (n : ℕ) :
    @Measurable Ω ℝ (countableProcessMeasurableSpace B) (borel ℝ)
      (B (TopologicalSpace.denseSeq ℝ≥0 n)) := by
  exact Measurable.of_comap_le (le_iSup (fun k : ℕ ↦
    MeasurableSpace.comap (B (TopologicalSpace.denseSeq ℝ≥0 k)) (borel ℝ)) n)

private theorem exists_countableProcess_measurable_ae_eq
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    ∃ g : Ω → ℝ,
      @Measurable Ω ℝ (countableProcessMeasurableSpace B) (borel ℝ) g ∧ g =ᵐ[P] B t := by
  obtain ⟨k, hk⟩ := exists_denseTimeApprox t
  have hLp := brownianEvalL2_tendsto hB hk
  have hmeasure := tendstoInMeasure_of_tendsto_Lp hLp
  obtain ⟨ns, _hns, hae⟩ := hmeasure.exists_seq_tendsto_ae
  let q : ℕ → ℝ≥0 := fun i ↦ TopologicalSpace.denseSeq ℝ≥0 (k (ns i))
  let g : Ω → ℝ := fun ω ↦ Filter.limsup (fun i ↦ B (q i) ω) Filter.atTop
  refine ⟨g, ?_, ?_⟩
  · exact Measurable.limsup fun i ↦ measurable_denseTime_eval B (k (ns i))
  · have hcoe_seq : ∀ᵐ ω ∂P, ∀ i,
        brownianEvalL2 hB (q i) ω = B (q i) ω :=
      ae_all_iff.mpr fun i ↦
        MemLp.coeFn_toLp (hB.isGaussianProcess.hasGaussianLaw_eval (q i)).memLp_two
    have hcoe_t : brownianEvalL2 hB t =ᵐ[P] B t :=
      MemLp.coeFn_toLp (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
    filter_upwards [hae, hcoe_seq, hcoe_t] with ω hlim hseq ht
    have hlim' : Filter.Tendsto (fun i ↦ B (q i) ω) Filter.atTop (𝓝 (B t ω)) := by
      convert hlim using 1
      · funext i
        exact (hseq i).symm
      · exact congrArg (fun x : ℝ ↦ 𝓝 x) ht.symm
    exact hlim'.limsup_eq

private theorem exists_countableProcess_measurableSet_ae_eq
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B)
    {s : Set Ω} (hs : MeasurableSet s) :
    ∃ t : Set Ω, @MeasurableSet Ω (countableProcessMeasurableSpace B) t ∧ s =ᵐ[P] t := by
  let mAE : MeasurableSpace Ω :=
    { MeasurableSet' := fun s ↦
        ∃ t : Set Ω, @MeasurableSet Ω (countableProcessMeasurableSpace B) t ∧ s =ᵐ[P] t
      measurableSet_empty :=
        ⟨∅, @MeasurableSet.empty Ω (countableProcessMeasurableSpace B),
          Filter.EventuallyEq.rfl⟩
      measurableSet_compl := by
        rintro s ⟨t, ht, hst⟩
        exact ⟨tᶜ, ht.compl, hst.compl⟩
      measurableSet_iUnion := by
        intro f hf
        choose g hgm hfg using hf
        refine ⟨⋃ i, g i, @MeasurableSet.iUnion Ω ℕ
          (countableProcessMeasurableSpace B) inferInstance g hgm, ?_⟩
        have hall : ∀ᵐ ω ∂P, ∀ i, ω ∈ f i ↔ ω ∈ g i :=
          ae_all_iff.mpr fun i ↦ (hfg i).mono fun _ h ↦ h.to_iff
        filter_upwards [hall] with ω hω
        apply propext
        constructor
        · intro hw
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
          exact Set.mem_iUnion.mpr ⟨i, (hω i).mp hi⟩
        · intro hw
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
          exact Set.mem_iUnion.mpr ⟨i, (hω i).mpr hi⟩ }
  have hcoord (t : ℝ≥0) : @Measurable Ω ℝ mAE (borel ℝ) (B t) := by
    intro u hu
    obtain ⟨g, hg, hgt⟩ :=
      exists_countableProcess_measurable_ae_eq (mΩ := mΩ) hB t
    refine ⟨g ⁻¹' u, hg hu, ?_⟩
    filter_upwards [hgt] with ω hω
    change (B t ω ∈ u) = (g ω ∈ u)
    exact congrArg (· ∈ u) hω.symm
  have hprocess : processMeasurableSpace B ≤ mAE :=
    iSup_le fun t ↦ (hcoord t).comap_le
  have hambient : mΩ ≤ mAE := by
    rw [← hgen]
    exact hprocess
  exact hambient s hs

/-- A probability space generated by a pre-Brownian process is separable modulo its measure.
This remains true when null-set modifications make the ambient sigma-algebra itself non-countably
generated. -/
theorem isSeparable_of_isWienerGenerated
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    MeasureTheory.IsSeparable P := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hmD : countableProcessMeasurableSpace B ≤ mΩ := by
    rw [← hgen]
    exact countableProcessMeasurableSpace_le_processMeasurableSpace B
  let μD : @Measure Ω (countableProcessMeasurableSpace B) := P.trim hmD
  let _ : @MeasurableSpace.CountablyGenerated Ω (countableProcessMeasurableSpace B) :=
    countableProcessMeasurableSpace_countablyGenerated B
  let _ : IsFiniteMeasure μD := MeasureTheory.isFiniteMeasure_trim hmD
  have hsepD : @MeasureTheory.IsSeparable Ω (countableProcessMeasurableSpace B) μD :=
    @MeasureTheory.isSeparable_of_sigmaFinite Ω (countableProcessMeasurableSpace B)
      μD inferInstance inferInstance
  obtain ⟨A, hAc, hAdense⟩ :=
    @exists_countable_measureDense Ω (countableProcessMeasurableSpace B) μD hsepD
  refine ⟨A, hAc, ?_⟩
  refine
    { measurable := by
        intro u hu
        apply hmD
        exact @Measure.MeasureDense.measurable Ω (countableProcessMeasurableSpace B)
          μD A hAdense u hu
      approx := ?_ }
  intro s hs _ ε hε
  obtain ⟨t, ht, hst⟩ := exists_countableProcess_measurableSet_ae_eq hB hgen hs
  have htfinite : μD t ≠ ∞ := (measure_lt_top μD t).ne
  obtain ⟨u, hu, htu⟩ :=
    @Measure.MeasureDense.approx Ω (countableProcessMeasurableSpace B) μD A
      hAdense t ht htfinite ε hε
  refine ⟨u, hu, ?_⟩
  have huD : @MeasurableSet Ω (countableProcessMeasurableSpace B) u :=
    @Measure.MeasureDense.measurable Ω (countableProcessMeasurableSpace B)
      μD A hAdense u hu
  have hsu : (s ∆ u) =ᵐ[P] (t ∆ u) :=
    hst.symmDiff (Filter.EventuallyEq.rfl : u =ᵐ[P] u)
  have htuD : @MeasurableSet Ω (countableProcessMeasurableSpace B) (t ∆ u) :=
    ht.symmDiff huD
  have htrim : μD (t ∆ u) = P (t ∆ u) := trim_measurableSet_eq hmD htuD
  calc
    P (s ∆ u) = P (t ∆ u) := measure_congr hsu
    _ = μD (t ∆ u) := htrim.symm
    _ < ENNReal.ofReal ε := htu

/-- Consequently, the real ambient `L²` space is second-countable. -/
theorem secondCountableTopology_randomL2_of_isWienerGenerated
    (hB : IsPreBrownianReal B P) (hgen : IsWienerGenerated B) :
    SecondCountableTopology (RandomL2 P) := by
  let _ : @MeasureTheory.IsSeparable Ω mΩ P :=
    isSeparable_of_isWienerGenerated hB hgen
  let _ : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  exact @MeasureTheory.Lp.SecondCountableTopology Ω ℝ mΩ inferInstance P 2
    inferInstance inferInstance inferInstance inferInstance

/-- The closed subspace generated by all selected homogeneous ranges. -/
def wienerSubspace (hB : IsPreBrownianReal B P) : Submodule ℝ (RandomL2 P) :=
  (⨆ n : ℕ, (homogeneousChaos hB n : Submodule ℝ (RandomL2 P))).topologicalClosure

/-- The assertion that the selected homogeneous subspaces exhaust ambient `L²(P)`. -/
def IsWienerTotal (hB : IsPreBrownianReal B P) : Prop :=
  wienerSubspace hB = ⊤

/-- Totality of the selected homogeneous ranges under the exact `L²` exhaustion condition used
by the tower.

Surjectivity of `processLpEmbedding` makes the positive-order tower take its Hilbert-equivalence
branch onto the centered subspace.  Each summand is represented by a selected multiple operator,
and order zero supplies the constant part. -/
theorem isWienerTotal_of_processLpEmbedding
    (hB : IsPreBrownianReal B P) [SecondCountableTopology (RandomL2 P)]
    (hmeas : ∀ t, Measurable (B t))
    (hexhausts : Function.Surjective (processLpEmbedding P B hmeas)) :
    IsWienerTotal hB := by
  let _ : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [IsWienerTotal, wienerSubspace, eq_top_iff]
  intro F _
  let oneP := IteratedIntegralConstruction.probabilityOne hB
  let c : ℝ := inner ℝ oneP F
  let X0 : RandomL2 P := F - c • oneP
  have hone : inner ℝ oneP oneP = 1 := by
    rw [real_inner_self_eq_norm_sq,
      IteratedIntegralConstruction.norm_probabilityOne hB]
    norm_num
  have hX0 : inner ℝ oneP X0 = 0 := by
    dsimp [X0]
    rw [inner_sub_right, inner_smul_right, hone]
    simp only [c, mul_one, sub_self]
  let X : IteratedIntegralConstruction.CenteredRandomL2 hB :=
    ⟨X0, Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hX0⟩
  obtain ⟨f, hf⟩ :=
    IteratedIntegralConstruction.positiveIteratedTowerLI_surjective_of_processLpEmbedding
      hB hmeas hexhausts X
  have hterm (n : ℕ) :
      IteratedIntegralConstruction.simplexIntegralLI hB n (f n) ∈
        wienerSubspace hB := by
    obtain ⟨g, hg⟩ := exists_multipleIntegralCLM_eq_simplexIntegralLI hB n (f n)
    apply Submodule.le_topologicalClosure
    apply le_iSup (fun k : ℕ ↦
      (homogeneousChaos hB k : Submodule ℝ (RandomL2 P))) (n + 1)
    rw [← hg]
    exact multipleIntegralCLM_mem_homogeneousChaos hB (n + 1) g
  have hXmem : (X : RandomL2 P) ∈ wienerSubspace hB := by
    have hXsum : HasSum
        (fun n ↦ IteratedIntegralConstruction.simplexIntegralLI hB n (f n))
        (X : RandomL2 P) := by
      simpa only [hf] using
        IteratedIntegralConstruction.hasSum_simplexIntegralLI hB f
    rw [← hXsum.tsum_eq]
    exact tsum_mem (Submodule.isClosed_topologicalClosure _) hterm
  have hone_mem : c • oneP ∈ wienerSubspace hB := by
    apply Submodule.le_topologicalClosure
    apply le_iSup (fun k : ℕ ↦
      (homogeneousChaos hB k : Submodule ℝ (RandomL2 P))) 0
    rw [homogeneousChaos_zero_eq_constants hB]
    apply Submodule.le_topologicalClosure
    refine ⟨c, ?_⟩
    change (Lp.constL 2 P ℝ) c = c • oneP
    rw [show c = c • (1 : ℝ) by simp only [smul_eq_mul, mul_one], map_smul]
    simp only [Lp.constL_apply, smul_eq_mul, mul_one, IteratedIntegralConstruction.probabilityOne,
      indicatorConstLp_univ, oneP]
  have hdecomp : F = c • oneP + (X : RandomL2 P) := by
    change F = c • oneP + X0
    dsimp only [X0]
    abel
  rw [hdecomp]
  exact add_mem hone_mem hXmem

/-- Density of finite sums of the selected homogeneous ranges on a Brownian-generated space.

Sigma-generation supplies second-countability and makes process-measurable `L²` exhaust the
ambient space, so `isWienerTotal_of_processLpEmbedding` applies. -/
theorem isWienerTotal_of_generated (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) : IsWienerTotal hB := by
  let _ : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated hB hgen
  let hmeas : ∀ t, Measurable (B t) := hgen.measurable
  exact isWienerTotal_of_processLpEmbedding hB hmeas
    (processLpEmbedding_surjective P B hmeas hgen)

/-- Expanded form of `isWienerTotal_of_generated`. -/
theorem homogeneousChaos_total (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) :
    (⨆ n : ℕ, (homogeneousChaos hB n : Submodule ℝ (RandomL2 P))).topologicalClosure = ⊤ :=
  isWienerTotal_of_generated hB hgen

/-- Hilbert-sum decomposition of the selected homogeneous ranges from the totality contract. -/
theorem wienerChaos_isHilbertSum_of_total (hB : IsPreBrownianReal B P)
    (htotal : IsWienerTotal hB) :
    IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) := by
  refine IsHilbertSum.mkInternal
    (F := fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
    (homogeneousChaos_orthogonalFamily hB) ?_
  change ⊤ ≤ wienerSubspace hB
  rw [htotal]

/-- Hilbert-sum decomposition of the selected homogeneous ranges on a generated space. -/
theorem wienerChaos_isHilbertSum (hB : IsPreBrownianReal B P)
    (hgen : IsWienerGenerated B) :
    IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ) :=
  wienerChaos_isHilbertSum_of_total hB (isWienerTotal_of_generated hB hgen)

/-- Orthogonal projection of `L²(P)` onto the selected `n`th homogeneous subspace. -/
def chaosProjection (hB : IsPreBrownianReal B P) (n : ℕ) :
    RandomL2 P →L[ℝ] RandomL2 P :=
  (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection

/-- A selected-range projection takes values in its corresponding closed subspace. -/
theorem chaosProjection_mem (hB : IsPreBrownianReal B P) (n : ℕ) (F : RandomL2 P) :
    chaosProjection hB n F ∈ homogeneousChaos hB n :=
  Submodule.starProjection_apply_mem _ _

/-- Projections onto distinct selected homogeneous subspaces compose to zero. -/
theorem chaosProjection_comp_eq_zero (hB : IsPreBrownianReal B P) {m n : ℕ}
    (hmn : m ≠ n) :
    chaosProjection hB m ∘L chaosProjection hB n = 0 := by
  change
    (homogeneousChaos hB m : Submodule ℝ (RandomL2 P)).starProjection ∘L
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection = 0
  rw [Submodule.starProjection_comp_starProjection_eq_zero_iff]
  exact homogeneousChaos_isOrtho hB hmn

/-- Unitary coordinates, canonical relative to the selected orthogonal subspaces. -/
def wienerChaosEquiv (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB) :
    RandomL2 P ≃ₗᵢ[ℝ]
      lp (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P))) 2 :=
  (wienerChaos_isHilbertSum_of_total hB htotal).linearIsometryEquiv

/-- Hilbert-sum coordinates are the orthogonal projections onto each selected subspace. -/
theorem wienerChaos_coordinate_eq_projection
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (n : ℕ) (F : RandomL2 P) :
    hsum.linearIsometryEquiv F n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F := by
  apply ext_inner_left ℝ
  intro u
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  calc
    inner ℝ u (hsum.linearIsometryEquiv F n) =
        inner ℝ (lp.single 2 n u) (hsum.linearIsometryEquiv F) :=
      (lp.inner_single_left n u (hsum.linearIsometryEquiv F)).symm
    _ = inner ℝ (hsum.linearIsometryEquiv.symm (lp.single 2 n u))
          (hsum.linearIsometryEquiv.symm (hsum.linearIsometryEquiv F)) := by
      rw [hsum.linearIsometryEquiv.symm.inner_map_map]
    _ = inner ℝ (u : RandomL2 P) F := by
      rw [hsum.linearIsometryEquiv_symm_apply_single,
        hsum.linearIsometryEquiv.symm_apply_apply]
      rfl

/-- The coordinate determined by totality is the corresponding selected-subspace projection. -/
theorem wienerChaosEquiv_apply (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) (n : ℕ) :
    (wienerChaosEquiv hB htotal F) n =
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).orthogonalProjectionOnto F :=
  wienerChaos_coordinate_eq_projection hB
    (wienerChaos_isHilbertSum_of_total hB htotal) n F

/-- Selected-tower expansion as the sum of ambient orthogonal projections. -/
theorem hasSum_starProjection_wienerChaos
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (F : RandomL2 P) :
    HasSum (fun n : ℕ =>
      (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F) F := by
  have h := hsum.hasSum_linearIsometryEquiv_symm (hsum.linearIsometryEquiv F)
  rw [hsum.linearIsometryEquiv.symm_apply_apply] at h
  convert h using 1
  funext n
  rw [wienerChaos_coordinate_eq_projection hB hsum n F]
  rfl

/-- Parseval identity for the selected-tower expansion. -/
theorem norm_sq_eq_tsum_starProjection_wienerChaos
    (hB : IsPreBrownianReal B P)
    (hsum : IsHilbertSum ℝ
      (fun n : ℕ => ↥(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)))
      (fun n : ℕ => (homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).subtypeₗᵢ))
    (F : RandomL2 P) :
    ‖F‖ ^ 2 = ∑' n : ℕ,
      ‖(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (hsum.linearIsometryEquiv F)
  rw [hsum.linearIsometryEquiv.norm_map] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
  rw [show (∑' n : ℕ, ‖hsum.linearIsometryEquiv F n‖ ^ 2) =
      ∑' n : ℕ,
      ‖(homogeneousChaos hB n : Submodule ℝ (RandomL2 P)).starProjection F‖ ^ 2 by
    congr 1
    funext n
    rw [wienerChaos_coordinate_eq_projection hB hsum n F]
    rfl] at h
  exact h

/-- Every square-integrable functional is the convergent sum of the coordinates canonical
relative to the selected subspaces whenever the totality contract holds. -/
theorem hasSum_wienerChaos (hB : IsPreBrownianReal B P) (htotal : IsWienerTotal hB)
    (F : RandomL2 P) :
    HasSum
      (fun n : ℕ =>
        ((wienerChaosEquiv hB htotal F) n).1)
      F := by
  simpa [wienerChaosEquiv] using
    (wienerChaos_isHilbertSum_of_total hB htotal).hasSum_linearIsometryEquiv_symm
      (wienerChaosEquiv hB htotal F)

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
