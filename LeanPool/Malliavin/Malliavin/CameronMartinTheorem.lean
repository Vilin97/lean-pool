/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.CameronMartin
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-!
# The Cameron--Martin theorem

Translation of a Gaussian measure by a Cameron--Martin vector preserves its measure class.
More precisely, if `h` belongs to the Cameron--Martin space, then the translated law has density

`exp (h(x) - ‖h‖² / 2)`

with respect to the original Gaussian measure.  Here `h(x)` means the canonical `L²(μ)`
representative supplied by the first-chaos construction in `Malliavin.CameronMartin`.

The analytic shift-versus-tilt step is `translated_eq_tilted`: both the translated and the
tilted measure give every continuous linear functional `L` the Gaussian law with mean
`L (mean μ) + ⟪ofDual μ L, h⟫` and variance `‖ofDual μ L‖²` (`map_translated_dual`,
`map_tilted_dual`, the latter through the moment generating function `mgf_tilted_dual`), so
they coincide by uniqueness of characteristic functions.  This file proves that the closed
first chaos is Gaussian and derives the normalized density formula from that step, then proves
its measure-theoretic consequences: mutual absolute continuity, the Radon--Nikodym derivative,
and the almost-everywhere logarithmic density formula used by the closability rung.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Real Topology

noncomputable section

universe u v u_1 u_2 u_3 u_4 u_5 u_6 u_8

recall MeasureTheory.Lp.stronglyMeasurable {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E p μ) : StronglyMeasurable ⇑f

recall MeasureTheory.StronglyMeasurable.measurable {α : Type u_1} {β : Type u_2}
    {f : α → β} {mα : MeasurableSpace α} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (hf : StronglyMeasurable f) : Measurable f

recall Measurable.sub_const {G : Type u_2} {α : Type u_3} [MeasurableSpace G]
    [Sub G] {m : MeasurableSpace α} {f : α → G} [MeasurableSub G]
    (hf : Measurable f) (c : G) : Measurable fun x ↦ f x - c

recall Measurable.exp {α : Type u_1} {m : MeasurableSpace α} {f : α → ℝ}
    (hf : Measurable f) : Measurable fun x ↦ Real.exp (f x)

recall Measurable.ennreal_ofReal {α : Type u_1} {mα : MeasurableSpace α}
    {f : α → ℝ} (hf : Measurable f) : Measurable fun x ↦ ENNReal.ofReal (f x)

recall Measurable.aemeasurable {α : Type u_1} {β : Type u_2}
    {m : MeasurableSpace α} [MeasurableSpace β] {f : α → β} {μ : Measure α}
    (h : Measurable f) : AEMeasurable f μ

recall Measurable.stronglyMeasurable {α : Type u_1} {β : Type u_2}
    {f : α → β} {mα : MeasurableSpace α} [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [SecondCountableTopology β]
    [OpensMeasurableSpace β] (hf : Measurable f) : StronglyMeasurable f

recall ENNReal.ofReal_ne_zero_iff {r : ℝ} : ENNReal.ofReal r ≠ 0 ↔ 0 < r

recall ENNReal.ofReal_ne_top {r : ℝ} : ENNReal.ofReal r ≠ ⊤

recall Real.exp_pos (x : ℝ) : 0 < Real.exp x

recall MeasureTheory.withDensity_absolutelyContinuous {α : Type u_1}
    {m : MeasurableSpace α} (μ : Measure α) (f : α → ENNReal) : μ.withDensity f ≪ μ

recall MeasureTheory.withDensity_absolutelyContinuous' {α : Type u_1}
    {m₀ : MeasurableSpace α} {μ : Measure α} {f : α → ENNReal}
    (hf : AEMeasurable f μ) (hf_ne_zero : ∀ᵐ x ∂μ, f x ≠ 0) : μ ≪ μ.withDensity f

recall MeasureTheory.Measure.rnDeriv_withDensity {α : Type u_1}
    {m : MeasurableSpace α} (ν : Measure α) [SigmaFinite ν] {f : α → ENNReal}
    (hf : Measurable f) : (ν.withDensity f).rnDeriv ν =ᵐ[ν] f

recall MeasureTheory.withDensity_apply {α : Type u_1} {m₀ : MeasurableSpace α}
    {μ : Measure α} (f : α → ENNReal) {s : Set α} (hs : MeasurableSet s) :
    μ.withDensity f s = ∫⁻ a in s, f a ∂μ

recall MeasureTheory.Measure.restrict_univ {α : Type u_2} {m₀ : MeasurableSpace α}
    {μ : Measure α} : μ.restrict Set.univ = μ

recall MeasureTheory.IsProbabilityMeasure.measure_univ {α : Type u_1}
    {m₀ : MeasurableSpace α} {μ : Measure α} [IsProbabilityMeasure μ] : μ Set.univ = 1

recall MeasureTheory.lintegral_ofReal_ne_top_iff_integrable {α : Type u_1}
    {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hfm : AEStronglyMeasurable f μ) (hf : 0 ≤ᵐ[μ] f) :
    (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≠ ⊤ ↔ Integrable f μ

recall MeasureTheory.integral_eq_lintegral_of_nonneg_ae {α : Type u_1}
    {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : 0 ≤ᵐ[μ] f) (hfm : AEStronglyMeasurable f μ) :
    ∫ a, f a ∂μ = (∫⁻ a, ENNReal.ofReal (f a) ∂μ).toReal

recall ENNReal.toReal_ofReal {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r

recall Real.log_exp (x : ℝ) : Real.log (Real.exp x) = x

recall ContinuousLinearMap.flip_apply {𝕜 : Type u_1} {𝕜₂ : Type u_2}
    {𝕜₃ : Type u_3} {E : Type u_4} {F : Type u_6} {G : Type u_8}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]
    [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
    [NontriviallyNormedField 𝕜₃] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F]
    [NormedSpace 𝕜₃ G] {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
    (f : E →SL[σ₁₃] F →SL[σ₂₃] G) (x : E) (y : F) : f.flip y x = f x y

recall ContinuousLinearMap.lpPairing_eq_integral {α : Type u_1} {𝕜 : Type u_2}
    {E : Type u_3} {F : Type u_4} {G : Type u_5} {m : MeasurableSpace α}
    {μ : Measure α} {p q : ENNReal} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]
    (B : E →L[𝕜] F →L[𝕜] G) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [p.HolderConjugate q] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G]
    [CompleteSpace G] (f : Lp E p μ) (g : Lp F q μ) :
    B.lpPairing μ p q f g = ∫ x, B (f x) (g x) ∂μ

recall MeasureTheory.integral_congr_ae {α : Type u_1} {G : Type u_5}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α}
    {μ : Measure α} {f g : α → G} (h : f =ᵐ[μ] g) :
    ∫ a, f a ∂μ = ∫ a, g a ∂μ

recall MeasureTheory.integral_sub {α : Type u_1} {G : Type u_5}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α}
    {μ : Measure α} {f g : α → G} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∫ a, f a - g a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ

recall ProbabilityTheory.IsGaussian.integral_dual {E : Type u_1}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsGaussian μ] [CompleteSpace E] [SecondCountableTopology E]
    (L : StrongDual ℝ E) : ∫ x, L x ∂μ = L (∫ x, x ∂μ)

recall Submodule.topologicalClosure_minimal {R : Type u} {M : Type v} [Semiring R]
    [TopologicalSpace M] [AddCommMonoid M] [Module R M] [ContinuousConstSMul R M]
    [ContinuousAdd M] (s : Submodule R M) {t : Submodule R M} (h : s ≤ t)
    (ht : IsClosed (t : Set M)) : s.topologicalClosure ≤ t

recall ContinuousLinearMap.isClosed_ker {R₁ : Type u_1} {R₂ : Type u_2}
    [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}
    [TopologicalSpace M₁] [AddCommMonoid M₁] {M₂ : Type u_6}
    [TopologicalSpace M₂] [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂]
    [T1Space M₂] (f : M₁ →SL[σ₁₂] M₂) : IsClosed (f.ker : Set M₁)

recall ProbabilityTheory.variance_of_integral_eq_zero {Ω : Type u_1}
    {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}
    (hX : AEMeasurable X μ) (hXint : ∫ x, X x ∂μ = 0) :
    Var[X; μ] = ∫ ω, X ω ^ 2 ∂μ

recall MeasureTheory.Lp.aestronglyMeasurable {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E p μ) : AEStronglyMeasurable ⇑f μ

recall MeasureTheory.AEStronglyMeasurable.aemeasurable {α : Type u_1}
    {m₀ : MeasurableSpace α} {μ : Measure α} {β : Type u_5} [MeasurableSpace β]
    [TopologicalSpace β] [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β]
    {f : α → β} (hf : AEStronglyMeasurable f μ) : AEMeasurable f μ

recall MeasureTheory.L2.inner_def {α : Type u_1} {E : Type u_2}
    {𝕜 : Type u_4} [RCLike 𝕜] {m : MeasurableSpace α} {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] (f g : Lp E 2 μ) :
    inner 𝕜 f g = ∫ a, inner 𝕜 (f a) (g a) ∂μ

recall real_inner_self_eq_norm_sq {F : Type u_3} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : inner ℝ x x = ‖x‖ ^ 2

recall MeasureTheory.withDensity_one {α : Type u_1} {m₀ : MeasurableSpace α}
    {μ : Measure α} : μ.withDensity 1 = μ

recall ProbabilityTheory.mgf_gaussianReal {Ω : Type u_1}
    {mΩ : MeasurableSpace Ω} {p : Measure Ω} {μ : ℝ} {v : NNReal} {X : Ω → ℝ}
    (hX : Measure.map X p = gaussianReal μ v) (t : ℝ) :
    mgf X p t = Real.exp (μ * t + (v : ℝ) * t ^ 2 / 2)

recall ProbabilityTheory.HasGaussianLaw.map_eq_gaussianReal {Ω : Type u_1}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}
    (h : HasGaussianLaw X P) :
    Measure.map X P = gaussianReal (∫ x, X x ∂P) (Var[X; P]).toNNReal

recall Real.coe_toNNReal (r : ℝ) (hr : 0 ≤ r) : (r.toNNReal : ℝ) = r

recall ProbabilityTheory.variance_nonneg {Ω : Type u_1} {mΩ : MeasurableSpace Ω}
    (X : Ω → ℝ) (μ : Measure Ω) : 0 ≤ Var[X; μ]

recall Real.exp_sub (x y : ℝ) : Real.exp (x - y) = Real.exp x / Real.exp y

recall MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_charFun {E : Type u_1}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ₀ : ProbabilityMeasure E}
    {μ : ℕ → ProbabilityMeasure E}
    (h : ∀ t, Tendsto (fun n ↦ charFun (↑(μ n) : Measure E) t) atTop
      (𝓝 (charFun (↑μ₀ : Measure E) t))) :
    Tendsto μ atTop (𝓝 μ₀)

recall ProbabilityTheory.charFun_gaussianReal {μ : ℝ} {v : NNReal} (t : ℝ) :
    charFun (gaussianReal μ v) t =
      Complex.exp (t * μ * Complex.I - (v : ℂ) * t ^ 2 / 2)

recall NNReal.tendsto_coe {α : Type u_2} {f : Filter α} {m : α → NNReal}
    {x : NNReal} : Tendsto (fun a ↦ (m a : ℝ)) f (𝓝 (x : ℝ)) ↔
    Tendsto m f (𝓝 x)

recall MeasureTheory.Measure.isProbabilityMeasure_map {α : Type u_1} {β : Type u_2}
    {m₀ : MeasurableSpace α} [MeasurableSpace β] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → β} (hf : AEMeasurable f μ) :
    IsProbabilityMeasure (μ.map f)

recall ProbabilityTheory.variance_eq_integral {Ω : Type u_1}
    {mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}
    (hX : AEMeasurable X μ) : Var[X; μ] = ∫ ω, (X ω - ∫ x, X x ∂μ) ^ 2 ∂μ

recall ProbabilityTheory.HasGaussianLaw.congr {Ω : Type u_1} {E : Type u_2}
    {mΩ : MeasurableSpace Ω} {P : Measure Ω} [TopologicalSpace E]
    [AddCommMonoid E] [Module ℝ E] [mE : MeasurableSpace E] {X Y : Ω → E}
    (hX : HasGaussianLaw X P) (h : X =ᵐ[P] Y) : HasGaussianLaw Y P

recall MeasureTheory.Measure.map_map {α : Type u_1} {β : Type u_2}
    {γ : Type u_3} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ : Measure α} {g : β → γ} {f : α → β}
    (hg : Measurable g) (hf : Measurable f) :
    Measure.map g (Measure.map f μ) = Measure.map (g ∘ f) μ

recall ProbabilityTheory.IsGaussian.memLp_dual {E : Type u_1}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [IsGaussian μ] (L : StrongDual ℝ E) (p : ENNReal)
    (hp : p ≠ ⊤) : MemLp L p μ

recall MeasureTheory.memLp_one_iff_integrable {α : Type u_1} {ε : Type u_5}
    {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε]
    [ContinuousENorm ε] {f : α → ε} : MemLp f 1 μ ↔ Integrable f μ

recall mem_closure_iff_seq_limit {X : Type u_1} [TopologicalSpace X]
    [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ x, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a)

recall MeasureTheory.tendstoInMeasure_of_tendsto_Lp {α : Type u_1}
    {ι : Type u_2} {E : Type u_4} {m : MeasurableSpace α} {μ : Measure α}
    {p : ENNReal} [NormedAddCommGroup E] [hp : Fact (1 ≤ p)] {f : ι → Lp E p μ}
    {g : Lp E p μ} {l : Filter ι} (hfg : Tendsto f l (𝓝 g)) :
    TendstoInMeasure μ (fun n ↦ (f n : α → E)) l (g : α → E)

recall MeasureTheory.TendstoInMeasure.tendstoInDistribution {ι : Type u_1}
    {E : Type u_2} {Ω' : Type u_3} {m' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    [IsProbabilityMeasure μ'] {mE : MeasurableSpace E} {Z : Ω' → E}
    {l : Filter ι} [PseudoEMetricSpace E] [BorelSpace E] [l.IsCountablyGenerated]
    [l.NeBot] {X : ι → Ω' → E} (h : TendstoInMeasure μ' X l Z)
    (hX : ∀ i, AEMeasurable (X i) μ') :
    TendstoInDistribution X l Z (fun _ ↦ μ') μ'

recall tendsto_nhds_unique {X : Type u_1} {Y : Type u_2} [TopologicalSpace X]
    [T2Space X] {f : Y → X} {l : Filter Y} {a b : X} [l.NeBot]
    (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b

recall ProbabilityTheory.integrable_exp_mul_gaussianReal {μ : ℝ} {v : NNReal}
    (t : ℝ) : Integrable (fun x ↦ Real.exp (t * x)) (gaussianReal μ v)

recall MeasureTheory.Integrable.comp_aemeasurable {α : Type u_1} {ε : Type u_5}
    {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε]
    [ContinuousENorm ε] {α' : Type u_8} [MeasurableSpace α'] {f : α → α'}
    {g : α' → ε} (hg : Integrable g (μ.map f)) (hf : AEMeasurable f μ) :
    Integrable (g ∘ f) μ

recall MeasureTheory.Integrable.div_const {α : Type u_1} {m : MeasurableSpace α}
    {μ : Measure α} {𝕜 : Type u_8} [NormedDivisionRing 𝕜] {f : α → 𝕜}
    (h : Integrable f μ) (c : 𝕜) : Integrable (fun x ↦ f x / c) μ

recall MeasureTheory.Integrable.congr {α : Type u_1} {ε : Type u_5}
    {m : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε]
    [ContinuousENorm ε] {f g : α → ε} (hf : Integrable f μ) (h : f =ᵐ[μ] g) :
    Integrable g μ

recall MeasureTheory.integral_div {α : Type u_1} {m : MeasurableSpace α}
    {μ : Measure α} {L : Type u_6} [RCLike L] (r : L) (f : α → L) :
    ∫ a, f a / r ∂μ = (∫ a, f a ∂μ) / r

recall Real.exp_ne_zero (x : ℝ) : Real.exp x ≠ 0

recall MeasureTheory.ofReal_integral_eq_lintegral_ofReal {α : Type u_1}
    {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hfi : Integrable f μ) (f_nn : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ x, f x ∂μ) = ∫⁻ x, ENNReal.ofReal (f x) ∂μ

recall MeasureTheory.Lp.coeFn_neg {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    (f : Lp E p μ) : ⇑(-f) =ᵐ[μ] -f

recall Real.exp_add (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y

recall ENNReal.ofReal_mul {p q : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (p * q) = ENNReal.ofReal p * ENNReal.ofReal q

recall ENNReal.eq_div_iff {a b c : ENNReal} (ha : a ≠ 0) (ha' : a ≠ ⊤) :
    b = c / a ↔ a * b = c

recall norm_neg {E : Type u_5} [SeminormedAddGroup E] (a : E) : ‖-a‖ = ‖a‖

recall ProbabilityTheory.eqOn_complexMGF_of_mgf {Ω : Type u_1} {m : MeasurableSpace Ω}
    {X : Ω → ℝ} {μ : Measure Ω} {Ω' : Type u_3} {mΩ' : MeasurableSpace Ω'}
    {Y : Ω' → ℝ} {μ' : Measure Ω'} [IsProbabilityMeasure μ]
    (hXY : mgf X μ = mgf Y μ') :
    Set.EqOn (complexMGF X μ) (complexMGF Y μ')
      {z | z.re ∈ interior (integrableExpSet X μ)}

recall MeasureTheory.Measure.ext_of_complexMGF_eq {Ω : Type u_1}
    {m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : Measure Ω}
    {Ω' : Type u_3} {mΩ' : MeasurableSpace Ω'} {Y : Ω' → ℝ} {μ' : Measure Ω'}
    [IsFiniteMeasure μ] [IsFiniteMeasure μ'] (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ') (h : complexMGF X μ = complexMGF Y μ') :
    Measure.map X μ = Measure.map Y μ'

recall MeasureTheory.charFunDual_eq_charFun_map_one {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
    {μ : Measure E} [OpensMeasurableSpace E] (L : StrongDual ℝ E) :
    charFunDual μ L = charFun (Measure.map (L : E → ℝ) μ) 1

recall MeasureTheory.Measure.ext_of_charFunDual {E : Type u_2}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {mE : MeasurableSpace E}
    [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {μ ν : Measure E}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (h : charFunDual μ = charFunDual ν) : μ = ν

recall MeasureTheory.integral_exp_tilted {α : Type u_1} {mα : MeasurableSpace α} {μ : Measure α}
    (f g : α → ℝ) :
    ∫ x, Real.exp (g x) ∂(μ.tilted f) = (∫ x, Real.exp ((f + g) x) ∂μ) / ∫ x, Real.exp (f x) ∂μ

recall ProbabilityTheory.gaussianReal_map_add_const {μ : ℝ} {v : ℝ≥0} (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v

recall MeasureTheory.isProbabilityMeasure_tilted {α : Type u_1} {mα : MeasurableSpace α}
    {μ : Measure α} {f : α → ℝ} [NeZero μ] (hf : Integrable (fun x ↦ Real.exp (f x)) μ) :
    IsProbabilityMeasure (μ.tilted f)

recall MeasureTheory.Measure.map_congr {α : Type u_1} {β : Type u_2} {mα : MeasurableSpace α}
    {mβ : MeasurableSpace β} {μ : Measure α} {f g : α → β} (h : f =ᵐ[μ] g) : μ.map f = μ.map g

recall MeasureTheory.Lp.coeFn_add {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    (f g : Lp E p μ) : ⇑(f + g) =ᵐ[μ] ⇑f + ⇑g

recall MeasureTheory.Lp.coeFn_smul {α : Type u_1} {𝕜 : Type u_2} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α} [NormedAddCommGroup E]
    [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] (c : 𝕜) (f : Lp E p μ) :
    ⇑(c • f) =ᵐ[μ] c • ⇑f

recall norm_add_sq_real {F : Type u_3} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x y : F) :
    ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x y + ‖y‖ ^ 2

recall real_inner_smul_right {F : Type u_3} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x y : F) (r : ℝ) : inner ℝ x (r • y) = r * inner ℝ x y

recall MeasureTheory.Measure.map_id {α : Type u_1} {mα : MeasurableSpace α}
    {μ : Measure α} : Measure.map id μ = μ

recall MeasureTheory.integral_const_mul {α : Type u_1} {m : MeasurableSpace α}
    {μ : Measure α} {L : Type u_6} [RCLike L] (r : L) (f : α → L) :
    ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ

namespace Malliavin.CameronMartin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]

private theorem map_eq_gaussianReal_of_mgf_eq
    {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsFiniteMeasure ν]
    {X : Ω → ℝ} (hX : AEMeasurable X ν) (m : ℝ) (v : ℝ≥0)
    (hmgf : mgf X ν = mgf id (gaussianReal m v)) :
    ν.map X = gaussianReal m v := by
  have heqOn := eqOn_complexMGF_of_mgf hmgf.symm
  have hcomplex : complexMGF id (gaussianReal m v) = complexMGF X ν := by
    funext z
    apply heqOn
    simp only [integrableExpSet_id_gaussianReal, interior_univ, Set.mem_univ, Set.ofPred_true]
  have hmap := Measure.ext_of_complexMGF_eq aemeasurable_id hX hcomplex
  simpa only [Measure.map_id] using hmap.symm

private theorem measure_eq_of_forall_map_dual_eq
    {μ ν : Measure W} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hproj : ∀ L : StrongDual ℝ W, μ.map L = ν.map L) : μ = ν := by
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, hproj L]

/-- The exponent in the Cameron--Martin density. -/
def densityExponent (h : Space μ) (x : W) : ℝ :=
  (h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2

/-- The real-valued, strictly positive Cameron--Martin density. -/
def realDensity (h : Space μ) (x : W) : ℝ :=
  Real.exp (densityExponent μ h x)

/-- The Cameron--Martin density, as an `ℝ≥0∞`-valued function suitable for `withDensity`. -/
def density (h : Space μ) (x : W) : ℝ≥0∞ :=
  ENNReal.ofReal (realDensity μ h x)

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The canonical representative of the density exponent is measurable. -/
theorem measurable_densityExponent (h : Space μ) :
    Measurable (densityExponent μ h) := by
  exact (Lp.stronglyMeasurable (h : Lp ℝ 2 μ)).measurable.sub_const _

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued Cameron--Martin density is measurable. -/
theorem measurable_realDensity (h : Space μ) : Measurable (realDensity μ h) := by
  exact (measurable_densityExponent μ h).exp

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued density is strongly measurable, hence also strongly measurable almost
everywhere for every reference measure on `W`. -/
theorem aestronglyMeasurable_realDensity (h : Space μ) :
    AEStronglyMeasurable (realDensity μ h) μ := by
  exact ⟨realDensity μ h, (measurable_realDensity μ h).stronglyMeasurable,
    Filter.EventuallyEq.rfl⟩

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The Cameron--Martin density is measurable. -/
theorem measurable_density (h : Space μ) : Measurable (density μ h) := by
  exact (measurable_realDensity μ h).ennreal_ofReal

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real-valued Cameron--Martin density is everywhere strictly positive. -/
theorem realDensity_pos (h : Space μ) (x : W) : 0 < realDensity μ h x :=
  Real.exp_pos _

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A Cameron--Martin density is everywhere strictly positive. -/
theorem density_ne_zero (h : Space μ) (x : W) : density μ h x ≠ 0 := by
  rw [density, ENNReal.ofReal_ne_zero_iff]
  exact realDensity_pos μ h x

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- A Cameron--Martin density is finite everywhere. -/
theorem density_ne_top (h : Space μ) (x : W) : density μ h x ≠ ∞ :=
  ENNReal.ofReal_ne_top

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- Converting the extended nonnegative density back to `ℝ` recovers `realDensity`. -/
@[simp]
theorem density_toReal (h : Space μ) (x : W) :
    (density μ h x).toReal = realDensity μ h x := by
  exact ENNReal.toReal_ofReal (realDensity_pos μ h x).le

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the density exponent vanishes pointwise. -/
@[simp]
theorem densityExponent_zero (x : W) :
    densityExponent μ (0 : Space μ) x = 0 := by
  simp only [densityExponent, ZeroMemClass.coe_zero, AEEqFun.coeFn_zero_eq, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_self]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the real-valued density is one. -/
@[simp]
theorem realDensity_zero (x : W) : realDensity μ (0 : Space μ) x = 1 := by
  simp only [realDensity, densityExponent_zero, Real.exp_zero]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- At the zero Cameron--Martin vector the extended nonnegative density is one. -/
@[simp]
theorem density_zero (x : W) : density μ (0 : Space μ) x = 1 := by
  simp only [density, realDensity_zero, ENNReal.ofReal_one]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The density exponent at the negative Cameron--Martin vector, almost everywhere. -/
theorem densityExponent_neg_ae (h : Space μ) :
    densityExponent μ (-h) =ᵐ[μ]
      fun x ↦ -(h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2 := by
  filter_upwards [Lp.coeFn_neg (h : Lp ℝ 2 μ)] with x hx
  change (((-h : Space μ) : Lp ℝ 2 μ) : W → ℝ) x =
    -((h : Lp ℝ 2 μ) : W → ℝ) x at hx
  simp only [densityExponent, norm_neg]
  rw [hx]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The product of the real densities at opposite shifts is constant almost everywhere. -/
theorem realDensity_mul_neg_ae (h : Space μ) :
    (fun x ↦ realDensity μ h x * realDensity μ (-h) x) =ᵐ[μ]
      fun _ ↦ Real.exp (-‖h‖ ^ 2) := by
  filter_upwards [densityExponent_neg_ae μ h] with x hx
  simp only [realDensity]
  rw [hx, ← Real.exp_add]
  congr 1
  simp only [densityExponent]
  ring

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The product of the extended densities at opposite shifts is constant almost everywhere. -/
theorem density_mul_neg_ae (h : Space μ) :
    (fun x ↦ density μ h x * density μ (-h) x) =ᵐ[μ]
      fun _ ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) := by
  filter_upwards [realDensity_mul_neg_ae μ h] with x hx
  simp only [density]
  rw [← ENNReal.ofReal_mul (realDensity_pos μ h x).le, hx]

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The real density of the opposite shift is a reciprocal density, almost everywhere. -/
theorem realDensity_neg_eq_div_ae (h : Space μ) :
    realDensity μ (-h) =ᵐ[μ]
      fun x ↦ Real.exp (-‖h‖ ^ 2) / realDensity μ h x := by
  filter_upwards [realDensity_mul_neg_ae μ h] with x hx
  apply (eq_div_iff (realDensity_pos μ h x).ne').2
  simpa only [mul_comm] using hx

omit [CompleteSpace W] [SecondCountableTopology W] in
/-- The extended density of the opposite shift is a reciprocal density, almost everywhere. -/
theorem density_neg_eq_div_ae (h : Space μ) :
    density μ (-h) =ᵐ[μ]
      fun x ↦ ENNReal.ofReal (Real.exp (-‖h‖ ^ 2)) / density μ h x := by
  filter_upwards [density_mul_neg_ae μ h] with x hx
  apply (ENNReal.eq_div_iff (density_ne_zero μ h x)
    (density_ne_top μ h x)).2
  exact hx

/-- Translation by the zero Cameron--Martin vector leaves the measure unchanged. -/
@[simp]
theorem translated_zero : translated μ (0 : Space μ) = μ := by
  simp only [translated, inclusion_apply, ZeroMemClass.coe_zero, AEEqFun.coeFn_zero_eq, zero_smul,
    integral_zero, translatedMeasure_zero]

/-- The Cameron--Martin formula holds at the zero vector without any analytic input. -/
theorem translated_eq_withDensity_zero :
    translated μ (0 : Space μ) = μ.withDensity (density μ (0 : Space μ)) := by
  rw [translated_zero, funext (density_zero μ)]
  exact withDensity_one.symm

/-! ### Centering and variance of the first chaos -/

/-- Expectation as a continuous linear functional on scalar `L²(μ)`. -/
noncomputable def expectationMap : Lp ℝ 2 μ →L[ℝ] ℝ :=
  ((ContinuousLinearMap.mul ℝ ℝ).lpPairing μ 2 2).flip (Lp.const 2 μ 1)

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- `expectationMap` agrees with the Bochner integral of the canonical `L²` representative. -/
@[simp]
theorem expectationMap_apply (f : Lp ℝ 2 μ) :
    expectationMap μ f = ∫ x, f x ∂μ := by
  rw [expectationMap, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  simp only [Lp.const_val, AEEqFun.coeFn_const_eq, ContinuousLinearMap.mul_apply', mul_one]

/-- Centered continuous linear functionals have expectation zero. -/
theorem expectationMap_centeredDual (L : StrongDual ℝ W) :
    expectationMap μ (centeredDualToLp μ L) = 0 := by
  rw [expectationMap_apply]
  rw [integral_congr_ae (centeredDualToLp_ae_eq μ L)]
  rw [integral_sub (by fun_prop) (by fun_prop)]
  rw [IsGaussian.integral_dual]
  simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- Every element of the closed first chaos has expectation zero. -/
theorem expectationMap_firstChaos (h : Space μ) :
    expectationMap μ (h : Lp ℝ 2 μ) = 0 := by
  have hle : firstChaos μ ≤ (expectationMap μ).ker := by
    unfold firstChaos
    apply Submodule.topologicalClosure_minimal
    · rintro f ⟨L, rfl⟩
      exact expectationMap_centeredDual μ L
    · exact (expectationMap μ).isClosed_ker
  exact hle h.property

/-- The canonical representative of every first-chaos element is centered. -/
theorem integral_coe_eq_zero (h : Space μ) :
    ∫ x, (h : Lp ℝ 2 μ) x ∂μ = 0 := by
  rw [← expectationMap_apply]
  exact expectationMap_firstChaos μ h

/-- The variance of a first-chaos element is the square of its Hilbert norm. -/
theorem variance_coe_eq_norm_sq (h : Space μ) :
    Var[fun x ↦ (h : Lp ℝ 2 μ) x; μ] = ‖h‖ ^ 2 := by
  rw [variance_of_integral_eq_zero
    (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable
    (integral_coe_eq_zero μ h)]
  calc
    ∫ x, (h : Lp ℝ 2 μ) x ^ 2 ∂μ =
        @inner ℝ _ _ (h : Lp ℝ 2 μ) (h : Lp ℝ 2 μ) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards with x
      simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
        abs_mul_abs_self]
    _ = ‖(h : Lp ℝ 2 μ)‖ ^ 2 := real_inner_self_eq_norm_sq _
    _ = ‖h‖ ^ 2 := by rfl

/-! ### Gaussianity of the closed first chaos -/

/-- A centered real Gaussian law, bundled as a probability measure. -/
private noncomputable def centeredGaussianPM (v : ℝ≥0) : ProbabilityMeasure ℝ :=
  ⟨gaussianReal 0 v, inferInstance⟩

/-- Centered real Gaussian laws vary continuously with their variance. -/
private lemma tendsto_centeredGaussianPM {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (hv : Tendsto v atTop (𝓝 v₀)) :
    Tendsto (fun n ↦ centeredGaussianPM (v n)) atTop (𝓝 (centeredGaussianPM v₀)) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_charFun
  intro t
  simp only [centeredGaussianPM, ProbabilityMeasure.coe_mk,
    charFun_gaussianReal, Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  have hvR : Tendsto (fun n ↦ (v n : ℝ)) atTop (𝓝 (v₀ : ℝ)) :=
    NNReal.tendsto_coe.mpr hv
  exact (((hvR.ofReal.mul_const ((t : ℂ) ^ 2)).div_const 2).neg).cexp

/-- The law of a real random variable, bundled as a probability measure. -/
private noncomputable def lawPM {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℝ)
    (hf : AEMeasurable f μ) : ProbabilityMeasure ℝ :=
  ⟨μ.map f, Measure.isProbabilityMeasure_map hf⟩

private theorem variance_coe_L2_eq_norm_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    Var[(f : Ω → ℝ); μ] = ‖f‖ ^ 2 := by
  rw [variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable, hf₀]
  simp only [sub_zero]
  rw [← real_inner_self_eq_norm_sq f, L2.inner_def]
  congr 1
  funext x
  simp only [pow_two, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
    abs_mul_abs_self]

/-- A centered Gaussian element of `L²(μ)` has law `N(0, ‖f‖²)`. -/
lemma law_eq_centeredGaussian {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Lp ℝ 2 μ)
    (hfG : HasGaussianLaw (f : Ω → ℝ) μ) (hf₀ : ∫ x, f x ∂μ = 0) :
    μ.map (f : Ω → ℝ) = gaussianReal 0 (‖f‖₊ ^ 2) := by
  rw [hfG.map_eq_gaussianReal, hf₀, variance_coe_L2_eq_norm_sq μ f hf₀]
  congr 1
  apply NNReal.eq
  simp only [Real.coe_toNNReal _ (sq_nonneg _), NNReal.coe_pow, coe_nnnorm]

/-- A limit in `L²` of centered Gaussian random variables is Gaussian. -/
lemma hasGaussianLaw_L2_limit_of_centered
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {f : ℕ → Lp ℝ 2 μ} {g : Lp ℝ 2 μ} (hfg : Tendsto f atTop (𝓝 g))
    (hfG : ∀ n, HasGaussianLaw (f n : Ω → ℝ) μ)
    (hf₀ : ∀ n, ∫ x, f n x ∂μ = 0) : HasGaussianLaw (g : Ω → ℝ) μ := by
  have hdist := (tendstoInMeasure_of_tendsto_Lp hfg).tendstoInDistribution
    (fun n ↦ (Lp.aestronglyMeasurable (f n)).aemeasurable)
  have hlaw : Tendsto
      (fun n ↦ lawPM μ (f n : Ω → ℝ)
        (Lp.aestronglyMeasurable (f n)).aemeasurable) atTop
      (𝓝 (lawPM μ (g : Ω → ℝ) (Lp.aestronglyMeasurable g).aemeasurable)) :=
    hdist.tendsto
  have hv : Tendsto (fun n ↦ ‖f n‖₊ ^ 2) atTop (𝓝 (‖g‖₊ ^ 2)) :=
    hfg.nnnorm.pow 2
  have hgauss := tendsto_centeredGaussianPM hv
  have heq : (fun n ↦ lawPM μ (f n : Ω → ℝ)
      (Lp.aestronglyMeasurable (f n)).aemeasurable) =
      fun n ↦ centeredGaussianPM (‖f n‖₊ ^ 2) := by
    funext n
    apply Subtype.ext
    exact law_eq_centeredGaussian μ (f n) (hfG n) (hf₀ n)
  rw [heq] at hlaw
  have hprobEq := tendsto_nhds_unique hlaw hgauss
  have hmeasureEq : μ.map (g : Ω → ℝ) = gaussianReal 0 (‖g‖₊ ^ 2) :=
    congrArg Subtype.val hprobEq
  refine ⟨?_⟩
  rw [hmeasureEq]
  infer_instance

private theorem hasGaussianLaw_centeredDualToLp (L : StrongDual ℝ W) :
    HasGaussianLaw ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ) μ := by
  apply HasGaussianLaw.congr (Y :=
    ((centeredDualToLp μ L : Lp ℝ 2 μ) : W → ℝ)) ?_
    (centeredDualToLp_ae_eq μ L).symm
  refine ⟨?_⟩
  have h_eq :
      μ.map (fun x ↦ L x - L (mean μ)) =
        (μ.map L).map (fun y ↦ y - L (mean μ)) := by
    calc
      μ.map (fun x ↦ L x - L (mean μ)) =
          μ.map ((fun y ↦ y - L (mean μ)) ∘ L) := rfl
      _ = (μ.map L).map (fun y ↦ y - L (mean μ)) :=
        (Measure.map_map (measurable_id.sub_const _) L.measurable).symm
  rw [h_eq]
  infer_instance

private theorem integral_centeredDualToLp_eq_zero (L : StrongDual ℝ W) :
    ∫ x, (centeredDualToLp μ L : Lp ℝ 2 μ) x ∂μ = 0 := by
  rw [integral_congr_ae (centeredDualToLp_ae_eq μ L)]
  have hL : Integrable L μ :=
    memLp_one_iff_integrable.mp (IsGaussian.memLp_dual μ L 1 (by norm_num))
  rw [integral_sub hL (integrable_const (L (mean μ)))]
  rw [IsGaussian.integral_dual L]
  simp only [mean, integral_const, probReal_univ, smul_eq_mul, one_mul, sub_self]

/-- Every Cameron--Martin-space representative belongs to the closed Gaussian first chaos. -/
theorem space_hasGaussianLaw (h : Space μ) :
    HasGaussianLaw ((h : Lp ℝ 2 μ) : W → ℝ) μ := by
  rcases mem_closure_iff_seq_limit.mp h.property with ⟨f, hf_range, hf_tendsto⟩
  choose L hL using hf_range
  apply hasGaussianLaw_L2_limit_of_centered μ hf_tendsto
  · intro n
    rw [← hL n]
    exact hasGaussianLaw_centeredDualToLp μ (L n)
  · intro n
    rw [← hL n]
    exact integral_centeredDualToLp_eq_zero μ (L n)

/-- The law of a first-chaos representative is the centered real Gaussian whose variance is its
squared `L²` norm. -/
theorem map_coe_eq_gaussianReal (h : Space μ) :
    μ.map ((h : Lp ℝ 2 μ) : W → ℝ) = gaussianReal 0 (‖h‖₊ ^ 2) := by
  calc
    μ.map ((h : Lp ℝ 2 μ) : W → ℝ) =
        gaussianReal 0 (‖(h : Lp ℝ 2 μ)‖₊ ^ 2) :=
      law_eq_centeredGaussian μ (h : Lp ℝ 2 μ)
        (space_hasGaussianLaw μ h) (integral_coe_eq_zero μ h)
    _ = gaussianReal 0 (‖h‖₊ ^ 2) := by rfl

/-- The exponential moment of a first-chaos representative is its Gaussian normalizer. -/
theorem integral_exp_coe (h : Space μ) :
    ∫ x, Real.exp ((h : Lp ℝ 2 μ) x) ∂μ = Real.exp (‖h‖ ^ 2 / 2) := by
  have hmgf := mgf_gaussianReal (space_hasGaussianLaw μ h).map_eq_gaussianReal 1
  rw [integral_coe_eq_zero μ h, Real.coe_toNNReal _
    (variance_nonneg (fun x ↦ (h : Lp ℝ 2 μ) x) μ),
    variance_coe_eq_norm_sq μ h] at hmgf
  simpa [mgf] using hmgf

/-- The exponential of a first-chaos representative is integrable. -/
theorem integrable_exp_coe (h : Space μ) :
    Integrable (fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x)) μ := by
  have hi : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (gaussianReal 0 (‖h‖₊ ^ 2)) := integrable_exp_mul_gaussianReal 1
  have himap : Integrable (fun y : ℝ ↦ Real.exp (1 * y))
      (μ.map ((h : Lp ℝ 2 μ) : W → ℝ)) := by
    rw [map_coe_eq_gaussianReal μ h]
    exact hi
  change Integrable ((fun y : ℝ ↦ Real.exp y) ∘
    ((h : Lp ℝ 2 μ) : W → ℝ)) μ
  simpa only [one_mul] using
    himap.comp_aemeasurable (Lp.aestronglyMeasurable (h : Lp ℝ 2 μ)).aemeasurable

/-- The real-valued Cameron--Martin density is integrable. -/
theorem integrable_realDensity (h : Space μ) : Integrable (realDensity μ h) μ := by
  have hi := (integrable_exp_coe μ h).div_const
    (Real.exp (‖h‖ ^ 2 / 2))
  apply hi.congr
  filter_upwards with x
  simp only [realDensity, densityExponent, Real.exp_sub]

/-- The real-valued Cameron--Martin density has expectation one. -/
theorem integral_realDensity (h : Space μ) : ∫ x, realDensity μ h x ∂μ = 1 := by
  rw [show realDensity μ h = fun x ↦ Real.exp ((h : Lp ℝ 2 μ) x) /
      Real.exp (‖h‖ ^ 2 / 2) by
        funext x
        simp only [realDensity, densityExponent, Real.exp_sub]]
  rw [integral_div, integral_exp_coe μ h]
  exact div_self (Real.exp_ne_zero _)

/-- The Cameron--Martin density integrates to one. -/
theorem lintegral_density (h : Space μ) : ∫⁻ x, density μ h x ∂μ = 1 := by
  change (∫⁻ x, ENNReal.ofReal (realDensity μ h x) ∂μ) = 1
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_realDensity μ h)
    (Filter.Eventually.of_forall fun x ↦ (realDensity_pos μ h x).le)]
  rw [integral_realDensity μ h]
  simp only [ENNReal.ofReal_one]

/-- Reduction of the Cameron--Martin density formula to the shift-versus-tilt identity.  Gaussian
closure of the first chaos and its MGF supply the normalizing factor. -/
theorem translated_eq_withDensity_of_eq_tilted (h : Space μ)
    (hshift : translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :
    translated μ h = μ.withDensity (density μ h) := by
  rw [hshift, Measure.tilted]
  congr with x
  rw [integral_exp_coe μ h]
  simp only [density, realDensity, densityExponent]
  rw [Real.exp_sub]

/-- The law of a continuous linear functional under the translated Gaussian measure: the
Gaussian with mean shifted by `L (inclusion μ h)` and unchanged variance `‖ofDual μ L‖²`. -/
theorem map_translated_dual (h : Space μ) (L : StrongDual ℝ W) :
    (translated μ h).map L =
      gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
  have hcoe : Measurable ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ) :=
    (Lp.stronglyMeasurable _).measurable
  calc (translated μ h).map L
      = μ.map (L ∘ translate (inclusion μ h)) := by
        unfold translated translatedMeasure
        rw [Measure.map_map L.continuous.measurable (measurable_translate _)]
    _ = μ.map ((fun y ↦ y + (L (mean μ) + L (inclusion μ h))) ∘
          ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)) := by
        apply Measure.map_congr
        filter_upwards [centeredDualToLp_ae_eq μ L] with x hx
        simp only [Function.comp_apply, translate, map_add, coe_ofDual, hx]
        ring
    _ = (μ.map ((ofDual μ L : Lp ℝ 2 μ) : W → ℝ)).map
          (fun y ↦ y + (L (mean μ) + L (inclusion μ h))) := by
        rw [Measure.map_map (by fun_prop) hcoe]
    _ = gaussianReal (L (mean μ) + L (inclusion μ h)) (‖ofDual μ L‖₊ ^ 2) := by
        rw [map_coe_eq_gaussianReal μ (ofDual μ L), gaussianReal_map_add_const, zero_add]

/-- The moment generating function of a continuous linear functional under the exponential
tilt by a first-chaos element: Gaussian with mean `L (mean μ) + ⟪ofDual μ L, h⟫` and variance
`‖ofDual μ L‖²`. -/
theorem mgf_tilted_dual (h : Space μ) (L : StrongDual ℝ W) (t : ℝ) :
    mgf L (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) t =
      Real.exp ((L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) * t +
        ((‖ofDual μ L‖₊ ^ 2 : ℝ≥0) : ℝ) * t ^ 2 / 2) := by
  set g : Space μ := ofDual μ L with hg
  have hnum : ∫ x, Real.exp (((fun x ↦ (h : Lp ℝ 2 μ) x) + fun x ↦ t * L x) x) ∂μ =
      Real.exp (t * L (mean μ)) * Real.exp (‖h + t • g‖ ^ 2 / 2) := by
    rw [← integral_exp_coe μ (h + t • g), ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [centeredDualToLp_ae_eq μ L,
      Lp.coeFn_add (h : Lp ℝ 2 μ) ((t • g : Space μ) : Lp ℝ 2 μ),
      Lp.coeFn_smul t (g : Lp ℝ 2 μ)] with x hx hadd hsmul
    simp only [Pi.add_apply]
    rw [← Real.exp_add, Submodule.coe_add, hadd, Pi.add_apply, Submodule.coe_smul, hsmul,
      Pi.smul_apply, hg, coe_ofDual, hx, smul_eq_mul]
    ring_nf
  have hsq : ‖h + t • g‖ ^ 2 = ‖h‖ ^ 2 + 2 * t * @inner ℝ _ _ g h + t ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_add_sq_real, Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_right,
      ← Submodule.coe_inner, real_inner_comm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  unfold mgf
  rw [integral_exp_tilted, hnum, integral_exp_coe μ h, hsq]
  simp only [coe_nnnorm, NNReal.coe_pow]
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-- The law of a continuous linear functional under the exponential tilt by a first-chaos
element. -/
theorem map_tilted_dual (h : Space μ) (L : StrongDual ℝ W) :
    (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)).map L =
      gaussianReal (L (mean μ) + @inner ℝ _ _ (ofDual μ L) h) (‖ofDual μ L‖₊ ^ 2) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  apply map_eq_gaussianReal_of_mgf_eq L.continuous.measurable.aemeasurable
  funext t
  rw [mgf_tilted_dual, mgf_gaussianReal Measure.map_id t]

/-- The analytic core of the Cameron--Martin theorem: translating by the covariance image of `h`
is the same as exponentially tilting by its first-chaos representative.  Both measures give
every continuous linear functional `L` the Gaussian law with mean `L (mean μ) + ⟪ofDual μ L, h⟫`
and variance `‖ofDual μ L‖²`, so they agree by `Measure.ext_of_charFunDual`. -/
theorem translated_eq_tilted (h : Space μ) :
    translated μ h = μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x) := by
  have : IsProbabilityMeasure (μ.tilted (fun x ↦ (h : Lp ℝ 2 μ) x)) :=
    isProbabilityMeasure_tilted (integrable_exp_coe μ h)
  have : IsProbabilityMeasure (translated μ h) :=
    Measure.isProbabilityMeasure_map (measurable_translate _).aemeasurable
  apply measure_eq_of_forall_map_dual_eq
  intro L
  rw [map_translated_dual, map_tilted_dual, apply_inclusion]

/-- The Cameron--Martin translation formula. -/
theorem translated_eq_withDensity (h : Space μ) :
    translated μ h = μ.withDensity (density μ h) := by
  exact translated_eq_withDensity_of_eq_tilted μ h (translated_eq_tilted μ h)

/-- The translated Gaussian law is absolutely continuous with respect to the original law. -/
theorem translated_absolutelyContinuous (h : Space μ) : translated μ h ≪ μ := by
  rw [translated_eq_withDensity]
  exact withDensity_absolutelyContinuous μ (density μ h)

/-- The original Gaussian law is absolutely continuous with respect to its Cameron--Martin
translation. -/
theorem absolutelyContinuous_translated (h : Space μ) : μ ≪ translated μ h := by
  rw [translated_eq_withDensity]
  exact withDensity_absolutelyContinuous' (measurable_density μ h).aemeasurable
    (Filter.Eventually.of_forall (density_ne_zero μ h))

/-- Translation by the ambient image of a Cameron--Martin vector preserves the measure class. -/
theorem isQuasiInvariantShift_inclusion (h : Space μ) :
    IsQuasiInvariantShift μ (inclusion μ h) := by
  exact ⟨translated_absolutelyContinuous μ h, absolutelyContinuous_translated μ h⟩

/-- The Radon--Nikodym derivative of the translated law is the Cameron--Martin density. -/
theorem rnDeriv_translated (h : Space μ) :
    (translated μ h).rnDeriv μ =ᵐ[μ] density μ h := by
  rw [translated_eq_withDensity]
  exact Measure.rnDeriv_withDensity μ (measurable_density μ h)

/-- The logarithmic Radon--Nikodym derivative is the first-chaos random variable minus half its
squared Cameron--Martin norm. -/
theorem logDensity_ae_eq (h : Space μ) :
    logDensity μ h =ᵐ[μ] densityExponent μ h := by
  unfold logDensity llr
  filter_upwards [rnDeriv_translated μ h] with x hx
  rw [hx]
  simp only [density_toReal, realDensity, Real.log_exp]

/-- Exponential moments of scalar multiples of a first-chaos representative. -/
theorem integrable_exp_mul_coe (h : Space μ) (c : ℝ) :
    Integrable (fun x ↦ Real.exp (c * (h : Lp ℝ 2 μ) x)) μ := by
  refine (integrable_exp_coe μ (c • h)).congr ?_
  filter_upwards [Lp.coeFn_smul c (h : Lp ℝ 2 μ)] with x hx
  rw [Submodule.coe_smul, hx, Pi.smul_apply, smul_eq_mul]

/-- **The Cameron--Martin translation formula for Bochner integrals**: for a continuous `F` and a
Cameron--Martin vector `h`, `∫ F (x + inclusion μ h) dμ = ∫ F x · exp (h x - ‖h‖² / 2) dμ`.
Without an integrability hypothesis this remains a formal Bochner-integral identity; Lean defines
the integral to be zero in a nonintegrable case. -/
theorem integral_add_inclusion {F : W → ℝ} (hF : Continuous F) (h : Space μ) :
    ∫ x, F (x + inclusion μ h) ∂μ =
      ∫ x, F x * Real.exp ((h : Lp ℝ 2 μ) x - ‖h‖ ^ 2 / 2) ∂μ := by
  have h1 : ∫ x, F (x + inclusion μ h) ∂μ = ∫ x, F x ∂(translated μ h) := by
    unfold translated translatedMeasure
    rw [integral_map (measurable_translate _).aemeasurable hF.aestronglyMeasurable]
    rfl
  rw [h1, translated_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    (measurable_density μ h) (Filter.Eventually.of_forall fun x ↦ (density_ne_top μ h x).lt_top)]
  congr 1
  funext x
  rw [density_toReal, smul_eq_mul, mul_comm]
  rfl

end Malliavin.CameronMartin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
