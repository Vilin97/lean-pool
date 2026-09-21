/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.TimeDerivative
import Mathlib.Probability.Process.Predictable

/-!
# An abstract Clark--Ocone representation contract

Assuming a `ClarkOconeFamily`, this file derives a conditional representation identity on an
abstract Wiener space carrying a Brownian coordinate process.
The time-space derivative is projected in product `L²` onto the predictable sigma-algebra using
Mathlib's genuine `condExpL2`.  No identification of its time sections with
`E[DₜF | 𝓕ₜ]` is proved here.  Instead, `integral_predictableProjection_Ioc` records the exact
conditional-moment identity on predictable rectangles, while `memLp_timeSection_ae` explains the
weaker almost-every-time section statement available for a chosen product-`L²` representative.
The separate fixed-time operator `filtrationCondExpL2` is identified almost everywhere with
Mathlib's function-valued conditional expectation by `filtrationCondExpL2_ae_eq_condExp`.

The identification of the Cameron--Martin space of the abstract Wiener measure with deterministic
`L²` time directions, and the corresponding Fubini map, are supplied by `TimeDerivative.lean`:
the time derivative `ClarkOconeFamily.timeDerivative` is constructed from the Brownian coordinates
(`Malliavin.timeDerivative`), not stipulated. The `ClarkOconeFamily` fields still package an
integration operator together with martingale representation and Malliavin--Itô duality. The
downstream `ItoConstruction.lean` constructs the natural-filtration integral independently; the
optional predicates
`ClarkOconeFamily.IsBrownianOnElementary` and
`ClarkOconeFamily.IsBrownianOnDeterministic` record compatibility with `B` on adapted elementary
and deterministic time integrands, respectively; the former implies the latter. Without one of
these hypotheses, the public identity and its centered/norm consequences concern the designated
contract operator rather than asserting that it is the constructed Brownian Itô integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

recall MeasureTheory.Lp.toLp_coeFn {α : Type u_1} {E : Type u_4}
    {m : MeasurableSpace α} {p : ENNReal} {μ : Measure α}
    [NormedAddCommGroup E] (f : Lp E p μ) (hf : MemLp (f : α → E) p μ) :
    hf.toLp (f : α → E) = f

recall MeasureTheory.MemLp.condExpL2_ae_eq_condExp
    {α : Type u_1} {E : Type u_3} {𝕜 : Type u_4} [RCLike 𝕜]
    {m m₀ : MeasurableSpace α} {μ : Measure α} {f : α → E}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [InnerProductSpace 𝕜 E] (hm : m ≤ m₀) (hf : MemLp f 2 μ)
    [IsFiniteMeasure μ] :
    (condExpL2 E 𝕜 hm hf.toLp : α → E) =ᵐ[μ] μ[f | m]

recall MeasureTheory.AEStronglyMeasurable.prodMk_left
    {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} {X : Type u_4} [TopologicalSpace X]
    [SFinite ν] {f : α × β → X} (hf : AEStronglyMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEStronglyMeasurable (fun y => f (x, y)) ν

recall MeasureTheory.MemLp.integrable_sq
    {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (h : MemLp f 2 μ) : Integrable (fun x => f x ^ 2) μ

recall MeasureTheory.Integrable.prod_right_ae
    {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [SFinite ν] [SFinite μ] ⦃f : α × β → E⦄
    (hf : Integrable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y => f (x, y)) ν

recall MeasureTheory.memLp_two_iff_integrable_sq
    {α : Type u_1} {m : MeasurableSpace α} {μ : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f μ) :
    MemLp f 2 μ ↔ Integrable (fun x => f x ^ 2) μ

recall MeasureTheory.integrableOn_Lp_of_measure_ne_top
    {α : Type u_1} {mα : MeasurableSpace α} {μ : Measure α}
    {E : Type u_4} [NormedAddCommGroup E] {p : ENNReal} {s : Set α}
    (f : Lp E p μ) (hp : 1 ≤ p) (hμs : μ s ≠ ∞) :
    IntegrableOn (f : α → E) s μ

recall MeasureTheory.setIntegral_prod
    {α : Type u_1} {β : Type u_2} {E : Type u_3}
    [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [NormedAddCommGroup E] [SFinite ν] [NormedSpace ℝ E] [SFinite μ]
    (f : α × β → E) {s : Set α} {t : Set β}
    (hf : IntegrableOn f (s ×ˢ t) (μ.prod ν)) :
    ∫ z in s ×ˢ t, f z ∂μ.prod ν = ∫ x in s, ∫ y in t, f (x, y) ∂ν ∂μ

recall MeasureTheory.integral_condExpL2_eq
    {α : Type u_1} {E' : Type u_3} {𝕜 : Type u_4} [RCLike 𝕜]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedSpace ℝ E'] {m m0 : MeasurableSpace α} {μ : Measure α} {s : Set α}
    (hm : m ≤ m0) (f : Lp E' 2 μ) (hs : MeasurableSet[m] s)
    (hμs : μ s ≠ ∞) :
    ∫ x in s, (condExpL2 E' 𝕜 hm f : α → E') x ∂μ = ∫ x in s, f x ∂μ

recall MeasureTheory.measurableSet_predictable_Ioc_prod
    {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω}
    [LinearOrder ι] [OrderBot ι] {𝓕 : Filtration ι m} (i j : ι) {s : Set Ω}
    (hs : MeasurableSet[𝓕 i] s) :
    MeasurableSet[𝓕.predictable] (Set.Ioc i j ×ˢ s)

recall MeasureTheory.Measure.prod_prod
    {α : Type u_1} {β : Type u_2} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν] (s : Set α) (t : Set β) :
    (μ.prod ν) (s ×ˢ t) = μ s * ν t

recall ProbabilityTheory.IsPreBrownianReal.indepFun_shift
    {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {B : NNReal → Ω → ℝ}
    {P : Measure Ω} (hB : IsPreBrownianReal B P) (t₀ : NNReal) :
    (fun ω (t : NNReal) => B (t₀ + t) ω - B t₀ ω) ⟂ᵢ[P]
      fun ω (t : Set.Iic t₀) => B (↑t) ω

recall MeasureTheory.Filtration.natural_eq_comap
    {Ω : Type u_1} {ι : Type u_2} {m : MeasurableSpace Ω}
    {β : ι → Type u_3} [(i : ι) → TopologicalSpace (β i)]
    [∀ i, TopologicalSpace.MetrizableSpace (β i)]
    [mβ : (i : ι) → MeasurableSpace (β i)] [∀ i, BorelSpace (β i)]
    [Preorder ι] (u : (i : ι) → Ω → β i)
    (hum : ∀ i, StronglyMeasurable (u i)) (i : ι) :
    (Filtration.natural u hum) i =
      MeasurableSpace.comap (fun ω (j : Set.Iic i) => u (↑j) ω) inferInstance

recall ProbabilityTheory.IndepFun_iff_Indep
    {Ω : Type u_1} {β : Type u_3} {γ : Type u_4}
    {_mΩ : MeasurableSpace Ω} [mβ : MeasurableSpace β] [mγ : MeasurableSpace γ]
    (f : Ω → β) (g : Ω → γ) (μ : Measure Ω) :
    IndepFun f g μ ↔
      Indep (MeasurableSpace.comap f mβ) (MeasurableSpace.comap g mγ) μ

recall ProbabilityTheory.indep_of_indep_of_le_right
    {Ω : Type u_1} {m₁ m₂ m₃ _mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (h_indep : Indep m₁ m₂ μ) (h32 : m₃ ≤ m₂) : Indep m₁ m₃ μ

recall ProbabilityTheory.IndepFun.comp
    {Ω : Type u_1} {β : Type u_6} {β' : Type u_7}
    {γ : Type u_8} {γ' : Type u_9}
    {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}
    {_mβ : MeasurableSpace β} {_mβ' : MeasurableSpace β'}
    {_mγ : MeasurableSpace γ} {_mγ' : MeasurableSpace γ'}
    {φ : β → γ} {ψ : β' → γ'}
    (hfg : IndepFun f g μ) (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (φ ∘ f) (ψ ∘ g) μ

recall ProbabilityTheory.IndepFun.congr
    {Ω : Type u_1} {β : Type u_6} {β' : Type u_7}
    {_mΩ : MeasurableSpace Ω} {μ : Measure Ω} {f : Ω → β} {g : Ω → β'}
    {mβ : MeasurableSpace β} {mβ' : MeasurableSpace β'}
    {f' : Ω → β} {g' : Ω → β'}
    (hfg : IndepFun f g μ) (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    IndepFun f' g' μ

recall ProbabilityTheory.IndepFun.integrable_mul
    {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {E : Type u_5} [TopologicalSpace E] [ContinuousENorm E] [Mul E]
    [ContinuousMul E] [ENormSMulClass E E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {X Y : Ω → E}
    (hXY : IndepFun X Y μ) (hX : Integrable X μ) (hY : Integrable Y μ) :
    Integrable (X * Y) μ

recall ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral
    {Ω : Type u_1} {𝕜 : Type u_5} [RCLike 𝕜]
    {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → 𝕜}
    (hXY : IndepFun X Y μ) (hX : AEStronglyMeasurable X μ)
    (hY : AEStronglyMeasurable Y μ) :
    μ[X * Y] = μ[X] * μ[Y]

recall MeasureTheory.Measure.QuasiMeasurePreserving.ae_eq_comp
    {α : Type u_1} {β : Type u_2} {δ : Type u_4}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {μa : Measure α} {μb : Measure β} {f : α → β}
    (h : Measure.QuasiMeasurePreserving f μa μb) {g₁ g₂ : β → δ}
    (hg : g₁ =ᵐ[μb] g₂) : g₁ ∘ f =ᵐ[μa] g₂ ∘ f

noncomputable
section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

/-- Square-integrable real processes on nonnegative time × sample space. -/
abbrev TimeProcessL2 (P : Measure W) :=
  Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P)

omit [CompleteSpace W] [BorelSpace W] in
/-- A product-`L²` representative has an `L²(P)` time section for almost every time.
The exceptional null set may depend on the representative, so this does not define evaluation
of a product-`L²` class at any prescribed time. -/
theorem memLp_timeSection_ae (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, MemLp (fun ω ↦ U (t, ω)) 2 P := by
  have hmeas := (Lp.memLp U).aestronglyMeasurable.prodMk_left
  have hint := (Lp.memLp U).integrable_sq.prod_right_ae
  filter_upwards [hmeas, hint] with t hmt hit
  exact (memLp_two_iff_integrable_sq hmt).2 hit

/-- The predictable `L²` processes associated to a filtration. -/
abbrev PredictableProcessL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  lpMeas ℝ ℝ 𝓕.predictable 2 (nonnegativeLebesgueMeasure.prod P)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- The predictable sigma-algebra is contained in the ambient product sigma-algebra. -/
theorem predictable_le_prod (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    𝓕.predictable ≤ (inferInstance : MeasurableSpace (ℝ≥0 × W)) := by
  apply measurableSpace_le_predictable_of_measurableSet
  · intro A hA
    exact (measurableSet_singleton (0 : ℝ≥0)).prod (𝓕.le 0 A hA)
  · intro t A hA
    exact measurableSet_Ioi.prod (𝓕.le t A hA)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The time coordinate is measurable from the predictable sigma-algebra. -/
theorem measurable_fst_predictable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    @Measurable (ℝ≥0 × W) ℝ≥0 𝓕.predictable inferInstance Prod.fst := by
  apply measurable_of_Iic
  intro t
  have hset : Prod.fst ⁻¹' Set.Iic t =
      ({0} ×ˢ (Set.univ : Set W)) ∪ (Set.Ioc 0 t ×ˢ Set.univ) := by
    ext ⟨s, w⟩
    simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_union, Set.mem_prod,
      Set.mem_singleton_iff, Set.mem_univ, and_true]
    constructor
    · intro hst
      rcases eq_or_lt_of_le (bot_le : (0 : ℝ≥0) ≤ s) with hs | hs
      · exact Or.inl hs.symm
      · exact Or.inr ⟨hs, hst⟩
    · rintro (hs | hs)
      · subst s
        exact (zero_le : (0 : ℝ≥0) ≤ t)
      · exact hs.2
  rw [hset]
  exact (measurableSet_predictable_singleton_bot_prod MeasurableSet.univ).union
    (measurableSet_predictable_Ioc_prod 0 t MeasurableSet.univ)

/-- Pull a deterministic time integrand back to the time--sample product along `Prod.fst`.
This is an isometry because `P` is a probability measure. -/
noncomputable def deterministicTimeEmbedding :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] TimeProcessL2 P :=
  Lp.compMeasurePreservingₗᵢ ℝ Prod.fst measurePreserving_fst

omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic time integrand is measurably predictable. -/
theorem deterministicTimeEmbedding_aestronglyMeasurable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    AEStronglyMeasurable[𝓕.predictable]
      (deterministicTimeEmbedding (P := P) f : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := by
  have hcomp : StronglyMeasurable[𝓕.predictable]
      ((f : ℝ≥0 → ℝ) ∘ Prod.fst) :=
    (Lp.stronglyMeasurable f).comp_measurable (measurable_fst_predictable 𝓕)
  exact hcomp.aestronglyMeasurable.congr
    (Lp.coeFn_compMeasurePreserving f measurePreserving_fst).symm

/-- The linear-isometric inclusion of deterministic square-integrable time functions into
predictable product-space processes. -/
noncomputable def deterministicPredictableEmbedding
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] PredictableProcessL2 𝓕 P where
  toFun f := ⟨deterministicTimeEmbedding (P := P) f,
    deterministicTimeEmbedding_aestronglyMeasurable 𝓕 f⟩
  map_add' f g := Subtype.ext (map_add (deterministicTimeEmbedding (P := P)) f g)
  map_smul' c f := Subtype.ext (map_smul (deterministicTimeEmbedding (P := P)) c f)
  norm_map' f := (deterministicTimeEmbedding (P := P)).norm_map f

omit [CompleteSpace W] [BorelSpace W] in
/-- A deterministic predictable integrand represents the function `(t, ω) ↦ f t`. -/
theorem deterministicPredictableEmbedding_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    (deterministicPredictableEmbedding (P := P) 𝓕 f : (ℝ≥0 × W) → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P] (f : ℝ≥0 → ℝ) ∘ Prod.fst :=
  Lp.coeFn_compMeasurePreserving f measurePreserving_fst

/-! ### Adapted elementary processes -/

/-- Pointwise representative of the one-step process `1_(a,b] Z`. -/
noncomputable def elementaryRepresentative (_𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (a b : ℝ≥0) (Z : W → ℝ) (p : ℝ≥0 × W) : ℝ :=
  if p.1 ∈ Set.Ioc a b then Z p.2 else 0

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] in
/-- If `Z` is `𝓕_a`-measurable, then `(t, ω) ↦ 1_(a,b](t) Z(ω)` is predictable. -/
theorem stronglyMeasurable_elementaryRepresentative
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {Z : W → ℝ} (hZ : StronglyMeasurable[𝓕 a] Z) :
    StronglyMeasurable[𝓕.predictable] (elementaryRepresentative 𝓕 a b Z) := by
  apply Measurable.stronglyMeasurable
  apply measurable_of_Iic
  intro c
  by_cases hc : 0 ≤ c
  · have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        (Set.Ioc a b ×ˢ (Z ⁻¹' Set.Ioi c))ᶜ := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic,
          Set.mem_compl_iff,
          Set.mem_prod, Set.mem_Ioi, true_and, not_lt]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic, hc,
          Set.mem_compl_iff,
          Set.mem_prod, Set.mem_Ioi, false_and, not_false_eq_true]
    rw [hset]
    exact (measurableSet_predictable_Ioc_prod a b
      (hZ.measurable measurableSet_Ioi)).compl
  · have hc' : c < 0 := lt_of_not_ge hc
    have hset : elementaryRepresentative 𝓕 a b Z ⁻¹' Set.Iic c =
        Set.Ioc a b ×ˢ (Z ⁻¹' Set.Iic c) := by
      ext p
      by_cases hp : p.1 ∈ Set.Ioc a b
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic,
          Set.mem_prod, true_and]
      · simp only [Set.mem_preimage, elementaryRepresentative, hp, ↓reduceIte, Set.mem_Iic,
          Set.mem_prod, false_and,
          iff_false, not_le, hc']
    rw [hset]
    exact measurableSet_predictable_Ioc_prod a b (hZ.measurable measurableSet_Iic)

/-- The scalar time indicator `1_(a,b]` as an `L²` function. -/
noncomputable def iocIndicator (a b : ℝ≥0) :
    Lp ℝ 2 nonnegativeLebesgueMeasure :=
  indicatorConstLp 2 measurableSet_Ioc
    (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)

namespace LegacyTensor

/-- Time-process classes for the upstream arbitrary-measure product convention. -/
abbrev TimeProcessL2 (P : Measure W) := Lp ℝ 2 (legacyProduct nonnegativeLebesgueMeasure P)

/-- Predictable classes for the upstream arbitrary-measure product convention. -/
abbrev PredictableProcessL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (P : Measure W) :=
  lpMeas ℝ ℝ 𝓕.predictable 2 (legacyProduct nonnegativeLebesgueMeasure P)

/-- The predictable `L²` class represented by `(t, ω) ↦ 1_(a,b](t) Z(ω)` for an
`𝓕_a`-measurable square-integrable coefficient `Z`. -/
noncomputable def elementaryPredictable
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : PredictableProcessL2 𝓕 P := by
  let hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  let Zm : W → ℝ := hZ.mk (Z : W → ℝ)
  let H : ℝ≥0 × W → ℝ := elementaryRepresentative 𝓕 a b Zm
  let V : Lp ℝ 2 (legacyProduct nonnegativeLebesgueMeasure P) :=
    tensor (iocIndicator a b) (Z : Lp ℝ 2 P)
  have hV : (V : ℝ≥0 × W → ℝ) =ᵐ[legacyProduct nonnegativeLebesgueMeasure P] H := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂legacyProduct nonnegativeLebesgueMeasure P,
        (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
          (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      legacyProduct_quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
    have hZm : ∀ᵐ p : ℝ≥0 × W ∂legacyProduct nonnegativeLebesgueMeasure P,
        (Z : W → ℝ) p.2 = Zm p.2 :=
      legacyProduct_quasiMeasurePreserving_snd.ae_eq_comp hZ.ae_eq_mk
    filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg, hZm]
      with p hp hg' hZm'
    rw [hp, hg', hZm']
    by_cases ht : p.1 ∈ Set.Ioc a b <;>
      simp [H, elementaryRepresentative, ht]
  exact ⟨V,
    (stronglyMeasurable_elementaryRepresentative 𝓕 a b hZ.stronglyMeasurable_mk)
      |>.aestronglyMeasurable.congr hV.symm⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Forgetting predictability, an elementary process is the product-space tensor
`1_(a,b] ⊗ Z`. -/
theorem elementaryPredictable_coeLp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P) =
      tensor (iocIndicator a b) (Z : RandomL2 P) := rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A pointwise representative of an elementary predictable process. -/
theorem elementaryPredictable_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : ℝ≥0 × W → ℝ) =ᵐ[
      legacyProduct nonnegativeLebesgueMeasure P]
      fun p => if p.1 ∈ Set.Ioc a b then (Z : W → ℝ) p.2 else 0 := by
  change (tensor (iocIndicator a b) (Z : Lp ℝ 2 P) : ℝ≥0 × W → ℝ) =ᵐ[_] _
  have hg : ∀ᵐ p : ℝ≥0 × W ∂legacyProduct nonnegativeLebesgueMeasure P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    legacyProduct_quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg]
    with p hp hg'
  rw [hp, hg']
  by_cases ht : p.1 ∈ Set.Ioc a b <;> simp [ht]

end LegacyTensor

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The predictable `L²` class represented by `(t, ω) ↦ 1_(a,b](t) Z(ω)` for an
`𝓕_a`-measurable square-integrable coefficient `Z`. -/
noncomputable def elementaryPredictable [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : PredictableProcessL2 𝓕 P := by
  let hZ : AEStronglyMeasurable[𝓕 a] (Z : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  let Zm : W → ℝ := hZ.mk (Z : W → ℝ)
  let H : ℝ≥0 × W → ℝ := elementaryRepresentative 𝓕 a b Zm
  let V : Lp ℝ 2 (nonnegativeLebesgueMeasure.prod P) :=
    tensor (iocIndicator a b) (Z : Lp ℝ 2 P)
  have hV : (V : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] H := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
          (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
    have hZm : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (Z : W → ℝ) p.2 = Zm p.2 :=
      Measure.quasiMeasurePreserving_snd.ae_eq_comp hZ.ae_eq_mk
    filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg, hZm]
      with p hp hg' hZm'
    rw [hp, hg', hZm']
    by_cases ht : p.1 ∈ Set.Ioc a b <;>
      simp [H, elementaryRepresentative, ht]
  exact ⟨V,
    (stronglyMeasurable_elementaryRepresentative 𝓕 a b hZ.stronglyMeasurable_mk)
      |>.aestronglyMeasurable.congr hV.symm⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Forgetting predictability, an elementary process is the product-space tensor
`1_(a,b] ⊗ Z`. -/
theorem elementaryPredictable_coeLp [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : TimeProcessL2 P) =
      tensor (iocIndicator a b) (Z : RandomL2 P) := rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- A pointwise representative of an elementary predictable process. -/
theorem elementaryPredictable_coeFn [SFinite P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (elementaryPredictable 𝓕 a b Z : ℝ≥0 × W → ℝ) =ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      fun p => if p.1 ∈ Set.Ioc a b then (Z : W → ℝ) p.2 else 0 := by
  change (tensor (iocIndicator a b) (Z : Lp ℝ 2 P) : ℝ≥0 × W → ℝ) =ᵐ[_] _
  have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (iocIndicator a b : ℝ≥0 → ℝ) p.1 =
        (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
        (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
  filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg]
    with p hp hg'
  rw [hp, hg']
  by_cases ht : p.1 ∈ Set.Ioc a b <;> simp [ht]

/-- The constant coefficient `1`, regarded as an `𝓕_a`-measurable `L²(P)` random variable. -/
noncomputable def adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨Lp.const 2 P (1 : ℝ),
    aestronglyMeasurable_const.congr (Lp.coeFn_const 2 P (1 : ℝ)).symm⟩

omit [CompleteSpace W] [BorelSpace W] in
/-- The one-step process with constant coefficient `1` on `(0,t]` is the deterministic
predictable embedding of `intervalIndicator t`. -/
theorem elementaryPredictable_adaptedOne
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    elementaryPredictable (P := P) 𝓕 0 t (adaptedOne (P := P) 𝓕 0) =
      deterministicPredictableEmbedding 𝓕 (intervalIndicator t) := by
  apply Subtype.ext
  rw [elementaryPredictable_coeLp]
  apply Lp.ext
  have hOne : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedOne (P := P) 𝓕 0 : W → ℝ) p.2 = 1 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_const 2 P (1 : ℝ))
  filter_upwards [coeFn_tensor (iocIndicator 0 t)
      (adaptedOne (P := P) 𝓕 0 : RandomL2 P),
    hOne, deterministicPredictableEmbedding_coeFn 𝓕 (intervalIndicator t)]
      with p hp hOnep hdet
  rw [hp, hOnep, hdet, Function.comp_apply, mul_one]
  rfl

/-- Orthogonal projection onto predictable time-space processes.  This is Mathlib's `L²`
conditional expectation with respect to the predictable sigma-algebra. -/
def predictableProjection (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    TimeProcessL2 P →L[ℝ] PredictableProcessL2 𝓕 P :=
  condExpL2 ℝ ℝ (predictable_le_prod 𝓕)

omit [CompleteSpace W] [BorelSpace W] in
/-- Predictable projection preserves integrals over predictable rectangles
`(a, b] × A` with `A ∈ 𝓕_a`.  This is the product-space conditional-expectation identity
available without choosing pointwise time sections. -/
theorem integral_predictableProjection_Ioc
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)
    (U : TimeProcessL2 P) (a b : ℝ≥0) {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∫ t in Set.Ioc a b, ∫ ω in A,
        (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure =
      ∫ t in Set.Ioc a b, ∫ ω in A, U (t, ω) ∂P
        ∂nonnegativeLebesgueMeasure := by
  let μ := nonnegativeLebesgueMeasure.prod P
  have hrect : μ (Set.Ioc a b ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hQ := integrableOn_Lp_of_measure_ne_top
    (predictableProjection 𝓕 U : TimeProcessL2 P)
    fact_one_le_two_ennreal.elim hrect
  have hU := integrableOn_Lp_of_measure_ne_top
    U fact_one_le_two_ennreal.elim hrect
  rw [← setIntegral_prod _ hQ, ← setIntegral_prod _ hU]
  exact integral_condExpL2_eq (predictable_le_prod 𝓕) U
    (measurableSet_predictable_Ioc_prod a b hA) hrect

/-- Conditional expectation at time `t`, regarded again as an ambient `L²(P)` random variable. -/
def filtrationCondExpL2 (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) :
    RandomL2 P →L[ℝ] RandomL2 P :=
  (lpMeas ℝ ℝ (𝓕 t) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (𝓕.le t))

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
/-- The ambient representative of `filtrationCondExpL2` agrees almost everywhere with
Mathlib's function-valued conditional expectation. -/
theorem filtrationCondExpL2_ae_eq_condExp
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P] P[(F : W → ℝ) | 𝓕 t] := by
  simpa only [filtrationCondExpL2, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Lp.toLp_coeFn] using
    (Lp.memLp F).condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le t)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- Timewise `L²` conditional expectation is contractive. -/
theorem norm_filtrationCondExpL2_le
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    ‖filtrationCondExpL2 𝓕 t F‖ ≤ ‖F‖ :=
  norm_condExpL2_coe_le (𝓕.le t) F

/-- The constant `L²` representative of the expectation of `F`. -/
def expectationL2 (F : RandomL2 P) : RandomL2 P :=
  Lp.const 2 P (∫ ω, F ω ∂P)

/-- Analytic data realizing the Malliavin derivative in time together with an abstract
integration, martingale-representation, and duality contract on predictable processes.

The structure does not yet identify `itoIntegral` with integration against `B` on elementary
predictable intervals. -/
structure ClarkOconeFamily (B : ℝ≥0 → W → ℝ) (P : Measure W) [IsGaussian P]
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) where
  /-- The designated process has Brownian finite-dimensional laws. -/
  isPreBrownian : IsPreBrownianReal B P
  /-- The Brownian coordinates are compatible with the linear Gaussian structure on `W`. -/
  coordinate : ℝ≥0 → StrongDual ℝ W
  /-- Identification of the process with the linear coordinates. -/
  coordinate_apply : ∀ t w, B t w = coordinate t w
  /-- The coordinates generate the ambient probability space. -/
  generated : IsWienerGenerated B
  /-- Measurability used to form the natural filtration. -/
  stronglyMeasurable : ∀ t, StronglyMeasurable (B t)
  /-- The filtration is the natural Brownian filtration. -/
  naturalFiltration : 𝓕 = Filtration.natural B stronglyMeasurable
  /-- Designated integration isometry on predictable square-integrable processes. -/
  itoIntegral : PredictableProcessL2 𝓕 P →L[ℝ] RandomL2 P
  /-- Norm isometry of the designated integration operator. -/
  norm_itoIntegral : ∀ u, ‖itoIntegral u‖ = ‖u‖
  /-- Outputs of the designated integration operator are centered. -/
  integral_itoIntegral : ∀ u, ∫ ω, itoIntegral u ω ∂P = 0
  /-- Terminal `L²` representation by the designated integration operator. -/
  martingaleRepresentation : ∀ G : RandomL2 P, ∃ u,
    G = expectationL2 G + itoIntegral u
  /-- Duality identifies the predictable Malliavin derivative as the MRT integrand.  Here the
  time derivative `Dₜ` is the one constructed in `TimeDerivative.lean` from the Brownian
  coordinates (`Malliavin.timeDerivative`): `J₁⁻¹` pointwise, then the Fubini lift. -/
  malliavinItoDuality : ∀ (F : D12 P) u,
    inner ℝ (F.1 - expectationL2 F.1) (itoIntegral u) =
      inner ℝ (predictableProjection 𝓕
        (Malliavin.timeDerivative isPreBrownian coordinate coordinate_apply generated
          (mderivD12 P F))) u

/-- The designated integral bundled as a linear isometry. -/
def ClarkOconeFamily.itoIntegralₗᵢ {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] RandomL2 P :=
  ⟨C.itoIntegral.toLinearMap, C.norm_itoIntegral⟩

@[simp]
theorem ClarkOconeFamily.itoIntegralₗᵢ_apply {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    C.itoIntegralₗᵢ u = C.itoIntegral u :=
  rfl

/-- The designated Itô integral, with codomain restricted to centered random variables. -/
noncomputable def ClarkOconeFamily.centeredItoIntegralₗᵢ
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P →ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker where
  toLinearMap := C.itoIntegralₗᵢ.toLinearMap.codRestrict
    (CameronMartin.expectationMap P).ker fun u => by
      rw [LinearMap.mem_ker]
      change CameronMartin.expectationMap P (C.itoIntegral u) = 0
      rw [CameronMartin.expectationMap_apply]
      exact C.integral_itoIntegral u
  norm_map' u := C.norm_itoIntegral u

@[simp]
theorem ClarkOconeFamily.centeredItoIntegralₗᵢ_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    (C.centeredItoIntegralₗᵢ u : RandomL2 P) = C.itoIntegral u :=
  rfl

/-- Martingale representation makes the centered Itô isometry onto. -/
theorem ClarkOconeFamily.centeredItoIntegralₗᵢ_surjective
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    Function.Surjective C.centeredItoIntegralₗᵢ := by
  intro G
  obtain ⟨u, hu⟩ := C.martingaleRepresentation (G : RandomL2 P)
  have hmean : ∫ w, (G : RandomL2 P) w ∂P = 0 := by
    rw [← CameronMartin.expectationMap_apply]
    exact G.property
  have hexpect : expectationL2 (G : RandomL2 P) = 0 := by
    rw [expectationL2, hmean]
    simp only [map_zero]
  refine ⟨u, Subtype.ext ?_⟩
  change C.itoIntegral u = (G : RandomL2 P)
  rw [hexpect, zero_add] at hu
  exact hu.symm

/-- Predictable square-integrable processes are linearly isometric to centered random variables. -/
noncomputable def ClarkOconeFamily.centeredItoEquiv
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) :
    PredictableProcessL2 𝓕 P ≃ₗᵢ[ℝ] (CameronMartin.expectationMap P).ker :=
  LinearIsometryEquiv.ofSurjective C.centeredItoIntegralₗᵢ
    C.centeredItoIntegralₗᵢ_surjective

@[simp]
theorem ClarkOconeFamily.centeredItoEquiv_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u : PredictableProcessL2 𝓕 P) :
    (C.centeredItoEquiv u : RandomL2 P) = C.itoIntegral u :=
  rfl

/-- The norm isometry of the designated integral polarizes to preservation of inner products. -/
theorem ClarkOconeFamily.inner_itoIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (u v : PredictableProcessL2 𝓕 P) :
    inner ℝ (C.itoIntegral u) (C.itoIntegral v) = inner ℝ u v :=
  C.itoIntegralₗᵢ.inner_map_map u v

/-- **The time derivative of the contract is constructed, not stipulated**: the
Cameron--Martin/Fubini realization `L²(P; H) → L²(ℝ≥0 × W)` of an `H`-valued random derivative
as `DₜF`, obtained from `Malliavin.timeDerivative` (`TimeDerivative.lean`). -/
noncomputable def ClarkOconeFamily.timeDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) : Lp (CameronMartin.Space P) 2 P →L[ℝ] TimeProcessL2 P :=
  (Malliavin.timeDerivative C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated).toContinuousLinearMap

/-- The time derivative preserves the `L²(Ω; H)` norm. -/
theorem ClarkOconeFamily.norm_timeDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (U : Lp (CameronMartin.Space P) 2 P) :
    ‖C.timeDerivative U‖ = ‖U‖ :=
  (Malliavin.timeDerivative C.isPreBrownian C.coordinate C.coordinate_apply
    C.generated).norm_map U

theorem ClarkOconeFamily.timeDerivative_apply {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (U : Lp (CameronMartin.Space P) 2 P) :
    C.timeDerivative U =
      Malliavin.timeDerivative C.isPreBrownian C.coordinate C.coordinate_apply C.generated U :=
  rfl

/-- A Brownian increment after time `a` is independent of every almost everywhere
`𝓕_a`-measurable real random variable. -/
theorem ClarkOconeFamily.indep_increment_of_adapted
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    {Z : W → ℝ} (hZ : AEStronglyMeasurable[𝓕 a] Z P) :
    IndepFun (fun w ↦ B b w - B a w) Z P := by
  let Zm : W → ℝ := hZ.mk Z
  have hshift := C.isPreBrownian.indepFun_shift a
  have heval : Measurable (fun x : ℝ≥0 → ℝ ↦ x (b - a)) := measurable_pi_apply _
  have hfuturePast := hshift.comp heval measurable_id
  have hfuturePast' : IndepFun (fun w ↦ B b w - B a w)
      (fun w (t : Set.Iic a) ↦ B t w) P := by
    convert hfuturePast using 1
    · funext w
      change B b w - B a w = B (a + (b - a)) w - B a w
      rw [add_comm, tsub_add_cancel_of_le hab]
    · rfl
  have hind := (IndepFun_iff_Indep _ _ _).mp hfuturePast'
  have hnat : 𝓕 a =
      MeasurableSpace.comap (fun w (t : Set.Iic a) ↦ B t w) inferInstance := by
    rw [C.naturalFiltration, Filtration.natural_eq_comap]
  rw [← hnat] at hind
  have hZm : @Measurable W ℝ (𝓕 a) inferInstance Zm :=
    hZ.stronglyMeasurable_mk.measurable
  have hindZm := indep_of_indep_of_le_right hind hZm.comap_le
  have hfunZm : IndepFun (fun w ↦ B b w - B a w) Zm P :=
    (IndepFun_iff_Indep _ _ _).mpr hindZm
  exact hfunZm.congr Filter.EventuallyEq.rfl hZ.ae_eq_mk.symm

/-- A Brownian increment after time `a` is independent of every square-integrable
`𝓕_a`-measurable coefficient. -/
theorem ClarkOconeFamily.indep_increment_adapted
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    IndepFun (fun w ↦ B b w - B a w) (Z : W → ℝ) P :=
  C.indep_increment_of_adapted hab (lpMeas.aestronglyMeasurable Z)

/-- The product of an adapted `L²` coefficient and its future Brownian increment is again
square-integrable.  Independence supplies the missing fourth-moment factorization. -/
theorem ClarkOconeFamily.memLp_adapted_mul_increment
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    MemLp (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) 2 P := by
  have hΔ : MemLp (fun w ↦ B b w - B a w) 2 P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  have hind := C.indep_increment_adapted hab Z
  have hindSq : IndepFun (fun w ↦ (B b w - B a w) ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hind.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hint : Integrable ((fun w ↦ (B b w - B a w) ^ 2) *
      fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    hindSq.integrable_mul hΔ.integrable_sq
      (Lp.memLp (Z : Lp ℝ 2 P)).integrable_sq
  have hZamb : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hmeas : AEStronglyMeasurable
      (fun w ↦ (Z : W → ℝ) w * (B b w - B a w)) P :=
    hZamb.mul hΔ.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq hmeas).2
  refine hint.congr (Filter.Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply]
  ring

/-- The terminal `L²(P)` value `Z · (B_b - B_a)` of a one-step adapted integrand. -/
noncomputable def ClarkOconeFamily.elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) : RandomL2 P :=
  (C.memLp_adapted_mul_increment hab Z).toLp
    (fun w ↦ (Z : W → ℝ) w * (B b w - B a w))

/-- A representative of the terminal value of a one-step adapted integrand. -/
theorem ClarkOconeFamily.coeFn_elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    (C.elementaryIntegralValue hab Z : W → ℝ) =ᵐ[P]
      fun w => (Z : W → ℝ) w * (B b w - B a w) :=
  MemLp.coeFn_toLp _

/-- The terminal value of every one-step adapted integrand is centered. -/
theorem ClarkOconeFamily.integral_elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ∫ w, C.elementaryIntegralValue hab Z w ∂P = 0 := by
  rw [integral_congr_ae (C.coeFn_elementaryIntegralValue hab Z)]
  have hZ : AEStronglyMeasurable (Z : W → ℝ) P :=
    AEStronglyMeasurable.mono (𝓕.le a) (lpMeas.aestronglyMeasurable Z)
  have hΔ : AEStronglyMeasurable (fun w ↦ B b w - B a w) P :=
    C.isPreBrownian.isGaussianProcess.hasGaussianLaw_sub.memLp_two.aestronglyMeasurable
  change ∫ w, ((Z : W → ℝ) * fun w ↦ B b w - B a w) w ∂P = 0
  rw [(C.indep_increment_adapted hab Z).symm.integral_mul_eq_mul_integral hZ hΔ]
  change (∫ w, (Z : W → ℝ) w ∂P) * (∫ w, B b w - B a w ∂P) = 0
  rw [integral_sub (C.isPreBrownian.integrable_eval b)
      (C.isPreBrownian.integrable_eval a),
    C.isPreBrownian.integral_eval, C.isPreBrownian.integral_eval, sub_zero, mul_zero]

/-- The terminal value attached to a constant-coefficient elementary process is its Brownian
increment. -/
theorem ClarkOconeFamily.elementaryIntegralValue_adaptedOne
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b) :
    C.elementaryIntegralValue hab (adaptedOne (P := P) 𝓕 a) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by
  apply Lp.ext
  have hOne : (adaptedOne (P := P) 𝓕 a : W → ℝ) =ᵐ[P]
      fun _ => (1 : ℝ) := by
    change (Lp.const 2 P (1 : ℝ) : W → ℝ) =ᵐ[P] fun _ => (1 : ℝ)
    exact Lp.coeFn_const 2 P (1 : ℝ)
  filter_upwards [C.coeFn_elementaryIntegralValue hab (adaptedOne (P := P) 𝓕 a),
    hOne,
    Lp.coeFn_sub (brownianLp C.isPreBrownian b) (brownianLp C.isPreBrownian a),
    coeFn_brownianLp C.isPreBrownian b, coeFn_brownianLp C.isPreBrownian a]
    with w hvalue hone hsub hb ha
  rw [hvalue, hone, hsub]
  simp only [Pi.sub_apply]
  rw [hb, ha]
  simp only [one_mul]

/-- At initial time zero, the constant-coefficient elementary value is the Brownian coordinate
itself. -/
theorem ClarkOconeFamily.elementaryIntegralValue_adaptedOne_zero
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (t : ℝ≥0) :
    C.elementaryIntegralValue (zero_le : (0 : ℝ≥0) ≤ t)
        (adaptedOne (P := P) 𝓕 0) =
      brownianLp C.isPreBrownian t := by
  rw [C.elementaryIntegralValue_adaptedOne, brownianLp_zero, sub_zero]

/-- Brownian compatibility on all one-step adapted `L²` integrands.  This is the textbook
formula `∫_a^b Z dB = Z (B_b - B_a)` and is stronger than compatibility on
deterministic integrands. -/
def ClarkOconeFamily.IsBrownianOnElementary
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) : Prop :=
  ∀ {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P),
    C.itoIntegral (elementaryPredictable 𝓕 a b Z) =
      C.elementaryIntegralValue hab Z

/-- The elementary compatibility formula satisfies the expected product-norm Itô isometry. -/
theorem ClarkOconeFamily.norm_elementaryIntegralValue
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ‖C.elementaryIntegralValue hab Z‖ = ‖iocIndicator a b‖ * ‖(Z : RandomL2 P)‖ := by
  let Δ : RandomL2 P := brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a
  have hΔcoe : (fun w ↦ B b w - B a w) =ᵐ[P] (Δ : W → ℝ) := by
    filter_upwards [Lp.coeFn_sub (brownianLp C.isPreBrownian b)
      (brownianLp C.isPreBrownian a), coeFn_brownianLp C.isPreBrownian b,
      coeFn_brownianLp C.isPreBrownian a] with w hsub hb ha
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hb, ha]
  have hindSq : IndepFun (fun w ↦ (Δ : W → ℝ) w ^ 2)
      (fun w ↦ (Z : W → ℝ) w ^ 2) P :=
    ((C.indep_increment_adapted hab Z).congr hΔcoe Filter.EventuallyEq.rfl).comp
      (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hfactor := hindSq.integral_mul_eq_mul_integral
    (Lp.memLp Δ).integrable_sq.aestronglyMeasurable
    (Lp.memLp (Z : RandomL2 P)).integrable_sq.aestronglyMeasurable
  have hsq : ‖C.elementaryIntegralValue hab Z‖ ^ 2 =
      ‖Δ‖ ^ 2 * ‖(Z : RandomL2 P)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def,
      ← real_inner_self_eq_norm_sq Δ, L2.inner_def,
      ← real_inner_self_eq_norm_sq (Z : RandomL2 P), L2.inner_def]
    simp only [RCLike.inner_apply, conj_trivial, pow_two] at hfactor ⊢
    rw [← hfactor]
    apply integral_congr_ae
    filter_upwards [C.coeFn_elementaryIntegralValue hab Z, hΔcoe]
      with w hvalue hΔw
    rw [hvalue, hΔw]
    simp only [Pi.mul_apply]
    ring
  have hΔnorm : ‖Δ‖ = ‖iocIndicator a b‖ := by
    dsimp only [Δ]
    rw [← wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab,
      norm_wienerIntegral]
    rfl
  apply (sq_eq_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [hsq, hΔnorm]
  ring

/-- Brownian compatibility on one-step adapted integrands extends by linearity to finite sums. -/
theorem ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_sum_elementaryPredictable
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) {ι : Type*} (s : Finset ι)
    (a b : ι → ℝ≥0) (hab : ∀ i, a i ≤ b i)
    (Z : ∀ i, lpMeas ℝ ℝ (𝓕 (a i)) 2 P) :
    C.itoIntegral (s.sum fun i ↦ elementaryPredictable 𝓕 (a i) (b i) (Z i)) =
      s.sum fun i ↦ C.elementaryIntegralValue (hab i) (Z i) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact hC (hab i) (Z i)

/-!
Constructing the full `ClarkOconeFamily` is the remaining analytic interface, not asserted here.
The identification of `Space P` with deterministic time `L²` and the Fubini lift are theorems in
`TimeDerivative.lean`. Downstream, `PredictableDensity.lean`, `ElementaryIto.lean`, and
`ItoConstruction.lean` prove density of the adapted elementary span and extend the genuine
Brownian values to a centered Itô isometry on all predictable `L²`. What remains stipulated by a
full family is martingale representation and Malliavin--Itô duality. Keeping the family explicit
prevents those deeper facts from being inferred from the Brownian finite-dimensional laws alone.
-/

/-- Necessary Brownian compatibility on deterministic integrands: the designated integral of
`1_{(0,t]}` is the Brownian coordinate `B t` in `L²(P)`.

This condition determines the integral on the whole deterministic `L²` subspace, but says nothing
about genuinely random predictable integrands.  In particular it is weaker than identifying the
designated operator with the Brownian Itô integral on adapted elementary processes. -/
def ClarkOconeFamily.IsBrownianOnDeterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) : Prop :=
  ∀ t, C.itoIntegral
    (deterministicPredictableEmbedding 𝓕 (intervalIndicator t)) = brownianLp C.isPreBrownian t

/-- Brownian compatibility on adapted elementary processes entails compatibility on every
deterministic interval indicator. -/
theorem ClarkOconeFamily.IsBrownianOnElementary.isBrownianOnDeterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) : C.IsBrownianOnDeterministic := by
  intro t
  have h := hC (zero_le : (0 : ℝ≥0) ≤ t) (adaptedOne (P := P) 𝓕 0)
  rw [elementaryPredictable_adaptedOne,
    C.elementaryIntegralValue_adaptedOne_zero] at h
  exact h

/-- Restriction of the designated integral to deterministic predictable processes. -/
noncomputable def ClarkOconeFamily.deterministicIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] RandomL2 P :=
  C.itoIntegral.comp (deterministicPredictableEmbedding 𝓕).toContinuousLinearMap

theorem ClarkOconeFamily.deterministicIntegral_apply
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.deterministicIntegral f =
      C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) := rfl

/-- Agreement on the interval indicators determines the designated integral on every
deterministic square-integrable integrand. -/
theorem ClarkOconeFamily.IsBrownianOnDeterministic.deterministicIntegral_eq_wienerIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) :
    C.deterministicIntegral = wienerIntegral C.isPreBrownian := by
  apply ContinuousLinearMap.ext_on dense_span_intervalIndicator
  intro f hf
  obtain ⟨t, rfl⟩ := hf
  rw [C.deterministicIntegral_apply, wienerIntegral_intervalIndicator]
  exact hC t

/-- Deterministic Brownian compatibility is equivalent to equality with the genuine Wiener
integral on the entire deterministic `L²` subspace. -/
theorem ClarkOconeFamily.isBrownianOnDeterministic_iff
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕) :
    C.IsBrownianOnDeterministic ↔
      C.deterministicIntegral = wienerIntegral C.isPreBrownian := by
  constructor
  · exact fun hC ↦ hC.deterministicIntegral_eq_wienerIntegral
  · intro hC t
    have ht := DFunLike.congr_fun hC (intervalIndicator t)
    rw [C.deterministicIntegral_apply, wienerIntegral_intervalIndicator] at ht
    exact ht

/-- The designated integral agrees with the genuine Wiener integral on every deterministic
integrand. -/
theorem ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕 f) =
      wienerIntegral C.isPreBrownian f := by
  rw [← C.deterministicIntegral_apply, hC.deterministicIntegral_eq_wienerIntegral]

/-- On a deterministic interval integrand, Brownian compatibility gives the corresponding
Brownian increment. -/
theorem ClarkOconeFamily.IsBrownianOnDeterministic.itoIntegral_deterministic_Ioc
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} {C : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnDeterministic) {a b : ℝ≥0} (hab : a ≤ b) :
    C.itoIntegral (deterministicPredictableEmbedding 𝓕
      (indicatorConstLp 2 measurableSet_Ioc
        (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ))) =
      brownianLp C.isPreBrownian b - brownianLp C.isPreBrownian a := by
  rw [hC.itoIntegral_deterministic,
    wienerIntegral_indicatorConstLp_Ioc C.isPreBrownian hab]

/-- The predictable product-space projection of the time-realized Malliavin derivative. -/
def predictableDerivative {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) : PredictableProcessL2 𝓕 P :=
  predictableProjection 𝓕
    (C.timeDerivative (mderivD12 P F))

/-- The Clark--Ocone integrand has a representative measurable for the predictable sigma-algebra. -/
theorem aestronglyMeasurable_predictableDerivative
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    AEStronglyMeasurable[𝓕.predictable]
      (predictableDerivative C F : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) :=
  lpMeas.aestronglyMeasurable _

/-- The designated integration operator applied to the predictable Malliavin derivative. -/
def clarkOconeIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) : RandomL2 P :=
  C.itoIntegral (predictableDerivative C F)

/-- Predictable projection is contractive, and the time realization is isometric. -/
theorem norm_predictableDerivative_le {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖predictableDerivative C F‖ ≤ ‖mderivD12 P F‖ := by
  calc
    ‖predictableDerivative C F‖ ≤ ‖C.timeDerivative (mderivD12 P F)‖ := by
      exact norm_condExpL2_le (predictable_le_prod 𝓕)
        (C.timeDerivative (mderivD12 P F))
    _ = ‖mderivD12 P F‖ := C.norm_timeDerivative _

/-- The abstract integration term has expectation zero. -/
theorem integral_clarkOconeIntegral {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∫ ω, clarkOconeIntegral C F ω ∂P = 0 :=
  C.integral_itoIntegral _

/-- The stipulated duality uniquely identifies any representing integrand with the predictable
derivative. -/
theorem eq_predictableDerivative_of_representation
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) (u : PredictableProcessL2 𝓕 P)
    (hu : F.1 = expectationL2 F.1 + C.itoIntegral u) :
    u = predictableDerivative C F := by
  have hcenter : F.1 - expectationL2 F.1 = C.itoIntegral u := by
    calc
      F.1 - expectationL2 F.1 =
          (expectationL2 F.1 + C.itoIntegral u) - expectationL2 F.1 :=
        congrArg (fun X : RandomL2 P => X - expectationL2 F.1) hu
      _ = C.itoIntegral u := by abel
  apply ext_inner_right ℝ
  intro v
  calc
    inner ℝ u v = inner ℝ (C.itoIntegral u) (C.itoIntegral v) :=
      (C.inner_itoIntegral u v).symm
    _ = inner ℝ (F.1 - expectationL2 F.1) (C.itoIntegral v) := by rw [hcenter]
    _ = inner ℝ (predictableDerivative C F) v := C.malliavinItoDuality F v

/-- **Abstract Clark--Ocone representation** supplied by `C`:
`F = E[F] + C.itoIntegral (predictableDerivative C F)` for every `F ∈ 𝔻₁,₂`.

Interpreting `predictableDerivative` timewise as `E[DₜF | 𝓕ₜ]`, and the last term as the
corresponding Brownian stochastic integral, requires compatibility theorems not yet included in
`ClarkOconeFamily`. -/
theorem clarkOcone {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    F.1 = expectationL2 F.1 + clarkOconeIntegral C F :=
  by
    obtain ⟨u, hu⟩ := C.martingaleRepresentation F.1
    have hu_eq := eq_predictableDerivative_of_representation C F u hu
    calc
      F.1 = expectationL2 F.1 + C.itoIntegral u := hu
      _ = expectationL2 F.1 + C.itoIntegral (predictableDerivative C F) := by rw [hu_eq]
      _ = expectationL2 F.1 + clarkOconeIntegral C F := rfl

/-- Centered form of the abstract `ClarkOconeFamily` representation. -/
theorem sub_expectationL2_eq_clarkOconeIntegral
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    F.1 - expectationL2 F.1 = clarkOconeIntegral C F := by
  calc
    F.1 - expectationL2 F.1 =
        (expectationL2 F.1 + clarkOconeIntegral C F) - expectationL2 F.1 :=
      congrArg (fun X : RandomL2 P => X - expectationL2 F.1)
        (clarkOcone C F)
    _ = clarkOconeIntegral C F := by abel

/-- Isometric norm identity for the centered abstract representation. -/
theorem norm_sub_expectationL2 {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖F.1 - expectationL2 F.1‖ = ‖predictableDerivative C F‖ := by
  rw [sub_expectationL2_eq_clarkOconeIntegral C F]
  exact C.norm_itoIntegral _

/-- `L²` Poincaré estimate obtained by predictable contraction in the abstract representation
contract. -/
theorem norm_sub_expectationL2_le_mderivD12
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ‖F.1 - expectationL2 F.1‖ ≤ ‖mderivD12 P F‖ := by
  rw [norm_sub_expectationL2 C F]
  exact norm_predictableDerivative_le C F

end Malliavin

end

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
