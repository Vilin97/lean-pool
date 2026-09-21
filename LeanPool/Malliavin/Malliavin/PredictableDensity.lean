/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ClarkOcone

/-!
# Density of adapted elementary predictable processes

This file proves that finite linear combinations of processes
`(t, ω) ↦ 1_(a,b](t) Z(ω)`, with `Z ∈ L²(P)` measurable at time `a`, are dense in
predictable product `L²`.  The proof uses the predictable rectangles as a generating π-system,
propagates orthogonality on each finite time frame by a π-λ argument, and exhausts nonnegative
time; the omitted time origin is null.

`predictableTrimEquiv` also identifies the local `lpMeas` model with the equivalent
trimmed-measure `L²` model used by completion constructions of the Itô integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5

recall Filter.exists_seq_monotone_tendsto_atTop_atTop
    (α : Type u_1) [Preorder α] [Nonempty α] [IsDirectedOrder α]
    [(atTop : Filter α).IsCountablyGenerated] :
    ∃ xs : ℕ → α, Monotone xs ∧
      Tendsto xs (atTop : Filter ℕ) (atTop : Filter α)

recall Filter.tendsto_atTop_atTop
    {α : Type u_1} {β : Type u_2} [Nonempty α] [Preorder α]
    [IsDirectedOrder α] {f : α → β} [Preorder β] :
    Tendsto f (atTop : Filter α) (atTop : Filter β) ↔
      ∀ b : β, ∃ i : α, ∀ a : α, i ≤ a → b ≤ f a

recall MeasurableSpace.induction_on_inter
    {α : Type u_1} {m : MeasurableSpace α}
    {C : ∀ s : Set α, MeasurableSet s → Prop} {s : Set (Set α)}
    (h_eq : m = MeasurableSpace.generateFrom s) (h_inter : IsPiSystem s)
    (empty : C ∅ .empty)
    (basic : ∀ t (ht : t ∈ s), C t (h_eq ▸ .basic t ht))
    (compl : ∀ t (htm : MeasurableSet t), C t htm → C tᶜ htm.compl)
    (iUnion : ∀ (f : ℕ → Set α), Pairwise (Disjoint on f) →
      ∀ (hfm : ∀ i, MeasurableSet (f i)),
      (∀ i, C (f i) (hfm i)) → C (⋃ i, f i) (.iUnion hfm)) :
    ∀ t (ht : MeasurableSet t), C t ht

recall MeasureTheory.integral_add_compl
    {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {s : Set X} {μ : Measure X} (hs : MeasurableSet s)
    (hfi : Integrable f μ) :
    ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ

recall MeasureTheory.integral_iUnion
    {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {μ : Measure X} {ι : Type u_3} [Countable ι]
    {s : ι → Set X} (hm : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Disjoint on s))
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    ∫ x in ⋃ i, s i, f x ∂μ = ∑' i, ∫ x in s i, f x ∂μ

recall MeasureTheory.tendsto_setIntegral_of_monotone
    {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {μ : Measure X} {ι : Type u_3} [Preorder ι]
    [(atTop : Filter ι).IsCountablyGenerated] {s : ι → Set X}
    (hsm : ∀ i, MeasurableSet (s i)) (h_mono : Monotone s)
    (hfi : IntegrableOn f (⋃ i, s i) μ) :
    Tendsto (fun i ↦ ∫ x in s i, f x ∂μ) (atTop : Filter ι)
      (𝓝 (∫ x in ⋃ i, s i, f x ∂μ))

recall MeasureTheory.lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    {α : Type u_1} {E' : Type u_2} {𝕜 : Type u_3} {p : ℝ≥0∞}
    {m m0 : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E']
    [NormedSpace ℝ E'] (hm : m ≤ m0) (f : lpMeas E' 𝕜 m p μ)
    (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ →
      IntegrableOn (f : Lp E' p μ) s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ →
      ∫ x in s, (f : Lp E' p μ) x ∂μ = 0) :
    (f : α → E') =ᵐ[μ] 0

recall MeasureTheory.Measure.restrict_restrict
    {α : Type u_1} {m0 : MeasurableSpace α} {μ : Measure α}
    {s t : Set α} (hs : MeasurableSet s) :
    (μ.restrict t).restrict s = μ.restrict (s ∩ t)

recall MeasureTheory.setIntegral_congr_set
    {X : Type u_1} {E : Type u_2} {mX : MeasurableSpace X}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} {s t : Set X} {μ : Measure X} (hst : s =ᵐ[μ] t) :
    ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ

recall Submodule.topologicalClosure_eq_top_iff
    {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    {K : Submodule 𝕜 E} [CompleteSpace E] :
    K.topologicalClosure = ⊤ ↔ Kᗮ = ⊥

recall Submodule.mem_orthogonal
    {𝕜 : Type u_1} {E : Type u_2} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) (v : E) :
    v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫_𝕜 = 0

recall MeasureTheory.lpMeasToLpTrimLie
    {α : Type u_1} (F : Type u_2) (𝕜 : Type u_3) (p : ℝ≥0∞)
    [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {m m0 : MeasurableSpace α} (μ : Measure α) [Fact (1 ≤ p)]
    (hm : m ≤ m0) :
    lpMeas F 𝕜 m p μ ≃ₗᵢ[𝕜] Lp F p (μ.trim hm)

recall MeasureTheory.lpMeasToLpTrim_ae_eq
    {α : Type u_1} {F : Type u_2} {𝕜 : Type u_3} {p : ℝ≥0∞}
    [RCLike 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {m m0 : MeasurableSpace α} {μ : Measure α} (hm : m ≤ m0)
    (f : lpMeas F 𝕜 m p μ) :
    (lpMeasToLpTrim F 𝕜 p μ hm f : α → F) =ᵐ[μ] (f : α → F)

recall ContinuousLinearMap.ext_on
    {R₁ : Type u_1} {R₂ : Type u_2} [Semiring R₁] [Semiring R₂]
    {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_3} [TopologicalSpace M₁]
    [AddCommMonoid M₁] {M₂ : Type u_4} [TopologicalSpace M₂]
    [AddCommMonoid M₂] [Module R₁ M₁] [Module R₂ M₂] [T2Space M₂]
    {s : Set M₁} (hs : Dense (Submodule.span R₁ s : Set M₁))
    {f g : M₁ →SL[σ₁₂] M₂} (h : Set.EqOn f g s) : f = g

noncomputable section

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The predictable-process subspace as the trimmed-measure `L²` model used by completion
constructions of the Itô integral. -/
noncomputable def predictableTrimEquiv
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    PredictableProcessL2 𝓕 P ≃ₗᵢ[ℝ]
      @Lp (ℝ≥0 × W) ℝ 𝓕.predictable _ 2
        ((nonnegativeLebesgueMeasure.prod P).trim (predictable_le_prod 𝓕)) :=
  lpMeasToLpTrimLie ℝ ℝ 2 (nonnegativeLebesgueMeasure.prod P) (predictable_le_prod 𝓕)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
/-- The trimmed representative agrees almost everywhere with the ambient representative. -/
theorem predictableTrimEquiv_ae_eq
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (u : PredictableProcessL2 𝓕 P) :
    (predictableTrimEquiv 𝓕 u : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      (u : ℝ≥0 × W → ℝ) :=
  lpMeasToLpTrim_ae_eq (predictable_le_prod 𝓕) u

/-- Basic rectangles generating the predictable sigma-algebra. -/
def predictableRectangle (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Set (Set (ℝ≥0 × W)) :=
  {S | ∃ F₀ : Set W, MeasurableSet[𝓕 0] F₀ ∧ S = ({(0 : ℝ≥0)} ×ˢ F₀)} ∪
  {S | ∃ a b : ℝ≥0, ∃ F : Set W,
    a < b ∧ MeasurableSet[𝓕 a] F ∧ S = (Set.Ioc a b ×ˢ F)}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
lemma isPiSystem_predictableRectangle
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    IsPiSystem (predictableRectangle 𝓕) := by
  rintro S₁ hS₁ S₂ hS₂ hne
  rcases hS₁ with ⟨F₀₁, hF₀₁, rfl⟩ | ⟨a₁, b₁, F₁, hab₁, hF₁, rfl⟩
  all_goals
    rcases hS₂ with ⟨F₀₂, hF₀₂, rfl⟩ | ⟨a₂, b₂, F₂, hab₂, hF₂, rfl⟩
  · left
    refine ⟨F₀₁ ∩ F₀₂, hF₀₁.inter hF₀₂, ?_⟩
    rw [Set.prod_inter_prod, Set.inter_self]
  · exfalso
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_singleton_iff,
      Set.mem_Ioc] at ht
    obtain ⟨⟨rfl, _⟩, ⟨ha₂, _⟩, _⟩ := ht
    exact not_lt_bot ha₂
  · exfalso
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc,
      Set.mem_singleton_iff] at ht
    obtain ⟨⟨⟨ha₁, _⟩, _⟩, rfl, _⟩ := ht
    exact not_lt_bot ha₁
  · right
    obtain ⟨⟨t, w⟩, ht⟩ := hne
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_Ioc] at ht
    obtain ⟨⟨⟨ha₁, hb₁⟩, _⟩, ⟨ha₂, hb₂⟩, _⟩ := ht
    have hlt : a₁ ⊔ a₂ < b₁ ⊓ b₂ :=
      lt_of_lt_of_le (max_lt ha₁ ha₂) (le_min hb₁ hb₂)
    refine ⟨a₁ ⊔ a₂, b₁ ⊓ b₂, F₁ ∩ F₂, hlt, ?_, ?_⟩
    · exact (𝓕.mono (le_max_left a₁ a₂) _ hF₁).inter
        (𝓕.mono (le_max_right a₁ a₂) _ hF₂)
    · rw [Set.prod_inter_prod, Set.Ioc_inter_Ioc]

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
theorem generateFrom_predictableRectangle
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    MeasurableSpace.generateFrom (predictableRectangle 𝓕) = 𝓕.predictable := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro S (⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, _hab, hF, rfl⟩)
    · exact measurableSet_predictable_singleton_bot_prod hF₀
    · exact measurableSet_predictable_Ioc_prod a b hF
  · apply measurableSpace_le_predictable_of_measurableSet
    · intro A hA
      exact MeasurableSpace.measurableSet_generateFrom (Or.inl ⟨A, hA, rfl⟩)
    · intro i A hA
      obtain ⟨seq, _hmono, htends⟩ :=
        Filter.exists_seq_monotone_tendsto_atTop_atTop ℝ≥0
      have hIoi : (Set.Ioi i : Set ℝ≥0) = ⋃ n : ℕ, Set.Ioc i (seq n) := by
        ext s
        simp only [Set.mem_Ioi, Set.mem_iUnion, Set.mem_Ioc]
        refine ⟨fun his ↦ ?_, fun ⟨_, h, _⟩ ↦ h⟩
        rw [Filter.tendsto_atTop_atTop] at htends
        obtain ⟨n, hn⟩ := htends s
        exact ⟨n, his, hn n le_rfl⟩
      rw [hIoi, Set.iUnion_prod_const]
      refine MeasurableSet.iUnion fun n ↦ ?_
      by_cases hin : i < seq n
      · exact MeasurableSpace.measurableSet_generateFrom
          (Or.inr ⟨i, seq n, A, hin, hA, rfl⟩)
      · have hempty : Set.Ioc i (seq n) ×ˢ A = (∅ : Set (ℝ≥0 × W)) := by
          rw [Set.Ioc_eq_empty_of_le (not_lt.mp hin), Set.empty_prod]
        rw [hempty]
        exact @MeasurableSet.empty _
          (MeasurableSpace.generateFrom (predictableRectangle 𝓕))

/-- An adapted indicator coefficient. -/
noncomputable def adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    lpMeas ℝ ℝ (𝓕 a) 2 P :=
  ⟨indicatorConstLp 2 (𝓕.le a F hF) (measure_ne_top P F) (1 : ℝ),
    mem_lpMeas_indicatorConstLp (𝓕.le a) hF (measure_ne_top P F)⟩

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
lemma adaptedIndicator_coeFn
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) =ᵐ[P]
      F.indicator (fun _ ↦ (1 : ℝ)) :=
  indicatorConstLp_coeFn (p := 2) (hs := 𝓕.le a F hF)
    (hμs := measure_ne_top P F) (c := (1 : ℝ))

omit [CompleteSpace W] [BorelSpace W] in
/-- An elementary process with an event-indicator coefficient is the indicator of its
predictable rectangle. -/
theorem elementaryPredictable_adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F) :
    (elementaryPredictable (P := P) 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF) :
        TimeProcessL2 P) =
      indicatorConstLp (μ := nonnegativeLebesgueMeasure.prod P) 2
        (measurableSet_Ioc.prod (𝓕.le a F hF))
        (by
          rw [Measure.prod_prod (μ := nonnegativeLebesgueMeasure) (ν := P)]
          exact ENNReal.mul_ne_top
            (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P F))
        (1 : ℝ) := by
  apply Lp.ext
  have hFprod : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) p.2 =
        F.indicator (1 : W → ℝ) p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (adaptedIndicator_coeFn (P := P) 𝓕 a hF)
  filter_upwards [elementaryPredictable_coeFn (P := P) 𝓕 a b
      (adaptedIndicator (P := P) 𝓕 a hF), hFprod,
    indicatorConstLp_coeFn (p := 2)
      (hs := measurableSet_Ioc.prod (𝓕.le a F hF))
      (hμs := by
        rw [Measure.prod_prod (μ := nonnegativeLebesgueMeasure) (ν := P)]
        exact ENNReal.mul_ne_top
          (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (measure_ne_top P F))
      (c := (1 : ℝ))] with p helem hFind hrect
  rw [helem, hrect, hFind]
  by_cases ht : p.1 ∈ Set.Ioc a b <;>
    by_cases hw : p.2 ∈ F <;> simp [ht, hw]

omit [CompleteSpace W] [BorelSpace W] [SecondCountableTopology W] in
lemma inner_elementaryPredictable_adaptedIndicator
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (a b : ℝ≥0)
    {F : Set W} (hF : MeasurableSet[𝓕 a] F)
    (g : PredictableProcessL2 𝓕 P) :
    ⟪elementaryPredictable 𝓕 a b (adaptedIndicator (P := P) 𝓕 a hF), g⟫_ℝ =
      ∫ z in Set.Ioc a b ×ˢ F, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P := by
  rw [Submodule.coe_inner, L2.inner_def]
  have hproc := elementaryPredictable_coeFn 𝓕 a b
    (adaptedIndicator (P := P) 𝓕 a hF)
  have hcoef : ∀ᵐ z : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
      (adaptedIndicator (P := P) 𝓕 a hF : W → ℝ) z.2 =
        F.indicator (fun _ ↦ (1 : ℝ)) z.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp
      (adaptedIndicator_coeFn (P := P) 𝓕 a hF)
  have hae : ∀ᵐ z ∂nonnegativeLebesgueMeasure.prod P,
      (⟪(elementaryPredictable 𝓕 a b
          (adaptedIndicator (P := P) 𝓕 a hF) : ℝ≥0 × W → ℝ) z,
        (g : ℝ≥0 × W → ℝ) z⟫_ℝ : ℝ) =
        (Set.Ioc a b ×ˢ F).indicator (g : ℝ≥0 × W → ℝ) z := by
    filter_upwards [hproc, hcoef] with z hz hZ
    rw [hz, hZ]
    by_cases ht : z.1 ∈ Set.Ioc a b <;>
      by_cases hw : z.2 ∈ F <;> simp [ht, hw]
  rw [integral_congr_ae hae]
  exact integral_indicator (measurableSet_Ioc.prod (𝓕.le a F hF))

/-- The algebraic span of all one-step adapted predictable processes. -/
def elementaryPredictableSpan
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) :
    Submodule ℝ (PredictableProcessL2 𝓕 P) :=
  Submodule.span ℝ {U | ∃ a b : ℝ≥0,
    ∃ _hab : a ≤ b, ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P,
      U = elementaryPredictable 𝓕 a b Z}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
    [SecondCountableTopology W] [IsGaussian P] in
lemma elementaryPredictable_mem_span
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W)) (a b : ℝ≥0)
    (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    elementaryPredictable 𝓕 a b Z ∈ elementaryPredictableSpan (P := P) 𝓕 := by
  apply Submodule.subset_span
  exact ⟨a, b, hab, Z, rfl⟩

omit [CompleteSpace W] [BorelSpace W] in
lemma integral_rectangle_eq_zero_of_orthogonal
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0 := by
  intro R hR
  rcases hR with ⟨F₀, hF₀, rfl⟩ | ⟨a, b, F, hab, hF, rfl⟩
  · apply setIntegral_measure_zero
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  · rw [← inner_elementaryPredictable_adaptedIndicator 𝓕 a b hF g]
    exact horth _ (elementaryPredictable_mem_span 𝓕 a b hab.le
      (adaptedIndicator (P := P) 𝓕 a hF))

omit [CompleteSpace W] [BorelSpace W] in
/-- Vanishing on generating rectangles propagates to every predictable set after restriction
to a finite time frame. -/
lemma integral_restrict_frame_eq_zero_of_rectangles
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (n : ℕ) (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂(nonnegativeLebesgueMeasure.prod P).restrict
        (Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ) = 0 := by
  let μ₀ := nonnegativeLebesgueMeasure.prod P
  let Φ : Set (ℝ≥0 × W) := Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ
  have hΦmem : Φ ∈ predictableRectangle 𝓕 :=
    Or.inr ⟨0, (n : ℝ≥0) + 1, Set.univ, by positivity,
      MeasurableSet.univ, rfl⟩
  have hRpred : ∀ R ∈ predictableRectangle 𝓕,
      MeasurableSet[𝓕.predictable] R := by
    intro R hR
    rw [← generateFrom_predictableRectangle 𝓕]
    exact MeasurableSpace.measurableSet_generateFrom hR
  have hμΦ : μ₀ Φ ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top
      (nonnegativeLebesgueMeasure_Ioc_ne_top 0 ((n : ℝ≥0) + 1))
      (measure_ne_top P Set.univ)
  have hint : Integrable (g : ℝ≥0 × W → ℝ) (μ₀.restrict Φ) :=
    integrableOn_Lp_of_measure_ne_top (g : TimeProcessL2 P) one_le_two hμΦ
  have htotal : ∫ z, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0 :=
    hrect Φ hΦmem
  have hbasic : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0 := by
    intro R hR
    have heq : ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ =
        ∫ z in R ∩ Φ, (g : ℝ≥0 × W → ℝ) z ∂μ₀ := by
      rw [show ∫ z in R, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ =
          ∫ z, (g : ℝ≥0 × W → ℝ) z ∂((μ₀.restrict Φ).restrict R) from rfl,
        Measure.restrict_restrict (predictable_le_prod 𝓕 R (hRpred R hR))]
    rw [heq]
    by_cases hne : (R ∩ Φ).Nonempty
    · exact hrect _ (isPiSystem_predictableRectangle 𝓕 R hR Φ hΦmem hne)
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, setIntegral_empty]
  refine MeasurableSpace.induction_on_inter
    (C := fun s _ ↦ ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict Φ = 0)
    (h_eq := (generateFrom_predictableRectangle 𝓕).symm)
    (h_inter := isPiSystem_predictableRectangle 𝓕)
    (empty := setIntegral_empty)
    (basic := hbasic)
    (compl := ?_) (iUnion := ?_) s hs
  · intro S hS hzero
    have hsplit := integral_add_compl
      (μ := μ₀.restrict Φ) (f := (g : ℝ≥0 × W → ℝ))
      (predictable_le_prod 𝓕 S hS) hint
    linarith
  · intro f hf hfm hzero
    rw [integral_iUnion (fun i ↦ predictable_le_prod 𝓕 (f i) (hfm i))
      hf hint.integrableOn]
    simp only [hzero, tsum_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- Vanishing on the generating predictable rectangles implies vanishing on every
finite-measure predictable set. -/
lemma integral_set_eq_zero_of_rectangles
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (hrect : ∀ R ∈ predictableRectangle 𝓕,
      ∫ z in R, (g : ℝ≥0 × W → ℝ) z
        ∂nonnegativeLebesgueMeasure.prod P = 0)
    (s : Set (ℝ≥0 × W)) (hs : MeasurableSet[𝓕.predictable] s)
    (hμs : (nonnegativeLebesgueMeasure.prod P) s < ∞) :
    ∫ z in s, (g : ℝ≥0 × W → ℝ) z
      ∂nonnegativeLebesgueMeasure.prod P = 0 := by
  let μ₀ := nonnegativeLebesgueMeasure.prod P
  let Φ : ℕ → Set (ℝ≥0 × W) :=
    fun n ↦ Set.Ioc 0 ((n : ℝ≥0) + 1) ×ˢ Set.univ
  have hΦmeas : ∀ n, MeasurableSet (Φ n) :=
    fun _ ↦ measurableSet_Ioc.prod MeasurableSet.univ
  have hΦmono : Monotone Φ := by
    intro n m hnm z hz
    refine ⟨⟨hz.1.1, ?_⟩, hz.2⟩
    apply le_trans hz.1.2
    gcongr
  have hzero : ∀ n,
      ∫ z in s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ = 0 := by
    intro n
    have hn := integral_restrict_frame_eq_zero_of_rectangles 𝓕 g hrect n s hs
    have heq : ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict (Φ n) =
        ∫ z in s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ := by
      rw [show ∫ z in s, (g : ℝ≥0 × W → ℝ) z ∂μ₀.restrict (Φ n) =
          ∫ z, (g : ℝ≥0 × W → ℝ) z
            ∂((μ₀.restrict (Φ n)).restrict s) from rfl,
        Measure.restrict_restrict (predictable_le_prod 𝓕 s hs)]
    exact heq ▸ hn
  have hint : IntegrableOn (g : ℝ≥0 × W → ℝ) s μ₀ :=
    integrableOn_Lp_of_measure_ne_top (g : TimeProcessL2 P) one_le_two hμs.ne
  have htend := tendsto_setIntegral_of_monotone
    (fun n ↦ (predictable_le_prod 𝓕 s hs).inter (hΦmeas n))
    (fun _ _ hnm ↦ Set.inter_subset_inter_right _ (hΦmono hnm))
    (hint.mono_set (Set.iUnion_subset fun _ ↦ Set.inter_subset_left))
  have hzeroUnion :
      ∫ z in ⋃ n, s ∩ Φ n, (g : ℝ≥0 × W → ℝ) z ∂μ₀ = 0 := by
    apply tendsto_nhds_unique htend
    simpa only [hzero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ ↦ (0 : ℝ)) atTop (𝓝 0))
  have hbotnull : μ₀ ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set W)) = 0 := by
    rw [Measure.prod_prod, measure_singleton, zero_mul]
  have hpositive : {z : ℝ≥0 × W | z.1 ≠ 0} ∈ ae μ₀ := by
    rw [show {z : ℝ≥0 × W | z.1 ≠ 0} =
        ({(0 : ℝ≥0)} ×ˢ (Set.univ : Set W))ᶜ by ext ⟨t, w⟩; simp]
    exact compl_mem_ae_iff.mpr hbotnull
  have hcov : ∀ᵐ z ∂μ₀, z ∈ ⋃ n, Φ n := by
    filter_upwards [hpositive] with z hz
    obtain ⟨t, w⟩ := z
    obtain ⟨n, hn⟩ := exists_nat_ge (t : ℝ≥0)
    refine Set.mem_iUnion.mpr ⟨n, ?_⟩
    exact ⟨⟨pos_iff_ne_zero.mpr hz,
      le_trans hn (le_add_of_nonneg_right zero_le_one)⟩, Set.mem_univ w⟩
  have hset : s =ᵐ[μ₀] ⋃ n, s ∩ Φ n := by
    filter_upwards [hcov] with z hz
    apply propext
    constructor
    · intro hzs
      obtain ⟨n, hzn⟩ := Set.mem_iUnion.mp hz
      exact Set.mem_iUnion.mpr ⟨n, hzs, hzn⟩
    · intro hzunion
      obtain ⟨n, hzs, _hzn⟩ := Set.mem_iUnion.mp hzunion
      exact hzs
  exact (setIntegral_congr_set hset).trans hzeroUnion

omit [CompleteSpace W] [BorelSpace W] in
/-- A predictable process orthogonal to every one-step adapted process vanishes almost
everywhere. -/
lemma ae_eq_zero_of_orthogonal_elementaryPredictable
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W))
    (g : PredictableProcessL2 𝓕 P)
    (horth : ∀ U : PredictableProcessL2 𝓕 P,
      U ∈ elementaryPredictableSpan (P := P) 𝓕 → ⟪U, g⟫_ℝ = 0) :
    (g : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] 0 := by
  apply lpMeas.ae_eq_zero_of_forall_setIntegral_eq_zero
    (predictable_le_prod 𝓕) g (by norm_num) (by norm_num)
  · intro s _hs hμs
    exact integrableOn_Lp_of_measure_ne_top
      (g : TimeProcessL2 P) one_le_two hμs.ne
  · intro s hs hμs
    exact integral_set_eq_zero_of_rectangles 𝓕 g
      (integral_rectangle_eq_zero_of_orthogonal 𝓕 g horth) s hs hμs

omit [CompleteSpace W] [BorelSpace W] in
/-- Finite linear combinations of one-step adapted processes are dense in predictable `L²`. -/
theorem dense_elementaryPredictableSpan
    (𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace W)) :
    Dense (elementaryPredictableSpan (P := P) 𝓕 :
      Set (PredictableProcessL2 𝓕 P)) := by
  let _ : Fact (𝓕.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × W))) := ⟨predictable_le_prod 𝓕⟩
  suffices horthbot : (elementaryPredictableSpan (P := P) 𝓕)ᗮ = ⊥ by
    rw [dense_iff_closure_eq, ← Submodule.topologicalClosure_coe,
      Submodule.topologicalClosure_eq_top_iff.mpr horthbot, Submodule.top_coe]
  rw [Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  apply Subtype.ext
  exact (Lp.eq_zero_iff_ae_eq_zero).mpr
    (ae_eq_zero_of_orthogonal_elementaryPredictable 𝓕 g
      (fun U hU ↦ hg U hU))

/-- The one-step Brownian target does not depend on which `ClarkOconeFamily` supplies the
Brownian and natural-filtration proofs. -/
theorem ClarkOconeFamily.elementaryIntegralValue_eq
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (C D : ClarkOconeFamily B P 𝓕) {a b : ℝ≥0} (hab : a ≤ b)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    C.elementaryIntegralValue hab Z = D.elementaryIntegralValue hab Z := by
  apply Lp.ext
  exact (C.coeFn_elementaryIntegralValue hab Z).trans
    (D.coeFn_elementaryIntegralValue hab Z).symm

/-- The elementary compatibility predicate determines the designated integral uniquely on all
predictable `L²`, because the elementary span is dense. -/
theorem ClarkOconeFamily.IsBrownianOnElementary.itoIntegral_eq
    {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    {C D : ClarkOconeFamily B P 𝓕}
    (hC : C.IsBrownianOnElementary) (hD : D.IsBrownianOnElementary) :
    C.itoIntegral = D.itoIntegral := by
  -- isDefEq on ContinuousLinearMap.ext_on costs >200k heartbeats inherently (type
  -- unification of C.itoIntegral and D.itoIntegral). suffices+ext, isClosed_property,
  -- and explicit type annotation all hit the same floor.
  apply ContinuousLinearMap.ext_on
    (s := {U | ∃ a b : ℝ≥0, ∃ _hab : a ≤ b,
      ∃ Z : lpMeas ℝ ℝ (𝓕 a) 2 P, U = elementaryPredictable 𝓕 a b Z})
  · simpa only [elementaryPredictableSpan] using
      (dense_elementaryPredictableSpan (P := P) 𝓕)
  · rintro U ⟨a, b, hab, Z, rfl⟩
    rw [hC hab Z, hD hab Z]
    exact C.elementaryIntegralValue_eq D hab Z

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
