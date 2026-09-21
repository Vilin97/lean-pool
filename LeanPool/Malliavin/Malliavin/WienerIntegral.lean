/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.CameronMartinTheorem
import LeanPool.Malliavin.Malliavin.IteratedIntegral

/-!
# The Wiener integral

The first-order stochastic integral of a deterministic kernel against a pre-Brownian process
`B`: the isometry `J₁ : L²(ℝ≥0) → L²(P)` determined by `J₁ (1_{(0, t]}) = B t`.

## Construction

The indicators `1_{(0, t]}` of the intervals `(0, t]` have dense span in `L²(ℝ≥0)`
(`dense_span_intervalIndicator`): an `L²` function orthogonal to all of them has vanishing
integral over every interval `(a, b]`, so the finite measures `g⁺ λ` and `g⁻ λ` agree on
intervals, hence everywhere (`Measure.ext_of_Ioc_finite`), and `g = 0`.

On the free module `ℝ≥0 →₀ ℝ` the two linear maps `v ↦ ∑ vₜ 1_{(0, t]}` (`stepToLp`) and
`v ↦ ∑ vₜ B t` (`stepToRandom`) have the same Gram matrix, `⟪1_{(0, s]}, 1_{(0, t]}⟫ = min s t =
E[B s B t]`, so the second is bounded by the first and `LinearMap.extendOfNorm` extends it
along the dense map `stepToLp` to the Wiener integral `wienerIntegral hB`.

## Main results

* `Malliavin.dense_span_intervalIndicator`: density of interval indicators in `L²(ℝ≥0)`;
* `Malliavin.wienerIntegral_intervalIndicator`: `J₁ (1_{(0, t]}) = B t`;
* `Malliavin.inner_wienerIntegral`, `norm_wienerIntegral`: the Itô isometry;
* `Malliavin.integral_wienerIntegral`: Wiener integrals are centered;
* `Malliavin.IteratedIntegralFamily.IsBrownian`: the ordered-box compatibility required of
  genuine iterated Itô integrals in addition to the Hilbert-space laws;
* `Malliavin.wienerIntegralKernel_box`, `inner_wienerIntegralKernel`: the transported Wiener
  integral satisfies the order-one Brownian box law, and `IsBrownian.integral_one_eq` shows that
  any Brownian-linked family must use this order-one operator;
* `Malliavin.integral_odd_eq_zero`, `inner_incrementProductLp_wienerIntegral`,
  `norm_sq_incrementProductLp`: odd moments vanish, products of disjoint increments are
  orthogonal to the first chaos, and the product on `(0, 1] × (1, 2]` is nonzero;
* `Malliavin.IteratedIntegralFamily.IsBrownian.not_range_one_le_closure_span_unitIncrementLp`:
  a Brownian family never has its order-one range inside the closed span of the unit increments;
* `Malliavin.hasGaussianLaw_wienerIntegral`, `map_wienerIntegral_eq_gaussianReal`: Wiener
  integrals are Gaussian with law `N(0, ‖f‖²)`;
* `Malliavin.range_wienerIntegral`, `exists_ne_zero_orthogonal_firstChaos`: the range of the
  Wiener integral is the first chaos `closure (span {B t})`, which together with the constants
  is a proper subspace of `L²(P)`; hence orders zero and one of a Brownian family never exhaust
  `L²(P)` (`IsBrownian.not_top_le_closure_sup_zero_one`);
* `Malliavin.IteratedIntegralFamily.box_zero`, `IsBrownian.of_pos`,
  `IteratedIntegralFamily.norm_sq_integral_boxKernel`: the order-zero clause of the link holds for
  every family, and the Hilbert-space laws fix all ordered-box norms;
* `IsBrownian.integral_two_boxKernel`: the Brownian link conditionally fixes the order-two box
  value as the corresponding product of increments.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3 u_4 u_5

recall LinearMap.extendOfNorm_eq {𝕜 : Type u_1} {𝕜₂ : Type u_2} {E : Type u_3} {Eₗ : Type u_4}
    {F : Type u_5} [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜₂] {σ₁₂ : 𝕜 →+* 𝕜₂}
    [AddCommGroup E] [SeminormedAddCommGroup Eₗ] [NormedAddCommGroup F] [Module 𝕜 E]
    [Module 𝕜₂ F] [IsBoundedSMul 𝕜₂ F] [Module 𝕜 Eₗ] [IsBoundedSMul 𝕜 Eₗ] [CompleteSpace F]
    {f : E →ₛₗ[σ₁₂] F} {e : E →ₗ[𝕜] Eₗ} (h_dense : DenseRange e)
    (h_norm : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖) (x : E) : f.extendOfNorm e (e x) = f x

recall MeasureTheory.Measure.ext_of_Ioc_finite {α : Type u_1} [TopologicalSpace α]
    {m : MeasurableSpace α} [SecondCountableTopology α] [LinearOrder α] [OrderTopology α]
    [BorelSpace α] (μ ν : Measure α) [IsFiniteMeasure μ] (hμν : μ Set.univ = ν Set.univ)
    (h : ∀ ⦃a b⦄, a < b → μ (Set.Ioc a b) = ν (Set.Ioc a b)) : μ = ν

recall MeasureTheory.withDensity_eq_iff_of_sigmaFinite {α : Type u_1} {m : MeasurableSpace α}
    {μ : Measure α} [SigmaFinite μ] {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) : μ.withDensity f = μ.withDensity g ↔ f =ᵐ[μ] g

recall MeasureTheory.L2.inner_indicatorConstLp_one {α : Type u_1} {𝕜 : Type u_2} [RCLike 𝕜]
    {m : MeasurableSpace α} {μ : Measure α} {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    (f : Lp 𝕜 2 μ) : ⟪indicatorConstLp 2 hs hμs (1 : 𝕜), f⟫_𝕜 = ∫ x in s, f x ∂μ

recall MeasureTheory.setIntegral_indicatorConstLp {X : Type u_1} {E : Type u_2}
    {mX : MeasurableSpace X} [NormedAddCommGroup E] [NormedSpace ℝ E] {s t : Set X}
    {μ : Measure X} [CompleteSpace E] {p : ℝ≥0∞} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (hμt : μ t ≠ ∞) (e : E) :
    ∫ x in s, indicatorConstLp p ht hμt e x ∂μ = μ.real (t ∩ s) • e

recall MeasureTheory.indicatorConstLp_coeFn {α : Type u_1} {E : Type u_2}
    {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E]
    {s : Set α} {hs : MeasurableSet s} {hμs : μ s ≠ ∞} {c : E} :
    (indicatorConstLp p hs hμs c : α → E) =ᵐ[μ] s.indicator fun _ ↦ c

recall MeasureTheory.ae_restrict_of_ae {α : Type u_1} {m : MeasurableSpace α}
    {μ : Measure α} {s : Set α} {q : α → Prop}
    (h : ∀ᵐ x ∂μ, q x) : ∀ᵐ x ∂μ.restrict s, q x

recall MeasureTheory.Measure.pi_pi {ι : Type u_1} {α : ι → Type u_2}
    [Fintype ι] [(i : ι) → MeasurableSpace (α i)]
    (μ : (i : ι) → Measure (α i)) [∀ i, SigmaFinite (μ i)]
    (s : (i : ι) → Set (α i)) :
    Measure.pi μ (Set.univ.pi s) = ∏ i, μ i (s i)

recall ENNReal.toReal_prod {ι : Type u_1} (s : Finset ι) (f : ι → ℝ≥0∞) :
    (∏ i ∈ s, f i).toReal = ∏ i ∈ s, (f i).toReal

recall real_inner_self_eq_norm_sq {F : Type u_3} [SeminormedAddCommGroup F]
    [InnerProductSpace ℝ F] (x : F) : inner ℝ x x = ‖x‖ ^ 2

recall MeasureTheory.integral_congr_ae {α : Type u_1} {G : Type u_5}
    [NormedAddCommGroup G] [NormedSpace ℝ G] {m : MeasurableSpace α} {μ : Measure α}
    {f g : α → G} (h : f =ᵐ[μ] g) : ∫ a, f a ∂μ = ∫ a, g a ∂μ

recall MeasureTheory.measureReal_def {α : Type u_1} {m : MeasurableSpace α}
    (μ : Measure α) (s : Set α) : μ.real s = (μ s).toReal

recall ENNReal.toReal_ofReal {r : ℝ} (h : 0 ≤ r) : (ENNReal.ofReal r).toReal = r

recall Finset.prod_congr {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι}
    [CommMonoid M] {f g : ι → M} (h : s₁ = s₂) :
    (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g

recall RCLike.inner_apply {𝕜 : Type u_1} [RCLike 𝕜] (x y : 𝕜) :
    inner 𝕜 x y = y * (starRingEnd 𝕜) x

recall Set.indicator_of_mem {α : Type u_1} {M : Type u_3} [Zero M]
    {s : Set α} {a : α} (h : a ∈ s) (f : α → M) : s.indicator f a = f a

recall Set.indicator_of_notMem {α : Type u_1} {M : Type u_3} [Zero M]
    {s : Set α} {a : α} (h : a ∉ s) (f : α → M) : s.indicator f a = 0

recall Set.inter_eq_left {α : Type u_1} {s t : Set α} : s ∩ t = s ↔ s ⊆ t

recall sub_nonneg {α : Type u_1} [AddGroup α] [LE α] [AddRightMono α]
    {a b : α} : 0 ≤ a - b ↔ b ≤ a

recall Finsupp.range_linearCombination {α : Type u_1} {M : Type u_2} (R : Type u_3) [Semiring R]
    [AddCommMonoid M] [Module R M] {v : α → M} :
    LinearMap.range (Finsupp.linearCombination R v) = Submodule.span R (Set.range v)

recall DenseRange.induction_on₂ {α : Type u_1} {β : Type u_2} [TopologicalSpace β] {e : α → β}
    {p : β → β → Prop} (he : DenseRange e) (hp : IsClosed {q : β × β | p q.1 q.2})
    (h : ∀ a₁ a₂, p (e a₁) (e a₂)) (b₁ b₂ : β) : p b₁ b₂

recall ProbabilityTheory.covariance_eq_sub {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {X Y : Ω → ℝ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) :
    covariance X Y μ = (∫ x, (X * Y) x ∂μ) - (∫ x, X x ∂μ) * ∫ x, Y x ∂μ

recall MeasureTheory.indicatorConstLp_disjoint_union {α : Type u_1} {E : Type u_2}
    {m : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α} [NormedAddCommGroup E] {s t : Set α}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hμs : μ s ≠ ∞) (hμt : μ t ≠ ∞)
    (hst : Disjoint s t) (c : E) :
    indicatorConstLp p (hs.union ht) (by finiteness) c =
      indicatorConstLp p hs hμs c + indicatorConstLp p ht hμt c

namespace Malliavin

/-! ### Density of interval indicators in `L²(ℝ≥0)` -/

section Density

theorem nonnegativeLebesgueMeasure_Ioc_ne_top (a b : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Ioc a b) ≠ ∞ := by
  rw [nonnegativeLebesgueMeasure_Ioc]
  exact ENNReal.ofReal_ne_top

theorem nonnegativeLebesgueMeasure_Iic_ne_top (T : ℝ≥0) :
    nonnegativeLebesgueMeasure (Set.Iic T) ≠ ∞ := by
  have hsub : Set.Iic T ⊆ Set.Icc 0 T := fun x hx ↦ ⟨zero_le, hx⟩
  exact ((measure_mono hsub).trans_lt isCompact_Icc.measure_lt_top).ne

/-- A square-integrable function is integrable on every interval `(a, b]`. -/
theorem integrableOn_Ioc_of_memLp {g : ℝ≥0 → ℝ} (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (a b : ℝ≥0) : IntegrableOn g (Set.Ioc a b) nonnegativeLebesgueMeasure := by
  have : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) :=
    isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top a b)
  exact (hg.restrict _).integrable one_le_two

/-- If the integrals of `g` over all intervals `(0, t]` vanish, so do those over all `(a, b]`. -/
theorem setIntegral_Ioc_eq_zero {g : ℝ≥0 → ℝ} (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (h : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0) (a b : ℝ≥0) :
    ∫ s in Set.Ioc a b, g s ∂nonnegativeLebesgueMeasure = 0 := by
  rcases le_or_gt b a with hab | hab
  · rw [Set.Ioc_eq_empty (not_lt.mpr hab)]
    simp only [Measure.restrict_empty, integral_zero_measure]
  · have hunion : Set.Ioc 0 a ∪ Set.Ioc a b = Set.Ioc 0 b :=
      Set.Ioc_union_Ioc_eq_Ioc zero_le hab.le
    have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) :=
      Set.Ioc_disjoint_Ioc.mpr ((min_le_left a b).trans (le_max_right 0 a))
    have := setIntegral_union hdisj measurableSet_Ioc (integrableOn_Ioc_of_memLp hg 0 a)
      (integrableOn_Ioc_of_memLp hg a b)
    rw [hunion, h, h] at this
    linarith

/-- **Uniqueness from interval integrals**: a square-integrable `g` on `ℝ≥0` whose integrals over
all intervals `(0, t]` vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_forall_setIntegral_Ioc {g : ℝ≥0 → ℝ}
    (hg : MemLp g 2 nonnegativeLebesgueMeasure)
    (h : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0) :
    g =ᵐ[nonnegativeLebesgueMeasure] 0 := by
  have hIoc := setIntegral_Ioc_eq_zero hg h
  have hT : ∀ T : ℕ, ∀ᵐ s ∂nonnegativeLebesgueMeasure, s ∈ Set.Iic (T : ℝ≥0) → g s = 0 := by
    intro T
    set μT := nonnegativeLebesgueMeasure.restrict (Set.Iic (T : ℝ≥0)) with hμT
    have : IsFiniteMeasure μT :=
      isFiniteMeasure_restrict.mpr (nonnegativeLebesgueMeasure_Iic_ne_top _)
    have hgT : Integrable g μT := (hg.restrict _).integrable one_le_two
    set gp : ℝ≥0 → ℝ := fun s ↦ max (g s) 0 with hgp_def
    set gm : ℝ≥0 → ℝ := fun s ↦ max (-g s) 0 with hgm_def
    have hgp : Integrable gp μT := hgT.pos_part
    have hgm : Integrable gm μT := hgT.neg_part
    have hgp_nn : ∀ s, 0 ≤ gp s := fun s ↦ le_max_right _ _
    have hgm_nn : ∀ s, 0 ≤ gm s := fun s ↦ le_max_right _ _
    have hsub : ∀ s, gp s - gm s = g s := fun s ↦ max_zero_sub_eq_self (g s)
    -- the integrals of `g` against `μT` over intervals and over the whole space vanish
    have hS : ∀ a b : ℝ≥0, ∫ s in Set.Ioc a b, g s ∂μT = 0 := by
      intro a b
      rw [hμT, Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Iic]
      exact hIoc _ _
    have huniv : ∫ s, g s ∂μT = 0 := by
      have hIic : Set.Iic (T : ℝ≥0) = Set.Icc (0 : ℝ≥0) T := by
        ext x
        simp only [Set.mem_Iic, Set.mem_Icc, zero_le, true_and]
      rw [hμT, hIic, ← setIntegral_congr_set Ioc_ae_eq_Icc]
      exact hIoc _ _
    -- hence the finite measures `gp μT` and `gm μT` agree on intervals and on the whole space
    have hμ : μT.withDensity (fun s ↦ ENNReal.ofReal (gp s)) =
        μT.withDensity (fun s ↦ ENNReal.ofReal (gm s)) := by
      have : IsFiniteMeasure (μT.withDensity (fun s ↦ ENNReal.ofReal (gp s))) :=
        isFiniteMeasure_withDensity_ofReal hgp.hasFiniteIntegral
      apply Measure.ext_of_Ioc_finite
      · rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
          Measure.restrict_univ,
          ← ofReal_integral_eq_lintegral_ofReal hgp (Filter.Eventually.of_forall hgp_nn),
          ← ofReal_integral_eq_lintegral_ofReal hgm (Filter.Eventually.of_forall hgm_nn)]
        congr 1
        have := integral_sub hgp hgm
        simp only [hsub] at this
        linarith
      · intro a b _
        rw [withDensity_apply _ measurableSet_Ioc, withDensity_apply _ measurableSet_Ioc,
          ← ofReal_integral_eq_lintegral_ofReal hgp.integrableOn
            (Filter.Eventually.of_forall hgp_nn),
          ← ofReal_integral_eq_lintegral_ofReal hgm.integrableOn
            (Filter.Eventually.of_forall hgm_nn)]
        congr 1
        have := integral_sub (hgp.integrableOn (s := Set.Ioc a b))
          (hgm.integrableOn (s := Set.Ioc a b))
        simp only [hsub] at this
        linarith [hS a b]
    rw [withDensity_eq_iff_of_sigmaFinite hgp.aemeasurable.ennreal_ofReal
      hgm.aemeasurable.ennreal_ofReal, hμT, Filter.EventuallyEq,
      ae_restrict_iff' measurableSet_Iic] at hμ
    filter_upwards [hμ] with s hs hsT
    have h1 := hs hsT
    rw [ENNReal.ofReal_eq_ofReal_iff (hgp_nn s) (hgm_nn s)] at h1
    have h2 := hsub s
    linarith
  rw [← ae_all_iff] at hT
  filter_upwards [hT] with s hs
  exact hs ⌈s⌉₊ (Nat.le_ceil s)

/-- The indicator of the interval `(0, t]` as an element of `L²(ℝ≥0)`. -/
noncomputable def intervalIndicator (t : ℝ≥0) : Lp ℝ 2 nonnegativeLebesgueMeasure :=
  indicatorConstLp 2 measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t) (1 : ℝ)

/-- The interval indicators `1_{(0, t]}` have dense span in `L²(ℝ≥0)`. -/
theorem dense_span_intervalIndicator :
    Dense (Submodule.span ℝ (Set.range intervalIndicator) :
      Set (Lp ℝ 2 nonnegativeLebesgueMeasure)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have key : ∀ t, ∫ s in Set.Ioc 0 t, g s ∂nonnegativeLebesgueMeasure = 0 := fun t ↦ by
    rw [← L2.inner_indicatorConstLp_one measurableSet_Ioc
      (nonnegativeLebesgueMeasure_Ioc_ne_top 0 t)]
    exact hg _ (Submodule.subset_span ⟨t, rfl⟩)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr (ae_eq_zero_of_forall_setIntegral_Ioc (Lp.memLp g) key)

/-- The Gram matrix of the interval indicators: `⟪1_{(0, s]}, 1_{(0, t]}⟫ = min s t`. -/
theorem inner_intervalIndicator (s t : ℝ≥0) :
    ⟪intervalIndicator s, intervalIndicator t⟫_ℝ = (min s t : ℝ) := by
  unfold intervalIndicator
  rw [L2.inner_indicatorConstLp_one, setIntegral_indicatorConstLp measurableSet_Ioc]
  have hinter : Set.Ioc 0 t ∩ Set.Ioc 0 s = Set.Ioc 0 (min s t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, le_min_iff]
    tauto
  rw [hinter, measureReal_def, nonnegativeLebesgueMeasure_Ioc, smul_eq_mul, mul_one,
    ENNReal.toReal_ofReal (by
      simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero, le_inf_iff,
        NNReal.zero_le_coe, and_self])]
  simp only [NNReal.coe_min, NNReal.coe_zero, sub_zero]

end Density

/-! ### The Wiener integral -/

section WienerIntegral

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The Brownian coordinate `B t` as an element of `L²(P)`. -/
noncomputable def brownianLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) : Lp ℝ 2 P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.toLp (B t)

theorem coeFn_brownianLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    (brownianLp hB t : Ω → ℝ) =ᵐ[P] B t :=
  MemLp.coeFn_toLp _

/-- The Brownian Gram matrix: `E[B s B t] = min s t`. -/
theorem inner_brownianLp (hB : IsPreBrownianReal B P) (s t : ℝ≥0) :
    ⟪brownianLp hB s, brownianLp hB t⟫_ℝ = (min s t : ℝ) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hs := (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two
  have ht := (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hcov := hB.covariance_eval s t
  rw [covariance_eq_sub hs ht, hB.integral_eval, hB.integral_eval, mul_zero, sub_zero,
    NNReal.coe_min] at hcov
  rw [L2.inner_def, ← hcov]
  apply integral_congr_ae
  filter_upwards [coeFn_brownianLp hB s, coeFn_brownianLp hB t] with ω hωs hωt
  rw [hωs, hωt]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm, Pi.mul_apply]

/-- The formal linear combination `v ↦ ∑ₜ vₜ 1_{(0, t]}` in `L²(ℝ≥0)`. -/
noncomputable def stepToLp : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Finsupp.linearCombination ℝ intervalIndicator

/-- The formal linear combination `v ↦ ∑ₜ vₜ B t` in `L²(P)`. -/
noncomputable def stepToRandom (hB : IsPreBrownianReal B P) : (ℝ≥0 →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 P :=
  Finsupp.linearCombination ℝ (brownianLp hB)

theorem stepToLp_single (t : ℝ≥0) (c : ℝ) :
    stepToLp (Finsupp.single t c) = c • intervalIndicator t :=
  Finsupp.linearCombination_single _ _ _

theorem stepToRandom_single (hB : IsPreBrownianReal B P) (t : ℝ≥0) (c : ℝ) :
    stepToRandom hB (Finsupp.single t c) = c • brownianLp hB t :=
  Finsupp.linearCombination_single _ _ _

/-- The Itô isometry on formal step functions. -/
theorem inner_stepToRandom (hB : IsPreBrownianReal B P) (v w : ℝ≥0 →₀ ℝ) :
    ⟪stepToRandom hB v, stepToRandom hB w⟫_ℝ = ⟪stepToLp v, stepToLp w⟫_ℝ := by
  unfold stepToRandom stepToLp
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_brownianLp, inner_intervalIndicator]

theorem norm_stepToRandom (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    ‖stepToRandom hB v‖ = ‖stepToLp v‖ := by
  have h := inner_stepToRandom hB v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem denseRange_stepToLp : DenseRange stepToLp := by
  change Dense (Set.range stepToLp)
  rw [← LinearMap.coe_range, stepToLp, Finsupp.range_linearCombination]
  exact dense_span_intervalIndicator

/-- **The Wiener integral** `J₁ : L²(ℝ≥0) → L²(P)` of a pre-Brownian process: the continuous
linear extension of `1_{(0, t]} ↦ B t`. -/
noncomputable def wienerIntegral (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →L[ℝ] Lp ℝ 2 P :=
  (stepToRandom hB).extendOfNorm stepToLp

theorem wienerIntegral_stepToLp (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    wienerIntegral hB (stepToLp v) = stepToRandom hB v :=
  LinearMap.extendOfNorm_eq denseRange_stepToLp
    ⟨1, fun v ↦ by rw [norm_stepToRandom, one_mul]⟩ v

/-- `J₁ (1_{(0, t]}) = B t`. -/
theorem wienerIntegral_intervalIndicator (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    wienerIntegral hB (intervalIndicator t) = brownianLp hB t := by
  have := wienerIntegral_stepToLp hB (Finsupp.single t 1)
  rwa [stepToLp_single, stepToRandom_single, one_smul, one_smul] at this

/-- `J₁ (1_{(a, b]}) = B b - B a`: the Wiener integral of an interval indicator is the Brownian
increment. -/
theorem wienerIntegral_indicatorConstLp_Ioc (hB : IsPreBrownianReal B P) {a b : ℝ≥0}
    (hab : a ≤ b) :
    wienerIntegral hB (indicatorConstLp 2 measurableSet_Ioc
      (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ)) = brownianLp hB b - brownianLp hB a := by
  have hdisj : Disjoint (Set.Ioc 0 a) (Set.Ioc a b) :=
    Set.Ioc_disjoint_Ioc.mpr ((min_le_left a b).trans (le_max_right 0 a))
  have hunion := indicatorConstLp_disjoint_union (p := 2) (μ := nonnegativeLebesgueMeasure)
    measurableSet_Ioc measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top 0 a)
    (nonnegativeLebesgueMeasure_Ioc_ne_top a b) hdisj (1 : ℝ)
  have hIoc : Set.Ioc 0 a ∪ Set.Ioc a b = Set.Ioc 0 b := Set.Ioc_union_Ioc_eq_Ioc zero_le hab
  rw [← wienerIntegral_intervalIndicator, ← wienerIntegral_intervalIndicator, ← map_sub]
  congr 1
  rw [eq_sub_iff_add_eq, add_comm, intervalIndicator, intervalIndicator, ← hunion]
  congr 1

/-- **The Itô isometry**: `⟪J₁ f, J₁ g⟫ = ⟪f, g⟫`. -/
theorem inner_wienerIntegral (hB : IsPreBrownianReal B P)
    (f g : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪wienerIntegral hB f, wienerIntegral hB g⟫_ℝ = ⟪f, g⟫_ℝ := by
  refine denseRange_stepToLp.induction_on₂
    (p := fun f g ↦ ⟪wienerIntegral hB f, wienerIntegral hB g⟫_ℝ = ⟪f, g⟫_ℝ) ?_ ?_ f g
  · exact isClosed_eq (((wienerIntegral hB).continuous.comp continuous_fst).inner
      ((wienerIntegral hB).continuous.comp continuous_snd))
      (continuous_fst.inner continuous_snd)
  · intro v w
    simp only [wienerIntegral_stepToLp, inner_stepToRandom]

theorem norm_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ‖wienerIntegral hB f‖ = ‖f‖ := by
  have h := inner_wienerIntegral hB f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- The Wiener integral as a linear isometry. -/
noncomputable def wienerIntegralₗᵢ (hB : IsPreBrownianReal B P) :
    Lp ℝ 2 nonnegativeLebesgueMeasure →ₗᵢ[ℝ] Lp ℝ 2 P :=
  ⟨(wienerIntegral hB).toLinearMap, norm_wienerIntegral hB⟩

omit [MeasurableSpace Ω] in
/-- Expectation on `L²(P)` is the pairing with the constant `1`. -/
theorem integral_eq_inner_const {m : MeasurableSpace Ω} (P : Measure Ω) [IsFiniteMeasure P]
    (X : Lp ℝ 2 P) :
    ∫ ω, X ω ∂P = ⟪X, Lp.const 2 P (1 : ℝ)⟫_ℝ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 P (1 : ℝ)] with ω hω
  rw [hω]
  simp only [Function.const_apply, RCLike.inner_apply, conj_trivial, one_mul]

/-- Wiener integrals are centered. -/
theorem integral_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ∫ ω, wienerIntegral hB f ω ∂P = 0 := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hB0 : ∀ t, ⟪brownianLp hB t, Lp.const 2 P (1 : ℝ)⟫_ℝ = 0 := fun t ↦ by
    rw [← integral_eq_inner_const, integral_congr_ae (coeFn_brownianLp hB t), hB.integral_eval]
  rw [integral_eq_inner_const]
  refine denseRange_stepToLp.induction_on f ?_ ?_
  · exact isClosed_eq ((wienerIntegral hB).continuous.inner continuous_const) continuous_const
  · intro v
    rw [wienerIntegral_stepToLp]
    unfold stepToRandom
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, real_inner_smul_left,
      hB0, mul_zero, Finset.sum_const_zero]

/-! ### The Brownian link

The Hilbert-space laws bundled in `IteratedIntegralFamily` (simplex isometry, centering,
orthogonality between orders) do not determine the operators: any isometric embedding of the
simplex spaces onto mutually orthogonal centered subspaces of `L²(P)` satisfies them.  The
genuine iterated Itô integrals must take indicators of ordered boxes to products of Brownian
increments (`chainIntegral`).  We record this compatibility as
`IteratedIntegralFamily.IsBrownian` and prove that the Wiener integral, transported to
`IteratedKernel 1`, satisfies the order-one clause together with the order-one Hilbert-space
laws; it is the order-one level of any Brownian family. -/

section BrownianLink

/-- The ordered box `∏ᵢ (u i, v i]` in `Fin n → ℝ≥0`. -/
def orderedBox {n : ℕ} (u v : Fin n → ℝ≥0) : Set (Fin n → ℝ≥0) :=
  Set.univ.pi fun i ↦ Set.Ioc (u i) (v i)

theorem measurableSet_orderedBox {n : ℕ} (u v : Fin n → ℝ≥0) :
    MeasurableSet (orderedBox u v) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioc

theorem iteratedKernelMeasure_orderedBox_ne_top {n : ℕ} (u v : Fin n → ℝ≥0) :
    iteratedKernelMeasure n (orderedBox u v) ≠ ∞ := by
  rw [orderedBox, iteratedKernelMeasure, Measure.pi_pi]
  exact ENNReal.prod_ne_top fun i _ ↦ nonnegativeLebesgueMeasure_Ioc_ne_top _ _

/-- The indicator of an ordered box as an order-`n` kernel. -/
noncomputable def boxKernel {n : ℕ} (u v : Fin n → ℝ≥0) : IteratedKernel n :=
  indicatorConstLp 2 (measurableSet_orderedBox u v) (iteratedKernelMeasure_orderedBox_ne_top u v)
    (1 : ℝ)

/-- **The Brownian ordered-box compatibility.**  A family satisfying the Hilbert-space laws of
`IteratedIntegralFamily` is *Brownian* for `B` if on the indicator of every ordered box
`u 0 ≤ v 0 ≤ u 1 ≤ v 1 ≤ ⋯ ≤ u (n-1) ≤ v (n-1)` its order-`n` operator is the product of the
Brownian increments `∏ᵢ (B (v i) - B (u i))`.  Genuine iterated Itô integrals must satisfy
this additional compatibility; this file proves its order-one realization, not existence in
all orders. -/
structure IteratedIntegralFamily.IsBrownian (J : IteratedIntegralFamily P) (B : ℝ≥0 → Ω → ℝ) :
    Prop where
  box : ∀ (n : ℕ) (u v : Fin n → ℝ≥0), (∀ i, u i ≤ v i) → (∀ i j, i < j → v i ≤ u j) →
    (fun ω ↦ J.integral n (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v

/-- The order-zero clause of the Brownian link holds for every family: the order-zero kernel
space is one-dimensional and `zeroOrder` identifies `J₀` with the integral. -/
theorem IteratedIntegralFamily.box_zero (J : IteratedIntegralFamily P) (u v : Fin 0 → ℝ≥0) :
    (fun ω ↦ J.integral 0 (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v := by
  have h := J.zeroOrder (boxKernel u v)
  have hint : ∫ t, boxKernel u v t ∂iteratedKernelMeasure 0 = 1 := by
    have hbox : orderedBox u v = Set.univ := by
      ext t
      simp only [orderedBox, Set.mem_pi, Set.mem_univ, Set.mem_Ioc, forall_const,
        IsEmpty.forall_iff]
    rw [boxKernel, integral_congr_ae indicatorConstLp_coeFn, hbox, Set.indicator_univ,
      integral_const, measureReal_def, iteratedKernelMeasure, Measure.pi_empty_univ]
    simp only [ENNReal.toReal_one, smul_eq_mul, mul_one]
  filter_upwards [h] with ω hω
  rw [hω, hint]
  simp only [chainIntegral, Finset.univ_eq_empty, Finset.prod_empty]

/-- To be Brownian it suffices to satisfy the box law at positive orders. -/
theorem IteratedIntegralFamily.IsBrownian.of_pos {J : IteratedIntegralFamily P}
    (h : ∀ (n : ℕ), 0 < n → ∀ (u v : Fin n → ℝ≥0), (∀ i, u i ≤ v i) →
      (∀ i j, i < j → v i ≤ u j) →
      (fun ω ↦ J.integral n (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v) :
    J.IsBrownian B := by
  refine ⟨fun n u v huv hord ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact J.box_zero u v
  · exact h n hn u v huv hord

/-- The Hilbert-space `sameOrder` law alone fixes the squared norm of every ordered-box image.
Brownian ordered-box compatibility is not needed for this norm identity. -/
theorem IteratedIntegralFamily.norm_sq_integral_boxKernel (J : IteratedIntegralFamily P)
    {n : ℕ} (u v : Fin n → ℝ≥0) (huv : ∀ i, u i ≤ v i)
    (hord : ∀ i j, i < j → v i ≤ u j) :
    ‖J.integral n (boxKernel u v)‖ ^ 2 = ∏ i, ((v i : ℝ) - u i) := by
  rw [← real_inner_self_eq_norm_sq, J.sameOrder]
  have hsubset : orderedBox u v ⊆ simplex ℝ≥0 n := by
    intro t ht
    rw [mem_simplex]
    intro i j hij
    have hit : t i ∈ Set.Ioc (u i) (v i) := ht i (Set.mem_univ i)
    have hjt : t j ∈ Set.Ioc (u j) (v j) := ht j (Set.mem_univ j)
    exact lt_of_le_of_lt (hit.2.trans (hord i j hij)) hjt.1
  have hcoe :
      (boxKernel u v : (Fin n → ℝ≥0) → ℝ) =ᵐ[iteratedKernelMeasure n]
        (orderedBox u v).indicator (fun _ ↦ (1 : ℝ)) :=
    indicatorConstLp_coeFn
  calc
    (∫ t in simplex ℝ≥0 n,
        inner ℝ (boxKernel u v t) (boxKernel u v t) ∂iteratedKernelMeasure n) =
        ∫ t in simplex ℝ≥0 n, boxKernel u v t ∂iteratedKernelMeasure n := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hcoe] with t ht
      rw [ht]
      by_cases hmem : t ∈ orderedBox u v
      · simp only [Set.indicator_of_mem hmem, RCLike.inner_apply, conj_trivial, one_mul]
      · simp only [Set.indicator_of_notMem hmem, RCLike.inner_apply, conj_trivial, zero_mul]
    _ = (iteratedKernelMeasure n).real (orderedBox u v ∩ simplex ℝ≥0 n) := by
      unfold boxKernel
      rw [setIntegral_indicatorConstLp (measurableSet_simplex n)]
      simp only [smul_eq_mul, mul_one]
    _ = (iteratedKernelMeasure n).real (orderedBox u v) := by
      rw [Set.inter_eq_left.mpr hsubset]
    _ = ∏ i, ((v i : ℝ) - u i) := by
      rw [measureReal_def, orderedBox, iteratedKernelMeasure, Measure.pi_pi,
        ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro i _
      rw [nonnegativeLebesgueMeasure_Ioc, ENNReal.toReal_ofReal]
      exact sub_nonneg.mpr (by exact_mod_cast huv i)

/-- Transport of the order-one kernel measure to Lebesgue measure on `ℝ≥0`. -/
theorem measurePreserving_funUnique_symm_nnreal :
    MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) ℝ≥0).symm nonnegativeLebesgueMeasure
      (iteratedKernelMeasure 1) :=
  (measurePreserving_funUnique nonnegativeLebesgueMeasure (Fin 1)).symm _

/-- Order-one kernels as square-integrable functions of one time variable. -/
noncomputable def kernelToLine : IteratedKernel 1 →ₗᵢ[ℝ] Lp ℝ 2 nonnegativeLebesgueMeasure :=
  Lp.compMeasurePreservingₗᵢ ℝ _ measurePreserving_funUnique_symm_nnreal

/-- The genuine order-one iterated Itô integral on `IteratedKernel 1`. -/
noncomputable def wienerIntegralKernel (hB : IsPreBrownianReal B P) :
    IteratedKernel 1 →L[ℝ] RandomL2 P :=
  (wienerIntegral hB).comp kernelToLine.toContinuousLinearMap

theorem wienerIntegralKernel_apply (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    wienerIntegralKernel hB f = wienerIntegral hB (kernelToLine f) := rfl

theorem simplex_one : simplex ℝ≥0 1 = Set.univ := by
  ext t
  simp only [Set.mem_univ, iff_true, mem_simplex]
  exact fun a b h ↦ (h.ne (Subsingleton.elim a b)).elim

/-- The simplex Itô isometry at order one. -/
theorem inner_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f g : IteratedKernel 1) :
    ⟪wienerIntegralKernel hB f, wienerIntegralKernel hB g⟫_ℝ =
      ∫ t in simplex ℝ≥0 1, ⟪f t, g t⟫_ℝ ∂iteratedKernelMeasure 1 := by
  rw [simplex_one, Measure.restrict_univ, ← L2.inner_def, wienerIntegralKernel_apply,
    wienerIntegralKernel_apply, inner_wienerIntegral, LinearIsometry.inner_map_map]

theorem integral_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ∫ ω, wienerIntegralKernel hB f ω ∂P = 0 :=
  integral_wienerIntegral hB _

theorem norm_wienerIntegralKernel (hB : IsPreBrownianReal B P) (f : IteratedKernel 1) :
    ‖wienerIntegralKernel hB f‖ = ‖f‖ := by
  rw [wienerIntegralKernel_apply, norm_wienerIntegral, LinearIsometry.norm_map]

theorem kernelToLine_boxKernel {a b : ℝ≥0} :
    kernelToLine (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      indicatorConstLp 2 measurableSet_Ioc (nonnegativeLebesgueMeasure_Ioc_ne_top a b) (1 : ℝ) := by
  have hset : (MeasurableEquiv.funUnique (Fin 1) ℝ≥0).symm ⁻¹'
      orderedBox (fun _ : Fin 1 ↦ a) (fun _ ↦ b) = Set.Ioc a b := by
    ext t
    simp only [MeasurableEquiv.funUnique_symm_apply, orderedBox, Set.mem_preimage, Set.mem_pi,
      Set.mem_univ,
      uniqueElim_const, Set.mem_Ioc, forall_const]
  unfold kernelToLine boxKernel
  change Lp.compMeasurePreserving _ measurePreserving_funUnique_symm_nnreal _ = _
  rw [Lp.indicatorConstLp_compMeasurePreserving]
  congr 1

/-- The Brownian link at order one: `J₁ (1_{(a, b]}) = B b - B a`. -/
theorem wienerIntegralKernel_boxKernel (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    wienerIntegralKernel hB (boxKernel (fun _ : Fin 1 ↦ a) (fun _ ↦ b)) =
      brownianLp hB b - brownianLp hB a := by
  rw [wienerIntegralKernel_apply, kernelToLine_boxKernel,
    wienerIntegral_indicatorConstLp_Ioc hB hab]

/-- The genuine `J₁` satisfies the order-one clause of the Brownian link. -/
theorem wienerIntegralKernel_box (hB : IsPreBrownianReal B P) (u v : Fin 1 → ℝ≥0)
    (huv : ∀ i, u i ≤ v i) :
    (fun ω ↦ wienerIntegralKernel hB (boxKernel u v) ω) =ᵐ[P] chainIntegral B u v := by
  have hu : u = fun _ ↦ u 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  have hv : v = fun _ ↦ v 0 := funext fun i ↦ by rw [Subsingleton.elim i 0]
  rw [hu, hv, wienerIntegralKernel_boxKernel hB (huv 0)]
  filter_upwards [Lp.coeFn_sub (brownianLp hB (v 0)) (brownianLp hB (u 0)),
    coeFn_brownianLp hB (v 0), coeFn_brownianLp hB (u 0)] with ω hsub hv0 hu0
  rw [hsub, Pi.sub_apply, hv0, hu0]
  simp only [Fin.isValue, chainIntegral, Finset.univ_unique, Fin.default_eq_zero, Finset.prod_const,
    Finset.card_singleton, pow_one]

/-- The box indicators `1_{(0, t]}` have dense span among order-one kernels. -/
theorem dense_span_boxKernel_one :
    Dense (Submodule.span ℝ
      (Set.range fun t : ℝ≥0 ↦ boxKernel (fun _ : Fin 1 ↦ 0) (fun _ ↦ t)) :
        Set (IteratedKernel 1)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff,
    Submodule.eq_bot_iff]
  intro g hg
  rw [Submodule.mem_orthogonal] at hg
  have hline : kernelToLine g ∈ (Submodule.span ℝ (Set.range intervalIndicator))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      rw [intervalIndicator, ← kernelToLine_boxKernel, LinearIsometry.inner_map_map]
      exact hg _ (Submodule.subset_span ⟨t, rfl⟩)
    | zero => simp only [inner_zero_left]
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  have hbot : (Submodule.span ℝ (Set.range intervalIndicator))ᗮ = ⊥ := by
    rw [← Submodule.topologicalClosure_eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top]
    exact dense_span_intervalIndicator
  rw [hbot, Submodule.mem_bot] at hline
  exact kernelToLine.injective (by rw [hline, map_zero])

/-- **Uniqueness of the order-one level.**  Any family of operators satisfying the Brownian link
has the Wiener integral as its order-one operator. -/
theorem IteratedIntegralFamily.IsBrownian.integral_one_eq {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    J.integral 1 = wienerIntegralKernel hB := by
  refine ContinuousLinearMap.ext_on dense_span_boxKernel_one ?_
  rintro _ ⟨t, rfl⟩
  have h1 := hJ.box 1 (fun _ ↦ 0) (fun _ ↦ t) (fun _ ↦ zero_le) (fun i j hij ↦
    (hij.ne (Subsingleton.elim i j)).elim)
  have h2 := wienerIntegralKernel_box hB (fun _ : Fin 1 ↦ 0) (fun _ ↦ t) (fun _ ↦ zero_le)
  exact Lp.ext (h1.trans h2.symm)

end BrownianLink

/-! ### Odd moments and a direction beyond the first chaos

The finite-dimensional laws of a pre-Brownian process are invariant under `B ↦ -B`, so all odd
moments vanish.  Consequently the product of two Brownian increments is orthogonal to the whole
first chaos (the range of the Wiener integral) and, for consecutive disjoint intervals, to the
constants, while its squared norm is `(b - a) (d - c)`.  In particular the unit-interval product
on `(0, 1] × (1, 2]` is nonzero, so `ℝ ⊕ H₁` is a proper subspace of `L²(P)`.  Identifying
this product with a second-order chaos additionally requires a Brownian-linked family. -/

section SecondChaos

/-- `L⁴ · L⁴ ⊆ L²`. -/
theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 :=
  ⟨by rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_inv (by norm_num) (by norm_num), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]⟩

/-- **Symmetry of a pre-Brownian process.**  The finite-dimensional laws are invariant under
`B ↦ -B`, so the Bochner integral of an odd measurable function of finitely many coordinates
vanishes.  No integrability hypothesis is needed for this formal statement because Lean's
Bochner integral is zero by convention in the nonintegrable case. -/
theorem integral_odd_eq_zero (hB : IsPreBrownianReal B P) (I : Finset ℝ≥0)
    {f : (I → ℝ) → ℝ} (hf : Measurable f) (hodd : ∀ x, f (-x) = -f x) :
    ∫ ω, f (I.restrict (B · ω)) ∂P = 0 := by
  have h1 := (hB.hasLaw I).integral_comp (f := f) hf.aestronglyMeasurable
  have h2 := (hB.neg.hasLaw I).integral_comp (f := f) hf.aestronglyMeasurable
  have e : (f ∘ fun ω ↦ I.restrict ((-B) · ω)) = fun ω ↦ -f (I.restrict (B · ω)) := by
    funext ω
    rw [Function.comp_apply, ← hodd]
    rfl
  rw [e, integral_neg] at h2
  simp only [Function.comp_apply] at h1
  linarith

/-- Third moments of a pre-Brownian process vanish. -/
theorem integral_mul_mul_eval (hB : IsPreBrownianReal B P) (a b c : ℝ≥0) :
    ∫ ω, B a ω * B b ω * B c ω ∂P = 0 := by
  let I : Finset ℝ≥0 := {a, b, c}
  have ha : a ∈ I := by simp [I]
  have hb : b ∈ I := by simp [I]
  have hc : c ∈ I := by simp [I]
  have := integral_odd_eq_zero hB I (f := fun x ↦ x ⟨a, ha⟩ * x ⟨b, hb⟩ * x ⟨c, hc⟩)
    (by fun_prop) (fun x ↦ by simp only [Pi.neg_apply]; ring)
  simpa [Finset.restrict] using this

/-- Expectation of an odd polynomial: `E[(B b - B a) (B d - B c) B t] = 0`. -/
theorem integral_incr_mul_incr_mul_eval (hB : IsPreBrownianReal B P) (a b c d t : ℝ≥0) :
    ∫ ω, (B b ω - B a ω) * (B d ω - B c ω) * B t ω ∂P = 0 := by
  let I : Finset ℝ≥0 := {a, b, c, d, t}
  have ha : a ∈ I := by simp [I]
  have hb : b ∈ I := by simp [I]
  have hc : c ∈ I := by simp [I]
  have hd : d ∈ I := by simp [I]
  have ht : t ∈ I := by simp [I]
  have := integral_odd_eq_zero hB I
    (f := fun x ↦ (x ⟨b, hb⟩ - x ⟨a, ha⟩) * (x ⟨d, hd⟩ - x ⟨c, hc⟩) * x ⟨t, ht⟩)
    (by fun_prop) (fun x ↦ by simp only [Pi.neg_apply]; ring)
  simpa [Finset.restrict] using this

/-- Brownian coordinates lie in every `Lᵖ`, `p < ∞`. -/
theorem memLp_eval (hB : IsPreBrownianReal B P) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (B t) p P :=
  (hB.isGaussianProcess.hasGaussianLaw_eval t).memLp hp

/-- The product of two Brownian increments is square integrable. -/
theorem memLp_two_incr_mul_incr (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    MemLp (fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω)) 2 P :=
  have := holderTriple_four_four_two
  MemLp.fun_mul ((memLp_eval hB b (p := 4) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB a (p := 4) ENNReal.ofNat_ne_top))
    ((memLp_eval hB d (p := 4) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB c (p := 4) ENNReal.ofNat_ne_top))

/-- The product of two Brownian increments as an element of `L²(P)`. -/
noncomputable def incrementProductLp (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    RandomL2 P :=
  (memLp_two_incr_mul_incr hB a b c d).toLp _

theorem coeFn_incrementProductLp (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0) :
    (incrementProductLp hB a b c d : Ω → ℝ) =ᵐ[P] fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω) :=
  MemLp.coeFn_toLp _

/-- Products of increments are orthogonal to the Brownian coordinates. -/
theorem inner_incrementProductLp_brownianLp (hB : IsPreBrownianReal B P) (a b c d t : ℝ≥0) :
    ⟪incrementProductLp hB a b c d, brownianLp hB t⟫_ℝ = 0 := by
  rw [L2.inner_def, ← integral_incr_mul_incr_mul_eval hB a b c d t]
  apply integral_congr_ae
  filter_upwards [coeFn_incrementProductLp hB a b c d, coeFn_brownianLp hB t] with ω h1 h2
  rw [h1, h2]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- **Products of increments are orthogonal to the first chaos**: for every `f ∈ L²(ℝ≥0)`,
`E[(B b - B a) (B d - B c) J₁ f] = 0`. -/
theorem inner_incrementProductLp_wienerIntegral (hB : IsPreBrownianReal B P) (a b c d : ℝ≥0)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    ⟪incrementProductLp hB a b c d, wienerIntegral hB f⟫_ℝ = 0 := by
  refine denseRange_stepToLp.induction_on f ?_ ?_
  · exact isClosed_eq (continuous_const.inner (wienerIntegral hB).continuous) continuous_const
  · intro v
    rw [wienerIntegral_stepToLp]
    unfold stepToRandom
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, inner_sum, real_inner_smul_right,
      inner_incrementProductLp_brownianLp, mul_zero, Finset.sum_const_zero]

/-- Products of increments over consecutive disjoint intervals are centered. -/
theorem integral_incr_mul_incr (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ∫ ω, (B b ω - B a ω) * (B d ω - B c ω) ∂P = 0 := by
  have h : ⟪brownianLp hB b - brownianLp hB a, brownianLp hB d - brownianLp hB c⟫_ℝ = 0 := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_brownianLp, inner_brownianLp,
      inner_brownianLp, inner_brownianLp,
      min_eq_left (by exact_mod_cast hbc.trans hcd), min_eq_left (by exact_mod_cast hbc),
      min_eq_left (by exact_mod_cast hab.trans (hbc.trans hcd)),
      min_eq_left (by exact_mod_cast hab.trans hbc)]
    ring
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a),
    Lp.coeFn_sub (brownianLp hB d) (brownianLp hB c), coeFn_brownianLp hB a,
    coeFn_brownianLp hB b, coeFn_brownianLp hB c, coeFn_brownianLp hB d] with ω h1 h2 ha hb hc hd
  rw [h1, h2, Pi.sub_apply, Pi.sub_apply, ha, hb, hc, hd]
  simp only [RCLike.inner_apply, conj_trivial, mul_comm]

/-- Increments over consecutive disjoint intervals are independent. -/
theorem indepFun_incr_incr (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    IndepFun (fun ω ↦ B b ω - B a ω) (fun ω ↦ B d ω - B c ω) P := by
  have hmono : Monotone ![a, b, c, d] := by
    refine Fin.monotone_iff_le_succ.mpr ?_
    intro i
    fin_cases i <;> simp [hab, hbc, hcd]
  have := (hB.hasIndepIncrements 3 ![a, b, c, d] hmono).indepFun (i := 0) (j := 2) (by decide)
  simpa only [Fin.isValue, Fin.succ_zero_eq_one, Matrix.cons_val_one, Matrix.cons_val_zero,
    Fin.castSucc_zero, Fin.reduceSucc, Matrix.cons_val, Fin.reduceCastSucc] using this

/-- The variance of a Brownian increment: `E[(B b - B a)²] = b - a`. -/
theorem integral_incr_sq (hB : IsPreBrownianReal B P) {a b : ℝ≥0} (hab : a ≤ b) :
    ∫ ω, (B b ω - B a ω) ^ 2 ∂P = (b : ℝ) - a := by
  have h : ⟪brownianLp hB b - brownianLp hB a, brownianLp hB b - brownianLp hB a⟫_ℝ =
      (b : ℝ) - a := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_brownianLp, inner_brownianLp,
      inner_brownianLp, inner_brownianLp, min_self, min_self,
      min_eq_right (by exact_mod_cast hab), min_eq_left (by exact_mod_cast hab)]
    ring
  rw [L2.inner_def] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (brownianLp hB b) (brownianLp hB a), coeFn_brownianLp hB a,
    coeFn_brownianLp hB b] with ω h1 ha hb
  rw [h1, Pi.sub_apply, ha, hb]
  simp only [sq, inner_self_eq_norm_sq_to_K, Real.norm_eq_abs, RCLike.ofReal_real_eq_id, id_eq,
    abs_mul_abs_self]

/-- Squared norm of a product of two consecutive disjoint Brownian increments. -/
theorem norm_sq_incrementProductLp (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    ‖incrementProductLp hB a b c d‖ ^ 2 = ((b : ℝ) - a) * ((d : ℝ) - c) := by
  have hX : MemLp (fun ω ↦ B b ω - B a ω) 2 P :=
    (memLp_eval hB b (p := 2) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB a (p := 2) ENNReal.ofNat_ne_top)
  have hY : MemLp (fun ω ↦ B d ω - B c ω) 2 P :=
    (memLp_eval hB d (p := 2) ENNReal.ofNat_ne_top).sub
      (memLp_eval hB c (p := 2) ENNReal.ofNat_ne_top)
  have hsq := (indepFun_incr_incr hB hab hbc hcd).integral_fun_comp_mul_comp
    (f := fun x : ℝ ↦ x ^ 2) (g := fun x : ℝ ↦ x ^ 2) hX.aemeasurable hY.aemeasurable
    (by fun_prop) (by fun_prop)
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, ← integral_incr_sq hB hab,
    ← integral_incr_sq hB hcd, ← hsq]
  apply integral_congr_ae
  filter_upwards [coeFn_incrementProductLp hB a b c d] with ω h1
  rw [h1]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

end SecondChaos

/-! ### Wiener integrals are Gaussian

Formal step sums `∑ₜ vₜ B t` are linear functionals of finitely many Brownian coordinates, hence
Gaussian; Wiener integrals are their `L²` limits, so they are Gaussian as well, with law
`N(0, ‖f‖²)` by the Itô isometry. -/

section Gaussian

open CameronMartin

/-- The pointwise formal step sum `∑ₜ vₜ B t`. -/
def stepSum (B : ℝ≥0 → Ω → ℝ) (v : ℝ≥0 →₀ ℝ) : Ω → ℝ :=
  fun ω ↦ v.sum fun t c ↦ c * B t ω

omit [MeasurableSpace Ω] in
theorem stepSum_zero : stepSum B 0 = fun _ ↦ 0 := by
  funext ω
  simp only [stepSum, Finsupp.sum_zero_index]

omit [MeasurableSpace Ω] in
theorem stepSum_single_add (t : ℝ≥0) (c : ℝ) (v : ℝ≥0 →₀ ℝ) :
    stepSum B (Finsupp.single t c + v) = fun ω ↦ c * B t ω + stepSum B v ω := by
  funext ω
  simp only [stepSum]
  rw [Finsupp.sum_add_index' (fun _ ↦ by simp only [zero_mul]) (fun _ _ _ ↦ by ring),
    Finsupp.sum_single_index]
  simp only [zero_mul]

/-- Formal step sums are linear functionals of finitely many Brownian coordinates, hence form a
Gaussian process indexed by `ℝ≥0 →₀ ℝ`. -/
theorem isGaussianProcess_stepSum (hB : IsPreBrownianReal B P) :
    IsGaussianProcess (stepSum B) P := by
  refine hB.isGaussianProcess.of_isGaussianProcess fun v ↦ ⟨v.support,
    LinearMap.toContinuousLinearMap (∑ t : v.support, (v t) • LinearMap.proj t), fun ω ↦ ?_⟩
  simp only [stepSum, Finsupp.sum, Finset.restrict, LinearMap.coe_toContinuousLinearMap',
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
  exact (Finset.sum_attach v.support fun t ↦ v t * B t ω).symm

theorem hasGaussianLaw_stepSum (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    HasGaussianLaw (stepSum B v) P :=
  (isGaussianProcess_stepSum hB).hasGaussianLaw_eval v

theorem coeFn_stepToRandom (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    (stepToRandom hB v : Ω → ℝ) =ᵐ[P] stepSum B v := by
  induction v using Finsupp.induction with
  | zero =>
    rw [map_zero, stepSum_zero]
    exact Lp.coeFn_zero _ _ _
  | single_add t c v _ _ ih =>
    rw [map_add, stepToRandom_single, stepSum_single_add t c v]
    filter_upwards [Lp.coeFn_add (c • brownianLp hB t) (stepToRandom hB v),
      Lp.coeFn_smul c (brownianLp hB t), coeFn_brownianLp hB t, ih] with ω h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, smul_eq_mul]

theorem hasGaussianLaw_stepToRandom (hB : IsPreBrownianReal B P) (v : ℝ≥0 →₀ ℝ) :
    HasGaussianLaw (stepToRandom hB v : Ω → ℝ) P :=
  (hasGaussianLaw_stepSum hB v).congr (coeFn_stepToRandom hB v).symm

/-- **Wiener integrals are Gaussian.** -/
theorem hasGaussianLaw_wienerIntegral (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    HasGaussianLaw (wienerIntegral hB f : Ω → ℝ) P := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.mp (denseRange_stepToLp f)
  choose v hv using hx
  have hlim' : Tendsto (fun n ↦ wienerIntegral hB (x n)) atTop (𝓝 (wienerIntegral hB f)) :=
    ((wienerIntegral hB).continuous.tendsto f).comp hlim
  refine hasGaussianLaw_L2_limit_of_centered P hlim' (fun n ↦ ?_) (fun n ↦ ?_)
  · rw [← hv n, wienerIntegral_stepToLp]
    exact hasGaussianLaw_stepToRandom hB (v n)
  · exact integral_wienerIntegral hB _

/-- **The law of a Wiener integral** is the centered Gaussian with variance `‖f‖²`. -/
theorem map_wienerIntegral_eq_gaussianReal (hB : IsPreBrownianReal B P)
    (f : Lp ℝ 2 nonnegativeLebesgueMeasure) :
    P.map (wienerIntegral hB f) = gaussianReal 0 (‖f‖₊ ^ 2) := by
  have hnn : ‖wienerIntegral hB f‖₊ = ‖f‖₊ := NNReal.eq (by simp [norm_wienerIntegral])
  rw [← hnn]
  exact law_eq_centeredGaussian P _ (hasGaussianLaw_wienerIntegral hB f)
    (integral_wienerIntegral hB f)

end Gaussian

/-! ### The first chaos

The range of the Wiener integral is the Gaussian first chaos `H₁`, the closed span of the
Brownian coordinates; together with the constants it is a proper closed subspace of `L²(P)`. -/

section FirstChaos

/-- The genuine Gaussian first chaos of the process: the closed span of the Brownian
coordinates.  It is not identified here with the selected order-one range of
`iteratedIntegralFamily`. -/
noncomputable def firstChaos (hB : IsPreBrownianReal B P) : Submodule ℝ (RandomL2 P) :=
  (Submodule.span ℝ (Set.range (brownianLp hB))).topologicalClosure

/-- **The first chaos is the range of the Wiener integral.** -/
theorem range_wienerIntegral (hB : IsPreBrownianReal B P) :
    LinearMap.range (wienerIntegral hB).toLinearMap = firstChaos hB := by
  apply le_antisymm
  · -- `J₁ f` is a limit of `J₁ (stepToLp v) = stepToRandom v ∈ span {B t}`
    rintro _ ⟨f, rfl⟩
    refine denseRange_stepToLp.induction_on f ?_ ?_
    · exact (Submodule.isClosed_topologicalClosure _).preimage (wienerIntegral hB).continuous
    · intro v
      rw [ContinuousLinearMap.coe_coe, wienerIntegral_stepToLp]
      apply Submodule.le_topologicalClosure
      unfold stepToRandom
      rw [Finsupp.linearCombination_apply]
      exact Submodule.finsuppSum_mem _ _ _ _ fun t _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)
  · -- the range is closed (isometry from a complete space) and contains every `B t`
    have hclosed : IsClosed (LinearMap.range (wienerIntegral hB).toLinearMap : Set (RandomL2 P)) :=
      (wienerIntegralₗᵢ hB).isometry.isClosedEmbedding.isClosed_range
    refine Submodule.topologicalClosure_minimal _ ?_ hclosed
    rw [Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    exact ⟨intervalIndicator t, wienerIntegral_intervalIndicator hB t⟩

/-- **The first chaos and the constants do not exhaust `L²(P)`**: `(B 1 - B 0)(B 2 - B 1)` is a
nonzero centered element orthogonal to the first chaos. -/
theorem exists_ne_zero_orthogonal_firstChaos (hB : IsPreBrownianReal B P) :
    ∃ Y : RandomL2 P, Y ≠ 0 ∧ ∫ ω, Y ω ∂P = 0 ∧ ∀ Z ∈ firstChaos hB, ⟪Y, Z⟫_ℝ = 0 := by
  refine ⟨incrementProductLp hB 0 1 1 2, ?_, ?_, ?_⟩
  · intro h
    have := norm_sq_incrementProductLp hB (a := 0) (b := 1) (c := 1) (d := 2) zero_le le_rfl
      one_le_two
    rw [h, norm_zero] at this
    norm_num at this
  · rw [integral_congr_ae (coeFn_incrementProductLp hB 0 1 1 2)]
    exact integral_incr_mul_incr hB zero_le le_rfl one_le_two
  · intro Z hZ
    rw [← range_wienerIntegral] at hZ
    obtain ⟨f, rfl⟩ := hZ
    exact inner_incrementProductLp_wienerIntegral hB 0 1 1 2 f

/-- Zero-order integrals of any family are orthogonal to centered random variables. -/
theorem IteratedIntegralFamily.inner_integral_zero_eq_zero (J : IteratedIntegralFamily P)
    {Y : RandomL2 P} (hY : ∫ ω, Y ω ∂P = 0) (f : IteratedKernel 0) :
    ⟪Y, J.integral 0 f⟫_ℝ = 0 := by
  rw [L2.inner_def]
  have h := J.zeroOrder f
  calc ∫ ω, ⟪Y ω, J.integral 0 f ω⟫_ℝ ∂P
      = ∫ ω, Y ω * (∫ t, f t ∂iteratedKernelMeasure 0) ∂P := by
        apply integral_congr_ae
        filter_upwards [h] with ω hω
        rw [hω]
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ = 0 := by rw [integral_mul_const, hY, zero_mul]

/-- **Orders zero and one never exhaust `L²(P)`** for a family satisfying the Brownian link:
`(B 1 - B 0)(B 2 - B 1)` is orthogonal to both. -/
theorem IteratedIntegralFamily.IsBrownian.not_top_le_closure_sup_zero_one
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    ¬ (⊤ : Submodule ℝ (RandomL2 P)) ≤
      (LinearMap.range (J.integral 0).toLinearMap ⊔
        LinearMap.range (J.integral 1).toLinearMap).topologicalClosure := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  intro hle
  obtain ⟨Y, hY0, hYc, hY1⟩ := exists_ne_zero_orthogonal_firstChaos hB
  have horth : Y ∈ (LinearMap.range (J.integral 0).toLinearMap ⊔
      LinearMap.range (J.integral 1).toLinearMap).topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro u hu
    rw [Submodule.mem_sup] at hu
    obtain ⟨a, ⟨f, rfl⟩, b, ⟨g, rfl⟩, rfl⟩ := hu
    rw [inner_add_right, ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_coe,
      J.inner_integral_zero_eq_zero hYc f, hJ.integral_one_eq hB, zero_add]
    apply hY1
    rw [← range_wienerIntegral]
    exact ⟨kernelToLine g, rfl⟩
  rw [Submodule.mem_orthogonal] at horth
  exact hY0 (inner_self_eq_zero.mp (horth Y (hle Submodule.mem_top)))

/-- **The first chaos is Gaussian**: every element has a Gaussian law.  The following theorem
identifies the law's center and variance. -/
theorem hasGaussianLaw_of_mem_firstChaos (hB : IsPreBrownianReal B P) {Z : RandomL2 P}
    (hZ : Z ∈ firstChaos hB) : HasGaussianLaw (Z : Ω → ℝ) P := by
  rw [← range_wienerIntegral] at hZ
  obtain ⟨f, rfl⟩ := hZ
  rw [ContinuousLinearMap.coe_coe]
  exact hasGaussianLaw_wienerIntegral hB f

/-- Every first-chaos element has the centered Gaussian law whose variance is its squared
`L²(P)` norm. -/
theorem map_eq_gaussianReal_of_mem_firstChaos (hB : IsPreBrownianReal B P) {Z : RandomL2 P}
    (hZ : Z ∈ firstChaos hB) : P.map Z = gaussianReal 0 (‖Z‖₊ ^ 2) := by
  rw [← range_wienerIntegral] at hZ
  obtain ⟨f, rfl⟩ := hZ
  rw [ContinuousLinearMap.coe_coe, map_wienerIntegral_eq_gaussianReal]
  congr 2
  exact NNReal.eq (by simp [norm_wienerIntegral])

/-- For a Brownian family, the order-two operator sends the indicator of an ordered box
`(a, b] × (c, d]` to the product of increments `(B b - B a) (B d - B c)`. -/
theorem IteratedIntegralFamily.IsBrownian.integral_two_boxKernel {J : IteratedIntegralFamily P}
    (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) {a b c d : ℝ≥0} (hab : a ≤ b)
    (hbc : b ≤ c) (hcd : c ≤ d) :
    J.integral 2 (boxKernel ![a, c] ![b, d]) = incrementProductLp hB a b c d := by
  apply Lp.ext
  have h := hJ.box 2 ![a, c] ![b, d] (fun i ↦ by fin_cases i <;> simp [hab, hcd])
    (fun i j hij ↦ by
      fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hij ⊢ <;>
        first | exact absurd hij (lt_irrefl _) | exact hbc | exact absurd hij (by decide))
  refine h.trans ?_
  refine (coeFn_incrementProductLp hB a b c d).symm.mono fun ω hω ↦ ?_
  rw [← hω]
  simp only [chainIntegral, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

/-- For a Brownian-linked family, the conditional order-two box value has squared norm
`(b - a) (d - c)`.  The norm formula itself is already an instance of
`IteratedIntegralFamily.norm_sq_integral_boxKernel`; the Brownian hypothesis is needed for the
preceding increment-product value identity. -/
theorem IteratedIntegralFamily.IsBrownian.norm_sq_integral_two_boxKernel
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P)
    {a b c d : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ‖J.integral 2 (boxKernel ![a, c] ![b, d])‖ ^ 2 = ((b : ℝ) - a) * ((d : ℝ) - c) := by
  rw [hJ.integral_two_boxKernel hB hab hbc hcd, norm_sq_incrementProductLp hB hab hbc hcd]

end FirstChaos

/-! ### Unit-increment embeddings are not Brownian

Embedding the kernel spaces isometrically into the closed span of the unit increments
`B (k + 1) - B k` produces families satisfying all the Hilbert-space laws, but never the
Brownian link: the order-one operator of a Brownian family is the Wiener integral, whose range
contains `B (1/2)`, and `B (1/2)` is not in the closed span of the unit increments. -/

section UnitIncrements

/-- The unit Brownian increments `B (k + 1) - B k` in `L²(P)`. -/
noncomputable def unitIncrementLp (hB : IsPreBrownianReal B P) (k : ℕ) : RandomL2 P :=
  brownianLp hB (k + 1) - brownianLp hB k

theorem inner_brownianLp_unitIncrementLp (hB : IsPreBrownianReal B P) (t : ℝ≥0) (k : ℕ) :
    ⟪brownianLp hB t, unitIncrementLp hB k⟫_ℝ = min (t : ℝ) (k + 1) - min (t : ℝ) k := by
  unfold unitIncrementLp
  rw [inner_sub_right, inner_brownianLp, inner_brownianLp]
  push_cast
  ring

/-- `B (1/2)` does not lie in the closed span of the unit increments: its inner product with
`B 1 - B 0` is `1/2` and with all other unit increments `0`, while `‖B (1/2)‖² = 1/2 ≠ 1/4`. -/
theorem brownianLp_half_notMem_closure_span_unitIncrementLp (hB : IsPreBrownianReal B P) :
    brownianLp hB (1 / 2) ∉
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by
  intro hmem
  set x := brownianLp hB (1 / 2) with hx
  set e₀ := unitIncrementLp hB 0 with he₀
  -- inner products of `x` with the unit increments
  have hx0 : ⟪x, e₀⟫_ℝ = 1 / 2 := by
    rw [hx, he₀, inner_brownianLp_unitIncrementLp]
    norm_num
  have hxk : ∀ k : ℕ, 1 ≤ k → ⟪x, unitIncrementLp hB k⟫_ℝ = 0 := by
    intro k hk
    rw [hx, inner_brownianLp_unitIncrementLp]
    have h1 : ((1 / 2 : ℝ≥0) : ℝ) ≤ k := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      norm_num
      linarith
    rw [min_eq_left (h1.trans (by linarith)), min_eq_left h1, sub_self]
  -- the unit increments are orthonormal
  have hee : ∀ k : ℕ, ⟪e₀, unitIncrementLp hB k⟫_ℝ = if k = 0 then 1 else 0 := by
    intro k
    have h0 : e₀ = brownianLp hB ((0 : ℕ) + 1) - brownianLp hB (0 : ℕ) := rfl
    rw [h0, inner_sub_left, inner_brownianLp_unitIncrementLp, inner_brownianLp_unitIncrementLp]
    push_cast
    simp only [zero_add]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · norm_num
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      rw [ite_eq_right hk.ne', min_eq_left (by linarith), min_eq_left h1, min_eq_left (by linarith),
        min_eq_left (by linarith)]
      ring
  -- `y := x - (1/2) e₀` lies in the closed span and is orthogonal to every generator
  set y := x - (1 / 2 : ℝ) • e₀ with hy
  have hymem : y ∈ (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure :=
    Submodule.sub_mem _ hmem (Submodule.smul_mem _ _
      (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨0, rfl⟩)))
  have hyk : ∀ k : ℕ, ⟪y, unitIncrementLp hB k⟫_ℝ = 0 := by
    intro k
    rw [hy, inner_sub_left, real_inner_smul_left, hee]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [ite_eq_left rfl, ← he₀, hx0]
      ring
    · rw [ite_eq_right hk.ne', hxk k hk]
      ring
  have hyorth : y ∈ (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosureᗮ := by
    rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
    intro u hu
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨k, rfl⟩ := hu
      exact hyk k
    | zero => simp only [inner_zero_right]
    | add u v _ _ hu hv => rw [inner_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [real_inner_smul_right, hu, mul_zero]
  -- hence `y = 0`, so `x = (1/2) e₀`, contradicting `‖x‖² = 1/2`
  have hy0 : y = 0 := by
    rw [Submodule.mem_orthogonal] at hyorth
    exact inner_self_eq_zero.mp (hyorth y hymem)
  have hxx : ⟪x, x⟫_ℝ = 1 / 2 := by
    rw [hx, inner_brownianLp]
    norm_num
  have hx' : x = (1 / 2 : ℝ) • e₀ := by
    rw [hy] at hy0
    exact sub_eq_zero.mp hy0
  have he₀e₀ : ⟪e₀, e₀⟫_ℝ = 1 := by
    have := hee 0
    rwa [ite_eq_left rfl, ← he₀] at this
  rw [hx', real_inner_smul_left, real_inner_smul_right, he₀e₀] at hxx
  norm_num at hxx

/-- `B 0 = 0` in `L²(P)`. -/
theorem brownianLp_zero (hB : IsPreBrownianReal B P) : brownianLp hB 0 = 0 := by
  apply Lp.ext
  filter_upwards [coeFn_brownianLp hB 0, hB.eval_zero_ae_eq_zero, Lp.coeFn_zero ℝ 2 P]
    with ω h1 h2 h3
  rw [h1, h2, h3, Pi.zero_apply]

/-- **No family satisfying the Brownian link has its order-one range inside the closed span of
the unit increments** `B (k + 1) - B k`: the order-one operator is the Wiener integral, whose
range contains `B (1/2)`. -/
theorem IteratedIntegralFamily.IsBrownian.not_range_one_le_closure_span_unitIncrementLp
    {J : IteratedIntegralFamily P} (hJ : J.IsBrownian B) (hB : IsPreBrownianReal B P) :
    ¬ LinearMap.range (J.integral 1).toLinearMap ≤
      (Submodule.span ℝ (Set.range (unitIncrementLp hB))).topologicalClosure := by
  intro hle
  apply brownianLp_half_notMem_closure_span_unitIncrementLp hB
  have h1 : J.integral 1 (boxKernel (fun _ : Fin 1 ↦ 0) (fun _ ↦ 1 / 2)) =
      brownianLp hB (1 / 2) := by
    rw [hJ.integral_one_eq hB, wienerIntegralKernel_boxKernel hB (by norm_num), brownianLp_zero,
      sub_zero]
  rw [← h1]
  exact hle ⟨_, rfl⟩

end UnitIncrements

end WienerIntegral

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
