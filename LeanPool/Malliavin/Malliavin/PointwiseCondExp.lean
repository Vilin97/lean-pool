/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import LeanPool.Malliavin.Malliavin.ClarkOcone
import LeanPool.Malliavin.Malliavin.WienerChaos
import Mathlib.Probability.Kernel.Condexp
import Mathlib.Probability.ConditionalExpectation

/-!
# Pointwise conditional expectations via the disintegration kernel

The ambient sample space `W` of the development is a complete second-countable normed space with
its Borel σ-algebra, hence a standard Borel space, and the Gaussian measure `P` is finite.
Mathlib's `condExpKernel P (𝓕 t)` therefore exists for every time `t`, and
`condExp_ae_eq_integral_condExpKernel` turns each fixed-time conditional expectation into an
honest pointwise integral

  `P[F | 𝓕 t] =ᵐ[P] fun ω ↦ ∫ y, F y ∂condExpKernel P (𝓕 t) ω`.

This file records the consequences for the Clark--Ocone development:

* `filtrationCondExpL2_ae_eq_integral_condExpKernel`: the fixed-time operator
  `filtrationCondExpL2` of `ClarkOcone.lean` is the kernel integral, almost everywhere;
* `condExp_timeSection_ae_eq_integral_condExpKernel`: for `U ∈ L²(ℝ≥0 × W)` and almost every
  time `t`, the conditional expectation of the time section `U (t, ·)` is the kernel integral
  `ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω` — this is the pointwise `E[Dₜ F | 𝓕ₜ]`
  formula, valid for almost every `t` with a null set that may depend on the representative;
* `setIntegral_predictableProjection`: the predictable projection preserves integrals over
  *every* predictable set of finite measure, not only over the rectangles recorded in
  `ClarkOcone.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal InnerProductSpace

namespace Malliavin

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]

/-- The fixed-time conditional expectation operator of the Clark--Ocone development is,
almost everywhere, the integral against the disintegration kernel `condExpKernel P (𝓕 t)`. -/
theorem filtrationCondExpL2_ae_eq_integral_condExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (t : ℝ≥0) (F : RandomL2 P) :
    (filtrationCondExpL2 𝓕 t F : W → ℝ) =ᵐ[P]
      fun ω ↦ ∫ y, F y ∂condExpKernel P (𝓕 t) ω :=
  (filtrationCondExpL2_ae_eq_condExp 𝓕 t F).trans
    (condExp_ae_eq_integral_condExpKernel (𝓕.le t) ((Lp.memLp F).integrable one_le_two))

/-- **Pointwise conditional expectation of time sections.**  For a product-`L²` process `U` and
almost every time `t`, the conditional expectation of the section `U (t, ·)` given `𝓕 t` is the
pointwise kernel integral `ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω`.  The exceptional set of
times depends on the chosen representative of `U`. -/
theorem condExp_timeSection_ae_eq_integral_condExpKernel
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      P[(fun ω ↦ U (t, ω)) | 𝓕 t] =ᵐ[P]
        fun ω ↦ ∫ y, U (t, y) ∂condExpKernel P (𝓕 t) ω := by
  filter_upwards [memLp_timeSection_ae U] with t ht
  exact condExp_ae_eq_integral_condExpKernel (𝓕.le t) (ht.integrable one_le_two)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- The predictable projection preserves integrals over every predictable set of finite
measure.  This extends `integral_predictableProjection_Ioc` from predictable rectangles to the
whole predictable σ-algebra. -/
theorem setIntegral_predictableProjection
    (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›) (U : TimeProcessL2 P) {s : Set (ℝ≥0 × W)}
    (hs : MeasurableSet[𝓕.predictable] s) (hμs : (nonnegativeLebesgueMeasure.prod P) s ≠ ∞) :
    ∫ x in s, (predictableProjection 𝓕 U : (ℝ≥0 × W) → ℝ) x ∂(nonnegativeLebesgueMeasure.prod P)
      = ∫ x in s, U x ∂(nonnegativeLebesgueMeasure.prod P) :=
  integral_condExpL2_eq (predictable_le_prod 𝓕) U hs hμs

/-! ### Sections of the predictable projection

For fixed `a` and `A ∈ 𝓕 a`, the sections of `predictableProjection 𝓕 U` carry the conditional
moments of `U` against `A` for almost every time `t > a`.  The exceptional null set of times
depends on `(a, A)`; upgrading to a null set uniform over all `A` (the genuine pointwise
`E[Uₜ | 𝓕ₜ]` identification) would require countable generation of the filtration. -/

section Sections

variable (𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›)

omit [CompleteSpace W] [BorelSpace W] in
/-- A window integral of the section integrals of the difference vanishes on every interval. -/
theorem setIntegral_timeSection_sub_eq_zero (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A)
    (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    {c d : ℝ≥0} (hac : a ≤ c) :
    ∫ t in Set.Ioc c d, ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P
      ∂nonnegativeLebesgueMeasure = 0 := by
  set μ := nonnegativeLebesgueMeasure.prod P with hμ
  have hrect : μ (Set.Ioc c d ×ˢ A) ≠ ∞ := by
    rw [hμ, Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
  have hQint := integrableOn_Lp_of_measure_ne_top
    (predictableProjection 𝓕 U : TimeProcessL2 P) fact_one_le_two_ennreal.elim hrect
  have hUint := integrableOn_Lp_of_measure_ne_top U fact_one_le_two_ennreal.elim hrect
  have hprod : ∫ x in Set.Ioc c d ×ˢ A, (D : ℝ≥0 × W → ℝ) x ∂μ = 0 := by
    calc ∫ x in Set.Ioc c d ×ˢ A, (D : ℝ≥0 × W → ℝ) x ∂μ
        = ∫ x in Set.Ioc c d ×ˢ A,
            ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x) ∂μ :=
          setIntegral_congr_ae ((measurableSet_Ioc.prod (𝓕.le a A hA)))
            (hD.mono fun x hx _ ↦ hx)
      _ = (∫ x in Set.Ioc c d ×ˢ A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x ∂μ) -
            ∫ x in Set.Ioc c d ×ˢ A, U x ∂μ := integral_sub hQint hUint
      _ = 0 := by
          rw [setIntegral_predictableProjection 𝓕 U
            (measurableSet_predictable_Ioc_prod c d (𝓕.mono hac A hA)) hrect, sub_self]
  rw [setIntegral_prod _ hDint] at hprod
  exact hprod

omit [CompleteSpace W] [BorelSpace W] in
/-- All window integrals of the section-integral function of the difference vanish. -/
theorem setIntegral_g_eq_zero (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) (D : TimeProcessL2 P)
    (hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x)
    (b : ℝ≥0) {s : Set ℝ≥0} (hs : MeasurableSet s) :
    ∫ t in s, (∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P)
      ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
  set g : ℝ≥0 → ℝ := fun t ↦ ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P with hg
  have hrect : (nonnegativeLebesgueMeasure.prod P) (Set.Ioc a b ×ˢ A) ≠ ∞ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
  have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
  have hgint : Integrable g (nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) := by
    have h1 : Integrable (D : ℝ≥0 × W → ℝ)
        ((nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)).prod (P.restrict A)) := by
      rw [Measure.prod_restrict]
      exact hDint
    exact h1.integral_prod_left
  -- the property holds on the generating π-system of intervals
  have hbase : ∀ c d : ℝ≥0, ∫ t in Set.Ioc c d, g t
      ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
    intro c d
    rw [Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc]
    exact setIntegral_timeSection_sub_eq_zero 𝓕 U hA D hD (le_max_right c a)
  -- extend to all measurable sets
  induction s, hs using MeasurableSpace.induction_on_inter
    (m := (inferInstance : MeasurableSpace ℝ≥0))
    (s := { S : Set ℝ≥0 | ∃ l u : ℝ≥0, l < u ∧ Set.Ioc l u = S })
    (h_eq := BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ≥0))
    (h_inter := isPiSystem_Ioc (id : ℝ≥0 → ℝ≥0) (id : ℝ≥0 → ℝ≥0)) with
  | empty => simp
  | basic s hs =>
      obtain ⟨c, d, -, rfl⟩ := hs
      exact hbase c d
  | compl s hs hind =>
      have htotal : ∫ t, g t ∂(nonnegativeLebesgueMeasure.restrict (Set.Ioc a b)) = 0 := by
        have := hbase a b
        rwa [Measure.restrict_restrict measurableSet_Ioc, Set.inter_self] at this
      have hsplit := integral_add_compl hs hgint
      rw [hind, zero_add] at hsplit
      rw [hsplit, htotal]
  | iUnion f hdis hmeas hind =>
      rw [integral_iUnion hmeas hdis hgint.integrableOn]
      simp only [hind, tsum_zero]

omit [CompleteSpace W] [BorelSpace W] in
/-- **Sections of the predictable projection carry the conditional moments of `U`**: for every
`a` and every `A ∈ 𝓕 a`, for almost every time `t > a`,

  `∫_A (predictableProjection 𝓕 U) (t, ·) dP = ∫_A U (t, ·) dP`.

The null set of times depends on `(a, A)`.  Together with the `𝓕 t`-measurability of the
sections this is the conditional-moment content of `E[Uₜ | 𝓕ₜ]` against every strictly prior
event. -/
theorem setIntegral_timeSection_predictableProjection_ae (U : TimeProcessL2 P) {a : ℝ≥0}
    {A : Set W} (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, U (t, ω) ∂P := by
  set Q : TimeProcessL2 P := (predictableProjection 𝓕 U : TimeProcessL2 P) with hQ
  set D : TimeProcessL2 P := Q - U with hDdef
  have hD : (D : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun x ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) x - U x := Lp.coeFn_sub Q U
  -- on each window the section integral of the difference vanishes a.e.
  have hwin : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      t ∈ Set.Ioc a (a + (n + 1 : ℕ)) →
        ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P = 0 := by
    intro n
    refine ae_imp_of_ae_restrict ?_
    have hrect : (nonnegativeLebesgueMeasure.prod P) (Set.Ioc a (a + (n + 1 : ℕ)) ×ˢ A) ≠ ∞ := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Ioc_lt_top.ne (measure_lt_top P A).ne
    have hDint := integrableOn_Lp_of_measure_ne_top D fact_one_le_two_ennreal.elim hrect
    have hgint : Integrable (fun t ↦ ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        (nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ)))) := by
      have h1 : Integrable (D : ℝ≥0 × W → ℝ)
          ((nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ)))).prod
            (P.restrict A)) := by
        rw [Measure.prod_restrict]
        exact hDint
      exact h1.integral_prod_left
    exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s hs _ ↦ hgint.integrableOn)
      (fun s hs _ ↦ setIntegral_g_eq_zero 𝓕 U hA D hD _ hs)
  -- sections of the difference are the difference of sections, and sections are integrable
  have hsec := Measure.ae_ae_of_ae_prod hD
  have hQsec := memLp_timeSection_ae Q
  have hUsec := memLp_timeSection_ae U
  have hwin' := ae_all_iff.mpr hwin
  filter_upwards [hwin', hsec, hQsec, hUsec] with t hwt hst hQt hUt hat
  obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
  have htmem : t ∈ Set.Ioc a (a + (n + 1 : ℕ)) := by
    refine ⟨hat, ?_⟩
    have : t - a ≤ (n + 1 : ℕ) := hn.trans (by exact_mod_cast Nat.le_succ n)
    calc t = a + (t - a) := by rw [add_tsub_cancel_of_le hat.le]
      _ ≤ a + (n + 1 : ℕ) := by gcongr
  have hzero := hwt n htmem
  have hcongr : ∫ ω in A, (D : ℝ≥0 × W → ℝ) (t, ω) ∂P
      = ∫ ω in A, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω)) ∂P :=
    setIntegral_congr_ae (𝓕.le a A hA) (hst.mono fun ω hω _ ↦ hω)
  have hsub : ∫ ω in A, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω)) ∂P
      = (∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        - ∫ ω in A, U (t, ω) ∂P :=
    integral_sub ((hQt.integrable one_le_two).integrableOn)
      ((hUt.integrable one_le_two).integrableOn)
  rw [hcongr, hsub] at hzero
  linarith [hzero]

omit [CompleteSpace W] [BorelSpace W] in
/-- **Conditional-moment identification of the sections**: for every `a` and `A ∈ 𝓕 a`, for
almost every `t > a` the section of the predictable projection has the same integral over `A`
as the fixed-time conditional expectation `E[U (t, ·) | 𝓕 t]`. -/
theorem setIntegral_timeSection_eq_condExp_ae (U : TimeProcessL2 P) {a : ℝ≥0} {A : Set W}
    (hA : MeasurableSet[𝓕 a] A) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω in A, (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) ∂P
        = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by
  filter_upwards [setIntegral_timeSection_predictableProjection_ae 𝓕 U hA,
    memLp_timeSection_ae U] with t ht hUt hat
  rw [ht hat]
  exact (setIntegral_condExp (𝓕.le t) (hUt.integrable one_le_two)
    (𝓕.mono hat.le A hA)).symm

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] in
/-- The map `ω ↦ (t, ω)` is measurable from `𝓕 t` to the predictable σ-algebra. -/
theorem measurable_section_predictable (t : ℝ≥0) :
    @Measurable W (ℝ≥0 × W) (𝓕 t) 𝓕.predictable (fun ω ↦ (t, ω)) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
  · intro A hA
    rw [MeasurableSpace.map_def]
    rcases eq_or_ne t 0 with ht | ht
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' ({⊥} ×ˢ A) = A := by
        ext ω
        simp only [ht, bot_eq_zero', Set.mem_singleton_iff, Set.mk_preimage_prod_right]
      rw [this]
      exact 𝓕.mono (by simp [ht]) A hA
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by
        ext ω
        simp only [bot_eq_zero', Set.mem_singleton_iff, ht, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (𝓕 t)
  · intro i A hA
    rw [MeasurableSpace.map_def]
    rcases lt_or_ge i t with hit | hit
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = A := by
        ext ω
        simp only [Set.mem_Ioi, hit, Set.mk_preimage_prod_right]
      rw [this]
      exact 𝓕.mono hit.le A hA
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by
        ext ω
        simp only [Set.mem_Ioi, not_lt.mpr hit, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (𝓕 t)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] in
/-- Sections of predictable strongly measurable processes are `𝓕 t`-strongly measurable, for
every `t`. -/
theorem stronglyMeasurable_timeSection_of_predictable {V : ℝ≥0 × W → ℝ}
    (hV : StronglyMeasurable[𝓕.predictable] V) (t : ℝ≥0) :
    StronglyMeasurable[𝓕 t] fun ω ↦ V (t, ω) :=
  hV.comp_measurable (measurable_section_predictable 𝓕 t)

omit [CompleteSpace W] [BorelSpace W] in
/-- **Pointwise representative of the predictable projection.**  The predictable projection of
`U` has a representative `G` that is strongly measurable for the predictable σ-algebra, whose
time section at *every* time `t` is `𝓕 t`-strongly measurable, and whose sections carry the
conditional moments of `U`: for every `a` and `A ∈ 𝓕 a`, for almost every `t > a`,

  `∫_A G (t, ·) dP = ∫_A E[U (t, ·) | 𝓕 t] dP`.

This is the pointwise `E[Uₜ | 𝓕ₜ]` content of the product-`L²` projection: only the uniformity
of the exceptional times over the generating events is left open. -/
theorem exists_representative_predictableProjection (U : TimeProcessL2 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ t, StronglyMeasurable[𝓕 t] fun ω ↦ G (t, ω)) ∧
      ∀ (a : ℝ≥0) (A : Set W), MeasurableSet[𝓕 a] A →
        ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
          ∫ ω in A, G (t, ω) ∂P
            = ∫ ω in A, (P[(fun ω ↦ U (t, ω)) | 𝓕 t]) ω ∂P := by
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableProjection 𝓕 U : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  refine ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk, fun t ↦
    stronglyMeasurable_timeSection_of_predictable 𝓕 hmeas.stronglyMeasurable_mk t,
    fun a A hA ↦ ?_⟩
  have hsec := Measure.ae_ae_of_ae_prod hmeas.ae_eq_mk
  filter_upwards [setIntegral_timeSection_eq_condExp_ae 𝓕 U hA, hsec] with t ht hst hat
  rw [← ht hat]
  exact setIntegral_congr_ae (𝓕.le a A hA) (hst.mono fun ω hω _ ↦ hω.symm)

omit [CompleteSpace W] [BorelSpace W] in
/-- A locally integrable function on `(a, ∞)` whose integrals over all intervals `(c, d]` with
`a ≤ c` vanish is zero almost everywhere on `(a, ∞)`. -/
theorem ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero {h : ℝ≥0 → ℝ} {a : ℝ≥0}
    (hloc : ∀ b : ℝ≥0, IntegrableOn h (Set.Ioc a b) nonnegativeLebesgueMeasure)
    (hzero : ∀ c d : ℝ≥0, a ≤ c →
      ∫ t in Set.Ioc c d, h t ∂nonnegativeLebesgueMeasure = 0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t → h t = 0 := by
  have hwin : ∀ n : ℕ, ∀ᵐ t ∂nonnegativeLebesgueMeasure,
      t ∈ Set.Ioc a (a + (n + 1 : ℕ)) → h t = 0 := by
    intro n
    refine ae_imp_of_ae_restrict ?_
    set ν := nonnegativeLebesgueMeasure.restrict (Set.Ioc a (a + (n + 1 : ℕ))) with hν
    have hbase : ∀ c d : ℝ≥0, ∫ t in Set.Ioc c d, h t ∂ν = 0 := by
      intro c d
      rw [hν, Measure.restrict_restrict measurableSet_Ioc, Set.Ioc_inter_Ioc]
      exact hzero _ _ (le_max_right c a)
    have hint : Integrable h ν := hloc _
    have hall : ∀ s : Set ℝ≥0, MeasurableSet s → ∫ t in s, h t ∂ν = 0 := by
      intro s hs
      induction s, hs using MeasurableSpace.induction_on_inter
        (m := (inferInstance : MeasurableSpace ℝ≥0))
        (s := { S : Set ℝ≥0 | ∃ l u : ℝ≥0, l < u ∧ Set.Ioc l u = S })
        (h_eq := BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Ioc ℝ≥0))
        (h_inter := isPiSystem_Ioc (id : ℝ≥0 → ℝ≥0) (id : ℝ≥0 → ℝ≥0)) with
      | empty => simp
      | basic s hs =>
          obtain ⟨c, d, -, rfl⟩ := hs
          exact hbase c d
      | compl s hs hind =>
          have htotal : ∫ t, h t ∂ν = 0 := by
            have := hbase a (a + (n + 1 : ℕ))
            rwa [hν, Measure.restrict_restrict measurableSet_Ioc, Set.inter_self] at this
          have hsplit := integral_add_compl hs hint
          rw [hind, zero_add] at hsplit
          rw [hsplit, htotal]
      | iUnion f hdis hmeas hind =>
          rw [integral_iUnion hmeas hdis hint.integrableOn]
          simp only [hind, tsum_zero]
    exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite
      (fun s hs _ ↦ hint.integrableOn) (fun s hs _ ↦ hall s hs)
  have hwin' := ae_all_iff.mpr hwin
  filter_upwards [hwin'] with t hwt hat
  obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
  refine hwt n ⟨hat, ?_⟩
  have : t - a ≤ (n + 1 : ℕ) := hn.trans (by exact_mod_cast Nat.le_succ n)
  calc t = a + (t - a) := by rw [add_tsub_cancel_of_le hat.le]
    _ ≤ a + (n + 1 : ℕ) := by gcongr

omit [CompleteSpace W] [BorelSpace W] in
/-- Pairing a product-`L²` process with the elementary tensor `1_{(c,d]} ⊗ g` computes the
window integral of the sectionwise pairings. -/
theorem inner_tensor_iocIndicator (D : TimeProcessL2 P) (c d : ℝ≥0) (g : Lp ℝ 2 P) :
    ⟪D, tensor (iocIndicator c d) g⟫_ℝ =
      ∫ t in Set.Ioc c d, (∫ ω, D (t, ω) * g ω ∂P) ∂nonnegativeLebesgueMeasure := by
  set T : TimeProcessL2 P := tensor (iocIndicator c d) g with hT
  have hint : Integrable (fun p : ℝ≥0 × W ↦ D p * T p) (nonnegativeLebesgueMeasure.prod P) := by
    have := L2.integrable_inner (𝕜 := ℝ) D T
    simpa [RCLike.inner_apply, conj_trivial, mul_comm] using this
  have hTfn : (T : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun p ↦ (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2 := by
    have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
        (iocIndicator c d : ℝ≥0 → ℝ) p.1 = (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 :=
      Measure.quasiMeasurePreserving_fst.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
          (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top c d) (c := (1 : ℝ)))
    filter_upwards [coeFn_tensor (iocIndicator c d) g, hg] with p hp hg'
    rw [hp, hg']
  have hint' : Integrable (fun p : ℝ≥0 × W ↦
      D p * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2))
      (nonnegativeLebesgueMeasure.prod P) :=
    hint.congr (hTfn.mono fun p hp ↦ by dsimp only; rw [hp])
  calc ⟪D, T⟫_ℝ
      = ∫ p, D p * T p ∂(nonnegativeLebesgueMeasure.prod P) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards with p
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]
    _ = ∫ p : ℝ≥0 × W, D p * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) p.1 * g p.2)
          ∂(nonnegativeLebesgueMeasure.prod P) :=
        integral_congr_ae (hTfn.mono fun p hp ↦ by dsimp only; rw [hp])
    _ = ∫ t, ∫ ω, D (t, ω) * ((Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) t * g ω) ∂P
          ∂nonnegativeLebesgueMeasure := integral_prod _ hint'
    _ = ∫ t, (Set.Ioc c d).indicator (1 : ℝ≥0 → ℝ) t * ∫ ω, D (t, ω) * g ω ∂P
          ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        rw [← integral_const_mul]
        congr 1
        funext ω
        ring
    _ = ∫ t, (Set.Ioc c d).indicator (fun t ↦ ∫ ω, D (t, ω) * g ω ∂P) t
          ∂nonnegativeLebesgueMeasure := by
        apply integral_congr_ae
        filter_upwards with t
        by_cases ht : t ∈ Set.Ioc c d <;> simp [ht]
    _ = ∫ t in Set.Ioc c d, (∫ ω, D (t, ω) * g ω ∂P) ∂nonnegativeLebesgueMeasure :=
        integral_indicator measurableSet_Ioc

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- The predictable projection is orthogonal: the correction `Π U - U` is orthogonal to every
predictable process. -/
theorem inner_predictableProjection_sub (U : TimeProcessL2 P) (V : PredictableProcessL2 𝓕 P) :
    ⟪(predictableProjection 𝓕 U : TimeProcessL2 P) - U, (V : TimeProcessL2 P)⟫_ℝ = 0 := by
  rw [inner_sub_left]
  have h := inner_condExpL2_eq_inner_fun (𝕜 := ℝ) (predictable_le_prod 𝓕) U
    (V : TimeProcessL2 P) (lpMeas.aestronglyMeasurable V)
  simp only [predictableProjection]
  rw [h, sub_self]

omit [CompleteSpace W] [BorelSpace W] in
/-- **Uniform conditional moments against a fixed coefficient**: for `Z ∈ L²` measurable for
`𝓕 a`, the sectionwise pairings of the correction `Π U - U` with `Z` vanish for almost every
`t > a`. -/
theorem pairing_timeSection_predictableProjection_ae (U : TimeProcessL2 P) (a : ℝ≥0)
    (Z : lpMeas ℝ ℝ (𝓕 a) 2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      ∫ ω, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω))
        * (Z : Lp ℝ 2 P) ω ∂P = 0 := by
  set D : TimeProcessL2 P := (predictableProjection 𝓕 U : TimeProcessL2 P) - U with hDdef
  have hZmeas : AEStronglyMeasurable[𝓕 a] ((Z : Lp ℝ 2 P) : W → ℝ) P :=
    lpMeas.aestronglyMeasurable Z
  -- interval integrals of the pairing function vanish
  have hzero : ∀ c d : ℝ≥0, a ≤ c →
      ∫ t in Set.Ioc c d, (∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (Z : Lp ℝ 2 P) ω ∂P)
        ∂nonnegativeLebesgueMeasure = 0 := by
    intro c d hac
    rw [← inner_tensor_iocIndicator D c d (Z : Lp ℝ 2 P)]
    have hZc : (Z : Lp ℝ 2 P) ∈ lpMeas ℝ ℝ (𝓕 c) 2 P :=
      mem_lpMeas_iff_aestronglyMeasurable.mpr
        ⟨hZmeas.mk _, hZmeas.stronglyMeasurable_mk.mono (𝓕.mono hac), hZmeas.ae_eq_mk⟩
    have hcoe := elementaryPredictable_coeLp 𝓕 c d ⟨(Z : Lp ℝ 2 P), hZc⟩
    rw [← hcoe]
    exact inner_predictableProjection_sub 𝓕 U _
  -- local integrability of the pairing function
  have hloc : ∀ b : ℝ≥0,
      IntegrableOn (fun t ↦ ∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (Z : Lp ℝ 2 P) ω ∂P)
        (Set.Ioc a b) nonnegativeLebesgueMeasure := by
    intro b
    set T : TimeProcessL2 P := tensor (iocIndicator a b) (Z : Lp ℝ 2 P) with hT
    have hint : Integrable (fun p : ℝ≥0 × W ↦ (D : ℝ≥0 × W → ℝ) p * (T : ℝ≥0 × W → ℝ) p)
        (nonnegativeLebesgueMeasure.prod P) := by
      have := L2.integrable_inner (𝕜 := ℝ) D T
      simpa [RCLike.inner_apply, conj_trivial, mul_comm] using this
    have hH : Integrable (fun t ↦ ∫ ω, (D : ℝ≥0 × W → ℝ) (t, ω) * (T : ℝ≥0 × W → ℝ) (t, ω) ∂P)
        nonnegativeLebesgueMeasure := hint.integral_prod_left
    have hTfn : (T : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P]
        fun p ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 * (Z : Lp ℝ 2 P) p.2 := by
      have hg : ∀ᵐ p : ℝ≥0 × W ∂nonnegativeLebesgueMeasure.prod P,
          (iocIndicator a b : ℝ≥0 → ℝ) p.1 = (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) p.1 :=
        Measure.quasiMeasurePreserving_fst.ae_eq_comp
          (indicatorConstLp_coeFn (p := 2) (hs := measurableSet_Ioc)
            (hμs := nonnegativeLebesgueMeasure_Ioc_ne_top a b) (c := (1 : ℝ)))
      filter_upwards [coeFn_tensor (iocIndicator a b) (Z : Lp ℝ 2 P), hg] with p hp hg'
      rw [hp, hg']
    have hsec := Measure.ae_ae_of_ae_prod hTfn
    refine (hH.restrict (s := Set.Ioc a b)).congr ?_
    have hsec' : ∀ᵐ t ∂nonnegativeLebesgueMeasure.restrict (Set.Ioc a b),
        (fun ω ↦ (T : ℝ≥0 × W → ℝ) (t, ω)) =ᵐ[P]
          fun ω ↦ (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) t * (Z : Lp ℝ 2 P) ω :=
      ae_restrict_of_ae hsec
    filter_upwards [hsec', ae_restrict_mem measurableSet_Ioc] with t hst htmem
    have hind : (Set.Ioc a b).indicator (1 : ℝ≥0 → ℝ) t = 1 := by
      simp only [htmem, Set.indicator_of_mem, Pi.one_apply]
    refine integral_congr_ae (hst.mono fun ω hω ↦ ?_)
    dsimp only at hω ⊢
    rw [hω, hind, one_mul]
  have h0 := ae_eq_zero_on_Ioi_of_forall_setIntegral_Ioc_eq_zero hloc hzero
  have hDsec := Measure.ae_ae_of_ae_prod
    (Lp.coeFn_sub (predictableProjection 𝓕 U : TimeProcessL2 P) U)
  filter_upwards [h0, hDsec] with t h0t hst hat
  rw [← h0t hat]
  refine integral_congr_ae (hst.mono fun ω hω ↦ ?_)
  dsimp only at hω ⊢
  rw [hω]
  simp only [mul_comm, Pi.sub_apply]

omit [CompleteSpace W] [BorelSpace W] in
/-- **Uniform conditional-expectation identification of the sections.**  When the ambient `L²`
space is second countable (for instance over a Wiener-generated Gaussian space,
`secondCountableTopology_randomL2_of_isWienerGenerated`), for every `a`, for almost every
`t > a` — with a null set *independent of any test event* — the conditional expectations given
`𝓕 a` of the sections of `Π U` and of `U` coincide:

  `E[(Π U) (t, ·) | 𝓕 a] =ᵐ[P] E[U (t, ·) | 𝓕 a]`. -/
theorem condExp_timeSection_predictableProjection_ae
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) (a : ℝ≥0) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 a]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 a] := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (RandomL2 P)
  have hall : ∀ᵐ t ∂nonnegativeLebesgueMeasure, ∀ g ∈ S, a < t →
      ∫ ω, ((predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω))
        * ((condExpL2 ℝ ℝ (𝓕.le a) g : Lp ℝ 2 P)) ω ∂P = 0 :=
    (ae_ball_iff hSc).mpr fun g _ ↦
      pairing_timeSection_predictableProjection_ae 𝓕 U a (condExpL2 ℝ ℝ (𝓕.le a) g)
  filter_upwards [hall, memLp_timeSection_ae (predictableProjection 𝓕 U : TimeProcessL2 P),
    memLp_timeSection_ae U] with t hallt hQt hUt hat
  -- the `L²` classes of the sections
  set q := hQt.toLp _ with hq
  set u := hUt.toLp _ with hu
  -- the conditional expectation of the difference vanishes, by density
  have hker : condExpL2 ℝ ℝ (𝓕.le a) (q - u) = 0 := by
    have hz : ∀ g ∈ S, ⟪((condExpL2 ℝ ℝ (𝓕.le a) (q - u) : lpMeas ℝ ℝ (𝓕 a) 2 P) :
        Lp ℝ 2 P), g⟫_ℝ = 0 := by
      intro g hg
      rw [inner_condExpL2_left_eq_right]
      have hqu : ((q - u : Lp ℝ 2 P) : W → ℝ) =ᵐ[P]
          fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) - U (t, ω) := by
        filter_upwards [Lp.coeFn_sub q u, hQt.coeFn_toLp, hUt.coeFn_toLp] with ω h1 h2 h3
        rw [h1, Pi.sub_apply, h2, h3]
      rw [L2.inner_def]
      have := hallt g hg hat
      rw [← this]
      apply integral_congr_ae
      filter_upwards [hqu] with ω hω
      rw [RCLike.inner_apply, conj_trivial, hω]
      exact mul_comm _ _
    have hzero : ((condExpL2 ℝ ℝ (𝓕.le a) (q - u) : lpMeas ℝ ℝ (𝓕 a) 2 P) : Lp ℝ 2 P) = 0 :=
      hSd.eq_zero_of_inner_left ℝ hz
    exact Subtype.ext hzero
  -- translate into function-valued conditional expectations
  have hQ := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le a) hQt
  have hU := MemLp.condExpL2_ae_eq_condExp (𝕜 := ℝ) (𝓕.le a) hUt
  have hsub : condExpL2 ℝ ℝ (𝓕.le a) q = condExpL2 ℝ ℝ (𝓕.le a) u := by
    have := map_sub (condExpL2 ℝ ℝ (𝓕.le a) :
      Lp ℝ 2 P →L[ℝ] lpMeas ℝ ℝ (𝓕 a) 2 P) q u
    rw [hker] at this
    have := sub_eq_zero.mp this.symm
    exact this
  calc P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 a]
      =ᵐ[P] ((condExpL2 ℝ ℝ (𝓕.le a) q : lpMeas ℝ ℝ (𝓕 a) 2 P) : W → ℝ) := hQ.symm
    _ = ((condExpL2 ℝ ℝ (𝓕.le a) u : lpMeas ℝ ℝ (𝓕 a) 2 P) : W → ℝ) := by rw [hsub]
    _ =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 a] := hU

/-- The strict-past σ-algebra `𝓕_{t⁻} = ⨆_{s < t} 𝓕 s`. -/
@[instance_reducible]
def filtrationPred (t : ℝ≥0) : MeasurableSpace W :=
  ⨆ (s : ℝ≥0) (_ : s < t), 𝓕 s

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
theorem filtrationPred_le (t : ℝ≥0) : filtrationPred 𝓕 t ≤ ‹MeasurableSpace W› :=
  iSup₂_le fun s _ ↦ 𝓕.le s

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
theorem le_filtrationPred {s t : ℝ≥0} (hst : s < t) : 𝓕 s ≤ filtrationPred 𝓕 t :=
  le_iSup₂ (f := fun (s : ℝ≥0) (_ : s < t) ↦ 𝓕 s) s hst

omit [CompleteSpace W] [BorelSpace W] in
/-- **Sections of the predictable projection are conditional expectations given the strict
past**: for almost every `t > 0`, with a null set independent of everything else,

  `E[(Π U) (t, ·) | 𝓕_{t⁻}] =ᵐ[P] E[U (t, ·) | 𝓕_{t⁻}]`,

where `𝓕_{t⁻} = ⨆_{s < t} 𝓕 s`.  Since a suitable representative of `Π U` has
`𝓕_{t⁻}`-measurable sections, this is the textbook identification of the predictable
projection; only left-continuity `𝓕_{t⁻} = 𝓕 t` of the filtration separates it from
`E[U (t, ·) | 𝓕 t]`. -/
theorem condExp_timeSection_predictableProjection_pred_ae
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | filtrationPred 𝓕 t]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hall : ∀ᵐ t ∂nonnegativeLebesgueMeasure, ∀ q ∈ S, q < t →
      P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) | 𝓕 q]
        =ᵐ[P] P[(fun ω ↦ U (t, ω)) | 𝓕 q] :=
    (ae_ball_iff hSc).mpr fun q _ ↦ condExp_timeSection_predictableProjection_ae 𝓕 U q
  filter_upwards [hall] with t hallt hat
  set X : W → ℝ := fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω) with hX
  set Y : W → ℝ := fun ω ↦ U (t, ω) with hY
  -- every strictly earlier level
  have hA : ∀ b : ℝ≥0, b < t → P[X | 𝓕 b] =ᵐ[P] P[Y | 𝓕 b] := by
    intro b hbt
    obtain ⟨q, hqS, hbq, hqt⟩ := hSd.exists_between hbt
    calc P[X | 𝓕 b]
        =ᵐ[P] P[P[X | 𝓕 q] | 𝓕 b] := (condExp_condExp_of_le (𝓕.mono hbq.le) (𝓕.le q)).symm
      _ =ᵐ[P] P[P[Y | 𝓕 q] | 𝓕 b] := condExp_congr_ae (hallt q hqS hqt)
      _ =ᵐ[P] P[Y | 𝓕 b] := condExp_condExp_of_le (𝓕.mono hbq.le) (𝓕.le q)
  -- an increasing exhaustion of the strict past
  set u : ℕ → ℝ≥0 := fun n ↦ t - t / (n + 2) with hu
  have hu_lt : ∀ n, u n < t := fun n ↦ tsub_lt_self hat (by positivity)
  have hu_mono : Monotone u := by
    intro m n hmn
    refine tsub_le_tsub_left ?_ t
    gcongr
  set ℱ : Filtration ℕ ‹MeasurableSpace W› :=
    ⟨fun n ↦ 𝓕 (u n), fun m n hmn ↦ 𝓕.mono (hu_mono hmn), fun n ↦ 𝓕.le _⟩ with hℱ
  have hsup : (⨆ n, ℱ n) = filtrationPred 𝓕 t := by
    refine le_antisymm (iSup_le fun n ↦ le_filtrationPred 𝓕 (hu_lt n)) (iSup₂_le fun s hst ↦ ?_)
    have hts : t - s ≠ 0 := (tsub_pos_of_lt hst).ne'
    obtain ⟨n, hn⟩ := exists_nat_ge (t / (t - s))
    have hle : t / ((n : ℝ≥0) + 2) ≤ t - s := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (pos_of_ne_zero hts)] at hn
      calc t ≤ (n : ℝ≥0) * (t - s) := hn
        _ ≤ ((n : ℝ≥0) + 2) * (t - s) := by gcongr; exact le_self_add
        _ = (t - s) * ((n : ℝ≥0) + 2) := mul_comm _ _
    have hsn : s ≤ u n := by
      rw [hu]
      have := tsub_le_tsub_left hle t
      refine le_trans ?_ this
      rw [tsub_tsub_cancel_of_le hst.le]
    exact le_trans (𝓕.mono hsn) (le_iSup (fun n ↦ ℱ n) n)
  -- Lévy's upward theorem for both conditional expectations
  have hXg : Integrable (P[X | filtrationPred 𝓕 t]) P := integrable_condExp
  have hYg : Integrable (P[Y | filtrationPred 𝓕 t]) P := integrable_condExp
  have hXm : StronglyMeasurable[⨆ n, ℱ n] (P[X | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hYm : StronglyMeasurable[⨆ n, ℱ n] (P[Y | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hXlim := hXg.tendsto_ae_condExp hXm
  have hYlim := hYg.tendsto_ae_condExp hYm
  -- the approximating conditional expectations agree
  have hlevels : ∀ n : ℕ, P[P[X | filtrationPred 𝓕 t] | ℱ n]
      =ᵐ[P] P[P[Y | filtrationPred 𝓕 t] | ℱ n] := by
    intro n
    have h1 : P[P[X | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] P[X | ℱ n] :=
      condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n) (filtrationPred_le 𝓕 t)
    have h2 : P[P[Y | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] P[Y | ℱ n] :=
      condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n) (filtrationPred_le 𝓕 t)
    exact h1.trans ((hA (u n) (hu_lt n)).trans h2.symm)
  have hlevels' := ae_all_iff.mpr hlevels
  filter_upwards [hXlim, hYlim, hlevels'] with ω hXω hYω hlω
  refine tendsto_nhds_unique ?_ hYω
  refine hXω.congr fun n ↦ ?_
  exact hlω n

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- For `t > 0`, the map `ω ↦ (t, ω)` is measurable from the strict past `𝓕_{t⁻}` to the
predictable σ-algebra. -/
theorem measurable_section_filtrationPred {t : ℝ≥0} (ht : 0 < t) :
    @Measurable W (ℝ≥0 × W) (filtrationPred 𝓕 t) 𝓕.predictable (fun ω ↦ (t, ω)) := by
  rw [measurable_iff_comap_le, MeasurableSpace.comap_le_iff_le_map]
  refine measurableSpace_le_predictable_of_measurableSet ?_ ?_
  · intro A hA
    rw [MeasurableSpace.map_def]
    rcases eq_or_ne t 0 with ht0 | ht0
    · exact absurd ht0 ht.ne'
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' ({⊥} ×ˢ A) = ∅ := by
        ext ω
        simp only [bot_eq_zero', Set.mem_singleton_iff, ht0, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (filtrationPred 𝓕 t)
  · intro i A hA
    rw [MeasurableSpace.map_def]
    rcases lt_or_ge i t with hit | hit
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = A := by
        ext ω
        simp only [Set.mem_Ioi, hit, Set.mk_preimage_prod_right]
      rw [this]
      exact le_filtrationPred 𝓕 hit A hA
    · have : (fun ω : W ↦ ((t, ω) : ℝ≥0 × W)) ⁻¹' (Set.Ioi i ×ˢ A) = ∅ := by
        ext ω
        simp only [Set.mem_Ioi, not_lt.mpr hit, not_false_eq_true, Set.mk_preimage_prod_right_eq_empty,
    Set.mem_empty_iff_false]
      rw [this]
      exact @MeasurableSet.empty _ (filtrationPred 𝓕 t)

omit [CompleteSpace W] [BorelSpace W] in
/-- **Textbook identification of the predictable projection.**  Any predictable strongly
measurable representative `G` of `predictableProjection 𝓕 U` satisfies, for almost every
`t > 0`,

  `G (t, ·) =ᵐ[P] E[U (t, ·) | 𝓕_{t⁻}]`,

a literal pointwise conditional-expectation formula for the sections. -/
theorem timeSection_predictableProjection_ae_eq_condExp
    [SecondCountableTopology (RandomL2 P)] (U : TimeProcessL2 P)
    {G : ℝ≥0 × W → ℝ} (hG : StronglyMeasurable[𝓕.predictable] G)
    (hGae : (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ)
      =ᵐ[nonnegativeLebesgueMeasure.prod P] G) :
    ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
      (fun ω ↦ G (t, ω)) =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := by
  have hsec := Measure.ae_ae_of_ae_prod hGae
  filter_upwards [condExp_timeSection_predictableProjection_pred_ae 𝓕 U, hsec,
    memLp_timeSection_ae (predictableProjection 𝓕 U : TimeProcessL2 P)] with t hct hst hQt hat
  have hGt : StronglyMeasurable[filtrationPred 𝓕 t] fun ω ↦ G (t, ω) :=
    hG.comp_measurable (measurable_section_filtrationPred 𝓕 hat)
  have hGint : Integrable (fun ω ↦ G (t, ω)) P :=
    (hQt.integrable one_le_two).congr hst
  calc (fun ω ↦ G (t, ω))
      = P[(fun ω ↦ G (t, ω)) | filtrationPred 𝓕 t] :=
        (condExp_of_stronglyMeasurable (filtrationPred_le 𝓕 t) hGt hGint).symm
    _ =ᵐ[P] P[(fun ω ↦ (predictableProjection 𝓕 U : ℝ≥0 × W → ℝ) (t, ω)) |
          filtrationPred 𝓕 t] := condExp_congr_ae (hst.mono fun ω hω ↦ hω.symm)
    _ =ᵐ[P] P[(fun ω ↦ U (t, ω)) | filtrationPred 𝓕 t] := hct hat

end Sections

section ClarkOconeIntegrand

variable {B : ℝ≥0 → W → ℝ} {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›}

/-- **The Clark--Ocone integrand, pointwise form.**  For `F ∈ 𝔻₁,₂`, the Clark--Ocone integrand
`predictableDerivative C F` has a representative `G` that is predictable strongly measurable,
whose section at every time `t` is `𝓕 t`-strongly measurable, and whose section integrals agree
with those of the fixed-time conditional expectation `E[(Dₜ F) | 𝓕 t]` of the time derivative
against every event `A ∈ 𝓕 a` for almost every `t > a`.  This is the textbook
`E[Dₜ F | 𝓕ₜ]` up to the uniformity of the exceptional times over test events. -/
theorem exists_representative_predictableDerivative (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      (∀ t, StronglyMeasurable[𝓕 t] fun ω ↦ G (t, ω)) ∧
      ∀ (a : ℝ≥0) (A : Set W), MeasurableSet[𝓕 a] A →
        ∀ᵐ t ∂nonnegativeLebesgueMeasure, a < t →
          ∫ ω in A, G (t, ω) ∂P
            = ∫ ω in A,
                (P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t]) ω ∂P :=
  exists_representative_predictableProjection 𝓕 (C.timeDerivative (mderivD12 P F))

/-- **The Clark--Ocone integrand is `E[Dₜ F | 𝓕_{t⁻}]`.**  Over any Clark--Ocone family the
integrand `predictableDerivative C F` has a predictable strongly measurable representative `G`
with, for almost every `t > 0`,

  `G (t, ·) =ᵐ[P] E[(Dₜ F) (t, ·) | 𝓕_{t⁻}]`,

the literal pointwise conditional expectation of the time derivative given the strict past.
Second countability of `L²(P)` holds automatically because the family is Wiener generated. -/
theorem exists_representative_predictableDerivative_condExp
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | filtrationPred 𝓕 t] := by
  have _i : SecondCountableTopology (RandomL2 P) :=
    secondCountableTopology_randomL2_of_isWienerGenerated C.isPreBrownian C.generated
  have hmeas : AEStronglyMeasurable[𝓕.predictable]
      ((predictableDerivative C F : TimeProcessL2 P) : (ℝ≥0 × W) → ℝ)
      (nonnegativeLebesgueMeasure.prod P) := lpMeas.aestronglyMeasurable _
  exact ⟨hmeas.mk _, hmeas.stronglyMeasurable_mk, hmeas.ae_eq_mk,
    timeSection_predictableProjection_ae_eq_condExp 𝓕 (C.timeDerivative (mderivD12 P F))
      hmeas.stronglyMeasurable_mk hmeas.ae_eq_mk⟩

/-- Tower form: the representative is the strict-past conditional expectation *of* the textbook
integrand `E[Dₜ F | 𝓕 t]`. -/
theorem exists_representative_predictableDerivative_condExp_condExp
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] |
            filtrationPred 𝓕 t] := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_representative_predictableDerivative_condExp C F
  refine ⟨G, hG1, hG2, ?_⟩
  filter_upwards [hG3] with t ht hat
  refine (ht hat).trans ?_
  refine (condExp_condExp_of_le ?_ (𝓕.le t)).symm
  exact iSup₂_le fun s hst ↦ 𝓕.mono hst.le

/-- **Textbook Clark--Ocone integrand under left-continuity.**  If the filtration is
left-continuous at positive times (`𝓕_{t⁻} = 𝓕 t`), the Clark--Ocone integrand has a
predictable representative `G` with, for almost every `t > 0`,

  `G (t, ·) =ᵐ[P] E[(Dₜ F) (t, ·) | 𝓕 t]`,

which is the literal textbook `E[Dₜ F | 𝓕ₜ]`.  Left-continuity of the natural Brownian
filtration is the single remaining input. -/
theorem exists_representative_predictableDerivative_condExp_of_leftContinuous
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P)
    (hlc : ∀ t : ℝ≥0, 0 < t → filtrationPred 𝓕 t = 𝓕 t) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_representative_predictableDerivative_condExp C F
  refine ⟨G, hG1, hG2, ?_⟩
  filter_upwards [hG3] with t ht hat
  rw [← hlc t hat]
  exact ht hat

/-- Variant of the textbook identification assuming left-continuity only at the level of
conditional expectations (`E[· | 𝓕_{t⁻}] =ᵐ E[· | 𝓕 t]` for integrable integrands), which is
the form provable modulo `P`-null sets. -/
theorem exists_representative_predictableDerivative_condExp_of_condExp_leftContinuous
    (C : ClarkOconeFamily B P 𝓕) (F : D12 P)
    (hlc : ∀ t : ℝ≥0, 0 < t → ∀ X : W → ℝ, Integrable X P →
      P[X | filtrationPred 𝓕 t] =ᵐ[P] P[X | 𝓕 t]) :
    ∃ G : ℝ≥0 × W → ℝ,
      StronglyMeasurable[𝓕.predictable] G ∧
      (predictableDerivative C F : ℝ≥0 × W → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] G ∧
      ∀ᵐ t ∂nonnegativeLebesgueMeasure, 0 < t →
        (fun ω ↦ G (t, ω)) =ᵐ[P]
          P[(fun ω ↦ (C.timeDerivative (mderivD12 P F)) (t, ω)) | 𝓕 t] := by
  obtain ⟨G, hG1, hG2, hG3⟩ := exists_representative_predictableDerivative_condExp C F
  refine ⟨G, hG1, hG2, ?_⟩
  filter_upwards [hG3, memLp_timeSection_ae (C.timeDerivative (mderivD12 P F))] with t ht hint hat
  exact (ht hat).trans (hlc t hat _ (hint.integrable one_le_two))

section NaturalFiltration

variable {B : ℝ≥0 → W → ℝ}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- For the natural filtration, the strict past is the supremum of the coordinate σ-algebras at
strictly earlier times. -/
theorem filtrationPred_natural (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) :
    filtrationPred (Filtration.natural B hm) t
      = ⨆ (s : ℝ≥0) (_ : s < t), MeasurableSpace.comap (B s) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun s hst ↦ iSup₂_le fun j hjs ↦ ?_
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j < t) ↦
      MeasurableSpace.comap (B j) inferInstance) j (lt_of_le_of_lt hjs hst)
  · refine iSup₂_le fun s hst ↦ le_trans ?_
      (le_filtrationPred (Filtration.natural B hm) hst)
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ s) ↦
      MeasurableSpace.comap (B j) inferInstance) s le_rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- The natural filtration at `t` splits as the strict past joined with the time-`t`
coordinate. -/
theorem natural_eq_filtrationPred_sup (hm : ∀ s, StronglyMeasurable (B s)) (t : ℝ≥0) :
    Filtration.natural B hm t
      = filtrationPred (Filtration.natural B hm) t
        ⊔ MeasurableSpace.comap (B t) inferInstance := by
  apply le_antisymm
  · refine iSup₂_le fun j hjt ↦ ?_
    rcases lt_or_eq_of_le hjt with hj | hj
    · refine le_sup_of_le_left ?_
      rw [filtrationPred_natural hm]
      exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j < t) ↦
        MeasurableSpace.comap (B j) inferInstance) j hj
    · subst hj
      exact le_sup_right
  · refine sup_le (iSup₂_le fun s hst ↦ (Filtration.natural B hm).mono hst.le) ?_
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ t) ↦
      MeasurableSpace.comap (B j) inferInstance) t le_rfl

omit [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] [BorelSpace W]
  [SecondCountableTopology W] [IsGaussian P] in
/-- The Brownian classes converge in `L²` along the strict-past exhaustion `t - t/(n+2)`:
`‖B_t - B_{u n}‖² = t/(n+2) → 0`.  First brick of the left-continuity capstone. -/
theorem tendsto_brownianLp_exhaustion (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Filter.Tendsto (fun n : ℕ ↦ brownianLp hB (t - t / (n + 2))) Filter.atTop
      (nhds (brownianLp hB t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ n : ℕ, ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖ ^ 2
      = ((t : ℝ) - (t - t / (n + 2) : ℝ≥0)) := by
    intro n
    have hle : (t - t / (n + 2) : ℝ≥0) ≤ t := tsub_le_self
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
      inner_brownianLp, inner_brownianLp, inner_brownianLp, inner_brownianLp, min_self, min_self,
      min_eq_left (by exact_mod_cast hle), min_eq_right (by exact_mod_cast hle)]
    ring
  have hto : Filter.Tendsto
      (fun n : ℕ ↦ ((t : ℝ) - (t - t / (n + 2) : ℝ≥0))) Filter.atTop (nhds 0) := by
    have hval : ∀ n : ℕ, ((t : ℝ) - (t - t / (n + 2) : ℝ≥0)) = (t : ℝ) / (n + 2) := by
      intro n
      have hdiv : (t / (n + 2) : ℝ≥0) ≤ t := by
        apply div_le_self zero_le
        exact_mod_cast Nat.le_add_left 1 (n + 1)
      rw [NNReal.coe_sub hdiv, NNReal.coe_div]
      push_cast
      ring
    simp only [hval]
    have := Filter.Tendsto.div_atTop (f := fun _ : ℕ ↦ (t : ℝ))
      (g := fun n : ℕ ↦ ((n : ℝ) + 2)) tendsto_const_nhds
      (Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    exact this
  have hnorm : Filter.Tendsto
      (fun n : ℕ ↦ ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖ ^ 2)
      Filter.atTop (nhds 0) := by
    simp only [hsq]
    exact hto
  have h0 : Filter.Tendsto
      (fun n : ℕ ↦ ‖brownianLp hB (t - t / (n + 2)) - brownianLp hB t‖)
      Filter.atTop (nhds 0) := by
    have := hnorm.sqrt
    simp only [Real.sqrt_zero] at this
    refine this.congr fun n ↦ ?_
    rw [Real.sqrt_sq (norm_nonneg _)]
  exact h0

/-- **The pre-Brownian martingale property**: `E[B b | 𝓕 a] = B a` for `a ≤ b`, over any
Clark--Ocone family. -/
theorem _root_.Malliavin.ClarkOconeFamily.condExp_brownian
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {a b : ℝ≥0} (hab : a ≤ b) :
    P[B b | 𝓕 a] =ᵐ[P] B a := by
  have hBb : MemLp (B b) 2 P :=
    (C.isPreBrownian.isGaussianProcess.hasGaussianLaw_eval b).memLp_two
  have hBa : MemLp (B a) 2 P :=
    (C.isPreBrownian.isGaussianProcess.hasGaussianLaw_eval a).memLp_two
  -- the increment is independent of `𝓕 a`
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
  -- conditional expectation of the increment vanishes
  have hmeas_incr : Measurable fun w ↦ B b w - B a w :=
    (C.stronglyMeasurable b).measurable.sub (C.stronglyMeasurable a).measurable
  have hincr : P[(fun w ↦ B b w - B a w) | 𝓕 a] =ᵐ[P] fun _ ↦ 0 := by
    have h := condExp_indep_eq (μ := P)
      (m₁ := MeasurableSpace.comap (fun w ↦ B b w - B a w) inferInstance)
      (m₂ := 𝓕 a) hmeas_incr.comap_le (𝓕.le a)
      (Measurable.stronglyMeasurable (measurable_iff_comap_le.mpr le_rfl)) hind
    refine h.trans ?_
    have hzero : ∫ w, (B b w - B a w) ∂P = 0 := by
      rw [integral_sub (hBb.integrable one_le_two) (hBa.integrable one_le_two),
        C.isPreBrownian.integral_eval b, C.isPreBrownian.integral_eval a, sub_zero]
    filter_upwards with w
    rw [hzero]
  -- `B a` is `𝓕 a`-measurable
  have hcomap_le : MeasurableSpace.comap (B a) inferInstance ≤ 𝓕 a := by
    rw [C.naturalFiltration]
    exact le_iSup₂ (f := fun (j : ℝ≥0) (_ : j ≤ a) ↦
      MeasurableSpace.comap (B j) inferInstance) a le_rfl
  have hBa_meas : StronglyMeasurable[𝓕 a] (B a) :=
    (Measurable.mono (measurable_iff_comap_le.mpr le_rfl) hcomap_le le_rfl).stronglyMeasurable
  -- assemble
  have hsplit : B b = fun w ↦ (B b w - B a w) + B a w := by
    funext w
    ring
  calc P[B b | 𝓕 a]
      = P[(fun w ↦ (B b w - B a w) + B a w) | 𝓕 a] := by rw [← hsplit]
    _ =ᵐ[P] P[(fun w ↦ B b w - B a w) | 𝓕 a] + P[B a | 𝓕 a] :=
        condExp_add ((hBb.integrable one_le_two).sub (hBa.integrable one_le_two))
          (hBa.integrable one_le_two) _
    _ =ᵐ[P] (fun _ ↦ (0 : ℝ)) + B a := by
        refine Filter.EventuallyEq.add hincr ?_
        exact condExp_of_stronglyMeasurable (𝓕.le a) hBa_meas (hBa.integrable one_le_two)
          |>.symm ▸ Filter.EventuallyEq.rfl
    _ =ᵐ[P] B a := by
        filter_upwards with w
        simp only [Pi.add_apply, zero_add]

/-- **The Brownian coordinate is measurable with respect to its strict past, up to null sets**:
`E[B t | 𝓕_{t⁻}] = B t` almost surely, for `t > 0`.  Third brick of the left-continuity
capstone: with Lévy's upward theorem the martingale values `B (t - t/(n+2))` converge to
`E[B t | 𝓕_{t⁻}]`, while in `L²` they converge to `B t`. -/
theorem _root_.Malliavin.ClarkOconeFamily.condExp_brownian_filtrationPred
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    P[B t | filtrationPred 𝓕 t] =ᵐ[P] B t := by
  -- the exhaustion of the strict past
  set u : ℕ → ℝ≥0 := fun n ↦ t - t / (n + 2) with hu
  have hu_lt : ∀ n, u n < t := fun n ↦ tsub_lt_self hat (by positivity)
  have hu_mono : Monotone u := by
    intro m n hmn
    refine tsub_le_tsub_left ?_ t
    gcongr
  set ℱ : Filtration ℕ ‹MeasurableSpace W› :=
    ⟨fun n ↦ 𝓕 (u n), fun m n hmn ↦ 𝓕.mono (hu_mono hmn), fun n ↦ 𝓕.le _⟩ with hℱ
  have hsup : (⨆ n, ℱ n) = filtrationPred 𝓕 t := by
    refine le_antisymm (iSup_le fun n ↦ le_filtrationPred 𝓕 (hu_lt n)) (iSup₂_le fun s hst ↦ ?_)
    have hts : t - s ≠ 0 := (tsub_pos_of_lt hst).ne'
    obtain ⟨n, hn⟩ := exists_nat_ge (t / (t - s))
    have hle : t / ((n : ℝ≥0) + 2) ≤ t - s := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (pos_of_ne_zero hts)] at hn
      calc t ≤ (n : ℝ≥0) * (t - s) := hn
        _ ≤ ((n : ℝ≥0) + 2) * (t - s) := by gcongr; exact le_self_add
        _ = (t - s) * ((n : ℝ≥0) + 2) := mul_comm _ _
    have hsn : s ≤ u n := by
      rw [hu]
      have := tsub_le_tsub_left hle t
      refine le_trans ?_ this
      rw [tsub_tsub_cancel_of_le hst.le]
    exact le_trans (𝓕.mono hsn) (le_iSup (fun n ↦ ℱ n) n)
  -- Lévy's upward convergence of the conditional expectations
  have hgm : StronglyMeasurable[⨆ n, ℱ n] (P[B t | filtrationPred 𝓕 t]) := by
    rw [hsup]
    exact stronglyMeasurable_condExp
  have hlev := (integrable_condExp (m := filtrationPred 𝓕 t)
    (f := B t) (μ := P)).tendsto_ae_condExp hgm
  have hlevn : ∀ n : ℕ, P[P[B t | filtrationPred 𝓕 t] | ℱ n] =ᵐ[P] B (u n) := by
    intro n
    refine (condExp_condExp_of_le (hsup ▸ le_iSup (fun n ↦ ℱ n) n)
      (filtrationPred_le 𝓕 t)).trans ?_
    exact C.condExp_brownian (hu_lt n).le
  -- `L²` convergence and an almost everywhere convergent subsequence
  have hL2 := tendsto_brownianLp_exhaustion C.isPreBrownian t
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hL2).exists_seq_tendsto_ae
  have hcoe := ae_all_iff.2 fun n : ℕ ↦ coeFn_brownianLp C.isPreBrownian (u n)
  filter_upwards [hlev, hae, hcoe, coeFn_brownianLp C.isPreBrownian t,
    ae_all_iff.2 hlevn] with ω h1 h2 h3 h4 h5
  -- the two limits agree
  have hleft : Filter.Tendsto (fun k ↦ P[P[B t | filtrationPred 𝓕 t] | ℱ (ns k)] ω)
      Filter.atTop (nhds (P[B t | filtrationPred 𝓕 t] ω)) :=
    h1.comp hns.tendsto_atTop
  have hleft' : Filter.Tendsto (fun k ↦ B (u (ns k)) ω) Filter.atTop
      (nhds (P[B t | filtrationPred 𝓕 t] ω)) :=
    hleft.congr fun k ↦ h5 (ns k)
  have hright : Filter.Tendsto (fun k ↦ B (u (ns k)) ω) Filter.atTop (nhds (B t ω)) := by
    rw [← h4]
    exact h2.congr fun k ↦ h3 (ns k)
  exact tendsto_nhds_unique hleft' hright

/-- `B t` has a strict-past strongly measurable version. -/
theorem _root_.Malliavin.ClarkOconeFamily.exists_stronglyMeasurable_filtrationPred_ae_eq
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace W›} (C : ClarkOconeFamily B P 𝓕)
    {t : ℝ≥0} (hat : 0 < t) :
    ∃ Z : W → ℝ, StronglyMeasurable[filtrationPred 𝓕 t] Z ∧ B t =ᵐ[P] Z :=
  ⟨P[B t | filtrationPred 𝓕 t], stronglyMeasurable_condExp,
    (C.condExp_brownian_filtrationPred hat).symm⟩

end NaturalFiltration

end ClarkOconeIntegrand

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
