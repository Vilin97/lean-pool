/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

public import Mathlib.Tactic.FunProp
public import LeanPool.ConcentrationInequalities.BennettBernstein

/-!
# Freedman / Bernstein inequality for martingales (adapted sums of sub-gamma increments)

The variance-based (Freedman) martingale tail: a finite adapted sum of conditionally sub-gamma
increments satisfies `P(∑ Yᵢ ≥ ε) ≤ exp(−ε²/(2(∑Vᵢ + cε)))`. Mathlib has Azuma (sub-Gaussian
martingales) but not the sub-gamma / Freedman version. Built on the sub-gamma MGF and Bernstein tail
of `Contrib.BennettBernstein`, with kernel-level tower additivity of the variance factors.

* `Contrib.Freedman.subgamma_bernstein_tail` — the Freedman/Bernstein upper tail.
* `Contrib.Freedman.Kernel.HasSubgammaMGF` (+ `add_compProd`, `add_of_indep`) — kernel-valued
  sub-gamma MGF with tower additivity.
* `Contrib.Freedman.MeasureSubgammaMGF`, `Contrib.Freedman.HasCondSubgammaMGF` — the measure- and
  conditional-level analogues, and the summation lemma over an adapted sequence.

Sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Contrib.Bennett
open scoped ENNReal NNReal Topology

namespace Contrib.Freedman

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {ν : Measure Ω'} {κ : Kernel Ω' Ω} {X : Ω → ℝ} {V c : ℝ≥0}

/-- Kernel-valued sub-gamma MGF bound.  Integrability is required for every real
parameter (rather than only the effective domain of the estimate), as in Mathlib's
kernel-valued sub-Gaussian definition; this is what makes the tower argument composable. -/
structure Kernel.HasSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (κ : Kernel Ω' Ω) (ν : Measure Ω' := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ∘ₘ ν)
  mgf_le : ∀ᵐ ω' ∂ν, ∀ t, 0 ≤ t → (c : ℝ) * t < 1 →
    mgf X (κ ω') t ≤ exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))

namespace Kernel.HasSubgammaMGF

lemma ae_integrable_exp_mul (h : Kernel.HasSubgammaMGF X V c κ ν) (t : ℝ) :
    ∀ᵐ ω' ∂ν, Integrable (fun y ↦ exp (t * X y)) (κ ω') :=
  Measure.ae_integrable_of_integrable_comp (h.integrable_exp_mul t)

lemma ae_forall_integrable_exp_mul (h : Kernel.HasSubgammaMGF X V c κ ν) :
    ∀ᵐ ω' ∂ν, ∀ t, Integrable (fun ω ↦ exp (t * X ω)) (κ ω') := by
  have hi (n : ℤ) : ∀ᵐ ω' ∂ν, Integrable (fun ω ↦ exp (n * X ω)) (κ ω') :=
    h.ae_integrable_exp_mul _
  rw [← ae_all_iff] at hi
  filter_upwards [hi] with ω' hi t
  exact integrable_exp_mul_of_le_of_le (hi _) (hi _) (Int.floor_le t) (Int.le_ceil t)

lemma memLp_exp_mul (h : Kernel.HasSubgammaMGF X V c κ ν) (t : ℝ) (p : ℝ≥0) :
    MemLp (fun ω ↦ exp (t * X ω)) p (κ ∘ₘ ν) := by
  by_cases hp0 : p = 0
  · simpa [hp0] using (h.integrable_exp_mul t).1
  rw [memLp_iff, eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (mod_cast hp0) (by simp)
    (h.integrable_exp_mul t).1]
  simp only [ENNReal.coe_toReal]
  have hi := (h.integrable_exp_mul (p * t)).2
  rw [hasFiniteIntegral_def] at hi
  convert hi using 3 with ω
  rw [enorm_eq_ofReal (by positivity), enorm_eq_ofReal (by positivity),
    ENNReal.ofReal_rpow_of_nonneg (by positivity), ← exp_mul, mul_comm, ← mul_assoc]
  positivity

@[simp] lemma fun_zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    Kernel.HasSubgammaMGF (fun _ ↦ 0) 0 c κ ν where
  integrable_exp_mul := by simp
  mgf_le := by
    filter_upwards with ω
    intro t ht htc
    simp [mgf, measureReal_le_one]

@[simp] lemma zero_measure : Kernel.HasSubgammaMGF X V c κ (0 : Measure Ω') := ⟨by simp, by simp⟩

@[simp] lemma zero [IsFiniteMeasure ν] [IsZeroOrMarkovKernel κ] :
    Kernel.HasSubgammaMGF 0 0 c κ ν := fun_zero

lemma congr {Y : Ω → ℝ} (h : Kernel.HasSubgammaMGF X V c κ ν) (h' : X =ᵐ[κ ∘ₘ ν] Y) :
    Kernel.HasSubgammaMGF Y V c κ ν where
  integrable_exp_mul t := by
    refine (integrable_congr ?_).mpr (h.integrable_exp_mul t)
    filter_upwards [h'] with ω hω using by rw [hω]
  mgf_le := by
    have h'' := Measure.ae_ae_of_ae_comp h'
    filter_upwards [h.mgf_le, h''] with ω' hm heq t ht htc
    rw [mgf_congr (Filter.EventuallyEq.symm heq)]
    exact hm t ht htc

variable {Ω'' : Type*} {mΩ'' : MeasurableSpace Ω''} {Y : Ω'' → ℝ} {W : ℝ≥0}

lemma prodMkLeft_compProd {η : Kernel Ω Ω''} (h : Kernel.HasSubgammaMGF Y W c η (κ ∘ₘ ν)) :
    Kernel.HasSubgammaMGF Y W c (Kernel.prodMkLeft Ω' η) (ν ⊗ₘ κ) := by
  by_cases hν : SFinite ν
  swap; · simp [hν]
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  constructor
  · simpa using h.integrable_exp_mul
  · have h2 := h.mgf_le
    rw [← Measure.snd_compProd, Measure.snd] at h2
    exact ae_of_ae_map (by fun_prop) h2

variable [SFinite ν]

lemma integrable_exp_add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : Kernel.HasSubgammaMGF X V c κ ν) (hY : Kernel.HasSubgammaMGF Y W c η (ν ⊗ₘ κ)) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * (X ω.1 + Y ω.2))) ((κ ⊗ₖ η) ∘ₘ ν) := by
  by_cases hκ : IsSFiniteKernel κ
  swap; · simp [hκ]
  rcases eq_zero_or_isMarkovKernel η with rfl | hη
  · simp
  simp_rw [mul_add, exp_add]
  refine MemLp.integrable_mul (p := 2) (q := 2) ?_ ?_
  · have hp := hX.memLp_exp_mul t 2
    simp only [ENNReal.coe_ofNat] at hp
    have heq : κ ∘ₘ ν = ((κ ⊗ₖ η) ∘ₘ ν).map Prod.fst := by
      rw [Measure.map_comp _ _ measurable_fst, ← Kernel.fst_eq, Kernel.fst_compProd]
    rwa [heq, memLp_map_measure_iff hp.aestronglyMeasurable measurable_fst.aemeasurable] at hp
  · have hp := hY.memLp_exp_mul t 2
    rwa [ENNReal.coe_ofNat, Measure.comp_compProd_comm, Measure.snd,
      memLp_map_measure_iff hp.aestronglyMeasurable measurable_snd.aemeasurable] at hp

/-- Multiplying two compatible sub-gamma estimates adds their variance factors. -/
private lemma mgf_mul_exp_le_add {a t : ℝ}
    (ha : a ≤ exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))) :
    a * exp ((W : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) ≤
      exp (((V + W : ℝ≥0) : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by
  calc
    a * exp ((W : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) ≤
        exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) *
          exp ((W : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by gcongr
    _ = _ := by rw [← exp_add, NNReal.coe_add]; congr 1; ring

/-- Additivity for an `s`-finite first kernel. -/
private lemma add_compProd_of_isSFiniteKernel {η : Kernel (Ω' × Ω) Ω''}
    [IsZeroOrMarkovKernel η] [IsSFiniteKernel κ]
    (hX : Kernel.HasSubgammaMGF X V c κ ν) (hY : Kernel.HasSubgammaMGF Y W c η (ν ⊗ₘ κ)) :
    Kernel.HasSubgammaMGF (fun p ↦ X p.1 + Y p.2) (V + W) c (κ ⊗ₖ η) ν := by
  let hsum_int := integrable_exp_add_compProd hX hY
  refine ⟨hsum_int, ?_⟩
  have hsum_ae : ∀ᵐ ω' ∂ν, ∀ t,
      Integrable (fun p ↦ exp (t * (X p.1 + Y p.2))) ((κ ⊗ₖ η) ω') := by
    have h (n : ℤ) := Measure.ae_integrable_of_integrable_comp (hsum_int n)
    rw [← ae_all_iff] at h
    filter_upwards [h] with ω' hi t
    exact integrable_exp_mul_of_le_of_le (hi _) (hi _) (Int.floor_le t) (Int.le_ceil t)
  filter_upwards [hX.mgf_le, hX.ae_forall_integrable_exp_mul,
    Measure.ae_ae_of_ae_compProd hY.mgf_le, hsum_ae]
    with ω' hX_mgf hX_int hY_mgf hsum_int'
  intro t ht htc
  calc mgf (fun p ↦ X p.1 + Y p.2) ((κ ⊗ₖ η) ω') t
  _ = ∫ x, exp (t * X x) * ∫ y, exp (t * Y y) ∂(η (ω', x)) ∂(κ ω') := by
    have hi := hsum_int' t
    simp_rw [mgf, mul_add, exp_add] at hi ⊢
    simp_rw [integral_compProd hi, integral_const_mul]
  _ ≤ ∫ x, exp (t * X x) *
      exp ((W : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) ∂(κ ω') := by
    refine integral_mono_of_nonneg ?_ ((hX_int t).mul_const _) ?_
    · exact ae_of_all _ fun _ ↦ mul_nonneg (by positivity)
        (integral_nonneg (fun _ ↦ by positivity))
    · have hy : ∀ᵐ x ∂κ ω', mgf Y (η (ω', x)) t ≤
          exp ((W : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by
        filter_upwards [hY_mgf] with x hx
        exact hx t ht htc
      filter_upwards [hy] with x hx
      exact mul_le_mul_of_nonneg_left hx (by positivity)
  _ ≤ exp (((V + W : ℝ≥0) : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by
    rw [integral_mul_const]
    exact mgf_mul_exp_le_add (hX_mgf t ht htc)

/-- Tower-property additivity of variance factors for two consecutive kernel increments. -/
lemma add_compProd {η : Kernel (Ω' × Ω) Ω''} [IsZeroOrMarkovKernel η]
    (hX : Kernel.HasSubgammaMGF X V c κ ν) (hY : Kernel.HasSubgammaMGF Y W c η (ν ⊗ₘ κ)) :
    Kernel.HasSubgammaMGF (fun p ↦ X p.1 + Y p.2) (V + W) c (κ ⊗ₖ η) ν := by
  by_cases hκ : IsSFiniteKernel κ
  · let _ := hκ
    exact add_compProd_of_isSFiniteKernel hX hY
  · rw [Kernel.compProd_of_not_isSFiniteKernel_left _ _ hκ]
    refine ⟨by simp, ?_⟩
    filter_upwards with ω t ht htc
    simpa [mgf] using exp_nonneg ((V + W : ℝ≥0) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))

/-- Additivity in the usual sequential-kernel formulation. -/
lemma add_of_indep {η : Kernel Ω Ω''} [IsZeroOrMarkovKernel η]
    (hX : Kernel.HasSubgammaMGF X V c κ ν) (hY : Kernel.HasSubgammaMGF Y W c η (κ ∘ₘ ν)) :
    Kernel.HasSubgammaMGF (fun p ↦ X p.1 + Y p.2) (V + W) c
      (κ ⊗ₖ Kernel.prodMkLeft Ω' η) ν :=
  hX.add_compProd hY.prodMkLeft_compProd

end Kernel.HasSubgammaMGF

end Contrib.Freedman

namespace Contrib.Freedman

section Conditional
variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {X : Ω → ℝ} {V c : ℝ≥0}
  {hm : m ≤ mΩ} [StandardBorelSpace Ω]
  {μ : Measure Ω} [IsFiniteMeasure μ]

variable (m) (hm) in
/-- Conditional sub-gamma MGF, expressed using the conditional-expectation kernel. -/
def HasCondSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) [IsFiniteMeasure μ] : Prop :=
  Contrib.Freedman.Kernel.HasSubgammaMGF X V c (condExpKernel μ m) (μ.trim hm)

namespace HasCondSubgammaMGF

lemma integrable_exp_mul (h : HasCondSubgammaMGF m hm X V c μ) (t : ℝ) :
    Integrable (fun ω ↦ exp (t * X ω)) μ :=
  condExpKernel_comp_trim (μ := μ) hm ▸
    Contrib.Freedman.Kernel.HasSubgammaMGF.integrable_exp_mul h t

lemma ae_condExp_le (h : HasCondSubgammaMGF m hm X V c μ) {t : ℝ}
    (ht : 0 ≤ t) (htc : (c : ℝ) * t < 1) :
    ∀ᵐ ω ∂μ, (μ[fun x ↦ exp (t * X x) | m]) ω ≤
      exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t))) := by
  have heq := condExp_ae_eq_trim_integral_condExpKernel hm
    (Contrib.Freedman.Kernel.HasSubgammaMGF.integrable_exp_mul h t)
  simp_rw [condExpKernel_comp_trim] at heq
  have hb := Contrib.Freedman.Kernel.HasSubgammaMGF.mgf_le h
  apply ae_of_ae_trim hm
  filter_upwards [heq, hb] with ω heq hb
  rw [heq]
  exact hb t ht htc

end HasCondSubgammaMGF

end Conditional

end Contrib.Freedman


namespace Contrib.Freedman

section MeasureLevel

variable {Ω Ω' : Type*} {m mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {μ : Measure Ω} {X : Ω → ℝ} {V W c : ℝ≥0}

/-- Measure-valued sub-gamma MGF bound, including exponential integrability. -/
structure MeasureSubgammaMGF (X : Ω → ℝ) (V c : ℝ≥0)
    (μ : Measure Ω := by volume_tac) : Prop where
  integrable_exp_mul : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, 0 ≤ t → (c : ℝ) * t < 1 →
    mgf X μ t ≤ exp ((V : ℝ) * t ^ 2 / (2 * (1 - (c : ℝ) * t)))

lemma measureSubgammaMGF_iff_kernel :
    MeasureSubgammaMGF X V c μ ↔
      Kernel.HasSubgammaMGF X V c (Kernel.const Unit μ) (Measure.dirac ()) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨by simpa, by
      filter_upwards with u
      intro t ht htc
      simpa only [Kernel.const_apply] using h2 t ht htc⟩,
    fun ⟨h1, h2⟩ ↦ ⟨by simpa using h1, by
      simpa only [ae_dirac_eq, Filter.eventually_pure, Kernel.const_apply] using h2⟩⟩

namespace MeasureSubgammaMGF

@[simp] lemma fun_zero [IsZeroOrProbabilityMeasure μ] :
    MeasureSubgammaMGF (fun _ ↦ 0) 0 c μ := by
  simp [measureSubgammaMGF_iff_kernel]

@[simp] lemma zero [IsZeroOrProbabilityMeasure μ] : MeasureSubgammaMGF 0 0 c μ := fun_zero

lemma of_map {μ : Measure Ω'} {Y : Ω' → Ω} (hY : AEMeasurable Y μ)
    (h : MeasureSubgammaMGF X V c (μ.map Y)) : MeasureSubgammaMGF (X ∘ Y) V c μ where
  integrable_exp_mul t := by
    have h1 := h.integrable_exp_mul t
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t ht htc := by
    convert h.mgf_le t ht htc using 1
    rw [mgf_map hY (h.integrable_exp_mul t).1]

lemma trim (hm : m ≤ mΩ) (hXm : Measurable[m] X) (hX : MeasureSubgammaMGF X V c μ) :
    MeasureSubgammaMGF X V c (μ.trim hm) where
  integrable_exp_mul t := by
    refine (hX.integrable_exp_mul t).trim hm ?_
    exact Measurable.stronglyMeasurable <| by fun_prop
  mgf_le t ht htc := by
    rw [mgf, ← integral_trim]
    · exact hX.mgf_le t ht htc
    · exact Measurable.stronglyMeasurable <| by fun_prop

end MeasureSubgammaMGF

end MeasureLevel

section Martingale

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {X : Ω → ℝ} [StandardBorelSpace Ω]

lemma MeasureSubgammaMGF.add_of_hasCondSubgammaMGF [IsFiniteMeasure μ]
    {Y : Ω → ℝ} {V W c : ℝ≥0} (hm : m ≤ mΩ)
    (hX : MeasureSubgammaMGF X V c (μ.trim hm))
    (hY : HasCondSubgammaMGF m hm Y W c μ) :
    MeasureSubgammaMGF (X + Y) (V + W) c μ := by
  suffices MeasureSubgammaMGF (fun p ↦ X p.1 + Y p.2) (V + W) c
      (@Measure.map Ω (Ω × Ω) mΩ (m.prod mΩ) (fun ω ↦ (id ω, id ω)) μ) by
    have h_eq : X + Y = (fun p ↦ X p.1 + Y p.2) ∘ (fun ω ↦ (id ω, id ω)) := rfl
    rw [h_eq]
    refine MeasureSubgammaMGF.of_map ?_ this
    exact @Measurable.aemeasurable _ _ _ (m.prod mΩ) _ _
      ((measurable_id'' hm).prodMk measurable_id)
  rw [measureSubgammaMGF_iff_kernel] at hX ⊢
  have hY' : Kernel.HasSubgammaMGF Y W c (condExpKernel μ m)
      (Kernel.const Unit (μ.trim hm) ∘ₘ Measure.dirac ()) := by simpa
  convert hX.add_of_indep hY'
  ext
  rw [Kernel.const_apply, ← Measure.compProd, compProd_trim_condExpKernel]
  apply Measure.map_congr
  filter_upwards with ω
  rfl

variable {Y : ℕ → Ω → ℝ} {V : ℕ → ℝ≥0} {c : ℝ≥0} {ℱ : Filtration ℕ mΩ}

lemma MeasureSubgammaMGF.sum_of_hasCondSubgammaMGF [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : MeasureSubgammaMGF (Y 0) (V 0) c μ) (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgammaMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (V (i + 1)) c μ) :
    MeasureSubgammaMGF (fun ω ↦ ∑ i ∈ Finset.range n, Y i ω)
      (∑ i ∈ Finset.range n, V i) c μ := by
  induction n with
  | zero => simp
  | succ n hn =>
    induction n with
    | zero => simp [h0]
    | succ n =>
      specialize hn fun i hi ↦ h_subG i (by lia)
      simp_rw [Finset.sum_range_succ _ (n + 1)]
      refine MeasureSubgammaMGF.add_of_hasCondSubgammaMGF (ℱ.le n) ?_
        (h_subG n (by lia))
      refine MeasureSubgammaMGF.trim (ℱ.le n) ?_ hn
      refine Finset.measurable_fun_sum (Finset.range (n + 1)) fun k hk ↦
        ((h_adapted k).mono (ℱ.mono ?_)).measurable
      simp only [Finset.mem_range] at hk
      lia

/-- Freedman/Bernstein upper tail for a finite adapted sum of conditionally sub-gamma increments. -/
theorem subgamma_bernstein_tail [IsZeroOrProbabilityMeasure μ]
    (h_adapted : StronglyAdapted ℱ Y) (h0 : MeasureSubgammaMGF (Y 0) (V 0) c μ) (n : ℕ)
    (h_subG : ∀ i < n - 1,
      HasCondSubgammaMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (V (i + 1)) c μ)
    {ε : ℝ} (hV : 0 < (∑ i ∈ Finset.range n, V i : ℝ≥0)) (hc : 0 < c) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ ∑ i ∈ Finset.range n, Y i ω} ≤
      Real.exp (-ε ^ 2 /
        (2 * (((∑ i ∈ Finset.range n, V i : ℝ≥0) : ℝ) + (c : ℝ) * ε))) := by
  let hsum := MeasureSubgammaMGF.sum_of_hasCondSubgammaMGF h_adapted h0 n h_subG
  apply subgamma_tail (h := hsum.mgf_le) (mod_cast hV) (mod_cast hc) hε
  exact hsum.integrable_exp_mul _

end Martingale

end Contrib.Freedman
