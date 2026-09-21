/-
Copyright (c) 2026 The lean-malliavin contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-malliavin contributors
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic.Recall

/-!
# The Fubini lift `L²(μ; L²(ν)) → L²(ν × μ)`

A square-integrable random variable `U` with values in `L²(ν)` should be the same thing as a
square-integrable function of two variables `(t, ω) ↦ U ω t`.  Choosing jointly measurable
representatives is delicate, so we construct the map as an isometry: on the simple tensors
`1_A • g` (the `L²(ν)`-valued indicator functions `indicatorConstLp`) it is
`(t, ω) ↦ g t · 1_A ω`, the Gram matrices of the two families agree (`inner_indicatorLp`,
`inner_tensorLp`), the simple tensors have dense span (`Lp.induction`), and
`LinearMap.extendOfNorm` extends along the dense map.

## Main definitions

* `Malliavin.fubiniLift`: the linear isometry `Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ)`;
* `Malliavin.tensorLp`: the simple tensor `(t, ω) ↦ g t · 1_A ω` in `L²(ν × μ)`.

## Main results

* `Malliavin.fubiniLift_indicatorLp`: `fubiniLift (1_A • g) = tensorLp A g`;
* `Malliavin.inner_fubiniLift`, `norm_fubiniLift`: the lift is an isometry;
* `Malliavin.inner_fubiniLift_tensorLp`: the weak Fubini identity
  `⟪fubiniLift U, g ⊗ 1_A⟫ = ∫ ω in A, ⟪g, U ω⟫ ∂μ`;
* `Malliavin.fubiniLift_smulLp`: on rank-one elements, `fubiniLift (G • g) = g ⊗ G`;
* `Malliavin.fubiniLift_surjective`, `fubiniEquiv`: for σ-finite measures the lift is onto, so
  `L²(μ; L²(ν)) ≃ L²(ν × μ)` isometrically.
-/

open MeasureTheory Filter Topology Function
open scoped ENNReal NNReal InnerProductSpace

universe u_1 u_2 u_3

recall MeasureTheory.integral_prod_mul {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SFinite ν] [SFinite μ] {L : Type u_3}
    [RCLike L] (f : α → L) (g : β → L) :
    ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y, g y ∂ν

recall MeasureTheory.Integrable.mul_prod {α : Type u_1} {β : Type u_2} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} {L : Type u_3} [NormedRing L] {f : α → L}
    {g : β → L} (hf : Integrable f μ) (hg : Integrable g ν) :
    Integrable (fun z : α × β ↦ f z.1 * g z.2) (μ.prod ν)

recall MeasureTheory.tendsto_measure_iInter_atTop {α : Type u_1} {ι : Type u_2}
    {m : MeasurableSpace α} {μ : Measure α} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated]
    {s : ι → Set α} (hs : ∀ i, NullMeasurableSet (s i) μ) (hm : Antitone s)
    (hf : ∃ i, μ (s i) ≠ ∞) : Tendsto (μ ∘ s) atTop (𝓝 (μ (⋂ n, s n)))

recall MeasurableSpace.induction_on_inter {α : Type u_1} {m : MeasurableSpace α}
    {C : ∀ s : Set α, MeasurableSet s → Prop} {s : Set (Set α)} (h_eq : m = .generateFrom s)
    (h_inter : IsPiSystem s) (empty : C ∅ .empty)
    (basic : ∀ t (ht : t ∈ s), C t (h_eq ▸ .basic t ht))
    (compl : ∀ t (htm : MeasurableSet t), C t htm → C tᶜ htm.compl)
    (iUnion : ∀ (f : ℕ → Set α), Pairwise (Disjoint on f) → ∀ (hfm : ∀ i, MeasurableSet (f i)),
      (∀ i, C (f i) (hfm i)) → C (⋃ i, f i) (.iUnion hfm)) :
    ∀ t (ht : MeasurableSet t), C t ht

namespace Malliavin

section Generic

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}

/-- Finite-measure measurable sets. -/
abbrev FiniteMeasurableSet (μ : Measure Ω) := {A : Set Ω // MeasurableSet A ∧ μ A ≠ ∞}

/-! ### Simple tensors -/

/-- The simple tensor `(t, ω) ↦ g t · 1_A ω` is square integrable on the product. -/
theorem memLp_tensor (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    MemLp (fun p : T × Ω ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2) 2 (ν.prod μ) := by
  have hg : MemLp (g : T → ℝ) 2 ν := Lp.memLp g
  have hA : MemLp (A.1.indicator (1 : Ω → ℝ)) 2 μ :=
    memLp_indicator_const 2 A.2.1 (1 : ℝ) (Or.inr A.2.2)
  refine (memLp_two_iff_integrable_sq (hg.1.comp_fst.mul hA.1.comp_snd)).mpr ?_
  refine (hg.integrable_sq.mul_prod hA.integrable_sq).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

/-- The simple tensor `(t, ω) ↦ g t · 1_A ω` as an element of `L²(ν × μ)`. -/
noncomputable def tensorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) : Lp ℝ 2 (ν.prod μ) :=
  (memLp_tensor A g).toLp _

theorem coeFn_tensorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    (tensorLp A g : T × Ω → ℝ) =ᵐ[ν.prod μ]
      fun p ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2 :=
  MemLp.coeFn_toLp _

/-- The `L²(ν)`-valued indicator `1_A • g` in `L²(μ; L²(ν))`. -/
noncomputable def indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) : Lp (Lp ℝ 2 ν) 2 μ :=
  indicatorConstLp 2 A.2.1 A.2.2 g

/-- Gram matrix of the `L²(ν)`-valued indicators: `⟪1_A • g, 1_{A'} • g'⟫ = μ (A ∩ A') ⟪g, g'⟫`. -/
theorem inner_indicatorLp (A A' : FiniteMeasurableSet μ) (g g' : Lp ℝ 2 ν) :
    ⟪indicatorLp A g, indicatorLp A' g'⟫_ℝ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
  unfold indicatorLp
  rw [L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ A.2.1 A.2.2 g,
    setIntegral_indicatorConstLp A.2.1 A'.2.1 A'.2.2, real_inner_smul_right, Set.inter_comm]

/-! ### The lift on formal combinations of simple tensors -/

/-- Formal combinations of simple tensors, realized in `L²(μ; L²(ν))`. -/
noncomputable def tensorStepToLp :
    (FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) →ₗ[ℝ] Lp (Lp ℝ 2 ν) 2 μ :=
  Finsupp.linearCombination ℝ fun x ↦ indicatorLp x.1 x.2

/-- Formal combinations of simple tensors, realized in `L²(ν × μ)`. -/
noncomputable def tensorStepToProd :
    (FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) →ₗ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  Finsupp.linearCombination ℝ fun x ↦ tensorLp x.1 x.2

theorem tensorStepToLp_single (x : FiniteMeasurableSet μ × Lp ℝ 2 ν) (c : ℝ) :
    tensorStepToLp (Finsupp.single x c) = c • indicatorLp x.1 x.2 :=
  Finsupp.linearCombination_single _ _ _

theorem tensorStepToProd_single (x : FiniteMeasurableSet μ × Lp ℝ 2 ν) (c : ℝ) :
    tensorStepToProd (Finsupp.single x c) = c • tensorLp x.1 x.2 :=
  Finsupp.linearCombination_single _ _ _

/-- Simple tensors have dense span in `L²(μ; L²(ν))`. -/
theorem denseRange_tensorStepToLp : DenseRange (tensorStepToLp (μ := μ) (ν := ν)) := by
  change Dense (Set.range tensorStepToLp)
  rw [← LinearMap.coe_range, tensorStepToLp, Finsupp.range_linearCombination,
    Submodule.dense_iff_topologicalClosure_eq_top, eq_top_iff]
  intro f _
  refine Lp.induction ENNReal.ofNat_ne_top
    (fun f : Lp (Lp ℝ 2 ν) 2 μ ↦ f ∈ (Submodule.span ℝ (Set.range fun x :
      FiniteMeasurableSet μ × Lp ℝ 2 ν ↦ indicatorLp x.1 x.2)).topologicalClosure)
    ?_ ?_ ?_ f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(⟨s, hs, hμs.ne⟩, c), rfl⟩)
  · intro f g _ _ _ hf hg
    exact Submodule.add_mem _ hf hg
  · exact Submodule.isClosed_topologicalClosure _

variable [SFinite μ] [SFinite ν]

/-- Gram matrix of the simple tensors: `⟪g ⊗ 1_A, g' ⊗ 1_{A'}⟫ = μ (A ∩ A') ⟪g, g'⟫`. -/
theorem inner_tensorLp (A A' : FiniteMeasurableSet μ) (g g' : Lp ℝ 2 ν) :
    ⟪tensorLp A g, tensorLp A' g'⟫_ℝ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
  rw [L2.inner_def]
  calc ∫ p, ⟪(tensorLp A g) p, (tensorLp A' g') p⟫_ℝ ∂(ν.prod μ)
      = ∫ p, (g p.1 * g' p.1) * ((A.1 ∩ A'.1).indicator (1 : Ω → ℝ) p.2) ∂(ν.prod μ) := by
        apply integral_congr_ae
        filter_upwards [coeFn_tensorLp A g, coeFn_tensorLp A' g'] with p h1 h2
        rw [h1, h2, Set.inter_indicator_one]
        simp only [RCLike.inner_apply, conj_trivial, Pi.mul_apply]
        ring
    _ = (∫ t, g t * g' t ∂ν) * ∫ ω, (A.1 ∩ A'.1).indicator (1 : Ω → ℝ) ω ∂μ :=
        integral_prod_mul (fun t ↦ g t * g' t) (fun ω ↦ (A.1 ∩ A'.1).indicator (1 : Ω → ℝ) ω)
    _ = μ.real (A.1 ∩ A'.1) * ⟪g, g'⟫_ℝ := by
        rw [integral_indicator_one (A.2.1.inter A'.2.1), L2.inner_def, mul_comm]
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        simp only [RCLike.inner_apply, conj_trivial, mul_comm]

theorem inner_tensorStepToProd (v w : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    ⟪tensorStepToProd v, tensorStepToProd w⟫_ℝ = ⟪tensorStepToLp v, tensorStepToLp w⟫_ℝ := by
  unfold tensorStepToProd tensorStepToLp
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, inner_tensorLp, inner_indicatorLp]

theorem norm_tensorStepToProd (v : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    ‖tensorStepToProd v‖ = ‖tensorStepToLp v‖ := by
  have h := inner_tensorStepToProd v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-! ### The Fubini lift -/

/-- **The Fubini lift** `L²(μ; L²(ν)) → L²(ν × μ)`, as a continuous linear map. -/
noncomputable def fubiniLiftL : Lp (Lp ℝ 2 ν) 2 μ →L[ℝ] Lp ℝ 2 (ν.prod μ) :=
  tensorStepToProd.extendOfNorm tensorStepToLp

theorem fubiniLiftL_tensorStepToLp (v : FiniteMeasurableSet μ × Lp ℝ 2 ν →₀ ℝ) :
    fubiniLiftL (tensorStepToLp v) = tensorStepToProd v :=
  LinearMap.extendOfNorm_eq denseRange_tensorStepToLp
    ⟨1, fun v ↦ by rw [norm_tensorStepToProd, one_mul]⟩ v

/-- `fubiniLift (1_A • g) = g ⊗ 1_A`. -/
theorem fubiniLiftL_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    fubiniLiftL (indicatorLp A g) = tensorLp A g := by
  have := fubiniLiftL_tensorStepToLp (Finsupp.single (A, g) (1 : ℝ))
  rwa [tensorStepToLp_single, tensorStepToProd_single, one_smul, one_smul] at this

/-- The Fubini lift preserves inner products. -/
theorem inner_fubiniLiftL (f g : Lp (Lp ℝ 2 ν) 2 μ) :
    ⟪fubiniLiftL f, fubiniLiftL g⟫_ℝ = ⟪f, g⟫_ℝ := by
  refine denseRange_tensorStepToLp.induction_on₂
    (p := fun f g ↦ ⟪fubiniLiftL f, fubiniLiftL g⟫_ℝ = ⟪f, g⟫_ℝ) ?_ ?_ f g
  · exact isClosed_eq ((fubiniLiftL.continuous.comp continuous_fst).inner
      (fubiniLiftL.continuous.comp continuous_snd)) (continuous_fst.inner continuous_snd)
  · intro v w
    simp only [fubiniLiftL_tensorStepToLp, inner_tensorStepToProd]

theorem norm_fubiniLiftL (f : Lp (Lp ℝ 2 ν) 2 μ) : ‖fubiniLiftL f‖ = ‖f‖ := by
  have h := inner_fubiniLiftL f f
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

/-- **The Fubini lift** `L²(μ; L²(ν)) → L²(ν × μ)` as a linear isometry. -/
noncomputable def fubiniLift : Lp (Lp ℝ 2 ν) 2 μ →ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  ⟨fubiniLiftL.toLinearMap, norm_fubiniLiftL⟩

theorem fubiniLift_apply (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniLift f = fubiniLiftL f := rfl

theorem fubiniLift_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    fubiniLift (indicatorLp A g) = tensorLp A g :=
  fubiniLiftL_indicatorLp A g

theorem coeFn_fubiniLift_indicatorLp (A : FiniteMeasurableSet μ) (g : Lp ℝ 2 ν) :
    (fubiniLift (indicatorLp A g) : T × Ω → ℝ) =ᵐ[ν.prod μ]
      fun p ↦ g p.1 * A.1.indicator (1 : Ω → ℝ) p.2 := by
  rw [fubiniLift_indicatorLp]
  exact coeFn_tensorLp A g

/-- **Weak Fubini identity**: pairing the lift of `U` with a simple tensor `g ⊗ 1_A` is the
integral over `A` of the `L²(ν)` pairing `⟪g, U ω⟫`. -/
theorem inner_fubiniLift_tensorLp (U : Lp (Lp ℝ 2 ν) 2 μ) (A : FiniteMeasurableSet μ)
    (g : Lp ℝ 2 ν) :
    ⟪fubiniLift U, tensorLp A g⟫_ℝ = ∫ ω in A.1, ⟪g, U ω⟫_ℝ ∂μ := by
  rw [← fubiniLift_indicatorLp, LinearIsometry.inner_map_map, real_inner_comm, indicatorLp,
    L2.inner_indicatorConstLp_eq_setIntegral_inner ℝ U A.2.1 g A.2.2]

end Generic

/-! ### Rank-one elements

The lift of a rank-one element `ω ↦ G ω • g` of `L²(μ; L²(ν))` is the tensor `(t, ω) ↦ g t · G ω`;
this extends `fubiniLift_indicatorLp` from indicators to all of `L²(μ)` by `Lp.induction`. -/

section RankOne

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The rank-one element `ω ↦ G ω • e` of `L²(μ; E)`, as a continuous linear map in `G`. -/
noncomputable def smulLp (e : E) : Lp ℝ 2 μ →L[ℝ] Lp E 2 μ :=
  (ContinuousLinearMap.toSpanSingleton ℝ e).compLpL 2 μ

theorem coeFn_smulLp (e : E) (G : Lp ℝ 2 μ) :
    (smulLp e G : Ω → E) =ᵐ[μ] fun ω ↦ G ω • e := by
  filter_upwards [(ContinuousLinearMap.toSpanSingleton ℝ e).coeFn_compLpL (p := 2) (μ := μ) G]
    with ω hω
  rw [smulLp, hω, ContinuousLinearMap.toSpanSingleton_apply]

theorem smulLp_indicatorConstLp (e : E) {A : Set Ω} (hA : MeasurableSet A)
    (hμA : μ A ≠ ∞) (c : ℝ) :
    smulLp e (indicatorConstLp 2 hA hμA c) = indicatorConstLp 2 hA hμA (c • e) := by
  apply Lp.ext
  filter_upwards [coeFn_smulLp e (indicatorConstLp 2 hA hμA c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c),
    indicatorConstLp_coeFn (p := 2) (hs := hA) (hμs := hμA) (c := c • e)] with ω h1 h2 h3
  rw [h1, h2, h3]
  by_cases hω : ω ∈ A <;> simp [hω]

/-- The product `(t, ω) ↦ g t * G ω` is square integrable on the product. -/
theorem memLp_tensor' (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    MemLp (fun p : T × Ω ↦ g p.1 * G p.2) 2 (ν.prod μ) := by
  refine (memLp_two_iff_integrable_sq
    ((Lp.aestronglyMeasurable g).comp_fst.mul (Lp.aestronglyMeasurable G).comp_snd)).mpr ?_
  refine ((Lp.memLp g).integrable_sq.mul_prod (Lp.memLp G).integrable_sq).congr ?_
  filter_upwards with p
  simp only [Pi.mul_apply]
  ring

/-- The tensor `(t, ω) ↦ g t * G ω` in `L²(ν × μ)`. -/
noncomputable def tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) : Lp ℝ 2 (ν.prod μ) :=
  (memLp_tensor' g G).toLp _

theorem coeFn_tensor (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    (tensor g G : T × Ω → ℝ) =ᵐ[ν.prod μ] fun p ↦ g p.1 * G p.2 :=
  MemLp.coeFn_toLp _

theorem tensor_add (g : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    tensor g (G + G') = tensor g G + tensor g G' := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (G + G' : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ]
      fun p ↦ G p.2 + G' p.2 :=
    Measure.quasiMeasurePreserving_snd.ae_eq_comp (Lp.coeFn_add G G')
  filter_upwards [coeFn_tensor g (G + G'), coeFn_tensor g G, coeFn_tensor g G',
    Lp.coeFn_add (tensor g G) (tensor g G'), h5] with p h1 h2 h3 h4 h5
  rw [h1, h4, Pi.add_apply, h2, h3, h5]
  ring

theorem tensor_smul (g : Lp ℝ 2 ν) (c : ℝ) (G : Lp ℝ 2 μ) :
    tensor g (c • G) = c • tensor g G := by
  apply Lp.ext
  have h5 : (fun p : T × Ω ↦ (c • G : Lp ℝ 2 μ) p.2) =ᵐ[ν.prod μ] fun p ↦ c * G p.2 := by
    have h : (c • (G : Ω → ℝ)) =ᵐ[μ] fun ω ↦ c * G ω :=
      Filter.Eventually.of_forall fun ω ↦ by simp
    exact Measure.quasiMeasurePreserving_snd.ae_eq_comp ((Lp.coeFn_smul c G).trans h)
  filter_upwards [coeFn_tensor g (c • G), coeFn_tensor g G, Lp.coeFn_smul c (tensor g G), h5]
    with p h1 h2 h3 h5
  rw [h1, h3, Pi.smul_apply, h2, h5, smul_eq_mul]
  ring

/-- Inner products of simple tensors factor into the two component inner products. -/
theorem inner_tensor [SFinite μ] [SFinite ν]
    (g g' : Lp ℝ 2 ν) (G G' : Lp ℝ 2 μ) :
    inner ℝ (tensor g G) (tensor g' G') = inner ℝ g g' * inner ℝ G G' := by
  rw [L2.inner_def, L2.inner_def, L2.inner_def]
  simp only [RCLike.inner_apply, conj_trivial]
  calc
    ∫ p, tensor g' G' p * tensor g G p ∂ν.prod μ =
        ∫ p, (g' p.1 * g p.1) * (G' p.2 * G p.2) ∂ν.prod μ := by
      apply integral_congr_ae
      filter_upwards [coeFn_tensor g G, coeFn_tensor g' G'] with p hfirst hsecond
      rw [hfirst, hsecond]
      ring
    _ = (∫ t, g' t * g t ∂ν) * ∫ w, G' w * G w ∂μ :=
      integral_prod_mul (fun t ↦ g' t * g t) (fun w ↦ G' w * G w)

/-- `‖g ⊗ G‖ = ‖g‖ * ‖G‖`. -/
theorem norm_tensor [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    ‖tensor g G‖ = ‖g‖ * ‖G‖ := by
  have h := inner_tensor g g G G
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    ← mul_pow] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp h

/-- `G ↦ g ⊗ G` as a continuous linear map. -/
noncomputable def tensorL [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 (ν.prod μ) :=
  LinearMap.mkContinuous
    { toFun := tensor g
      map_add' := tensor_add g
      map_smul' := tensor_smul g } ‖g‖ fun G ↦ by
      change ‖tensor g G‖ ≤ ‖g‖ * ‖G‖
      rw [norm_tensor]

theorem tensorL_apply [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    tensorL g G = tensor g G := rfl

/-- **The Fubini lift on rank-one elements**: `fubiniLift (G • g) = g ⊗ G`. -/
theorem fubiniLift_smulLp [SFinite μ] [SFinite ν] (g : Lp ℝ 2 ν) (G : Lp ℝ 2 μ) :
    fubiniLift (smulLp g G) = tensor g G := by
  refine Lp.induction ENNReal.ofNat_ne_top
    (fun G : Lp ℝ 2 μ ↦ fubiniLift (smulLp g G) = tensor g G) ?_ ?_ ?_ G
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst, smulLp_indicatorConstLp]
    change fubiniLift (indicatorLp ⟨s, hs, hμs.ne⟩ (c • g)) = _
    rw [fubiniLift_indicatorLp]
    apply Lp.ext
    filter_upwards [coeFn_tensorLp ⟨s, hs, hμs.ne⟩ (c • g),
      coeFn_tensor g (indicatorConstLp 2 hs hμs.ne c),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := c)),
      Measure.quasiMeasurePreserving_fst.ae_eq_comp (Lp.coeFn_smul c g)] with p h1 h2 h3 h4
    rw [h1, h2]
    simp only [Function.comp_apply] at h3 h4
    rw [h3, h4, Pi.smul_apply, smul_eq_mul]
    by_cases hp : p.2 ∈ s <;> simp [hp, mul_comm]
  · intro G G' _ _ _ hG hG'
    rw [map_add, map_add, hG, hG', tensor_add]
  · exact isClosed_eq (fubiniLift.continuous.comp (smulLp g).continuous) (tensorL g).continuous

end RankOne

/-! ### Surjectivity: the Fubini isomorphism

The range of the Fubini lift is closed and contains the indicators of all finite rectangles; a
Dynkin-system argument inside each finite rectangle, followed by exhaustion along the spanning
sets of the two σ-finite measures, shows that it contains the indicator of every finite-measure
set, hence everything (`Lp.induction`). -/

section Surj

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}

/-- Changing the set of an `indicatorConstLp` along an equality of sets. -/
theorem indicatorConstLp_congr_set {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] {p : ℝ≥0∞} {s t : Set α} (h : s = t) (hs : MeasurableSet s)
    (hms : m s ≠ ∞) (c : E) :
    indicatorConstLp p hs hms c = indicatorConstLp p (h ▸ hs) (h ▸ hms) c := by
  subst h
  rfl

variable [SFinite μ] [SFinite ν]

/-- The range of the Fubini lift, a closed subspace of `L²(ν × μ)`. -/
noncomputable abbrev fubiniRange : Submodule ℝ (Lp ℝ 2 (ν.prod μ)) :=
  LinearMap.range (fubiniLift (μ := μ) (ν := ν)).toLinearMap

theorem isClosed_fubiniRange : IsClosed (fubiniRange (μ := μ) (ν := ν) : Set (Lp ℝ 2 (ν.prod μ))) :=
  (fubiniLift (μ := μ) (ν := ν)).isometry.isClosedEmbedding.isClosed_range

/-- Indicators of finite rectangles lie in the range. -/
theorem indicatorConstLp_prod_mem_fubiniRange {U : Set T} {A : Set Ω} (hU : MeasurableSet U)
    (hA : MeasurableSet A) (hνU : ν U ≠ ∞) (hμA : μ A ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 (hU.prod hA) (by rw [Measure.prod_prod]; finiteness) c ∈
      fubiniRange (μ := μ) (ν := ν) := by
  refine ⟨indicatorLp ⟨A, hA, hμA⟩ (indicatorConstLp 2 hU hνU c), ?_⟩
  rw [LinearIsometry.coe_toLinearMap, fubiniLift_indicatorLp]
  apply Lp.ext
  filter_upwards [coeFn_tensorLp ⟨A, hA, hμA⟩ (indicatorConstLp 2 hU hνU c),
    indicatorConstLp_coeFn (p := 2) (hs := hU.prod hA)
      (hμs := by rw [Measure.prod_prod]; finiteness) (c := c),
    Measure.quasiMeasurePreserving_fst.ae_eq_comp
      (indicatorConstLp_coeFn (p := 2) (hs := hU) (hμs := hνU) (c := c))] with p h1 h2 h3
  rw [h1, h2]
  simp only [Function.comp_apply] at h3
  rw [h3]
  by_cases hp1 : p.1 ∈ U <;> by_cases hp2 : p.2 ∈ A <;> simp [Set.indicator, hp1, hp2]

/-- `‖X‖² = ∫ ‖X x‖²` in `L²(m; E)`. -/
theorem norm_sq_eq_integral_norm_sq {α E : Type*} [MeasurableSpace α] {m : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (X : Lp E 2 m) :
    ‖X‖ ^ 2 = ∫ x, ‖X x‖ ^ 2 ∂m := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext x
  exact real_inner_self_eq_norm_sq _

/-- Pointwise: the indicator of a disjoint union minus a partial sum of indicators is the
indicator of the tail. -/
theorem indicator_iUnion_sub_sum {α : Type*} {f : ℕ → Set α} (hf : Pairwise (Disjoint on f))
    (c : ℝ) (N : ℕ) (x : α) :
    (⋃ i, f i).indicator (fun _ ↦ c) x - ∑ i ∈ Finset.range N, (f i).indicator (fun _ ↦ c) x =
      (⋃ i, ⋃ (_ : N ≤ i), f i).indicator (fun _ ↦ c) x := by
  by_cases hx : x ∈ ⋃ i, f i
  · obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
    have hj' : ∀ i, i ≠ j → x ∉ f i := fun i hi hx' ↦ Set.disjoint_left.mp (hf hi) hx' hj
    rw [Set.indicator_of_mem hx]
    by_cases hjN : N ≤ j
    · rw [Finset.sum_eq_zero fun i hi ↦ Set.indicator_of_notMem
        (hj' i (by rw [Finset.mem_range] at hi; omega)) _,
        Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨j, hjN, hj⟩), sub_zero]
    · have hnot : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
        obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp h
        exact hj' i (by omega) hxi
      rw [Finset.sum_eq_single_of_mem j (Finset.mem_range.mpr (by omega))
        (fun i _ hi ↦ Set.indicator_of_notMem (hj' i hi) _), Set.indicator_of_mem hj,
        Set.indicator_of_notMem hnot, sub_self]
  · have hnot : ∀ i, x ∉ f i := fun i hi ↦ hx (Set.mem_iUnion.mpr ⟨i, hi⟩)
    have : x ∉ ⋃ i, ⋃ (_ : N ≤ i), f i := fun h ↦ by
      obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp h
      exact hnot i hxi
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem this,
      Finset.sum_eq_zero fun i _ ↦ Set.indicator_of_notMem (hnot i) _, sub_zero]

/-- A closed subspace of `L²` containing the indicators of pairwise disjoint sets of finite total
measure contains the indicator of their union. -/
theorem indicatorConstLp_iUnion_mem {α : Type*} [MeasurableSpace α] {m : Measure α}
    {K : Submodule ℝ (Lp ℝ 2 m)} (hK : IsClosed (K : Set (Lp ℝ 2 m))) {f : ℕ → Set α}
    (hf : Pairwise (Disjoint on f)) (hfm : ∀ i, MeasurableSet (f i))
    (hU : m (⋃ i, f i) ≠ ∞) (c : ℝ)
    (hmem : ∀ i, indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c ∈ K) :
    indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c ∈ K := by
  set S : ℕ → Lp ℝ 2 m := fun N ↦ ∑ i ∈ Finset.range N, indicatorConstLp 2 (hfm i)
    (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c with hS
  have hSK : ∀ N, S N ∈ K := fun N ↦ Submodule.sum_mem _ fun i _ ↦ hmem i
  -- the tails `⋃ i ≥ N, f i` have measure tending to zero
  set tail : ℕ → Set α := fun N ↦ ⋃ i, ⋃ (_ : N ≤ i), f i with htail
  have htail_meas : ∀ N, MeasurableSet (tail N) := fun N ↦
    MeasurableSet.iUnion fun i ↦ MeasurableSet.iUnion fun _ ↦ hfm i
  have htail_sub : ∀ N, tail N ⊆ ⋃ i, f i := fun N ↦
    Set.iUnion_subset fun i ↦ Set.iUnion_subset fun _ ↦ Set.subset_iUnion f i
  have htail_anti : Antitone tail := fun N M hNM ↦
    Set.iUnion_mono fun i ↦ Set.iUnion_mono' fun h ↦ ⟨hNM.trans h, le_rfl⟩
  have htail_inter : ⋂ N, tail N = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro hx
    obtain ⟨i, _, hxi⟩ := Set.mem_iUnion₂.mp (hx 0)
    obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp (hx (i + 1))
    exact Set.disjoint_left.mp (hf (by omega : i ≠ j)) hxi hxj
  have htail_tendsto : Tendsto (fun N ↦ m (tail N)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun N ↦ (htail_meas N).nullMeasurableSet) htail_anti
      ⟨0, ne_top_of_le_ne_top hU (measure_mono (htail_sub 0))⟩
    rwa [htail_inter, measure_empty] at this
  -- the difference between the indicator of the union and a partial sum is the tail indicator
  have hdiff : ∀ N, ∀ᵐ x ∂m, (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c : α → ℝ) x -
      (S N : α → ℝ) x = (tail N).indicator (fun _ ↦ c) x := by
    intro N
    have hsum := Lp.coeFn_finsetSum (Finset.range N) fun i ↦ indicatorConstLp 2 (hfm i)
      (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c
    have hind : ∀ᵐ x ∂m, ∀ i : ℕ, (indicatorConstLp 2 (hfm i)
        (ne_top_of_le_ne_top hU (measure_mono (Set.subset_iUnion f i))) c : α → ℝ) x =
          (f i).indicator (fun _ ↦ c) x :=
      ae_all_iff.2 fun i ↦ indicatorConstLp_coeFn
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.iUnion hfm)
      (hμs := hU) (c := c), hsum, hind] with x h1 h2 h3
    rw [h1, hS, h2, Finset.sum_apply]
    simp_rw [h3]
    exact indicator_iUnion_sub_sum hf c N x
  have hnorm : ∀ N, ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2 =
      c ^ 2 * (m (tail N)).toReal := by
    intro N
    rw [norm_sq_eq_integral_norm_sq]
    calc ∫ x, ‖(indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N) x‖ ^ 2 ∂m
        = ∫ x, (tail N).indicator (fun _ ↦ c ^ 2) x ∂m := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c) (S N),
            hdiff N] with x h1 h2
          rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, sq_abs]
          by_cases hx : x ∈ tail N <;> simp [hx]
      _ = c ^ 2 * (m (tail N)).toReal := by
          rw [integral_indicator_const _ (htail_meas N), smul_eq_mul, mul_comm]
          rfl
  have hlim : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun N ↦ (m (tail N)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp htail_tendsto
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : Tendsto (fun N ↦ ‖indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c - S N‖ ^ 2)
        atTop (𝓝 0) := by
      simp_rw [hnorm]
      simpa using h1.const_mul (c ^ 2)
    have := h2.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hS_tendsto : Tendsto S atTop (𝓝 (indicatorConstLp 2 (MeasurableSet.iUnion hfm) hU c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [norm_sub_rev] using hlim
  exact hK.mem_of_tendsto hS_tendsto (Filter.Eventually.of_forall hSK)

/-- Within a finite rectangle, the indicator of every measurable set lies in the range. -/
theorem indicatorConstLp_inter_prod_mem_fubiniRange {U₀ : Set T} {A₀ : Set Ω}
    (hU₀ : MeasurableSet U₀) (hA₀ : MeasurableSet A₀) (hνU₀ : ν U₀ ≠ ∞) (hμA₀ : μ A₀ ≠ ∞) :
    ∀ (S : Set (T × Ω)) (hS : MeasurableSet S) (c : ℝ),
      indicatorConstLp 2 (hS.inter (hU₀.prod hA₀))
        (ne_top_of_le_ne_top (by rw [Measure.prod_prod]; finiteness)
          (measure_mono Set.inter_subset_right)) c ∈ fubiniRange (μ := μ) (ν := ν) := by
  have hR : (ν.prod μ) (U₀ ×ˢ A₀) ≠ ∞ := by rw [Measure.prod_prod]; finiteness
  have hfin : ∀ S : Set (T × Ω), (ν.prod μ) (S ∩ U₀ ×ˢ A₀) ≠ ∞ := fun S ↦
    ne_top_of_le_ne_top hR (measure_mono Set.inter_subset_right)
  refine MeasurableSpace.induction_on_inter
    (C := fun S hS ↦ ∀ c : ℝ, indicatorConstLp 2 (hS.inter (hU₀.prod hA₀)) (hfin S) c ∈
      fubiniRange (μ := μ) (ν := ν))
    generateFrom_prod.symm isPiSystem_prod ?_ ?_ ?_ ?_
  · intro c
    rw [indicatorConstLp_congr_set (Set.empty_inter _), indicatorConstLp_empty]
    exact Submodule.zero_mem _
  · rintro _ ⟨U, hU, A, hA, rfl⟩ c
    rw [indicatorConstLp_congr_set (Set.prod_inter_prod (s₁ := U) (t₁ := A))]
    exact indicatorConstLp_prod_mem_fubiniRange (hU.inter hU₀) (hA.inter hA₀)
      (ne_top_of_le_ne_top hνU₀ (measure_mono Set.inter_subset_right))
      (ne_top_of_le_ne_top hμA₀ (measure_mono Set.inter_subset_right)) c
  · intro t ht hind c
    have hdisj : Disjoint (t ∩ U₀ ×ˢ A₀) (tᶜ ∩ U₀ ×ˢ A₀) :=
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left disjoint_compl_right
    have hunion := indicatorConstLp_disjoint_union (p := 2) (μ := ν.prod μ)
      (ht.inter (hU₀.prod hA₀)) (ht.compl.inter (hU₀.prod hA₀)) (hfin t) (hfin tᶜ) hdisj c
    have hset : (t ∩ U₀ ×ˢ A₀) ∪ (tᶜ ∩ U₀ ×ˢ A₀) = U₀ ×ˢ A₀ := by
      ext p
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
      tauto
    rw [indicatorConstLp_congr_set hset] at hunion
    have hR' : indicatorConstLp 2 (hset ▸ (ht.inter (hU₀.prod hA₀)).union
        (ht.compl.inter (hU₀.prod hA₀))) (hset ▸ (by finiteness)) c ∈
          fubiniRange (μ := μ) (ν := ν) :=
      indicatorConstLp_prod_mem_fubiniRange hU₀ hA₀ hνU₀ hμA₀ c
    have heq : indicatorConstLp 2 (ht.compl.inter (hU₀.prod hA₀)) (hfin tᶜ) c =
        indicatorConstLp 2 (hset ▸ (ht.inter (hU₀.prod hA₀)).union
          (ht.compl.inter (hU₀.prod hA₀))) (hset ▸ (by finiteness)) c -
        indicatorConstLp 2 (ht.inter (hU₀.prod hA₀)) (hfin t) c := by
      rw [hunion, add_sub_cancel_left]
    rw [heq]
    exact Submodule.sub_mem _ hR' (hind c)
  · intro f hf hfm hind c
    rw [indicatorConstLp_congr_set (Set.iUnion_inter (U₀ ×ˢ A₀) f)]
    refine indicatorConstLp_iUnion_mem isClosed_fubiniRange
      (hf.mono fun i j hij ↦ Disjoint.mono Set.inter_subset_left Set.inter_subset_left hij)
      (fun i ↦ (hfm i).inter (hU₀.prod hA₀)) _ c fun i ↦ hind i c

variable [SigmaFinite μ] [SigmaFinite ν]

/-- Indicators of all finite-measure sets lie in the range. -/
theorem indicatorConstLp_mem_fubiniRange {S : Set (T × Ω)} (hS : MeasurableSet S)
    (hμS : (ν.prod μ) S ≠ ∞) (c : ℝ) :
    indicatorConstLp 2 hS hμS c ∈ fubiniRange (μ := μ) (ν := ν) := by
  set R : ℕ → Set (T × Ω) := fun n ↦ spanningSets ν n ×ˢ spanningSets μ n with hR
  have hRm : ∀ n, MeasurableSet (R n) := fun n ↦
    (measurableSet_spanningSets ν n).prod (measurableSet_spanningSets μ n)
  have hRmono : Monotone R := fun n m hnm ↦
    Set.prod_mono (monotone_spanningSets ν hnm) (monotone_spanningSets μ hnm)
  have hRunion : ⋃ n, R n = Set.univ := by
    ext ⟨t, ω⟩
    simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, iff_true, hR]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ((iUnion_spanningSets ν).symm ▸ Set.mem_univ t)
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp ((iUnion_spanningSets μ).symm ▸ Set.mem_univ ω)
    exact ⟨max n m, monotone_spanningSets ν (le_max_left n m) hn,
      monotone_spanningSets μ (le_max_right n m) hm⟩
  have hmem : ∀ n, indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c ∈
        fubiniRange (μ := μ) (ν := ν) := fun n ↦
    indicatorConstLp_inter_prod_mem_fubiniRange (measurableSet_spanningSets ν n)
      (measurableSet_spanningSets μ n) (measure_spanningSets_lt_top ν n).ne
      (measure_spanningSets_lt_top μ n).ne S hS c
  -- the complements `S \ R n` shrink to `∅`
  set D : ℕ → Set (T × Ω) := fun n ↦ S \ R n with hD
  have hDm : ∀ n, MeasurableSet (D n) := fun n ↦ hS.diff (hRm n)
  have hDanti : Antitone D := fun n m hnm ↦ Set.sdiff_subset_sdiff_right (hRmono hnm)
  have hDinter : ⋂ n, D n = ∅ := by
    ext p
    simp only [Set.mem_iInter, hD, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false, not_forall,
      not_and, not_not]
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp (hRunion ▸ Set.mem_univ p)
    exact ⟨n, fun _ ↦ hn⟩
  have hDtendsto : Tendsto (fun n ↦ (ν.prod μ) (D n)) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (fun n ↦ (hDm n).nullMeasurableSet) hDanti
      ⟨0, ne_top_of_le_ne_top hμS (measure_mono Set.sdiff_subset)⟩
    rwa [hDinter, measure_empty] at this
  -- the difference of indicators is the indicator of `S \ R n`
  have hdiff : ∀ n, ∀ᵐ p ∂(ν.prod μ), (indicatorConstLp 2 hS hμS c : T × Ω → ℝ) p -
      (indicatorConstLp 2 (hS.inter (hRm n))
        (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c : T × Ω → ℝ) p =
      (D n).indicator (fun _ ↦ c) p := by
    intro n
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hS) (hμs := hμS) (c := c),
      indicatorConstLp_coeFn (p := 2) (hs := hS.inter (hRm n))
        (hμs := ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) (c := c)]
      with p h1 h2
    rw [h1, h2]
    by_cases hp : p ∈ S <;> by_cases hpR : p ∈ R n <;> simp [Set.indicator, hD, hp, hpR]
  have hnorm : ∀ n, ‖indicatorConstLp 2 hS hμS c - indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c‖ ^ 2 =
      c ^ 2 * ((ν.prod μ) (D n)).toReal := by
    intro n
    rw [norm_sq_eq_integral_norm_sq]
    calc ∫ p, ‖(indicatorConstLp 2 hS hμS c - indicatorConstLp 2 (hS.inter (hRm n))
          (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c) p‖ ^ 2 ∂(ν.prod μ)
        = ∫ p, (D n).indicator (fun _ ↦ c ^ 2) p ∂(ν.prod μ) := by
          apply integral_congr_ae
          filter_upwards [Lp.coeFn_sub (indicatorConstLp 2 hS hμS c)
            (indicatorConstLp 2 (hS.inter (hRm n))
              (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c), hdiff n]
            with p h1 h2
          rw [h1, Pi.sub_apply, h2, Real.norm_eq_abs, sq_abs]
          by_cases hp : p ∈ D n <;> simp [hp]
      _ = c ^ 2 * ((ν.prod μ) (D n)).toReal := by
          rw [integral_indicator_const _ (hDm n), smul_eq_mul, mul_comm]
          rfl
  have hlim : Tendsto (fun n ↦ indicatorConstLp 2 (hS.inter (hRm n))
      (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c) atTop
      (𝓝 (indicatorConstLp 2 hS hμS c)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h1 : Tendsto (fun n ↦ ((ν.prod μ) (D n)).toReal) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hDtendsto
      rw [ENNReal.toReal_zero] at this
      exact this
    have h2 : Tendsto (fun n ↦ ‖indicatorConstLp 2 hS hμS c - indicatorConstLp 2
        (hS.inter (hRm n)) (ne_top_of_le_ne_top hμS (measure_mono Set.inter_subset_left)) c‖ ^ 2)
        atTop (𝓝 0) := by
      simp_rw [hnorm]
      simpa using h1.const_mul (c ^ 2)
    have := h2.sqrt
    simp only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] at this
    simpa only [norm_sub_rev] using this
  exact isClosed_fubiniRange.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)

/-- **The Fubini lift is onto**: its range is all of `L²(ν × μ)`. -/
theorem fubiniRange_eq_top : fubiniRange (μ := μ) (ν := ν) = ⊤ := by
  rw [eq_top_iff]
  intro f _
  refine Lp.induction ENNReal.ofNat_ne_top (fun f : Lp ℝ 2 (ν.prod μ) ↦ f ∈ fubiniRange) ?_ ?_
    isClosed_fubiniRange f
  · intro c s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact indicatorConstLp_mem_fubiniRange hs hμs.ne c
  · intro f g _ _ _ hf hg
    exact Submodule.add_mem _ hf hg

theorem fubiniLift_surjective : Function.Surjective (fubiniLift (μ := μ) (ν := ν)) := fun y ↦ by
  have : y ∈ fubiniRange (μ := μ) (ν := ν) :=
    (fubiniRange_eq_top (μ := μ) (ν := ν)) ▸ Submodule.mem_top
  exact this

/-- **The Fubini isomorphism** `L²(μ; L²(ν)) ≃ L²(ν × μ)`. -/
noncomputable def fubiniEquiv : Lp (Lp ℝ 2 ν) 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 (ν.prod μ) :=
  LinearIsometryEquiv.ofSurjective fubiniLift fubiniLift_surjective

theorem fubiniEquiv_apply (f : Lp (Lp ℝ 2 ν) 2 μ) : fubiniEquiv f = fubiniLift f := rfl

end Surj

/-! ### Bounded multipliers

Multiplication by a bounded measurable function `G` of `ω` is a continuous linear map on
`L²(μ; E)`; the Fubini lift intertwines it with multiplication by `G ∘ snd` on `L²(ν × μ)`
(`fubiniLift_boundedSMul`). -/

section Multiplier

variable {Ω E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [NormedAddCommGroup E]
  [NormedSpace ℝ E]

/-- Multiplication by a bounded measurable scalar function, as a map on `L²(μ; E)`. -/
theorem memLp_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : MemLp (fun x ↦ G x • U x) 2 μ := by
  refine MemLp.of_le ((Lp.memLp U).norm.const_mul C) (hG.smul (Lp.aestronglyMeasurable U))
    (Filter.Eventually.of_forall fun x ↦ ?_)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x)
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs (C * ‖U x‖),
    abs_of_nonneg (mul_nonneg hC0 (norm_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a bounded measurable scalar function as a linear map on `L²(μ; E)`. -/
noncomputable def boundedSMulₗ {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →ₗ[ℝ] Lp E 2 μ where
  toFun U := (memLp_boundedSMul hG hC U).toLp _
  map_add' U V := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_add U V] with x hx
    rw [hx, Pi.add_apply, Pi.add_apply, smul_add]
  map_smul' c U := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [Lp.coeFn_smul c U] with x hx
    rw [hx, Pi.smul_apply, Pi.smul_apply, smul_comm]

theorem boundedSMulₗ_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMulₗ hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl

theorem norm_boundedSMulₗ_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMulₗ hG hC U‖ ≤ C * ‖U‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)] with x hx
  rw [boundedSMulₗ_apply, hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Multiplication by a bounded measurable scalar function as a continuous linear map on
`L²(μ; E)`. -/
noncomputable def boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) : Lp E 2 μ →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous (boundedSMulₗ hG hC) C (norm_boundedSMulₗ_le hG hC)

theorem boundedSMul_apply {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    boundedSMul hG hC U = (memLp_boundedSMul hG hC U).toLp _ := rfl

theorem norm_boundedSMul_le {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) : ‖boundedSMul hG hC U‖ ≤ C * ‖U‖ :=
  norm_boundedSMulₗ_le hG hC U

theorem coeFn_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp E 2 μ) :
    (boundedSMul hG hC U : Ω → E) =ᵐ[μ] fun x ↦ G x • U x :=
  MemLp.coeFn_toLp (memLp_boundedSMul hG hC U)

end Multiplier

section Compat

variable {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T] {μ : Measure Ω} {ν : Measure T}
  [SFinite μ] [SFinite ν]

omit [SFinite μ] [SFinite ν] in
/-- A bounded measurable function of `ω`, viewed on `T × Ω`. -/
theorem aestronglyMeasurable_comp_snd {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) :
    AEStronglyMeasurable (fun p : T × Ω ↦ G p.2) (ν.prod μ) :=
  hG.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd

/-- **The Fubini lift commutes with multiplication by bounded functions of `ω`**:
`fubiniLift (G • U) = (G ∘ snd) • fubiniLift U`. -/
theorem fubiniLift_boundedSMul {G : Ω → ℝ} (hG : AEStronglyMeasurable G μ) {C : ℝ}
    (hC : ∀ x, |G x| ≤ C) (U : Lp (Lp ℝ 2 ν) 2 μ) :
    fubiniLift (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2) (fubiniLift U) := by
  refine Lp.induction ENNReal.ofNat_ne_top (fun U : Lp (Lp ℝ 2 ν) 2 μ ↦
    fubiniLift (boundedSMul hG hC U) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2) (fubiniLift U))
    ?_ ?_ ?_ U
  · intro g s hs hμs
    rw [Lp.simpleFunc.coe_indicatorConst]
    change fubiniLift (boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g)) =
      boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2)
        (fubiniLift (indicatorLp ⟨s, hs, hμs.ne⟩ g))
    rw [fubiniLift_indicatorLp]
    have h1 : boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g) =
        smulLp g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))) := by
      apply Lp.ext
      filter_upwards [coeFn_boundedSMul hG hC (indicatorLp ⟨s, hs, hμs.ne⟩ g),
        coeFn_smulLp g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
        coeFn_boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := g),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ))]
        with x h1 h2 h3 h4 h5
      rw [h1, h2, h3, indicatorLp, h4, h5]
      by_cases hx : x ∈ s <;> simp [hx]
    rw [h1, fubiniLift_smulLp]
    apply Lp.ext
    filter_upwards [coeFn_tensor g (boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
      coeFn_boundedSMul (aestronglyMeasurable_comp_snd (ν := ν) hG) (fun p ↦ hC p.2)
        (tensorLp ⟨s, hs, hμs.ne⟩ g),
      coeFn_tensorLp ⟨s, hs, hμs.ne⟩ g,
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (coeFn_boundedSMul hG hC (indicatorConstLp 2 hs hμs.ne (1 : ℝ))),
      Measure.quasiMeasurePreserving_snd.ae_eq_comp
        (indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs.ne) (c := (1 : ℝ)))]
      with p h1 h2 h3 h4 h5
    rw [h1, h2, h3]
    simp only [Function.comp_apply] at h4 h5
    rw [h4, h5, smul_eq_mul, smul_eq_mul]
    by_cases hp : p.2 ∈ s <;> simp [hp, mul_comm]
  · intro U V _ _ _ hU hV
    rw [map_add, map_add, hU, hV, map_add, map_add]
  · exact isClosed_eq (fubiniLift.continuous.comp (boundedSMul hG hC).continuous)
      ((boundedSMul _ _).continuous.comp fubiniLift.continuous)

end Compat

end Malliavin

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
