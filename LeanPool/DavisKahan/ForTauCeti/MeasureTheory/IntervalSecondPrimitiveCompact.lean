/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.IntervalWeakSecondDeriv
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.FiniteRankCompact
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# The second-primitive operator on `L²(0,1]` is compact

`secondPrimitive` — integration against the truncated linear kernel `max (t-s) 0` — defines a
bounded operator on `L²` of the unit interval.  This file bundles it as a continuous linear
map and proves it is a compact operator, by exhibiting it as the operator-norm limit of
finite-rank snapshots: freeze the output variable on the cells of a uniform partition.  The
kernel is `1`-Lipschitz in the output variable, so the `n`-cell snapshot is within `1/n` in
operator norm, and each snapshot has range inside the span of the cell indicators.

This is the quantitative heart of Rellich compactness for the free-beam form space of
Davis--Kahan 1970 Section 9: the form-space embedding factors as this operator plus a
finite-rank affine part, so no weak-topology argument is ever needed.

The scalar field is an arbitrary `RCLike` `𝕜`; in particular the operator and its compactness
are available over `ℝ`.

## Main results

* `TauCeti.secondPrimitiveCLM`: the bundled operator on `Lp 𝕜 2 unitIocMeasure`.
* `TauCeti.isCompactOperator_secondPrimitiveCLM`: compactness.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ## Function-level algebra of the second primitive -/

/-- The second primitive depends only on the almost-everywhere class of the density. -/
theorem secondPrimitive_congr_ae {w w' : ℝ → 𝕜} (h : w =ᵐ[unitIocMeasure] w') :
    secondPrimitive w = secondPrimitive w' := by
  funext t
  rw [secondPrimitive_def, secondPrimitive_def]
  refine integral_congr_ae ?_
  filter_upwards [h] with s hs
  rw [hs]

/-- The second primitive is additive in the density. -/
theorem secondPrimitive_add {w w' : ℝ → 𝕜} (hw : Integrable w unitIocMeasure)
    (hw' : Integrable w' unitIocMeasure) :
    secondPrimitive (w + w') = secondPrimitive w + secondPrimitive w' := by
  funext t
  rw [Pi.add_apply, secondPrimitive_def, secondPrimitive_def, secondPrimitive_def,
    ← integral_add (integrable_secondPrimitiveKernel_mul hw t)
      (integrable_secondPrimitiveKernel_mul hw' t)]
  congr 1 with s
  simp only [Pi.add_apply]
  ring

/-- The second primitive is homogeneous in the density. -/
theorem secondPrimitive_smul (c : 𝕜) (w : ℝ → 𝕜) :
    secondPrimitive (c • w) = c • secondPrimitive w := by
  funext t
  rw [Pi.smul_apply, smul_eq_mul, secondPrimitive_def, secondPrimitive_def,
    ← integral_const_mul]
  congr 1 with s
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The `L¹` norm of an `L²` element of the unit interval is bounded by its `L²` norm. -/
theorem integral_norm_coeFn_le (W : Lp 𝕜 2 unitIocMeasure) :
    ∫ t, ‖W t‖ ∂unitIocMeasure ≤ ‖W‖ := by
  have hmeas := (Lp.memLp W).aestronglyMeasurable
  have h1 : ∫ t, ‖W t‖ ∂unitIocMeasure
      = (eLpNorm (W : ℝ → 𝕜) 1 unitIocMeasure).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmeas, eLpNorm_one_eq_lintegral_enorm]
  have h2 : eLpNorm (W : ℝ → 𝕜) 1 unitIocMeasure
      ≤ eLpNorm (W : ℝ → 𝕜) 2 unitIocMeasure :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) hmeas
  rw [h1, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top W) h2

/-- Coefficient-level integrability of an `L²` element on the unit interval. -/
theorem integrable_coeFn (W : Lp 𝕜 2 unitIocMeasure) :
    Integrable (W : ℝ → 𝕜) unitIocMeasure :=
  (Lp.memLp W).integrable one_le_two

/-! ## The bundled operator -/

/-- The second primitive of an `L²` element, as an element of `L²`. -/
def secondPrimitiveLp (W : Lp 𝕜 2 unitIocMeasure) : Lp 𝕜 2 unitIocMeasure :=
  (memLp_secondPrimitive (integrable_coeFn W)).toLp (secondPrimitive (W : ℝ → 𝕜))

/-- The defining almost-everywhere identity of `secondPrimitiveLp`. -/
theorem coeFn_secondPrimitiveLp (W : Lp 𝕜 2 unitIocMeasure) :
    (secondPrimitiveLp W : ℝ → 𝕜) =ᵐ[unitIocMeasure] secondPrimitive (W : ℝ → 𝕜) :=
  MemLp.coeFn_toLp _

/-- Almost-everywhere pointwise bound for the second primitive of an `L²` element. -/
theorem ae_norm_secondPrimitive_coeFn_le (W : Lp 𝕜 2 unitIocMeasure) :
    ∀ᵐ t ∂unitIocMeasure, ‖secondPrimitive (W : ℝ → 𝕜) t‖ ≤ ‖W‖ := by
  filter_upwards [ae_norm_secondPrimitive_le (integrable_coeFn W)] with t ht
  exact ht.trans (integral_norm_coeFn_le W)

/-- Norm bound for the bundled second primitive. -/
theorem norm_secondPrimitiveLp_le (W : Lp 𝕜 2 unitIocMeasure) :
    ‖secondPrimitiveLp W‖ ≤ ‖W‖ := by
  rw [secondPrimitiveLp, Lp.norm_def]
  have hbound := eLpNorm_le_of_ae_bound (p := 2) (ae_norm_secondPrimitive_coeFn_le W)
  have hμ : (unitIocMeasure Set.univ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 := by
    rw [measure_univ]
    simp
  rw [hμ, one_mul] at hbound
  have heq : eLpNorm ((memLp_secondPrimitive (integrable_coeFn W)).toLp
        (secondPrimitive (W : ℝ → 𝕜))) 2 unitIocMeasure
      = eLpNorm (secondPrimitive (W : ℝ → 𝕜)) 2 unitIocMeasure :=
    eLpNorm_congr_ae (MemLp.coeFn_toLp _)
  rw [heq]
  calc (eLpNorm (secondPrimitive (W : ℝ → 𝕜)) 2 unitIocMeasure).toReal
      ≤ (ENNReal.ofReal ‖W‖).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = ‖W‖ := ENNReal.toReal_ofReal (norm_nonneg W)

/-- The second-primitive operator on `L²` of the unit interval. -/
def secondPrimitiveCLM : Lp 𝕜 2 unitIocMeasure →L[𝕜] Lp 𝕜 2 unitIocMeasure :=
  LinearMap.mkContinuous
    { toFun := secondPrimitiveLp
      map_add' := by
        intro W V
        have hcongr : secondPrimitive ((W + V : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
            = secondPrimitive ((W : ℝ → 𝕜) + (V : ℝ → 𝕜)) :=
          secondPrimitive_congr_ae (Lp.coeFn_add W V)
        refine Lp.ext ?_
        filter_upwards [coeFn_secondPrimitiveLp (W + V), coeFn_secondPrimitiveLp W,
          coeFn_secondPrimitiveLp V,
          Lp.coeFn_add (secondPrimitiveLp W) (secondPrimitiveLp V)] with t h1 h2 h3 h4
        rw [h1, h4, hcongr,
          secondPrimitive_add (integrable_coeFn W) (integrable_coeFn V)]
        simp only [Pi.add_apply, h2, h3]
      map_smul' := by
        intro c W
        have hcongr : secondPrimitive ((c • W : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
            = secondPrimitive (c • (W : ℝ → 𝕜)) :=
          secondPrimitive_congr_ae (Lp.coeFn_smul c W)
        refine Lp.ext ?_
        filter_upwards [coeFn_secondPrimitiveLp (c • W), coeFn_secondPrimitiveLp W,
          Lp.coeFn_smul c (secondPrimitiveLp W)] with t h1 h2 h3
        simp only [RingHom.id_apply]
        rw [h1, h3, hcongr, secondPrimitive_smul]
        simp only [Pi.smul_apply, smul_eq_mul, h2] }
    1
    (fun W => by simpa using norm_secondPrimitiveLp_le W)

/-- The defining almost-everywhere identity of the bundled operator. -/
theorem coeFn_secondPrimitiveCLM (W : Lp 𝕜 2 unitIocMeasure) :
    (secondPrimitiveCLM W : ℝ → 𝕜) =ᵐ[unitIocMeasure] secondPrimitive (W : ℝ → 𝕜) :=
  coeFn_secondPrimitiveLp W

/-! ## Evaluation functionals and cell indicators -/

/-- Evaluation of the second primitive at a point, as a continuous linear functional. -/
def secondPrimitiveEval (x : ℝ) : Lp 𝕜 2 unitIocMeasure →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun W => secondPrimitive (W : ℝ → 𝕜) x
      map_add' := by
        intro W V
        have hcongr : secondPrimitive ((W + V : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
            = secondPrimitive ((W : ℝ → 𝕜) + (V : ℝ → 𝕜)) :=
          secondPrimitive_congr_ae (Lp.coeFn_add W V)
        rw [hcongr, secondPrimitive_add (integrable_coeFn W) (integrable_coeFn V)]
        rfl
      map_smul' := by
        intro c W
        have hcongr : secondPrimitive ((c • W : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
            = secondPrimitive (c • (W : ℝ → 𝕜)) :=
          secondPrimitive_congr_ae (Lp.coeFn_smul c W)
        rw [hcongr, secondPrimitive_smul]
        rfl }
    (|x| + 1)
    (fun W => by
      change ‖secondPrimitive ((W : ℝ → 𝕜)) x‖ ≤ (|x| + 1) * ‖W‖
      have hker : ∀ᵐ s ∂unitIocMeasure,
          ‖(secondPrimitiveKernel x s : 𝕜) * (W : ℝ → 𝕜) s‖
            ≤ (|x| + 1) * ‖(W : ℝ → 𝕜) s‖ := by
        filter_upwards [ae_mem_unitIocMeasure] with s hs
        rw [norm_mul, RCLike.norm_ofReal,
          abs_of_nonneg (secondPrimitiveKernel_nonneg x s)]
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (secondPrimitiveKernel_le_abs hs.1.le).trans (by linarith)
      rw [secondPrimitive_def]
      calc ‖∫ s, (secondPrimitiveKernel x s : 𝕜) * (W : ℝ → 𝕜) s ∂unitIocMeasure‖
          ≤ ∫ s, ‖(secondPrimitiveKernel x s : 𝕜) * (W : ℝ → 𝕜) s‖ ∂unitIocMeasure :=
            MeasureTheory.norm_integral_le_integral_norm _
        _ ≤ ∫ s, (|x| + 1) * ‖(W : ℝ → 𝕜) s‖ ∂unitIocMeasure := by
            refine integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun s => norm_nonneg _)
              ((integrable_coeFn W).norm.const_mul _) hker
        _ = (|x| + 1) * ∫ s, ‖(W : ℝ → 𝕜) s‖ ∂unitIocMeasure := integral_const_mul _ _
        _ ≤ (|x| + 1) * ‖W‖ := by
            refine mul_le_mul_of_nonneg_left (integral_norm_coeFn_le W) ?_
            positivity)

/-- Applying the evaluation functional. -/
@[simp] theorem secondPrimitiveEval_apply (x : ℝ) (W : Lp 𝕜 2 unitIocMeasure) :
    secondPrimitiveEval x W = secondPrimitive (W : ℝ → 𝕜) x := by
  unfold secondPrimitiveEval
  rfl

/-- The partition cell `(i/(n+1), (i+1)/(n+1)]`. -/
def partitionCell (n i : ℕ) : Set ℝ :=
  Set.Ioc ((i : ℝ) / (n + 1)) (((i : ℝ) + 1) / (n + 1))

/-- The partition cells are measurable. -/
theorem measurableSet_partitionCell (n i : ℕ) : MeasurableSet (partitionCell n i) :=
  measurableSet_Ioc

/-- The indicator of a partition cell as an `L²` element. -/
def cellIndicatorLp (n i : ℕ) : Lp 𝕜 2 unitIocMeasure :=
  indicatorConstLp 2 (measurableSet_partitionCell n i) (measure_ne_top _ _) (1 : 𝕜)

/-- The finite-rank snapshot of the second-primitive operator on `n+1` cells. -/
def secondPrimitiveApprox (n : ℕ) :
    Lp 𝕜 2 unitIocMeasure →L[𝕜] Lp 𝕜 2 unitIocMeasure :=
  ∑ i ∈ Finset.range (n + 1),
    (secondPrimitiveEval ((i : ℝ) / (n + 1))).smulRight (cellIndicatorLp n i)

/-- A rank-one operator is compact. -/
theorem isCompactOperator_smulRight {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (φ : E →L[𝕜] 𝕜) (v : F) : IsCompactOperator (φ.smulRight v) := by
  have hle : LinearMap.range ((φ.smulRight v : E →L[𝕜] F) : E →ₗ[𝕜] F)
      ≤ Submodule.span 𝕜 {v} := by
    rintro y ⟨x, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  have : FiniteDimensional 𝕜
      (LinearMap.range ((φ.smulRight v : E →L[𝕜] F) : E →ₗ[𝕜] F)) :=
    Submodule.finiteDimensional_of_le hle
  exact ContinuousLinearMap.isCompactOperator_of_finiteDimensional_range _

/-- Finite sums of compact operators are compact. -/
theorem isCompactOperator_finsetSum {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (s : Finset ι) (f : ι → (E →L[𝕜] F))
    (h : ∀ i ∈ s, IsCompactOperator (f i)) :
    IsCompactOperator (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    have hz : IsCompactOperator (0 : E → F) := isCompactOperator_zero
    simpa using hz
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have h1 : IsCompactOperator (f a) := h a (Finset.mem_insert_self a s)
    have h2 : IsCompactOperator (∑ i ∈ s, f i) :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have := h1.add h2
    simpa using this
-- Unifying the rank-one summands against the finite-sum compactness lemma is slower at a
-- general `RCLike` scalar than it was at the fixed complex field.
/-- Every snapshot is compact. -/
theorem isCompactOperator_secondPrimitiveApprox (n : ℕ) :
    IsCompactOperator (secondPrimitiveApprox (𝕜 := 𝕜) n) := by
  unfold secondPrimitiveApprox
  rw [FunLike.coe_sum]
  exact isCompactOperator_finsetSum (Finset.range (n + 1))
    (fun i => (secondPrimitiveEval (𝕜 := 𝕜) ((i : ℝ) / (n + 1))).smulRight
      (cellIndicatorLp (𝕜 := 𝕜) n i))
    (fun i _ => isCompactOperator_smulRight _ _)

/-! ## The partition lemma and the approximation estimate -/

/-- Every point of `(0,1]` lies in exactly one partition cell. -/
theorem exists_unique_partitionCell (n : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    ∃ j ∈ Finset.range (n + 1), t ∈ partitionCell n j ∧
      ∀ i ∈ Finset.range (n + 1), i ≠ j → t ∉ partitionCell n i := by
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have htm0 : 0 < t * ((n : ℝ) + 1) := mul_pos ht.1 hm
  have htm1 : t * ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    calc t * ((n : ℝ) + 1) ≤ 1 * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right ht.2 hm.le
      _ = (n : ℝ) + 1 := one_mul _
  set c : ℤ := ⌈t * ((n : ℝ) + 1)⌉ with hcdef
  have hc1 : 1 ≤ c := by
    rw [hcdef]
    exact Int.ceil_pos.mpr htm0
  have hcn : c ≤ (n : ℤ) + 1 := by
    rw [hcdef]
    refine Int.ceil_le.mpr ?_
    push_cast
    exact htm1
  set j : ℕ := (c - 1).toNat with hjdef
  have hjz : (j : ℤ) = c - 1 := by
    rw [hjdef]
    exact Int.toNat_of_nonneg (by omega)
  have hjr : (j : ℝ) = (c : ℝ) - 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) hjz
  have hjmem : j ∈ Finset.range (n + 1) := by
    rw [Finset.mem_range]
    omega
  have hcell : t ∈ partitionCell n j := by
    unfold partitionCell
    constructor
    · rw [div_lt_iff₀ hm, hjr]
      have := Int.ceil_lt_add_one (t * ((n : ℝ) + 1))
      rw [← hcdef] at this
      linarith
    · rw [le_div_iff₀ hm, hjr]
      have := Int.le_ceil (t * ((n : ℝ) + 1))
      rw [← hcdef] at this
      linarith
  refine ⟨j, hjmem, hcell, ?_⟩
  intro i _ hij hti
  apply hij
  have h1 : (i : ℝ) < t * ((n : ℝ) + 1) := by
    have := hti.1
    rwa [div_lt_iff₀ hm] at this
  have h2 : t * ((n : ℝ) + 1) ≤ (i : ℝ) + 1 := by
    have := hti.2
    rwa [le_div_iff₀ hm] at this
  have hceq : c = (i : ℤ) + 1 := by
    rw [hcdef, Int.ceil_eq_iff]
    constructor
    · push_cast
      linarith
    · push_cast
      linarith
  omega

/-- Coefficient functions of a finite sum of `L²` elements. -/
theorem coeFn_lp_finsetSum {ι : Type*} (s : Finset ι) (f : ι → Lp 𝕜 2 unitIocMeasure) :
    ((∑ i ∈ s, f i : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
      =ᵐ[unitIocMeasure] fun t => ∑ i ∈ s, (f i : ℝ → 𝕜) t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero 𝕜 2 unitIocMeasure] with t ht
    exact ht
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with t h1 h2
    rw [h1]
    simp only [Pi.add_apply, h2]
    rw [Finset.sum_insert ha]

/-- Almost-everywhere estimate: the `n`-cell snapshot is within `‖W‖/(n+1)` of the second
primitive, pointwise. -/
theorem ae_norm_secondPrimitive_sub_approx_le (n : ℕ) (W : Lp 𝕜 2 unitIocMeasure) :
    ∀ᵐ t ∂unitIocMeasure,
      ‖secondPrimitive (W : ℝ → 𝕜) t - ((secondPrimitiveApprox n W : Lp 𝕜 2 unitIocMeasure)
          : ℝ → 𝕜) t‖ ≤ (1 / ((n : ℝ) + 1)) * ‖W‖ := by
  have hsum : (secondPrimitiveApprox n W : Lp 𝕜 2 unitIocMeasure)
      = ∑ i ∈ Finset.range (n + 1),
          secondPrimitiveEval ((i : ℝ) / (n + 1)) W • cellIndicatorLp n i := by
    unfold secondPrimitiveApprox
    rw [sum_apply]
    exact Finset.sum_congr rfl fun i _ => rfl
  have hindMeas : ∀ i : ℕ,
      ((cellIndicatorLp n i : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜)
        =ᵐ[unitIocMeasure] (partitionCell n i).indicator fun _ => (1 : 𝕜) :=
    fun i => indicatorConstLp_coeFn
  have hsmul : ∀ᵐ t ∂unitIocMeasure, ∀ i : ℕ,
      ((secondPrimitiveEval ((i : ℝ) / (n + 1)) W • cellIndicatorLp n i
          : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜) t
        = secondPrimitiveEval ((i : ℝ) / (n + 1)) W
            * (partitionCell n i).indicator (fun _ => (1 : 𝕜)) t := by
    rw [MeasureTheory.ae_all_iff]
    intro i
    filter_upwards [Lp.coeFn_smul (secondPrimitiveEval ((i : ℝ) / (n + 1)) W)
      (cellIndicatorLp (𝕜 := 𝕜) n i), hindMeas i] with t h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
  rw [hsum]
  filter_upwards [ae_mem_unitIocMeasure, coeFn_lp_finsetSum (Finset.range (n + 1))
      (fun i => secondPrimitiveEval ((i : ℝ) / (n + 1)) W • cellIndicatorLp (𝕜 := 𝕜) n i),
    hsmul] with t htIoc hcoe hval
  rw [hcoe]
  obtain ⟨j, hjmem, hjcell, hjuniq⟩ := exists_unique_partitionCell n htIoc
  have hcollapse : (∑ i ∈ Finset.range (n + 1),
      ((secondPrimitiveEval ((i : ℝ) / (n + 1)) W • cellIndicatorLp n i
          : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜) t)
      = secondPrimitive (W : ℝ → 𝕜) ((j : ℝ) / (n + 1)) := by
    calc (∑ i ∈ Finset.range (n + 1),
        ((secondPrimitiveEval ((i : ℝ) / (n + 1)) W • cellIndicatorLp n i
            : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜) t)
        = ∑ i ∈ Finset.range (n + 1),
            secondPrimitiveEval ((i : ℝ) / (n + 1)) W
              * (partitionCell n i).indicator (fun _ => (1 : 𝕜)) t :=
          Finset.sum_congr rfl fun i _ => hval i
      _ = secondPrimitiveEval ((j : ℝ) / (n + 1)) W
            * (partitionCell n j).indicator (fun _ => (1 : 𝕜)) t :=
          Finset.sum_eq_single_of_mem j hjmem fun i hi hij => by
            rw [Set.indicator_of_notMem (hjuniq i hi hij), mul_zero]
      _ = secondPrimitive (W : ℝ → 𝕜) ((j : ℝ) / (n + 1)) := by
          rw [Set.indicator_of_mem hjcell, mul_one, secondPrimitiveEval_apply]
  rw [hcollapse]
  have hm : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdist : |t - (j : ℝ) / (n + 1)| ≤ 1 / ((n : ℝ) + 1) := by
    have h1 : (j : ℝ) / (n + 1) < t := hjcell.1
    have h2 : t ≤ ((j : ℝ) + 1) / (n + 1) := hjcell.2
    rw [abs_of_nonneg (by linarith)]
    have : ((j : ℝ) + 1) / (n + 1) - (j : ℝ) / (n + 1) = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    linarith
  calc ‖secondPrimitive (W : ℝ → 𝕜) t - secondPrimitive (W : ℝ → 𝕜) ((j : ℝ) / (n + 1))‖
      ≤ |t - (j : ℝ) / (n + 1)| * ∫ s, ‖(W : ℝ → 𝕜) s‖ ∂unitIocMeasure :=
        norm_secondPrimitive_sub_le (integrable_coeFn W) _ _
    _ ≤ (1 / ((n : ℝ) + 1)) * ‖W‖ := by
        refine mul_le_mul hdist (integral_norm_coeFn_le W) ?_ ?_
        · exact integral_nonneg fun s => norm_nonneg _
        · positivity

/-- Operator-norm estimate for the snapshots. -/
theorem norm_secondPrimitiveApprox_sub_le (n : ℕ) :
    ‖secondPrimitiveApprox (𝕜 := 𝕜) n - secondPrimitiveCLM‖ ≤ 1 / ((n : ℝ) + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun W => ?_
  rw [sub_apply]
  have hae : ∀ᵐ t ∂unitIocMeasure,
      ‖((secondPrimitiveApprox n W - secondPrimitiveCLM W : Lp 𝕜 2 unitIocMeasure)
          : ℝ → 𝕜) t‖ ≤ (1 / ((n : ℝ) + 1)) * ‖W‖ := by
    filter_upwards [Lp.coeFn_sub (secondPrimitiveApprox n W) (secondPrimitiveCLM W),
      coeFn_secondPrimitiveCLM W, ae_norm_secondPrimitive_sub_approx_le n W]
      with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, norm_sub_rev]
    exact h3
  have hb := eLpNorm_le_of_ae_bound (p := 2) hae
  rw [measure_univ, ENNReal.one_rpow, one_mul] at hb
  rw [Lp.norm_def]
  calc (eLpNorm ((secondPrimitiveApprox n W - secondPrimitiveCLM W
          : Lp 𝕜 2 unitIocMeasure) : ℝ → 𝕜) 2 unitIocMeasure).toReal
      ≤ (ENNReal.ofReal ((1 / ((n : ℝ) + 1)) * ‖W‖)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
    _ = (1 / ((n : ℝ) + 1)) * ‖W‖ := ENNReal.toReal_ofReal (by positivity)

/-- **The second-primitive operator is compact**: it is the operator-norm limit of the
finite-rank cell snapshots. -/
theorem isCompactOperator_secondPrimitiveCLM :
    IsCompactOperator (secondPrimitiveCLM (𝕜 := 𝕜)) := by
  have htend : Filter.Tendsto (fun n : ℕ => secondPrimitiveApprox (𝕜 := 𝕜) n)
      Filter.atTop (nhds secondPrimitiveCLM) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _)
      (fun n => norm_secondPrimitiveApprox_sub_le n) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  exact isCompactOperator_of_tendsto htend
    (Filter.Eventually.of_forall (isCompactOperator_secondPrimitiveApprox (𝕜 := 𝕜)))

end

end TauCeti
