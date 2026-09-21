/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryVerySmallOperator
import LeanPool.QuadraticCarleson.QuadraticCarleson.CanonicalScaleAtomIntegrals
import LeanPool.QuadraticCarleson.QuadraticCarleson.FiniteModulationKernelComparison
import LeanPool.QuadraticCarleson.QuadraticCarleson.QuadraticHilbertMaximalMeasurable

/-!
# Genuine inputs for the lacunary middle-range argument

This module realizes the three functions occurring in source lines 636--648:
the actual middle-scale input, its frozen `R_{k,τ}` replacement, and the
signed error.  It proves their exact algebraic recombination and the
disjoint-scale `L¹` packing needed before the finite-modulation estimate and
Kalton log-convexity are applied.
-/

open Function MeasureTheory Set
open scoped ENNReal BigOperators

namespace QuadraticCarleson
namespace LacunaryMiddleOperator

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open CalderonZygmundLevelAtoms
open CanonicalScaleAtoms LacunaryMiddleRange LacunaryMiddleRangeSummation
open LacunaryLowSupport LacunaryVerySmallOperator PositiveEndpointOptimization
open LowKernelLevelSummation PositiveLowFullEstimate
open QuadraticHilbertMaximalMeasurable


noncomputable section

/-- The genuine scale-sliced input `∑_{j∈S_{k,m}} b_{j,k}`. -/
def middleRangeInput
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m : ℤ) (x : ℝ) : ℂ :=
  ∑ j ∈ S B c m, stoppingScaleLevelBadPart A f j k x

/-- The frozen input `∑_{j∈R_{k,τ}} b_{j,k}` used throughout one
modulation block. -/
def frozenBlockInput
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) (x : ℝ) : ℂ :=
  ∑ j ∈ R B c τ, stoppingScaleLevelBadPart A f j k x

/-- The paper's signed error
`-∑_{j∈R_{k,τ}\S_{k,m}} b_{j,k}`. -/
def frozenBlockErrorInput
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ m : ℤ) (x : ℝ) : ℂ :=
  -∑ j ∈ R B c τ \ S B c m,
    stoppingScaleLevelBadPart A f j k x

/-- Exact source identity
`∑_{j∈S} b_{j,k} = ∑_{j∈R} b_{j,k} + Err`. -/
theorem middleRangeInput_eq_frozenBlockInput_add_error
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) {τ m : ℤ}
    (hm : m ∈ Q B τ) (x : ℝ) :
    middleRangeInput A f k B c m x =
      frozenBlockInput A f k B c τ x +
        frozenBlockErrorInput A f k B c τ m x := by
  unfold middleRangeInput frozenBlockInput frozenBlockErrorInput
  have hsub : S B c m ⊆ R B c τ := S_subset_R hm
  rw [← Finset.sum_sdiff hsub]
  ring

theorem measurable_middleRangeInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (m : ℤ) :
    Measurable (middleRangeInput A f k B c m) := by
  unfold middleRangeInput
  exact Finset.measurable_fun_sum (S B c m) fun j _ ↦
    measurable_stoppingScaleLevelBadPart hf j k

theorem measurable_frozenBlockInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (τ : ℤ) :
    Measurable (frozenBlockInput A f k B c τ) := by
  unfold frozenBlockInput
  exact Finset.measurable_fun_sum (R B c τ) fun j _ ↦
    measurable_stoppingScaleLevelBadPart hf j k

theorem measurable_frozenBlockErrorInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (τ m : ℤ) :
    Measurable (frozenBlockErrorInput A f k B c τ m) := by
  unfold frozenBlockErrorInput
  exact (Finset.measurable_fun_sum (R B c τ \ S B c m) fun j _ ↦
    measurable_stoppingScaleLevelBadPart hf j k).neg

theorem integrable_middleRangeInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (m : ℤ) :
    Integrable (middleRangeInput A f k B c m) := by
  unfold middleRangeInput
  exact integrable_finsetSum _ fun j _ ↦
    integrable_stoppingScaleLevelBadPart hf hfi j hAk

theorem integrable_frozenBlockInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ) :
    Integrable (frozenBlockInput A f k B c τ) := by
  unfold frozenBlockInput
  exact integrable_finsetSum _ fun j _ ↦
    integrable_stoppingScaleLevelBadPart hf hfi j hAk

theorem integrable_frozenBlockErrorInput
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ m : ℤ) :
    Integrable (frozenBlockErrorInput A f k B c τ m) := by
  unfold frozenBlockErrorInput
  exact (integrable_finsetSum _ fun j _ ↦
    integrable_stoppingScaleLevelBadPart hf hfi j hAk).neg

/-- The actual low-kernel action on the middle-scale input. -/
def middleRangeLowAction
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (m : ℤ) (x : ℝ) : ℂ :=
  ∫ y, paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
    middleRangeInput A f k B c m y

/-- The low-kernel action on the input frozen over a modulation block. -/
def frozenBlockLowAction
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ m : ℤ) (x : ℝ) : ℂ :=
  ∫ y, paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
    frozenBlockInput A f k B c τ y

/-- The low-kernel action on the signed frozen-range error. -/
def frozenBlockErrorLowAction
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ m : ℤ) (x : ℝ) : ℂ :=
  ∫ y, paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
    frozenBlockErrorInput A f k B c τ m y

/-- The genuine finite maximum over all dyadic modulations in the paper's
block `Q_τ`.  The empty-block value is canonically zero. -/
noncomputable def frozenBlockMaxEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) (x : ℝ) : ENNReal :=
  (Q B τ).sup fun m ↦ ‖frozenBlockLowAction A f k B c τ m x‖ₑ

/-- The finite modulation-block maximum of the genuinely maximally
truncated quadratic Hilbert transforms acting on the frozen input. -/
noncomputable def frozenBlockHilbertMaxEnorm
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) (x : ℝ) : ENNReal :=
  (Q B τ).sup fun m ↦
    quadraticHilbertMaximalTruncation (dyadicModulation m)
      (frozenBlockInput A f k B c τ) x

theorem measurable_frozenBlockLowAction
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (τ m : ℤ) :
    Measurable (frozenBlockLowAction A f k B c τ m) := by
  have hjoint : Measurable (fun p : ℝ × ℝ ↦
      paperLowCZKernel
          (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2 *
        frozenBlockInput A f k B c τ p.2) := by
    have hK : Measurable (fun p : ℝ × ℝ ↦
        paperLowCZKernel
          (dyadicModulation m) (dyadicModulation_pos m).ne' B p.1 p.2) :=
      (continuous_paperLowOscillatoryKernel
          (dyadicModulation_pos m).ne' B).measurable.comp
        (measurable_fst.sub measurable_snd)
    exact hK.mul ((measurable_frozenBlockInput hf k B c τ).comp measurable_snd)
  exact hjoint.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_frozenBlockMaxEnorm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (τ : ℤ) :
    Measurable (frozenBlockMaxEnorm A f k B c τ) := by
  have hterm (m : ℤ) : Measurable fun x : ℝ ↦
      ‖frozenBlockLowAction A f k B c τ m x‖ₑ :=
    (measurable_frozenBlockLowAction hf k B c τ m).enorm
  have hsup (s : Finset ℤ) : Measurable fun x : ℝ ↦
      s.sup fun m ↦ ‖frozenBlockLowAction A f k B c τ m x‖ₑ := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sup_empty] using
        (measurable_const : Measurable fun _ : ℝ ↦ (⊥ : ENNReal))
    | @insert m s hm ih =>
      simp only [Finset.sup_insert]
      exact (hterm m).sup ih
  exact hsup (Q B τ)

theorem measurable_frozenBlockHilbertMaxEnorm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ) :
    Measurable (frozenBlockHilbertMaxEnorm A f k B c τ) := by
  have hfm := measurable_frozenBlockInput (A := A) hf k B c τ
  have hfi' := integrable_frozenBlockInput (A := A) hf hfi hAk B c τ
  have hterm (m : ℤ) : Measurable fun x : ℝ ↦
      quadraticHilbertMaximalTruncation (dyadicModulation m)
        (frozenBlockInput A f k B c τ) x :=
    measurable_quadraticHilbertMaximalTruncation
      (dyadicModulation m) hfm hfi'
  have hsup (s : Finset ℤ) : Measurable fun x : ℝ ↦
      s.sup fun m ↦ quadraticHilbertMaximalTruncation (dyadicModulation m)
        (frozenBlockInput A f k B c τ) x := by
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sup_empty] using
        (measurable_const : Measurable fun _ : ℝ ↦ (⊥ : ENNReal))
    | @insert m s hm ih =>
      simp only [Finset.sup_insert]
      exact (hterm m).sup ih
  exact hsup (Q B τ)

/-- Every genuine output in a modulation block is bounded by that block's
finite maximum. -/
theorem frozenBlockLowAction_enorm_le_max
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) {τ m : ℤ}
    (hm : m ∈ Q B τ) (x : ℝ) :
    ‖frozenBlockLowAction A f k B c τ m x‖ₑ ≤
      frozenBlockMaxEnorm A f k B c τ x := by
  exact Finset.le_sup (f := fun m : ℤ ↦
    ‖frozenBlockLowAction A f k B c τ m x‖ₑ) hm

/-- One frozen low-kernel output is controlled by the corresponding
maximally truncated quadratic Hilbert transform plus the elementary
Hardy--Littlewood boundary term.  This is the exact analytic reduction used
before the finite-modulation sparse estimate in the paper. -/
theorem frozenBlockLowAction_enorm_le_hilbertMax_add_maximal
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ m : ℤ) (x : ℝ) :
    ‖frozenBlockLowAction A f k B c τ m x‖ₑ ≤
      2 * quadraticHilbertMaximalTruncation (dyadicModulation m)
          (frozenBlockInput A f k B c τ) x +
        16 * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖frozenBlockInput A f k B c τ y‖ₑ) x := by
  have hfm := measurable_frozenBlockInput (A := A) hf k B c τ
  have hfi' := integrable_frozenBlockInput (A := A) hf hfi hAk B c τ
  have h := finiteQuadraticDyadicBlock_enorm_le_maximalTruncation_add_maximal
    (dyadicModulation m)
    (oscillatoryScaleIndex (dyadicModulation m) 0 (dyadicModulation_pos m).ne')
    B hfm hfi' x
  simpa only [frozenBlockLowAction, paperLowCZKernel, finiteQuadraticDyadicBlock,
    paperLowOscillatoryKernel_eq_consecutive] using h

/-- Taking the finite maximum over the whole modulation block preserves the
same comparison, with a single Hardy--Littlewood term. -/
theorem frozenBlockMaxEnorm_le_hilbertMax_add_maximal
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ : ℤ) (x : ℝ) :
    frozenBlockMaxEnorm A f k B c τ x ≤
      2 * frozenBlockHilbertMaxEnorm A f k B c τ x +
        16 * centeredHardyLittlewoodMaximal
          (fun y ↦ ‖frozenBlockInput A f k B c τ y‖ₑ) x := by
  apply Finset.sup_le
  intro m hm
  apply (frozenBlockLowAction_enorm_le_hilbertMax_add_maximal
    hf hfi hAk B c τ m x).trans
  gcongr
  exact Finset.le_sup (s := Q B τ)
    (f := fun n : ℤ ↦ quadraticHilbertMaximalTruncation (dyadicModulation n)
      (frozenBlockInput A f k B c τ) x) hm

/-- Applying the genuine low kernel preserves the exact frozen-range
recombination identity. -/
theorem middleRangeLowAction_eq_frozenBlockLowAction_add_error
    (A : ℕ → ℝ) {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) {τ m : ℤ}
    (hm : m ∈ Q B τ) (x : ℝ) :
    middleRangeLowAction A f k B c m x =
      frozenBlockLowAction A f k B c τ m x +
        frozenBlockErrorLowAction A f k B c τ m x := by
  have hK : AEStronglyMeasurable (fun y ↦ paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y) :=
    ((continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂volume,
      ‖paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y‖ ≤
          8 * Real.sqrt |dyadicModulation m| := Filter.Eventually.of_forall fun y ↦ by
    simpa only [paperLowCZKernel] using
      paperLowOscillatoryKernel_norm_le_global
        (dyadicModulation_pos m).ne' B (x - y)
  have hFrozen := (integrable_frozenBlockInput hf hfi hAk B c τ).bdd_mul hK hbound
  have hError := (integrable_frozenBlockErrorInput hf hfi hAk B c τ m).bdd_mul hK hbound
  unfold middleRangeLowAction frozenBlockLowAction frozenBlockErrorLowAction
  simp_rw [middleRangeInput_eq_frozenBlockInput_add_error A f k B c hm]
  rw [← integral_add hFrozen hError]
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- A canonical scale in the too-large alternative has identically zero
low-kernel action outside the global fivefold stopping set. -/
theorem canonicalScaleLowAction_eq_zero_of_tooLarge
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k B c : ℕ} (hAk : 0 ≤ A k) {m j : ℤ}
    (hlarge : (c : ℤ) + 2 * (B : ℤ) < m + 2 * j)
    {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength) :
    (∫ y, paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y) = 0 := by
  rw [integral_paperLowCZKernel_stoppingScaleLevelBadPart_eq_tsum_cells
    hf hfi hAk]
  have hzero (I : {I : stoppingCell f //
      I ∈ dyadicAtomScaleClass (stoppingLength (f := f)) j}) :
      (∫ y in centeredInterval (stoppingCenter I.1) (stoppingLength I.1),
        paperLowCZKernel
            (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          levelAtom A f k (stoppingCenter I.1) (stoppingLength I.1) y) = 0 := by
    rw [← integral_paperLowCZKernel_mul_levelAtom_eq_setIntegral
      (dyadicModulation_pos m).ne' B k
        (stoppingCenter I.1) (stoppingLength I.1) x]
    apply integral_paperLowCZKernel_mul_levelAtom_eq_zero_of_tooLarge
      k B c m j hlarge (stoppingLength_pos I.1) I.2.1
    intro hxI
    exact hx (mem_iUnion.mpr ⟨I.1, hxI⟩)
  simp only [hzero, tsum_zero]

/-- The genuine action on the signed error is the negative finite sum of
the genuine scale actions. -/
theorem frozenBlockErrorLowAction_eq_neg_sum
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) (B c : ℕ) (τ m : ℤ) (x : ℝ) :
    frozenBlockErrorLowAction A f k B c τ m x =
      -∑ j ∈ R B c τ \ S B c m,
        ∫ y, paperLowCZKernel
            (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
          stoppingScaleLevelBadPart A f j k y := by
  have hK : AEStronglyMeasurable (fun y ↦ paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y) :=
    ((continuous_paperLowOscillatoryKernel (dyadicModulation_pos m).ne' B).measurable.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hbound : ∀ᵐ y ∂volume,
      ‖paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y‖ ≤
          8 * Real.sqrt |dyadicModulation m| := Filter.Eventually.of_forall fun y ↦ by
    simpa only [paperLowCZKernel] using
      paperLowOscillatoryKernel_norm_le_global
        (dyadicModulation_pos m).ne' B (x - y)
  have hi (j : ℤ) : Integrable (fun y ↦ paperLowCZKernel
      (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
        stoppingScaleLevelBadPart A f j k y) :=
    (integrable_stoppingScaleLevelBadPart hf hfi j hAk).bdd_mul hK hbound
  unfold frozenBlockErrorLowAction frozenBlockErrorInput
  simp_rw [mul_neg, Finset.mul_sum]
  rw [integral_neg]
  congr 1
  rw [integral_finsetSum]
  intro j _
  exact hi j

/-- Pointwise, the whole frozen-range error outside the exceptional set is
dominated by the genuine very-small triangle majorant at that magnitude
level. The too-large alternative has disappeared exactly by support. -/
theorem enorm_frozenBlockErrorLowAction_le_verySmall
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {k : ℕ} (hAk : 0 ≤ A k) {B c : ℕ} {τ m : ℤ}
    {x : ℝ}
    (hx : x ∉ fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength) :
    ‖frozenBlockErrorLowAction A f k B c τ m x‖ₑ ≤
      verySmallLowContributionAtLevel A f k B c x := by
  rw [frozenBlockErrorLowAction_eq_neg_sum hf hfi hAk B c τ m x, enorm_neg]
  let D : Finset ℤ := R B c τ \ S B c m
  let u : ℤ → ℂ := fun j ↦
    ∫ y, paperLowCZKernel
        (dyadicModulation m) (dyadicModulation_pos m).ne' B x y *
      stoppingScaleLevelBadPart A f j k y
  have hterm : ∀ j ∈ D,
      ‖u j‖ₑ ≤ restrictedCanonicalScaleLowActionEnorm A f k B c m j x := by
    intro j hj
    rcases mem_R_sdiff_S_imp_mem_L_or_tooLarge hj with hsmall | hlarge
    · simp [u, restrictedCanonicalScaleLowActionEnorm,
        canonicalScaleLowActionEnorm, hsmall]
    · have hz : u j = 0 := by
        exact canonicalScaleLowAction_eq_zero_of_tooLarge
          hf hfi hAk hlarge hx
      rw [hz, enorm_zero]
      exact bot_le
  calc
    ‖∑ j ∈ D, u j‖ₑ ≤ ∑ j ∈ D, ‖u j‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ j ∈ D,
        restrictedCanonicalScaleLowActionEnorm A f k B c m j x :=
      Finset.sum_le_sum hterm
    _ ≤ ∑' j : ℤ,
        restrictedCanonicalScaleLowActionEnorm A f k B c m j x :=
      ENNReal.summable.sum_le_tsum D (fun _ _ ↦ bot_le)
    _ ≤ ∑' m' : ℤ, ∑' j : ℤ,
        restrictedCanonicalScaleLowActionEnorm A f k B c m' j x :=
      ENNReal.le_tsum m
    _ = verySmallLowContributionAtLevel A f k B c x := rfl

/-- `L¹` mass of one genuine frozen block input. -/
def frozenBlockInputL1Mass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (τ : ℤ) : ENNReal :=
  ∫⁻ x, ‖frozenBlockInput A f k B c τ x‖ₑ

/-- Triangle inequality for one frozen block, before sparse packing. -/
theorem frozenBlockInputL1Mass_le_scale_sum
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    (k B c : ℕ) (τ : ℤ) :
    frozenBlockInputL1Mass A f k B c τ ≤
      ∑ j ∈ R B c τ,
        ∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ := by
  unfold frozenBlockInputL1Mass frozenBlockInput
  calc
    (∫⁻ x, ‖∑ j ∈ R B c τ,
        stoppingScaleLevelBadPart A f j k x‖ₑ) ≤
        ∫⁻ x, ∑ j ∈ R B c τ,
          ‖stoppingScaleLevelBadPart A f j k x‖ₑ := by
      apply lintegral_mono
      intro x
      exact enorm_sum_le _ _
    _ = ∑ j ∈ R B c τ,
        ∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ := by
      rw [lintegral_finsetSum]
      intro j _
      exact (measurable_stoppingScaleLevelBadPart hf j k).enorm

/-- Frozen block mass retained on one of the paper's sparse residue classes. -/
def sparseFrozenBlockInputL1Mass
    (A : ℕ → ℝ) (f : ℝ → ℂ) (k B c : ℕ) (ρ τ : ℤ) : ENNReal :=
  if τ ≡ ρ [ZMOD sparseModulus] then
    frozenBlockInputL1Mass A f k B c τ else 0

/-- The disjoint frozen scale ranges in a fixed sparse residue class lose no
mass beyond the standard factor two from the centered atoms. -/
theorem tsum_sparseFrozenBlockInputL1Mass_le_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k B c : ℕ} (hAk : 0 ≤ A k) (hB : 0 < B) (hc : 2 * c ≤ 5 * B)
    (ρ : ℤ) :
    (∑' τ : ℤ, sparseFrozenBlockInputL1Mass A f k B c ρ τ) ≤
      2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k := by
  let a : ℤ → ENNReal := fun j ↦
    ∫⁻ x, ‖stoppingScaleLevelBadPart A f j k x‖ₑ
  have hterm : ∀ τ : ℤ,
      sparseFrozenBlockInputL1Mass A f k B c ρ τ ≤
        sparseBlockMass B c ρ a τ := by
    intro τ
    by_cases hτρ : τ ≡ ρ [ZMOD sparseModulus]
    · simp only [sparseFrozenBlockInputL1Mass, sparseBlockMass, hτρ, if_true]
      exact frozenBlockInputL1Mass_le_scale_sum hf k B c τ
    · simp [sparseFrozenBlockInputL1Mass, sparseBlockMass, hτρ]
  calc
    (∑' τ : ℤ, sparseFrozenBlockInputL1Mass A f k B c ρ τ) ≤
        ∑' τ : ℤ, sparseBlockMass B c ρ a τ :=
      ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' j : ℤ, a j := tsum_sparseBlockMass_le B c hB hc ρ a
    _ = ∫⁻ x, ‖canonicalLevelBadPart A f k x‖ₑ := by
      exact tsum_lintegral_enorm_stoppingScaleLevelBadPart hf k
    _ ≤ 2 * PositiveLevelIntegration.magnitudeLevelL1Mass volume A f k :=
      lintegral_enorm_canonicalLevelBadPart_le hf hAk


end
end LacunaryMiddleOperator
end QuadraticCarleson
