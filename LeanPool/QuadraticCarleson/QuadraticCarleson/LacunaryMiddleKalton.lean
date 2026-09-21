/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryMiddleOperator
import LeanPool.QuadraticCarleson.QuadraticCarleson.KaltonPaperApplication
import LeanPool.QuadraticCarleson.QuadraticCarleson.LacunaryVerySmallEndpoint

/-!
# Kalton applied to the genuine frozen modulation-block outputs

The functions in this file are the concrete low-kernel actions from
`LacunaryMiddleOperator`, not an abstract family. The only conditional
analytic input is an individual frozen-block weak-L¹ estimate. Countable
suprema, level summation, measurability, and the fivefold exceptional-set
contribution are all discharged here.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace LacunaryMiddleKalton

open CalderonZygmundDyadicStopping CalderonZygmundStoppingIntervals
open PositiveEndpointOptimization PositiveLowFullEstimate
open LacunaryMiddleOperator KaltonPaperApplication LacunaryVerySmallEndpoint


/-- The main frozen-block expression from source lines 652--655, with the
canonical lacunary level atoms and the actual finite modulation maxima. -/
noncomputable def lacunaryFrozenMainOutput
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (x : ℝ) : ℝ≥0∞ :=
  ∑' k : ℕ, ⨆ τ : ℤ, frozenBlockMaxEnorm lacunaryAmplitude f k (B k) c τ x

theorem measurable_lacunaryFrozenMainOutput
    {f : ℝ → ℂ} (hf : Measurable f) (B : ℕ → ℕ) (c : ℕ) :
    Measurable (lacunaryFrozenMainOutput f B c) :=
  measurable_paperBlockOutput fun k τ ↦ measurable_frozenBlockMaxEnorm hf k (B k) c τ

/-- The exact per-block analytic hypothesis; it is imposed only on a single
finite modulation maximum, not on the assembled middle contribution. -/
def HasIndividualFrozenBlockWeakBounds
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (W : ℕ → ℤ → ℝ) : Prop :=
  ∀ k τ, HasExtendedWeakL1Bound
    (volume.restrict (fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength)ᶜ)
    (W k τ) (frozenBlockMaxEnorm lacunaryAmplitude f k (B k) c τ)

/-- All countable assembly is now applied to the genuine frozen outputs.
There is no summability, boundedness, or assembly-identity hypothesis. -/
theorem lacunaryFrozenMainOutput_compl_levelSet_mul_le
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℕ → ℕ} {c : ℕ} {W : ℕ → ℤ → ℝ}
    (hblock : HasIndividualFrozenBlockWeakBounds f B c W)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume
      ({x | ENNReal.ofReal a < lacunaryFrozenMainOutput f B c x} ∩
        (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
      24 * paperBlockBudget W := by
  have h := paperBlockOutput_levelSet_mul_le_budget
    (fun k τ ↦ measurable_frozenBlockMaxEnorm (A := lacunaryAmplitude) hf k (B k) c τ)
    hblock ha
  change ENNReal.ofReal a *
    (volume.restrict (fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength)ᶜ)
      {x | ENNReal.ofReal a < lacunaryFrozenMainOutput f B c x} ≤ _ at h
  rw [Measure.restrict_apply (measurableSet_lt measurable_const
    (measurable_lacunaryFrozenMainOutput hf B c))] at h
  exact h

theorem lacunaryFrozenMainOutput_compl_levelSet_one_le
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℕ → ℕ} {c : ℕ} {W : ℕ → ℤ → ℝ}
    (hblock : HasIndividualFrozenBlockWeakBounds f B c W) :
    volume ({x | 1 < lacunaryFrozenMainOutput f B c x} ∩
      (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
        24 * paperBlockBudget W := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    lacunaryFrozenMainOutput_compl_levelSet_mul_le hf hblock (by norm_num : (0 : ℝ) < 1)

/-- The global normalized bound includes the canonical stopping set with
its proved L¹ cost. -/
theorem lacunaryFrozenMainOutput_levelSet_one_le
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {W : ℕ → ℤ → ℝ}
    (hblock : HasIndividualFrozenBlockWeakBounds f B c W) :
    volume {x | 1 < lacunaryFrozenMainOutput f B c x} ≤
      5 * (∫⁻ x, ‖f x‖ₑ) + 24 * paperBlockBudget W := by
  let E := fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength
  let S := {x | 1 < lacunaryFrozenMainOutput f B c x}
  have hs : S ⊆ E ∪ (S ∩ Eᶜ) := by
    intro x hx
    by_cases he : x ∈ E
    · exact Or.inl he
    · exact Or.inr ⟨hx, he⟩
  exact ((measure_mono hs).trans (measure_union_le _ _)).trans
    (add_le_add (volume_canonicalFivefoldExceptionalSet_le hfi)
      (lacunaryFrozenMainOutput_compl_levelSet_one_le hf hblock))

/-- With a finite weighted budget, finiteness of the genuine level sum on
the exceptional-set complement is a conclusion of Kalton. -/
theorem ae_lacunaryFrozenMainOutput_lt_top_compl
    {f : ℝ → ℂ} (hf : Measurable f) {B : ℕ → ℕ} {c : ℕ} {W : ℕ → ℤ → ℝ}
    (hblock : HasIndividualFrozenBlockWeakBounds f B c W)
    (hbudget : paperBlockBudget W ≠ ∞) :
    ∀ᵐ x ∂volume.restrict (fivefoldExceptionalSet
      (stoppingCenter (f := f)) stoppingLength)ᶜ,
        lacunaryFrozenMainOutput f B c x < ∞ :=
  ae_paperBlockOutput_lt_top
    (fun k τ ↦ measurable_frozenBlockMaxEnorm hf k (B k) c τ) hblock hbudget

/-- The precise remaining finite-modulation estimate: one actual frozen
block has weak constant `C log₁(B_k)² ‖frozenBlockInput‖₁` on the canonical
exceptional-set complement. No supremum in `τ` or sum in `k` is assumed here. -/
def HasLogSquaredFrozenBlockWeakBounds
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ (k : ℕ) (τ : ℤ) (a : ℝ), 0 < a →
    ENNReal.ofReal a *
      (volume.restrict (fivefoldExceptionalSet
        (stoppingCenter (f := f)) stoppingLength)ᶜ)
        {x | ENNReal.ofReal a < frozenBlockMaxEnorm lacunaryAmplitude f k (B k) c τ x} ≤
      ENNReal.ofReal (C * paperLog 1 (B k : ℝ) ^ 2) *
        frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ

/-- The logarithmic weak-bound constant weighted by the L¹ mass of a frozen block input. -/
noncomputable def frozenBlockLogWeakConstant
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) (C : ℝ) (k : ℕ) (τ : ℤ) : ℝ :=
  (C * paperLog 1 (B k : ℝ) ^ 2) *
    ∫ x, ‖frozenBlockInput lacunaryAmplitude f k (B k) c τ x‖

theorem ofReal_frozenBlockLogWeakConstant
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (B : ℕ → ℕ) (c : ℕ) {C : ℝ} (hC : 0 ≤ C) (k : ℕ) (τ : ℤ) :
    ENNReal.ofReal (frozenBlockLogWeakConstant f B c C k τ) =
      ENNReal.ofReal (C * paperLog 1 (B k : ℝ) ^ 2) *
        frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ := by
  rw [frozenBlockLogWeakConstant, ENNReal.ofReal_mul (mul_nonneg hC (sq_nonneg _)),
    ofReal_integral_norm_eq_lintegral_enorm
      (integrable_frozenBlockInput hf hfi (lacunaryAmplitude_pos k).le (B k) c τ)]
  rfl

theorem individualFrozenBlockWeakBounds_of_logSquared
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f B c C) :
    HasIndividualFrozenBlockWeakBounds f B c (frozenBlockLogWeakConstant f B c C) := by
  intro k τ
  refine ⟨mul_nonneg (mul_nonneg hblock.1 (sq_nonneg _))
    (integral_nonneg fun x ↦ norm_nonneg _), ?_⟩
  intro a ha
  rw [ofReal_frozenBlockLogWeakConstant hf hfi B c hblock.1 k τ]
  exact hblock.2 k τ a ha

/-- The actual weighted frozen-input mass appearing after Kalton. -/
noncomputable def frozenLogSquaredMassBudget
    (f : ℝ → ℂ) (B : ℕ → ℕ) (c : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, ENNReal.ofReal
    (paperLog 1 ((k : ℝ) + 2) * paperLog 1 (B k : ℝ) ^ 2) *
      ∑' τ : ℤ, frozenBlockInputL1Mass lacunaryAmplitude f k (B k) c τ

theorem paperBlockBudget_frozenBlockLogWeakConstant
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    (B : ℕ → ℕ) (c : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    paperBlockBudget (frozenBlockLogWeakConstant f B c C) =
      ENNReal.ofReal C * frozenLogSquaredMassBudget f B c := by
  unfold paperBlockBudget frozenLogSquaredMassBudget
  simp_rw [ofReal_frozenBlockLogWeakConstant hf hfi B c hC,
    ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  rw [ENNReal.ofReal_mul hC,
    ENNReal.ofReal_mul (le_trans zero_le_one (paperOuterWeight_one_le k))]
  ring

/-- The paper's concrete frozen-block Kalton budget inequality, conditional
only on the explicitly stated individual finite-block weak estimate. -/
theorem lacunaryFrozenMainOutput_compl_levelSet_mul_le_logSquaredMass
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f B c C)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal a * volume
      ({x | ENNReal.ofReal a < lacunaryFrozenMainOutput f B c x} ∩
        (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
      24 * ENNReal.ofReal C * frozenLogSquaredMassBudget f B c := by
  have h := lacunaryFrozenMainOutput_compl_levelSet_mul_le hf
    (individualFrozenBlockWeakBounds_of_logSquared hf hfi hblock) ha
  rw [paperBlockBudget_frozenBlockLogWeakConstant hf hfi B c hblock.1] at h
  simpa only [mul_assoc] using h

theorem lacunaryFrozenMainOutput_compl_levelSet_one_le_logSquaredMass
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f B c C) :
    volume ({x | 1 < lacunaryFrozenMainOutput f B c x} ∩
      (fivefoldExceptionalSet (stoppingCenter (f := f)) stoppingLength)ᶜ) ≤
        24 * ENNReal.ofReal C * frozenLogSquaredMassBudget f B c := by
  simpa only [ENNReal.ofReal_one, one_mul] using
    lacunaryFrozenMainOutput_compl_levelSet_mul_le_logSquaredMass hf hfi hblock
      (by norm_num : (0 : ℝ) < 1)

theorem lacunaryFrozenMainOutput_levelSet_one_le_logSquaredMass
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f)
    {B : ℕ → ℕ} {c : ℕ} {C : ℝ}
    (hblock : HasLogSquaredFrozenBlockWeakBounds f B c C) :
    volume {x | 1 < lacunaryFrozenMainOutput f B c x} ≤
      5 * (∫⁻ x, ‖f x‖ₑ) +
        24 * ENNReal.ofReal C * frozenLogSquaredMassBudget f B c := by
  have h := lacunaryFrozenMainOutput_levelSet_one_le hf hfi
    (individualFrozenBlockWeakBounds_of_logSquared hf hfi hblock)
  rw [paperBlockBudget_frozenBlockLogWeakConstant hf hfi B c hblock.1] at h
  simpa only [mul_assoc] using h


end LacunaryMiddleKalton
end QuadraticCarleson
