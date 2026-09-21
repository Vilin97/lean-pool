/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BoundedOperator.Projector
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Blocks
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.Problem
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.OperatorNorm
import Mathlib.Topology.Basic

/-!
# Constructor data for a symmetric operator ideal family

`TauCeti.SymmetricOperatorIdealFamily` presents an operator ideal by a single
total `ℝ≥0∞` gauge, which is the representation the library uses everywhere.  A
*concrete* ideal, though, is normally discovered in the opposite shape: a
membership predicate, an `ℝ`-valued norm defined on the members, and the ideal
laws stated for members only.  The paper's Hilbert--Schmidt classes are exactly
that.

`SymmetricOperatorIdealFamily.Core` bundles that data and `ofCore` turns it into
a family, extending the gauge by `∞` off the ideal.  The extension argument is
proved once here rather than once per concrete ideal.

`Core` is not a second representation of an operator ideal.  Nothing consumes a
`Core`, no theorem is stated about one, and the two ideals built through it --
`hilbertSchmidtComplex` and the real descent under
`Sources/DavisKahan1970/Ideals/` -- are `SymmetricOperatorIdealFamily`s from the
moment they are defined.

This module is the successor of `RectangularSymmetricIdealFamily`, which was the
same free data used as a family in its own right, with its own gauge theory and
its own concrete instances converted back and forth from the canonical ones.
-/

namespace TauCeti.SymmetricOperatorIdealFamily

open scoped ENNReal InnerProductSpace

universe u v

/-- Constructor data for a `SymmetricOperatorIdealFamily`, presented the way a
concrete ideal is usually built: a membership predicate together with an
`ℝ`-valued gauge whose laws hold *on members only*.

`ofCore` turns this into a family.  This is not a second representation of an
operator ideal -- it carries no gauge of its own once `ofCore` has been applied,
and no theorem is stated about a `Core`.  It exists because the natural way to
present the paper's Hilbert--Schmidt classes is a predicate plus a real norm with
conditional laws, and rebuilding each of those field-by-field as an unconditional
`ℝ≥0∞` gauge would repeat the extension argument below once per ideal. -/
structure Core (𝕜 : Type u) [RCLike 𝕜] where
  Mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → Prop
  gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      (E →L[𝕜] F) → ℝ
  zero_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      Mem (0 : E →L[𝕜] F)
  add_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B → Mem (A + B)
  smul_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A → Mem (c • A)
  adjoint_mem :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → Mem A.adjoint
  comp_mem :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → Mem (L ∘L A ∘L R)
  gauge_nonneg :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → 0 ≤ gauge A
  gauge_zero :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F],
      gauge (0 : E →L[𝕜] F) = 0
  -- There is deliberately no `gauge_eq_zero` field: on the constructed family
  -- definiteness follows from `opNorm_le_gauge`, since the operator norm is
  -- already definite.  See `OperatorIdealFamily.gauge_eq_zero_iff`.
  gauge_add_le :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A B : E →L[𝕜] F}, Mem A → Mem B →
        gauge (A + B) ≤ gauge A + gauge B
  gauge_smul :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (c : 𝕜) {A : E →L[𝕜] F}, Mem A →
        gauge (c • A) = ‖c‖ * gauge A
  gauge_adjoint :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → gauge A.adjoint = gauge A
  gauge_comp_le :
    ∀ {E F G H : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
      [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
      (L : F →L[𝕜] G) {A : E →L[𝕜] F} (R : H →L[𝕜] E),
      Mem A → gauge (L ∘L A ∘L R) ≤ ‖L‖ * gauge A * ‖R‖
  opNorm_le_gauge :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      {A : E →L[𝕜] F}, Mem A → ‖A‖ ≤ gauge A
  gauge_complete :
    ∀ {E F : Type v}
      [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
      (A : ℕ → E →L[𝕜] F),
      (∀ n, Mem (A n)) →
      (∀ ε : ℝ, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
        gauge (A m - A n) < ε) →
      ∃ L, Mem L ∧ ∀ ε : ℝ, 0 < ε → ∃ N, ∀ n, N ≤ n →
        gauge (A n - L) < ε

variable {𝕜 : Type u} [RCLike 𝕜]

/-! ### The family a `Core` determines

A `Core`'s gauge is meaningful only *on* members, so it does not determine a
family in `ℝ`: off the ideal its value is unconstrained.  It does determine one
in `ℝ≥0∞`, by sending every non-member to `∞`, which is what `OperatorIdealFamily`
means by a total gauge.  The result agrees with the `Core`'s gauge on members,
which is all any consumer asks of it.

The ten lemmas below are that extension argument, proved once here so that a
concrete ideal has only to supply its conditional real laws. -/

/-- The `ℝ≥0∞` gauge a `Core` determines: its real gauge on members, `∞` off the
ideal. -/
noncomputable def Core.extendedGauge
    (N : Core.{u, v} 𝕜)
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
    (A : E →L[𝕜] F) : ℝ≥0∞ :=
  open Classical in
  if N.Mem A then ENNReal.ofReal (N.gauge A) else ∞

variable {N : Core.{u, v} 𝕜}
variable {E F G H : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
variable [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- On members the extended gauge is the `Core`'s own gauge. -/
theorem Core.extendedGauge_of_mem {A : E →L[𝕜] F} (hA : N.Mem A) :
    Core.extendedGauge N A = ENNReal.ofReal (N.gauge A) := ite_eq_left hA

/-- Off the ideal the extended gauge is `∞`. -/
theorem Core.extendedGauge_of_not_mem {A : E →L[𝕜] F} (hA : ¬ N.Mem A) :
    Core.extendedGauge N A = ∞ := ite_eq_right hA

/-- Finiteness of the extended gauge is exactly `Core` membership. -/
theorem Core.extendedGauge_ne_top_iff {A : E →L[𝕜] F} :
    Core.extendedGauge N A ≠ ∞ ↔ N.Mem A := by
  classical
  by_cases h : N.Mem A
  · simp [Core.extendedGauge_of_mem h, h]
  · simp [Core.extendedGauge_of_not_mem h, h]

/-- Scaling by a nonzero scalar does not change membership. -/
theorem Core.mem_smul_iff {c : 𝕜} (hc : c ≠ 0) {A : E →L[𝕜] F} :
    N.Mem (c • A) ↔ N.Mem A := by
  refine ⟨fun h => ?_, fun h => N.smul_mem c h⟩
  have := N.smul_mem c⁻¹ h
  rwa [← mul_smul, inv_mul_cancel₀ hc, one_smul] at this

/-- Membership is adjoint-invariant. -/
theorem Core.mem_adjoint_iff {A : E →L[𝕜] F} : N.Mem A.adjoint ↔ N.Mem A := by
  refine ⟨fun h => ?_, fun h => N.adjoint_mem h⟩
  have := N.adjoint_mem h
  rwa [ContinuousLinearMap.adjoint_adjoint] at this

/-- Subadditivity, unconditionally: off the ideal the right-hand side is `∞`. -/
theorem Core.extendedGauge_add_le (A B : E →L[𝕜] F) :
    Core.extendedGauge N (A + B)
      ≤ Core.extendedGauge N A + Core.extendedGauge N B := by
  classical
  by_cases hA : N.Mem A
  · by_cases hB : N.Mem B
    · rw [Core.extendedGauge_of_mem hA, Core.extendedGauge_of_mem hB,
        Core.extendedGauge_of_mem (N.add_mem hA hB),
        ← ENNReal.ofReal_add (N.gauge_nonneg hA) (N.gauge_nonneg hB)]
      exact ENNReal.ofReal_le_ofReal (N.gauge_add_le hA hB)
    · simp [Core.extendedGauge_of_not_mem hB]
  · simp [Core.extendedGauge_of_not_mem hA]

/-- Absolute homogeneity, unconditionally.  The `c = 0` case is where the
extension is doing work: the left side is the gauge of `0`, and the right side is
`0 * ∞ = 0` in `ℝ≥0∞` when `A` is off the ideal. -/
theorem Core.extendedGauge_smul (c : 𝕜) (A : E →L[𝕜] F) :
    Core.extendedGauge N (c • A) = ‖c‖ₑ * Core.extendedGauge N A := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Core.extendedGauge_of_mem (N.zero_mem (E := E) (F := F)), N.gauge_zero]
  · by_cases hA : N.Mem A
    · rw [Core.extendedGauge_of_mem hA,
        Core.extendedGauge_of_mem (N.smul_mem c hA), N.gauge_smul c hA,
        ENNReal.ofReal_mul (norm_nonneg c), ← ofReal_norm]
    · rw [Core.extendedGauge_of_not_mem hA,
        Core.extendedGauge_of_not_mem (fun h => hA ((Core.mem_smul_iff hc).mp h))]
      simp [ENNReal.mul_top, enorm_ne_zero.mpr hc]

/-- The operator norm is dominated by the extended gauge. -/
theorem Core.enorm_le_extendedGauge (A : E →L[𝕜] F) :
    ‖A‖ₑ ≤ Core.extendedGauge N A := by
  classical
  by_cases hA : N.Mem A
  · rw [Core.extendedGauge_of_mem hA, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (N.opNorm_le_gauge hA)
  · simp [Core.extendedGauge_of_not_mem hA]

/-- The two-sided ideal law, unconditionally. -/
theorem Core.extendedGauge_comp_le (L : F →L[𝕜] G) (A : E →L[𝕜] F) (R : H →L[𝕜] E) :
    Core.extendedGauge N (L ∘L A ∘L R)
      ≤ ‖L‖ₑ * Core.extendedGauge N A * ‖R‖ₑ := by
  classical
  by_cases hA : N.Mem A
  · rw [Core.extendedGauge_of_mem hA,
      Core.extendedGauge_of_mem (N.comp_mem L R hA),
      ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (norm_nonneg L),
      ← ENNReal.ofReal_mul (mul_nonneg (norm_nonneg L) (N.gauge_nonneg hA))]
    exact ENNReal.ofReal_le_ofReal (N.gauge_comp_le L R hA)
  · rcases eq_or_ne ‖L‖ₑ 0 with hL | hL
    · have hL0 : L = 0 := by
        rw [← ofReal_norm, ENNReal.ofReal_eq_zero] at hL
        exact norm_eq_zero.mp (le_antisymm hL (norm_nonneg L))
      subst hL0
      simp [ContinuousLinearMap.zero_comp,
        Core.extendedGauge_of_mem (N.zero_mem (E := H) (F := G)), N.gauge_zero]
    · rcases eq_or_ne ‖R‖ₑ 0 with hR | hR
      · have hR0 : R = 0 := by
          rw [← ofReal_norm, ENNReal.ofReal_eq_zero] at hR
          exact norm_eq_zero.mp (le_antisymm hR (norm_nonneg R))
        subst hR0
        simp [ContinuousLinearMap.comp_zero,
          Core.extendedGauge_of_mem (N.zero_mem (E := H) (F := G)), N.gauge_zero]
      · rw [Core.extendedGauge_of_not_mem hA]
        simp [ENNReal.mul_top, hL, hR]

/-- The extended gauge is adjoint-invariant. -/
theorem Core.extendedGauge_adjoint (A : E →L[𝕜] F) :
    Core.extendedGauge N A.adjoint = Core.extendedGauge N A := by
  classical
  by_cases hA : N.Mem A
  · rw [Core.extendedGauge_of_mem hA, Core.extendedGauge_of_mem (N.adjoint_mem hA),
      N.gauge_adjoint hA]
  · rw [Core.extendedGauge_of_not_mem hA,
      Core.extendedGauge_of_not_mem (fun h => hA (Core.mem_adjoint_iff.mp h))]

/-- **The symmetric ideal family a `Core` presents.**

The `Core`'s conditional `ℝ` laws become the family's unconditional `ℝ≥0∞` ones
by the extension above, and `isComplete_ofCore` carries `gauge_complete` across
as the `IsComplete` instance, so nothing the `Core` proved is dropped.

`ofCore` is not injective and is not meant to be: two `Core`s differing only in
what gauge they assign to non-members give the same family, because the family
assigns `∞` to all of them.  What is preserved is the whole of the ideal --
membership (`gauge_ofCore_ne_top_iff`) and the gauge on it
(`toReal_gauge_ofCore`). -/
noncomputable def ofCore (N : Core.{u, v} 𝕜) :
    SymmetricOperatorIdealFamily.{u, v} 𝕜 where
  gauge := Core.extendedGauge N
  gauge_add_le := Core.extendedGauge_add_le
  gauge_smul := Core.extendedGauge_smul
  enorm_le_gauge := Core.enorm_le_extendedGauge
  gauge_comp_le := Core.extendedGauge_comp_le
  gauge_adjoint := Core.extendedGauge_adjoint

/-- The constructed family's gauge is the extended gauge, definitionally. -/
@[simp]
theorem gauge_ofCore (N : Core.{u, v} 𝕜)
    (A : E →L[𝕜] F) : (ofCore N).gauge A = Core.extendedGauge N A := rfl

/-- Membership in the constructed family is the `Core`'s own membership. -/
theorem gauge_ofCore_ne_top_iff {N : Core.{u, v} 𝕜}
    {A : E →L[𝕜] F} : (ofCore N).gauge A ≠ ∞ ↔ N.Mem A :=
  Core.extendedGauge_ne_top_iff

/-- On members, the real view of the constructed family is the `Core`'s own
gauge.  With `gauge_ofCore_ne_top_iff` this is the exact sense in which `ofCore`
loses nothing: `toReal ∘ gauge` is the canonical real view's `gaugeReal`, so a
consumer reading the family in `ℝ` reads back what the `Core` supplied. -/
theorem toReal_gauge_ofCore {N : Core.{u, v} 𝕜}
    {A : E →L[𝕜] F} (hA : N.Mem A) :
    ((ofCore N).gauge A).toReal = N.gauge A := by
  rw [gauge_ofCore, Core.extendedGauge_of_mem hA,
    ENNReal.toReal_ofReal (N.gauge_nonneg hA)]

/-- The constructed family is complete.

This is the field `ofCore` would otherwise drop.  The family has no completeness
field — completeness is the separate class `IsComplete`,
`CompleteSpace (N.Elem E F)` — whereas a `Core` carries `gauge_complete` as an
`ℝ`-valued Cauchy statement.  Every `Core` has that field, so the instance is
unconditional; the proof is the translation between the two idioms, using the
fact that `Elem`'s norm is exactly the `Core`'s gauge on members. -/
instance isComplete_ofCore (N : Core.{u, v} 𝕜) :
    (ofCore N).toOperatorIdealFamily.IsComplete where
  completeSpace := by
    intro E F _ _ _ _ _ _
    have hnorm : ∀ x : (ofCore N).toOperatorIdealFamily.Elem E F,
        ‖x‖ = N.gauge x.val := fun x =>
      toReal_gauge_ofCore (gauge_ofCore_ne_top_iff.mp x.gauge_val_ne_top)
    refine Metric.complete_of_cauchySeq_tendsto fun a ha => ?_
    have hmem : ∀ n, N.Mem (a n).val := fun n =>
      gauge_ofCore_ne_top_iff.mp (a n).gauge_val_ne_top
    have hcauchy : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m n, M ≤ m → M ≤ n →
        N.gauge ((a m).val - (a n).val) < ε := by
      intro ε hε
      rw [Metric.cauchySeq_iff] at ha
      obtain ⟨M, hM⟩ := ha ε hε
      refine ⟨M, fun m n hm hn => ?_⟩
      have h := hM m hm n hn
      rw [dist_eq_norm, hnorm] at h
      exact h
    obtain ⟨L, hLmem, hL⟩ := N.gauge_complete (fun n => (a n).val) hmem hcauchy
    refine ⟨OperatorIdealFamily.Elem.mk (gauge_ofCore_ne_top_iff.mpr hLmem), ?_⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := hL ε hε
    refine ⟨M, fun n hn => ?_⟩
    rw [dist_eq_norm, hnorm]
    exact hM n hn

end TauCeti.SymmetricOperatorIdealFamily
