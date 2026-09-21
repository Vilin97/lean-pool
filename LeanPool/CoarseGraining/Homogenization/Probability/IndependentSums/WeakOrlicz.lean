/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real

/-! # Weak Orlicz -/

namespace Homogenization
namespace IndependentSums

open MeasureTheory

variable {Ω : Type*}

/-!
Weak-Orlicz tail notation for the independent-sums probability mini-library.

This file follows the Chapter 4 note-facing convention directly:

- `X ≤ O_Ψ(A)` means `P[X > A t] ≤ Ψ(t)⁻¹` for every `t ≥ 1`;
- `X = O_Ψ(A)` means the same bound for `|X|`;
- `Γ_σ` and `Ψ_σ` are the stretched-exponential and log-normal model classes.

The definitions are intentionally tail-based rather than Banach-space based:
the notes use a weak-tail calculus, and this is the theorem surface needed for
the later concentration arguments.
-/

/-- The upper-tail event `{X > a}`. -/
def upperTailEvent (X : Ω → ℝ) (a : ℝ) : Set Ω :=
  {ω | a < X ω}

/-- The absolute upper-tail event `{|X| > a}`. -/
def absTailEvent (X : Ω → ℝ) (a : ℝ) : Set Ω :=
  upperTailEvent (fun ω => |X ω|) a

@[simp] theorem mem_upperTailEvent {X : Ω → ℝ} {a : ℝ} {ω : Ω} :
    ω ∈ upperTailEvent X a ↔ a < X ω :=
  Iff.rfl

@[simp] theorem mem_absTailEvent {X : Ω → ℝ} {a : ℝ} {ω : Ω} :
    ω ∈ absTailEvent X a ↔ a < |X ω| :=
  Iff.rfl

theorem upperTailEvent_mono_right {X : Ω → ℝ} {a b : ℝ} (hab : a ≤ b) :
    upperTailEvent X b ⊆ upperTailEvent X a := by
  intro ω hω
  show a < X ω
  exact lt_of_le_of_lt hab hω

theorem absTailEvent_mono_right {X : Ω → ℝ} {a b : ℝ} (hab : a ≤ b) :
    absTailEvent X b ⊆ absTailEvent X a :=
  upperTailEvent_mono_right (X := fun ω => |X ω|) hab

variable [MeasurableSpace Ω]

/-- The weak-Orlicz upper-tail relation `X ≤ O_Ψ(A)` from the notes. -/
def IsBigOWith (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  ∀ ⦃t : ℝ⦄, 1 ≤ t → μ.real (upperTailEvent X (A * t)) ≤ (Ψ t)⁻¹

/-- The symmetric weak-Orlicz relation `X = O_Ψ(A)`, defined through `|X|`. -/
def IsBigO (μ : Measure Ω) (Ψ : ℝ → ℝ) (X : Ω → ℝ) (A : ℝ) : Prop :=
  IsBigOWith μ Ψ (fun ω => |X ω|) A

/-- The baseline regularity package for a weak-Orlicz tail function:
monotonicity on `[0, ∞)` and the lower bound `Ψ ≥ 1` there. -/
def AdmissiblePsi (Ψ : ℝ → ℝ) : Prop :=
  MonotoneOn Ψ (Set.Ici 0) ∧ ∀ ⦃t : ℝ⦄, 0 ≤ t → 1 ≤ Ψ t

theorem IsBigOWith.of_le {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {A : ℝ}
    (hX : IsBigOWith μ Ψ X A) (hYX : ∀ ω, Y ω ≤ X ω) :
    IsBigOWith μ Ψ Y A := by
  intro t ht
  refine (measureReal_mono ?_).trans (hX ht)
  intro ω hω
  exact lt_of_lt_of_le hω (hYX ω)

theorem IsBigO.of_abs_le {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X Y : Ω → ℝ} {A : ℝ}
    (hX : IsBigO μ Ψ X A) (hYX : ∀ ω, |Y ω| ≤ |X ω|) :
    IsBigO μ Ψ Y A :=
  hX.of_le hYX

theorem IsBigOWith.mono_scale {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {A B : ℝ}
    (hX : IsBigOWith μ Ψ X A) (hAB : A ≤ B) :
    IsBigOWith μ Ψ X B := by
  intro t ht
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  refine (measureReal_mono ?_).trans (hX ht)
  exact upperTailEvent_mono_right (mul_le_mul_of_nonneg_right hAB ht0)

theorem IsBigO.mono_scale {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {A B : ℝ}
    (hX : IsBigO μ Ψ X A) (hAB : A ≤ B) :
    IsBigO μ Ψ X B := by
  exact IsBigOWith.mono_scale (μ := μ) (Ψ := Ψ) (X := fun ω => |X ω|)
    (A := A) (B := B) hX hAB

theorem IsBigOWith.const_mul {μ : Measure Ω} {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hX : IsBigOWith μ Ψ X A) :
    IsBigOWith μ Ψ (fun ω => c * X ω) (c * A) := by
  by_cases hc0 : c = 0
  · intro t ht
    have hrhs_nonneg : 0 ≤ (Ψ t)⁻¹ := by
      have hμ_nonneg : 0 ≤ μ.real (upperTailEvent X (A * t)) := by positivity
      exact le_trans hμ_nonneg (hX ht)
    simpa [upperTailEvent, hc0] using hrhs_nonneg
  · have hc_pos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    intro t ht
    have hset :
        upperTailEvent (fun ω => c * X ω) ((c * A) * t) = upperTailEvent X (A * t) := by
      ext ω
      constructor
      · intro hω
        change ((c * A) * t) < c * X ω at hω
        have hω' : c * (A * t) < c * X ω := by
          simpa [mul_assoc] using hω
        exact lt_of_mul_lt_mul_left hω' hc
      · intro hω
        change ((c * A) * t) < c * X ω
        have hmul : c * (A * t) < c * X ω := by
          exact mul_lt_mul_of_pos_left hω hc_pos
        simpa [mul_assoc] using hmul
    rw [hset]
    exact hX ht

theorem IsBigO.const_mul {μ : Measure Ω} {Ψ : ℝ → ℝ}
    {X : Ω → ℝ} {A c : ℝ} (hc : 0 ≤ c)
    (hX : IsBigO μ Ψ X A) :
    IsBigO μ Ψ (fun ω => c * X ω) (c * A) := by
  simpa [IsBigO, abs_mul, abs_of_nonneg hc] using
    IsBigOWith.const_mul (μ := μ) (Ψ := Ψ) (X := fun ω => |X ω|) (A := A) (c := c) hc hX

theorem IsBigO.neg {μ : Measure Ω} [IsFiniteMeasure μ] {Ψ : ℝ → ℝ} {X : Ω → ℝ}
    {A : ℝ}
    (hX : IsBigO μ Ψ X A) :
    IsBigO μ Ψ (fun ω => -X ω) A := by
  exact hX.of_abs_le fun ω => by simp

/-- The stretched-exponential model tail function `Γ_σ(t) = exp(t^σ)`. -/
noncomputable def gammaSigma (σ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp (t ^ σ)

/-- The log-normal model tail function
`Ψ_σ(t) = exp((σ⁻¹)^2 log(1 + σ t)^2)`. -/
noncomputable def psiSigma (σ : ℝ) : ℝ → ℝ :=
  fun t => Real.exp ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))

@[simp] theorem gammaSigma_apply (σ t : ℝ) :
    gammaSigma σ t = Real.exp (t ^ σ) :=
  rfl

@[simp] theorem psiSigma_apply (σ t : ℝ) :
    psiSigma σ t = Real.exp ((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ)) :=
  rfl

@[simp] theorem gammaSigma_inv (σ t : ℝ) :
    (gammaSigma σ t)⁻¹ = Real.exp (-(t ^ σ)) := by
  simp [gammaSigma, Real.exp_neg]

@[simp] theorem psiSigma_inv (σ t : ℝ) :
    (psiSigma σ t)⁻¹ =
      Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  simp [psiSigma, Real.exp_neg]

theorem one_le_gammaSigma {σ t : ℝ} (ht : 0 ≤ t) :
    1 ≤ gammaSigma σ t := by
  have hpow : 0 ≤ t ^ σ := Real.rpow_nonneg ht σ
  simpa [gammaSigma] using (Real.exp_le_exp).2 hpow

theorem one_le_psiSigma {σ t : ℝ} :
    1 ≤ psiSigma σ t := by
  have hexp : 0 ≤ (σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ) := by
    exact mul_nonneg (inv_nonneg.mpr (sq_nonneg σ)) (sq_nonneg _)
  simpa [psiSigma] using (Real.exp_le_exp).2 hexp

theorem gammaSigma_monotoneOn {σ : ℝ} (hσ : 0 ≤ σ) :
    MonotoneOn (gammaSigma σ) (Set.Ici 0) := by
  intro x hx y hy hxy
  exact (Real.exp_le_exp).2 (Real.rpow_le_rpow hx hxy hσ)

theorem admissiblePsi_gammaSigma {σ : ℝ} (hσ : 0 ≤ σ) :
    AdmissiblePsi (gammaSigma σ) := by
  refine ⟨gammaSigma_monotoneOn hσ, ?_⟩
  intro t ht
  exact one_le_gammaSigma ht

theorem psiSigma_monotoneOn {σ : ℝ} (hσ : 0 ≤ σ) :
    MonotoneOn (psiSigma σ) (Set.Ici 0) := by
  intro x hx y hy hxy
  have hargx_pos : 0 < 1 + σ * x := by
    have hσx_nonneg : 0 ≤ σ * x := mul_nonneg hσ hx
    linarith
  have hargy_pos : 0 < 1 + σ * y := by
    have hσy_nonneg : 0 ≤ σ * y := mul_nonneg hσ hy
    linarith
  have hargx_one : 1 ≤ 1 + σ * x := by
    have hσx_nonneg : 0 ≤ σ * x := mul_nonneg hσ hx
    linarith
  have hargy_one : 1 ≤ 1 + σ * y := by
    have hσy_nonneg : 0 ≤ σ * y := mul_nonneg hσ hy
    linarith
  have hargxy : 1 + σ * x ≤ 1 + σ * y := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (mul_le_mul_of_nonneg_left hxy hσ) 1
  have hlog_le :
      Real.log (1 + σ * x) ≤ Real.log (1 + σ * y) := by
    exact Real.log_le_log hargx_pos hargxy
  have hlogx_nonneg : 0 ≤ Real.log (1 + σ * x) := Real.log_nonneg hargx_one
  have hlogy_nonneg : 0 ≤ Real.log (1 + σ * y) := Real.log_nonneg hargy_one
  have hlog_sq :
      (Real.log (1 + σ * x)) ^ (2 : ℕ) ≤ (Real.log (1 + σ * y)) ^ (2 : ℕ) := by
    nlinarith
  exact (Real.exp_le_exp).2 <|
    mul_le_mul_of_nonneg_left hlog_sq (inv_nonneg.mpr (sq_nonneg σ))

theorem admissiblePsi_psiSigma {σ : ℝ} (hσ : 0 ≤ σ) :
    AdmissiblePsi (psiSigma σ) := by
  refine ⟨psiSigma_monotoneOn hσ, ?_⟩
  intro t ht
  exact one_le_psiSigma

theorem isBigOWith_gammaSigma_iff {μ : Measure Ω} {X : Ω → ℝ} {A σ : ℝ} :
    IsBigOWith μ (gammaSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (upperTailEvent X (A * t)) ≤ Real.exp (-(t ^ σ)) := by
  constructor
  · intro h t ht
    simpa [gammaSigma, ← Real.exp_neg] using h ht
  · intro h t ht
    simpa [gammaSigma, ← Real.exp_neg] using h ht

theorem isBigO_gammaSigma_iff {μ : Measure Ω} {X : Ω → ℝ} {A σ : ℝ} :
    IsBigO μ (gammaSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (absTailEvent X (A * t)) ≤ Real.exp (-(t ^ σ)) := by
  constructor
  · intro h t ht
    simpa [IsBigO, IsBigOWith, absTailEvent, gammaSigma, ← Real.exp_neg] using h ht
  · intro h t ht
    simpa [IsBigO, IsBigOWith, absTailEvent, gammaSigma, ← Real.exp_neg] using h ht

theorem isBigOWith_psiSigma_iff {μ : Measure Ω} {X : Ω → ℝ} {A σ : ℝ} :
    IsBigOWith μ (psiSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (upperTailEvent X (A * t)) ≤
          Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  constructor
  · intro h t ht
    simpa [psiSigma, ← Real.exp_neg] using h ht
  · intro h t ht
    simpa [psiSigma, ← Real.exp_neg] using h ht

theorem isBigO_psiSigma_iff {μ : Measure Ω} {X : Ω → ℝ} {A σ : ℝ} :
    IsBigO μ (psiSigma σ) X A ↔
      ∀ ⦃t : ℝ⦄, 1 ≤ t →
        μ.real (absTailEvent X (A * t)) ≤
          Real.exp (-((σ ^ (2 : ℕ))⁻¹ * (Real.log (1 + σ * t)) ^ (2 : ℕ))) := by
  constructor
  · intro h t ht
    simpa [IsBigO, IsBigOWith, absTailEvent, psiSigma, ← Real.exp_neg] using h ht
  · intro h t ht
    simpa [IsBigO, IsBigOWith, absTailEvent, psiSigma, ← Real.exp_neg] using h ht

end IndependentSums
end Homogenization
