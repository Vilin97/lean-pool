/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/

/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution

/-!
# Convolution by a compactly supported smooth function

This file defines the convolution of a function `φ` with a periodic
distribution `u ∈ X_n^*`, the rescaled function `φ_ε`, and proves the
mollifier convergence theorem: `φ_ε * u → (∫ φ) · u` in `H^s` as `ε → 0⁺`.

## Main definitions

* `ftRn n φ ξ` — the Fourier transform of `φ : ℝⁿ → ℂ` at `ξ ∈ ℝⁿ`:
  `φ̂(ξ) = ∫ φ(y) e^{-iξ·y} dy` (no `(2π)^{-n}` factor).
* `convDistrib n φ u` — the convolution `φ * u` for `u ∈ X_n^*`, defined via
  `(φ * u)^(m) = φ̂(m) · û(m)`.
* `rescale n φ ε` — the rescaled function `φ_ε(x) = ε^{-n} φ(x/ε)`.

## Main results

* `memSobolevDistrib_convDistrib` — H^s-closure under convolution.
* `convDistrib_add`, `convDistrib_smul` — ℂ-linearity in `u`.
* `ftRn_rescale` — the rescaling identity `(φ_ε)^(ξ) = φ̂(εξ)`.
* `mollifier_convergence` — mollifier convergence theorem.
-/

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev MeasureTheory


noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Fourier transform on ℝⁿ -/

/-- The Fourier transform of `φ : ℝⁿ → ℂ` at `ξ ∈ ℝⁿ`:
`φ̂(ξ) = ∫ φ(y) e^{-iξ·y} dy` (no `(2π)^{-n}` factor). -/
def ftRn (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (ξ : Fin n → ℝ) : ℂ :=
  ∫ y, φ y * exp (-(I * ↑(∑ j : Fin n, ξ j * y j)))

/-
Bound on the Fourier transform: `‖φ̂(ξ)‖ ≤ ∫ ‖φ‖`.
-/
lemma ftRn_norm_le (φ : (Fin n → ℝ) → ℂ) (_hφ : Integrable φ) (ξ : Fin n → ℝ) :
    ‖ftRn n φ ξ‖ ≤ ∫ y, ‖φ y‖ := by
      convert MeasureTheory.norm_integral_le_integral_norm
          ( fun y => φ y * exp ( - ( I * ↑( ∑ j : Fin n, ξ j * y j ) ) ) ) using 1
      all_goals first
      | rfl
      | ( norm_num [ Complex.norm_exp ] )

/-
Continuity of the Fourier transform in `ξ`.
-/
lemma continuous_ftRn (φ : (Fin n → ℝ) → ℂ) (hφ : Integrable φ) :
    Continuous (ftRn n φ) := by
      refine' continuous_iff_continuousAt.mpr _;
      intro ξ;
      refine' MeasureTheory.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
      refine' fun x => ‖φ x‖;
      · exact Filter.Eventually.of_forall fun x => hφ.1.mul ( Continuous.aestronglyMeasurable (
          by continuity ) );
      · norm_num [ Complex.norm_exp ];
      · exact hφ.norm;
      · exact Filter.Eventually.of_forall fun x => Continuous.tendsto ( by continuity ) _

/-! ## Convolution with a distribution -/

/-- The convolution `φ * u` of a function `φ` with a distribution `u ∈ X_n^*`,
defined via Fourier coefficients: `(φ * u)^(m) = φ̂(m) · û(m)`. -/
def convDistrib (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (u : TrigPolyDual n) : TrigPolyDual n :=
  seqToDual n (fun m => ftRn n φ (fun j => (m j : ℝ)) * fourierCoeffDistrib u m)

/-- The Fourier coefficient of the convolution. -/
lemma fourierCoeffDistrib_convDistrib (φ : (Fin n → ℝ) → ℂ) (u : TrigPolyDual n)
    (m : Fin n → ℤ) :
    fourierCoeffDistrib (convDistrib n φ u) m =
      ftRn n φ (fun j => (m j : ℝ)) * fourierCoeffDistrib u m := by
  exact congr_fun (fourierCoeffDistrib_seqToDual _) m

/-! ## Fourier coefficient linearity helpers -/

lemma fourierCoeffDistrib_smul_complex (c : ℂ) (u : TrigPolyDual n) (m : Fin n → ℤ) :
    fourierCoeffDistrib (c • u) m = c * fourierCoeffDistrib u m := by
  simp [fourierCoeffDistrib]

lemma fourierCoeffDistrib_sub (u v : TrigPolyDual n) (m : Fin n → ℤ) :
    fourierCoeffDistrib (u - v) m = fourierCoeffDistrib u m - fourierCoeffDistrib v m := by
  simp [fourierCoeffDistrib]

lemma fourierCoeffDistrib_add (u v : TrigPolyDual n) (m : Fin n → ℤ) :
    fourierCoeffDistrib (u + v) m = fourierCoeffDistrib u m + fourierCoeffDistrib v m := by
  simp [fourierCoeffDistrib]

lemma seqToDual_add (a b : (Fin n → ℤ) → ℂ) :
    seqToDual n (a + b) = seqToDual n a + seqToDual n b := by
      unfold seqToDual;
      ext; simp [Finsupp.linearCombination_apply]

lemma seqToDual_smul (c : ℂ) (a : (Fin n → ℤ) → ℂ) :
    seqToDual n (c • a) = c • seqToDual n a := by
      ext m; simp [seqToDual]

/-! ## H^s closure under convolution (Lemma) -/

/-
**H^s-closure under convolution.** If `φ` is integrable and `u ∈ H^s`,
then `φ * u ∈ H^s`.
-/
theorem memSobolevDistrib_convDistrib (φ : (Fin n → ℝ) → ℂ) (hφ : Integrable φ)
    {s : ℝ} {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u) :
    MemSobolevDistrib n s (convDistrib n φ u) := by
      refine' .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg s m ) ( sq_nonneg _ ) ) (
          fun m => _ ) ( hu.mul_left ( ( ∫ y, ‖φ y‖ ) ^ 2 ) );
      rw [ mul_comm ];
      rw [ mul_left_comm ];
      rw [ mul_comm ];
      rw [ fourierCoeffDistrib_convDistrib ];
      apply mul_le_mul_of_nonneg_left _ (weight_nonneg s m)
      rw [norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (ftRn_norm_le φ hφ _) 2) (sq_nonneg _)

/-! ## ℂ-linearity in u (Lemma) -/

/-
Linearity of convolution in `u`: `φ * (u + v) = φ * u + φ * v`.
-/
theorem convDistrib_add (φ : (Fin n → ℝ) → ℂ) (u v : TrigPolyDual n) :
    convDistrib n φ (u + v) = convDistrib n φ u + convDistrib n φ v := by
      unfold convDistrib;
      ext m; simp [fourierCoeffDistrib_add, seqToDual];
      ring

/-
Scalar compatibility of convolution: `φ * (c · u) = c · (φ * u)`.
-/
theorem convDistrib_smul (φ : (Fin n → ℝ) → ℂ) (c : ℂ) (u : TrigPolyDual n) :
    convDistrib n φ (c • u) = c • convDistrib n φ u := by
      ext m;
      simp +decide [ convDistrib, fourierCoeffDistrib_smul_complex ];
      simp +decide [ seqToDual, mul_left_comm ]

/-! ## Rescaling (Definition) -/

/-- The rescaled function `φ_ε(x) = ε^{-n} φ(x/ε)` for `ε > 0`. -/
def rescale (n : ℕ) (φ : (Fin n → ℝ) → ℂ) (ε : ℝ) (x : Fin n → ℝ) : ℂ :=
  (((ε⁻¹) ^ n : ℝ) : ℂ) * φ (ε⁻¹ • x)

/-
The rescaling identity: `(φ_ε)^(ξ) = φ̂(εξ)`.
-/
lemma ftRn_rescale (φ : (Fin n → ℝ) → ℂ) (_hφ : Integrable φ)
    {ε : ℝ} (hε : 0 < ε) (ξ : Fin n → ℝ) :
    ftRn n (rescale n φ ε) ξ = ftRn n φ (ε • ξ) := by
      unfold ftRn rescale;
      -- Apply the change of variables $z = \epsilon^{-1} y$ to the integral.
      have h_change : ∀ {f : (Fin n → ℝ) → ℂ}, ∫ y, f y = ∫ z, f (ε • z) * ε ^ n := by
        intro f; rw [ MeasureTheory.integral_mul_const ] ; rw [
            MeasureTheory.Measure.integral_comp_smul ] ; norm_num [ hε.ne' ] ;
        rw [ abs_of_pos hε, inv_mul_eq_div, div_mul_cancel₀ _ ( by norm_cast; positivity ) ];
      convert h_change using 3 ; norm_num [ hε.ne', mul_assoc, mul_left_comm, mul_comm ]

/-! ## Mollifier convergence (Theorem) -/

/-
**Mollifier convergence.** If `φ` is integrable with continuous Fourier
transform, then `φ_ε * u → (∫ φ) · u` in `H^s` as `ε → 0⁺`. Here
`∫ φ = φ̂(0) = ftRn n φ 0`.
-/
theorem mollifier_convergence (φ : (Fin n → ℝ) → ℂ)
    (hφ : Integrable φ)
    {s : ℝ} {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u) :
    Filter.Tendsto
      (fun ε => sobolevNormSqDistrib n s
        (convDistrib n (rescale n φ ε) u - ftRn n φ 0 • u))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds 0) := by
        convert tendsto_tsum_of_dominated_convergence
            (f := fun ε m => weight n s m *
              ‖fourierCoeffDistrib (convDistrib n (rescale n φ ε) u - ftRn n φ 0 • u) m‖ ^ 2)
            (g := fun _ => (0:ℝ))
            (bound := fun m => weight n s m * (2 * ∫ y, ‖φ y‖) ^ 2 * ‖fourierCoeffDistrib u m‖ ^ 2)
            ?hsum ?hab ?hbound using 1
        all_goals try first
        | rfl
        | (simp only [ tsum_zero ])
        case hsum => convert hu.mul_left ( ( 2 * ∫ y, ‖φ y‖ ) ^ 2 ) using 2 <;> first | rfl | ring
        case hab =>
          intro m;
          -- By definition of $fourierCoeffDistrib$, we know that
          have h_fourierCoeffDistrib : ∀ x > 0, fourierCoeffDistrib (convDistrib n (rescale n φ
              x) u - ftRn n φ 0 • u) m = (ftRn n φ (x • (fun j => (m j : ℝ))) - ftRn n φ 0) *
              fourierCoeffDistrib u m := by
            intro x hx
            rw [fourierCoeffDistrib_sub, fourierCoeffDistrib_convDistrib,
              fourierCoeffDistrib_smul_complex, ftRn_rescale _ hφ hx]
            ring
          rw [ Filter.tendsto_congr' ( Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun x hx
              => by rw [ h_fourierCoeffDistrib x hx ] ) ];
          refine' tendsto_nhdsWithin_of_tendsto_nhds _;
          refine' Continuous.tendsto' _ _ _ _ <;> norm_num;
          exact Continuous.mul continuous_const <| Continuous.pow ( Continuous.mul (
              Continuous.norm <| Continuous.sub ( continuous_ftRn _ hφ |> Continuous.comp <|
              continuous_id.smul continuous_const ) continuous_const ) continuous_const ) _;
        case hbound =>
          refine' Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => fun m => _;
          rw [ fourierCoeffDistrib_sub, fourierCoeffDistrib_convDistrib,
              fourierCoeffDistrib_smul_complex ];
          rw [ show ftRn n ( rescale n φ ε ) ( fun j => ( m j : ℝ ) ) = ftRn n φ ( ε • fun j =>
              ( m j : ℝ ) ) from ftRn_rescale _ hφ hε _ ];
          -- Apply the triangle inequality to the norm.
          have h_triangle : ‖ftRn n φ (ε • fun j => (m j : ℝ)) * fourierCoeffDistrib u m - ftRn
              n φ 0 * fourierCoeffDistrib u m‖ ≤ (2 * ∫ y, ‖φ y‖) * ‖fourierCoeffDistrib u m‖ := by
            have h_triangle : ‖ftRn n φ (ε • fun j => (m j : ℝ)) - ftRn n φ 0‖ ≤ 2 * ∫ y, ‖φ y‖
                := by
              have h_triangle : ‖ftRn n φ (ε • fun j => (m j : ℝ))‖ ≤ ∫ y, ‖φ y‖ ∧ ‖ftRn n φ 0‖
                  ≤ ∫ y, ‖φ y‖ := by
                exact ⟨ ftRn_norm_le _ hφ _, ftRn_norm_le _ hφ _ ⟩;
              exact le_trans ( norm_sub_le _ _ ) ( by linarith );
            rw [← sub_mul, norm_mul]
            exact mul_le_mul_of_nonneg_right h_triangle (norm_nonneg _)
          rw [ Real.norm_of_nonneg ( by exact mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ];
          simpa only [ mul_pow, mul_assoc ] using mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ (
              norm_nonneg _ ) h_triangle 2 ) ( weight_nonneg _ _ )

end NashEmbedding.Sobolev

end
