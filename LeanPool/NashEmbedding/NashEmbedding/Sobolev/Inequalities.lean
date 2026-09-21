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
import Mathlib
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Distribution
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Periodization

/-!
# Sobolev Inequalities

Generic inequalities for `sobolevNormSqDistrib` and `MemSobolevDistrib`.
These are tools applicable across the `NashEmbedding.Sobolev` infrastructure,
not specific to any particular construction (mollifier, Riemann sum,
etc.).
-/

open scoped BigOperators
open Complex Real MeasureTheory

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-
Quasi-triangle inequality for `sobolevNormSqDistrib`:
    `‖a - c‖_{H^s_*}^2 ≤ 2 ‖a - b‖_{H^s_*}^2 + 2 ‖b - c‖_{H^s_*}^2`.
-/
lemma sobolevNormSqDistrib_triangle (s : ℝ) (a b c : TrigPolyDual n)
    (hab : MemSobolevDistrib n s (a - b)) (hbc : MemSobolevDistrib n s (b - c)) :
    sobolevNormSqDistrib n s (a - c) ≤
      2 * sobolevNormSqDistrib n s (a - b) + 2 * sobolevNormSqDistrib n s (b - c) := by
  unfold MemSobolevDistrib at hab hbc;
  unfold MemSobolev at *;
  unfold sobolevNormSqDistrib;
  unfold sobolevNormSq;
  rw [ ← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add ];
  · refine' Summable.tsum_le_tsum _ _ _;
    · intro m;
      -- Apply the triangle inequality to the norm of the difference.
      have h_triangle : ‖fourierCoeffDistrib (a - c) m‖ ^ 2 ≤ 2 * ‖fourierCoeffDistrib (a - b) m‖ ^ 2 + 2 * ‖fourierCoeffDistrib (b - c) m‖ ^ 2 := by
        have h_triangle : ‖fourierCoeffDistrib (a - c) m‖ ≤ ‖fourierCoeffDistrib (a - b) m‖ + ‖fourierCoeffDistrib (b - c) m‖ := by
          exact IsAbsoluteValue.abv_sub_le Norm.norm (a fun₀ | -m => 1) (b fun₀ | -m => 1) (c fun₀ | -m => 1);
        nlinarith only [ sq_nonneg ( ‖fourierCoeffDistrib ( a - b ) m‖ - ‖fourierCoeffDistrib ( b - c ) m‖ ), h_triangle, norm_nonneg ( fourierCoeffDistrib ( a - c ) m ), norm_nonneg ( fourierCoeffDistrib ( a - b ) m ), norm_nonneg ( fourierCoeffDistrib ( b - c ) m ) ];
      nlinarith [ show 0 ≤ weight n s m by exact Real.rpow_nonneg ( add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _ ) _ ];
    · -- By definition of `fourierCoeffDistrib`, we have `fourierCoeffDistrib (a - c) = fourierCoeffDistrib (a - b) + fourierCoeffDistrib (b - c)`.
      have h_fourierCoeffDistrib : fourierCoeffDistrib (a - c) = fourierCoeffDistrib (a - b) + fourierCoeffDistrib (b - c) := by
        ext m; simp [fourierCoeffDistrib];
      -- Apply the inequality $|x + y|^2 \leq 2|x|^2 + 2|y|^2$ to each term in the sum.
      have h_ineq : ∀ m : Fin n → ℤ, ‖fourierCoeffDistrib (a - c) m‖ ^ 2 ≤ 2 * ‖fourierCoeffDistrib (a - b) m‖ ^ 2 + 2 * ‖fourierCoeffDistrib (b - c) m‖ ^ 2 := by
        intro m; rw [ h_fourierCoeffDistrib ] ; norm_num;
        nlinarith only [ norm_nonneg ( fourierCoeffDistrib ( a - b ) m + fourierCoeffDistrib ( b - c ) m ), norm_add_le ( fourierCoeffDistrib ( a - b ) m ) ( fourierCoeffDistrib ( b - c ) m ), sq_nonneg ( ‖fourierCoeffDistrib ( a - b ) m‖ - ‖fourierCoeffDistrib ( b - c ) m‖ ) ];
      refine' Summable.of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) ) ( fun m => mul_le_mul_of_nonneg_left ( h_ineq m ) ( weight_nonneg _ _ ) ) _;
      convert hab.mul_left 2 |> Summable.add <| hbc.mul_left 2 using 2
      all_goals (first | rfl | ring)
    · exact Summable.add ( hab.mul_left _ ) ( hbc.mul_left _ );
  · exact hab.mul_left 2;
  · exact hbc.mul_left 2

/-! ## Closure properties of `MemSobolevDistrib` and `integrationEmbed` -/

/-
`MemSobolevDistrib` is closed under subtraction.
-/
lemma MemSobolevDistrib.sub {s : ℝ} {a b : TrigPolyDual n}
    (ha : MemSobolevDistrib n s a) (hb : MemSobolevDistrib n s b) :
    MemSobolevDistrib n s (a - b) := by
  refine' .of_nonneg_of_le ( fun m => _ ) ( fun m => _ ) ( Summable.add ha hb |> Summable.mul_left 2 );
  · exact mul_nonneg ( by exact Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ) _ ) ( sq_nonneg _ );
  · -- Apply the triangle inequality to the norm of the difference.
    have h_triangle : ‖fourierCoeffDistrib (a - b) m‖ ^ 2 ≤ 2 * (‖fourierCoeffDistrib a m‖ ^ 2 + ‖fourierCoeffDistrib b m‖ ^ 2) := by
      have h_bound : ‖fourierCoeffDistrib (a - b) m‖ ≤ ‖fourierCoeffDistrib a m‖ + ‖fourierCoeffDistrib b m‖ := by
        convert norm_sub_le ( fourierCoeffDistrib a m ) ( fourierCoeffDistrib b m ) using 2
        all_goals rfl
      exact le_trans ( pow_le_pow_left₀ ( norm_nonneg _ ) h_bound 2 ) ( by linarith [ sq_nonneg ( ‖fourierCoeffDistrib a m‖ - ‖fourierCoeffDistrib b m‖ ) ] );
    nlinarith [ show 0 ≤ weight n s m by exact le_of_lt ( weight_pos s m ) ]

/-! ## `integrationEmbed` linearity (subject to continuity)

The unconditional identities `ι(f + g) = ι(f) + ι(g)` and
`ι(f - g) = ι(f) - ι(g)` are FALSE: Bochner-integral additivity fails when
one of the two functions is non-integrable on the period cube `[0, 2π]ⁿ`.
The identities do hold once integrability of the integrands `f · e_{-m}`
and `g · e_{-m}` on the period cube is available. We package this as a
continuity hypothesis on `f` and `g`: continuous ⟹ (continuous × continuous
bounded) ⟹ integrable on the compact period cube, and additivity of the
Bochner integral kicks in.

Consumers that only have `IntegrableOn f` (weaker than `Continuous f`)
would need a variant with `IntegrableOn` hypotheses and a
`MeasureTheory.Integrable.bdd_mul`-style step to get integrability of
`f · e_{-m}`; not needed here.
-/

/-- Internal helper: additivity of `stdFourierCoeff` on continuous
functions. -/
private lemma stdFourierCoeff_add_of_continuous
    {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (m : Fin n → ℤ) :
    stdFourierCoeff n (fun x => f x + g x) m
      = stdFourierCoeff n f m + stdFourierCoeff n g m := by
  unfold stdFourierCoeff
  rw [← mul_add]
  congr 1
  have hfe : IntegrableOn (fun θ => f θ * fourierExp n (-m) θ)
      (Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))) :=
    (hf.mul ((fourierExp_contDiff (-m)).continuous)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hge : IntegrableOn (fun θ => g θ * fourierExp n (-m) θ)
      (Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))) :=
    (hg.mul ((fourierExp_contDiff (-m)).continuous)).continuousOn.integrableOn_compact
      isCompact_Icc
  rw [← MeasureTheory.integral_add hfe hge]
  congr 1
  funext θ
  ring

/-- Internal helper: subtraction analogue of
`stdFourierCoeff_add_of_continuous`. -/
private lemma stdFourierCoeff_sub_of_continuous
    {f g : (Fin n → ℝ) → ℂ} (hf : Continuous f) (hg : Continuous g)
    (m : Fin n → ℤ) :
    stdFourierCoeff n (fun x => f x - g x) m
      = stdFourierCoeff n f m - stdFourierCoeff n g m := by
  unfold stdFourierCoeff
  rw [← mul_sub]
  congr 1
  have hfe : IntegrableOn (fun θ => f θ * fourierExp n (-m) θ)
      (Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))) :=
    (hf.mul ((fourierExp_contDiff (-m)).continuous)).continuousOn.integrableOn_compact
      isCompact_Icc
  have hge : IntegrableOn (fun θ => g θ * fourierExp n (-m) θ)
      (Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ))) :=
    (hg.mul ((fourierExp_contDiff (-m)).continuous)).continuousOn.integrableOn_compact
      isCompact_Icc
  rw [← MeasureTheory.integral_sub hfe hge]
  congr 1
  funext θ
  ring

/-- Internal helper: `seqToDual` is additive in its sequence argument. -/
private lemma seqToDual_add (a b : (Fin n → ℤ) → ℂ) :
    seqToDual n (a + b) = seqToDual n a + seqToDual n b := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.add_apply]
  show (Finsupp.linearCombination ℂ (fun m => (a + b) (-m))) u
     = (Finsupp.linearCombination ℂ (fun m => a (-m))) u
     + (Finsupp.linearCombination ℂ (fun m => b (-m))) u
  simp only [Finsupp.linearCombination_apply, Pi.add_apply, smul_add]
  exact Finsupp.sum_add

/-- Internal helper: `seqToDual` distributes over negation. -/
private lemma seqToDual_neg (a : (Fin n → ℤ) → ℂ) :
    seqToDual n (-a) = -seqToDual n a := by
  refine LinearMap.ext fun u => ?_
  simp only [LinearMap.neg_apply]
  show (Finsupp.linearCombination ℂ (fun m => (-a) (-m))) u
     = -(Finsupp.linearCombination ℂ (fun m => a (-m))) u
  simp only [Finsupp.linearCombination_apply, Pi.neg_apply, smul_neg]
  rw [Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]

/-- Internal helper: `seqToDual` distributes over subtraction. -/
private lemma seqToDual_sub (a b : (Fin n → ℤ) → ℂ) :
    seqToDual n (a - b) = seqToDual n a - seqToDual n b := by
  rw [sub_eq_add_neg, seqToDual_add, seqToDual_neg, ← sub_eq_add_neg]

/-- `integrationEmbed` is additive on continuous functions:
`ι(f + g) = ι(f) + ι(g)`. Continuity is needed to give Bochner-integral
additivity of the integrands `f · e_{-m}` and `g · e_{-m}` on the compact
period cube `[0, 2π]ⁿ`. Without integrability the unconditional identity
is false — see the section header. -/
lemma integrationEmbed_add {f g : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    integrationEmbed n (fun x => f x + g x)
      = integrationEmbed n f + integrationEmbed n g := by
  unfold integrationEmbed
  have hseq : stdFourierCoeff n (fun x => f x + g x)
              = stdFourierCoeff n f + stdFourierCoeff n g := by
    funext m
    exact stdFourierCoeff_add_of_continuous hf hg m
  rw [hseq]
  exact seqToDual_add _ _

/-- `integrationEmbed` distributes over subtraction on continuous functions:
`ι(f - g) = ι(f) - ι(g)`. Companion of `integrationEmbed_add`; same caveat. -/
lemma integrationEmbed_sub {f g : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    integrationEmbed n (fun x => f x - g x)
      = integrationEmbed n f - integrationEmbed n g := by
  unfold integrationEmbed
  have hseq : stdFourierCoeff n (fun x => f x - g x)
              = stdFourierCoeff n f - stdFourierCoeff n g := by
    funext m
    exact stdFourierCoeff_sub_of_continuous hf hg m
  rw [hseq]
  exact seqToDual_sub _ _

end NashEmbedding.Sobolev

end
