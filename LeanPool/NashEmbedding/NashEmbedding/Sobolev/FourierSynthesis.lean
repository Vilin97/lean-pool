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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation

/-!
# Fourier Synthesis: Smoothness, Sup-Norm Bound, and Basic Properties

**Main result.** Let `k ∈ ℕ` and `s ∈ ℝ` with `2s > n`. For each
`a ∈ ℓ²_(s+k)(ℤⁿ)`, the Fourier series `ǎ(θ) = ∑ aₘ eₘ(θ)` defines a
function of class `Cᵏ` that is `2π`-periodic in each variable, and the map
`a ↦ ǎ` is a continuous linear injection from `ℓ²_(s+k)` into `Cᵏ(ℝⁿ; ℂ)`.

We prove a concrete bound: for each multi-index `α` with `|α| ≤ k`,
`sup_θ |∂^α ǎ(θ)| ≤ C · ‖a‖_(s+k)`, where `C` depends only on `n`, `s`, `k`.
-/

open scoped BigOperators Real
open NashEmbedding.Sobolev Complex


noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The Fourier synthesis map: `ǎ(θ) = ∑ aₘ eₘ(θ)`. -/
def fourierSynthesis (n : ℕ) (a : (Fin n → ℤ) → ℂ) (θ : Fin n → ℝ) : ℂ :=
  ∑' m : Fin n → ℤ, a m * fourierExp n m θ

/-- For a multi-index `α : Fin n → ℕ`, the monomial `m^α = ∏ mⱼ^{αⱼ}`. -/
def monomialPow (m : Fin n → ℤ) (α : Fin n → ℕ) : ℤ :=
  ∏ j : Fin n, m j ^ α j

/-- The total degree `|α| = ∑ αⱼ`. -/
def multiDeg (α : Fin n → ℕ) : ℕ :=
  ∑ j : Fin n, α j

/-- The `α`-th derivative coefficient: `(im)^α aₘ`. -/
def derivCoeff (α : Fin n → ℕ) (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ :=
  (Complex.I ^ (multiDeg α)) * (monomialPow m α : ℂ) * a m

/-
Key bound: `|(im)^α| ≤ (1 + |m|²)^{k/2}` when `|α| ≤ k`.
-/
lemma norm_derivCoeff_le {k : ℕ} {α : Fin n → ℕ} (hα : multiDeg α ≤ k)
    (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    ‖derivCoeff α a m‖ ≤ weight n (k / 2 : ℝ) m * ‖a m‖ := by
  -- Apply the inequality on the absolute value of the product.
  have h_prod : ‖(∏ j, ((m j : ℂ) ^ (α j)))‖ ≤ (1 + ∑ j, (m j : ℝ) ^ 2) ^ ((∑ j, α j) / 2 : ℝ) := by
    -- Apply the inequality on the absolute value of each term in the product.
    have h_abs_term : ∀ j, ‖(m j : ℂ) ^ (α j)‖ ≤ (1 + ∑ j, (m j : ℝ) ^ 2) ^ ((α j) / 2 : ℝ) := by
      intro j
      have h_abs_term : ‖(m j : ℂ)‖ ≤ (1 + ∑ j, (m j : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
        norm_num [ ← Real.sqrt_eq_rpow ];
        apply Real.abs_le_sqrt
        have hterm := Finset.single_le_sum (fun i _ => sq_nonneg (m i : ℝ)) (Finset.mem_univ j)
        linarith only [hterm]
      convert pow_le_pow_left₀ ( norm_nonneg _ ) h_abs_term ( α j ) using 1
      all_goals (first
        | rfl
        | (norm_num; done)
        | (rw [← Real.rpow_natCast _ (α j), ← Real.rpow_mul
              (add_nonneg zero_le_one <| Finset.sum_nonneg fun _ _ => sq_nonneg _)];
           congr 1; ring))
    simpa [ Finset.sum_div _ _ _, Real.rpow_sum_of_pos ( add_pos_of_pos_of_nonneg zero_lt_one <|
        Finset.sum_nonneg fun _ _ => sq_nonneg _ ) ] using Finset.prod_le_prod₀ ( fun _ _ =>
        norm_nonneg _ ) fun j ( hj : j ∈ Finset.univ ) => h_abs_term j;
  convert mul_le_mul_of_nonneg_right h_prod ( show 0 ≤ ‖a m‖ by positivity ) |> le_trans <| ?_
      using 1
  · unfold derivCoeff
    unfold monomialPow; norm_num [ Complex.norm_exp ]
  · gcongr
    apply Real.rpow_le_rpow_of_exponent_le
      (le_add_of_nonneg_right <| Finset.sum_nonneg fun _ _ => sq_nonneg _)
    rw [div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2)]
    exact_mod_cast hα

/-
If `a ∈ ℓ²_(s+k)` and `|α| ≤ k`, then `m ↦ (im)^α aₘ` is in `ℓ²_(s)`.
-/
lemma memSobolev_derivCoeff {s : ℝ} {k : ℕ} {α : Fin n → ℕ}
    (hα : multiDeg α ≤ k)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + k) a) :
    MemSobolev n s (derivCoeff α a) := by
  refine .of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg s m ) ( sq_nonneg _ ) ) ( fun m
      => ?_ ) ( ha.mul_left ( 1 : ℝ ) );
  have hXp : (0 : ℝ) < 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h_weight_split : weight n (s + ↑k) m
                      = weight n s m * weight n ((↑k : ℝ) * (1/2)) m ^ 2 := by
    unfold weight
    rw [pow_two, ← Real.rpow_add hXp, ← Real.rpow_add hXp]
    congr 1; ring
  convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( norm_nonneg _ ) ( norm_derivCoeff_le hα
      a m ) 2 ) ( weight_nonneg s m ) using 1
  all_goals (first
    | rfl
    | (ring!; done)
    | (rw [h_weight_split]; ring))

/-
If `a ∈ ℓ²_(s+k)`, `2s > n`, and `|α| ≤ k`, then `m ↦ (im)^α aₘ ∈ ℓ¹`.
-/
lemma summable_norm_derivCoeff {s : ℝ} {k : ℕ} {α : Fin n → ℕ}
    (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    (hα : multiDeg α ≤ k)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + k) a) :
    Summable (fun m : Fin n → ℤ => ‖derivCoeff α a m‖) := by
  -- By memSobolev_derivCoeff, derivCoeff α a ∈ ℓ²_(s).
  have h_mem : MemSobolev n s (derivCoeff α a) := by
    exact memSobolev_derivCoeff hα ha;
  exact summable_norm_of_memSobolev hn hs h_mem

/-
**Sup-norm bound for Fourier synthesis.** If `a ∈ ℓ²_(s+k)`, `2s > n`, and
`|α| ≤ k`, then `sup_θ |∂^α ǎ(θ)| ≤ C · ‖a‖_(s+k)` where the constant
`C = (∑ (1+|m|²)^{-s})^{1/2}` depends only on `n` and `s`.
-/
theorem fourierSynthesis_supBound {s : ℝ} {k : ℕ} {α : Fin n → ℕ}
    (hn : 0 < n) (hs : (n : ℝ) < 2 * s) (hα : multiDeg α ≤ k)
    {a : (Fin n → ℤ) → ℂ} (ha : MemSobolev n (s + k) a)
    (θ : Fin n → ℝ) :
    ‖∑' m : Fin n → ℤ, derivCoeff α a m * fourierExp n m θ‖ ≤
      (∑' m : Fin n → ℤ, weight n (-s) m) ^ (1/2 : ℝ) *
        sobolevNormSq n (s + k) a ^ (1/2 : ℝ) := by
  -- Apply the Cauchy-Schwarz inequality to the sum.
  have h_cauchy_schwarz : (∑' m : Fin n → ℤ, ‖derivCoeff α a m‖) ^ 2 ≤ (∑' m : Fin n → ℤ, weight
      n (-s) m) * (∑' m : Fin n → ℤ, weight n (s : ℝ) m * ‖derivCoeff α a m‖ ^ 2) := by
    convert tsum_norm_sq_le hn hs ( memSobolev_derivCoeff hα ha ) using 1
    simp [sobolevNormSq]
  -- Apply the norm_derivCoeff_le bound to the sum.
  have h_norm_derivCoeff_le_sum : (∑' m : Fin n → ℤ, weight n s m * ‖derivCoeff α a m‖ ^ 2) ≤
      (∑' m : Fin n → ℤ, weight n (s + k) m * ‖a m‖ ^ 2) := by
    have h_norm_derivCoeff_le_sum : ∀ m : Fin n → ℤ, weight n s m * ‖derivCoeff α a m‖ ^ 2 ≤
        weight n (s + k) m * ‖a m‖ ^ 2 := by
      intro m
      have h_norm_derivCoeff_le : ‖derivCoeff α a m‖ ≤ weight n (k / 2 : ℝ) m * ‖a m‖ := by
        convert norm_derivCoeff_le hα a m using 1;
      have hXp : (0 : ℝ) < 1 + ∑ i : Fin n, ((m i : ℝ) ^ 2) :=
        add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have h_pow_sq_div : ((1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) ^ ((↑k : ℝ) / 2)) ^ 2
                       = (1 + ∑ i : Fin n, ((m i : ℝ) ^ 2)) ^ ((↑k : ℝ)) := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hXp.le]
        congr 1; push_cast; ring
      convert mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( norm_nonneg _ )
          h_norm_derivCoeff_le 2 ) ( weight_nonneg s m ) using 1
      all_goals (first
        | rfl
        | (ring; done)
        | (unfold weight
           rw [mul_pow, h_pow_sq_div, ← mul_assoc, ← Real.rpow_add hXp]))
    apply_rules [ Summable.tsum_le_tsum ];
    exact Summable.of_nonneg_of_le ( fun m => mul_nonneg ( weight_nonneg _ _ ) ( sq_nonneg _ ) )
        h_norm_derivCoeff_le_sum ha;
  -- Apply the triangle inequality to the sum.
  have h_triangle : ‖∑' m : Fin n → ℤ, derivCoeff α a m * fourierExp n m θ‖ ≤ ∑' m : Fin n → ℤ,
      ‖derivCoeff α a m‖ := by
    convert sup_norm_fourierSeries_le _ θ using 1;
    convert summable_norm_derivCoeff hn hs hα ha using 1;
  convert h_triangle.trans ( Real.le_sqrt_of_sq_le h_cauchy_schwarz ) |> le_trans <|
      Real.sqrt_le_sqrt <| mul_le_mul_of_nonneg_left h_norm_derivCoeff_le_sum <| tsum_nonneg fun
      _ => weight_nonneg _ _ using 1
  all_goals (first
    | rfl
    | (unfold sobolevNormSq
       rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul (tsum_nonneg fun _ =>
           weight_nonneg _ _)]))

/-- **Fourier synthesis: 2π-periodicity.** The Fourier synthesis `ǎ` is
`2π`-periodic in each variable. -/
theorem fourierSynthesis_periodic
    {a : (Fin n → ℤ) → ℂ} 
    (θ : Fin n → ℝ) (j : Fin n) :
    fourierSynthesis n a (Function.update θ j (θ j + 2 * π)) =
      fourierSynthesis n a θ := by
  simp only [fourierSynthesis]
  exact tsum_congr fun m => by rw [fourierExp_add_two_pi]

/-
**Fourier synthesis: linearity.** The map `a ↦ ǎ` is linear.
-/
theorem fourierSynthesis_add
    {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (hb : Summable (fun m => ‖b m‖))
    (θ : Fin n → ℝ) :
    fourierSynthesis n (a + b) θ = fourierSynthesis n a θ + fourierSynthesis n b θ := by
  unfold fourierSynthesis;
  rw [ ← Summable.tsum_add ];
  · exact tsum_congr fun m => add_mul _ _ _;
  · exact .of_norm <| by simpa [ norm_fourierExp ] using ha;
  · exact .of_norm <| by simpa [ norm_fourierExp ] using hb

theorem fourierSynthesis_smul
    {a : (Fin n → ℤ) → ℂ} (c : ℂ)
    
    (θ : Fin n → ℝ) :
    fourierSynthesis n (c • a) θ = c * fourierSynthesis n a θ := by
  unfold fourierSynthesis;
  simp +decide [ mul_assoc, mul_left_comm, ← tsum_mul_left ]

/-
**Fourier synthesis: injectivity.** If `ǎ = 0` then `a = 0`, provided
`a ∈ ℓ¹`.
-/
theorem fourierSynthesis_injective
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (h : ∀ θ : Fin n → ℝ, fourierSynthesis n a θ = 0) :
    a = 0 := by
  apply funext;
  have h_inner : ∀ m₀ : Fin n → ℤ, ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
      fourierSynthesis n a θ * starRingEnd ℂ (fourierExp n m₀ θ) = (2 * Real.pi) ^ n * a m₀ := by
    intro m₀
    have h_fourier_coeff_inner : ∀ m : Fin n → ℤ, ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2
        * Real.pi • 1), fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) = if m = m₀ then (2
        * Real.pi) ^ n else 0 := by
      intro m
      have h_fourier_coeff_inner : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
          Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = if m = m₀ then (2 *
          Real.pi) ^ n else 0 := by
        split_ifs with h;
        · simp +decide only [Algebra.mul_smul_comm, mul_one, h, sub_self, zero_mul, Finset.sum_const_zero, ofReal_zero, mul_zero, exp_zero, MeasureTheory.integral_const, MeasureTheory.measureReal_def, MeasurableSet.univ, MeasureTheory.Measure.restrict_apply, Set.univ_inter, real_smul, ofReal_pow, ofReal_mul, ofReal_ofNat];
          erw [ Real.volume_Icc_pi ] ; norm_num [ mul_comm ];
          rw [ ENNReal.toReal_ofReal ( by positivity ) ] ; norm_num;
        · -- Since $m \neq m₀$, there exists some $j$ such that $m_j \neq m₀_j$.
          obtain ⟨j, hj⟩ : ∃ j : Fin n, m j ≠ m₀ j := by
            exact Function.ne_iff.mp h;
          have h_integral_zero : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
              Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = (∏ j, ∫ θ_j : ℝ
              in Set.Icc 0 (2 * Real.pi), Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) *
              θ_j)) := by
            have h_integral_zero : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
                Complex.exp (Complex.I * (∑ j, ((m j : ℝ) - (m₀ j : ℝ)) * θ j)) = ∫ θ : Fin n →
                ℝ, (∏ j, (if 0 ≤ θ j ∧ θ j ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m j :
                ℝ) - (m₀ j : ℝ)) * θ j) else 0)) := by
              rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
              congr with θ ; simp +decide only [Pi.le_def, Pi.zero_apply, Pi.smul_apply, Pi.ofNat_apply, smul_eq_mul];
              split_ifs <;> simp_all +decide [ mul_assoc, mul_comm, mul_left_comm,
                  Finset.prod_ite ];
              · rw [ ← Complex.exp_sum, Finset.mul_sum _ _ _ ];
              · grind;
            have h_integral_zero : ∫ θ : Fin n → ℝ, (∏ j, (if 0 ≤ θ j ∧ θ j ≤ 2 * Real.pi then
                Complex.exp (Complex.I * ((m j : ℝ) - (m₀ j : ℝ)) * θ j) else 0)) = ∏ j, ∫ θ_j :
                ℝ, (if 0 ≤ θ_j ∧ θ_j ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m j : ℝ) -
                (m₀ j : ℝ)) * θ_j) else 0) := by
              rw [ ← MeasureTheory.integral_fintype_prod_eq_prod ];
              rfl;
            simp_all +decide [ ← MeasureTheory.integral_indicator, Set.indicator_apply ];
          have h_integral_zero : ∫ θ_j : ℝ in Set.Icc 0 (2 * Real.pi), Complex.exp (Complex.I *
              ((m j : ℝ) - (m₀ j : ℝ)) * θ_j) = 0 := by
            rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le
                Real.two_pi_pos.le ];
            have := @integral_exp_mul_complex 0 ( 2 * Real.pi );
            have hz : I * ((m j : ℂ) - (m₀ j : ℂ)) * (2 * (π : ℂ))
                    = ((m j - m₀ j : ℤ) : ℂ) * (2 * π * I) := by push_cast; ring
            convert this ( show ( I * ( m j - m₀ j : ℂ ) ) ≠ 0 from mul_ne_zero
                Complex.I_ne_zero <| sub_ne_zero_of_ne <| mod_cast hj ) using 1
            all_goals (first
              | rfl
              | (norm_num; done)
              | (push_cast; ring; done)
              | (symm
                 rw [div_eq_zero_iff]
                 left
                 simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
                 push_cast
                 exact sub_eq_zero.mpr (Complex.exp_eq_one_iff.mpr ⟨m j - m₀ j, hz⟩)));
          simp_all +decide [ Finset.prod_eq_zero ( Finset.mem_univ j ) ];
      convert h_fourier_coeff_inner using 3 ; norm_num [ fourierExp ] ; ring;
      norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Finset.sum_sub_distrib ];
      exact ⟨ by rw [ Real.cos_sub ], by rw [ Real.sin_sub ] ; ring ⟩;
    have h_fourier_coeff_inner : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
        ∑' m : Fin n → ℤ, a m * fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) = ∑' m :
        Fin n → ℤ, a m * ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1),
        fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) := by
      rw [ MeasureTheory.integral_tsum ];
      · simp +decide only [mul_assoc, MeasureTheory.integral_const_mul];
      · intro m; exact Continuous.aestronglyMeasurable ( by
          refine Continuous.mul ?_ ?_;
          · refine continuous_const.mul ?_;
            exact Complex.continuous_exp.comp <| Continuous.mul continuous_const <|
                Complex.continuous_ofReal.comp <| continuous_finsetSum _ fun _ _ =>
                Continuous.mul ( continuous_const ) <| continuous_apply _;
          · exact Complex.continuous_conj.comp ( Complex.continuous_exp.comp <| by continuity ) ) ;
      · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
          (g := fun m => ENNReal.ofReal (‖a m‖ * (2 * Real.pi) ^ n)) (fun m => ?_)) ?_)

        · refine le_trans (MeasureTheory.lintegral_mono
            (g := fun _ => ENNReal.ofReal ‖a m‖) (fun x => ?_)) ?_

          · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ norm_fourierExp ];
            finiteness;
          · simp +decide only [mul_comm, Algebra.smul_mul_assoc, one_mul, ofReal_norm, MeasureTheory.lintegral_const, MeasurableSet.univ, MeasureTheory.Measure.restrict_apply, Set.univ_inter, norm_nonneg, ENNReal.ofReal_mul, Nat.ofNat_pos, mul_nonneg_iff_of_pos_right, Real.pi_pos.le, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat];
            erw [ Real.volume_Icc_pi ] ; norm_num [ mul_comm, Real.pi_pos.le ];
        · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
          · exact fun m => mul_nonneg ( norm_nonneg _ ) ( pow_nonneg ( by positivity ) _ );
          · exact ha.mul_right _;
    convert h_fourier_coeff_inner using 1;
    · simp +decide only [fourierSynthesis, ← tsum_mul_right];
    · rw [ tsum_eq_single m₀ ] <;> simp_all +decide [ mul_comm ];
  simp_all +decide [ mul_eq_zero, Real.pi_ne_zero ]

end NashEmbedding.Sobolev

end
