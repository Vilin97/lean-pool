/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wiygul
-/
module


/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Tactic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Basic
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Summability
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Differentiation

/-!
# Fourier Synthesis: Smoothness, Sup-Norm Bound, and Basic Properties

**Main result.** Let `k ∈ ℕ` and `s ∈ ℝ` with `2s > n`. For each
`a ∈ ℓ²_(s+k)(ℤⁿ)`, the Fourier series `a_check(θ) = ∑ aₘ eₘ(θ)` defines a
function of class `Cᵏ` that is `2π`-periodic in each variable, and the map
`a ↦ a_check` is a continuous linear injection from `ℓ²_(s+k)` into `Cᵏ(ℝⁿ; ℂ)`.

We prove a concrete bound: for each multi-index `α` with `|α| ≤ k`,
`sup_θ |∂^α a_check(θ)| ≤ C · ‖a‖_(s+k)`, where `C` depends only on `n`, `s`, `k`.
-/

@[expose] public section

open scoped BigOperators Real
open NashEmbedding.Sobolev Complex


noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-- The Fourier synthesis map: `a_check(θ) = ∑ aₘ eₘ(θ)`. -/
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
`|α| ≤ k`, then `sup_θ |∂^α a_check(θ)| ≤ C · ‖a‖_(s+k)` where the constant
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

/-- **Fourier synthesis: 2π-periodicity.** The Fourier synthesis `a_check` is
`2π`-periodic in each variable. -/
theorem fourierSynthesis_periodic
    {a : (Fin n → ℤ) → ℂ}
    (θ : Fin n → ℝ) (j : Fin n) :
    fourierSynthesis n a (Function.update θ j (θ j + 2 * π)) =
      fourierSynthesis n a θ := by
  simp only [fourierSynthesis]
  exact tsum_congr fun m => by rw [fourierExp_add_two_pi]

/-
**Fourier synthesis: linearity.** The map `a ↦ a_check` is linear.
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
  simp +decide [ mul_assoc,  ← tsum_mul_left ]

/-! ## Orthogonality of Fourier exponentials -/

/-
Orthogonality of Fourier exponentials on `[0, 2π]ⁿ`:
`∫_{[0,2π]^n} eₘ(θ) · conj(e_{m₀}(θ)) dθ = (2π)^n δ_{m,m₀}`.
-/
lemma fourierExp_inner_eq (m m₀ : Fin n → ℤ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      fourierExp n m θ * starRingEnd ℂ (fourierExp n m₀ θ) =
    if m = m₀ then ((2 * π) ^ n : ℝ) else 0 := by
  split_ifs with h;
  · simp +decide only [Algebra.mul_smul_comm, mul_one, fourierExp, ofReal_sum, ofReal_mul,
    ofReal_intCast, ← h, ofReal_pow, ofReal_ofNat];
    norm_num [ Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
    erw [ MeasureTheory.measureReal_def ];
    erw [ Real.volume_Icc_pi ]; norm_num [ mul_comm ];
    rw [ ENNReal.toReal_ofReal ( by positivity ) ]; norm_num;
  · -- Since $m \neq m_0$, there exists $j$ such that $m_j \neq m_{0,j}$.
    obtain ⟨j, hj⟩ : ∃ j : Fin n, m j ≠ m₀ j := by
      exact Function.ne_iff.mp h;
    -- The integral over the product space can be factored into a product of integrals.
    have h_prod : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp
        (Complex.I * ∑ i : Fin n, ((m i - m₀ i) : ℂ) * θ i) = ∏ i : Fin n, ∫ θ : ℝ in Set.Icc 0
        (2 * Real.pi), Complex.exp (Complex.I * ((m i - m₀ i) : ℂ) * θ) := by
      have h_prod : ∫ θ : Fin n → ℝ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • 1), Complex.exp
          (Complex.I * ∑ i : Fin n, ((m i - m₀ i) : ℂ) * θ i) = ∫ θ : Fin n → ℝ, (∏ i : Fin n,
          (if 0 ≤ θ i ∧ θ i ≤ 2 * Real.pi then Complex.exp (Complex.I * ((m i - m₀ i) : ℂ) * θ
          i) else 0)) := by
        rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator, Pi.le_def,
            forall_and ];
        congr with x; split_ifs <;> simp_all +decide only [ne_eq, mul_comm, and_self,
          ↓reduceIte, mul_left_comm, not_and, not_forall, not_le, Finset.prod_ite,
          Finset.prod_const, zero_eq_mul, pow_eq_zero_iff', Finset.card_eq_zero,
          Finset.filter_eq_empty_iff, Finset.mem_univ,  not_lt, forall_const, true_and];
        · rw [ ← Complex.exp_sum, Finset.mul_sum _ _ _ ];
        · grind;
      have h_prod : ∀ (f : Fin n → ℝ → ℂ), (∫ θ : Fin n → ℝ, ∏ i : Fin n, f i (θ i)) = ∏ i : Fin
          n, ∫ θ : ℝ, f i θ := by
        exact fun f => MeasureTheory.integral_fin_nat_prod_volume_eq_prod f;
      convert h_prod ( fun i θ => if 0 ≤ θ ∧ θ ≤ 2 * Real.pi then Complex.exp ( Complex.I * ( m
          i - m₀ i ) * θ ) else 0 ) using 1;
      exact Finset.prod_congr rfl fun _ _ => by rw [ ← MeasureTheory.integral_indicator ] <;>
          norm_num [ Set.indicator ];
    -- For $m_j \neq m_{0,j}$, the integral $\int_0^{2\pi} e^{i(m_j - m_{0,j})\theta}
    -- d\theta$ is zero.
    have h_integral_zero : ∀ j : Fin n, m j ≠ m₀ j → ∫ θ : ℝ in Set.Icc 0 (2 * Real.pi),
        Complex.exp (Complex.I * ((m j - m₀ j) : ℂ) * θ) = 0 := by
      intro j hj; rw [ MeasureTheory.integral_Icc_eq_integral_Ioc, ←
          intervalIntegral.integral_of_le Real.two_pi_pos.le ];
      have := @integral_exp_mul_complex 0 ( 2 * Real.pi );
      convert this ( show ( I * ( m j - m₀ j : ℂ ) ) ≠ 0 from mul_ne_zero Complex.I_ne_zero <|
          sub_ne_zero_of_ne <| mod_cast hj ) using 1; norm_num;
      exact Eq.symm ( div_eq_zero_iff.mpr <| Or.inl <| sub_eq_zero.mpr <|
          Complex.exp_eq_one_iff.mpr ⟨ m j - m₀ j, by push_cast; ring ⟩ );
    convert h_prod using 1;
    · unfold fourierExp; norm_num [ Complex.exp_add, Complex.exp_neg, mul_sub, sub_mul,
        Finset.sum_sub_distrib ];
      norm_num [ Complex.exp_sub, Complex.exp_neg, Complex.exp_conj ];
      norm_num [ div_eq_mul_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
    · rw [ Finset.prod_eq_zero ( Finset.mem_univ j ) ( h_integral_zero j hj ) ]; norm_num

/-! ## Fourier inversion formula -/

/-
**Fourier inversion.** If `a ∈ ℓ¹(ℤⁿ)`, then the inner product of the
Fourier synthesis `a_check(θ) = ∑ aₘ eₘ(θ)` with `conj(e_{m₀}(θ))` over
`[0, 2π]ⁿ` recovers `(2π)ⁿ · a_{m₀}`.
-/
lemma fourierSynthesis_inner
    {a : (Fin n → ℤ) → ℂ} (ha : Summable (fun m => ‖a m‖))
    (m₀ : Fin n → ℤ) :
    ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * π • (1 : Fin n → ℝ)),
      fourierSynthesis n a θ * starRingEnd ℂ (fourierExp n m₀ θ) =
    ((2 * π) ^ n : ℝ) * a m₀ := by
  -- Expand the integral using the definition of `fourierSynthesis`.
  have h_expand : ∫ θ in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • (1 : Fin n → ℝ)),
      fourierSynthesis n a θ * (starRingEnd ℂ) (fourierExp n m₀ θ) = ∑' m : Fin n → ℤ, a m * ∫ θ
      in Set.Icc (0 : Fin n → ℝ) (2 * Real.pi • (1 : Fin n → ℝ)), fourierExp n m θ *
      (starRingEnd ℂ) (fourierExp n m₀ θ) := by
    simp +decide only [fourierSynthesis, ← MeasureTheory.integral_const_mul];
    rw [ ← MeasureTheory.integral_tsum ];
    · simp +decide only [← tsum_mul_right, ← mul_assoc];
    · intro m; apply_rules [ Continuous.aestronglyMeasurable, Continuous.mul, continuous_const ];
      · exact Complex.continuous_exp.comp <| Continuous.mul continuous_const <| by continuity;
      · exact Complex.continuous_conj.comp ( Complex.continuous_exp.comp <| by continuity );
    · refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum
          (g := fun m => ENNReal.ofReal (‖a m‖ * (2 * Real.pi) ^ n)) (fun m => ?_)) ?_)
      · refine le_trans (MeasureTheory.lintegral_mono
            (g := fun _ => ENNReal.ofReal ‖a m‖) (fun x => ?_)) ?_
        · rw [ ENNReal.le_ofReal_iff_toReal_le ] <;> norm_num [ norm_fourierExp ];
          finiteness;
        · simp +decide only [Algebra.mul_smul_comm, mul_one, ofReal_norm,
          MeasureTheory.lintegral_const, MeasurableSet.univ,
          MeasureTheory.Measure.restrict_apply, Set.univ_inter, Real.volume_Icc_pi, Pi.smul_apply,
          Pi.ofNat_apply, smul_eq_mul,  sub_zero, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, mul_pow, norm_nonneg, ENNReal.ofReal_mul,
          Nat.ofNat_nonneg, pow_nonneg, ENNReal.ofReal_pow, ENNReal.ofReal_ofNat];
          rw [ ENNReal.ofReal_mul ( by positivity ), ENNReal.ofReal_pow ( by positivity ) ];
              ring_nf; norm_num;
      · rw [ ← ENNReal.ofReal_tsum_of_nonneg ] <;> norm_num;
        · exact fun m => mul_nonneg ( norm_nonneg _ ) ( pow_nonneg ( by positivity ) _ );
        · exact ha.mul_right _;
  rw [ h_expand, tsum_eq_single m₀ ];
  · rw [ mul_comm, fourierExp_inner_eq ]; norm_num;
  · intro m hm; rw [ fourierExp_inner_eq m m₀ ] ; aesop;

/-
**Fourier synthesis: injectivity.** If `a_check = 0` then `a = 0`, provided
`a ∈ ℓ¹`.
-/
theorem fourierSynthesis_injective
    {a : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖))
    (h : ∀ θ : Fin n → ℝ, fourierSynthesis n a θ = 0) :
    a = 0 := by
  funext m
  have hm := fourierSynthesis_inner ha m
  simp only [h, zero_mul, MeasureTheory.integral_zero] at hm
  apply (mul_eq_zero.mp hm.symm).resolve_left
  exact_mod_cast pow_ne_zero n (mul_ne_zero (by norm_num) Real.pi_ne_zero)

end NashEmbedding.Sobolev

end
