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
public import Mathlib.Data.Int.Star
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic
public import Mathlib.Topology.Separation.CompletelyRegular
public import LeanPool.NashEmbedding.NashEmbedding.Sobolev.Convolution

/-!
# Riemann-Sum Approximation of Convolution

This file defines the Riemann-sum operator `R^φ_M u ∈ X_n^*` and proves
its convergence to the convolution `φ * u` in `H^s_{2πℤⁿ}(ℝⁿ)` as `M → ∞`.

## Main definitions

* `meshPoint n M k` — the mesh point `(2π/M) · k` for `k ∈ {0,…,M-1}^n`
* `riemannK n u M m` — the discrete Fourier coefficient `K_M(m)`
* `riemannSumDistrib n φ u M` — the Riemann-sum operator `R^φ_M u`
* `FTRapidDecay n φ` — rapid decay of `φ̂|_{ℤⁿ}`

## Main results

* `memSobolevDistrib_riemannSumDistrib` — H^s closure of `R^φ_M u`
* `riemannSum_convergence` — `R^φ_M u → φ * u` in `H^s` as `M → ∞`
-/

@[expose] public section

open scoped BigOperators ComplexConjugate
open Complex Real NashEmbedding.Sobolev MeasureTheory


noncomputable
section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Mesh points -/

/-- The mesh point `z_k = (2π/M) · k` for index `k : Fin n → Fin M`. -/
def meshPoint (n : ℕ) (M : ℕ) (k : Fin n → Fin M) : Fin n → ℝ :=
  fun j => (2 * π / (M : ℝ)) * ((k j : ℕ) : ℝ)

/-! ## Discrete Fourier coefficient K_M(m) -/

/-- The discrete Fourier coefficient
    `K_M(m) = (2π/M)ⁿ ∑_k u_check(z_k) e^{-im·z_k}`
    where `u_check = fourierSynthesis n (fourierCoeffDistrib u)`. -/
def riemannK (n : ℕ) (u : TrigPolyDual n) (M : ℕ) (m : Fin n → ℤ) : ℂ :=
  (((2 * π / (M : ℝ)) ^ n : ℝ) : ℂ) *
    ∑ k : Fin n → Fin M,
      fourierSynthesis n (fourierCoeffDistrib u) (meshPoint n M k) *
      fourierExp n (-m) (meshPoint n M k)

/-! ## Riemann-sum operator -/

/-- The Riemann-sum operator `R^φ_M u ∈ X_n^*`, defined via Fourier coefficients:
    `(R^φ_M u)^(m) = (2π)^{-n} · φ̂(m) · K_M(m)`.
    When `supp(φ) ⊂ (-π,π)ⁿ`, this equals `integrationEmbed n (r^φ_δ u)`
    where `r^φ_δ u(x) = δⁿ ∑_z φ^per(x-z) u_check(z)`. -/
def riemannSumDistrib (n : ℕ) (φ : (Fin n → ℝ) → ℂ)
    (u : TrigPolyDual n) (M : ℕ) : TrigPolyDual n :=
  seqToDual n (fun m =>
    (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ *
    ftRn n φ (fun j => (m j : ℝ)) *
    riemannK n u M m)

/-- Fourier coefficient of the Riemann-sum operator. -/
lemma fourierCoeffDistrib_riemannSumDistrib (φ : (Fin n → ℝ) → ℂ)
    (u : TrigPolyDual n) (M : ℕ) (m : Fin n → ℤ) :
    fourierCoeffDistrib (riemannSumDistrib n φ u M) m =
      (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ *
      ftRn n φ (fun j => (m j : ℝ)) *
      riemannK n u M m :=
  congr_fun (fourierCoeffDistrib_seqToDual _) m

/-! ## Rapid decay hypothesis -/

/-- The condition that `φ̂|_{ℤⁿ}` has rapid decay: lies in `ℓ²_{(s)}` for every `s`.
    This holds for `φ ∈ C_c^∞(ℝⁿ; ℂ)` by iterated integration by parts. -/
def FTRapidDecay (n : ℕ) (φ : (Fin n → ℝ) → ℂ) : Prop :=
  ∀ s : ℝ, Summable (fun m : Fin n → ℤ =>
    weight n s m * ‖ftRn n φ (fun j => (m j : ℝ))‖ ^ 2)

/-! ## Helper: Fourier exponential multiplication -/

/-
Product of Fourier exponentials: `eₐ(θ) · e_b(θ) = e_{a+b}(θ)`.
-/
lemma fourierExp_mul (a b : Fin n → ℤ) (θ : Fin n → ℝ) :
    fourierExp n a θ * fourierExp n b θ = fourierExp n (a + b) θ := by
  unfold fourierExp;
  simp +decide [ ← Complex.exp_add, Finset.sum_add_distrib, add_mul ];
  grind +extAll

/-! ## Geometric sum for roots of unity -/

/-
For `M ≥ 1`, `∑_{j : Fin M} exp(2πi q j / M) = M` if `M ∣ q`, else `0`.
-/
lemma geom_sum_exp (M : ℕ) (hM : 0 < M) (q : ℤ) :
    ∑ j : Fin M, exp (↑(2 * π * (q : ℝ) * (j : ℕ) / (M : ℝ)) * I) =
    if (M : ℤ) ∣ q then (M : ℂ) else 0 := by
  split_ifs with hMq <;> simp_all +decide only [ofReal_div, ofReal_mul, ofReal_ofNat,
    ofReal_intCast, ofReal_natCast];
  · obtain ⟨ k, rfl ⟩ := hMq; norm_num [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv,
      hM.ne' ];
    calc
      _ = ∑ _j : Fin M, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Complex.exp_eq_one_iff]
        use k * j
        push_cast
        ring
      _ = _ := by norm_num
  · -- Let $\omega = e^{2 \pi i q / M}$. Since $M \nmid q$, $\omega \neq 1$.
    set ω : ℂ := Complex.exp (2 * Real.pi * q / M * Complex.I)
    have hω_ne_one : ω ≠ 1 := by
      rw [ Ne.eq_def, Complex.exp_eq_one_iff ];
      norm_num [ Complex.ext_iff, div_eq_iff, Real.pi_ne_zero, hM.ne' ];
      exact fun x hx => hMq <| ⟨ x, by rw [ ← @Int.cast_inj ℝ ]; push_cast; nlinarith [
          Real.pi_pos ] ⟩
    have hω_pow_M : ω ^ M = 1 := by
      rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ]; use q; ring_nf;
          norm_num [ hM.ne' ];
    -- The sum of a geometric series with common ratio $\omega$ and $M$ terms is
    -- $\frac{\omega^M - 1}{\omega - 1}$.
    have h_geo_series : ∑ j ∈ Finset.range M, ω ^ j = (ω ^ M - 1) / (ω - 1) := by
      rw [ geom_sum_eq hω_ne_one ];
    convert h_geo_series using 1 <;> norm_num [ ← Complex.exp_nat_mul, mul_div_assoc, mul_comm ];
    · rw [ Finset.sum_range ]; congr; ext; rw [ ← Complex.exp_nat_mul ]; ring;
    · rw [ hω_pow_M, sub_self, zero_div ]

/-! ## Riemann sum of a single Fourier exponential -/

/-
The Riemann sum of `e^{iℓ·θ}` over the mesh equals `Mⁿ` if `M ∣ ℓ_j` for all `j`,
    else `0`.
-/
lemma riemannSum_fourierExp (M : ℕ) (hM : 0 < M) (ℓ : Fin n → ℤ) :
    ∑ k : Fin n → Fin M,
      fourierExp n ℓ (meshPoint n M k) =
    if (∀ j, (M : ℤ) ∣ ℓ j) then ((M : ℂ) ^ n) else 0 := by
  split_ifs with h;
  · -- For each j, since M divides ℓ_j, we have ℓ_j (2π/M) k_j = 2π * (ℓ_j / M) * k_j, which is an
    -- integer multiple of 2π. Thus, exp(i ℓ_j (2π/M) k_j) = 1.
    have h_exp_one : ∀ j : Fin n, ∀ k : Fin M, Complex.exp (Complex.I * (ℓ j : ℝ) * (2 * Real.pi
        / M) * (k : ℝ)) = 1 := by
      intro j k; specialize h j; obtain ⟨ m, hm ⟩ := h; norm_num [ hm, Complex.exp_eq_one_iff ]
      ring_nf
      exact ⟨ m * k, by simp [ hM.ne', mul_assoc, mul_comm, mul_left_comm ] ⟩;
    unfold fourierExp meshPoint; simp +decide ;
    simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _, Complex.exp_sum ];
  · -- Apply the geometric sum lemma to each term in the product.
    have h_prod : ∏ j : Fin n, ∑ k : Fin M, Complex.exp (↑(2 * π * (ℓ j : ℝ) * (k : ℕ) / (M :
        ℝ)) * I) = 0 := by
      simp_all +decide only [not_forall, ofReal_div, ofReal_mul, ofReal_ofNat, ofReal_intCast,
        ofReal_natCast, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and];
      obtain ⟨ a, ha ⟩ := h; use a; have := geom_sum_exp M hM ( ℓ a ) ; aesop;
    convert h_prod using 1;
    rw [ Fintype.prod_sum ];
    unfold fourierExp meshPoint; norm_num [ ← Complex.exp_sum ] ; ring;
    simp +decide only [mul_comm, mul_assoc, Finset.mul_sum _ _ _, mul_left_comm]

/-! ## Bound on the normalized discrete Fourier coefficient -/

/-
Bound: `‖(2π)^{-n} K_M(m)‖ ≤ ∑ ‖û(k)‖`.
-/
lemma norm_riemannK_normalized_le {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u)
    (M : ℕ) (m : Fin n → ℤ) :
    ‖(((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m‖ ≤
      ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖ := by
  unfold riemannK;
  by_cases hM : M = 0 <;> simp_all +decide only [mul_comm, mul_pow, ofReal_mul, ofReal_pow,
    ofReal_ofNat, mul_inv_rev, CharP.cast_eq_zero, div_eq_mul_inv, inv_zero, mul_left_comm,
    zero_mul, mul_zero, ofReal_zero, mul_assoc, Complex.norm_mul, norm_inv, norm_pow, norm_real,
    norm_eq_abs, abs_pi, norm_zero, Complex.norm_ofNat, inv_pow, ofReal_inv, ofReal_natCast,
    ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
    mul_inv_cancel_left₀, ofReal_eq_zero, pi_ne_zero, RCLike.norm_natCast];
  · simp +decide only [ne_eq, hn.ne', not_false_eq_true, zero_pow, zero_mul, mul_zero];
    exact tsum_nonneg fun _ => norm_nonneg _;
  · refine le_trans ( mul_le_mul_of_nonneg_left ( norm_sum_le _ _ ) ( by positivity ) ) ?_;
    refine le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (g := fun _ => ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖)
        (fun _ _ => ?_)) (by positivity)) ?_
    · convert sup_norm_fourierSeries_le _ _ using 1
      · rw [norm_mul, norm_fourierExp, mul_one]
        congr! 1
      exact summable_norm_of_memSobolev hn ( by linarith ) hu;
    · norm_num [ Finset.card_univ, Fintype.card_pi ];
      rw [ ← mul_assoc, inv_mul_cancel₀ ( by positivity ), one_mul ]

/-! ## Aliasing formula -/

/-
The aliasing formula: `(2π)^{-n} K_M(m) = ∑_ℓ û(m + Mℓ)`.
-/
lemma riemannK_aliasing {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u)
    (M : ℕ) (hM : 0 < M) (m : Fin n → ℤ) :
    (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m =
    ∑' ℓ : Fin n → ℤ,
      fourierCoeffDistrib u (fun j => m j + (M : ℤ) * ℓ j) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ k : Fin n → Fin M, ∑' ℓ : Fin n → ℤ, fourierCoeffDistrib u ℓ * fourierExp n
      (ℓ - m) (meshPoint n M k) = ∑' ℓ : Fin n → ℤ, fourierCoeffDistrib u ℓ * ∑ k : Fin n → Fin
      M, fourierExp n (ℓ - m) (meshPoint n M k) := by
    have h_fubini : Summable (fun ℓ : Fin n → ℤ => ‖fourierCoeffDistrib u ℓ‖) := by
      exact summable_norm_of_memSobolev hn hs hu;
    have h_fubini : ∀ {f : (Fin n → ℤ) → (Fin n → Fin M) → ℂ}, (∀ k, Summable (fun ℓ => f ℓ k))
        → (∀ ℓ, Summable (fun k => f ℓ k)) → ∑ k, ∑' ℓ, f ℓ k = ∑' ℓ, ∑ k, f ℓ k := by
      exact fun {f} a a_1 => Eq.symm (Summable.tsum_finsetSum fun i a_2 => a i);
    convert h_fubini _ _ using 1;
    · simp +decide only [Finset.mul_sum _ _ _];
    · intro k;
      exact Summable.of_norm <| by simpa [ norm_fourierExp ] using ‹Summable fun ℓ : Fin n → ℤ
          => ‖fourierCoeffDistrib u ℓ‖›;
    · exact fun ℓ => ⟨ _, hasSum_fintype _ ⟩;
  -- Apply the result of the geometric sum to simplify the expression.
  have h_geo_sum : ∀ ℓ : Fin n → ℤ, ∑ k : Fin n → Fin M, fourierExp n (ℓ - m) (meshPoint n M k)
      = if (∀ j, (M : ℤ) ∣ (ℓ j - m j)) then ((M : ℂ) ^ n) else 0 := by
    exact fun ℓ => riemannSum_fourierExp M hM (ℓ - m);
  convert congr_arg ( fun x : ℂ => ( ( 2 * Real.pi ) ^ n : ℂ ) ⁻¹ * ( ( 2 * Real.pi / M ) ^ n :
      ℂ ) * x ) h_fubini using 1;
  · unfold riemannK;
    simp +decide [ mul_assoc, mul_comm, mul_left_comm, fourierSynthesis ];
    simp +decide [ sub_eq_add_neg, fourierExp_mul, mul_assoc, mul_comm, ← tsum_mul_left ];
  · rw [ ← tsum_mul_left ]; rw [ ← tsum_eq_tsum_of_ne_zero_bij ];
    · exact fun x => fun j => m j + M * x.val j
    · intro x y hxy; ext j; replace hxy := congr_fun hxy j; simp_all +decide only [mul_ite,
      mul_zero, add_right_inj, mul_eq_mul_left_iff, Int.natCast_eq_zero];
      exact hxy.resolve_right hM.ne';
    · intro x hx; simp_all +decide only [mul_ite, mul_zero, Function.support, ne_eq,
      ite_eq_right_iff, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff', OfNat.ofNat_ne_zero,
      ofReal_eq_zero, pi_ne_zero, or_self, false_and, div_eq_zero_iff, Nat.cast_eq_zero,
      false_or, not_imp, not_or, not_and, Decidable.not_not, Set.mem_ofPred_eq, Set.mem_range,
      Subtype.exists, exists_prop];
      have hcoord : ∀ j, m j + M * ((x j - m j) / M) = x j := by
        intro j
        rw [mul_comm, Int.ediv_mul_cancel (hx.1 j)]
        ring
      exact ⟨fun j => (x j - m j) / M, by simpa only [hcoord] using hx.2.2.1,
        funext hcoord⟩
    · simp_all +decide [ mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv ];
      field_simp;
      exact fun _ _ => by rw [ ← mul_pow, mul_div_cancel₀ _ ( by norm_cast; linarith ) ] ;

private theorem lattice_tail_norm_tendsto_zero (a : (Fin n → ℤ) → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (m : Fin n → ℤ) :
 Filter.Tendsto (fun M : ℝ => ∑' k : Fin n → ℤ, ‖a k‖ * (if ∃ j, |k j - m j| ≥ M then 1 else 0))
     Filter.atTop (nhds 0) := by
  have h_tail_zero : Filter.Tendsto (fun M : ℝ => ∑' k : Fin n → ℤ, ‖a k‖ * (if ∃ j, |k j - m j|
      ≥ M then 1 else 0)) Filter.atTop (nhds (∑' k : Fin n → ℤ, ‖a k‖ * 0)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun k => ‖a k‖) ?_ ?_ ?_
    · convert ha using 1;
    · intro k
      simp only [Int.cast_abs, Int.cast_sub, ge_iff_le, mul_ite, mul_one, mul_zero]
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_gt_atTop (∑ j : Fin n, |(k j : ℝ) - m j|)] with x hx
      have hnot : ¬ ∃ j, |(k j : ℝ) - m j| ≥ x := by
        rintro ⟨j, hj⟩
        have hjle := Finset.single_le_sum (fun a _ => abs_nonneg ((k a : ℝ) - m a))
          (Finset.mem_univ j)
        linarith
      rw [ite_eq_right hnot]
    · filter_upwards [ Filter.eventually_gt_atTop 0 ] with M hM using fun k => by split_ifs <;>
        norm_num;
  aesop;

private theorem lattice_dilate_tail_norm_le (a : (Fin n → ℤ) → ℂ)
    (ha : Summable (fun k => ‖a k‖)) (m : Fin n → ℤ) :
 ∀ M : ℕ, M ≥ 1 → ‖∑' ℓ : Fin n → ℤ, a (fun j => m j + (M : ℤ) * ℓ j) * (if ℓ ≠ 0 then 1 else
     0)‖ ≤ ∑' k : Fin n → ℤ, ‖a k‖ * (if ∃ j, |k j - m j| ≥ M then 1 else 0) := by
  intros M hM
  have h_tail_norm : ‖∑' ℓ : Fin n → ℤ, a (fun j => m j + (M : ℤ) * ℓ j) * (if ℓ ≠ 0 then 1 else
      0)‖ ≤ ∑' ℓ : Fin n → ℤ, ‖a (fun j => m j + (M : ℤ) * ℓ j)‖ * (if ℓ ≠ 0 then 1 else 0) := by
    by_cases h : Summable ( fun ℓ : Fin n → ℤ => a ( fun j => m j + M * ℓ j ) * if ℓ ≠ 0 then 1
        else 0 ) <;> simp_all +decide only [ge_iff_le, ne_eq, ite_not, mul_ite, Pi.zero_apply,
          mul_zero, add_zero, mul_one, not_false_eq_true, tsum_eq_zero_of_not_summable, norm_zero];
    · convert norm_tsum_le_tsum_norm ?_ using 1;
      · exact tsum_congr fun x => by split_ifs <;> simp +decide [ * ] ;
      · exact h.norm;
    · exact tsum_nonneg fun _ => by positivity;
  refine le_trans h_tail_norm ?_;
  have h_tail_norm : ∀ k : Fin n → ℤ, ‖a k‖ * (if ∃ j, |k j - m j| ≥ M then 1 else 0) ≥ ∑' ℓ :
      Fin n → ℤ, ‖a (fun j => m j + (M : ℤ) * ℓ j)‖ * (if k = fun j => m j + (M : ℤ) * ℓ j then
      1 else 0) * (if ℓ ≠ 0 then 1 else 0) := by
    intro k
    by_cases hk : ∃ j, |k j - m j| ≥ M;
    · rw [ tsum_eq_sum ];
      any_goals exact { fun j => ( k j - m j ) / M };
      · simp +decide [ hk ];
        grind;
      · simp +contextual only [Finset.mem_singleton, funext_iff, not_forall, mul_ite, mul_one,
        mul_zero, ne_eq, Pi.zero_apply, ite_eq_right_iff, norm_eq_zero, forall_exists_index];
        intro b x hx y hy h; specialize h x; simp_all +decide [ Int.mul_ediv_cancel_left _ ( by
            positivity : ( M : ℤ ) ≠ 0 ) ];
    · rw [ tsum_eq_single 0 ] <;> simp +contextual only [ge_iff_le, hk, ↓reduceIte, mul_zero,
      Pi.zero_apply, add_zero, mul_ite, mul_one, ne_eq, not_true_eq_false, Std.le_refl,
      not_false_eq_true, ite_eq_right_iff, norm_eq_zero];
      intro b' hb' hk'; contrapose! hk; simp_all +decide only [ge_iff_le, ne_eq, funext_iff,
        Pi.zero_apply, not_forall, mul_ite, mul_one, mul_zero, add_sub_cancel_left, abs_mul,
        Nat.abs_cast];
      exact ⟨ hb'.choose, le_mul_of_one_le_right ( by positivity ) ( mod_cast abs_pos.mpr
          hb'.choose_spec ) ⟩;
  refine le_trans ?_ ( Summable.tsum_le_tsum h_tail_norm ?_ ?_ );
  · rw [ ← Summable.tsum_comm ];
    · refine le_of_eq ?_;
      refine tsum_congr fun ℓ => ?_;
      rw [ tsum_eq_single ( fun j => m j + M * ℓ j ) ] <;> simp +contextual [ funext_iff ];
    · have h_summable : Summable (fun k : Fin n → ℤ => ‖a k‖) := by
        convert ha using 1;
      rw [ summable_iff_vanishing ] at *;
      intro e he; obtain ⟨ s, hs ⟩ := h_summable e he; use s.image fun x => ( x, fun j => ( x j
          - m j ) / M ); intro t ht; simp_all +decide only [Finset.disjoint_left, ge_iff_le,
            ne_eq, ite_not, mul_ite, Pi.zero_apply, mul_zero, add_zero, mul_one, implies_true,
            Finset.mem_image, not_exists, not_and, Prod.forall, Prod.mk.injEq];
      convert hs ( Finset.image ( fun x : ( Fin n → ℤ ) × ( Fin n → ℤ ) => fun j => m j + M *
          x.2 j ) ( t.filter fun x => x.2 ≠ 0 ∧ x.1 = fun j => m j + M * x.2 j ) ) _ using 1;
      · rw [ Finset.sum_image ];
        · rw [ Finset.sum_filter ]; congr; ext; aesop;
        · intro x hx y hy; simp_all +decide only [funext_iff, Pi.zero_apply, not_forall, ne_eq,
          Finset.coe_filter, Set.mem_ofPred_eq, add_right_inj, mul_eq_mul_left_iff,
          Int.natCast_eq_zero];
          intro h
          apply Prod.ext
          · funext i
            cases h i <;> simp_all +decide [ne_of_gt (zero_lt_one.trans_le hM)]
          · funext i
            cases h i <;> simp_all +decide [ne_of_gt (zero_lt_one.trans_le hM)]
      · simp +zetaDelta only [ne_eq, Finset.mem_image, Finset.mem_filter, Prod.exists,
        ↓existsAndEq, and_true, forall_exists_index, and_imp] at *;
        intro a x hx hx' hx''; specialize ht _ _ hx _
        · simp_all +decide only [funext_iff, Pi.zero_apply, not_forall]
          exact fun j => m j + M * x j
        simp_all +decide only [mul_comm, add_sub_cancel_left, forall_const];
        exact fun ha => ht ha <| funext fun j => by rw [ Int.mul_ediv_cancel _ ( by positivity ) ];
  · refine Summable.of_nonneg_of_le ( fun k => tsum_nonneg fun ℓ => by positivity ) ( fun k =>
      h_tail_norm k ) ?_;
    have h_summable : Summable (fun k : Fin n → ℤ => ‖a k‖) := by
      convert ha using 1;
    exact Summable.of_nonneg_of_le ( fun k => mul_nonneg ( norm_nonneg _ ) ( by positivity ) ) (
        fun k => mul_le_of_le_one_right ( norm_nonneg _ ) ( by split_ifs <;> norm_num ) )
        h_summable;
  · have h_summable : Summable (fun k : Fin n → ℤ => ‖a k‖) := by
      convert ha using 1;
    exact Summable.of_nonneg_of_le ( fun k => mul_nonneg ( norm_nonneg _ ) ( by positivity ) ) (
        fun k => mul_le_of_le_one_right ( norm_nonneg _ ) ( by split_ifs <;> norm_num ) )
        h_summable;

/-! ## Pointwise convergence of normalized K_M -/

/-
The normalized discrete Fourier sum `(2π)^{-n} K_M(m) → û(m)` as `M → ∞`.
    Via the aliasing formula, `(2π)^{-n} K_M(m) = ∑_{ℓ} û(m + Mℓ)`, and the
    tail `∑_{ℓ ≠ 0} û(m + Mℓ) → 0` by ℓ¹ summability of `û`.
-/
lemma riemannK_normalized_tendsto {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u)
    (m : Fin n → ℤ) :
    Filter.Tendsto
      (fun M : ℕ => (((2 * π : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m)
      Filter.atTop
      (nhds (fourierCoeffDistrib u m)) := by
  -- For M ≥ 1, by riemannK_aliasing:
  have halias : ∀ M ≥ 1, (((2 * Real.pi : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m = ∑' ℓ : Fin n →
      ℤ, fourierCoeffDistrib u (fun j => m j + (M : ℤ) * ℓ j) := by
    intro M hM; convert riemannK_aliasing hn hs hu M hM m using 1;
  -- The tail ∑'_{ℓ ≠ 0} û(m+Mℓ) has norm ≤ ∑_{ℓ ≠ 0} ‖û(m+Mℓ)‖ ≤ ∑_{k : ‖k-m‖_∞ ≥ M} ‖û(k)‖ →
  -- 0 since it's the tail of a convergent series (the terms escape to infinity).
  have h_tail_zero := lattice_tail_norm_tendsto_zero (fourierCoeffDistrib u)
    (summable_norm_of_memSobolev hn hs hu) m
  -- For M ≥ 1, the value equals û(m) + tail.
  have h_eq : ∀ M : ℕ, M ≥ 1 → (((2 * Real.pi : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m =
      fourierCoeffDistrib u m + ∑' ℓ : Fin n → ℤ, fourierCoeffDistrib u (fun j => m j + (M : ℤ)
      * ℓ j) * (if ℓ ≠ 0 then 1 else 0) := by
    intro M hM; rw [halias M hM, Summable.tsum_eq_add_tsum_ite]
    · simp +decide only [ne_eq, ite_not, mul_ite, mul_zero, mul_one]
      congr! 1
      norm_num
    · have := summable_norm_of_memSobolev hn hs hu;
      apply Summable.of_norm
      apply this.comp_injective
      intro a b h
      funext j
      have hj := congr_fun h j
      simpa [hM, ne_of_gt (zero_lt_one.trans_le hM)] using hj
  -- The norm of the tail is bounded by the sum of the norms of the terms in the tail.
  have h_tail_norm := lattice_dilate_tail_norm_le (fourierCoeffDistrib u)
    (summable_norm_of_memSobolev hn hs hu) m
  rw [ Metric.tendsto_nhds ] at *;
  intro ε hε; filter_upwards [ Filter.eventually_ge_atTop 1, h_tail_zero ε hε |> fun h =>
      h.natCast_atTop ] with M hM₁ hM₂; simp_all +decide only [ge_iff_le, ofReal_pow,
        ofReal_mul, ofReal_ofNat, gt_iff_lt, Int.cast_abs, Int.cast_sub, mul_ite, mul_one,
        mul_zero, dist_eq_norm, sub_zero, norm_eq_abs, Filter.eventually_atTop, ne_eq, ite_not,
        Pi.zero_apply, add_zero, add_sub_cancel_left, implies_true];
  refine lt_of_le_of_lt ( h_tail_norm M hM₁ ) ?_;
  convert lt_of_abs_lt hM₂ using 1;
  norm_cast

/-! ## H^s closure -/

/-
**H^s-closure of the Riemann-sum operator.**
    If `φ̂` has rapid decay and `u ∈ H^s` with `2s > n`, then `R^φ_M u ∈ H^s`.
-/
theorem memSobolevDistrib_riemannSumDistrib (φ : (Fin n → ℝ) → ℂ)
    (hφ : FTRapidDecay n φ)
    {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u)
    (M : ℕ) :
    MemSobolevDistrib n s (riemannSumDistrib n φ u M) := by
  refine .of_nonneg_of_le ( fun m => ?_ ) ( fun m => ?_ ) (hφ s |>.mul_right ((∑' k : Fin n → ℤ,
    ‖fourierCoeffDistrib u k‖) ^ 2))
  · exact mul_nonneg (weight_nonneg _ _) (sq_nonneg _)
  rw [ mul_assoc ];
  gcongr;
  · exact Real.rpow_nonneg ( add_nonneg zero_le_one ( Finset.sum_nonneg fun _ _ => sq_nonneg _ )
      ) _;
  · rw [ ← mul_pow ];
    gcongr;
    convert mul_le_mul_of_nonneg_left ( norm_riemannK_normalized_le hn hs hu M m ) ( norm_nonneg
        ( ftRn n φ fun j => ( m j : ℝ ) ) ) using 1;
    rw [ fourierCoeffDistrib_riemannSumDistrib ];
    norm_num [ mul_assoc, mul_comm, mul_left_comm ]

/-! ## Main convergence theorem -/

/-
**Riemann-sum convergence to convolution.** As `M → ∞`,
    `R^φ_M u → φ * u` in `H^s_{2πℤⁿ}(ℝⁿ)`:
    `sobolevNormSqDistrib n s (R^φ_M u - φ * u) → 0`.
-/
theorem riemannSum_convergence (φ : (Fin n → ℝ) → ℂ)
    (hφ_rd : FTRapidDecay n φ)
    {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {u : TrigPolyDual n} (hu : MemSobolevDistrib n s u) :
    Filter.Tendsto
      (fun M : ℕ => sobolevNormSqDistrib n s
        (riemannSumDistrib n φ u M - convDistrib n φ u))
      Filter.atTop
      (nhds 0) := by
  have h_dom : ∀ m : Fin n → ℤ, Filter.Tendsto (fun M : ℕ => ‖fourierCoeffDistrib
      (riemannSumDistrib n φ u M - convDistrib n φ u) m‖ ^ 2) Filter.atTop (nhds 0) := by
    intro m
    have h_pointwise : Filter.Tendsto (fun M : ℕ => fourierCoeffDistrib (riemannSumDistrib n φ u
        M) m - fourierCoeffDistrib (convDistrib n φ u) m) Filter.atTop (nhds 0) := by
      have h_fourier_coeff : Filter.Tendsto
          (fun M : ℕ =>
            (((2 * Real.pi : ℝ) ^ n : ℝ) : ℂ)⁻¹ * riemannK n u M m - fourierCoeffDistrib u m)
          Filter.atTop (nhds 0) := by
            convert Filter.Tendsto.sub_const ( riemannK_normalized_tendsto hn hs hu m ) (
                fourierCoeffDistrib u m ) using 2; ring!;
      convert h_fourier_coeff.const_mul ( ftRn n φ ( fun j => ( m j : ℝ ) ) ) using 2 <;>
          norm_num [ fourierCoeffDistrib_riemannSumDistrib, fourierCoeffDistrib_convDistrib ];
          ring;
    simpa [ fourierCoeffDistrib_sub ] using h_pointwise.norm.pow 2;
  have h_dom : ∀ M : ℕ, ∀ m : Fin n → ℤ, weight n s m * ‖fourierCoeffDistrib (riemannSumDistrib
      n φ u M - convDistrib n φ u) m‖ ^ 2 ≤ weight n s m * (2 * ∑' k : Fin n → ℤ,
      ‖fourierCoeffDistrib u k‖) ^ 2 * ‖ftRn n φ (fun j => (m j : ℝ))‖ ^ 2 := by
    intros M m
    have h_fourier_coeff : fourierCoeffDistrib (riemannSumDistrib n φ u M - convDistrib n φ u) m
        = ftRn n φ (fun j => (m j : ℝ)) * (((2 * π : ℝ) ^ n : ℝ)⁻¹ * riemannK n u M m -
        fourierCoeffDistrib u m) := by
      rw [ fourierCoeffDistrib_sub ]; ring!;
      rw [ fourierCoeffDistrib_riemannSumDistrib, fourierCoeffDistrib_convDistrib ]; ring!;
          norm_num [ mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero ];
      exact Or.inl <| by rw [ inv_eq_one_div, div_pow ]; norm_num;
    have h_fourier_coeff_bound : ‖(((2 * π : ℝ) ^ n : ℝ)⁻¹ * riemannK n u M m -
        fourierCoeffDistrib u m)‖ ≤ 2 * ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖ := by
      have h_fourier_coeff_bound : ‖(((2 * π : ℝ) ^ n : ℝ)⁻¹ * riemannK n u M m)‖ ≤ ∑' k : Fin n
          → ℤ, ‖fourierCoeffDistrib u k‖ := by
        convert norm_riemannK_normalized_le hn hs hu M m using 1;
        norm_num;
      have h_fourier_coeff_bound : ‖fourierCoeffDistrib u m‖ ≤ ∑' k : Fin n → ℤ,
          ‖fourierCoeffDistrib u k‖ := by
        have h_fourier_coeff_bound : Summable (fun k : Fin n → ℤ => ‖fourierCoeffDistrib u k‖) := by
          convert summable_norm_of_memSobolev hn hs hu using 1;
        exact Summable.le_tsum h_fourier_coeff_bound m ( fun _ _ => norm_nonneg _ );
      exact le_trans ( norm_sub_le _ _ ) ( by linarith );
    rw [ h_fourier_coeff, norm_mul ];
    rw [ mul_pow, mul_assoc ];
    apply mul_le_mul_of_nonneg_left _ (weight_nonneg s m)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) h_fourier_coeff_bound 2
    nlinarith only [hsq, sq_nonneg ‖ftRn n φ (fun j => (m j : ℝ))‖]
  have h_dom : Summable (fun m : Fin n → ℤ => weight n s m * (2 * ∑' k : Fin n → ℤ,
      ‖fourierCoeffDistrib u k‖) ^ 2 * ‖ftRn n φ (fun j => (m j : ℝ))‖ ^ 2) := by
    convert hφ_rd s |> Summable.mul_left ( ( 2 * ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖ ) ^
        2 ) using 2; first | rfl | ring;
  have h_ab : ∀ m : Fin n → ℤ, Filter.Tendsto (fun M : ℕ => weight n s m * ‖fourierCoeffDistrib
      (riemannSumDistrib n φ u M - convDistrib n φ u) m‖ ^ 2) Filter.atTop (nhds 0) :=
    fun m => by simpa using Filter.Tendsto.const_mul _ ( ‹∀ m : Fin n → ℤ, Filter.Tendsto ( fun
        M : ℕ => ‖fourierCoeffDistrib ( riemannSumDistrib n φ u M - convDistrib n φ u ) m‖ ^ 2 )
        Filter.atTop ( nhds 0 ) › m )
  have h_bound : ∀ᶠ M in Filter.atTop, ∀ m : Fin n → ℤ, ‖weight n s m * ‖fourierCoeffDistrib
      (riemannSumDistrib n φ u M - convDistrib n φ u) m‖ ^ 2‖ ≤ weight n s m * (2 * ∑' k : Fin n
      → ℤ, ‖fourierCoeffDistrib u k‖) ^ 2 * ‖ftRn n φ (fun j => (m j : ℝ))‖ ^ 2 := by
    filter_upwards [Filter.eventually_gt_atTop 0] with M hM
    intro m
    rw [Real.norm_of_nonneg (mul_nonneg (weight_nonneg _ _) (sq_nonneg _))]
    exact ‹∀ M : ℕ, ∀ m : Fin n → ℤ,
      weight n s m * ‖fourierCoeffDistrib (riemannSumDistrib n φ u M - convDistrib n φ u) m‖ ^ 2 ≤
        weight n s m * (2 * ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖) ^ 2 *
          ‖ftRn n φ fun j => ↑(m j)‖ ^ 2› M m
  convert tendsto_tsum_of_dominated_convergence
      (f := fun M m => weight n s m *
        ‖fourierCoeffDistrib (riemannSumDistrib n φ u M - convDistrib n φ u) m‖ ^ 2)
      (g := fun _ => (0:ℝ))
      (bound := fun m => weight n s m * (2 * ∑' k : Fin n → ℤ, ‖fourierCoeffDistrib u k‖) ^ 2 *
          ‖ftRn n φ (fun j => (m j : ℝ))‖ ^ 2)
      h_dom h_ab h_bound using 1
  all_goals first
  | rfl
  | (simp only [ tsum_zero ])

end NashEmbedding.Sobolev

end
