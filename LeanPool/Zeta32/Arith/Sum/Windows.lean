/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Arith.Sum.PNT.PrimeWeightedAbel

/-! Prime sums over windows `n/u₂ < p ≤ n/u₁` (the proof notes, §8.5, Lemma 11),
in the parametrisation `u = n/p`.

* `logSum (n/u₂) (n/u₁) / n → 1/u₁ − 1/u₂`       (θ(y) ~ y)
* `wsum (n/u₂) (n/u₁) / n² → (1/u₁² − 1/u₂²)/2`  (Abel summation with `f(t) = t`)
* `lsum (n/u₂) (n/u₁) → log (u₂/u₁)`              (Abel summation with `f(t) = 1/t`)

and the resulting limit of one "piece" `∑ (A n + B p + C n²/p) log p`, plus the splitting of a
window
into consecutive pieces. -/

public section

open Finset Filter Topology MeasureTheory Set Real Asymptotics

namespace Zeta32.ArithSum.PrimeSums
noncomputable section

/-- `∑_{a < p ≤ b} (log p)/p`. -/
def lsum (a b : ℝ) : ℝ := ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, (k : ℝ)⁻¹ * cPrime k

lemma cPrime_nonneg (k : ℕ) : 0 ≤ cPrime k := by
  unfold cPrime
  split_ifs with h
  · exact Real.log_nonneg (by exact_mod_cast h.one_lt.le)
  · exact le_rfl

/-! ### Abel summation for `f(t) = 1/t` -/

lemma lsum_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    lsum a b = b⁻¹ * Chebyshev.theta b - a⁻¹ * Chebyshev.theta a -
      ∫ t in Set.Ioc a b, deriv (fun t : ℝ => t⁻¹) t * Chebyshev.theta t := by
  unfold lsum
  have hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (fun t : ℝ => t⁻¹) t := fun t ht =>
    differentiableAt_inv (ne_of_gt (ha.trans_le ht.1))
  have hint : IntegrableOn (deriv fun t : ℝ => t⁻¹) (Set.Icc a b) := by
    rw [deriv_inv']
    refine ContinuousOn.integrableOn_Icc ?_
    refine ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) ?_)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1))
  have h := sum_mul_eq_sub_sub_integral_mul cPrime (f := fun t : ℝ => t⁻¹) ha.le hab hd hint
  rw [h, ← theta_eq_sum_Icc_cPrime, ← theta_eq_sum_Icc_cPrime]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [theta_eq_sum_Icc_cPrime t]

lemma lsum_close {a b η : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ y ∈ Set.Icc a b, |Chebyshev.theta y - y| ≤ η * y) :
    |lsum a b - Real.log (b / a)| ≤ η * (2 + Real.log (b / a)) := by
  have hb : 0 < b := ha.trans_le hab
  rw [lsum_eq ha hab]
  set g : ℝ → ℝ := deriv (fun t : ℝ => t⁻¹) with hg
  have hgt : ∀ t, g t = -(t ^ 2)⁻¹ := fun t => by rw [hg, deriv_inv]
  have hgc : ContinuousOn g (Set.Icc a b) := by
    rw [show g = fun t => -(t ^ 2)⁻¹ from funext hgt]
    refine ContinuousOn.neg (ContinuousOn.inv₀ (continuousOn_pow 2) ?_)
    intro t ht
    exact pow_ne_zero 2 (ne_of_gt (ha.trans_le ht.1))
  have hgI : IntegrableOn g (Set.Icc a b) := hgc.integrableOn_Icc
  -- integrability of `g * θ` and of `g * id`
  have hθI : IntegrableOn (fun t => g t * Chebyshev.theta t) (Set.Ioc a b) := by
    have := integrableOn_mul_sum_Icc cPrime (m := 0) ha.le hgI
    refine (this.mono_set Set.Ioc_subset_Icc_self).congr_fun (fun t _ => ?_) measurableSet_Ioc
    simp only
    rw [theta_eq_sum_Icc_cPrime t]
  have hidI : IntegrableOn (fun t => g t * t) (Set.Ioc a b) :=
    ((hgc.mul continuousOn_id).integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hinvI : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc a b) := by
    refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    exact ContinuousOn.inv₀ continuousOn_id fun t ht => ne_of_gt (ha.trans_le ht.1)
  -- `∫ g t * t = - log (b/a)`
  have hlog : ∫ t in Set.Ioc a b, t⁻¹ = Real.log (b / a) := by
    rw [← intervalIntegral.integral_of_le hab, integral_inv_of_pos ha hb]
  have hJ : ∫ t in Set.Ioc a b, g t * t = -Real.log (b / a) := by
    rw [← hlog, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht0 : t ≠ 0 := ne_of_gt (ha.trans ht.1)
    simp only [hgt]
    field_simp
  -- the integral error
  have hI : |(∫ t in Set.Ioc a b, g t * Chebyshev.theta t) - (-Real.log (b / a))| ≤
      η * Real.log (b / a) := by
    rw [← hJ, ← integral_sub hθI hidI]
    calc |∫ t in Set.Ioc a b, (g t * Chebyshev.theta t - g t * t)|
        = ‖∫ t in Set.Ioc a b, (g t * Chebyshev.theta t - g t * t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ t in Set.Ioc a b, ‖g t * Chebyshev.theta t - g t * t‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ t in Set.Ioc a b, η * t⁻¹ := by
          refine setIntegral_mono_on (hθI.sub hidI).norm (hinvI.const_mul η) measurableSet_Ioc
            fun t ht => ?_
          have ht0 : 0 < t := ha.trans ht.1
          have hh := h t (Set.Ioc_subset_Icc_self ht)
          rw [Real.norm_eq_abs, ← mul_sub, abs_mul, hgt, abs_neg,
            abs_of_pos (inv_pos.mpr (pow_pos ht0 2))]
          calc (t ^ 2)⁻¹ * |Chebyshev.theta t - t| ≤ (t ^ 2)⁻¹ * (η * t) :=
                mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr (sq_nonneg t))
            _ = η * t⁻¹ := by field_simp
      _ = η * Real.log (b / a) := by rw [integral_const_mul, hlog]
  -- endpoint terms
  have hbθ := h b ⟨hab, le_rfl⟩
  have haθ := h a ⟨le_rfl, hab⟩
  have e1 : |b⁻¹ * Chebyshev.theta b - 1| ≤ η := by
    rw [show b⁻¹ * Chebyshev.theta b - 1 = b⁻¹ * (Chebyshev.theta b - b) by field_simp,
      abs_mul, abs_of_pos (inv_pos.mpr hb)]
    calc b⁻¹ * |Chebyshev.theta b - b| ≤ b⁻¹ * (η * b) :=
          mul_le_mul_of_nonneg_left hbθ (inv_nonneg.mpr hb.le)
      _ = η := by field_simp
  have e2 : |a⁻¹ * Chebyshev.theta a - 1| ≤ η := by
    rw [show a⁻¹ * Chebyshev.theta a - 1 = a⁻¹ * (Chebyshev.theta a - a) by field_simp,
      abs_mul, abs_of_pos (inv_pos.mpr ha)]
    calc a⁻¹ * |Chebyshev.theta a - a| ≤ a⁻¹ * (η * a) :=
          mul_le_mul_of_nonneg_left haθ (inv_nonneg.mpr ha.le)
      _ = η := by field_simp
  rw [abs_le] at e1 e2 hI ⊢
  constructor <;> nlinarith [e1.1, e1.2, e2.1, e2.2, hI.1, hI.2]

/-! ### Window limits in the parametrisation `u = n/p` -/

export Zeta5Irrational (wsum_tendsto)

theorem lsum_tendsto {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun K : ℝ => lsum (K / d) (K / c)) atTop (𝓝 (Real.log (d / c))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hd : 0 < d := hc.trans_le hcd
  have hL : 0 ≤ Real.log (d / c) := Real.log_nonneg (by rw [le_div_iff₀ hc]; linarith)
  set η := ε / (2 * (2 + Real.log (d / c))) with hη_def
  have hη : 0 < η := by positivity
  obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp (theta_eventually_close hη)
  refine ⟨max (d * Y₀) 1, fun K hK => ?_⟩
  have hK1 : 1 ≤ K := le_trans (le_max_right _ _) hK
  have hK0 : 0 < K := by linarith
  have hKY : d * Y₀ ≤ K := le_trans (le_max_left _ _) hK
  have ha : 0 < K / d := by positivity
  have hab : K / d ≤ K / c := div_le_div_of_nonneg_left hK0.le hc hcd
  have hbound := lsum_close ha hab (fun y hy => hY₀ y (by
    have : Y₀ ≤ K / d := by rw [le_div_iff₀ hd]; linarith
    linarith [hy.1]))
  have hq : K / c / (K / d) = d / c := by field_simp
  rw [hq] at hbound
  rw [Real.dist_eq]
  calc |lsum (K / d) (K / c) - Real.log (d / c)| ≤ η * (2 + Real.log (d / c)) := hbound
    _ = ε / 2 := by rw [hη_def]; field_simp
    _ < ε := by linarith

theorem logSum_tendsto {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) :
    Tendsto (fun K : ℝ => logSum (K / d) (K / c) / K) atTop (𝓝 (1 / c - 1 / d)) := by
  have hd : 0 < d := hc.trans_le hcd
  have h := logSum_scaled_tendsto (a := d⁻¹) (b := c⁻¹) (inv_pos.mpr hd)
    (inv_anti₀ hc hcd)
  have e : (fun K : ℝ => logSum (d⁻¹ * K) (c⁻¹ * K) / K) = fun K => logSum (K / d) (K / c) / K := by
    funext K
    rw [div_eq_inv_mul K d, div_eq_inv_mul K c]
  rw [e] at h
  simpa only [one_div] using h

/-! ### One piece -/

/-- `∑_{n/u₂ < p ≤ n/u₁} (A n + B p + C n²/p) log p`. -/
def pieceSum (A B C u₁ u₂ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Ioc ⌊(n : ℝ) / u₂⌋₊ ⌊(n : ℝ) / u₁⌋₊,
    (A * n + B * k + C * (n : ℝ) ^ 2 / k) * cPrime k

/-- The normalised limit of one piece. -/
@[expose]
def pieceLim (A B C u₁ u₂ : ℝ) : ℝ :=
  A * (1 / u₁ - 1 / u₂) + B * ((1 / u₁ ^ 2 - 1 / u₂ ^ 2) / 2) + C * Real.log (u₂ / u₁)

lemma pieceSum_eq (A B C u₁ u₂ : ℝ) (n : ℕ) :
    pieceSum A B C u₁ u₂ n = A * n * logSum ((n : ℝ) / u₂) ((n : ℝ) / u₁) +
      B * wsum ((n : ℝ) / u₂) ((n : ℝ) / u₁) + C * (n : ℝ) ^ 2 * lsum ((n : ℝ) / u₂) ((n : ℝ) /
        u₁) := by
  unfold pieceSum logSum wsum lsum
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pieceSum_tendsto (A B C : ℝ) {u₁ u₂ : ℝ} (hu₁ : 0 < u₁) (hu : u₁ < u₂) :
    Tendsto (fun n : ℕ => pieceSum A B C u₁ u₂ n / (n : ℝ) ^ 2) atTop
      (𝓝 (pieceLim A B C u₁ u₂)) := by
  have hL := ((logSum_tendsto hu₁ hu.le).comp tendsto_natCast_atTop_atTop).const_mul A
  have hW := ((wsum_tendsto hu₁ hu).comp tendsto_natCast_atTop_atTop).const_mul B
  have hS := ((lsum_tendsto hu₁ hu.le).comp tendsto_natCast_atTop_atTop).const_mul C
  have h := (hL.add hW).add hS
  unfold pieceLim
  refine (tendsto_congr' ?_).mp h
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [Function.comp, pieceSum_eq]
  field_simp

/-! ### Splitting a window into consecutive pieces -/

lemma floor_div_anti {x s t : ℝ} (hx : 0 ≤ x) (hs : 0 < s) (hst : s ≤ t) :
    ⌊x / t⌋₊ ≤ ⌊x / s⌋₊ :=
  Nat.floor_le_floor (div_le_div_of_nonneg_left hx hs hst)

theorem sum_split_pieces (F : ℕ → ℝ) (t : ℕ → ℝ) (x : ℝ) (hx : 0 ≤ x) (ht0 : 0 < t 0) :
    ∀ N : ℕ, (∀ i < N, t i ≤ t (i + 1)) →
      ∑ k ∈ Finset.Ioc ⌊x / t N⌋₊ ⌊x / t 0⌋₊, F k =
        ∑ i ∈ Finset.range N, ∑ k ∈ Finset.Ioc ⌊x / t (i + 1)⌋₊ ⌊x / t i⌋₊, F k := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hmono
    have hmono' : ∀ i < N, t i ≤ t (i + 1) := fun i hi => hmono i (by omega)
    have hle : ∀ i ≤ N, t 0 ≤ t i := by
      intro i hi
      induction i with
      | zero => exact le_rfl
      | succ i ihi => exact (ihi (by omega)).trans (hmono i (by omega))
    have htN : 0 < t N := ht0.trans_le (hle N le_rfl)
    rw [Finset.sum_range_succ, ← ih hmono',
      ← Finset.sum_Ioc_consecutive _ (floor_div_anti hx htN (hmono N (by omega)))
        (floor_div_anti hx ht0 (hle N le_rfl)), add_comm]

/-- If the summand agrees on piece `i` with `(A i) n + (B i) k + (C i) n²/k` (times `cPrime k`),
the window
sum is the sum of the pieces, and its normalised limit is the sum of the piece limits. -/
theorem window_tendsto (f : ℕ → ℕ → ℝ) (t A B C : ℕ → ℝ) (N : ℕ) (ht0 : 0 < t 0)
    (hmono : ∀ i < N, t i < t (i + 1))
    (hf : ∀ n : ℕ, 0 < n → ∀ i < N, ∀ k ∈ Finset.Ioc ⌊(n : ℝ) / t (i + 1)⌋₊ ⌊(n : ℝ) / t i⌋₊,
      f n k * cPrime k = (A i * n + B i * k + C i * (n : ℝ) ^ 2 / k) * cPrime k) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Ioc ⌊(n : ℝ) / t N⌋₊ ⌊(n : ℝ) / t 0⌋₊, f n k * cPrime k) /
      (n : ℝ) ^ 2) atTop (𝓝 (∑ i ∈ Finset.range N, pieceLim (A i) (B i) (C i) (t i) (t (i +
        1)))) := by
  have hpos : ∀ i ≤ N, 0 < t i := by
    intro i hi
    induction i with
    | zero => exact ht0
    | succ i ihi => exact (ihi (by omega)).trans (hmono i (by omega))
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range N,
      pieceSum (A i) (B i) (C i) (t i) (t (i + 1)) n / (n : ℝ) ^ 2) atTop
      (𝓝 (∑ i ∈ Finset.range N, pieceLim (A i) (B i) (C i) (t i) (t (i + 1)))) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hi' := Finset.mem_range.mp hi
    exact pieceSum_tendsto _ _ _ (hpos i hi'.le) (hmono i hi')
  refine (tendsto_congr' ?_).mp hlim
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [sum_split_pieces _ t _ (Nat.cast_nonneg n) ht0 N (fun i hi => (hmono i hi).le),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  unfold pieceSum
  exact (Finset.sum_congr rfl (hf n hn i (Finset.mem_range.mp hi))).symm

end
end Zeta32.ArithSum.PrimeSums

end
