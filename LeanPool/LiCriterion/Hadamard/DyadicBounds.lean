/-
Copyright (c) 2026 Nicholas Bulka. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Bulka
-/
module


public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Tactic

/-!
# Weighted dyadic sum bounds

Real-power identities, shell estimates, and cofinal finite-sum bounds shared by
simple-zero and multiplicity-weighted Hadamard growth estimates.
-/

@[expose] public section

open scoped BigOperators

namespace Hadamard.DyadicBounds

/-- Rewrite a dyadic growth bound divided by a natural power as a geometric term. -/
theorem dyadic_power_quotient (Ccount lam δ : ℝ) (p k : ℕ) :
    Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) =
      ((2 : ℝ) ^ (lam + δ) * Ccount) * ((2 : ℝ) ^ (lam + δ - p)) ^ k := by
  let q : ℝ := (2 : ℝ) ^ (lam + δ - p)
  let A : ℝ := (2 : ℝ) ^ (lam + δ) * Ccount
  have hqk : q ^ k = ((2 : ℝ) ^ k) ^ (lam + δ - p) := by
    simpa [q] using
      (Real.rpow_pow_comm (x := (2 : ℝ)) (hx := by positivity) (lam + δ - p) k)
  have hpow_rat :
      ((2 : ℝ) ^ k) ^ (lam + δ - p) =
        ((2 : ℝ) ^ k) ^ (lam + δ) / ((2 : ℝ) ^ k) ^ p := by
    have hk_pos : 0 < (2 : ℝ) ^ k := by positivity
    have hsub : lam + δ - p = (lam + δ) - ((p : ℕ) : ℝ) := by
      norm_num
    have hnat : ((2 : ℝ) ^ k) ^ p = ((2 : ℝ) ^ k) ^ ((p : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    rw [hnat, hsub]
    exact Real.rpow_sub hk_pos (lam + δ) ((p : ℕ) : ℝ)
  have hrewrite :
      Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) =
        A * q ^ k := by
    have hpow_succ : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by
      simp [pow_succ, mul_comm]
    have hpowk_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
    have h2_nonneg : (0 : ℝ) ≤ 2 := by norm_num
    calc
      Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p)
          =
            Ccount * ((2 * (2 : ℝ) ^ k) ^ (lam + δ)) *
              ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) := by
              simp [hpow_succ]
      _ = Ccount * ((2 : ℝ) ^ (lam + δ) * ((2 : ℝ) ^ k) ^ (lam + δ)) *
            ((1 : ℝ) / ((2 : ℝ) ^ k) ^ p) := by
              have hsplit :
                  ((2 : ℝ) * (2 : ℝ) ^ k) ^ (lam + δ) =
                    (2 : ℝ) ^ (lam + δ) * ((2 : ℝ) ^ k) ^ (lam + δ) := by
                simpa using
                  (Real.mul_rpow
                    (x := (2 : ℝ)) (y := (2 : ℝ) ^ k) (z := lam + δ)
                    h2_nonneg hpowk_nonneg)
              simp [hsplit, mul_assoc,
                -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      _ = (2 : ℝ) ^ (lam + δ) * Ccount *
            (((2 : ℝ) ^ k) ^ (lam + δ) / ((2 : ℝ) ^ k) ^ p) := by
              simp [div_eq_mul_inv, mul_assoc, mul_comm,
                -mul_eq_mul_left_iff, -mul_eq_mul_right_iff]
      _ = (2 : ℝ) ^ (lam + δ) * Ccount * (((2 : ℝ) ^ k) ^ (lam + δ - p)) := by
              rw [hpow_rat]
      _ = A * q ^ k := by
              simp [A, hqk, mul_assoc, mul_comm]
  exact hrewrite

/-- Bound a finite geometric tail by the corresponding infinite tail. -/
theorem geometric_sum_from_le (q : ℝ) (hq_pos : 0 < q) (hq_lt_one : q < 1)
    (n t : ℕ) : (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) ≤ q ^ (n + 1) * (1 - q)⁻¹ := by
  have hsum : Summable (fun i : ℕ => q ^ i) :=
    summable_geometric_of_lt_one (le_of_lt hq_pos) hq_lt_one
  have hsum' : Summable (fun i : ℕ => q ^ (n + 1) * q ^ i) :=
    hsum.mul_left (q ^ (n + 1))
  have hnonneg : ∀ i : ℕ, 0 ≤ q ^ (n + 1) * q ^ i := by
    intro i
    positivity
  have hle_tsum :
      (∑ i ∈ Finset.range t, q ^ (n + 1) * q ^ i)
        ≤ ∑' i : ℕ, q ^ (n + 1) * q ^ i := by
    refine
      Summable.sum_le_tsum
        (s := Finset.range t) (f := fun i : ℕ => q ^ (n + 1) * q ^ i) ?_ hsum'
    intro i hi
    exact hnonneg i
  have hpow_add : ∀ i : ℕ, q ^ (n + 1 + i) = q ^ (n + 1) * q ^ i := by
    intro i
    simp [pow_add, mul_assoc]
  have hsum_eq :
      (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) =
        (∑ i ∈ Finset.range t, q ^ (n + 1) * q ^ i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simp [hpow_add i]
  have htsum_eq :
      (∑' i : ℕ, q ^ (n + 1) * q ^ i) = (q ^ (n + 1)) * (1 - q)⁻¹ := by
    have hgeom0 : (∑' i : ℕ, q ^ i) = (1 - q)⁻¹ :=
      tsum_geometric_of_lt_one (h₁ := le_of_lt hq_pos) (h₂ := hq_lt_one)
    calc
      (∑' i : ℕ, q ^ (n + 1) * q ^ i) = (q ^ (n + 1)) * ∑' i : ℕ, q ^ i := by
          rw [tsum_mul_left]
      _ = (q ^ (n + 1)) * (1 - q)⁻¹ := by rw [hgeom0]
  have hle_tsum' :
      (∑ i ∈ Finset.range t, q ^ (n + 1 + i)) ≤ ∑' i : ℕ, q ^ (n + 1) * q ^ i := by
    rw [hsum_eq]
    exact hle_tsum
  exact le_trans hle_tsum' (by rw [htsum_eq])

/-- Bound a weighted dyadic shell using the weight of its enclosing ball. -/
theorem dyadic_shell_sum_bound {ι : Type*} [DecidableEq ι]
    (z : ι → ℂ) (w : ι → ℝ) (hw : ∀ ρ, 0 ≤ w ρ) (ball : ℕ → Finset ι)
    (hmem : ∀ k ρ, ρ ∈ ball k ↔ ‖z ρ‖ ≤ (2 : ℝ) ^ k)
    (p n k : ℕ) (hk : n + 1 ≤ k) (Ccount lam δ : ℝ)
    (hcount : (∑ ρ ∈ ball (k + 1), w ρ) ≤
      Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ)) :
    (∑ ρ ∈ ball (k + 1) \ ball k,
      if (2 : ℝ) ^ (n + 1) < ‖z ρ‖ then w ρ / ‖z ρ‖ ^ (p + 1) else 0) ≤
      ((2 : ℝ) ^ (lam + δ) * Ccount) *
        ((2 : ℝ) ^ (lam + δ - ((p : ℝ) + 1))) ^ k := by
  let g : ι → ℝ := fun ρ =>
    if (2 : ℝ) ^ (n + 1) < ‖z ρ‖ then w ρ / ‖z ρ‖ ^ (p + 1) else 0
  let A := (2 : ℝ) ^ (lam + δ) * Ccount
  let q := (2 : ℝ) ^ (lam + δ - ((p : ℝ) + 1))
  let diff : Finset ι := ball (k + 1) \ ball k
  have hterm_le :
      ∀ ρ, ρ ∈ diff →
        w ρ / ‖z ρ‖ ^ (p + 1) ≤ w ρ / ((2 : ℝ) ^ k) ^ (p + 1) := by
    intro ρ hρ
    have hnot : ¬ ‖z ρ‖ ≤ (2 : ℝ) ^ k := by
      intro hle
      have : ρ ∈ ball k :=
        (hmem k ρ).2 hle
      exact (Finset.mem_sdiff.1 hρ).2 this
    have hk_le_norm : (2 : ℝ) ^ k ≤ ‖z ρ‖ := le_of_lt (lt_of_not_ge hnot)
    have hk_pos : 0 < ((2 : ℝ) ^ k) ^ (p + 1) := by positivity
    have hk_pow_le : ((2 : ℝ) ^ k) ^ (p + 1) ≤ ‖z ρ‖ ^ (p + 1) :=
      pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k) hk_le_norm (p + 1)
    have hw_nonneg : 0 ≤ w ρ := hw ρ
    have hfrac :
        (1 : ℝ) / ‖z ρ‖ ^ (p + 1) ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1) := by
      simpa [one_div, inv_pow] using (one_div_le_one_div_of_le hk_pos hk_pow_le)
    simpa [div_eq_mul_inv, one_div, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hfrac hw_nonneg)
  have hsum_le :
      (∑ ρ ∈ diff, w ρ / ‖z ρ‖ ^ (p + 1)) ≤
        ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ (p + 1) := Finset.sum_le_sum hterm_le
  have hsum_diff :
      (∑ ρ ∈ diff, w ρ) ≤ Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) := by
    have hdiff_le_ball :
        (∑ ρ ∈ diff, w ρ) ≤ ∑ ρ ∈ ball (k + 1), w ρ := by
      refine
        Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.sdiff_subset : diff ⊆ ball (k + 1)) ?_
      intro ρ _ _
      exact hw ρ
    exact le_trans hdiff_le_ball hcount
  have hrewrite :
      Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) =
        A * q ^ k := by
    simpa only [A, q, Nat.cast_add, Nat.cast_one] using
      dyadic_power_quotient Ccount lam δ (p + 1) k
  have hdiff_simp :
      (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖z ρ‖ ^ (p + 1) := by
    refine Finset.sum_congr rfl ?_
    intro ρ hρ
    have hnot : ¬ ‖z ρ‖ ≤ (2 : ℝ) ^ k := by
      intro hle
      have : ρ ∈ ball k :=
        (hmem k ρ).2 hle
      exact (Finset.mem_sdiff.1 hρ).2 this
    have hlt : (2 : ℝ) ^ k < ‖z ρ‖ := lt_of_not_ge hnot
    have hk_pow_le : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ k :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk
    have hcond : (2 : ℝ) ^ (n + 1) < ‖z ρ‖ := by
      exact lt_of_lt_of_le (hk_pow_le.trans_lt hlt) (le_rfl)
    simp [g, hcond]
  calc
    (∑ ρ ∈ diff, g ρ) = ∑ ρ ∈ diff, w ρ / ‖z ρ‖ ^ (p + 1) := hdiff_simp
    _ ≤ ∑ ρ ∈ diff, w ρ / ((2 : ℝ) ^ k) ^ (p + 1) := hsum_le
    _ = (∑ ρ ∈ diff, w ρ) * ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
          simp [div_eq_mul_inv, Finset.sum_mul]
    _ ≤
        (Ccount * ((2 : ℝ) ^ (k + 1)) ^ (lam + δ)) *
          ((1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1)) := by
          have hconst_nonneg : 0 ≤ (1 : ℝ) / ((2 : ℝ) ^ k) ^ (p + 1) := by positivity
          exact mul_le_mul_of_nonneg_right hsum_diff hconst_nonneg
    _ = A * q ^ k := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hrewrite

/-- A uniform bound on sums over cofinal finite sets bounds the infinite sum. -/
theorem tsum_le_of_cofinal_finset_bound {ι : Type*}
    (ball : ℕ → Finset ι) (g : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ i, 0 ≤ g i) (hcofinal : ∀ t : Finset ι, ∃ n, t ⊆ ball n)
    (hball : ∀ n, ∑ i ∈ ball n, g i ≤ B) : ∑' i, g i ≤ B := by
  apply tsum_le_of_sum_le' hB
  intro t
  obtain ⟨n, hn⟩ := hcofinal t
  exact (Finset.sum_le_sum_of_subset_of_nonneg hn (fun i _ _ => hg i)).trans (hball n)

/-- A cutoff supported on a finite set has the corresponding finite sum. -/
theorem cutoff_finsum_eq_sum {ι : Type*} (s : Finset ι)
    (P : ι → Prop) [DecidablePred P] (f : ι → ℝ) (hs : ∀ a, a ∈ s ↔ P a) :
    (∑ᶠ a, if P a then f a else 0) = ∑ a ∈ s, f a := by
  classical
  have hsupp : Function.support (fun a => if P a then f a else 0) ⊆ s := by
    intro a ha
    by_contra hnot
    have hp : ¬P a := fun h => hnot ((hs a).2 h)
    simp [hp, Function.mem_support] at ha
  rw [finsum_eq_sum_of_support_subset (f := fun a => if P a then f a else 0) (s := s) hsupp]
  exact Finset.sum_congr rfl fun a ha => ite_eq_left ((hs a).1 ha)

/-- A nested sequence of finite sets with geometrically bounded shells has a bounded tail. -/
theorem sum_le_of_geometric_shells {ι : Type*} [DecidableEq ι]
    (ball : ℕ → Finset ι) (g : ι → ℝ) (A q : ℝ) (hA : 0 ≤ A)
    (hq_pos : 0 < q) (hq_lt : q < 1) (n m : ℕ)
    (hsub : ∀ k, ball k ⊆ ball (k + 1))
    (hzero : ∀ k, k ≤ n + 1 → ∑ i ∈ ball k, g i = 0)
    (hshell : ∀ k, n + 1 ≤ k → ∑ i ∈ ball (k + 1) \ ball k, g i ≤ A * q ^ k) :
    (∑ i ∈ ball m, g i) ≤ A * q / (1 - q) * q ^ n := by
  by_cases hm : m ≤ n + 1
  · rw [hzero m hm]
    exact mul_nonneg (div_nonneg (mul_nonneg hA hq_pos.le) (sub_pos.mpr hq_lt).le)
      (pow_nonneg hq_pos.le _)
  have hind : ∀ t, (∑ i ∈ ball (n + 1 + t), g i) ≤
      A * ∑ j ∈ Finset.range t, q ^ (n + 1 + j) := by
    intro t
    induction t with
    | zero => simp [hzero (n + 1) le_rfl]
    | succ t ih =>
      have hdecomp := Finset.sum_sdiff (f := g) (hsub (n + 1 + t))
      have hs := hshell (n + 1 + t) (Nat.le_add_right _ _)
      rw [Finset.sum_range_succ, mul_add]
      have heq : n + 1 + (t + 1) = n + 1 + t + 1 := by omega
      rw [heq]
      linarith
  have hm_ge : n + 1 ≤ m := (lt_of_not_ge hm).le
  have hfinite := hind (m - (n + 1))
  rw [Nat.add_sub_of_le hm_ge] at hfinite
  have hgeom := geometric_sum_from_le q hq_pos hq_lt n (m - (n + 1))
  calc
    (∑ i ∈ ball m, g i) ≤ A * (q ^ (n + 1) * (1 - q)⁻¹) :=
      hfinite.trans (mul_le_mul_of_nonneg_left hgeom hA)
    _ = A * q / (1 - q) * q ^ n := by rw [pow_succ]; ring

/-- Every finite set lies in one member of a dyadic ball exhaustion. -/
theorem dyadic_ball_cofinal {ι : Type*} (z : ι → ℂ) (ball : ℕ → Finset ι)
    (hmem : ∀ k ρ, ρ ∈ ball k ↔ ‖z ρ‖ ≤ (2 : ℝ) ^ k)
    (t : Finset ι) : ∃ m, t ⊆ ball m := by
  classical
  by_cases ht : t.Nonempty
  · obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (t.sup' ht fun i => ‖z i‖)
      (by norm_num : (1 : ℝ) < 2)
    exact ⟨m, fun i hi => (hmem m i).2 ((Finset.le_sup' (f := fun i => ‖z i‖) hi).trans hm.le)⟩
  · exact ⟨0, by simp [Finset.not_nonempty_iff_eq_empty.mp ht]⟩

end Hadamard.DyadicBounds
