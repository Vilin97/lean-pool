/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import LeanPool.NaslundCounterexample.Families

/-!
# The growth rate

`D_3(n)` is the largest size of a square-difference-free set of polynomials of degree below `n`.
It is nondecreasing, at most `3^n`, and at least `810^e` at `n = 8e` by the first family. Writing
`L = log 810 / log 3`, the three facts give

`log D_3(n) / (n log 3) ≥ (1/8 - 1/n) · L` for `n ≥ 8`,

so the lower limit of the left side is at least `L/8`. Finally `16/21 ≤ L/8` is the natural-number
comparison `3^128 ≤ 810^21`, and `16/21 = 0.76190…` is the stated bound.
-/

@[expose] public section

namespace NaslundCounterexample

open Polynomial

/-- The finite set `polynomialsBelow n` is exactly the set of polynomials of degree below `n`. -/
theorem mem_polynomialsBelow (n : ℕ) (f : (ZMod 3)[X]) : f ∈ polynomialsBelow n ↔ f.degree < n := by
  classical
  constructor
  · intro hf
    unfold polynomialsBelow at hf
    rw [Finset.mem_image] at hf
    obtain ⟨c, -, rfl⟩ := hf
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr ?_
    intro i _
    exact below_C_mul_X_pow (c i) (i : ℕ) n i.isLt
  · intro hf
    unfold polynomialsBelow
    rw [Finset.mem_image]
    refine ⟨fun i : Fin n => f.coeff (i : ℕ), Finset.mem_univ _, ?_⟩
    change (∑ i : Fin n, C (f.coeff (i : ℕ)) * X ^ (i : ℕ)) = f
    rcases eq_or_ne f 0 with rfl | h0
    · simp
    · have hn : f.natDegree < n := (natDegree_lt_iff_degree_lt h0).mpr hf
      rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * (X : (ZMod 3)[X]) ^ i) n]
      simp only [C_mul_X_pow_eq_monomial]
      exact (f.as_sum_range' n hn).symm

/-- There are at most `3^n` polynomials of degree below `n`. -/
theorem polynomialsBelow_card_le (n : ℕ) : (polynomialsBelow n).card ≤ 3 ^ n := by
  classical
  unfold polynomialsBelow
  refine le_trans Finset.card_image_le ?_
  simp [Finset.card_univ, ZMod.card]

/-- The polynomials of degree below `n` sit inside those of degree below `n'` for `n ≤ n'`. -/
theorem polynomialsBelow_mono {n n' : ℕ} (h : n ≤ n') : polynomialsBelow n ⊆ polynomialsBelow n'
    := by
  intro f hf
  rw [mem_polynomialsBelow] at hf ⊢
  exact lt_of_lt_of_le hf (by exact_mod_cast h)

/-- Every square-difference-free set of polynomials of degree below `n` is counted by `D_3(n)`. -/
theorem card_le_maximumCardinality {n : ℕ} {A : Finset (ZMod 3)[X]} (hA : AllBelow n A) (hS :
    SquareDifferenceFree A) :
    A.card ≤ maximumCardinality n := by
  classical
  have hsub : A ⊆ polynomialsBelow n := fun f hf => (mem_polynomialsBelow n f).mpr (hA f hf)
  unfold maximumCardinality
  refine Finset.le_sup (f := Finset.card) ?_
  simp only [Finset.mem_filter, Finset.mem_powerset]
  exact ⟨hsub, hS⟩

/-- `D_3` is nondecreasing. -/
theorem maximumCardinality_mono : Monotone maximumCardinality := by
  intro n n' h
  classical
  unfold maximumCardinality
  exact Finset.sup_mono
    (Finset.filter_subset_filter _ (Finset.powerset_mono.mpr (polynomialsBelow_mono h)))

/-- `D_3(n) ≤ 3^n`, the trivial upper bound. -/
theorem maximumCardinality_le (n : ℕ) : maximumCardinality n ≤ 3 ^ n := by
  classical
  unfold maximumCardinality
  refine Finset.sup_le fun A hA => ?_
  have hsub : A ⊆ polynomialsBelow n := Finset.mem_powerset.mp (Finset.mem_filter.mp hA).1
  exact le_trans (Finset.card_le_card hsub) (polynomialsBelow_card_le n)

/-- `D_3(n) ≥ 1`, witnessed by the one-element set `{0}`. -/
theorem one_le_maximumCardinality (n : ℕ) : 1 ≤ maximumCardinality n := by
  classical
  have hA : AllBelow n ({0} : Finset (ZMod 3)[X]) := by
    intro f hf
    rw [Finset.mem_singleton] at hf
    subst hf
    exact below_zero n
  have hS : SquareDifferenceFree ({0} : Finset (ZMod 3)[X]) := by
    intro f hf g hg z hz
    rw [Finset.mem_singleton] at hf hg
    subst hf; subst hg
    have h0 : z ^ 2 = 0 := by simpa using hz.symm
    simpa using h0
  simpa using card_le_maximumCardinality hA hS

/-- The first family gives `D_3(8e) ≥ 810^e`. -/
theorem pow_le_maximumCardinality (e : ℕ) : 810 ^ e ≤ maximumCardinality (8 * e) := by
  have h := card_le_maximumCardinality (familyFromZero_allBelow e) (familyFromZero_sdf e)
  rwa [familyFromZero_card e] at h

/-- **The growth rate.** `16/21 = 0.76190… ≤ liminf log D_3(n) / (n log 3)`.

For `n ≥ 8` and `e = ⌊n/8⌋` the first family gives `D_3(n) ≥ D_3(8e) ≥ 810^e`, so the quotient is
at least `(1/8 - 1/n) log 810 / log 3`; letting `n` grow, the lower limit is at least
`log 810 / (8 log 3)`, and `16/21 ≤ log 810 / (8 log 3)` is the comparison `3^128 ≤ 810^21`. -/
theorem liminf_ge :
    (16 / 21 : ℝ) ≤
      Filter.liminf (fun n : ℕ => Real.log (maximumCardinality n) / (n * Real.log 3)) Filter.atTop
          := by
  set u : ℕ → ℝ := fun n => Real.log (maximumCardinality n) / (n * Real.log 3) with hu
  have h3 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  have h810 : (0 : ℝ) < Real.log 810 := Real.log_pos (by norm_num)
  set c : ℝ := Real.log 810 / (8 * Real.log 3) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hclog : Real.log 810 = 8 * c * Real.log 3 := by
    rw [hc]; field_simp
  -- The sequence is bounded above by `1`, which pays the cobounded side condition.
  have hb : ∀ᶠ n : ℕ in Filter.atTop, u n ≤ 1 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hD : (maximumCardinality n : ℝ) ≤ (3 : ℝ) ^ n := by exact_mod_cast maximumCardinality_le n
    have hD1 : (0 : ℝ) < (maximumCardinality n : ℝ) := by exact_mod_cast one_le_maximumCardinality n
    have hlog : Real.log (maximumCardinality n) ≤ (n : ℝ) * Real.log 3 := by
      have h := Real.log_le_log hD1 hD
      rwa [Real.log_pow] at h
    simp only [hu]
    rw [div_le_one (by positivity)]
    exact hlog
  have hcob : Filter.IsCoboundedUnder (· ≥ ·) Filter.atTop u :=
    Filter.IsBoundedUnder.isCoboundedUnder_ge ⟨1, hb⟩
  -- `16/21 ≤ log 810 / (8 log 3)` is the comparison `3^128 ≤ 810^21`.
  have hkey : (16 / 21 : ℝ) ≤ c := by
    rw [hc, le_div_iff₀ (by positivity)]
    have hnum : ((3 : ℝ) ^ (128 : ℕ)) ≤ ((810 : ℝ) ^ (21 : ℕ)) := by norm_num
    have h1 : Real.log ((3 : ℝ) ^ (128 : ℕ)) ≤ Real.log ((810 : ℝ) ^ (21 : ℕ)) :=
      Real.log_le_log (by positivity) hnum
    rw [Real.log_pow, Real.log_pow] at h1
    push_cast at h1
    linarith
  refine le_trans hkey ?_
  refine le_of_forall_lt_imp_le_of_dense fun ρ hρ => ?_
  refine Filter.le_liminf_of_le hcob ?_
  obtain ⟨N, hN⟩ := exists_nat_ge (7 * c / (c - ρ))
  have hcρ : 0 < c - ρ := sub_pos.mpr hρ
  have hN' : 7 * c ≤ (N : ℝ) * (c - ρ) := by
    rw [div_le_iff₀ hcρ] at hN
    linarith
  filter_upwards [Filter.eventually_ge_atTop (max N 8)] with n hn
  have hn8 : 8 ≤ n := le_trans (le_max_right N 8) hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 8) hn
  have hn0 : (0 : ℝ) < n := by
    have hpos : (0 : ℕ) < n := by omega
    exact_mod_cast hpos
  have hdiv1 : 8 * (n / 8) ≤ n := by omega
  have hdiv2 : n ≤ 8 * (n / 8) + 7 := by omega
  have hge : (810 : ℕ) ^ (n / 8) ≤ maximumCardinality n := le_trans (pow_le_maximumCardinality (n
      / 8)) (maximumCardinality_mono hdiv1)
  have hgeR : ((810 : ℝ)) ^ (n / 8) ≤ (maximumCardinality n : ℝ) := by exact_mod_cast hge
  have hlog : ((n / 8 : ℕ) : ℝ) * Real.log 810 ≤ Real.log (maximumCardinality n) := by
    have h := Real.log_le_log (by positivity) hgeR
    rwa [Real.log_pow] at h
  have hen : (n : ℝ) ≤ 8 * ((n / 8 : ℕ) : ℝ) + 7 := by exact_mod_cast hdiv2
  have hcl : (0 : ℝ) < c * Real.log 3 := by positivity
  have hNn : 7 * c ≤ (n : ℝ) * (c - ρ) :=
    le_trans hN' (mul_le_mul_of_nonneg_right hnN hcρ.le)
  have step1 : ((n : ℝ) - 7) * (c * Real.log 3) ≤ ((n / 8 : ℕ) : ℝ) * Real.log 810 := by
    calc
      _ ≤ (8 * ((n / 8 : ℕ) : ℝ)) * (c * Real.log 3) :=
        mul_le_mul_of_nonneg_right (by linarith) hcl.le
      _ = _ := by rw [hclog]; ring
  have step2 : ρ * ((n : ℝ) * Real.log 3) ≤ ((n : ℝ) - 7) * (c * Real.log 3) := by
    have h : ρ * (n : ℝ) ≤ ((n : ℝ) - 7) * c := by linarith
    calc
      _ = (ρ * (n : ℝ)) * Real.log 3 := by ring
      _ ≤ (((n : ℝ) - 7) * c) * Real.log 3 := mul_le_mul_of_nonneg_right h h3.le
      _ = _ := by ring
  simp only [hu]
  rw [le_div_iff₀ (by positivity)]
  linarith

end NaslundCounterexample
