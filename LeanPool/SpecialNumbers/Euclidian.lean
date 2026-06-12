/-
Copyright (c) 2026 Walter Moreira, Joe Stubbs. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Walter Moreira, Joe Stubbs
-/
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Euclid Numbers

This file introduces the Euclid numbers as defined in [knuth1989concrete].
This is sequence [A129871](https://oeis.org/A129871) in [oeis]

## Implementation notes

The reference [knuth1989concrete] names the sequence $(e_n)_{n\ge 1}$ as
*Euclid numbers*, while [oeis] names it
$(e_n)_{n\ge 0}$ as *Sylvester's sequence*. We chose to follow
the notation from [knuth1989concrete].

## Main results

- Recurrence with a product of Euclid numbers.
- Co-primality of Euclid numbers.
- Explicit formula.

## References

* [Concrete Mathematics][knuth1989concrete]
* [The On-Line Encyclopedia of Integer Sequences][oeis]
-/

namespace SpecialNumbers

namespace Euclid

/--
The sequence of Euclid numbers $(e_n)_{n\ge 0}$.

Definition by a simple recurrence. The more explicit recurrence is proved in
Theorem `euclid_prod_finset_add_one`.
-/
def euclid : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 1 => (euclid n) ^ 2 - (euclid n) + 1

-- The definition conforms to the standard one for the first few examples
@[simp]
theorem euclid_zero : euclid 0 = 1 := by rfl

@[simp]
theorem euclid_one : euclid 1 = 2 := by rfl

@[simp]
theorem euclid_two : euclid 2 = 3 := by rfl

@[simp]
theorem euclid_three : euclid 3 = 7 := by rfl

/--
The Euclid numbers satisfy the recurrence:
$$
e_{n+1} = \prod_{i=1}^n e_i + 1.
$$
-/
theorem euclid_prod_finset_add_one {n : ℕ} :
    euclid (n + 1) = ∏ x ∈ Finset.Icc 1 n, euclid x + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [euclid]
    · simp only [Nat.pow_two, le_add_iff_nonneg_left, zero_le, Finset.prod_Icc_succ_top,
        Nat.add_right_cancel_iff]
      rw [← Nat.sub_one_mul]
      congr
      simp [ih]
    · simp

/--
Another expression of `euclid_prod_finset_add_one` for easier application when $n\ge 1$:
$$
e_n = \prod_{i=1}^{n-1} e_i + 1.
$$
-/
theorem euclid_prod_finset_add_one_of_pos {n : ℕ} (h : n ≥ 1) :
    euclid n = ∏ x∈Finset.Icc 1 (n - 1), euclid x + 1 := by
  have c : n = (n - 1) + 1 := by omega
  rw [c, euclid_prod_finset_add_one]
  simp

/--
Euclid numbers are positive.
-/
theorem euclid_gt_zero {n : ℕ} : 0 < euclid n := by
  unfold euclid
  split <;> linarith

theorem euclid_ne_zero {n : ℕ} : NeZero (euclid n) := NeZero.of_pos euclid_gt_zero

/--
Euclid numbers are $\ge 1$.
-/
theorem euclid_ge_one {n : ℕ} : 1 ≤ euclid n := by
  simp [Nat.one_le_iff_ne_zero]
  linarith [@euclid_gt_zero n]

/--
Only $e_0 = 1$.
-/
theorem euclid_gt_one_of_pos {n : ℕ} (h : n ≥ 1) : 1 < euclid n := by
  cases n
  · contradiction
  · simp [euclid_prod_finset_add_one, euclid_gt_zero]

/--
$e_n \equiv 1\ (\mathrm{mod}~e_m)$, when $0 < m < n$.
-/
theorem euclid_mod_eq_one {m n : ℕ} (h1 : m < n) (h2 : 0 < m) :
    euclid n % euclid m = 1 := by
  rw [euclid_prod_finset_add_one_of_pos]
  · have d : (euclid m) ∣  ∏ x ∈ Finset.Icc 1 (n-1), euclid x := by
      apply Finset.dvd_prod_of_mem
      exact Finset.mem_Icc.mpr (by omega)
    rw [Nat.add_mod]
    simp only [Nat.dvd_iff_mod_eq_zero.mp d, zero_add, dvd_refl, Nat.mod_mod_of_dvd]
    exact Nat.mod_eq_of_lt <| euclid_gt_one_of_pos <| by linarith
  · linarith

private lemma euclid_coprime_of_lt {m n : ℕ} (h : m < n) :
    Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m = 0
  · simp [c]
  · rw [Nat.Coprime, Nat.gcd_rec, euclid_mod_eq_one h (by omega)]
    exact Nat.gcd_one_left (euclid m)

/--
The Euclid numbers are co-prime: $\gcd(e_n, e_m) = 1$, for $n\neq m$.
-/
theorem euclid_coprime {m n : ℕ} (h : m ≠ n) : Nat.Coprime (euclid m) (euclid n) := by
  by_cases c : m < n
  · exact euclid_coprime_of_lt c
  · exact Nat.coprime_comm.mp <| euclid_coprime_of_lt <| by omega

/--
The Euclid numbers are strictly increasing: $e_n < e_{n+1}$, for all $n\in\mathbb{N}$.
-/
theorem euclid_strictMono : StrictMono euclid := by
  apply strictMono_nat_of_lt_succ
  intro n
  by_cases c : n = 0
  · simp [c]
  · have h : euclid n - 1 ≥ 1 := Nat.le_sub_one_of_lt <| euclid_gt_one_of_pos <| by omega
    calc
      euclid (n + 1) = (euclid n) * (euclid n - 1) + 1 := by simp [euclid, pow_two, Nat.mul_sub_one]
      _ ≥ (euclid n) * 1 + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) _
      _ > euclid n := by linarith

-- An auxiliary sequence that converges to the constant in the explicit formula for
-- the Euclid numbers.
private noncomputable def logEuclidSub (n : ℕ) : ℝ := 1 / 2 ^ n * Real.log (euclid n - 1 / 2)

private theorem reuclid_ge_one (n : ℕ) : (1 : ℝ) ≤ euclid n := Nat.one_le_cast.mpr euclid_ge_one

private theorem logEuclidSub_monotone : Monotone logEuclidSub := by
  refine monotone_nat_of_le_succ ?ha
  intro m
  simp only [logEuclidSub, one_div]
  refine le_of_mul_le_mul_left ?h1 ((by simp) : (0 : ℝ) < (2 ^ (m + 1)))
  simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
    pow_eq_zero_iff, OfNat.ofNat_ne_zero, mul_inv_cancel_left₀]
  rw [← mul_assoc, ← pow_sub₀ 2 (by linarith) (by linarith), Nat.add_sub_self_left m 1,
      pow_one, ← Real.log_rpow, Real.rpow_two]
  · refine (Real.log_le_log_iff ?hh1 ?hh2).mpr ?hh3
    · exact sq_pos_iff.mpr <| Ne.symm <| ne_of_lt <| by linarith [reuclid_ge_one m]
    · linarith [reuclid_ge_one (m + 1)]
    · cases m
      case zero => norm_num
      case succ m =>
        simp [euclid]
        ring_nf
        rw [Nat.cast_sub, <- Nat.cast_pow]
        · linarith
        · exact Nat.le_self_pow (by linarith) _
  · linarith [reuclid_ge_one m]

-- An auxiliary sequence that bounds `logEuclidSubHalf` from above and helps proving
-- its convergence.
private noncomputable def logEuclidAdd : ℕ → ℝ
  | 0 => 1
  | n => 1 / 2 ^ n * Real.log (euclid n + 1 / 2)

private theorem logEuclidAdd_strictAnti : StrictAnti logEuclidAdd := by
  refine strictAnti_nat_of_succ_lt ?ha
  intro m
  simp only [logEuclidAdd, one_div]
  split
  · norm_num
    have hlog : Real.log (5 / 2) ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by positivity)]
      linarith [Real.exp_one_gt_d9]
    linarith [hlog]
  · refine lt_of_mul_lt_mul_left ?h1 ((by simp) : (0 : ℝ) ≤ (2 ^ (m + 1)))
    simp only [ne_eq, Nat.add_eq_zero_iff, one_ne_zero, and_false, not_false_eq_true,
      pow_eq_zero_iff, OfNat.ofNat_ne_zero, mul_inv_cancel_left₀]
    rw [← mul_assoc, ← pow_sub₀ 2 (by linarith) (by linarith), Nat.add_sub_self_left m 1,
        pow_one, ← Real.log_rpow, Real.rpow_two]
    · refine (Real.log_lt_log_iff (by positivity) ?hh2).mpr ?hh3
      · exact sq_pos_iff.mpr <| Ne.symm <| ne_of_lt <| by linarith [reuclid_ge_one m]
      · simp [euclid]
        ring_nf
        rw [Nat.cast_sub, <- Nat.cast_pow]
        · linarith [reuclid_ge_one m]
        · exact Nat.le_self_pow (by linarith) _
    · linarith [reuclid_ge_one m]

private theorem logEuclidSub_lt_logEuclidAdd {n : ℕ} :
    logEuclidSub n < logEuclidAdd n := by
  simp only [logEuclidSub, one_div, logEuclidAdd]
  cases n
  case zero =>
    norm_num
    rw [Real.log_lt_iff_lt_exp] <;> linarith [Real.exp_one_gt_d9]
  case succ m =>
    simp only [inv_pos, Nat.ofNat_pos, pow_succ_pos, mul_lt_mul_iff_right₀]
    refine (Real.log_lt_log_iff ?_ ?_).mpr ?_ <;> linarith [reuclid_ge_one (m+1)]

private theorem bddAbove_logEuclidSub : BddAbove (Set.range logEuclidSub) := by
  rw [bddAbove_def]
  use logEuclidAdd 0
  intro y h
  obtain ⟨ z, hz ⟩ := h
  rw [<- hz]
  trans logEuclidAdd z
  · linarith [@logEuclidSub_lt_logEuclidAdd z]
  · have : logEuclidAdd z ≤ logEuclidAdd 0 :=
      StrictAnti.antitone logEuclidAdd_strictAnti (by linarith)
    linarith

open Filter

private noncomputable def euclidLogConstant : ℝ := ⨆ i, logEuclidSub i

/--
The sequence
$$
\frac{1}{2^n}\log\left(e_n - \frac{1}{2}\right)
$$
converges to $\log E$, where $E$ is the contant in the
explicit formula for the Euclid numbers `euclid_eq_floor_constant_pow`.
-/
noncomputable def euclidConstant : ℝ := Real.exp euclidLogConstant

@[simp]
private theorem log_euclidConstant_eq_euclidLogConstant :
    Real.log euclidConstant = euclidLogConstant := by
  simp [euclidConstant]

private theorem logEuclidSub_tendsto_euclidLogConstant :
    Tendsto logEuclidSub atTop (nhds euclidLogConstant) := by
  exact tendsto_atTop_ciSup logEuclidSub_monotone bddAbove_logEuclidSub

/--
The sequence `pl_euc_m` is bounded above by `euclid_log_constant`:
$$
\frac{1}{2^n}\log\left(e_n - \frac{1}{2}\right) \le \log E
$$
for all $n\in\mathbb{N}$.
-/
private theorem logEuclidSub_le_euclidLogConstant {n : ℕ} : logEuclidSub n ≤ euclidLogConstant :=
  Monotone.ge_of_tendsto logEuclidSub_monotone logEuclidSub_tendsto_euclidLogConstant n

private theorem euclidLogConstant_lt_logEuclidAdd {n : ℕ} : euclidLogConstant < logEuclidAdd n := by
  have h : logEuclidAdd (n + 1) ∈ upperBounds (Set.range logEuclidSub) := by
    refine mem_upperBounds.mpr ?h
    intros x h
    obtain ⟨ m, h2 ⟩ := h
    rw [<- h2]
    let z := max m (n + 1)
    have : logEuclidSub m ≤ logEuclidSub z := logEuclidSub_monotone (by omega)
    have : logEuclidAdd z ≤ logEuclidAdd (n + 1) :=
      StrictAnti.antitone logEuclidAdd_strictAnti (by omega)
    have : logEuclidSub z < logEuclidAdd z := logEuclidSub_lt_logEuclidAdd
    linarith
  have c : euclidLogConstant ≤ logEuclidAdd (n + 1) := (isLUB_le_iff
    (isLUB_of_tendsto_atTop logEuclidSub_monotone logEuclidSub_tendsto_euclidLogConstant)).mpr h
  have d : logEuclidAdd (n + 1) < logEuclidAdd n := logEuclidAdd_strictAnti (by linarith)
  linarith

/--
$0 < E$.
-/
theorem euclidConstant_pos : 0 < euclidConstant := Real.exp_pos euclidLogConstant

/--
$e_n \le E^{2^n} + \frac{1}{2}$ for all $n\in\mathbb{N}$.
-/
theorem euclid_le_constant_pow {n : ℕ} : euclid n ≤ euclidConstant ^ (2 ^ n) + 1 / 2 := by
  apply tsub_le_iff_right.mp
  refine (Real.log_le_log_iff ?ha ?hb).mp ?h
  · linarith [reuclid_ge_one n]
  · exact pow_pos euclidConstant_pos (2 ^ n)
  · simp only [one_div, Real.log_pow, Nat.cast_pow, Nat.cast_ofNat,
      log_euclidConstant_eq_euclidLogConstant]
    have c : logEuclidSub n ≤ euclidLogConstant := logEuclidSub_le_euclidLogConstant
    simp only [logEuclidSub, one_div] at c
    rwa [<- inv_mul_le_iff₀]
    positivity

/--
$E^{2^n} + \frac{1}{2} < e_n + 1$ for all $n\in\mathbb{N}$.
-/
theorem constant_pow_lt_euclid_add_one {n : ℕ} :
    euclidConstant ^ (2 ^ n) + 1 / 2 < euclid n + 1 := by
  apply lt_tsub_iff_right.mp
  rw [add_sub_assoc]
  norm_num
  refine (Real.log_lt_log_iff ?ha ?hb).mp ?h
  · exact pow_pos euclidConstant_pos (2 ^ n)
  · linarith [reuclid_ge_one n]
  · norm_num
    refine (lt_div_iff₀' (by positivity)).mp ?he
    rw [div_eq_inv_mul]
    simp only [one_div]
    let c := @euclidLogConstant_lt_logEuclidAdd n
    simp only [logEuclidAdd, one_div] at c
    split at c
    · let d := @euclidLogConstant_lt_logEuclidAdd 2
      simp only [logEuclidAdd, one_div, euclid_two, Nat.cast_ofNat] at d
      norm_num at *
      have e : (1 / 4) * Real.log (7 / 2) < Real.log (3 / 2) := by
        rw [<- Real.log_rpow (by positivity)]
        refine (Real.log_lt_log_iff ?haa ?hbb).mpr ?hcc
        · positivity
        · positivity
        · refine (Real.lt_rpow_inv_iff_of_pos ?hhx ?hy ?hz).mp ?aa
          any_goals positivity
          norm_num
      linarith
    · exact c

/--
$e_n = \lfloor E^{2^n} + \frac{1}{2}\rfloor$ for all $n\in\mathbb{N}$.
-/
theorem euclid_eq_floor_constant_pow {n : ℕ} : euclid n = ⌊euclidConstant ^ (2 ^ n) + 1 / 2⌋₊ := by
  symm
  refine (Nat.floor_eq_iff ?h).mpr ?hb
  · linarith [pow_pos euclidConstant_pos (2 ^ n)]
  · exact ⟨ euclid_le_constant_pow, constant_pow_lt_euclid_add_one ⟩

end Euclid

end SpecialNumbers
