/-
Copyright (c) 2024 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joris Roos
-/
import LeanPool.LeanBooleanfun.BooleanValued
import LeanPool.LeanBooleanfun.ToMathlib.Finset

/-!
# Arrow's theorem

This file proves a version of Arrow's theorem [arrow1950] for 3-candidate elections,
see `dictator_of_condorcet_and_unanimous`.
We follow O'Donnell [odonnell2014], Sec. 2.5,
which follows Kalai's approach [kalai2002] via Fourier analysis of Boolean valued functions.

## Implementation notes

The proof in [odonnell2014] makes key use of notions from probability such as
joint probability distributions on the discrete cube. We prefer to avoid this in this formalization,
so we unpack most of the probability language in the proof.
This is mainly facilitated by introducing an auxiliary linear operator, see `_Tnae3`.

## References
* [K. Arrow, *A difficulty in the concept of social welfare*][arrow1950]
* [G. Kalai, *A Fourier-theoretic perspective on the Condorcet paradox and Arrow's
  theorem*][kalai2002]
* [R. O'Donnell, *Analysis of Boolean functions*][odonnell2014]
-/

noncomputable section

namespace LeanPool.LeanBooleanfun.BooleanFun.BV

open Finset Pi RealInnerProductSpace

variable {α : Type*}
variable {n : ℕ}

variable {f : BooleanFunc n} [hbv : BooleanValued f]

/-- Encodes votes of `n` voters in a 2-candidate election. -/
abbrev Votes (n : ℕ) := Fin n → Fin 2

/-- `±1`-valued majority function -/
def majority : BooleanFunc n := fun x ↦ if ∑ j, (x j).val > n / 2 then 1 else -1

/-- The majority function is Boolean valued. -/
instance : BooleanValued (@majority n) where
  one_or_neg_one := by
    intro x
    rw [majority.eq_def]
    split_ifs
    · left; rfl
    · right; rfl

/-- A dictator is a Walsh character of a singleton set. -/
abbrev dictator {n : ℕ} (i : Fin n) : BooleanFunc n := χ {i}

/-- Not-all-equal predicate on three values. -/
abbrev NAE3 (x y z : α) : Prop := ¬ (x = y ∧ y = z)

/-- Voter preferences in an election among 3 candidates A, B, C are represented by three
vote ensembles `x y z` representing votes in the three 2-candidate elections among the candidates:
`x` contains the votes for the election A vs. B, `y` for B vs. C and `z` for C vs. A.
Three vote ensembles `x y z` are consistent if they encode a ranking of the
three candidates A, B, C for each voter. This is expressed by the not-all-equal predicate.
See [odonnell2014], Sec. 2.5. -/
def VoteConsistent (x y z : Votes n) : Prop :=
    ∀ i, NAE3 (x i) (y i) (z i)

namespace VoteConsistent

/-- Commute arguments of `VoteConsistent` predicate -/
lemma comm_right {x y z : Votes n} :
    VoteConsistent x y z = VoteConsistent x z y := by
  apply propext
  constructor <;> { intro h i; specialize h i; push Not; intro h'; rw [h'] at h; tauto }

/-- Commute arguments of `VoteConsistent` predicate -/
lemma comm_rcyc {x y z : Votes n} :
    VoteConsistent x y z = VoteConsistent y z x := by
  apply propext
  constructor <;> { intro h i; specialize h i; push Not; intro h'; rw [h'] at h; tauto }

end VoteConsistent

/-- A voting rule is Condorcet, if in every 3-candidate election conducted
  using it there is a Condercet winner. -/
def IsCondorcet (f : BooleanFunc n) : Prop :=
    ∀ x y z, VoteConsistent x y z → NAE3 (f x) (f y) (f z)

/-- A voting rule admits a dictator if it is equal to `dictator i` for some `i`. -/
def HasDictator (f : BooleanFunc n) : Prop :=
    ∃ i, f = dictator i

/-- A voting rule is unanimous if it selects candidate `i` if everyone votes for `i`. -/
def IsUnanimous (f : BooleanFunc n) : Prop := f 0 = 1 ∧ f 1 = -1

/-- The (unique) voting rule for zero voters is not unanimous. -/
lemma zero_not_unanimous (f : BooleanFunc n) (hn : n = 0) : ¬IsUnanimous f := by
  rw [IsUnanimous]
  push Not
  intro h
  have : (1 : Fin n → Fin 2) = 0 := by
    rw [hn]; trivial
  rw [this, h]
  norm_num

/-- Explicit Walsh-Fourier expansion of the not-all-equal predicate on a 3-tuple composed with a
Boolean valued function. A crucial step in the proof of Arrow's theorem. -/
lemma oneOn_NAE3_eq {x y z : Fin n → Fin 2} :
    oneOn (NAE3 (f x) (f y) (f z)) =
      3/4 - (1/4) * (f x) * (f y) - (1/4) * (f y) * (f z) - (1/4) * (f x) * (f z) := by
  obtain ⟨h0|h0, h1|h1, h2|h2⟩ := And.intro (hbv.one_or_neg_one x)
    (And.intro (hbv.one_or_neg_one y) (hbv.one_or_neg_one z)) <;>
      { rw [h0, h1, h2]; norm_num }

/-- The probability of a Condorcet winner equals the proportion out of
    the `6ⁿ` possible voter preferences `(x, y, z)` so that `(f(x), f(y), f(z))`
    is a consistent preference tuple. The impartial culture assumption is encoded
    by giving each tuple `(x, y, z)` the same weight. -/
def probabilityCondorcetWinner (f : BooleanFunc n) : ℝ :=
    (1/6)^n * ∑ x, ∑ y, ∑ z, oneOn (NAE3 (f x) (f y) (f z))
      * oneOn (VoteConsistent x y z)

/-- Auxiliary lemma for the proof of `probabilityCondorcetWinner_eq_one` -/
lemma _triple_sum_oneOn_consistent_eq :
    ∑ x : Fin n → Fin 2, ∑ y : Fin n → Fin 2, ∑ z : Fin n → Fin 2,
      oneOn (VoteConsistent x y z) = 6^n := by
  unfold VoteConsistent
  simp_rw [← oneOn_prod]
  conv => enter [1, 2, x, 2, y]
          rw [← Fintype.prod_sum (f := fun i ↦ fun c ↦ oneOn (NAE3 (x i) (y i) c))]
  conv => enter [1, 2, x]
          rw [← Fintype.prod_sum (f := fun i ↦ fun b ↦ ∑ c, oneOn (NAE3 (x i) b c))]
  rw [← Fintype.prod_sum (f := fun _ ↦ fun a ↦ ∑ b, ∑ c, oneOn (NAE3 a b c))]
  norm_num

omit hbv in
/-- If a voting rule is Condorcet, then the probability of a Condorcet winner equals 1. -/
lemma probabilityCondorcetWinner_eq_one (hc : IsCondorcet f) :
    probabilityCondorcetWinner f = 1 := by
  have : ∀ x y z : Fin n → Fin 2, NAE3 (f x) (f y) (f z) ∧ VoteConsistent x y z ↔
      VoteConsistent x y z := by
    intro x y z
    specialize hc x y z
    tauto
  unfold probabilityCondorcetWinner
  simp_rw [← oneOn_and, this, _triple_sum_oneOn_consistent_eq]
  simp

/-- Auxiliary linear operator -/
private abbrev _Tnae3 : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun := fun f ↦
    fun x ↦ (1/3)^n * ∑ y, f y * ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z)
  map_add' := by
    intro f g
    funext x
    simp only [one_div, inv_pow, Pi.add_apply, sum_boole]
    conv => enter [1, 2, 2, y]; rw [add_mul]
    rw [sum_add_distrib, mul_add]
  map_smul' := by
    intro c f
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    conv => enter [1, 2, 2, y]; rw [mul_assoc]
    rw [← mul_sum, ← mul_assoc, mul_comm _ c, mul_assoc]

/-- Notation for the auxiliary linear operator `_Tnae3`-/
local notation "T" => _Tnae3

/-- One of two crucial steps in the proof of Arrow's theorem:
 the auxiliary linear operator can be expressed in terms of `noiseOperator`. -/
lemma _eq_noise_operator : T = @noiseOperator n (-1/3) := by
  apply Module.Basis.ext (b := walshBasis)
  intro S
  rw [walshBasis, noiseOperator, coe_basisOfOrthonormalOfCardEqFinrank,
    LinearMap.coe_mk, AddHom.coe_mk, multiplier_walsh]
  funext x
  rw [Pi.smul_apply, smul_eq_mul]
  have : ∀ y : Fin n → Fin 2, ∑ z : Fin n → Fin 2, oneOn (VoteConsistent x y z)
      =  ∏ i, (1 + oneOn (x i ≠ y i)) := by
    intro y
    unfold VoteConsistent
    simp_rw [← oneOn_prod]
    rw [← Fintype.prod_sum (f := fun i => fun v => oneOn (NAE3 (x i) (y i) v))]
    suffices ∀ i, ∑ v : Fin 2, oneOn (NAE3 (x i) (y i) v) = (1 + oneOn (x i ≠ y i)) by
      simp_rw [this]
    intro i
    by_cases h : x i = y i
    · simp only [h, not_and, forall_const, Classical.ite_not, Fin.sum_univ_two, Fin.isValue, ne_eq,
        not_true_eq_false, if_false, add_zero]
      induction y i using Fin.cases with
      | zero => simp
      | succ k => simp [Fin.fin_one_eq_zero]
    · simp [h]; norm_num
  conv => enter [1, 2, 2, y]; rw [this, walshCharacter.eq_def]
          enter [1, 1]; rw [← filter_univ_mem (s := S)]
  conv => enter [1, 2, 2, y]; rw [prod_filter, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (f := fun i ↦ fun v ↦
    (if i ∈ S then (-1)^v.val else 1) * (1 + oneOn (x i ≠ v)))]
  have haux (w : Fin 2) (g : Fin 2 → ℝ) : ∑ v : Fin 2, g v = g w + g (1-w) := by
    induction w using Fin.cases with
    | zero => simp
    | succ k => simp only [Fin.sum_univ_two, Fin.isValue, Fin.fin_one_eq_zero k]
                exact add_comm _ _
  conv => enter [1, 2, 2, i]; rw [haux (x i), oneOn_false (by simp)]
          rw [oneOn_true (by omega), add_zero, mul_one]
  rw [← prod_filter_mul_prod_filter_not (p := fun i ↦ i ∈ S), prod_filter, prod_filter]
  have haux2 (v : Fin 2) : ((-1) : ℝ)^v.val + (-1)^(1-v).val * (1 + 1) = (-1) * (-1)^v.val := by
    induction v using Fin.cases with
    | zero => simp
    | succ k =>
      simp only [Fin.fin_one_eq_zero k, Fin.isValue, Fin.succ_zero_eq_one, Fin.coe_ofNat_eq_mod,
        Nat.mod_succ, pow_one, sub_self, Nat.zero_mod, pow_zero, one_mul, neg_add_cancel_left,
        mul_neg, mul_one, neg_neg]
  conv => enter [1, 2, 1, 2, i]; rw [ite_mul, ite_add_ite, ite_ite_same, haux2]
  rw [← prod_filter, filter_univ_mem, prod_mul_distrib, prod_const, ← walsh_def]
  conv => enter [1, 2, 2, 2, i]; rw [ite_mul, ite_add_ite, ite_ite_not']; arg 2; norm_num
  rw [← prod_filter, prod_const, filter_univ_not_mem, card_compl, Fintype.card_fin]
  rw [pow_sub₀ _ (by simp) (card_finset_fin_le _)]
  rw [show ((-1 : ℝ)/3) ^ S.card = (-1) ^ S.card * (1/3) ^ S.card from by
    rw [show ((-1 : ℝ)/3) = (-1) * (1/3) from by ring, mul_pow]]
  rw [div_pow, one_pow, div_pow, one_pow]
  field_simp

/-- The probability of having a Condorcet winner can be expressed in terms of the noise operator.
See [odonnell2014], Theorem 2.56. -/
theorem probabilityCondorcetWinner_eq :
    probabilityCondorcetWinner f = 3/4 * (1 - noiseStability (-1/3) f) := by
  simp_rw [probabilityCondorcetWinner.eq_def, oneOn_NAE3_eq, sub_mul, sum_sub_distrib]
  conv => enter [1, 2, 1, 1, 1]; tactic => simp_rw [← mul_sum]
  rw [_triple_sum_oneOn_consistent_eq]
  conv => enter [1, 2, 2, 2, x]; rw [sum_comm]; enter [2, y, 2, z];
          rw [VoteConsistent.comm_right]
  conv => enter [1, 2, 1, 2]; rw [sum_comm]; enter [2, x]; rw [sum_comm];
          enter [2, y, 2, z]; rw [VoteConsistent.comm_rcyc]
  rw [sub_sub, sub_sub, ← two_mul]
  nth_rewrite 1 [← one_mul (∑ x, _)]
  rw [← add_mul]
  conv => enter [1, 2, 2, 2, 2, x, 2, y, 2, z]; rw [mul_assoc, mul_assoc]
  conv => enter [1, 2, 2, 2]; tactic => simp_rw [← mul_sum]
  have : ∑ x, f x * ∑ y, f y * ∑ z, oneOn (VoteConsistent x y z)
      = 6^n * noiseStability (-1/3) f := by
    calc
      _ = 3^n * (1/3)^n * ∑ x, f x * ∑ y, f y * ∑ z, oneOn (VoteConsistent x y z) := by
            simp only [one_div, inv_pow, isUnit_iff_ne_zero, ne_eq,
              pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and, not_false_eq_true,
              IsUnit.mul_inv_cancel, one_mul]
      _ = 3^n * ∑ x, f x * T f x := by
            rw [mul_assoc, mul_sum];
            conv => {enter [1, 2, 2, x]; rw [← mul_assoc, mul_comm _ (f x), mul_assoc]}; rfl
      _ = 3^n * 2^n * (1/2)^n * ∑ x, f x * T f x := by
            simp only [LinearMap.coe_mk, one_div, inv_pow, sum_boole, AddHom.coe_mk,
              isUnit_iff_ne_zero, ne_eq, pow_eq_zero_iff', OfNat.ofNat_ne_zero, false_and,
              not_false_eq_true, IsUnit.mul_inv_cancel_right]
      _ = 6^n * (1/2)^n * ∑ x, f x * T f x := by congr; rw [← mul_pow]; congr; norm_num
      _ = 6^n * ⟪f, T f⟫ := by rw [mul_assoc]; rfl
      _ = 6^n * ⟪f, noiseOperator (-1/3) f⟫ := by rw [_eq_noise_operator]
  rw [this]
  have h16n : ((1 : ℝ) / 6) ^ n * 6 ^ n = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀ _ (pow_ne_zero _ (by norm_num : (6 : ℝ) ≠ 0))]
  have hneg : (-(1 : ℝ)/3) = -(1/3) := by ring
  rw [hneg]
  linear_combination
    ((3 : ℝ)/4 - 3/4 * noiseStability (-(1/3)) f) * h16n

/-- Arrow's theorem as formulated in [odonnell2014], Sec. 2.5 : Every unanimous voting rule that
always admits a Condorcet winner is a dictatorship. -/
theorem dictator_of_condorcet_and_unanimous (h : IsUnanimous f) :
    IsCondorcet f → HasDictator f := by
  wlog hn : 0 < n
  · have := zero_not_unanimous f (Nat.eq_zero_of_not_pos hn)
    contradiction
  intro hc
  have := probabilityCondorcetWinner_eq_one hc
  let ρ : ℝ := -1/3
  have : noiseStability ρ f = ρ := by
    rw [probabilityCondorcetWinner_eq] at this
    calc
      _ = 1 - 4/3 * (3/4 * ((1 : ℝ) - (noiseStability ρ f))) := by ring
      _ = _   := by rw [this]; ring
  have hsumzero : ∑ S, (ρ^S.card - ρ) * |𝓕 f S|^2 = 0 := by
    simp_rw [sub_mul, sum_sub_distrib]
    rw [← noise_stability_eq_sum_fourier, this]
    nth_rewrite 1 [← mul_one ρ]
    rw [← fourier_eq_one (f := f), mul_sum, sub_self]
  have hmz : ∀ S ∈ univ, (ρ^S.card - ρ) * |𝓕 f S|^2 = 0 := by
    have : ∀ S ∈ univ, 0 ≤ (ρ ^ S.card - ρ) * |𝓕 f S| ^ 2 := by
      intro S _
      apply mul_nonneg
      · by_cases hk : Even S.card
        · obtain ⟨k, hk⟩ := hk
          rw [hk, ← two_mul]
          apply add_nonneg
          · calc
              0 ≤ (ρ^2)^k := pow_nonneg (pow_two_nonneg _) _
              _ = ρ^(2 * k) := by rw [pow_mul]
          · norm_num
        · obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hk
          rw [hk]
          calc
            0 ≤ (-ρ) * (1 - (ρ^2)^k)    := by
              apply mul_nonneg
              · norm_num
              · apply sub_nonneg.mpr
                exact pow_le_one₀ (pow_two_nonneg ρ) (by norm_num)
            _ = (-ρ) * (1 - ρ^(2 * k))    := by rw [pow_mul]
            _ = ρ^(2 * k + 1) - ρ         := by ring
      · exact sq_nonneg _
    apply (sum_eq_zero_iff_of_nonneg this).mp hsumzero
  have hnez : ∀ k : ℕ, k ≠ 1 → ρ^k - ρ ≠ 0 := by
    intro k
    apply not_imp_not.mpr
    intro h
    have h := eq_add_of_sub_eq h
    rw [zero_add] at h
    obtain h|h|h|h := pow_eq_self_imp h
      <;> first | assumption | norm_num at h
  have : ∀ S, S.card ≠ 1 → 𝓕 f S = 0 := by
    intro S hS
    have := hmz S (by simp)
    have := eq_zero_of_ne_zero_of_mul_left_eq_zero (hnez S.card hS) this
    simp at this
    assumption
  have := fourier_eq_zero_iff_fourier_weight_eq.mp this
  rw [norm_sq_eq_one] at this
  obtain ⟨i, ⟨c, hfeq⟩⟩ := eq_character_of_fourier_weight_one_eq_one hn this
  use i
  have := funext_iff.mp hfeq 0
  rw [h.1] at this
  simp only [Pi.smul_apply, prod_singleton, Pi.zero_apply, Fin.isValue, Fin.coe_ofNat_eq_mod,
    Nat.zero_mod, pow_zero, smul_eq_mul, mul_one] at this
  rw [hfeq, ← this]
  simp

end LeanPool.LeanBooleanfun.BooleanFun.BV
