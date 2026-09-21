/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module


public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Factorization.DegreeTwo.TranslatedSpanFactorization
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NonpositiveCoefficientMap
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.TruncationIntegerPartPrimal
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Domain
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType
import Mathlib.Data.Prod.Lex
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# An explicit PS06 degree-two irreducible

This module constructs a coefficient-one series whose support consists of rows converging to
`-1/(m+1)`, with those row limits converging to zero. Its support has exact order type `ω²`; after
adding the constant term one, it has order type `ω² + 1`.

The translated-truncation classes at the first three row limits have pairwise separated cofinal
supports and are linearly independent modulo `J + K`. Thus `V(a)` has dimension greater than two,
and PS06, Corollary 3.3 proves the series irreducible over every characteristic-zero coefficient
field. This is the explicit witness used by the omnific-integer example.
-/

open scoped HahnSeries

public noncomputable section

namespace PommersheimShahriari.DegreeTwoExample

universe v

variable {K : Type v} [Field K]

/-- The limit point of block `m` in the explicit degree-two support. -/
def degreeTwoCutoff (m : ℕ) : ℝ :=
  -(1 / (m + 1 : ℝ))

@[simp]
theorem degreeTwoCutoff_apply (m : ℕ) :
    degreeTwoCutoff m = -(1 / (m + 1 : ℝ)) := (rfl)

/-- The exponent in block `p.1` at position `p.2`. -/
def degreeTwoExponentPair (p : ℕ × ℕ) : ℝ :=
  degreeTwoCutoff p.1 -
    1 / ((p.1 + 1 : ℝ) * (p.1 + 2 : ℝ) * (p.2 + 1 : ℝ))

theorem degreeTwoExponentPair_apply (p : ℕ × ℕ) :
    degreeTwoExponentPair p =
      -(1 / (p.1 + 1 : ℝ)) - 1 / ((p.1 + 1 : ℝ) * (p.1 + 2 : ℝ) * (p.2 + 1 : ℝ)) := (rfl)

private theorem degreeTwoExponentPair_strictMono_second (m : ℕ) :
    StrictMono (fun n : ℕ ↦ degreeTwoExponentPair (m, n)) := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [degreeTwoExponentPair]
  apply sub_lt_sub_left
  apply one_div_lt_one_div_of_lt
  · positivity
  · gcongr
    omega

private theorem degreeTwoExponentPair_lt_cutoff (m n : ℕ) :
    degreeTwoExponentPair (m, n) < degreeTwoCutoff m := by
  dsimp [degreeTwoExponentPair]
  have : 0 <
      1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)) := by
    positivity
  linarith

private theorem degreeTwoCutoff_lt_next_exponent_zero (m : ℕ) :
    degreeTwoCutoff m < degreeTwoExponentPair (m + 1, 0) := by
  dsimp [degreeTwoCutoff, degreeTwoExponentPair]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring_nf
  nlinarith

private theorem degreeTwoExponentPair_lt_of_first_lt
    {m m' n n' : ℕ} (hmm' : m < m') :
    degreeTwoExponentPair (m, n) < degreeTwoExponentPair (m', n') := by
  calc
    degreeTwoExponentPair (m, n) < degreeTwoCutoff m :=
      degreeTwoExponentPair_lt_cutoff m n
    _ < degreeTwoExponentPair (m + 1, 0) :=
      degreeTwoCutoff_lt_next_exponent_zero m
    _ ≤ degreeTwoExponentPair (m', n') := by
      by_cases hsucc : m + 1 = m'
      · subst m'
        exact (degreeTwoExponentPair_strictMono_second (m + 1)).monotone
          (Nat.zero_le n')
      · have hfirst : m + 1 < m' := lt_of_le_of_ne (Nat.succ_le_iff.mpr hmm') hsucc
        exact (degreeTwoExponentPair_lt_of_first_lt hfirst).le
termination_by m' - m

private theorem degreeTwoExponent_strictMono :
    StrictMono (fun p : Lex (ℕ × ℕ) ↦ degreeTwoExponentPair (ofLex p)) := by
  intro p q hpq
  rw [Prod.Lex.lt_iff] at hpq
  rcases hpq with hfirst | ⟨hfirst, hsecond⟩
  · exact degreeTwoExponentPair_lt_of_first_lt hfirst
  · change degreeTwoExponentPair ((ofLex p).1, (ofLex p).2) <
      degreeTwoExponentPair ((ofLex q).1, (ofLex q).2)
    rw [hfirst]
    exact degreeTwoExponentPair_strictMono_second _ hsecond

/-- The explicit order embedding used by the degree-two witness. -/
def degreeTwoExponentEmbedding : Lex (ℕ × ℕ) ↪o ℝ :=
  OrderEmbedding.ofStrictMono _ degreeTwoExponent_strictMono

@[simp]
theorem degreeTwoExponentEmbedding_apply (m n : ℕ) :
    degreeTwoExponentEmbedding (toLex (m, n)) = degreeTwoExponentPair (m, n) :=
  (rfl)

/-- The coefficient-one series on the natural numbers. -/
def natOnes : K⟦ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using Set.IsPWO.of_linearOrder (Set.univ : Set ℕ)

@[simp]
theorem natOnes_coeff (n : ℕ) : (natOnes (K := K)).coeff n = 1 :=
  (rfl)

@[simp]
theorem natOnes_support : (natOnes (K := K)).support = Set.univ := by
  ext n
  simp [natOnes]

/-- The coefficient-one series indexed by two lexicographic natural coordinates. -/
def lexNatPairOnes : K⟦Lex (ℕ × ℕ)⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using
      Set.IsPWO.of_linearOrder (Set.univ : Set (Lex (ℕ × ℕ)))

@[simp]
theorem lexNatPairOnes_support :
    (lexNatPairOnes (K := K)).support = Set.univ := by
  ext p
  simp [lexNatPairOnes]

/-- An explicit coefficient-one Hahn series of support order type `ω²`. -/
def degreeTwoSeries : K⟦ℝ⟧ :=
  HahnSeries.embDomain degreeTwoExponentEmbedding (lexNatPairOnes (K := K))

theorem degreeTwoSeries_coeff_embedding (m n : ℕ) :
    (degreeTwoSeries (K := K)).coeff
      (degreeTwoExponentEmbedding (toLex (m, n))) = 1 := by
  rw [degreeTwoSeries, HahnSeries.embDomain_coeff]
  rfl

theorem degreeTwoSeries_support :
    (degreeTwoSeries (K := K)).support = Set.range degreeTwoExponentEmbedding := by
  rw [degreeTwoSeries, HahnSeries.support_embDomain, lexNatPairOnes_support,
    Set.image_univ]

@[simp]
theorem degreeTwoSeries_coeff_zero : (degreeTwoSeries (K := K)).coeff 0 = 0 := by
  rw [← not_ne_iff, ← HahnSeries.mem_support, degreeTwoSeries_support (K := K)]
  rintro ⟨p, hp⟩
  rcases p with ⟨m, n⟩
  have hneg := (degreeTwoExponentPair_lt_cutoff m n).trans (by
    rw [degreeTwoCutoff_apply]
    exact neg_neg_of_pos (by positivity))
  change degreeTwoExponentPair (m, n) = 0 at hp
  linarith

theorem degreeTwoSeries_supportOrderType :
    (degreeTwoSeries (K := K)).supportOrderType =
      Ordinal.omega0 ^ (2 : Ordinal) := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : (degreeTwoSeries (K := K)).support ≃o Lex (ℕ × ℕ) :=
    (OrderIso.setCongr (degreeTwoSeries (K := K)).support
      (Set.range degreeTwoExponentEmbedding)
      (degreeTwoSeries_support (K := K))).trans
      degreeTwoExponentEmbedding.orderIso.symm
  rw [(degreeTwoSeries (K := K)).isPWO_support.orderType_eq_typeLT_of_orderIso e]
  change Ordinal.type (Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)) = _
  rw [Ordinal.type_prod_lex]
  simp only [Ordinal.type_nat_lt]
  have hsucc : Order.succ (1 : Ordinal) = 2 := one_add_one_eq_two
  rw [← hsucc, Ordinal.opow_succ, Ordinal.opow_one]

/-- The degree-two series regarded as a nonpositive real Hahn series. -/
def degreeTwoNonpositive : HahnSeries.Nonpositive ℝ K :=
  ⟨degreeTwoSeries (K := K), by
    rw [HahnSeries.mem_nonpositiveSubring, degreeTwoSeries_support (K := K)]
    rintro _ ⟨p, rfl⟩
    rcases p with ⟨m, n⟩
    exact (degreeTwoExponentPair_lt_cutoff m n).le.trans
      (by rw [degreeTwoCutoff_apply]
          exact neg_nonpos.mpr (by positivity))⟩

/-- The exponent in block `m` after translating its limit point to zero. -/
def degreeTwoBlockExponent (m n : ℕ) : ℝ :=
  -(1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)))

@[simp]
theorem degreeTwoBlockExponent_apply (m n : ℕ) :
    degreeTwoBlockExponent m n =
      -(1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ))) := (rfl)

private theorem degreeTwoBlockExponent_strictMono (m : ℕ) :
    StrictMono (degreeTwoBlockExponent m) := by
  apply strictMono_nat_of_lt_succ
  intro n
  dsimp [degreeTwoBlockExponent]
  apply neg_lt_neg
  apply one_div_lt_one_div_of_lt
  · positivity
  · gcongr
    omega

/-- The translated support of block `m`, approaching exponent zero from below. -/
def degreeTwoBlockEmbedding (m : ℕ) : ℕ ↪o ℝ :=
  OrderEmbedding.ofStrictMono _ (degreeTwoBlockExponent_strictMono m)

@[simp]
theorem degreeTwoBlockEmbedding_apply (m n : ℕ) :
    degreeTwoBlockEmbedding m n = degreeTwoBlockExponent m n :=
  (rfl)

/-- Block `m` translated so that its limiting cutoff is zero. -/
def degreeTwoBlock (m : ℕ) : Berarducci.Series K :=
  ⟨HahnSeries.embDomain (degreeTwoBlockEmbedding m) (natOnes (K := K)), by
    rw [HahnSeries.mem_nonpositiveSubring, HahnSeries.support_embDomain,
      natOnes_support, Set.image_univ]
    rintro _ ⟨n, rfl⟩
    rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply]
    have h : (0 : ℝ) <
        1 / ((m + 1 : ℝ) * (m + 2 : ℝ) * (n + 1 : ℝ)) := by
      positivity
    exact neg_nonpos.mpr h.le⟩

theorem degreeTwoBlock_coeff_embedding (m n : ℕ) :
    ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff
      (degreeTwoBlockEmbedding m n) = 1 := by
  rw [degreeTwoBlock, HahnSeries.embDomain_coeff]
  exact natOnes_coeff n

theorem degreeTwoBlock_support (m : ℕ) :
    ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).support =
      Set.range (degreeTwoBlockEmbedding m) := by
  rw [degreeTwoBlock, HahnSeries.support_embDomain, natOnes_support,
    Set.image_univ]

private theorem degreeTwoCutoff_strictMono : StrictMono degreeTwoCutoff := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [degreeTwoCutoff_apply, degreeTwoCutoff_apply]
  apply neg_lt_neg
  apply one_div_lt_one_div_of_lt
  · positivity
  · norm_num

private theorem degreeTwoExponentPair_eq_cutoff_add_block (m n : ℕ) :
    degreeTwoExponentPair (m, n) =
      degreeTwoCutoff m + degreeTwoBlockExponent m n := by
  rw [degreeTwoCutoff_apply, degreeTwoBlockExponent_apply]
  rfl

private theorem degreeTwoCutoff_lt_exponentPair_of_lt
    {m m' n' : ℕ} (hmm' : m < m') :
    degreeTwoCutoff m < degreeTwoExponentPair (m', n') := by
  calc
    degreeTwoCutoff m < degreeTwoExponentPair (m + 1, 0) :=
      degreeTwoCutoff_lt_next_exponent_zero m
    _ ≤ degreeTwoExponentPair (m', n') := by
      by_cases hsucc : m + 1 = m'
      · subst m'
        exact (degreeTwoExponentPair_strictMono_second (m + 1)).monotone
          (Nat.zero_le n')
      · have hfirst : m + 1 < m' := lt_of_le_of_ne (Nat.succ_le_iff.mpr hmm') hsucc
        exact (degreeTwoExponentPair_lt_of_first_lt hfirst).le

private def degreeTwoGermLowerBound : ℕ → ℝ
  | 0 => -2
  | m + 1 => degreeTwoCutoff m - degreeTwoCutoff (m + 1)

private theorem degreeTwoGermLowerBound_neg (m : ℕ) :
    degreeTwoGermLowerBound m < 0 := by
  cases m with
  | zero => norm_num [degreeTwoGermLowerBound]
  | succ m =>
      rw [degreeTwoGermLowerBound]
      exact sub_neg.mpr (degreeTwoCutoff_strictMono (Nat.lt_succ_self m))

private theorem first_eq_of_exponent_eq_cutoff_add_of_lowerBound_lt
    {m m' n' : ℕ} {delta : ℝ}
    (hdelta : degreeTwoGermLowerBound m < delta) (hdelta0 : delta ≤ 0)
    (hexponent : degreeTwoExponentPair (m', n') = degreeTwoCutoff m + delta) :
    m' = m := by
  rcases lt_trichotomy m' m with hlt | heq | hgt
  · cases m with
    | zero => omega
    | succ m =>
        have hm'le : m' ≤ m := Nat.lt_succ_iff.mp hlt
        have hcutoff : degreeTwoCutoff m' ≤ degreeTwoCutoff m :=
          degreeTwoCutoff_strictMono.monotone hm'le
        have hexpLt : degreeTwoExponentPair (m', n') < degreeTwoCutoff m :=
          (degreeTwoExponentPair_lt_cutoff m' n').trans_le hcutoff
        rw [hexponent] at hexpLt
        rw [degreeTwoGermLowerBound] at hdelta
        linarith
  · exact heq
  · have hbad := degreeTwoCutoff_lt_exponentPair_of_lt (n' := n') hgt
    rw [hexponent] at hbad
    linarith

private theorem degreeTwo_germ_coeff_eq_block (m : ℕ) {delta : ℝ}
    (hlower : degreeTwoGermLowerBound m < delta) (hdelta0 : delta ≤ 0) :
    ((Berarducci.translatedTruncation (degreeTwoSeries (K := K) : K⟦ℝ⟧)
      (degreeTwoCutoff m) : Berarducci.Series K) : K⟦ℝ⟧).coeff delta =
        ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff delta := by
  rw [Berarducci.coeff_translatedTruncation, ite_eq_left hdelta0]
  by_cases hblock : delta ∈ Set.range (degreeTwoBlockEmbedding m)
  · obtain ⟨n, rfl⟩ := hblock
    rw [degreeTwoBlock_coeff_embedding (K := K)]
    have harg : degreeTwoCutoff m + degreeTwoBlockEmbedding m n =
        degreeTwoExponentEmbedding (toLex (m, n)) := by
      rw [degreeTwoBlockEmbedding_apply, degreeTwoExponentEmbedding_apply,
        degreeTwoExponentPair_eq_cutoff_add_block]
    rw [harg, degreeTwoSeries_coeff_embedding (K := K)]
  · have hblockCoeff :
        ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff delta = 0 := by
      apply not_ne_iff.mp
      intro hne
      apply hblock
      rw [← degreeTwoBlock_support (K := K)]
      exact (HahnSeries.mem_support _ _).mpr hne
    rw [hblockCoeff]
    apply not_ne_iff.mp
    rw [← HahnSeries.mem_support, degreeTwoSeries_support (K := K)]
    rintro ⟨p, hp⟩
    rcases p with ⟨m', n'⟩
    change degreeTwoExponentPair (m', n') = degreeTwoCutoff m + delta at hp
    have hm' : m' = m := first_eq_of_exponent_eq_cutoff_add_of_lowerBound_lt
      hlower hdelta0 hp
    subst m'
    apply hblock
    refine ⟨n', ?_⟩
    rw [degreeTwoBlockEmbedding_apply]
    rw [degreeTwoExponentPair_eq_cutoff_add_block] at hp
    linarith

/-- At cutoff `m`, the translated germ of the degree-two series is the germ of block `m`. -/
theorem degreeTwo_translatedTruncationClass_eq_block (m : ℕ) :
    PommersheimShahriari.translatedTruncationClass (degreeTwoSeries (K := K))
        (degreeTwoCutoff m) =
      PommersheimShahriari.toSeriesQuotientByJAddConstants (degreeTwoBlock (K := K) m) := by
  rw [PommersheimShahriari.translatedTruncationClass_apply,
    PommersheimShahriari.toSeriesQuotientByJAddConstants_eq_iff]
  apply Berarducci.negativeMonomialIdeal_le_nearConstantSubgroup
  change Berarducci.translatedTruncation (degreeTwoSeries (K := K)) (degreeTwoCutoff m) -
      degreeTwoBlock (K := K) m ∈ HahnSeries.Nonpositive.negativeMonomialIdeal K
  rw [← Berarducci.toGerm_eq_toGerm_iff]
  apply Berarducci.toGerm_eq_toGerm_iff_exists_coeff_eq.mpr
  exact ⟨degreeTwoGermLowerBound m, degreeTwoGermLowerBound_neg m,
    fun _ hlower hdelta0 ↦ degreeTwo_germ_coeff_eq_block (K := K) m hlower hdelta0⟩

private theorem degreeTwoBlock_zero_threeMul_not_mem_one (N : ℕ) :
    degreeTwoBlockEmbedding 0 (3 * N) ∉
      Set.range (degreeTwoBlockEmbedding 1) := by
  rintro ⟨k, hk⟩
  rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply,
    degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply] at hk
  field_simp at hk
  norm_num [Nat.cast_add, Nat.cast_mul] at hk
  ring_nf at hk
  have hkNat : 2 + N * 6 = 6 + k * 6 := by exact_mod_cast hk
  omega

private theorem degreeTwoBlock_zero_threeMul_not_mem_two (N : ℕ) :
    degreeTwoBlockEmbedding 0 (3 * N) ∉
      Set.range (degreeTwoBlockEmbedding 2) := by
  rintro ⟨k, hk⟩
  rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply,
    degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply] at hk
  field_simp at hk
  norm_num [Nat.cast_add, Nat.cast_mul] at hk
  ring_nf at hk
  have hkNat : 2 + N * 6 = 12 + k * 12 := by exact_mod_cast hk
  omega

private theorem degreeTwoBlock_one_twoMul_not_mem_two (N : ℕ) :
    degreeTwoBlockEmbedding 1 (2 * N) ∉
      Set.range (degreeTwoBlockEmbedding 2) := by
  rintro ⟨k, hk⟩
  rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply,
    degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply] at hk
  field_simp at hk
  norm_num [Nat.cast_add, Nat.cast_mul] at hk
  ring_nf at hk
  have hkNat : 6 + N * 12 = 12 + k * 12 := by exact_mod_cast hk
  omega

private theorem exists_degreeTwoBlockEmbedding_gt
    (m scale : ℕ) (hscale : 0 < scale) {eta : ℝ} (heta : eta < 0) :
    ∃ N, eta < degreeTwoBlockEmbedding m (scale * N) := by
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (neg_pos.mpr heta)
  refine ⟨N, ?_⟩
  rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply]
  have hdenNat : N + 1 ≤ (m + 1) * (m + 2) * (scale * N + 1) := by
    calc
      N + 1 ≤ scale * N + 1 := by
        apply Nat.add_le_add_right
        simpa using Nat.mul_le_mul_right N (Nat.succ_le_iff.mpr hscale)
      _ ≤ (m + 1) * (m + 2) * (scale * N + 1) :=
        Nat.le_mul_of_pos_left _ (by positivity)
  have hden : (N + 1 : ℝ) ≤
      (m + 1 : ℝ) * (m + 2 : ℝ) * (scale * N + 1 : ℝ) := by
    exact_mod_cast hdenNat
  have hrecip := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < N + 1) hden
  norm_num [Nat.cast_mul] at hN hrecip ⊢
  linarith

private theorem degreeTwoBlock_coeff_eq_zero_of_not_mem_range
    (m : ℕ) {delta : ℝ}
    (hdelta : delta ∉ Set.range (degreeTwoBlockEmbedding m)) :
    ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff delta = 0 := by
  apply not_ne_iff.mp
  intro hne
  apply hdelta
  rw [← degreeTwoBlock_support (K := K)]
  exact (HahnSeries.mem_support _ _).mpr hne

private theorem degreeTwoBlock_coeff_smul (r : K) (m : ℕ) (delta : ℝ) :
    ((r • degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff delta =
      r * ((degreeTwoBlock (K := K) m : Berarducci.Series K) : K⟦ℝ⟧).coeff delta := by
  rw [HahnSeries.Nonpositive.coe_smul, HahnSeries.coeff_smul, smul_eq_mul]

/-- The three translated row germs used to certify dimension greater than two. -/
def degreeTwoTranslatedTruncationClass (i : Fin 3) :
    PommersheimShahriari.SeriesQuotientByJAddConstants K :=
  PommersheimShahriari.toSeriesQuotientByJAddConstants (degreeTwoBlock (K := K) i)

theorem degreeTwoTranslatedTruncationClass_linearIndependent :
    LinearIndependent K (degreeTwoTranslatedTruncationClass (K := K)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hsum i
  have hsum' :
      g 0 • degreeTwoTranslatedTruncationClass (K := K) 0 +
          g 1 • degreeTwoTranslatedTruncationClass (K := K) 1 +
          g 2 • degreeTwoTranslatedTruncationClass (K := K) 2 = 0 := by
    simpa [Fin.sum_univ_three] using hsum
  let b : Berarducci.Series K :=
    g 0 • degreeTwoBlock (K := K) 0 + g 1 • degreeTwoBlock (K := K) 1 +
      g 2 • degreeTwoBlock (K := K) 2
  have hzero : PommersheimShahriari.toSeriesQuotientByJAddConstants b = 0 := by
    simpa [b, degreeTwoTranslatedTruncationClass, map_add, map_smul] using hsum'
  have hnear : b ∈ Berarducci.nearConstantSubgroup K :=
    PommersheimShahriari.toSeriesQuotientByJAddConstants_eq_zero_iff.mp hzero
  obtain ⟨eta, heta, hcoeff⟩ :=
    Berarducci.exists_coeff_eq_of_sub_mem_nearConstantSubgroup
      (b := b) (c := 0) (by simpa using hnear)
  obtain ⟨N0, hN0⟩ :=
    exists_degreeTwoBlockEmbedding_gt 0 3 (by norm_num) heta
  have hdelta0 : degreeTwoBlockEmbedding 0 (3 * N0) < 0 := by
    rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply]
    exact neg_neg_of_pos (by positivity)
  have heq0 := hcoeff (degreeTwoBlockEmbedding 0 (3 * N0)) hN0 hdelta0
  have h01 := degreeTwoBlock_coeff_eq_zero_of_not_mem_range (K := K) 1
    (degreeTwoBlock_zero_threeMul_not_mem_one N0)
  have h02 := degreeTwoBlock_coeff_eq_zero_of_not_mem_range (K := K) 2
    (degreeTwoBlock_zero_threeMul_not_mem_two N0)
  have hg0 : g 0 = 0 := by
    simp only [b, Subring.coe_add, HahnSeries.coeff_add,
      degreeTwoBlock_coeff_smul (K := K)] at heq0
    rw [degreeTwoBlock_coeff_embedding (K := K), h01, h02] at heq0
    simpa using heq0
  obtain ⟨N1, hN1⟩ :=
    exists_degreeTwoBlockEmbedding_gt 1 2 (by norm_num) heta
  have hdelta1 : degreeTwoBlockEmbedding 1 (2 * N1) < 0 := by
    rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply]
    exact neg_neg_of_pos (by positivity)
  have heq1 := hcoeff (degreeTwoBlockEmbedding 1 (2 * N1)) hN1 hdelta1
  have h12 := degreeTwoBlock_coeff_eq_zero_of_not_mem_range (K := K) 2
    (degreeTwoBlock_one_twoMul_not_mem_two N1)
  have hg1 : g 1 = 0 := by
    simp only [b, Subring.coe_add, HahnSeries.coeff_add,
      degreeTwoBlock_coeff_smul (K := K)] at heq1
    rw [hg0, degreeTwoBlock_coeff_embedding (K := K), h12] at heq1
    simpa using heq1
  obtain ⟨N2, hN2⟩ :=
    exists_degreeTwoBlockEmbedding_gt 2 1 (by norm_num) heta
  have hdelta2 : degreeTwoBlockEmbedding 2 (1 * N2) < 0 := by
    rw [degreeTwoBlockEmbedding_apply, degreeTwoBlockExponent_apply]
    exact neg_neg_of_pos (by positivity)
  have heq2 := hcoeff (degreeTwoBlockEmbedding 2 (1 * N2)) hN2 hdelta2
  have hg2 : g 2 = 0 := by
    simp only [b, Subring.coe_add, HahnSeries.coeff_add,
      degreeTwoBlock_coeff_smul (K := K)] at heq2
    rw [hg0, hg1, degreeTwoBlock_coeff_embedding (K := K)] at heq2
    simpa using heq2
  fin_cases i <;> assumption

private theorem degreeTwoCutoff_neg (m : ℕ) : degreeTwoCutoff m < 0 := by
  rw [degreeTwoCutoff_apply]
  exact neg_neg_of_pos (by positivity)

theorem degreeTwoTranslatedTruncationClass_mem_translatedTruncationSpan (i : Fin 3) :
    degreeTwoTranslatedTruncationClass (K := K) i ∈
      PommersheimShahriari.translatedTruncationSpan (degreeTwoNonpositive (K := K)) := by
  have h := PommersheimShahriari.translatedTruncationClass_mem_translatedTruncationSpan
    (degreeTwoNonpositive (K := K)) (degreeTwoCutoff_neg i)
  change PommersheimShahriari.translatedTruncationClass (degreeTwoSeries (K := K))
      (degreeTwoCutoff i) ∈
    PommersheimShahriari.translatedTruncationSpan (degreeTwoNonpositive (K := K)) at h
  rw [degreeTwo_translatedTruncationClass_eq_block (K := K)] at h
  exact h

/-- The three row classes, regarded as elements of the witness's translated-truncation span. -/
def degreeTwoTranslatedTruncationSpanVector (i : Fin 3) :
    PommersheimShahriari.translatedTruncationSpan (degreeTwoNonpositive (K := K)) :=
  ⟨degreeTwoTranslatedTruncationClass (K := K) i,
    degreeTwoTranslatedTruncationClass_mem_translatedTruncationSpan (K := K) i⟩

theorem degreeTwoTranslatedTruncationSpanVector_linearIndependent :
    LinearIndependent K (degreeTwoTranslatedTruncationSpanVector (K := K)) := by
  apply LinearIndependent.of_comp
    (PommersheimShahriari.translatedTruncationSpan (degreeTwoNonpositive (K := K))).subtype
  simpa [Function.comp_def, degreeTwoTranslatedTruncationSpanVector] using
    (degreeTwoTranslatedTruncationClass_linearIndependent (K := K))

theorem two_lt_rank_degreeTwo_translatedTruncationSpan :
    (2 : Cardinal) < Module.rank K
      (PommersheimShahriari.translatedTruncationSpan (degreeTwoNonpositive (K := K))) := by
  have h :=
    (degreeTwoTranslatedTruncationSpanVector_linearIndependent (K := K)).cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast,
    Cardinal.lift_id'] at h
  exact (by norm_num : (2 : Cardinal) < 3).trans_le h

private theorem exists_degreeTwoCutoff_gt {eta : ℝ} (heta : eta < 0) :
    ∃ m, eta < degreeTwoCutoff m := by
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt (neg_pos.mpr heta)
  refine ⟨m, ?_⟩
  rw [degreeTwoCutoff_apply]
  linarith

theorem degreeTwoNonpositive_not_mem_nearConstantSubgroup :
    degreeTwoNonpositive (K := K) ∉ Berarducci.nearConstantSubgroup K := by
  intro hnear
  obtain ⟨eta, heta, hcoeff⟩ :=
    Berarducci.exists_coeff_eq_of_sub_mem_nearConstantSubgroup
      (b := degreeTwoNonpositive (K := K)) (c := 0) (by simpa using hnear)
  obtain ⟨m, hm⟩ := exists_degreeTwoCutoff_gt heta
  obtain ⟨n, hn⟩ := exists_degreeTwoBlockEmbedding_gt m 1 (by norm_num)
    (sub_neg.mpr hm)
  have hdeltaEta :
      eta < degreeTwoExponentEmbedding (toLex (m, 1 * n)) := by
    rw [degreeTwoExponentEmbedding_apply,
      degreeTwoExponentPair_eq_cutoff_add_block,
      ← degreeTwoBlockEmbedding_apply]
    linarith
  have hdelta0 :
      degreeTwoExponentEmbedding (toLex (m, 1 * n)) < 0 := by
    rw [degreeTwoExponentEmbedding_apply]
    exact (degreeTwoExponentPair_lt_cutoff m (1 * n)).trans
      (degreeTwoCutoff_neg m)
  have heq := hcoeff (degreeTwoExponentEmbedding (toLex (m, 1 * n)))
    hdeltaEta hdelta0
  change (degreeTwoSeries (K := K)).coeff
      (degreeTwoExponentEmbedding (toLex (m, 1 * n))) = 0 at heq
  rw [degreeTwoSeries_coeff_embedding (K := K)] at heq
  exact one_ne_zero heq

theorem degreeTwoNonpositive_irreducible [CharZero K] :
    Irreducible (degreeTwoNonpositive (K := K)) := by
  apply PommersheimShahriari.irreducible_of_two_lt_rank_translatedTruncationSpan
    (degreeTwoNonpositive_not_mem_nearConstantSubgroup (K := K))
  · left
    change (degreeTwoSeries (K := K)).supportOrderType = _
    exact degreeTwoSeries_supportOrderType (K := K)
  · exact two_lt_rank_degreeTwo_translatedTruncationSpan (K := K)

/-- The degree-two witness with constant coefficient one. -/
def degreeTwoWithConstant : Berarducci.Series K :=
  degreeTwoNonpositive (K := K) + HahnSeries.Nonpositive.C 1

theorem degreeTwoWithConstant_coe :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧) =
      degreeTwoSeries (K := K) + HahnSeries.C 1 := by
  rw [degreeTwoWithConstant, Subring.coe_add, HahnSeries.Nonpositive.coe_C]
  rfl

theorem degreeTwoWithConstant_coeff_embedding (m n : ℕ) :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).coeff
      (degreeTwoExponentEmbedding (toLex (m, n))) = 1 := by
  rw [degreeTwoWithConstant_coe (K := K), HahnSeries.coeff_add,
    degreeTwoSeries_coeff_embedding (K := K), HahnSeries.C_apply]
  have hpair : degreeTwoExponentPair (m, n) ≠ 0 :=
    ((degreeTwoExponentPair_lt_cutoff m n).trans (by
      rw [degreeTwoCutoff_apply]
      exact neg_neg_of_pos (by positivity))).ne
  simp [hpair]

@[simp]
theorem degreeTwoWithConstant_coeff_zero :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).coeff 0 = 1 := by
  rw [degreeTwoWithConstant_coe (K := K), HahnSeries.coeff_add,
    degreeTwoSeries_coeff_zero, HahnSeries.C_apply]
  simp

theorem degreeTwoWithConstant_coeff_eq_zero {x : ℝ}
    (hrange : x ∉ Set.range degreeTwoExponentEmbedding) (hx0 : x ≠ 0) :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).coeff x = 0 := by
  rw [degreeTwoWithConstant_coe (K := K), HahnSeries.coeff_add]
  simp only [HahnSeries.C_apply, HahnSeries.coeff_single, ite_eq_right hx0, add_zero]
  rw [← not_ne_iff, ← HahnSeries.mem_support, degreeTwoSeries_support (K := K)]
  exact hrange

/-- The constant term together with the explicit two-dimensional exponent range is the whole
support of the degree-two witness. -/
theorem degreeTwoWithConstant_support :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).support =
      Set.range degreeTwoExponentEmbedding ∪ {0} := by
  ext x
  constructor
  · intro hx
    by_cases hrange : x ∈ Set.range degreeTwoExponentEmbedding
    · exact Set.mem_union_left _ hrange
    · by_cases hx0 : x = 0
      · exact Set.mem_union_right _ (Set.mem_singleton_iff.mpr hx0)
      · have hzero := degreeTwoWithConstant_coeff_eq_zero (K := K) hrange hx0
        rw [HahnSeries.mem_support] at hx
        exact (hx hzero).elim
  · intro hx
    rcases hx with hrange | hx0
    · obtain ⟨p, rfl⟩ := hrange
      rcases p with ⟨m, n⟩
      change ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).coeff
        (degreeTwoExponentEmbedding (toLex (m, n))) ≠ 0
      rw [degreeTwoWithConstant_coeff_embedding]
      exact one_ne_zero
    · have hx : x = 0 := by simpa using hx0
      subst x
      rw [HahnSeries.mem_support, degreeTwoWithConstant_coeff_zero]
      exact one_ne_zero

theorem degreeTwoWithConstant_constantCoeff :
    HahnSeries.Nonpositive.constantCoeff (degreeTwoWithConstant (K := K)) = 1 := by
  rw [HahnSeries.Nonpositive.constantCoeff_apply, degreeTwoWithConstant_coe (K := K),
    HahnSeries.coeff_add, degreeTwoSeries_coeff_zero, HahnSeries.C_apply]
  simp

private theorem degreeTwoSeries_supportBelow_C_one :
    HahnSeries.SupportBelow (degreeTwoSeries (K := K)) (HahnSeries.C 1) := by
  rw [HahnSeries.supportBelow_iff]
  intro i hi j hj
  rw [degreeTwoSeries_support (K := K)] at hi
  obtain ⟨p, rfl⟩ := hi
  rw [HahnSeries.C_apply] at hj
  have hj0 : j = 0 := HahnSeries.eq_of_mem_support_single hj
  subst j
  rcases p with ⟨m, n⟩
  exact (degreeTwoExponentPair_lt_cutoff m n).trans (degreeTwoCutoff_neg m)
theorem degreeTwoWithConstant_supportOrderType :
    ((degreeTwoWithConstant (K := K) : Berarducci.Series K) : K⟦ℝ⟧).supportOrderType =
      Ordinal.omega0 ^ (2 : Ordinal) + 1 := by
  apply (HahnSeries.supportOrderType_eq_add_iff _ _ _).mpr
  refine ⟨degreeTwoSeries (K := K), HahnSeries.C 1,
    degreeTwoSeries_supportBelow_C_one (K := K), degreeTwoSeries_supportOrderType (K := K),
    ?_, ?_⟩
  · rw [HahnSeries.C_apply, HahnSeries.supportOrderType_single one_ne_zero]
  · exact degreeTwoWithConstant_coe (K := K)

theorem degreeTwoWithConstant_not_mem_nearConstantSubgroup :
    degreeTwoWithConstant (K := K) ∉ Berarducci.nearConstantSubgroup K := by
  intro hnear
  have hconstant : HahnSeries.Nonpositive.C (1 : K) ∈
      Berarducci.nearConstantSubgroup K := by
    rw [Berarducci.mem_nearConstantSubgroup_iff]
    exact ⟨0, (HahnSeries.Nonpositive.negativeMonomialIdeal K).zero_mem,
      1, zero_add _⟩
  apply degreeTwoNonpositive_not_mem_nearConstantSubgroup (K := K)
  have hsub := (Berarducci.nearConstantSubgroup K).sub_mem hnear hconstant
  simpa [degreeTwoWithConstant] using hsub

private theorem translatedTruncation_C_one_eq_zero {x : ℝ} (hx : x < 0) :
    Berarducci.translatedTruncation (HahnSeries.C (1 : K)) x = 0 := by
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext delta
  rw [Berarducci.coeff_translatedTruncation]
  by_cases hdelta : delta ≤ 0
  · rw [ite_eq_left hdelta, HahnSeries.C_apply]
    have hsum : x + delta ≠ 0 := ne_of_lt (add_neg_of_neg_of_nonpos hx hdelta)
    simp [hsum]
  · rw [ite_eq_right hdelta]
    rfl

theorem degreeTwoWithConstant_translatedTruncationClass_eq_block (m : ℕ) :
    PommersheimShahriari.translatedTruncationClass
        (degreeTwoWithConstant (K := K) : K⟦ℝ⟧) (degreeTwoCutoff m) =
      PommersheimShahriari.toSeriesQuotientByJAddConstants (degreeTwoBlock (K := K) m) := by
  rw [PommersheimShahriari.translatedTruncationClass_apply]
  rw [degreeTwoWithConstant_coe (K := K)]
  rw [Berarducci.translatedTruncation_add,
    translatedTruncation_C_one_eq_zero (degreeTwoCutoff_neg m), add_zero]
  simpa only [PommersheimShahriari.translatedTruncationClass_apply] using
    degreeTwo_translatedTruncationClass_eq_block (K := K) m

theorem degreeTwoWithConstant_translatedTruncationClass_mem_translatedTruncationSpan (i : Fin 3) :
    degreeTwoTranslatedTruncationClass (K := K) i ∈
      PommersheimShahriari.translatedTruncationSpan (degreeTwoWithConstant (K := K)) := by
  have h := PommersheimShahriari.translatedTruncationClass_mem_translatedTruncationSpan
    (degreeTwoWithConstant (K := K)) (degreeTwoCutoff_neg i)
  rw [degreeTwoWithConstant_translatedTruncationClass_eq_block (K := K)] at h
  exact h

/-- The three row classes in the constant-one witness's translated-truncation span. -/
def degreeTwoWithConstantTranslatedTruncationSpanVector (i : Fin 3) :
    PommersheimShahriari.translatedTruncationSpan (degreeTwoWithConstant (K := K)) :=
  ⟨degreeTwoTranslatedTruncationClass (K := K) i,
    degreeTwoWithConstant_translatedTruncationClass_mem_translatedTruncationSpan (K := K) i⟩

theorem degreeTwoWithConstant_two_lt_rank_translatedTruncationSpan :
    (2 : Cardinal) < Module.rank K
      (PommersheimShahriari.translatedTruncationSpan (degreeTwoWithConstant (K := K))) := by
  have hli : LinearIndependent K
      (degreeTwoWithConstantTranslatedTruncationSpanVector (K := K)) := by
    apply LinearIndependent.of_comp
      (PommersheimShahriari.translatedTruncationSpan (degreeTwoWithConstant (K := K))).subtype
    simpa [Function.comp_def, degreeTwoWithConstantTranslatedTruncationSpanVector] using
      (degreeTwoTranslatedTruncationClass_linearIndependent (K := K))
  have h := hli.cardinal_lift_le_rank
  simp only [Cardinal.mk_fintype, Fintype.card_fin, Cardinal.lift_natCast,
    Cardinal.lift_id'] at h
  exact (by norm_num : (2 : Cardinal) < 3).trans_le h
theorem degreeTwoWithConstant_irreducible [CharZero K] :
    Irreducible (degreeTwoWithConstant (K := K)) := by
  apply PommersheimShahriari.irreducible_of_two_lt_rank_translatedTruncationSpan
    (degreeTwoWithConstant_not_mem_nearConstantSubgroup (K := K))
  · exact Or.inr (degreeTwoWithConstant_supportOrderType (K := K))
  · exact degreeTwoWithConstant_two_lt_rank_translatedTruncationSpan (K := K)


/-- Coefficient maps along a field homomorphism out of `ℝ` carry the degree-two series with
constant term over `ℝ` to the same series over the target field: all its coefficients are `0` or
`1`. -/
theorem nonpositiveCoefficientMap_degreeTwoWithConstant {E : Type*} [Field E] (f : ℝ →+* E) :
    HahnSeries.Nonpositive.nonpositiveCoefficientMap f (degreeTwoWithConstant (K := ℝ)) =
      degreeTwoWithConstant (K := E) := by
  apply Subtype.ext
  apply HahnSeries.coeff_injective
  funext x
  rw [HahnSeries.Nonpositive.coe_nonpositiveCoefficientMap]
  by_cases hx : x ∈ Set.range degreeTwoExponentEmbedding
  · obtain ⟨p, rfl⟩ := hx
    rcases p with ⟨m, n⟩
    have hR := degreeTwoWithConstant_coeff_embedding (K := ℝ) m n
    have hE := degreeTwoWithConstant_coeff_embedding (K := E) m n
    rw [degreeTwoExponentEmbedding_apply] at hR hE
    change f (((degreeTwoWithConstant (K := ℝ) : Berarducci.Series ℝ) : ℝ⟦ℝ⟧).coeff
        (degreeTwoExponentPair (m, n))) =
      ((degreeTwoWithConstant (K := E) : Berarducci.Series E) : E⟦ℝ⟧).coeff
        (degreeTwoExponentPair (m, n))
    rw [hR, hE, map_one]
  · by_cases hx0 : x = 0
    · subst hx0
      rw [degreeTwoWithConstant_coeff_zero, degreeTwoWithConstant_coeff_zero, map_one]
    · rw [degreeTwoWithConstant_coeff_eq_zero hx hx0,
        degreeTwoWithConstant_coeff_eq_zero hx hx0, map_zero]

end PommersheimShahriari.DegreeTwoExample
