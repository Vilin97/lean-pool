/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
/-!
# The Lubin–Tate endomorphism commutation law: the first theta identity in equal characteristic

For the normalization `pi = T` and `bar_pi = u⁻¹ T`, this file constructs
the Lubin--Tate endomorphism `[u]` over the base integer ring `k[[T]]` and
proves the first identity of Corollary the Lubin–Tate endomorphism commutation law,

`theta^phi = theta o [u]`.

The endomorphism `[u]` is constructed independently from `theta`: its
linear coefficient is `u`, and its higher additive coefficients are the
unique contracting solutions forced by commutation with
`Y^q + bar_pi Y`.
-/

noncomputable section

open scoped PowerSeries


universe u v

namespace LubinTate
namespace EqualCharacteristic

variable {k : Type u} [Field k] [Finite k]

/-- The source prime `bar_pi = u⁻¹ T`, before extension of coefficients to
the completed maximal unramified ring. -/
noncomputable def equalCharacteristicSourceUniformizer
    (u : k⟦X⟧ˣ) : k⟦X⟧ :=
  ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) * PowerSeries.X

/-- The contracting coefficient obtained after dividing the commutation
equation for `[u]` by `bar_pi`. -/
noncomputable def equalCharacteristicSourceBracketGamma
    (u : k⟦X⟧ˣ) (j : ℕ) : k⟦X⟧ :=
  (u : k⟦X⟧) *
    ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧) ^ (Nat.card k ^ j) *
      PowerSeries.X ^ (Nat.card k ^ j - 1)

/-- Positive-index source bracket gamma terms have zero constant coefficient. -/
theorem equalCharacteristicSourceBracketGamma_constantCoeff
    (u : k⟦X⟧ˣ) (j : ℕ) (hj : 0 < j) :
    PowerSeries.coeff 0 (equalCharacteristicSourceBracketGamma u j) = 0 := by
  have hq : 1 < Nat.card k := Finite.one_lt_card
  have hpow : 0 < Nat.card k ^ j - 1 :=
    Nat.sub_pos_of_lt (Nat.one_lt_pow hj.ne' hq)
  simp [equalCharacteristicSourceBracketGamma, hpow.ne']

/-- The numerator on the right of the coefficient equation for `[u]`. -/
noncomputable def equalCharacteristicSourceBracketNumerator
    (a : k⟦X⟧) : k⟦X⟧ :=
  a - a ^ Nat.card k

/-- The source bracket numerator has zero constant coefficient. -/
theorem equalCharacteristicSourceBracketNumerator_constantCoeff
    (a : k⟦X⟧) :
    PowerSeries.coeff 0 (equalCharacteristicSourceBracketNumerator a) = 0 := by
  let : Fintype k := Fintype.ofFinite k
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply,
    equalCharacteristicSourceBracketNumerator,
    map_sub, map_pow, Nat.card_eq_fintype_card,
    FiniteField.pow_card, sub_self]

/-- Division of `a-a^q` by `bar_pi = u⁻¹T`. -/
noncomputable def equalCharacteristicSourceBracketBeta
    (u : k⟦X⟧ˣ) (a : k⟦X⟧) : k⟦X⟧ :=
  (u : k⟦X⟧) *
    equalCharacteristicPowerSeriesTail
      (equalCharacteristicSourceBracketNumerator a)

/-- The additive coefficients of the Lubin--Tate endomorphism `[u]` for
the source series `Y^q + (u⁻¹T)Y`. -/
noncomputable def equalCharacteristicSourceBracketCoefficient
    (u : k⟦X⟧ˣ) : ℕ → k⟦X⟧
  | 0 => (u : k⟦X⟧)
  | j + 1 =>
      contractingFrobeniusEquationSolution (R := k)
        (RingHom.id k)
        (equalCharacteristicSourceBracketGamma u (j + 1))
        (equalCharacteristicSourceBracketBeta u
          (equalCharacteristicSourceBracketCoefficient u j))

omit [Finite k] in
/-- The zeroth source bracket coefficient is the source unit itself. -/
@[simp]
theorem equalCharacteristicSourceBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicSourceBracketCoefficient u 0 = (u : k⟦X⟧) :=
  rfl

/-- Successive source bracket coefficients satisfy the defining Artin–Schreier equation. -/
theorem equalCharacteristicSourceBracketCoefficient_succ_equation
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicSourceBracketCoefficient u (j + 1) -
        equalCharacteristicSourceBracketGamma u (j + 1) *
          equalCharacteristicSourceBracketCoefficient u (j + 1) =
      equalCharacteristicSourceBracketBeta u
        (equalCharacteristicSourceBracketCoefficient u j) := by
  rw [equalCharacteristicSourceBracketCoefficient]
  have hgamma := equalCharacteristicSourceBracketGamma_constantCoeff
    u (j + 1) (Nat.zero_lt_succ j)
  apply (sub_eq_iff_eq_add).2
  simpa using
    (contractingFrobeniusEquationSolution_spec (R := k)
      (RingHom.id k)
      (equalCharacteristicSourceBracketGamma u (j + 1))
      (equalCharacteristicSourceBracketBeta u
        (equalCharacteristicSourceBracketCoefficient u j)) hgamma)

/-- The coefficient comparison equivalent to commutation of `[u]` with
`Y^q + bar_pi Y`. -/
theorem equalCharacteristicSourceBracketCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicSourceUniformizer u *
          equalCharacteristicSourceBracketCoefficient u (j + 1) -
        equalCharacteristicSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicSourceBracketCoefficient u (j + 1) =
      equalCharacteristicSourceBracketCoefficient u j -
        equalCharacteristicSourceBracketCoefficient u j ^ Nat.card k := by
  let qj := Nat.card k ^ (j + 1)
  let a := equalCharacteristicSourceBracketCoefficient u (j + 1)
  let b := equalCharacteristicSourceBracketCoefficient u j
  let v : k⟦X⟧ := ((u⁻¹ : k⟦X⟧ˣ) : k⟦X⟧)
  have hqj : 1 ≤ qj := by
    exact Nat.one_le_iff_ne_zero.mpr
      (pow_ne_zero _ Nat.card_pos.ne')
  have hvu : v * (u : k⟦X⟧) = 1 := by
    change (((u⁻¹ * u : k⟦X⟧ˣ) : k⟦X⟧)) = 1
    simp
  have hpiGamma :
      equalCharacteristicSourceUniformizer u *
          equalCharacteristicSourceBracketGamma u (j + 1) =
        equalCharacteristicSourceUniformizer u ^ qj := by
    rw [equalCharacteristicSourceUniformizer,
      equalCharacteristicSourceBracketGamma, mul_pow]
    change (v * PowerSeries.X) *
        ((u : k⟦X⟧) * v ^ qj * PowerSeries.X ^ (qj - 1)) =
      v ^ qj * PowerSeries.X ^ qj
    calc
      _ = (v * (u : k⟦X⟧)) * v ^ qj *
          (PowerSeries.X ^ (qj - 1) * PowerSeries.X) := by
            ac_rfl
      _ = v ^ qj * PowerSeries.X ^ qj := by
        rw [hvu, one_mul, ← pow_succ, Nat.sub_add_cancel hqj]
  have htail :
      PowerSeries.X *
          equalCharacteristicPowerSeriesTail
            (equalCharacteristicSourceBracketNumerator b) =
        equalCharacteristicSourceBracketNumerator b := by
    have hsplit := equalCharacteristicPowerSeries_eq_X_mul_tail_add_C
      (equalCharacteristicSourceBracketNumerator b)
    rw [equalCharacteristicSourceBracketNumerator_constantCoeff] at hsplit
    simpa only [map_zero, add_zero] using hsplit.symm
  have hpiBeta :
      equalCharacteristicSourceUniformizer u *
          equalCharacteristicSourceBracketBeta u b =
        equalCharacteristicSourceBracketNumerator b := by
    rw [equalCharacteristicSourceUniformizer,
      equalCharacteristicSourceBracketBeta]
    change (v * PowerSeries.X) *
        ((u : k⟦X⟧) *
          equalCharacteristicPowerSeriesTail
            (equalCharacteristicSourceBracketNumerator b)) = _
    calc
      _ = (v * (u : k⟦X⟧)) *
          (PowerSeries.X *
            equalCharacteristicPowerSeriesTail
              (equalCharacteristicSourceBracketNumerator b)) := by
            ac_rfl
      _ = _ := by rw [hvu, one_mul, htail]
  have hrec := congrArg
    (fun z : k⟦X⟧ ↦ equalCharacteristicSourceUniformizer u * z)
    (equalCharacteristicSourceBracketCoefficient_succ_equation u j)
  change equalCharacteristicSourceUniformizer u *
      (a - equalCharacteristicSourceBracketGamma u (j + 1) * a) =
    equalCharacteristicSourceUniformizer u *
      equalCharacteristicSourceBracketBeta u b at hrec
  rw [mul_sub, ← mul_assoc, hpiGamma, hpiBeta] at hrec
  simpa [a, b, qj, equalCharacteristicSourceBracketNumerator] using hrec

/-- The Lubin--Tate endomorphism `[u]` over the base integer ring. -/
noncomputable def equalCharacteristicSourceBracket
    (u : k⟦X⟧ˣ) : (k⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicSourceBracketCoefficient u)

/-- The source bracket coefficient at `q ^ j` is its `j`th recursive coefficient. -/
@[simp]
theorem equalCharacteristicSourceBracket_coeff_pow
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicSourceBracket u) =
      equalCharacteristicSourceBracketCoefficient u j := by
  exact equalCharacteristicQAdditiveSeries_coeff_pow k _ j

/-- The source bracket has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicSourceBracket_constantCoeff
    (u : k⟦X⟧ˣ) :
    PowerSeries.constantCoeff (equalCharacteristicSourceBracket u) = 0 := by
  exact equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The source bracket may be substituted into another power series. -/
theorem equalCharacteristicSourceBracket_hasSubst
    (u : k⟦X⟧ˣ) :
    PowerSeries.HasSubst (equalCharacteristicSourceBracket u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicSourceBracket_constantCoeff u)

/-- Coefficients of `[u]` after passing to the completed maximal unramified
integer ring. -/
noncomputable def equalCharacteristicCompletedSourceBracketCoefficient
    (u : k⟦X⟧ˣ) (j : ℕ) : (AlgebraicClosure k)⟦X⟧ :=
  PowerSeries.map (algebraMap k (AlgebraicClosure k))
    (equalCharacteristicSourceBracketCoefficient u j)

/-- The same base-defined Lubin--Tate endomorphism `[u]`, viewed over the
completed maximal unramified integer ring. -/
noncomputable def equalCharacteristicCompletedSourceBracket
    (u : k⟦X⟧ˣ) : ((AlgebraicClosure k)⟦X⟧)⟦X⟧ :=
  equalCharacteristicQAdditiveSeries k
    (equalCharacteristicCompletedSourceBracketCoefficient u)

/-- The completed source bracket records its `j`th coefficient at exponent `q ^ j`. -/
@[simp]
theorem equalCharacteristicCompletedSourceBracket_coeff_pow
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.coeff (Nat.card k ^ j)
        (equalCharacteristicCompletedSourceBracket u) =
      equalCharacteristicCompletedSourceBracketCoefficient u j := by
  exact equalCharacteristicQAdditiveSeries_coeff_pow k _ j

/-- The completed source bracket has zero constant coefficient. -/
@[simp]
theorem equalCharacteristicCompletedSourceBracket_constantCoeff
    (u : k⟦X⟧ˣ) :
    PowerSeries.constantCoeff
        (equalCharacteristicCompletedSourceBracket u) = 0 := by
  exact equalCharacteristicQAdditiveSeries_constantCoeff k _

/-- The completed source bracket is valid as a substitution series. -/
theorem equalCharacteristicCompletedSourceBracket_hasSubst
    (u : k⟦X⟧ˣ) :
    PowerSeries.HasSubst (equalCharacteristicCompletedSourceBracket u) :=
  PowerSeries.HasSubst.of_constantCoeff_zero'
    (equalCharacteristicCompletedSourceBracket_constantCoeff u)

omit [Finite k] in
/-- The zeroth completed bracket coefficient is the scalar extension of the source unit. -/
@[simp]
theorem equalCharacteristicCompletedSourceBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicCompletedSourceBracketCoefficient u 0 =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) (u : k⟦X⟧) := by
  simp [equalCharacteristicCompletedSourceBracketCoefficient]

omit [Finite k] in
/-- Scalar extension sends the source uniformizer to its completed counterpart. -/
theorem equalCharacteristicSourceUniformizer_map
    (u : k⟦X⟧ˣ) :
    PowerSeries.map (algebraMap k (AlgebraicClosure k))
        (equalCharacteristicSourceUniformizer u) =
      equalCharacteristicCompletedSourceUniformizer u := by
  simp [equalCharacteristicSourceUniformizer,
    equalCharacteristicCompletedSourceUniformizer]

/-- Frobenius fixes every coefficient coming from the base integer ring. -/
theorem equalCharacteristicPowerSeriesFrobenius_map_algebraMap
    (a : k⟦X⟧) :
    equalCharacteristicPowerSeriesFrobenius k
        (PowerSeries.map (algebraMap k (AlgebraicClosure k)) a) =
      PowerSeries.map (algebraMap k (AlgebraicClosure k)) a := by
  let : Fintype k := Fintype.ofFinite k
  apply PowerSeries.ext
  intro n
  rw [equalCharacteristicPowerSeriesFrobenius_coeff,
    PowerSeries.coeff_map]
  calc
    (algebraMap k (AlgebraicClosure k) (PowerSeries.coeff n a)) ^
          Nat.card k =
        algebraMap k (AlgebraicClosure k)
          ((PowerSeries.coeff n a) ^ Nat.card k) := by
            rw [map_pow]
    _ = _ := by
      rw [Nat.card_eq_fintype_card,
        FiniteField.pow_card]

/-- In particular the base-defined endomorphism `[u]` is fixed by
coefficient Frobenius. -/
theorem equalCharacteristicCompletedSourceBracket_frobenius
    (u : k⟦X⟧ˣ) :
    PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (equalCharacteristicCompletedSourceBracket u) =
      equalCharacteristicCompletedSourceBracket u := by
  rw [equalCharacteristicCompletedSourceBracket,
    equalCharacteristicQAdditiveSeries_map]
  congr 1
  funext j
  exact equalCharacteristicPowerSeriesFrobenius_map_algebraMap
    (equalCharacteristicSourceBracketCoefficient u j)

/-- The coefficient equation for `[u]`, after extension to the completed
maximal unramified integer ring. -/
theorem equalCharacteristicCompletedSourceBracketCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    equalCharacteristicCompletedSourceUniformizer u *
          equalCharacteristicCompletedSourceBracketCoefficient u (j + 1) -
        equalCharacteristicCompletedSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicCompletedSourceBracketCoefficient u (j + 1) =
      equalCharacteristicCompletedSourceBracketCoefficient u j -
        equalCharacteristicCompletedSourceBracketCoefficient u j ^ Nat.card k := by
  have h := congrArg
    (PowerSeries.map (algebraMap k (AlgebraicClosure k)))
    (equalCharacteristicSourceBracketCoefficient_succ_comparison u j)
  simpa [equalCharacteristicCompletedSourceBracketCoefficient,
    map_sub, map_mul, map_pow,
    equalCharacteristicSourceUniformizer_map] using h

/-- The Lubin–Tate endomorphism commutation law: the independently constructed `[u]` commutes with the
source Lubin--Tate series `Y^q + (u⁻¹T)Y`. -/
theorem equalCharacteristicCompletedSourceBracket_commutes
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst (equalCharacteristicCompletedSourceBracket u)
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicCompletedSourceUniformizer u)) =
      PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicCompletedSourceUniformizer u))
        (equalCharacteristicCompletedSourceBracket u) := by
  rw [equalCharacteristicCompletedSourceBracket,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries,
    equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries]
  congr 1
  funext j
  cases j with
  | zero =>
      simp [equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicLubinTateSubstitutionCoefficient, mul_comm]
  | succ j =>
      rw [equalCharacteristicLubinTatePostcompositionCoefficient,
        equalCharacteristicLubinTateSubstitutionCoefficient]
      have h :=
        equalCharacteristicCompletedSourceBracketCoefficient_succ_comparison
          u j
      linear_combination h

section QAdditiveComposition

variable {R : Type v} [CommRing R] [Nontrivial R] [Algebra k R]

/-- A `q^i`-th power shifts additive exponents by `i`; the coefficient at
`q^n` is zero for `n<i` and otherwise is the `q^i`-th power of the
coefficient at `q^(n-i)`. -/
theorem equalCharacteristicQAdditiveSeries_pow_card_pow
    (a : ℕ → R) (i : ℕ) :
    equalCharacteristicQAdditiveSeries k a ^ (Nat.card k ^ i) =
      equalCharacteristicQAdditiveSeries k (fun n ↦
        if i ≤ n then a (n - i) ^ (Nat.card k ^ i) else 0) := by
  induction i with
  | zero =>
      simp
  | succ i ih =>
      rw [pow_succ, pow_mul, ih,
        equalCharacteristicQAdditiveSeries_pow_card]
      congr 1
      funext n
      cases n with
      | zero =>
          simp [equalCharacteristicQAdditiveShift]
      | succ n =>
          by_cases hin : i ≤ n
          · have hisucc : i + 1 ≤ n + 1 := Nat.succ_le_succ hin
            simp [equalCharacteristicQAdditiveShift, hin, hisucc,
              pow_mul]
          · have hisucc : ¬ i + 1 ≤ n + 1 := by omega
            simp [equalCharacteristicQAdditiveShift, hin, hisucc,
              Nat.card_pos.ne']

/-- Coefficient form of the preceding shift formula. -/
theorem equalCharacteristicQAdditiveSeries_pow_card_pow_coeff
    (a : ℕ → R) (i n : ℕ) :
    PowerSeries.coeff (Nat.card k ^ n)
        (equalCharacteristicQAdditiveSeries k a ^ (Nat.card k ^ i)) =
      if i ≤ n then a (n - i) ^ (Nat.card k ^ i) else 0 := by
  rw [equalCharacteristicQAdditiveSeries_pow_card_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow]

/-- The finite convolution of coefficients occurring in the composition
of two `q`-additive series. -/
def equalCharacteristicQAdditiveCompositionCoefficient
    (b a : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1),
    b i * a (n - i) ^ (Nat.card k ^ i)

/-- Composition of two `q`-additive series is again `q`-additive, with the
usual finite Frobenius convolution of coefficients. -/
theorem equalCharacteristicQAdditiveSeries_subst_qAdditiveSeries
    (b a : ℕ → R) :
    PowerSeries.subst (equalCharacteristicQAdditiveSeries k a)
        (equalCharacteristicQAdditiveSeries k b) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicQAdditiveCompositionCoefficient (k := k) b a) := by
  let A := equalCharacteristicQAdditiveSeries k a
  let B := equalCharacteristicQAdditiveSeries k b
  have hA : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (equalCharacteristicQAdditiveSeries_constantCoeff k a)
  apply PowerSeries.ext
  intro n
  by_cases hn : IsEqualCharacteristicAdditiveExponent k n
  · obtain ⟨r, rfl⟩ := hn
    rw [equalCharacteristicQAdditiveSeries_coeff_pow,
      PowerSeries.coeff_subst' hA]
    let F : ℕ → R := fun d ↦
      PowerSeries.coeff d B •
        PowerSeries.coeff (Nat.card k ^ r) (A ^ d)
    change ∑ᶠ d : ℕ, F d = _
    have hsupport : Function.support F ⊆
        (((Finset.range (r + 1)).image (fun i ↦ Nat.card k ^ i) :
          Finset ℕ) : Set ℕ) := by
      intro d hd
      change F d ≠ 0 at hd
      by_cases hde : IsEqualCharacteristicAdditiveExponent k d
      · obtain ⟨i, rfl⟩ := hde
        by_cases hir : i ≤ r
        · exact Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨i, Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hir), rfl⟩)
        · have hzero :=
            equalCharacteristicQAdditiveSeries_pow_card_pow_coeff
              (k := k) a i r
          rw [ite_eq_right hir] at hzero
          simp [F, A, hzero] at hd
      · have hzero :=
          equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde
        simp [F, B, hzero] at hd
    rw [finsum_eq_sum_of_support_subset F hsupport,
      Finset.sum_image]
    · simp only [F, A, B,
        equalCharacteristicQAdditiveSeries_coeff_pow,
        equalCharacteristicQAdditiveSeries_pow_card_pow_coeff,
        equalCharacteristicQAdditiveCompositionCoefficient]
      apply Finset.sum_congr rfl
      intro i hi
      have hir : i ≤ r := by
        exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      simp [hir, smul_eq_mul]
    · intro i hi j hj hij
      exact (natCard_pow_injective k hij)
  · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k _ n hn,
      PowerSeries.coeff_subst' hA,
      finsum_eq_zero_of_forall_eq_zero]
    intro d
    by_cases hde : IsEqualCharacteristicAdditiveExponent k d
    · obtain ⟨i, rfl⟩ := hde
      rw [equalCharacteristicQAdditiveSeries_pow_card_pow]
      have hzero := equalCharacteristicQAdditiveSeries_coeff_eq_zero
        k (fun m ↦ if i ≤ m then a (m - i) ^ (Nat.card k ^ i) else 0)
        n hn
      simp [hzero]
    · rw [equalCharacteristicQAdditiveSeries_coeff_eq_zero k b d hde]
      simp

end QAdditiveComposition

/-- Coefficients of `theta o [u]`.  The sum is finite at every additive
exponent. -/
noncomputable def equalCharacteristicThetaAfterBracketCoefficient
    (u : k⟦X⟧ˣ) : ℕ → (AlgebraicClosure k)⟦X⟧ :=
  equalCharacteristicQAdditiveCompositionCoefficient (k := k)
    (equalCharacteristicThetaCoefficient u)
    (equalCharacteristicCompletedSourceBracketCoefficient u)

/-- The formal composite `theta o [u]` is the additive series with the
preceding finite convolution coefficients. -/
theorem equalCharacteristicThetaSeries_subst_sourceBracket
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst (equalCharacteristicCompletedSourceBracket u)
        (equalCharacteristicThetaSeries u) =
      equalCharacteristicQAdditiveSeries k
        (equalCharacteristicThetaAfterBracketCoefficient u) := by
  exact equalCharacteristicQAdditiveSeries_subst_qAdditiveSeries
    (k := k) (equalCharacteristicThetaCoefficient u)
    (equalCharacteristicCompletedSourceBracketCoefficient u)

/-- The linear term of `theta o [u]` is `phi(b₀)`, by the semilinear
equation `phi(b₀)=u b₀`. -/
theorem equalCharacteristicThetaAfterBracketCoefficient_zero
    (u : k⟦X⟧ˣ) :
    equalCharacteristicThetaAfterBracketCoefficient u 0 =
      equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicThetaCoefficient u 0) := by
  have hsemi := equalCharacteristicPowerSeriesFrobenius_semilinearUnit
    (k := k) (u : k⟦X⟧)
      (by
        intro hzero
        have hunit := PowerSeries.isUnit_constantCoeff (u : k⟦X⟧) u.isUnit
        apply hunit.ne_zero
        simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hzero)
  rw [equalCharacteristicThetaCoefficient_zero]
  simpa [equalCharacteristicThetaAfterBracketCoefficient,
    equalCharacteristicQAdditiveCompositionCoefficient,
    equalCharacteristicCompletedSourceBracketCoefficient,
    mul_comm] using hsemi.symm

/-- The first-identity candidate `theta o [u]` satisfies the same
Frobenius-intertwining equation as `theta^phi`.  This is the formal-series
calculation in the proof of Corollary the Lubin–Tate endomorphism commutation law. -/
theorem equalCharacteristicThetaSeries_subst_sourceBracket_intertwines
    (u : k⟦X⟧ˣ) :
    PowerSeries.subst
        (equalCharacteristicCompletedLubinTateSeries (k := k)
          (equalCharacteristicCompletedSourceUniformizer u))
        (PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
          (PowerSeries.subst (equalCharacteristicCompletedSourceBracket u)
            (equalCharacteristicThetaSeries u))) =
      PowerSeries.subst
        (PowerSeries.subst (equalCharacteristicCompletedSourceBracket u)
          (equalCharacteristicThetaSeries u))
        (equalCharacteristicCompletedLubinTateSeries
          (k := k) PowerSeries.X) := by
  let H := equalCharacteristicCompletedSourceBracket u
  let Ebar := equalCharacteristicCompletedLubinTateSeries (k := k)
    (equalCharacteristicCompletedSourceUniformizer u)
  let E := equalCharacteristicCompletedLubinTateSeries
    (k := k) (PowerSeries.X : (AlgebraicClosure k)⟦X⟧)
  let Theta := equalCharacteristicThetaSeries u
  let ThetaF := equalCharacteristicThetaSeriesFrobenius u
  have hH : PowerSeries.HasSubst H :=
    equalCharacteristicCompletedSourceBracket_hasSubst u
  have hEbar : PowerSeries.HasSubst Ebar :=
    equalCharacteristicCompletedLubinTateSeries_hasSubst
      (equalCharacteristicCompletedSourceUniformizer u)
  have hTheta : PowerSeries.HasSubst Theta :=
    equalCharacteristicThetaSeries_hasSubst u
  have hmap :
      PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
          (PowerSeries.subst H Theta) =
        PowerSeries.subst H ThetaF := by
    change (PowerSeries.subst H Theta).map
        (equalCharacteristicPowerSeriesFrobenius k) = _
    rw [PowerSeries.map_subst hH]
    have hHfixed :
        PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k) H = H := by
      simpa only [H] using
        equalCharacteristicCompletedSourceBracket_frobenius u
    change MvPowerSeries.map
        (equalCharacteristicPowerSeriesFrobenius k) H = H at hHfixed
    rw [hHfixed]
    rfl
  change PowerSeries.subst Ebar
      (PowerSeries.map (equalCharacteristicPowerSeriesFrobenius k)
        (PowerSeries.subst H Theta)) =
    PowerSeries.subst (PowerSeries.subst H Theta) E
  calc
    _ = PowerSeries.subst Ebar (PowerSeries.subst H ThetaF) := by rw [hmap]
    _ = PowerSeries.subst (PowerSeries.subst Ebar H) ThetaF :=
      PowerSeries.subst_comp_subst_apply hH hEbar ThetaF
    _ = PowerSeries.subst (PowerSeries.subst H Ebar) ThetaF := by
      rw [equalCharacteristicCompletedSourceBracket_commutes u]
    _ = PowerSeries.subst H (PowerSeries.subst Ebar ThetaF) :=
      (PowerSeries.subst_comp_subst_apply hEbar hH ThetaF).symm
    _ = PowerSeries.subst H (PowerSeries.subst Theta E) := by
      rw [equalCharacteristicThetaSeries_intertwines u]
    _ = PowerSeries.subst (PowerSeries.subst H Theta) E :=
      PowerSeries.subst_comp_subst_apply hTheta hH E

/-- Reading the coefficient at `q^(j+1)` in a `q`-additive Frobenius
intertwiner gives exactly the contracting recursion from the contracting Frobenius equation. -/
theorem equalCharacteristicQAdditiveIntertwiner_succ_comparison
    (u : k⟦X⟧ˣ)
    (c : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hintertwines :
      PowerSeries.subst
          (equalCharacteristicCompletedLubinTateSeries (k := k)
            (equalCharacteristicCompletedSourceUniformizer u))
          (equalCharacteristicQAdditiveSeries k
            (fun i ↦ equalCharacteristicPowerSeriesFrobenius k (c i))) =
        PowerSeries.subst (equalCharacteristicQAdditiveSeries k c)
          (equalCharacteristicCompletedLubinTateSeries
            (k := k) PowerSeries.X))
    (j : ℕ) :
    PowerSeries.X * c (j + 1) -
        equalCharacteristicCompletedSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) =
      equalCharacteristicPowerSeriesFrobenius k (c j) -
        c j ^ Nat.card k := by
  rw [equalCharacteristicQAdditiveSeries_subst_completedLubinTateSeries,
    equalCharacteristicCompletedLubinTateSeries_subst_qAdditiveSeries]
    at hintertwines
  have hcoeff := congrArg
    (PowerSeries.coeff (Nat.card k ^ (j + 1))) hintertwines
  rw [equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicQAdditiveSeries_coeff_pow,
    equalCharacteristicLubinTateSubstitutionCoefficient,
    equalCharacteristicLubinTatePostcompositionCoefficient] at hcoeff
  linear_combination -hcoeff

/-- Two `q`-additive Frobenius intertwiners with the same linear
coefficient coincide.  This is the uniqueness step of the contracting Frobenius equation,
in the coefficient recursion used by Corollary the Lubin–Tate endomorphism commutation law. -/
theorem equalCharacteristicQAdditiveIntertwinerCoefficient_unique
    (u : k⟦X⟧ˣ)
    (c d : ℕ → (AlgebraicClosure k)⟦X⟧)
    (hzero : c 0 = d 0)
    (hc : ∀ j : ℕ,
      PowerSeries.X * c (j + 1) -
          equalCharacteristicCompletedSourceUniformizer u ^
              (Nat.card k ^ (j + 1)) *
            equalCharacteristicPowerSeriesFrobenius k (c (j + 1)) =
        equalCharacteristicPowerSeriesFrobenius k (c j) -
          c j ^ Nat.card k)
    (hd : ∀ j : ℕ,
      PowerSeries.X * d (j + 1) -
          equalCharacteristicCompletedSourceUniformizer u ^
              (Nat.card k ^ (j + 1)) *
            equalCharacteristicPowerSeriesFrobenius k (d (j + 1)) =
        equalCharacteristicPowerSeriesFrobenius k (d j) -
          d j ^ Nat.card k) :
    c = d := by
  funext j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      have hcj := hc j
      have hdj := hd j
      rw [ih] at hcj
      let delta := c (j + 1) - d (j + 1)
      have hdiff :
          PowerSeries.X * delta -
              equalCharacteristicCompletedSourceUniformizer u ^
                  (Nat.card k ^ (j + 1)) *
                equalCharacteristicPowerSeriesFrobenius k delta = 0 := by
        dsimp only [delta]
        rw [map_sub]
        linear_combination hcj - hdj
      have hhom :
          delta - equalCharacteristicThetaGamma u (j + 1) *
              equalCharacteristicPowerSeriesFrobenius k delta = 0 := by
        apply PowerSeries.X_mul_injective
        change PowerSeries.X *
            (delta - equalCharacteristicThetaGamma u (j + 1) *
              equalCharacteristicPowerSeriesFrobenius k delta) =
          PowerSeries.X * 0
        rw [mul_sub, ← mul_assoc,
          equalCharacteristicThetaGamma_mul_X u (j + 1)
            (Nat.zero_lt_succ j), mul_zero]
        exact hdiff
      have hgamma := equalCharacteristicThetaGamma_constantCoeff u
        (j + 1) (Nat.zero_lt_succ j)
      have hunique := existsUnique_contractingFrobeniusEquation
        (equalCharacteristicCoefficientFrobenius k).toRingHom
        (equalCharacteristicThetaGamma u (j + 1)) 0 hgamma
      have hzeroSolution :
          (0 : (AlgebraicClosure k)⟦X⟧) -
              equalCharacteristicThetaGamma u (j + 1) *
                equalCharacteristicPowerSeriesFrobenius k 0 = 0 := by
        simp
      have hdelta : delta = 0 :=
        hunique.unique hhom hzeroSolution
      exact sub_eq_zero.mp (by simpa only [delta] using hdelta)

/-- The source prime is fixed by arithmetic Frobenius because it is
defined over the base field. -/
theorem equalCharacteristicCompletedSourceUniformizer_frobenius
    (u : k⟦X⟧ˣ) :
    equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicCompletedSourceUniformizer u) =
      equalCharacteristicCompletedSourceUniformizer u := by
  rw [← equalCharacteristicSourceUniformizer_map]
  exact equalCharacteristicPowerSeriesFrobenius_map_algebraMap
    (equalCharacteristicSourceUniformizer u)

/-- Applying Frobenius to theta's defining coefficient comparison gives
the recursion for the coefficient sequence of `theta^phi`. -/
theorem equalCharacteristicThetaFrobeniusCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u (j + 1)) -
        equalCharacteristicCompletedSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicPowerSeriesFrobenius k
              (equalCharacteristicThetaCoefficient u (j + 1))) =
      equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u j)) -
        equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaCoefficient u j) ^ Nat.card k := by
  have h := congrArg (equalCharacteristicPowerSeriesFrobenius k)
    (equalCharacteristicThetaCoefficient_succ_comparison u j)
  simpa [map_sub, map_mul, map_pow,
    equalCharacteristicThetaBetaNumerator,
    equalCharacteristicPowerSeriesFrobenius_X,
    equalCharacteristicCompletedSourceUniformizer_frobenius] using h

/-- The finite convolution coefficients of `theta o [u]` satisfy the same
recursion, because `[u]` commutes with the source Lubin--Tate series. -/
theorem equalCharacteristicThetaAfterBracketCoefficient_succ_comparison
    (u : k⟦X⟧ˣ) (j : ℕ) :
    PowerSeries.X *
          equalCharacteristicThetaAfterBracketCoefficient u (j + 1) -
        equalCharacteristicCompletedSourceUniformizer u ^
            (Nat.card k ^ (j + 1)) *
          equalCharacteristicPowerSeriesFrobenius k
            (equalCharacteristicThetaAfterBracketCoefficient u (j + 1)) =
      equalCharacteristicPowerSeriesFrobenius k
          (equalCharacteristicThetaAfterBracketCoefficient u j) -
        equalCharacteristicThetaAfterBracketCoefficient u j ^ Nat.card k := by
  have hintertwines :=
    equalCharacteristicThetaSeries_subst_sourceBracket_intertwines u
  rw [equalCharacteristicThetaSeries_subst_sourceBracket,
    equalCharacteristicQAdditiveSeries_map] at hintertwines
  exact equalCharacteristicQAdditiveIntertwiner_succ_comparison
    u (equalCharacteristicThetaAfterBracketCoefficient u)
      hintertwines j

/-- The Lubin–Tate endomorphism commutation law, first theta identity in the equal-characteristic
specialization:

`theta^phi = theta o [u]`.

Here `[u]` is the base-defined Lubin--Tate endomorphism constructed above,
not a series defined from the desired identity. -/
theorem equalCharacteristicThetaSeriesFrobenius_eq_subst_sourceBracket
    (u : k⟦X⟧ˣ) :
    equalCharacteristicThetaSeriesFrobenius u =
      PowerSeries.subst (equalCharacteristicCompletedSourceBracket u)
        (equalCharacteristicThetaSeries u) := by
  have hcoeff :
      (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicThetaCoefficient u j)) =
      equalCharacteristicThetaAfterBracketCoefficient u :=
    equalCharacteristicQAdditiveIntertwinerCoefficient_unique u
      (fun j ↦ equalCharacteristicPowerSeriesFrobenius k
        (equalCharacteristicThetaCoefficient u j))
      (equalCharacteristicThetaAfterBracketCoefficient u)
      (equalCharacteristicThetaAfterBracketCoefficient_zero u).symm
      (equalCharacteristicThetaFrobeniusCoefficient_succ_comparison u)
      (equalCharacteristicThetaAfterBracketCoefficient_succ_comparison u)
  rw [equalCharacteristicThetaSeriesFrobenius_eq_qAdditiveSeries,
    equalCharacteristicThetaSeries_subst_sourceBracket]
  exact congrArg (equalCharacteristicQAdditiveSeries k) hcoeff

end EqualCharacteristic
end LubinTate
