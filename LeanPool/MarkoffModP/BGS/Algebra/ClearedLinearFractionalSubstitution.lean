/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Algebra.RatFuncLinearFractionalEquiv

/-!
# Cleared linear-fractional substitution

For a polynomial `f` of degree `n`, this file studies the polynomial obtained from
`f ((a * X + b) / (c * X + d))` by multiplying by `(c * X + d) ^ n`.

The degree assumption in the irreducibility theorem is essential: inversion sends the
linear polynomial `X` to the unit polynomial `1` after clearing its denominator.
-/

namespace BGS

open Polynomial
open IntermediateField

noncomputable section

variable {K : Type*} [Field K]

/-- The denominator-cleared substitution
`(cX+d)^deg(f) f((aX+b)/(cX+d))`, written without division. -/
def clearedLinearFractionalSubstitution (f : K[X]) (a b c d : K) : K[X] :=
  f.support.sum fun i ↦ C (f.coeff i) * (C a * X + C b) ^ i *
    (C c * X + C d) ^ (f.natDegree - i)

private theorem linearPolynomial_natDegree_le_one (u v : K) :
    (C u * X + C v).natDegree ≤ 1 := by
  calc
    (C u * X + C v).natDegree ≤ max (C u * X).natDegree (C v).natDegree :=
      natDegree_add_le _ _
    _ ≤ 1 := max_le (natDegree_mul_le.trans (by simp)) (by simp)

private theorem clearedLinearFractionalSummand_natDegree_le
    (f : K[X]) (a b c d : K) {i : ℕ} (hi : i ≤ f.natDegree) :
    (C (f.coeff i) * (C a * X + C b) ^ i *
      (C c * X + C d) ^ (f.natDegree - i)).natDegree ≤ f.natDegree := by
  have outerProductDegree :
      (C (f.coeff i) * (C a * X + C b) ^ i *
        (C c * X + C d) ^ (f.natDegree - i)).natDegree ≤
        (C (f.coeff i) * (C a * X + C b) ^ i).natDegree +
          ((C c * X + C d) ^ (f.natDegree - i)).natDegree :=
    natDegree_mul_le
  have innerProductDegree :
      (C (f.coeff i) * (C a * X + C b) ^ i).natDegree ≤
        (C (f.coeff i)).natDegree + ((C a * X + C b) ^ i).natDegree :=
    natDegree_mul_le
  calc
    _ ≤ ((C (f.coeff i)).natDegree + ((C a * X + C b) ^ i).natDegree) +
          ((C c * X + C d) ^ (f.natDegree - i)).natDegree :=
      outerProductDegree.trans (add_le_add innerProductDegree (le_refl _))
    _ ≤ (0 + i) + (f.natDegree - i) := by
      apply add_le_add
      · apply add_le_add
        · simp
        · exact natDegree_pow_le.trans <|
            (Nat.mul_le_mul_left i (linearPolynomial_natDegree_le_one a b)).trans (by simp)
      · exact natDegree_pow_le.trans <|
          (Nat.mul_le_mul_left (f.natDegree - i)
            (linearPolynomial_natDegree_le_one c d)).trans (by simp)
    _ = f.natDegree := by omega

theorem natDegree_clearedLinearFractionalSubstitution_le
    (f : K[X]) (a b c d : K) :
    (clearedLinearFractionalSubstitution f a b c d).natDegree ≤ f.natDegree := by
  exact natDegree_sum_le_of_forall_le f.support _ fun i hi ↦
    clearedLinearFractionalSummand_natDegree_le f a b c d
      (le_natDegree_of_ne_zero (mem_support_iff.mp hi))

theorem aeval_clearedLinearFractionalSubstitution
    {L : Type*} [Field L] [Algebra K L] (f : K[X]) (a b c d : K) (x y : L)
    (hrelation :
      algebraMap K L a * x + algebraMap K L b =
        y * (algebraMap K L c * x + algebraMap K L d)) :
    aeval x (clearedLinearFractionalSubstitution f a b c d) =
      (algebraMap K L c * x + algebraMap K L d) ^ f.natDegree * aeval y f := by
  rw [clearedLinearFractionalSubstitution, map_sum]
  simp only [map_mul, map_pow, aeval_def, eval₂_add, eval₂_mul, eval₂_C, eval₂_X]
  calc
    ∑ i ∈ f.support,
        algebraMap K L (f.coeff i) *
            (algebraMap K L a * x + algebraMap K L b) ^ i *
            (algebraMap K L c * x + algebraMap K L d) ^ (f.natDegree - i) =
        (algebraMap K L c * x + algebraMap K L d) ^ f.natDegree *
          ∑ i ∈ f.support, algebraMap K L (f.coeff i) * y ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hiDegree : i ≤ f.natDegree :=
        le_natDegree_of_ne_zero (mem_support_iff.mp hi)
      rw [hrelation, mul_pow]
      have hpow :
          (algebraMap K L c * x + algebraMap K L d) ^ i *
              (algebraMap K L c * x + algebraMap K L d) ^ (f.natDegree - i) =
            (algebraMap K L c * x + algebraMap K L d) ^ f.natDegree := by
        rw [← pow_add, Nat.add_sub_of_le hiDegree]
      rw [← hpow]
      ring
    _ = (algebraMap K L c * x + algebraMap K L d) ^ f.natDegree * aeval y f := by
      rw [aeval_def, eval₂_eq_sum, sum_def]

/-- An invertible linear-fractional change of variable preserves irreducibility after
clearing denominators at the degree of the polynomial.  Degree at least two is necessary:
for the inversion matrix, the cleared transform of `X` is `1`. -/
theorem irreducible_clearedLinearFractionalSubstitution
    {f : K[X]} (hf : Irreducible f) (hfDegree : 2 ≤ f.natDegree)
    {a b c d : K} (hdet : a * d - b * c ≠ 0) :
    Irreducible (clearedLinearFractionalSubstitution f a b c d) := by
  let : Fact (Irreducible f) := ⟨hf⟩
  let E := AdjoinRoot f
  let : FiniteDimensional K E := by
    change FiniteDimensional K (AdjoinRoot f)
    exact (AdjoinRoot.powerBasis hf.ne_zero).finite
  let α : E := AdjoinRoot.root f
  have hfDegreeNeOne : f.natDegree ≠ 1 := by omega
  have hroot : aeval α f = 0 := by
    change eval₂ (algebraMap K E) (AdjoinRoot.root f) f = 0
    exact AdjoinRoot.eval₂_root f
  have hinverseDenominator :
      algebraMap K E a - algebraMap K E c * α ≠ 0 := by
    by_cases hc : c = 0
    · have ha : a ≠ 0 := by
        intro ha
        apply hdet
        simp [ha, hc]
      simp [hc, ha]
    · intro hzero
      have hcMap : algebraMap K E c ≠ 0 := by
        simpa using (algebraMap K E).injective.ne hc
      have hα : α = algebraMap K E (a / c) := by
        rw [map_div₀ (algebraMap K E) a c]
        apply (eq_div_iff hcMap).2
        have := sub_eq_zero.mp hzero
        rw [mul_comm]
        exact this.symm
      exact hf.aeval_ne_zero_of_natDegree_ne_one hfDegreeNeOne
        ⟨a / c, hα.symm⟩ hroot
  let β : E :=
    (algebraMap K E d * α - algebraMap K E b) /
      (algebraMap K E a - algebraMap K E c * α)
  have hforwardDenominatorFormula :
      algebraMap K E c * β + algebraMap K E d =
        algebraMap K E (a * d - b * c) /
          (algebraMap K E a - algebraMap K E c * α) := by
    dsimp [β]
    apply (eq_div_iff hinverseDenominator).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hinverseDenominator]
    simp only [map_sub, map_mul]
    ring
  have hforwardDenominator :
      algebraMap K E c * β + algebraMap K E d ≠ 0 := by
    rw [hforwardDenominatorFormula]
    exact div_ne_zero (by simpa using (algebraMap K E).injective.ne hdet)
      hinverseDenominator
  have hforwardNumeratorFormula :
      algebraMap K E a * β + algebraMap K E b =
        α * algebraMap K E (a * d - b * c) /
          (algebraMap K E a - algebraMap K E c * α) := by
    dsimp [β]
    apply (eq_div_iff hinverseDenominator).2
    rw [add_mul, mul_assoc, div_mul_cancel₀ _ hinverseDenominator]
    simp only [map_sub, map_mul]
    ring
  have hlinearFractionalRelation :
      algebraMap K E a * β + algebraMap K E b =
        α * (algebraMap K E c * β + algebraMap K E d) := by
    rw [hforwardNumeratorFormula, hforwardDenominatorFormula]
    ring
  have hαFormula :
      α = (algebraMap K E a * β + algebraMap K E b) /
        (algebraMap K E c * β + algebraMap K E d) := by
    apply (eq_div_iff hforwardDenominator).2
    exact hlinearFractionalRelation.symm
  have hβGenerates : K⟮β⟯ = (⊤ : IntermediateField K E) := by
    apply top_unique
    rw [← IntermediateField.adjoin_root_eq_top f]
    apply IntermediateField.adjoin_simple_le_iff.mpr
    change α ∈ K⟮β⟯
    rw [hαFormula]
    exact div_mem
      (add_mem (mul_mem (IntermediateField.algebraMap_mem _ a)
        (IntermediateField.mem_adjoin_simple_self K β))
        (IntermediateField.algebraMap_mem _ b))
      (add_mem (mul_mem (IntermediateField.algebraMap_mem _ c)
        (IntermediateField.mem_adjoin_simple_self K β))
        (IntermediateField.algebraMap_mem _ d))
  have hminpolyDegree : (minpoly K β).natDegree = f.natDegree := by
    have hprimitive := (Field.primitive_element_iff_minpoly_natDegree_eq K β).mp hβGenerates
    exact hprimitive.trans (AdjoinRoot.powerBasis hf.ne_zero).finrank
  have htransformedRoot :
      aeval β (clearedLinearFractionalSubstitution f a b c d) = 0 := by
    rw [aeval_clearedLinearFractionalSubstitution f a b c d β α
      hlinearFractionalRelation, hroot, mul_zero]
  have hminpolyDvd : minpoly K β ∣ clearedLinearFractionalSubstitution f a b c d :=
    minpoly.dvd K β htransformedRoot
  have htransformedNonzero : clearedLinearFractionalSubstitution f a b c d ≠ 0 := by
    intro hzero
    let q := Algebra.ratFuncLinearFractionalValue a b c d
    have hden := Algebra.ratFuncLinearFractional_denominator_ne_zero hdet
    have hrelation :
        RatFunc.C a * RatFunc.X + RatFunc.C b =
          q * (RatFunc.C c * RatFunc.X + RatFunc.C d) := by
      dsimp [q, Algebra.ratFuncLinearFractionalValue]
      exact (div_mul_cancel₀ _ hden).symm
    have heval := aeval_clearedLinearFractionalSubstitution f a b c d RatFunc.X q hrelation
    rw [hzero, map_zero] at heval
    have hqTranscendental : Transcendental K q :=
      Algebra.ratFuncLinearFractionalValue_transcendental hdet
    have hfAtQ : aeval q f ≠ 0 := by
      intro hqRoot
      exact hf.ne_zero ((transcendental_iff.mp hqTranscendental) f hqRoot)
    exact (mul_ne_zero (pow_ne_zero _ hden) hfAtQ) heval.symm
  have hassociated :
      Associated (minpoly K β) (clearedLinearFractionalSubstitution f a b c d) := by
    apply associated_of_dvd_of_natDegree_le hminpolyDvd htransformedNonzero
    · rw [hminpolyDegree]
      exact natDegree_clearedLinearFractionalSubstitution_le f a b c d
  exact hassociated.irreducible_iff.mp (minpoly.irreducible (Algebra.IsIntegral.isIntegral β))

end

end BGS
