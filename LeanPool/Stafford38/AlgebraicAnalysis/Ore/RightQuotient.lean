/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity

/-!
# Finite right quotients over noncommutative Ore coefficients

Monic right division leaves coefficient-left remainders. A signed reverse
normal-ordering identity rewrites them in a finite right-coefficient window.
The natural scalar ring is therefore `Bᵐᵒᵖ`, not `B`; this removes the
commutativity restriction from the older finite-quotient consumer.

The final section instantiates the construction on the outer momentum layer
of the iterated Weyl tower and uses the literal generators `d` and `x^N d`.
-/

namespace AlgebraicAnalysis.OreRightQuotient

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision
open AlgebraicAnalysis.OreAssociativity

noncomputable section

variable {B : Type*} [Ring B]

instance normalOreNontrivial [Nontrivial B] (D : OreDivisionDerivation B) :
    Nontrivial (NormalOre D) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  have h' : normalForm D (0 : Polynomial B) = normalForm D 1 := by
    rw [normalForm_zero, normalForm_one]
    exact h
  exact zero_ne_one (normalForm_injective D h')

theorem normalCoefficient_injective (D : OreDivisionDerivation B) :
    Function.Injective (normalCoefficient D) := by
  intro a b h
  apply Polynomial.C_injective
  apply normalForm_injective D
  simpa only [normalForm_C] using h

instance normalOreOpSMul (D : OreDivisionDerivation B) :
    SMul Bᵐᵒᵖ (NormalOre D) :=
  ⟨fun b a => a * normalCoefficient D b.unop⟩

instance normalOreOpModule (D : OreDivisionDerivation B) :
    Module Bᵐᵒᵖ (NormalOre D) :=
  Module.ofMinimalAxioms
    (fun b x y => by
      change (x + y) * normalCoefficient D b.unop =
        x * normalCoefficient D b.unop + y * normalCoefficient D b.unop
      exact add_mul x y (normalCoefficient D b.unop))
    (fun b c x => by
      change x * normalCoefficient D (b + c).unop =
        x * normalCoefficient D b.unop + x * normalCoefficient D c.unop
      rw [MulOpposite.unop_add, (normalCoefficient D).map_add, mul_add])
    (fun b c x => by
      change x * normalCoefficient D (b * c).unop =
        (x * normalCoefficient D c.unop) * normalCoefficient D b.unop
      rw [MulOpposite.unop_mul, (normalCoefficient D).map_mul, mul_assoc])
    (fun x => by
      change x * normalCoefficient D (1 : Bᵐᵒᵖ).unop = x
      rw [MulOpposite.unop_one, (normalCoefficient D).map_one, mul_one])

@[simp] theorem normalOre_op_smul_def (D : OreDivisionDerivation B)
    (b : Bᵐᵒᵖ) (a : NormalOre D) :
    b • a = a * normalCoefficient D b.unop := rfl

@[simp] theorem normalForm_X_pow_coe (D : OreDivisionDerivation B) (n : ℕ) :
    (normalForm D (X ^ n) : AddMonoid.End (Polynomial B)) =
      (leftOreShift D) ^ n := by
  change OreAmbient.eval D (faithfulAmbient D) (X ^ n) = _
  rw [Polynomial.X_pow_eq_monomial, OreAmbient.eval_monomial]
  simp [faithfulAmbient]

theorem normalForm_monomial_reverse (D : OreDivisionDerivation B)
    (b : B) (n : ℕ) :
    normalForm D (monomial n b) =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
        n.choose ij.1 •
          ((-1 : NormalOre D) ^ ij.1 *
            ((MulOpposite.op ((D^[ij.1]) b)) •
              normalForm D (X ^ ij.2))) := by
  apply Subtype.ext
  change OreAmbient.eval D (faithfulAmbient D) (monomial n b) = _
  rw [OreAmbient.eval_monomial]
  rw [OreAmbient.reverse_mul D (faithfulAmbient D) b n]
  unfold OreAmbient.reverseExpansion OreAmbient.reverseSignedTerm
    OreAmbient.reverseTerm
  change _ = (faithfulRange D).subtype
    (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
      n.choose ij.1 •
        ((-1 : NormalOre D) ^ ij.1 *
          ((MulOpposite.op ((D^[ij.1]) b)) •
            normalForm D (X ^ ij.2))))
  have hsum :
      (faithfulRange D).subtype
          (∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
            n.choose ij.1 •
              ((-1 : NormalOre D) ^ ij.1 *
                ((MulOpposite.op ((D^[ij.1]) b)) •
                  normalForm D (X ^ ij.2)))) =
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n,
          (faithfulRange D).subtype
            (n.choose ij.1 •
              ((-1 : NormalOre D) ^ ij.1 *
                ((MulOpposite.op ((D^[ij.1]) b)) •
                  normalForm D (X ^ ij.2)))) := by
    exact map_sum (faithfulRange D).subtype.toAddMonoidHom _ _
  rw [hsum]
  apply Finset.sum_congr rfl
  intro ij hij
  change
    n.choose ij.1 •
        ((-1 : AddMonoid.End (Polynomial B)) ^ ij.1 *
          ((leftOreShift D) ^ ij.2 * coefficientLeft ((D^[ij.1]) b))) =
      n.choose ij.1 •
        ((((-1 : NormalOre D) ^ ij.1 *
          ((MulOpposite.op ((D^[ij.1]) b)) •
            normalForm D (X ^ ij.2))) : NormalOre D) :
              AddMonoid.End (Polynomial B))
  apply congrArg (fun z : AddMonoid.End (Polynomial B) => n.choose ij.1 • z)
  simp only [normalOre_op_smul_def]
  change
    (-1 : AddMonoid.End (Polynomial B)) ^ ij.1 *
        ((leftOreShift D) ^ ij.2 * coefficientLeft ((D^[ij.1]) b)) =
      (-1 : AddMonoid.End (Polynomial B)) ^ ij.1 *
        (((normalForm D (X ^ ij.2) : NormalOre D) :
            AddMonoid.End (Polynomial B)) * coefficientLeft ((D^[ij.1]) b))
  rw [normalForm_X_pow_coe]

/-- The finite right-coefficient window of order less than `n`. -/
def rightCoefficientWindow (D : OreDivisionDerivation B) (n : ℕ) :
    Submodule Bᵐᵒᵖ (NormalOre D) :=
  Submodule.span Bᵐᵒᵖ
    (Set.range fun j : Fin n => normalForm D (X ^ (j : ℕ)))

lemma normalForm_monomial_mem_rightCoefficientWindow
    (D : OreDivisionDerivation B) (b : B) {j n : ℕ} (hj : j < n) :
    normalForm D (monomial j b) ∈ rightCoefficientWindow D n := by
  rw [normalForm_monomial_reverse]
  apply Submodule.sum_mem
  intro ij hij
  rw [← Nat.cast_smul_eq_nsmul Bᵐᵒᵖ]
  apply Submodule.smul_mem
  have hijSum : ij.1 + ij.2 = j :=
    Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hijLt : ij.2 < n := by omega
  have hpow : normalForm D (X ^ ij.2) ∈ rightCoefficientWindow D n := by
    apply Submodule.subset_span
    exact ⟨⟨ij.2, hijLt⟩, rfl⟩
  have hscalar :
      (MulOpposite.op ((D^[ij.1]) b)) • normalForm D (X ^ ij.2) ∈
        rightCoefficientWindow D n :=
    Submodule.smul_mem _ _ hpow
  by_cases heven : Even ij.1
  · rw [heven.neg_one_pow]
    simpa only [one_mul] using hscalar
  · have hodd : Odd ij.1 := Nat.not_even_iff_odd.mp heven
    rw [hodd.neg_one_pow]
    simpa only [neg_one_mul] using
      (rightCoefficientWindow D n).neg_mem hscalar

theorem normalForm_mem_rightCoefficientWindow_of_degree_lt
    (D : OreDivisionDerivation B) (p : Polynomial B) (n : ℕ)
    (hp : p = 0 ∨ p.natDegree < n) :
    normalForm D p ∈ rightCoefficientWindow D n := by
  rcases hp with rfl | hp
  · simp
  · change normalFormAddHom D p ∈ rightCoefficientWindow D n
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum_def,
      map_sum (normalFormAddHom D)]
    apply Submodule.sum_mem
    intro j hj
    apply normalForm_monomial_mem_rightCoefficientWindow D
    exact lt_of_le_of_lt (Polynomial.le_natDegree_of_mem_supp j hj) hp

/-- A right ideal viewed as a coefficient-opposite submodule. -/
def rightIdealAsCoeffSubmodule (D : OreDivisionDerivation B)
    (I : Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D)) :
    Submodule Bᵐᵒᵖ (NormalOre D) where
  carrier := I
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' := by
    intro b a ha
    change a * normalCoefficient D b.unop ∈ I
    rw [← op_smul_eq_mul]
    exact I.smul_mem (MulOpposite.op (normalCoefficient D b.unop)) ha

/-- The right ideal generated by two normal forms. -/
def twoGeneratorRightIdeal (D : OreDivisionDerivation B)
    (H J : Polynomial B) :
    Submodule (NormalOre D)ᵐᵒᵖ (NormalOre D) :=
  Submodule.span (NormalOre D)ᵐᵒᵖ
    ({normalForm D H, normalForm D J} : Set (NormalOre D))

/-- The coefficient-opposite submodule underlying a two-generator ideal. -/
def twoGeneratorCoeffSubmodule (D : OreDivisionDerivation B)
    (H J : Polynomial B) : Submodule Bᵐᵒᵖ (NormalOre D) :=
  rightIdealAsCoeffSubmodule D (twoGeneratorRightIdeal D H J)

/-- The corresponding quotient as a coefficient-opposite module. -/
abbrev TwoGeneratorQuotient (D : OreDivisionDerivation B)
    (H J : Polynomial B) :=
  NormalOre D ⧸ twoGeneratorCoeffSubmodule D H J

lemma normalForm_H_mem_twoGeneratorRightIdeal
    (D : OreDivisionDerivation B) (H J : Polynomial B) :
    normalForm D H ∈ twoGeneratorRightIdeal D H J := by
  apply Submodule.subset_span
  simp

lemma normalForm_rightMul_H_mem_twoGeneratorCoeffSubmodule
    (D : OreDivisionDerivation B) (H J q : Polynomial B) :
    normalForm D (rightMul D H q) ∈
      twoGeneratorCoeffSubmodule D H J := by
  change normalForm D (rightMul D H q) ∈ twoGeneratorRightIdeal D H J
  rw [normalForm_mul, ← op_smul_eq_mul]
  exact (twoGeneratorRightIdeal D H J).smul_mem
    (MulOpposite.op (normalForm D q))
    (normalForm_H_mem_twoGeneratorRightIdeal D H J)

theorem rightCoefficientWindow_quotient_surjective
    [Nontrivial B] (D : OreDivisionDerivation B)
    (H J : Polynomial B) (hH : H.Monic) :
    Function.Surjective
      ((twoGeneratorCoeffSubmodule D H J).mkQ.comp
        (rightCoefficientWindow D H.natDegree).subtype) := by
  intro y
  obtain ⟨a, rfl⟩ :=
    (twoGeneratorCoeffSubmodule D H J).mkQ_surjective y
  obtain ⟨p, rfl⟩ := normalForm_surjective D a
  obtain ⟨q, r, hdecomp, hr⟩ := right_division_exists D H p hH
  have hrWindow : normalForm D r ∈
      rightCoefficientWindow D H.natDegree :=
    normalForm_mem_rightCoefficientWindow_of_degree_lt D r H.natDegree hr
  refine ⟨⟨normalForm D r, hrWindow⟩, ?_⟩
  change (twoGeneratorCoeffSubmodule D H J).mkQ (normalForm D r) =
    (twoGeneratorCoeffSubmodule D H J).mkQ (normalForm D p)
  apply (Submodule.Quotient.eq (twoGeneratorCoeffSubmodule D H J)).2
  have hmultiple : normalForm D (rightMul D H q) ∈
      twoGeneratorCoeffSubmodule D H J :=
    normalForm_rightMul_H_mem_twoGeneratorCoeffSubmodule D H J q
  rw [hdecomp, normalForm_add]
  simpa using (twoGeneratorCoeffSubmodule D H J).neg_mem hmultiple

theorem twoGeneratorQuotient_finite
    [Nontrivial B] (D : OreDivisionDerivation B)
    (H J : Polynomial B) (hH : H.Monic) :
    Module.Finite Bᵐᵒᵖ (TwoGeneratorQuotient D H J) := by
  let : Module.Finite Bᵐᵒᵖ (rightCoefficientWindow D H.natDegree) :=
    Module.Finite.span_of_finite Bᵐᵒᵖ (Set.finite_range
      (fun j : Fin H.natDegree => normalForm D (X ^ (j : ℕ))))
  exact Module.Finite.of_surjective
    ((twoGeneratorCoeffSubmodule D H J).mkQ.comp
      (rightCoefficientWindow D H.natDegree).subtype)
    (rightCoefficientWindow_quotient_surjective D H J hH)



end
end AlgebraicAnalysis.OreRightQuotient
