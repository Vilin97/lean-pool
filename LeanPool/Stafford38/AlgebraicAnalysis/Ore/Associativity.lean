/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightDivision

/-!
# Associativity of derivation Ore normal forms over a noncommutative ring

This removes the commutativity assumption from the faithful-operator proof of
associativity for `Stafford.OreDivision.rightMul`.
-/

namespace AlgebraicAnalysis.OreAssociativity

open Polynomial
open AlgebraicAnalysis
open AlgebraicAnalysis.OreDivision

noncomputable section

variable {B : Type*} [Ring B]

lemma derivation_one (D : OreDivisionDerivation B) : D 1 = 0 := by
  have h := D.leibniz 1 1
  simp only [one_mul, mul_one] at h
  symm
  calc
    0 = D 1 - D 1 := (sub_self _).symm
    _ = (D 1 + D 1) - D 1 := by rw [← h]
    _ = D 1 := by abel

/-- Apply the coefficient derivation to every coefficient. -/
def coefficientDerivation (D : OreDivisionDerivation B) :
    Polynomial B →+ Polynomial B where
  toFun p := p.sum fun i b => monomial i (D b)
  map_zero' := by simp [Polynomial.sum_def]
  map_add' p q := by
    change (p + q).sum (fun i b => monomial i (D b)) =
      p.sum (fun i b => monomial i (D b)) +
        q.sum (fun i b => monomial i (D b))
    apply Polynomial.sum_add_index
    · intro i
      simp [D.map_zero]
    · intro i a b
      simp [D.map_add]

@[simp]
lemma coefficientDerivation_monomial
    (D : OreDivisionDerivation B) (i : ℕ) (b : B) :
    coefficientDerivation D (monomial i b) = monomial i (D b) := by
  by_cases hb : b = 0
  · subst b
    simp [D.map_zero]
  · simp [coefficientDerivation,  D.map_zero]

@[simp]
lemma coefficientDerivation_C_mul
    (D : OreDivisionDerivation B) (b : B) (p : Polynomial B) :
    coefficientDerivation D (C b * p) =
      C b * coefficientDerivation D p + C (D b) * p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp [map_add, hp, hq, mul_add,  add_assoc, add_left_comm,
        add_comm]
  | monomial n a =>
      simp [D.leibniz]

/-- Coefficients act by ordinary left multiplication. -/
def coefficientLeft : B →+* AddMonoid.End (Polynomial B) where
  toFun b :=
    { toFun := fun p => C b * p
      map_zero' := by simp
      map_add' := by intro p q; simp [mul_add] }
  map_one' := by
    apply AddMonoidHom.ext
    intro p
    change C (1 : B) * p = p
    simp
  map_mul' b c := by
    apply AddMonoidHom.ext
    intro p
    change C (b * c) * p = C b * (C c * p)
    simp [mul_assoc]
  map_zero' := by
    apply AddMonoidHom.ext
    intro p
    change C (0 : B) * p = 0
    simp
  map_add' b c := by
    apply AddMonoidHom.ext
    intro p
    change C (b + c) * p = C b * p + C c * p
    simp [add_mul]

/-- Left multiplication by the Ore variable on normal forms. -/
def leftOreShift (D : OreDivisionDerivation B) :
    AddMonoid.End (Polynomial B) where
  toFun p := p * X + coefficientDerivation D p
  map_zero' := by simp
  map_add' p q := by
    simp only [add_mul, map_add]
    abel

/-- The faithful left-regular representation of the one-variable Ore model. -/
def faithfulAmbient (D : OreDivisionDerivation B) :
    OreAmbient B (AddMonoid.End (Polynomial B)) D where
  embed := coefficientLeft
  x := leftOreShift D
  relation := by
    intro b
    apply AddMonoidHom.ext
    intro p
    change (C b * p) * X + coefficientDerivation D (C b * p) =
      C b * (p * X + coefficientDerivation D p) + C (D b) * p
    rw [coefficientDerivation_C_mul]
    noncomm_ring

@[simp]
lemma coefficientDerivation_X_pow
    (D : OreDivisionDerivation B) (n : ℕ) :
    coefficientDerivation D (X ^ n) = 0 := by
  rw [Polynomial.X_pow_eq_monomial, coefficientDerivation_monomial,
    derivation_one, monomial_zero_right]

@[simp]
lemma leftOreShift_X_pow (D : OreDivisionDerivation B) (n : ℕ) :
    leftOreShift D (X ^ n) = X ^ (n + 1) := by
  change X ^ n * X + coefficientDerivation D (X ^ n) = X ^ (n + 1)
  rw [coefficientDerivation_X_pow, add_zero, pow_succ]

lemma leftOreShift_pow_apply_one (D : OreDivisionDerivation B) (n : ℕ) :
    ((leftOreShift D) ^ n) (1 : Polynomial B) = X ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ']
      change leftOreShift D (((leftOreShift D) ^ n) 1) = X ^ (n + 1)
      rw [ih]
      exact leftOreShift_X_pow D n

lemma faithful_eval_apply_one (D : OreDivisionDerivation B)
    (p : Polynomial B) :
    OreAmbient.eval D (faithfulAmbient D) p (1 : Polynomial B) = p := by
  rw [OreAmbient.eval]
  change (p.sum fun i b =>
    coefficientLeft b * (leftOreShift D) ^ i) 1 = p
  rw [Polynomial.sum_def]
  calc
    (∑ n ∈ p.support,
        coefficientLeft (p.coeff n) * (leftOreShift D) ^ n) 1 =
        (∑ n ∈ p.support,
          ⇑(coefficientLeft (p.coeff n) * (leftOreShift D) ^ n)) 1 := by
      exact congrFun
        (AddMonoidHom.coe_finsetSum
          (fun n => coefficientLeft (p.coeff n) * (leftOreShift D) ^ n)
          p.support) (1 : Polynomial B)
    _ = ∑ n ∈ p.support,
        (coefficientLeft (p.coeff n) * (leftOreShift D) ^ n) 1 := by
      exact Finset.sum_apply (1 : Polynomial B) p.support
        (fun n => ⇑(coefficientLeft (p.coeff n) * (leftOreShift D) ^ n))
    _ = ∑ n ∈ p.support,
        C (p.coeff n) * (((leftOreShift D) ^ n) 1) := by rfl
    _ = p := by
      simp_rw [leftOreShift_pow_apply_one]
      simpa only [Polynomial.sum_def] using Polynomial.sum_C_mul_X_pow_eq p

theorem faithful_eval_injective (D : OreDivisionDerivation B) :
    Function.Injective (OreAmbient.eval D (faithfulAmbient D)) := by
  intro p q hpq
  have h := DFunLike.congr_fun hpq (1 : Polynomial B)
  simpa [faithful_eval_apply_one] using h

lemma faithful_eval_one (D : OreDivisionDerivation B) :
    OreAmbient.eval D (faithfulAmbient D) (1 : Polynomial B) = 1 := by
  rw [show (1 : Polynomial B) = C (1 : B) by simp, OreAmbient.eval]
  rw [Polynomial.sum_C_index]
  · simp [faithfulAmbient]
  · simp [faithfulAmbient]

lemma faithful_eval_C (D : OreDivisionDerivation B) (b : B) :
    OreAmbient.eval D (faithfulAmbient D) (C b) = coefficientLeft b := by
  rw [OreAmbient.eval, Polynomial.sum_C_index]
  · simp [faithfulAmbient]
  · simp [faithfulAmbient]

lemma faithful_eval_X (D : OreDivisionDerivation B) :
    OreAmbient.eval D (faithfulAmbient D) X = leftOreShift D := by
  rw [← Polynomial.monomial_one_one_eq_X]
  rw [OreAmbient.eval_monomial]
  simp [faithfulAmbient]

/-- Associativity of the derivation-corrected normal-form product. -/
theorem rightMul_assoc_of_ring
    (D : OreDivisionDerivation B) (p q r : Polynomial B) :
    rightMul D (rightMul D p q) r =
      rightMul D p (rightMul D q r) := by
  apply faithful_eval_injective D
  rw [OreAmbient.eval_rightMul, OreAmbient.eval_rightMul,
    OreAmbient.eval_rightMul, OreAmbient.eval_rightMul]
  exact mul_assoc _ _ _

/-! ## The concrete associative Ore ring -/

/-- The image of the faithful normal-form representation. -/
def faithfulRange (D : OreDivisionDerivation B) :
    Subring (AddMonoid.End (Polynomial B)) where
  carrier := Set.range (OreAmbient.eval D (faithfulAmbient D))
  zero_mem' := ⟨0, OreAmbient.eval_zero D (faithfulAmbient D)⟩
  one_mem' := ⟨1, faithful_eval_one D⟩
  add_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, OreAmbient.eval_add D (faithfulAmbient D) p q⟩
  neg_mem' := by
    rintro _ ⟨p, rfl⟩
    exact ⟨-p, map_neg (OreAmbient.evalAddHom D (faithfulAmbient D)) p⟩
  mul_mem' := by
    rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨rightMul D p q, OreAmbient.eval_rightMul D (faithfulAmbient D) p q⟩

/-- The one-variable derivation Ore extension, represented faithfully by its
left-regular action on normal polynomials. -/
abbrev NormalOre (D : OreDivisionDerivation B) := faithfulRange D

/-- A coefficient-left polynomial regarded as an element of the Ore ring. -/
def normalForm (D : OreDivisionDerivation B) (p : Polynomial B) : NormalOre D :=
  ⟨OreAmbient.eval D (faithfulAmbient D) p, ⟨p, rfl⟩⟩

@[simp]
theorem normalForm_injective (D : OreDivisionDerivation B) :
    Function.Injective (normalForm D) := by
  intro p q h
  apply faithful_eval_injective D
  exact Subtype.ext_iff.mp h

theorem normalForm_surjective (D : OreDivisionDerivation B) :
    Function.Surjective (normalForm D) := by
  rintro ⟨_, p, rfl⟩
  exact ⟨p, rfl⟩

@[simp]
theorem normalForm_zero (D : OreDivisionDerivation B) :
    normalForm D 0 = 0 := by
  apply Subtype.ext
  exact OreAmbient.eval_zero D (faithfulAmbient D)

@[simp]
theorem normalForm_one (D : OreDivisionDerivation B) :
    normalForm D 1 = 1 := by
  apply Subtype.ext
  exact faithful_eval_one D

@[simp]
theorem normalForm_add (D : OreDivisionDerivation B)
    (p q : Polynomial B) :
    normalForm D (p + q) = normalForm D p + normalForm D q := by
  apply Subtype.ext
  exact OreAmbient.eval_add D (faithfulAmbient D) p q

@[simp]
theorem normalForm_neg (D : OreDivisionDerivation B)
    (p : Polynomial B) : normalForm D (-p) = -normalForm D p := by
  apply Subtype.ext
  exact map_neg (OreAmbient.evalAddHom D (faithfulAmbient D)) p

@[simp]
theorem normalForm_mul (D : OreDivisionDerivation B)
    (p q : Polynomial B) :
    normalForm D (rightMul D p q) = normalForm D p * normalForm D q := by
  apply Subtype.ext
  exact OreAmbient.eval_rightMul D (faithfulAmbient D) p q

/-- The normal-form map as an additive homomorphism. -/
def normalFormAddHom (D : OreDivisionDerivation B) :
    Polynomial B →+ NormalOre D where
  toFun := normalForm D
  map_zero' := normalForm_zero D
  map_add' := normalForm_add D

/-- Normal forms are additively equivalent to ordinary coefficient-left
polynomials. -/
def normalFormAddEquiv (D : OreDivisionDerivation B) :
    Polynomial B ≃+ NormalOre D :=
  AddEquiv.ofBijective (normalFormAddHom D)
    ⟨normalForm_injective D, normalForm_surjective D⟩

/-- The canonical coefficient embedding. -/
def normalCoefficient (D : OreDivisionDerivation B) : B →+* NormalOre D :=
  coefficientLeft.codRestrict (faithfulRange D) fun b => by
    exact ⟨C b, faithful_eval_C D b⟩

@[simp]
theorem normalForm_C (D : OreDivisionDerivation B) (b : B) :
    normalForm D (C b) = normalCoefficient D b := by
  apply Subtype.ext
  exact faithful_eval_C D b

/-- The canonical Ore variable. -/
def normalVariable (D : OreDivisionDerivation B) : NormalOre D :=
  normalForm D X

theorem normalForm_monomial (D : OreDivisionDerivation B) (n : ℕ) (b : B) :
    normalForm D (monomial n b) =
      normalCoefficient D b * normalVariable D ^ n := by
  apply Subtype.ext
  change OreAmbient.eval D (faithfulAmbient D) (monomial n b) =
    coefficientLeft b * OreAmbient.eval D (faithfulAmbient D) X ^ n
  rw [OreAmbient.eval_monomial, faithful_eval_X]
  rfl

/-- The defining derivation relation `X b = b X + D(b)`. -/
theorem normalVariable_mul_coefficient (D : OreDivisionDerivation B) (b : B) :
    normalVariable D * normalCoefficient D b =
      normalCoefficient D b * normalVariable D + normalCoefficient D (D b) := by
  apply Subtype.ext
  change
    OreAmbient.eval D (faithfulAmbient D) X * coefficientLeft b =
      coefficientLeft b * OreAmbient.eval D (faithfulAmbient D) X +
        coefficientLeft (D b)
  rw [faithful_eval_X]
  exact (faithfulAmbient D).relation b

/-! ## Universal property -/

variable {A : Type*} [Ring A]

lemma ambient_eval_one (D : OreDivisionDerivation B) (O : OreAmbient B A D) :
    OreAmbient.eval D O (1 : Polynomial B) = 1 := by
  rw [show (1 : Polynomial B) = C (1 : B) by simp, OreAmbient.eval]
  rw [Polynomial.sum_C_index]
  · simp
  · simp

lemma ambient_eval_C (D : OreDivisionDerivation B) (O : OreAmbient B A D)
    (b : B) : OreAmbient.eval D O (C b) = O.embed b := by
  rw [OreAmbient.eval, Polynomial.sum_C_index]
  · simp
  · simp

lemma ambient_eval_X (D : OreDivisionDerivation B) (O : OreAmbient B A D) :
    OreAmbient.eval D O X = O.x := by
  rw [← Polynomial.monomial_one_one_eq_X, OreAmbient.eval_monomial]
  simp

/-- The universal map out of the concrete Ore ring. -/
def oreLift (D : OreDivisionDerivation B) (O : OreAmbient B A D) :
    NormalOre D →+* A where
  toFun z := OreAmbient.eval D O ((normalFormAddEquiv D).symm z)
  map_zero' := by
    change OreAmbient.eval D O ((normalFormAddEquiv D).symm 0) = 0
    rw [(normalFormAddEquiv D).symm.map_zero]
    exact OreAmbient.eval_zero D O
  map_one' := by
    have h : (normalFormAddEquiv D).symm (1 : NormalOre D) = 1 := by
      apply (normalFormAddEquiv D).injective
      simp [normalFormAddEquiv, normalFormAddHom]
    change OreAmbient.eval D O ((normalFormAddEquiv D).symm 1) = 1
    rw [h]
    exact ambient_eval_one D O
  map_add' z w := by
    change OreAmbient.eval D O ((normalFormAddEquiv D).symm (z + w)) =
      OreAmbient.eval D O ((normalFormAddEquiv D).symm z) +
        OreAmbient.eval D O ((normalFormAddEquiv D).symm w)
    have h := (normalFormAddEquiv D).symm.toAddHom.map_add z w
    change (normalFormAddEquiv D).symm (z + w) =
      (normalFormAddEquiv D).symm z + (normalFormAddEquiv D).symm w at h
    rw [h]
    exact OreAmbient.eval_add D O _ _
  map_mul' z w := by
    let p := (normalFormAddEquiv D).symm z
    let q := (normalFormAddEquiv D).symm w
    have hz : normalForm D p = z := by
      change (normalFormAddEquiv D) p = z
      exact (normalFormAddEquiv D).apply_symm_apply z
    have hw : normalForm D q = w := by
      change (normalFormAddEquiv D) q = w
      exact (normalFormAddEquiv D).apply_symm_apply w
    have hpq : (normalFormAddEquiv D).symm (z * w) = rightMul D p q := by
      apply (normalFormAddEquiv D).injective
      rw [(normalFormAddEquiv D).apply_symm_apply]
      symm
      change normalForm D (rightMul D p q) = z * w
      rw [normalForm_mul, hz, hw]
    change OreAmbient.eval D O ((normalFormAddEquiv D).symm (z * w)) =
      OreAmbient.eval D O p * OreAmbient.eval D O q
    rw [hpq]
    exact OreAmbient.eval_rightMul D O p q

@[simp]
theorem oreLift_normalForm (D : OreDivisionDerivation B)
    (O : OreAmbient B A D) (p : Polynomial B) :
    oreLift D O (normalForm D p) = OreAmbient.eval D O p := by
  change OreAmbient.eval D O ((normalFormAddEquiv D).symm (normalForm D p)) = _
  rw [show normalForm D p = (normalFormAddEquiv D) p by rfl]
  rw [(normalFormAddEquiv D).symm_apply_apply]

@[simp]
theorem oreLift_coefficient (D : OreDivisionDerivation B)
    (O : OreAmbient B A D) (b : B) :
    oreLift D O (normalCoefficient D b) = O.embed b := by
  rw [← normalForm_C, oreLift_normalForm, ambient_eval_C]

@[simp]
theorem oreLift_variable (D : OreDivisionDerivation B)
    (O : OreAmbient B A D) : oreLift D O (normalVariable D) = O.x := by
  rw [normalVariable, oreLift_normalForm, ambient_eval_X]

/-- A ring map out of `NormalOre D` is uniquely determined by the coefficient
map and the image of the Ore variable. -/
theorem oreLift_unique (D : OreDivisionDerivation B) (O : OreAmbient B A D)
    (g : NormalOre D →+* A)
    (hCoefficient : ∀ b, g (normalCoefficient D b) = O.embed b)
    (hVariable : g (normalVariable D) = O.x) :
    g = oreLift D O := by
  ext z
  rcases normalForm_surjective D z with ⟨p, rfl⟩
  rw [oreLift_normalForm]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [normalForm_add, g.map_add, OreAmbient.eval_add, hp, hq]
  | monomial n b =>
      rw [normalForm_monomial, g.map_mul, g.map_pow, hCoefficient, hVariable,
        OreAmbient.eval_monomial]


end
end AlgebraicAnalysis.OreAssociativity
