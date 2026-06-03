/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.HeckeRIngs.AbstractHeckeRing.Associativity

/-!
# Hecke Rings: Ring Instance and API

The `Ring (𝕋 P ℤ)` instance and user-facing API lemmas for working with Hecke rings.
-/

open MulOpposite Set DoubleCoset Subgroup Subgroup.Commensurable

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- Associativity of multiplication in the Hecke ring, deduced from `IsScalarTower`
and faithfulness of the module action. -/
lemma mul_assoc_𝕋 (f g h : 𝕋 P ℤ) : (f * g) * h = f * (g * h) := by
  apply (instFaithfulSMulHeckeModule P).eq_of_smul_eq_smul (M := 𝕋 P ℤ); intro a
  have e1 := (instIsScalarTower P).smul_assoc g f a
  have e2 := (instIsScalarTower P).smul_assoc h g (f • a)
  have e3 := (instIsScalarTower P).smul_assoc (g * h) f a
  have e4 := (instIsScalarTower P).smul_assoc h (f * g) a
  simp only [smul_def] at e1 e2 e3 e4; rw [e1, ← e2] at e4; rwa [← e3] at e4

/-- The Hecke ring is a non-unital semiring (associativity + distributivity). -/
noncomputable instance instNonUnitalSemiring : NonUnitalSemiring (𝕋 P ℤ) :=
  { instNonUnitalNonAssocSemiring P with mul_assoc := mul_assoc_𝕋 P }

/-- The multiplicative identity of the Hecke ring is `TSingle (HeckeCoset.one P) 1`. -/
noncomputable instance instOne𝕋 : One (𝕋 P Z) :=
  ⟨TSingle P Z (HeckeCoset.one P) 1⟩

/-- The one element of the Hecke ring unfolds to `TSingle (HeckeCoset.one P) 1`. -/
theorem one_def : (1 : 𝕋 P Z) = TSingle P Z (HeckeCoset.one P) 1 := rfl

/-- The Hecke ring is a non-associative semiring (one is a two-sided identity). -/
noncomputable instance instNonAssocSemiring : NonAssocSemiring (𝕋 P ℤ) :=
  { instNonUnitalNonAssocSemiring P with
    natCast := fun n => TSingle P ℤ (HeckeCoset.one P) n
    natCast_zero := by simp only [Nat.cast_zero, single_zero]
    natCast_succ := fun _ => by
      simp only [Nat.cast_add, Nat.cast_one, single_add, add_right_inj]; rfl
    one_mul := fun f => by
      simp only [one_def, mul_def]; rw [TSingle]; simp only [zero_smul, sum_fun_zero,
        sum_single_index, one_smul]
      have := Finsupp.sum_single f; nth_rw 2 [← this]; congr; ext D z v
      have := one_mul_singleton_𝕋 P D z; simp_rw [TSingle] at *
      rw [← this, mul_singleton_𝕋]; simp only [one_smul]
    mul_one := fun f => by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]
      have := Finsupp.sum_single f; nth_rw 2 [← this]; congr; ext D z v
      have := singleton_one_mul_𝕋 P D z; simp_rw [TSingle] at this
      rw [← this, mul_singleton_𝕋]; simp only [one_smul] }

/-- The Hecke ring is a semiring. -/
noncomputable instance instSemiring : Semiring (𝕋 P ℤ) :=
  { HeckeRing.instNonUnitalSemiring P,
    HeckeRing.instNonAssocSemiring P with }

/-- The Hecke ring is a non-associative ring (semiring + additive inverses). -/
noncomputable instance instNonAssocRing : NonAssocRing (𝕋 P ℤ) :=
  { HeckeRing.instAddCommGroup𝕋 P ℤ,
    HeckeRing.instNonAssocSemiring P with
    intCast := fun n => TSingle P ℤ (HeckeCoset.one P) n
    intCast_ofNat := fun _ => rfl
    intCast_negSucc := fun _ => by
      simp only [TSingle, Int.negSucc_eq, Finsupp.single_neg]; congr 1 }

/-- The Hecke ring `𝕋 P ℤ` is a ring. -/
noncomputable instance instRing : Ring (𝕋 P ℤ) :=
  { HeckeRing.instNonAssocRing P, HeckeRing.instSemiring P with }

/-! ## Algebra compatibility lemmas

In mathlib v4.29, `Finsupp` gains pointwise multiplication instances that conflict with
the Hecke ring's custom convolution multiplication. The lemmas below use the Hecke `Ring`
instance explicitly so that `rw` can match the custom `Mul`. -/

protected lemma mul_sub (a b c : 𝕋 P ℤ) : a * (b - c) = a * b - a * c :=
  @_root_.mul_sub _ (instRing (P := P)).toNonAssocRing.toNonUnitalNonAssocRing a b c

protected lemma sub_mul (a b c : 𝕋 P ℤ) : (a - b) * c = a * c - b * c :=
  @_root_.sub_mul _ (instRing (P := P)).toNonAssocRing.toNonUnitalNonAssocRing a b c

protected lemma mul_assoc (a b c : 𝕋 P ℤ) : a * b * c = a * (b * c) :=
  @_root_.mul_assoc _ (instSemiring (P := P)).toMonoid.toSemigroup a b c

protected lemma mul_add (a b c : 𝕋 P ℤ) : a * (b + c) = a * b + a * c :=
  (instNonUnitalNonAssocSemiring P).left_distrib a b c

protected lemma add_mul (a b c : 𝕋 P ℤ) : (a + b) * c = a * c + b * c :=
  (instNonUnitalNonAssocSemiring P).right_distrib a b c

protected lemma pow_succ (a : 𝕋 P ℤ) (n : ℕ) : a ^ (n + 1) = a ^ n * a :=
  @_root_.pow_succ _ (instSemiring (P := P)).toMonoid a n

protected lemma pow_succ' (a : 𝕋 P ℤ) (n : ℕ) : a ^ (n + 1) = a * a ^ n :=
  @_root_.pow_succ' _ (instSemiring (P := P)).toMonoid a n

section API

/-- A basis element with coefficient zero is zero. -/
lemma T_single_zero (D : HeckeCoset P) :
    TSingle P ℤ D 0 = 0 := Finsupp.single_zero _

/-- Addition of two basis elements with the same double coset. -/
lemma T_single_add (D : HeckeCoset P) (a b : ℤ) :
    TSingle P ℤ D a + TSingle P ℤ D b = TSingle P ℤ D (a + b) :=
  (Finsupp.single_add D a b).symm

/-- Negation of a basis element. -/
lemma T_single_neg (D : HeckeCoset P) (a : ℤ) :
    -TSingle P ℤ D a = TSingle P ℤ D (-a) := (Finsupp.single_neg D a).symm

/-- Subtraction of two basis elements with the same double coset. -/
lemma T_single_sub (D : HeckeCoset P) (a b : ℤ) :
    TSingle P ℤ D a - TSingle P ℤ D b = TSingle P ℤ D (a - b) := by
  rw [sub_eq_add_neg, T_single_neg, T_single_add, sub_eq_add_neg]

/-- Scalar multiplication on a basis element. -/
lemma T_single_smul (D : HeckeCoset P) (n a : ℤ) :
    n • TSingle P ℤ D a = TSingle P ℤ D (n * a) := Finsupp.smul_single' n D a

/-- The integer cast into the Hecke ring lands on the identity double coset. -/
@[simp] lemma intCast_eq (n : ℤ) : (n : 𝕋 P ℤ) = TSingle P ℤ (HeckeCoset.one P) n :=
  rfl

/-- The product of two basis elements equals the scaled multiplication finsupp. -/
lemma T_single_mul_T_single (D₁ D₂ : HeckeCoset P) (a b : ℤ) :
    TSingle P ℤ D₁ a * TSingle P ℤ D₂ b =
      a • b • m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) :=
  mul_singleton_𝕋 P D₁ D₂ a b

/-- The product of two unit-coefficient basis elements is the multiplication finsupp. -/
@[simp] lemma T_single_one_mul_T_single_one (D₁ D₂ : HeckeCoset P) :
    TSingle P ℤ D₁ 1 * TSingle P ℤ D₂ 1 =
      m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  simp [T_single_mul_T_single]

/-- Right multiplication by 1 is the identity. -/
lemma T_single_mul_one (D : HeckeCoset P) (a : ℤ) :
    TSingle P ℤ D a * 1 = TSingle P ℤ D a := singleton_one_mul_𝕋 P D a

/-- Left multiplication by 1 is the identity. -/
lemma one_mul_T_single (D : HeckeCoset P) (a : ℤ) :
    1 * TSingle P ℤ D a = TSingle P ℤ D a := one_mul_singleton_𝕋 P D a

/-- When `heckeMultiplicity` is one on a single output and zero elsewhere, multiplication of
unit-coefficient basis elements produces a single basis element. -/
lemma T_single_one_mul_eq_single (D₁ D₂ D_out : HeckeCoset P)
    (h_one : heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
      (HeckeCoset.rep D_out) = 1)
    (h_zero : ∀ A, A ≠ D_out → heckeMultiplicity P (HeckeCoset.rep D₁)
      (HeckeCoset.rep D₂) (HeckeCoset.rep A) = 0) :
    TSingle P ℤ D₁ 1 * TSingle P ℤ D₂ 1 = TSingle P ℤ D_out 1 := by
  rw [T_single_one_mul_T_single_one,
    m_eq_single P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D_out h_one h_zero]

/-- Evaluating the multiplication finsupp at a double coset gives `heckeMultiplicity`. -/
@[simp] lemma m_apply (g₁ g₂ : P.Δ) (D : HeckeCoset P) :
    (m P g₁ g₂) D = heckeMultiplicity P g₁ g₂ (HeckeCoset.rep D) := rfl

/-- Right multiplication by `HeckeCoset.one` is the identity on `m`. -/
@[simp] lemma m_mul_T_one (D : HeckeCoset P) :
    m P (HeckeCoset.rep D) (HeckeCoset.one P).rep =
      Finsupp.single (⟦HeckeCoset.rep D⟧ : HeckeCoset P) 1 :=
  m_mul_one_eq_single P (HeckeCoset.rep D)

/-- Left multiplication by `HeckeCoset.one` is the identity on `m`. -/
@[simp] lemma m_T_one_mul (D : HeckeCoset P) :
    m P (HeckeCoset.one P).rep (HeckeCoset.rep D) =
      Finsupp.single (⟦HeckeCoset.rep D⟧ : HeckeCoset P) 1 :=
  m_one_mul_eq_single P (HeckeCoset.rep D)

/-- The support of the multiplication finsupp equals `mulSupport`. -/
lemma m_support (g₁ g₂ : P.Δ) :
    (m P g₁ g₂).support = mulSupport P g₁ g₂ := rfl

/-- The multiplicity `heckeMultiplicity` is nonneg since it is a natural number cast to `ℤ`. -/
lemma heckeMultiplicity_nonneg (g₁ g₂ d : P.Δ) :
    0 ≤ heckeMultiplicity P g₁ g₂ d := by
  simp [heckeMultiplicity]

/-- Extensionality for Hecke ring elements. -/
@[ext] lemma ext_𝕋 {f g : 𝕋 P ℤ}
    (h : ∀ D : HeckeCoset P, f.toFun D = g.toFun D) : f = g := Finsupp.ext h

/-- Induction principle for Hecke ring elements (basis + accumulation). -/
lemma induction_on_𝕋 {C : 𝕋 P ℤ → Prop} (f : 𝕋 P ℤ) (h_zero : C 0)
    (h_add : ∀ (D : HeckeCoset P) (a : ℤ) (g : 𝕋 P ℤ),
      D ∉ g.support → a ≠ 0 → C g → C (TSingle P ℤ D a + g)) : C f :=
  Finsupp.induction f h_zero h_add

/-- Linear induction principle: reduce to zero, single basis elements, and sums. -/
lemma induction_linear_𝕋 {C : 𝕋 P ℤ → Prop} (f : 𝕋 P ℤ) (h_zero : C 0)
    (h_single : ∀ (D : HeckeCoset P) (a : ℤ), C (TSingle P ℤ D a))
    (h_add : ∀ f g : 𝕋 P ℤ, C f → C g → C (f + g)) : C f :=
  Finsupp.induction_linear f h_zero h_add h_single

/-- Every Hecke ring element is a finite sum of basis elements. -/
lemma sum_single_𝕋 (f : 𝕋 P ℤ) :
    f = ∑ D ∈ f.support, TSingle P ℤ D (f.toFun D) := single_basis ℤ f

/-- The action of a basis Hecke element on a basis module element as a sum over orbits. -/
lemma T_single_smul_HeckeLeftCoset_single (D : HeckeCoset P) (m₀ : HeckeLeftCoset P) (a b : Z) :
    TSingle P Z D a • HeckeLeftCosetSingle P Z m₀ b =
    ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀),
      HeckeLeftCosetSingle P Z i (a * b) :=
  single_smul_single P Z D m₀ a b

end API

end HeckeRing
