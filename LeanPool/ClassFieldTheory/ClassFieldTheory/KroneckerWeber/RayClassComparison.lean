/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Topology
public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Rational
public import Mathlib.NumberTheory.Cyclotomic.Gal
/-!
# The rational ray-class/cyclotomic comparison

For `K = ℚ`, both the ray class quotient modulo `(m)` and the Galois
group of the `m`-th cyclotomic field are canonically `(ℤ/mℤ)ˣ`.  This
file composes the two independently constructed equivalences and verifies
the degree/index equality showing that the ray class
field is `ℚ(μ_m)`.
-/

@[expose] public section

open scoped NumberField Cyclotomic

noncomputable section

namespace KroneckerWeber

open Polynomial

/-- The rational ray class group modulo `(m)` is canonically the
automorphism group of the `m`-th cyclotomic field. -/
noncomputable def rationalRayClassGroupEquivCyclotomicAut
    (m : ℕ) (hm : m ≠ 0) :
    RayClass.RayClassGroup (RayClass.rationalModulus m) ≃*
      (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ) := by
  letI : NeZero m := ⟨hm⟩
  letI : NeZero (m : ℚ) := ⟨by exact_mod_cast hm⟩
  letI : IsCyclotomicExtension {m} ℚ
      (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  exact
    (RayClass.rationalRayClassGroupEquivZModUnits m hm).trans
      (IsCyclotomicExtension.autEquivPow
        (CyclotomicField m ℚ)
        (Polynomial.cyclotomic.irreducible_rat
          (Nat.pos_of_ne_zero hm))).symm

/-- The quotient by the rational ray-class norm subgroup is the Galois
group of the corresponding cyclotomic field. -/
noncomputable def rationalRayClassFieldQuotientEquivCyclotomicAut
    (m : ℕ) (hm : m ≠ 0) :
    IdeleClassGroup ℚ ⧸
        RayClass.Modulus.congruenceSubgroup
          (RayClass.rationalModulus m) ≃*
      (CyclotomicField m ℚ ≃ₐ[ℚ] CyclotomicField m ℚ) :=
  rationalRayClassGroupEquivCyclotomicAut m hm

/-- The index of the rational ray congruence subgroup equals the degree
of the `m`-th cyclotomic field. -/
theorem rationalRayClassFieldQuotient_card_eq_cyclotomicDegree
    (m : ℕ) (hm : m ≠ 0) :
    Nat.card
        (IdeleClassGroup ℚ ⧸
          RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) =
      Module.finrank ℚ (CyclotomicField m ℚ) := by
  let : NeZero m := ⟨hm⟩
  let : NeZero (m : ℚ) := ⟨by exact_mod_cast hm⟩
  let : IsCyclotomicExtension {m} ℚ
      (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  let : IsGalois ℚ (CyclotomicField m ℚ) :=
    IsCyclotomicExtension.isGalois {m} ℚ
      (CyclotomicField m ℚ)
  calc
    Nat.card
        (IdeleClassGroup ℚ ⧸
          RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) =
        Nat.card
          (CyclotomicField m ℚ ≃ₐ[ℚ]
            CyclotomicField m ℚ) :=
      Nat.card_congr
        (rationalRayClassFieldQuotientEquivCyclotomicAut
          m hm).toEquiv
    _ = Module.finrank ℚ (CyclotomicField m ℚ) :=
      IsGalois.card_aut_eq_finrank ℚ (CyclotomicField m ℚ)

/-- Both sides of the rational ray-class/cyclotomic comparison have
Euler-totient order. -/
theorem rationalRayClassFieldQuotient_card_eq_totient
    (m : ℕ) (hm : m ≠ 0) :
    Nat.card
        (IdeleClassGroup ℚ ⧸
          RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) =
      m.totient := by
  let : NeZero m := ⟨hm⟩
  let : NeZero (m : ℚ) := ⟨by exact_mod_cast hm⟩
  let : IsCyclotomicExtension {m} ℚ
      (CyclotomicField m ℚ) :=
    CyclotomicField.isCyclotomicExtension m ℚ
  calc
    Nat.card
        (IdeleClassGroup ℚ ⧸
          RayClass.Modulus.congruenceSubgroup
            (RayClass.rationalModulus m)) =
        Module.finrank ℚ (CyclotomicField m ℚ) :=
      rationalRayClassFieldQuotient_card_eq_cyclotomicDegree
        m hm
    _ = m.totient :=
      IsCyclotomicExtension.finrank
        (CyclotomicField m ℚ)
        (Polynomial.cyclotomic.irreducible_rat
          (Nat.pos_of_ne_zero hm))

end KroneckerWeber
