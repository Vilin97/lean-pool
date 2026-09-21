/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
/-!
# Hilbert ramification theory: ramification and inertia in towers

This file records the tower identities for ramification indices and inertia
degrees used in the prime-decomposition tower identity.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

variable {A B C : Type*}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C]
variable [IsScalarTower A B C]

/-- The prime-decomposition tower identity:
ramification indices multiply in a tower. -/
theorem ramificationIdx_tower
    [IsDedekindDomain B] [IsDedekindDomain C]
    {p : Ideal A} {P : Ideal B} {Q : Ideal C}
    [P.IsPrime] [Q.IsPrime]
    (hP : Ideal.map (algebraMap B C) P ≠ ⊥)
    (hp : Ideal.map (algebraMap A C) p ≠ ⊥)
    (hPQ : Ideal.map (algebraMap B C) P ≤ Q) :
    Ideal.ramificationIdx' p Q =
      Ideal.ramificationIdx' p P *
        Ideal.ramificationIdx' P Q := by
  exact Ideal.ramificationIdx'_algebra_tower hP hp hPQ

/-- The prime-decomposition tower identity:
inertia degrees multiply in a tower. -/
theorem dedekindTower_inertiaDeg_tower
    (p : Ideal A) [p.IsMaximal]
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (Q : Ideal C) [Q.LiesOver P] :
    Q.inertiaDeg A =
      P.inertiaDeg A * Q.inertiaDeg B := by
  exact Ideal.inertiaDeg_tower (R := A) P Q

/-- The prime-decomposition tower arithmetic identity:
if the top layer of a tower already accounts for the full product `e * f`,
while ramification indices and inertia degrees multiply in the tower, then the
lower layer is unramified with residue degree one, and the top layer has the
original invariants. -/
theorem dedekindTower_tower_invariants_of_top_product
    {e f eBase fBase eTop fTop : ℕ}
    (heTop : eTop ≠ 0) (hfTop : fTop ≠ 0)
    (he : e = eBase * eTop)
    (hf : f = fBase * fTop)
    (hprod : eTop * fTop = e * f) :
    eBase = 1 ∧ fBase = 1 ∧ eTop = e ∧ fTop = f := by
  have htop_pos : 0 < eTop * fTop :=
    Nat.mul_pos (Nat.pos_of_ne_zero heTop) (Nat.pos_of_ne_zero hfTop)
  have hmain : eBase * fBase = 1 := by
    apply Nat.mul_right_cancel htop_pos
    calc
      (eBase * fBase) * (eTop * fTop)
          = (eBase * eTop) * (fBase * fTop) := by ac_rfl
      _ = e * f := by rw [← he, ← hf]
      _ = eTop * fTop := hprod.symm
      _ = 1 * (eTop * fTop) := by simp
  have heBase : eBase = 1 :=
    Nat.eq_one_of_mul_eq_one_right hmain
  have hfBase : fBase = 1 :=
    Nat.eq_one_of_mul_eq_one_left hmain
  refine ⟨heBase, hfBase, ?_, ?_⟩
  · rw [he, heBase, one_mul]
  · rw [hf, hfBase, one_mul]

/-- The prime-decomposition tower identity:
the ideal-theoretic tower form of the preceding arithmetic cancellation.  The
hypothesis `hprod` is exactly the equality supplied in the prime-decomposition tower identity by
the nonsplitting of the top prime and the fixed-field degree computation
`[L : Z_P] = e * f`. -/
theorem dedekindTower_ideal_tower_invariants_of_top_product
    [IsDedekindDomain B] [IsDedekindDomain C] [Module.Finite B C]
    {p : Ideal A} [p.IsMaximal]
    {P : Ideal B} [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    {Q : Ideal C} [Q.IsPrime] [Q.LiesOver P]
    (hP : Ideal.map (algebraMap B C) P ≠ ⊥)
    (hp : Ideal.map (algebraMap A C) p ≠ ⊥)
    (hPQ : Ideal.map (algebraMap B C) P ≤ Q)
    (hprod :
      Ideal.ramificationIdx' P Q * Q.inertiaDeg B =
        Ideal.ramificationIdx' p Q * Q.inertiaDeg A) :
    Ideal.ramificationIdx' p P = 1 ∧
      P.inertiaDeg A = 1 ∧
      Ideal.ramificationIdx' P Q =
        Ideal.ramificationIdx' p Q ∧
      Q.inertiaDeg B = Q.inertiaDeg A := by
  have heTop :
      Ideal.ramificationIdx' P Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
      (p := P) (P := Q) hP inferInstance hPQ
  exact
    dedekindTower_tower_invariants_of_top_product
      heTop (Q.inertiaDeg_pos B).ne'
      (ramificationIdx_tower
        (A := A) (B := B) (C := C) hP hp hPQ)
      (dedekindTower_inertiaDeg_tower
        (A := A) (B := B) (C := C) p P Q)
      hprod

/-- A prime-decomposition arithmetic consequence:
if the top layer of a tower has the full ramification index and residue degree
one, then the middle layer has ramification index one and the full residue
degree. -/
theorem dedekindRamification_tower_middle_invariants_of_top_invariants
    {e f eBase fBase eTop fTop : ℕ}
    (heTop : eTop ≠ 0)
    (he : e = eBase * eTop)
    (hf : f = fBase * fTop)
    (heTop_eq : eTop = e)
    (hfTop_eq : fTop = 1) :
    eBase = 1 ∧ fBase = f := by
  have heBase : eBase = 1 := by
    apply Eq.symm
    apply Nat.mul_right_cancel (Nat.pos_of_ne_zero heTop)
    calc
      1 * eTop = eTop := one_mul eTop
      _ = e := heTop_eq
      _ = eBase * eTop := he
  have hfBase : fBase = f := by
    rw [hf, hfTop_eq, mul_one]
  exact ⟨heBase, hfBase⟩

/-- A prime-decomposition consequence:
the ideal-theoretic tower form of the preceding arithmetic cancellation.  This
is the step from the already-proved `P/P_T` invariants to the `P_T/P_Z`
invariants in the diagram `Z_P -> T_P -> L`. -/
theorem dedekindRamification_ideal_tower_middle_invariants_of_top_invariants
    [IsDedekindDomain B] [IsDedekindDomain C]
    {p : Ideal A} [p.IsMaximal]
    {P : Ideal B} [P.IsPrime] [P.IsMaximal] [P.LiesOver p]
    {Q : Ideal C} [Q.IsPrime] [Q.LiesOver P]
    (hP : Ideal.map (algebraMap B C) P ≠ ⊥)
    (hp : Ideal.map (algebraMap A C) p ≠ ⊥)
    (hPQ : Ideal.map (algebraMap B C) P ≤ Q)
    (heTop :
      Ideal.ramificationIdx' P Q =
        Ideal.ramificationIdx' p Q)
    (hfTop : Q.inertiaDeg B = 1) :
    Ideal.ramificationIdx' p P = 1 ∧
      P.inertiaDeg A = Q.inertiaDeg A := by
  have heTop_ne :
      Ideal.ramificationIdx' P Q ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
      (p := P) (P := Q) hP inferInstance hPQ
  exact
    dedekindRamification_tower_middle_invariants_of_top_invariants
      heTop_ne
      (ramificationIdx_tower
        (A := A) (B := B) (C := C) hP hp hPQ)
      (dedekindTower_inertiaDeg_tower
        (A := A) (B := B) (C := C) p P Q)
      heTop hfTop

end Dedekind
end HilbertRamification
