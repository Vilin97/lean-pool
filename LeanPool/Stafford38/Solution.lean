/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.FoundationClosure

namespace Stafford38Challenge

abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

def relation {k : Type*} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k (PhaseVar n)) (omega i j)

abbrev WeylAlg (k : Type*) [Field k] (n : ℕ) :=
  RingQuot (relation (k := k) (n := n) (Matrix.J (Fin n) k))

def UniversalStatement : Prop :=
  ∀ (k : Type*) [Field k] [CharZero k] (n : ℕ) (d : WeylAlg k n),
    d ≠ 0 → ∃ F R S : WeylAlg k n, (1 : WeylAlg k n) = d * R + F * d * S

private def toSubstantive (k : Type*) [Field k] (n : ℕ) :
    WeylAlg k n ≃ₐ[k] Stafford38.WeylAlg k n :=
  AlgEquiv.refl

theorem universalStatement : UniversalStatement := by
  intro k _ _ n d hd
  let e := toSubstantive k n
  have hsd : e d ≠ 0 := by
    intro h
    apply hd
    apply e.injective
    simpa using h
  rcases Stafford38.universalStatement (k := k) n (e d) hsd with ⟨F, R, S, h⟩
  refine ⟨e.symm F, e.symm R, e.symm S, ?_⟩
  simpa using congrArg e.symm h

end Stafford38Challenge
