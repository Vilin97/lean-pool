/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Polynomial.Laurent

import LeanPool.ConwayRefinement.ConwayRefinement.RingTheory.LocalizationUFM
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Unique factorisation in the group ring of a free abelian group of finite rank

The group ring of `ℤ ^ k` over a field is reached from the field by `k` Laurent extensions. Each
one is a polynomial extension, which preserves unique factorisation, followed by a localization at
the powers of the variable, which preserves it as well.
-/

universe u v

public noncomputable section

namespace LaurentPolynomial

/-- A Laurent polynomial ring over a unique factorisation domain is a unique factorisation
domain. -/
theorem uniqueFactorizationMonoid {A : Type u} [CommRing A] [IsDomain A]
    [UniqueFactorizationMonoid A] : UniqueFactorizationMonoid (LaurentPolynomial A) := by
  have hle : Submonoid.powers (Polynomial.X : Polynomial A) ≤ nonZeroDivisors (Polynomial A) := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n Polynomial.X_ne_zero)
  exact IsLocalization.uniqueFactorizationMonoid
    (B := LaurentPolynomial A) (Submonoid.powers (Polynomial.X : Polynomial A)) hle

end LaurentPolynomial

namespace AddMonoidAlgebra

/-- Splitting off the first coordinate of a tuple of integers. -/
def finSuccAddEquiv (n : ℕ) : ((Fin (n + 1)) → ℤ) ≃+ (ℤ × (Fin n → ℤ)) where
  toFun f := (f 0, fun i ↦ f i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv f := by
    funext i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro j
      simp
  right_inv p := by
    ext
    · simp
    · simp
  map_add' f g := by
    ext
    · simp
    · simp

/-- The group ring of `ℤ ^ k` over a field is a unique factorisation domain. -/
theorem uniqueFactorizationMonoid_finInt (K : Type v) [Field K] :
    ∀ k : ℕ, UniqueFactorizationMonoid (AddMonoidAlgebra K (Fin k → ℤ))
  | 0 => by
    refine MulEquiv.uniqueFactorizationMonoid
      (AddMonoidAlgebra.uniqueAlgEquiv (R := K) (A := K)
        (M := (Fin 0 → ℤ))).symm.toRingEquiv.toMulEquiv ?_
    infer_instance
  | (k + 1) => by
    have ih := uniqueFactorizationMonoid_finInt K k
    have hlaurent : UniqueFactorizationMonoid
        (LaurentPolynomial (AddMonoidAlgebra K (Fin k → ℤ))) :=
      LaurentPolynomial.uniqueFactorizationMonoid
    have f : AddMonoidAlgebra K (Fin (k + 1) → ℤ) ≃+*
        LaurentPolynomial (AddMonoidAlgebra K (Fin k → ℤ)) :=
      RingEquiv.trans
        (AddMonoidAlgebra.domCongr (R := K) (A := K) (e := finSuccAddEquiv k)).toRingEquiv
        (AddMonoidAlgebra.curryAlgEquiv (R := K) (A := K) (M := ℤ)
          (N := (Fin k → ℤ))).toRingEquiv
    exact MulEquiv.uniqueFactorizationMonoid f.symm.toMulEquiv hlaurent

end AddMonoidAlgebra
