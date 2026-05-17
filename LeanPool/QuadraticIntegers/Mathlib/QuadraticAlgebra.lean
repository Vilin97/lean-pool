/-
Copyright (c) 2026 Riccardo Brasca, Pietro Monticone. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/

import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace LeanPool
namespace QuadraticIntegers
namespace Mathlib
namespace QuadraticAlgebra

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]

instance instAlgebraBaseChange (a b : R) :
    Algebra (_root_.QuadraticAlgebra R a b)
      (_root_.QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  (_root_.QuadraticAlgebra.lift ⟨_root_.QuadraticAlgebra.omega, by
    simpa using (_root_.QuadraticAlgebra.omega_mul_omega_eq_add
      (a := algebraMap R S a) (b := algebraMap R S b))⟩).toRingHom.toAlgebra

instance instAlgebraInt (a b : ℤ) :
    Algebra (_root_.QuadraticAlgebra ℤ a b) (_root_.QuadraticAlgebra S a b) :=
  (_root_.QuadraticAlgebra.lift ⟨_root_.QuadraticAlgebra.omega, by
    simpa [Int.cast_smul_eq_zsmul] using
      (_root_.QuadraticAlgebra.omega_mul_omega_eq_add (R := S) (a := a) (b := b))⟩
    ).toRingHom.toAlgebra

instance instAlgebraIntPure (a : ℤ) :
    Algebra (_root_.QuadraticAlgebra ℤ a 0) (_root_.QuadraticAlgebra S a 0) :=
  (_root_.QuadraticAlgebra.lift ⟨_root_.QuadraticAlgebra.omega, by
    simpa [Int.cast_smul_eq_zsmul] using
      (_root_.QuadraticAlgebra.omega_mul_omega_eq_add (R := S) (a := a) (b := 0))⟩
    ).toRingHom.toAlgebra

end QuadraticAlgebra
end Mathlib
end QuadraticIntegers
end LeanPool
