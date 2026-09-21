/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.Characteristic.Polynomial

/-!
# Linear substitutions on polynomial phase space

A square matrix acts on the phase-space polynomial ring by substituting its
row-linear combination for each variable. Composition is contravariant in the
matrix order, matching the Weyl-generator substitution convention. Explicit
mutual inverse certificates produce an algebra equivalence.
-/

namespace Stafford38.CharacteristicLinearAction

open Stafford38.Characteristic

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The linear symbol polynomial determined by a row of the change-of-variables matrix. -/
def symbolLinearCombination {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    SymbolRing k n :=
  ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

/-- The symbol-algebra map induced by a matrix of linear substitutions. -/
def symbolLinearAlgHom {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) :
    SymbolRing k n →ₐ[k] SymbolRing k n :=
  MvPolynomial.aeval (symbolLinearCombination k M)

@[simp]
theorem symbolLinearAlgHom_X {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (i : PhaseVar n) :
    symbolLinearAlgHom k M (MvPolynomial.X i) =
      symbolLinearCombination k M i := by
  rw [symbolLinearAlgHom, MvPolynomial.aeval_X]

theorem symbolLinearAlgHom_C {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k) (c : k) :
    symbolLinearAlgHom k M (MvPolynomial.C c) = MvPolynomial.C c := by
  rw [symbolLinearAlgHom, MvPolynomial.aeval_C]
  rfl

theorem symbolLinearAlgHom_comp {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k) :
    (symbolLinearAlgHom k M).comp (symbolLinearAlgHom k N) =
      symbolLinearAlgHom k (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [AlgHom.comp_apply, symbolLinearAlgHom_X, symbolLinearAlgHom_X]
  simp only [symbolLinearCombination, map_sum, map_mul,
    symbolLinearAlgHom_C, symbolLinearAlgHom_X, Matrix.mul_apply]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem symbolLinearAlgHom_one {n : ℕ} :
    symbolLinearAlgHom k (1 : Matrix (PhaseVar n) (PhaseVar n) k) =
      AlgHom.id k (SymbolRing k n) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [symbolLinearCombination, Matrix.one_apply]

/-- The polynomial substitution equivalence attached to explicitly certified
inverse matrices. -/
def symbolLinearAlgEquivOfInverse {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    SymbolRing k n ≃ₐ[k] SymbolRing k n :=
  AlgEquiv.ofAlgHom (symbolLinearAlgHom k M) (symbolLinearAlgHom k N)
    (by rw [symbolLinearAlgHom_comp, hNM, symbolLinearAlgHom_one])
    (by rw [symbolLinearAlgHom_comp, hMN, symbolLinearAlgHom_one])

@[simp]
theorem symbolLinearAlgEquivOfInverse_X {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : PhaseVar n) :
    symbolLinearAlgEquivOfInverse k M N hMN hNM (MvPolynomial.X i) =
      symbolLinearCombination k M i :=
  symbolLinearAlgHom_X k M i

@[simp]
theorem symbolLinearAlgEquivOfInverse_symm_X {n : ℕ}
    (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : PhaseVar n) :
    (symbolLinearAlgEquivOfInverse k M N hMN hNM).symm
        (MvPolynomial.X i) = symbolLinearCombination k N i :=
  symbolLinearAlgHom_X k N i

/- Exact statement pins for matrix order and both substitutions. -/
example {n : ℕ} (M N : Matrix (PhaseVar n) (PhaseVar n) k) :
    (symbolLinearAlgHom k M).comp (symbolLinearAlgHom k N) =
      symbolLinearAlgHom k (N * M) :=
  symbolLinearAlgHom_comp k M N

example {n : ℕ} (M N : Matrix (PhaseVar n) (PhaseVar n) k)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : PhaseVar n) :
    (symbolLinearAlgEquivOfInverse k M N hMN hNM).symm
        (MvPolynomial.X i) = symbolLinearCombination k N i :=
  symbolLinearAlgEquivOfInverse_symm_X k M N hMN hNM i


end

end Stafford38.CharacteristicLinearAction
