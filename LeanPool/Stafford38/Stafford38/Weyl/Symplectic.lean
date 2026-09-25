/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
public import LeanPool.Stafford38.Proofs.WeylSymplectic


/-!
# General-rank linear symplectic changes of Weyl generators

A matrix preserving the standard symplectic form defines an algebra
endomorphism of the presented Weyl algebra. Two form-preserving matrices that
are mutual inverses define a checked algebra equivalence. The inverse is part
of the input, which keeps this theorem independent of matrix inversion APIs
and makes the exact direction of generator substitution explicit.
-/

@[expose] public section

namespace Stafford38.WeylSymplectic

open Stafford
open AlgebraicAnalysis

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The standard symplectic matrix on coordinate and momentum indices. -/
abbrev standardForm (n : ℕ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k :=
  Matrix.J (Fin n) k

/-- Preservation of the standard Weyl commutator relations under a symplectic linear change. -/
theorem standardSymplecticHpres {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n) :
    ∀ i j,
      Stafford.commutator
          (freeWeylLinearCombination M
            (freeWeylGenerator (standardForm k n)) i)
          (freeWeylLinearCombination M
            (freeWeylGenerator (standardForm k n)) j) =
        algebraMap k (FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n))
          (standardForm k n i j) := by
  exact symplectic_linear_change_preserves_commutator M
    (freeWeylGenerator (standardForm k n)) (standardForm k n)
    (fun i j => freeWeylGenerator_commutator (standardForm k n) i j) hM

/-- The presented Weyl algebra endomorphism induced by a standard symplectic matrix. -/
def standardSymplecticAlgHom {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n) :
    FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n) →ₐ[k]
      FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n) :=
  freeWeylSymplecticAlgHom M (standardForm k n)
    (standardSymplecticHpres k M hM)

@[simp]
theorem standardSymplecticAlgHom_generator {n : ℕ}
    (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (i : Fin n ⊕ Fin n) :
    standardSymplecticAlgHom k M hM
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination M (freeWeylGenerator (standardForm k n)) i :=
  freeWeylSymplecticAlgHom_generator M (standardForm k n)
    (standardSymplecticHpres k M hM) i

theorem standardSymplecticAlgHom_comp_eq_id {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hNM : N * M = 1) :
    (standardSymplecticAlgHom k M hM).comp
        (standardSymplecticAlgHom k N hN) =
      AlgHom.id k (FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n)) := by
  apply RingQuot.ringQuot_ext' k
  apply FreeAlgebra.hom_ext
  funext i
  change standardSymplecticAlgHom k M hM
      (standardSymplecticAlgHom k N hN
        (freeWeylGenerator (standardForm k n) i)) =
    freeWeylGenerator (standardForm k n) i
  calc
    _ = freeWeylLinearCombination (N * M)
        (freeWeylGenerator (standardForm k n)) i := by
      simpa [standardSymplecticAlgHom] using
        freeWeylSymplecticAlgHom_comp_generator M N (standardForm k n)
          (standardSymplecticHpres k M hM)
          (standardSymplecticHpres k N hN) i
    _ = _ := by
      rw [hNM]
      exact freeWeylLinearCombination_one (standardForm k n) i

/-- A general-rank symplectic change with an explicitly certified inverse. -/
def standardSymplecticAlgEquivOfInverse {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hMN : M * N = 1) (hNM : N * M = 1) :
    FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n) ≃ₐ[k]
      FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n) :=
  AlgEquiv.mk
    { toFun := standardSymplecticAlgHom k M hM
      invFun := standardSymplecticAlgHom k N hN
      left_inv := fun x => DFunLike.congr_fun
        (standardSymplecticAlgHom_comp_eq_id k N M hN hM hMN) x
      right_inv := fun x => DFunLike.congr_fun
        (standardSymplecticAlgHom_comp_eq_id k M N hM hN hNM) x }
    (standardSymplecticAlgHom k M hM).map_mul
    (standardSymplecticAlgHom k M hM).map_add
    (standardSymplecticAlgHom k M hM).commutes

@[simp]
theorem standardSymplecticAlgEquivOfInverse_generator {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : Fin n ⊕ Fin n) :
    standardSymplecticAlgEquivOfInverse k M N hM hN hMN hNM
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination M (freeWeylGenerator (standardForm k n)) i :=
  standardSymplecticAlgHom_generator k M hM i

@[simp]
theorem standardSymplecticAlgEquivOfInverse_symm_generator {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : Fin n ⊕ Fin n) :
    (standardSymplecticAlgEquivOfInverse k M N hM hN hMN hNM).symm
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination N (freeWeylGenerator (standardForm k n)) i :=
  standardSymplecticAlgHom_generator k N hN i

/- Exact statement pins for composition order and both substitution maps. -/
example {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hNM : N * M = 1) :
    (standardSymplecticAlgHom k M hM).comp
        (standardSymplecticAlgHom k N hN) =
      AlgHom.id k (FreeWeyl k (Fin n ⊕ Fin n) (standardForm k n)) :=
  standardSymplecticAlgHom_comp_eq_id k M N hM hN hNM

example {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : Fin n ⊕ Fin n) :
    standardSymplecticAlgEquivOfInverse k M N hM hN hMN hNM
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination M (freeWeylGenerator (standardForm k n)) i :=
  standardSymplecticAlgEquivOfInverse_generator k M N hM hN hMN hNM i

example {n : ℕ}
    (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) k)
    (hM : M * standardForm k n * Matrix.transpose M = standardForm k n)
    (hN : N * standardForm k n * Matrix.transpose N = standardForm k n)
    (hMN : M * N = 1) (hNM : N * M = 1) (i : Fin n ⊕ Fin n) :
    (standardSymplecticAlgEquivOfInverse k M N hM hN hMN hNM).symm
        (freeWeylGenerator (standardForm k n) i) =
      freeWeylLinearCombination N (freeWeylGenerator (standardForm k n)) i :=
  standardSymplecticAlgEquivOfInverse_symm_generator
    k M N hM hN hMN hNM i


end

end Stafford38.WeylSymplectic
