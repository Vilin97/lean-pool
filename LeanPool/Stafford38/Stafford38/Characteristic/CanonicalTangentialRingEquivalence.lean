/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import LeanPool.Stafford38.Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness


/-!
The polynomial-ring equivalence identifying old and retained tangential variables.
-/

@[expose] public section

namespace Stafford38.Characteristic.CanonicalTangentialRingEquivalence

open Stafford38.Characteristic
open Stafford38.Characteristic.CanonicalNormalSymbolFiniteness
open Stafford38.Characteristic.CanonicalTangentialSymbolFiniteness
open Stafford38.Characteristic.NormalSymbolPolynomial
open Stafford38.WeylIteratedEquivalence

noncomputable section

variable {k : Type*} [Field k]

/-- The old rank-`n` phase variable, regarded as a rank-`n+1` variable which
is neither the new momentum nor the new coordinate. -/
def oldTangentialVar (n : ℕ) (i : Fin n ⊕ Fin n) : TangentialVar n :=
  ⟨⟨oldIndex i, by
      cases i with
      | inl i => simp [oldIndex]
      | inr i => simp [oldIndex]⟩,
    by
      cases i with
      | inl i => simp [oldIndex]
      | inr i => simp [oldIndex]⟩

private theorem oldTangentialVar_injective (n : ℕ) :
    Function.Injective (oldTangentialVar n) := by
  intro i j h
  apply Stafford38.WeylPBW.oldIndex_injective
  exact congrArg (fun v : TangentialVar n => v.1.1) h

private theorem oldTangentialVar_surjective (n : ℕ) :
    Function.Surjective (oldTangentialVar n) := by
  intro v
  rcases v with ⟨⟨w, hnormal⟩, hcoordinate⟩
  rcases w with i | i
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact False.elim (hcoordinate (by rfl))
    · exact ⟨Sum.inl j, rfl⟩
  · rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact False.elim (hnormal (by rfl))
    · exact ⟨Sum.inr j, rfl⟩

/-- The exact variable dictionary: the two retained subtype exclusions are
precisely the image of `oldIndex`. -/
def oldTangentialVarEquiv (n : ℕ) :
    (Fin n ⊕ Fin n) ≃ TangentialVar n :=
  Equiv.ofBijective (oldTangentialVar n)
    ⟨oldTangentialVar_injective n, oldTangentialVar_surjective n⟩

@[simp]
theorem oldTangentialVarEquiv_apply (n : ℕ) (i : Fin n ⊕ Fin n) :
    (oldTangentialVarEquiv n i).1.1 = oldIndex i :=
  rfl

/-- Rename old phase variables into the coefficient ring which omits both
new variables. -/
def oldSymbolTangentialAlgEquiv (n : ℕ) :
    MvPolynomial (Fin n ⊕ Fin n) k ≃ₐ[k] tangentialCoeffRing (k := k) n :=
  MvPolynomial.renameEquiv k (oldTangentialVarEquiv n)

@[simp]
theorem oldSymbolTangentialAlgEquiv_X (n : ℕ)
    (i : Fin n ⊕ Fin n) :
    oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i) =
      MvPolynomial.X (oldTangentialVarEquiv n i) := by
  simp [oldSymbolTangentialAlgEquiv]

/-- Under the full coefficient-action homomorphism, the renamed variable is
the actual ambient symbol indexed by `oldIndex`. -/
theorem tangentialCoeffActionHom_oldSymbol_X (n : ℕ)
    (i : Fin n ⊕ Fin n) :
    ((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)
        (oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i)) =
      (MvPolynomial.X (oldIndex i) : SymbolRing k (n + 1)) := by
  simp [oldSymbolTangentialAlgEquiv, tangentialPolynomialActionHom,
    normalCoeffTangentialAlgEquiv, tangentialVariableEquiv,
    normalPolynomialActionHom, normalSymbolAlgEquiv, normalVariableEquiv,
    oldTangentialVarEquiv_apply]

/-- Consequently the named tangential coefficient module acts on every
symbol module by the same old-generator symbol used by the canonical total
polynomial action. -/
theorem tangentialCoeffModule_oldSymbol_X_action
    (n : ℕ) (E : Type*) [AddCommGroup E]
    [Module (SymbolRing k (n + 1)) E]
    (i : Fin n ⊕ Fin n) (z : E) :
    @SMul.smul (tangentialCoeffRing (k := k) n) E
        (tangentialCoeffModule (k := k) n E).toSMul
        (oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i)) z =
      (MvPolynomial.X (oldIndex i) : SymbolRing k (n + 1)) • z := by
  change ((tangentialPolynomialActionHom (k := k) n).comp Polynomial.C)
      (oldSymbolTangentialAlgEquiv (k := k) n (MvPolynomial.X i)) • z = _
  rw [tangentialCoeffActionHom_oldSymbol_X]


end
end Stafford38.Characteristic.CanonicalTangentialRingEquivalence
