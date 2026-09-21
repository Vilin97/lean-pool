/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Ore.ScalarAlgebra
import LeanPool.Stafford38.Proofs.WeylSymplectic

/-!
# Universal property of the presented Weyl algebra

This factors the quotient lift used by the existing symplectic maps: any
family satisfying the prescribed commutators induces a unique algebra map.
-/

namespace Stafford38.WeylUniversal

open Stafford
open AlgebraicAnalysis

noncomputable section

variable {k ι A : Type*} [Field k] [Ring A] [Algebra k A]

def freeWeylGeneratorMap (z : ι → A) : FreeAlgebra k ι →ₐ[k] A :=
  FreeAlgebra.lift k z

theorem freeWeylGeneratorMap_respects (omega : Matrix ι ι k) (z : ι → A)
    (hz : ∀ i j, Stafford.commutator (z i) (z j) = algebraMap k A (omega i j)) :
  ∀ ⦃a b : FreeAlgebra k ι⦄,
      freeWeylRelation omega a b →
        freeWeylGeneratorMap z a = freeWeylGeneratorMap z b
  | _, _, ⟨i, j, rfl, rfl⟩ => by
      simp only [freeWeylGeneratorMap, map_sub, map_mul,
        FreeAlgebra.lift_ι_apply, AlgHom.commutes]
      exact hz i j

/-- The algebra map induced by a family with the prescribed commutators. -/
def freeWeylLift (omega : Matrix ι ι k) (z : ι → A)
    (hz : ∀ i j, Stafford.commutator (z i) (z j) = algebraMap k A (omega i j)) :
    FreeWeyl k ι omega →ₐ[k] A :=
  RingQuot.liftAlgHom k
    ⟨freeWeylGeneratorMap z, freeWeylGeneratorMap_respects omega z hz⟩

@[simp] theorem freeWeylLift_generator (omega : Matrix ι ι k) (z : ι → A)
    (hz : ∀ i j, Stafford.commutator (z i) (z j) = algebraMap k A (omega i j)) (i : ι) :
    freeWeylLift omega z hz (freeWeylGenerator omega i) = z i := by
  simp [freeWeylLift, freeWeylGenerator, freeWeylGeneratorMap,
    RingQuot.liftAlgHom_mkAlgHom_apply]

/-- Algebra maps out of the presented Weyl algebra are determined by the
canonical generators. -/
theorem freeWeyl_algHom_ext (omega : Matrix ι ι k)
    (f g : FreeWeyl k ι omega →ₐ[k] A)
    (h : ∀ i, f (freeWeylGenerator omega i) =
      g (freeWeylGenerator omega i)) : f = g := by
  apply RingQuot.ringQuot_ext' k
  apply FreeAlgebra.hom_ext
  funext i
  exact h i


end
end Stafford38.WeylUniversal
