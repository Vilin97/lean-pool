/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Subgroup.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
/-!
# Cardinality under inertia scalar restriction

This is the finite-cardinality consequence of the inertia-subgroup cardinality formula used when
the base completion is identified with a concrete local field.
-/

@[expose] public section

noncomputable section

universe u v w

namespace HilbertRamification
namespace ValuationSubring

open RamificationTheory.HilbertRamification.ValuationSubring

variable {K : Type u} {M : Type v} {L : Type w}
variable [Field K] [Field M] [Field L]
variable [Algebra K M] [Algebra M L] [Algebra K L]
variable [IsScalarTower K M L]

/-- Restriction of scalars embeds the inertia group over an intermediate
base into the inertia group over the smaller base. -/
theorem inertiaGroupRestrictScalars_injective
    (A : _root_.ValuationSubring L) :
    Function.Injective
      (inertiaGroupRestrictScalars (K := K) (M := M) A) := by
  intro σ τ hστ
  apply Subtype.ext
  apply Subtype.ext
  apply decompositionGroupRestriction_restrictAutomorphismScalars_injective
    (K := K) (M := M) (L := L)
  simpa [inertiaGroupRestrictScalars, decompositionGroupRestrictScalars] using
    congrArg
      (fun ρ : inertiaGroup K A ↦
        (((ρ : decompositionGroup K A) : L ≃ₐ[K] L))) hστ

/-- The inertia cardinality cannot increase when restricting scalars from
an intermediate base field. -/
theorem natCard_inertiaGroup_le_restrictScalars
    [FiniteDimensional K L]
    (A : _root_.ValuationSubring L) :
    Nat.card (inertiaGroup M A) ≤ Nat.card (inertiaGroup K A) := by
  let : Finite (L ≃ₐ[K] L) := inferInstance
  let : Finite (decompositionGroup K A) := inferInstance
  let : Finite (inertiaGroup K A) := inferInstance
  exact Nat.card_le_card_of_injective
    (inertiaGroupRestrictScalars (K := K) (M := M) A)
    (inertiaGroupRestrictScalars_injective (K := K) (M := M) A)

end ValuationSubring
end HilbertRamification

end
