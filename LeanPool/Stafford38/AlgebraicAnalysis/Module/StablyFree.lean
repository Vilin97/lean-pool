/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

module

public import Mathlib.RingTheory.Finiteness.Projective


/-!
# Stable freeness interface for projective modules

This module records the application-independent right-module formulation of
stable freeness used in filtered-ring arguments.  It is a definition, not a
claim that any particular ring has the property.
-/

@[expose] public section

namespace AlgebraicAnalysis
namespace StablyFree

universe u

/-- Every finitely generated projective right `R`-module becomes finite free
after adding a finite free summand.  Right modules are represented as modules
over `Rᵐᵒᵖ`, so the order of scalar multiplication remains explicit. -/
def StablyFreeProjectives (R : Type u) [Ring R] : Prop :=
  ∀ (P : Type u) [AddCommGroup P] [Module Rᵐᵒᵖ P],
    Module.Projective Rᵐᵒᵖ P → Module.Finite Rᵐᵒᵖ P →
      ∃ m n : ℕ,
        Nonempty (P × (Fin m → Rᵐᵒᵖ) ≃ₗ[Rᵐᵒᵖ] (Fin n → Rᵐᵒᵖ))

end StablyFree
end AlgebraicAnalysis
