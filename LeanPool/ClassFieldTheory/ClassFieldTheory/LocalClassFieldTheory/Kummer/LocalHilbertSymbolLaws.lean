/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
/-!
# Kernel laws for the local Hilbert symbol

The local Hilbert-symbol character is the composite of the local Artin map,
the injective character obtained by evaluating automorphisms on the chosen
Kummer radical, and the equivalence that transports roots of unity back to
the base field.  Consequently its kernel is exactly the local norm subgroup.
This also makes the induced character on the concrete norm quotient
injective.
-/

noncomputable section

namespace LocalClassFieldTheory
namespace Kummer

open KummerTheory
open LocalFieldTheory

variable (K : Type) [Field K]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The kernel of the local Hilbert-symbol character is exactly the norm
subgroup from the associated simple Kummer extension. -/
theorem localHilbertSymbolHom_ker
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    (localHilbertSymbolHom K n hnK hmu b).ker =
      localNormSubgroup K (chosenSimpleKummerExtension K n hnK b) := by
  unfold localHilbertSymbolHom
  rw [MonoidHom.ker_comp_of_injective _ _
    (nthRootsSubgroupEquivOfPrimitiveRoots
      K (chosenSimpleKummerExtension K n hnK b) n hmu).symm.injective]
  rw [MonoidHom.ker_comp_of_injective _ _
    (chosenSimpleKummerRootCharacter_injective K n hnK hmu b)]
  exact chosenSimpleKummerNormResidueAutomorphism_ker K n hnK hmu b

/-- A local Hilbert symbol is one exactly when its first argument is a norm
from the simple Kummer extension determined by its second argument. -/
theorem localHilbertSymbol_eq_one_iff_mem_localNormSubgroup
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (a b : Kˣ) :
    localHilbertSymbol K n hnK hmu a b = 1 ↔
      a ∈ localNormSubgroup K (chosenSimpleKummerExtension K n hnK b) := by
  change localHilbertSymbolHom K n hnK hmu b a = 1 ↔ _
  rw [← MonoidHom.mem_ker, localHilbertSymbolHom_ker K n hnK hmu b]

/-- The local Hilbert-symbol character induced on the corresponding norm
quotient is injective. -/
theorem localHilbertSymbolFromNormQuotient_injective
    (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Function.Injective
      (localHilbertSymbolFromNormQuotient K n hnK hmu b) := by
  apply
    (localHilbertSymbolFromNormQuotient K n hnK hmu b).ker_eq_bot_iff.mp
  ext q
  refine NormQuotient.inductionOn
    (motive := fun q =>
      q ∈ (localHilbertSymbolFromNormQuotient K n hnK hmu b).ker ↔
        q ∈ (⊥ : Subgroup
          (NormQuotient K (chosenSimpleKummerExtension K n hnK b))))
    q ?_
  intro a
  rw [MonoidHom.mem_ker, Subgroup.mem_bot,
    localHilbertSymbolFromNormQuotient_normClass,
    localHilbertSymbol_eq_one_iff_mem_localNormSubgroup,
    normClass_eq_one_iff_mem]

end Kummer
end LocalClassFieldTheory
