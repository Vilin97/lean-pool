/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.HilbertSymbols.GlobalHilbertPairingProperties
import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.HilbertSymbols.HilbertProductFormula
/-!
# Finite support of every local Hilbert-pairing family

The norm-residue criterion determines exactly where a local symbol equals
one, even though it does not determine the symbol's other values.  Hence the
finite support of one constructed family transfers to every family satisfying
the local Hilbert-pairing laws.  No product-formula assumption is made about
the family being studied.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The local norm-residue law alone forces finite support of the finite-place
values on any fixed pair of nonzero global elements. -/
theorem globalHilbertPairing_hasFiniteSupport_of_isLocallyHilbert
    (F : Type u) [Field F] [NumberField F]
    (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : GlobalHilbertPairingFamily F n)
    (hB : GlobalHilbertPairingFamily.IsLocallyHilbert F B) :
    GlobalHilbertPairingFamily.HasFiniteSupport F B hmu := by
  obtain ⟨C, hC, hCfinite, _⟩ :=
    exists_globalHilbertPairingFamily_productFormula F n hmu
  intro a b
  apply (hCfinite a b).of_eq_one_iff
  intro v
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots
      (algebraMap F (v.adicCompletion F)).injective hmu
  let av : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom a
  let bv : (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom b
  change e.symm ((C v).symbol av bv) = 1 ↔
    e.symm ((B v).symbol av bv) = 1
  simp only [MulEquiv.map_eq_one_iff]
  exact ((hC v).2.2.2 av bv).trans ((hB v).2.2.2 av bv).symm

end ClassFieldTheory
