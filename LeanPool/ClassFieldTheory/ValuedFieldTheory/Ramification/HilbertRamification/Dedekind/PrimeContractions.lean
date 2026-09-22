/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldTower
/-!
# Hilbert ramification theory: number-field prime contractions

This file specializes the fixed fields `Z_P` and `T_P` to rings of integers
of number fields and defines the contracted primes `p`, `P_Z`, and `P_T`.
-/

noncomputable section

namespace HilbertRamification
namespace Dedekind

open Algebra NumberField
open scoped Pointwise

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*}
variable [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable (G : Type*) [Group G] [MulSemiringAction G L] [SMulCommClass G K L]

/-- Number-field ring-of-integers extensions are finite as modules.  Mathlib
keeps the corresponding `Algebra.IsIntegral.finite` conversion out of instance
search, so the HRT number-field layer records the source explicitly. -/
theorem ringOfIntegers_moduleFinite :
    Module.Finite (𝓞 K) (𝓞 L) := by
  exact
    ⟨(isNoetherian_def.mp
      (inferInstance : IsNoetherian (𝓞 K) (𝓞 L)) ⊤)⟩

/-- The contraction of a maximal finite prime of a number-field ring of
integers to a subfield ring of integers is nonzero. -/
theorem ringOfIntegers_under_ne_bot
    {E F : Type*} [Field E] [Field F] [NumberField E]
    [Algebra E F] (P : Ideal (𝓞 F)) [P.IsMaximal] :
    P.under (𝓞 E) ≠ ⊥ := by
  exact
    Ring.ne_bot_of_isMaximal_of_not_isField
      (M := P.under (𝓞 E)) inferInstance
      (RingOfIntegers.not_isField E)

/-- prime-decomposition theory:
`p = P ∩ O_K`, the prime ideal of the base number field below `P`. -/
abbrev basePrime
    (P : Ideal (𝓞 L)) :
    Ideal (𝓞 K) :=
  P.under (𝓞 K)

/-- The contracted base prime is prime. -/
instance basePrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (basePrime (K := K) P).IsPrime :=
  inferInstance

/-- The top prime lies over its contraction to the base ring of integers. -/
instance basePrime_liesOver
    (P : Ideal (𝓞 L)) :
    P.LiesOver (basePrime (K := K) P) where
  over := rfl

omit [NumberField L] in
/-- Prime-decomposition statement:
for a finite prime `P` of `O_L`, its contraction to `O_K` is nonzero. -/
theorem basePrime_ne_bot
    (P : Ideal (𝓞 L)) [P.IsMaximal] :
    basePrime (K := K) P ≠ ⊥ := by
  exact ringOfIntegers_under_ne_bot (E := K) (F := L) P

/-- The prime-decomposition tower identity:
`P_Z = P ∩ O_{Z_P}` for the decomposition field. -/
abbrev decompositionFieldPrime
    (P : Ideal (𝓞 L)) :
    Ideal (𝓞 (decompositionField (K := K) (L := L) G P)) :=
  P.under (𝓞 (decompositionField (K := K) (L := L) G P))

/-- The contracted decomposition-field prime is prime. -/
instance decompositionFieldPrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (decompositionFieldPrime (K := K) (L := L) G P).IsPrime :=
  inferInstance

/-- The top prime lies over its contraction to the decomposition field. -/
instance decompositionFieldPrime_liesOver
    (P : Ideal (𝓞 L)) :
    P.LiesOver (decompositionFieldPrime (K := K) (L := L) G P) where
  over := rfl

/-- The decomposition-field contraction lies over the base contraction. -/
instance decompositionFieldPrime_liesOver_basePrime
    (P : Ideal (𝓞 L)) :
    (decompositionFieldPrime (K := K) (L := L) G P).LiesOver
      (basePrime (K := K) P) :=
  Ideal.LiesOver.tower_bot P
    (decompositionFieldPrime (K := K) (L := L) G P)
    (basePrime (K := K) P)

/-- The prime-decomposition tower identity:
the contracted decomposition-field prime `P_Z` is nonzero for a finite prime
`P` of `O_L`. -/
theorem decompositionFieldPrime_ne_bot
    (P : Ideal (𝓞 L)) [P.IsMaximal] :
    decompositionFieldPrime (K := K) (L := L) G P ≠ ⊥ := by
  exact
    ringOfIntegers_under_ne_bot
      (E := decompositionField (K := K) (L := L) G P) (F := L) P

/-- A prime-decomposition consequence:
`P_T = P ∩ O_{T_P}` for the inertia field. -/
abbrev inertiaFieldPrime
    (P : Ideal (𝓞 L)) :
    Ideal (𝓞 (inertiaField (K := K) (L := L) G P)) :=
  P.under (𝓞 (inertiaField (K := K) (L := L) G P))

/-- The contracted inertia-field prime is prime. -/
instance inertiaFieldPrime_isPrime
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    (inertiaFieldPrime (K := K) (L := L) G P).IsPrime :=
  inferInstance

/-- The top prime lies over its contraction to the inertia field. -/
instance inertiaFieldPrime_liesOver
    (P : Ideal (𝓞 L)) :
    P.LiesOver (inertiaFieldPrime (K := K) (L := L) G P) where
  over := rfl

/-- The inertia field has the same underlying field whether viewed over `K`
or over the decomposition field; this instance keeps ring-of-integers
extensions in the tower explicit. -/
instance inertiaFieldAlgebraDecompositionField
    (P : Ideal (𝓞 L)) :
    Algebra (decompositionField (K := K) (L := L) G P)
      (inertiaField (K := K) (L := L) G P) := by
  change
    Algebra (decompositionField (K := K) (L := L) G P)
      (inertiaFieldOverDecompositionField (K := K) (L := L) G P)
  infer_instance

/-- The ring-of-integers tower from the decomposition field through the inertia
field to `L` is scalar-compatible. -/
instance ringOfIntegers_isScalarTower_decomposition_inertia
    (P : Ideal (𝓞 L)) :
    IsScalarTower
      (𝓞 (decompositionField (K := K) (L := L) G P))
      (𝓞 (inertiaField (K := K) (L := L) G P))
      (𝓞 L) := by
  change
    IsScalarTower
      (𝓞 (decompositionField (K := K) (L := L) G P))
      (𝓞 (inertiaFieldOverDecompositionField (K := K) (L := L) G P))
      (𝓞 L)
  infer_instance

/-- The inertia-field contraction lies over the decomposition-field
contraction. -/
instance inertiaFieldPrime_liesOver_decompositionFieldPrime
    (P : Ideal (𝓞 L)) :
    (inertiaFieldPrime (K := K) (L := L) G P).LiesOver
      (decompositionFieldPrime (K := K) (L := L) G P) :=
  Ideal.LiesOver.tower_bot P
    (inertiaFieldPrime (K := K) (L := L) G P)
    (decompositionFieldPrime (K := K) (L := L) G P)

/-- The inertia-field contraction lies over the base contraction. -/
instance inertiaFieldPrime_liesOver_basePrime
    (P : Ideal (𝓞 L)) :
    (inertiaFieldPrime (K := K) (L := L) G P).LiesOver
      (basePrime (K := K) P) :=
  Ideal.LiesOver.tower_bot P
    (inertiaFieldPrime (K := K) (L := L) G P)
    (basePrime (K := K) P)

/-- A prime-decomposition consequence:
the contracted inertia-field prime `P_T` is nonzero for a finite prime `P` of
`O_L`. -/
theorem inertiaFieldPrime_ne_bot
    (P : Ideal (𝓞 L)) [P.IsMaximal] :
    inertiaFieldPrime (K := K) (L := L) G P ≠ ⊥ := by
  exact
    ringOfIntegers_under_ne_bot
      (E := inertiaField (K := K) (L := L) G P) (F := L) P

end Dedekind
end HilbertRamification
