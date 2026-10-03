/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassOfFinitePrime
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.FinitePrimeSplitsCompletely
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.FrobeniusAndHilbertClassFields.IsBigHilbertClassField
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.ConductorsAndRayClassFields.RayPrincipalIdealMembership
public import LeanPool.ClassFieldTheory.ClassFieldTheory.Theorems.FrobeniusAndHilbertClassFields.BigHilbertClassFieldPrimeSplitting
/-!
# Totally positive principal primes and splitting

A finite prime splits completely in the big Hilbert class field exactly
when its fractional ideal has a totally positive generator.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable
section

namespace ClassFieldTheory

open scoped Classical in
/-- Equivalently, a prime splits completely in the big Hilbert class field
exactly when it has a totally positive generator. -/
theorem finitePrime_splitsCompletelyInBigHilbertClassField_iff_positivePrincipal
    (K : Type) [Field K] [NumberField K]
    (E : FiniteAbelianExtension K) (hE : IsBigHilbertClassField E)
    (v : HeightOneSpectrum (𝓞 K)) :
    FinitePrimeSplitsCompletely K E v ↔
      ∃ x : Kˣ,
        (∀ w : RayClassRealPlace K,
          0 < w.1.embedding_of_isReal w.2 (x : K)) ∧
        toPrincipalIdeal (𝓞 K) K x = finitePrimeFractionalIdeal v := by
  rw [finitePrime_splitsCompletelyInBigHilbertClassField_iff K E hE v]
  change ((⟨finitePrimeFractionalIdeal v, _⟩ :
    rayClassPrimeToIdeals (narrowRayClassModulus K)) :
      RayClassGroup (narrowRayClassModulus K)) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  change finitePrimeFractionalIdeal v ∈
    rayPrincipalIdealSubgroup (narrowRayClassModulus K) ↔ _
  rw [mem_rayPrincipalIdealSubgroup_iff]
  simp [IsRayCongruent, narrowRayClassModulus]

end ClassFieldTheory
