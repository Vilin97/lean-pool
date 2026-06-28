/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.QuotientKernel

/-!
# Quotient refinement via kernels

Refinement can be read as a kernel inclusion statement: finer quotients have
smaller fibers and therefore force fewer identifications.  The converse is
cleanest when the fine quotient is surjective, which is automatic for an image
quotient.
-/

namespace OrdvecFormalization

/-- A refinement makes fine-kernel collisions coarse-kernel collisions. -/
theorem quotientRefines_kernel_subset {Ω Zfine Zcoarse : Type}
    {Qfine : Ω → Zfine} {Qcoarse : Ω → Zcoarse}
    (href : QuotientRefines Qfine Qcoarse) :
    ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel Qfine ω₁ ω₂ → Kernel Qcoarse ω₁ ω₂ := by
  rcases href with ⟨f, hf⟩
  intro ω₁ ω₂ hfine
  unfold Kernel at hfine ⊢
  rw [hf ω₁, hf ω₂, hfine]

/-- Kernel inclusion builds a refinement when the fine quotient is surjective. -/
theorem quotientRefines_of_surjective_of_kernel_subset {Ω Zfine Zcoarse : Type}
    (Qfine : Ω → Zfine) (Qcoarse : Ω → Zcoarse)
    (hsurj : Function.Surjective Qfine)
    (hker : ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel Qfine ω₁ ω₂ → Kernel Qcoarse ω₁ ω₂) :
    QuotientRefines Qfine Qcoarse := by
  classical
  refine ⟨fun z => Qcoarse (Classical.choose (hsurj z)), ?_⟩
  intro ω
  have hrep : Qfine (Classical.choose (hsurj (Qfine ω))) = Qfine ω :=
    Classical.choose_spec (hsurj (Qfine ω))
  exact (hker hrep).symm

/-- For surjective fine quotients, refinement is exactly kernel inclusion. -/
theorem quotientRefines_iff_kernel_subset_of_surjective {Ω Zfine Zcoarse : Type}
    (Qfine : Ω → Zfine) (Qcoarse : Ω → Zcoarse)
    (hsurj : Function.Surjective Qfine) :
    QuotientRefines Qfine Qcoarse ↔
      ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel Qfine ω₁ ω₂ → Kernel Qcoarse ω₁ ω₂ := by
  constructor
  · exact quotientRefines_kernel_subset
  · exact quotientRefines_of_surjective_of_kernel_subset Qfine Qcoarse hsurj

/--
The image quotient of a fine map refines a coarse map exactly when fine-kernel
collisions imply coarse-kernel collisions.
-/
theorem imageQuotient_refines_iff_kernel_subset {Ω Zfine Zcoarse : Type}
    [Fintype Ω] [DecidableEq Zfine]
    (Qfine : Ω → Zfine) (Qcoarse : Ω → Zcoarse) :
    QuotientRefines (imageQuotient Qfine) Qcoarse ↔
      ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel Qfine ω₁ ω₂ → Kernel Qcoarse ω₁ ω₂ := by
  rw [quotientRefines_iff_kernel_subset_of_surjective
    (imageQuotient Qfine) Qcoarse (imageQuotient_surjective Qfine)]
  constructor
  · intro hker ω₁ ω₂ hfine
    exact hker (Subtype.ext hfine)
  · intro hker ω₁ ω₂ hfine
    exact hker (congrArg Subtype.val hfine)

/-- Kernel inclusion gives a concrete refinement from the fine image quotient. -/
theorem imageQuotient_refines_of_kernel_subset {Ω Zfine Zcoarse : Type}
    [Fintype Ω] [DecidableEq Zfine]
    (Qfine : Ω → Zfine) (Qcoarse : Ω → Zcoarse)
    (hker : ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel Qfine ω₁ ω₂ → Kernel Qcoarse ω₁ ω₂) :
    QuotientRefines (imageQuotient Qfine) Qcoarse :=
  (imageQuotient_refines_iff_kernel_subset Qfine Qcoarse).mpr hker

end OrdvecFormalization
