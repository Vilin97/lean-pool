/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteQuotientImage
import LeanPool.OrdvecFormalization.QuotientConstraints

/-!
# Quotient kernels

The kernel of a compression map records its forced identifications.  A target is
safe for that compression exactly when the compression kernel is contained in
the target kernel.
-/

namespace OrdvecFormalization

/-- Kernel relation of a quotient/compression map. -/
def Kernel {Ω Z : Type} (C : Ω → Z) (ω₁ ω₂ : Ω) : Prop :=
  C ω₁ = C ω₂

/-- Target indistinguishability relation. -/
def TargetKernel {Ω A : Type} (target : Ω → A) (ω₁ ω₂ : Ω) : Prop :=
  target ω₁ = target ω₂

/-- The compression kernel is contained in the target kernel. -/
def KernelContainedInTarget {Ω Z A : Type}
    (C : Ω → Z) (target : Ω → A) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, Kernel C ω₁ ω₂ → TargetKernel target ω₁ ω₂

theorem kernelContainedInTarget_iff_fiberInvariant {Ω Z A : Type}
    (C : Ω → Z) (target : Ω → A) :
    KernelContainedInTarget C target ↔ FiberInvariant C target := by
  rfl

/--
Image-quotient factorization is equivalent to constancy on the fibers of the
ambient compression map.
-/
theorem ruleFactorsThrough_image_iff_fiberInvariant {Ω Z A : Type}
    [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (target : Ω → A) :
    RuleFactorsThrough (imageQuotient C) target ↔ FiberInvariant C target := by
  constructor
  · intro hfac ω₁ ω₂ hC
    exact ruleFactorsThrough_fiberInvariant (imageQuotient C) target hfac
      (Subtype.ext hC)
  · intro hinv
    apply fiberInvariant_ruleFactorsThrough_of_surjective
      (imageQuotient C) target (imageQuotient_surjective C)
    intro ω₁ ω₂ hQ
    exact hinv (congrArg Subtype.val hQ)

/--
Image-quotient factorization is equivalent to kernel containment: every
compression collision must also be a target indistinguishability.
-/
theorem ruleFactorsThrough_image_iff_kernelContainedInTarget {Ω Z A : Type}
    [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (target : Ω → A) :
    RuleFactorsThrough (imageQuotient C) target ↔
      KernelContainedInTarget C target := by
  rw [ruleFactorsThrough_image_iff_fiberInvariant,
    kernelContainedInTarget_iff_fiberInvariant]

/-- Kernel containment is enough to build a target rule on the image quotient. -/
theorem ruleFactorsThrough_image_of_kernelContainedInTarget {Ω Z A : Type}
    [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (target : Ω → A)
    (h : KernelContainedInTarget C target) :
    RuleFactorsThrough (imageQuotient C) target :=
  (ruleFactorsThrough_image_iff_kernelContainedInTarget C target).mpr h

/-- Any image-quotient factorized target has kernel containment. -/
theorem kernelContainedInTarget_of_ruleFactorsThrough_image {Ω Z A : Type}
    [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (target : Ω → A)
    (h : RuleFactorsThrough (imageQuotient C) target) :
    KernelContainedInTarget C target :=
  (ruleFactorsThrough_image_iff_kernelContainedInTarget C target).mp h

end OrdvecFormalization
