/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.Final
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.RayClassComparison
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.Setup
public import LeanPool.ClassFieldTheory.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport
/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

@[expose] public section

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
