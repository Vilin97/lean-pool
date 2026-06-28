/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import LeanPool.OrdvecFormalization.FiniteQuotientSearch

/-!
# Finite quotient images

This file keeps quotient reasoning on the actually reachable image of a finite
compression map.  For an encoder/corpus map `C : Ω → Z`, the image quotient is
surjective by construction, without assuming that `C` reaches the whole
ambient codomain `Z`.
-/

namespace OrdvecFormalization

/-- The finite image of a quotient/compression map. -/
abbrev QuotientImage {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) : Type :=
  QuotientImageBucket C

/-- The quotient map whose codomain is restricted to the actual finite image. -/
def imageQuotient {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) : Ω → QuotientImage C :=
  fun ω => ⟨C ω, Finset.mem_image.mpr ⟨ω, Finset.mem_univ ω, rfl⟩⟩

@[simp]
theorem imageQuotient_val {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (ω : Ω) :
    (imageQuotient C ω).1 = C ω := rfl

/-- The image quotient is surjective onto the reachable quotient image. -/
theorem imageQuotient_surjective {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) :
    Function.Surjective (imageQuotient C) := by
  intro z
  rcases Finset.mem_image.mp z.2 with ⟨ω, _hω, hω⟩
  exact ⟨ω, Subtype.ext hω⟩

/-- The full fiber over an ambient quotient bucket. -/
def Fiber {Ω Z : Type} (C : Ω → Z) (z : Z) : Set Ω :=
  {ω | C ω = z}

/-- The full fiber over a reachable image bucket. -/
def ImageFiber {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (z : QuotientImage C) : Set Ω :=
  {ω | imageQuotient C ω = z}

/-- The quotient buckets observed in a finite sample. -/
abbrev ObservedBuckets {Ω Z : Type} [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) : Finset Z :=
  ObservedQuotients C sample

/-- Reachable quotient buckets that have not appeared in a finite sample. -/
def UnobservedBuckets {Ω Z : Type} [Fintype Ω] [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) : Finset Z :=
  QuotientImageFinset C \ ObservedBuckets C sample

/-- Number of sampled observations in a quotient bucket. -/
def FiberSize {Ω Z : Type} [DecidableEq Z]
    (C : Ω → Z) (sample : Finset Ω) (z : Z) : ℕ :=
  (sample.filter fun ω => C ω = z).card

/-- Two sampled observations collide when they are distinct but share a bucket. -/
def HasCollision {Ω Z : Type}
    (C : Ω → Z) (sample : Finset Ω) : Prop :=
  ∃ ω₁ ω₂ : Ω, ω₁ ∈ sample ∧ ω₂ ∈ sample ∧ ω₁ ≠ ω₂ ∧ C ω₁ = C ω₂

/-- Injectivity restricted to a finite sample. -/
def InjectiveOnSample {Ω Z : Type}
    (C : Ω → Z) (sample : Finset Ω) : Prop :=
  ∀ ⦃ω₁ ω₂ : Ω⦄, ω₁ ∈ sample → ω₂ ∈ sample → C ω₁ = C ω₂ → ω₁ = ω₂

end OrdvecFormalization
