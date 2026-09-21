/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Basic.Denumerable
/-!
# Topological structure of local-field units: reindexing the Iwasawa product

The equal-characteristic proof naturally indexes copies of `ℤ_[p]` by a
positive integer prime to `p` and a residue-field basis vector.  This file
records that, when the basis is nonempty, this is exactly a countable product.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField

/-- Positive degrees prime to `p`, as used in the Iwasawa product. -/
def IwasawaDegree (p : ℕ) := {n : ℕ // 1 ≤ n ∧ Nat.Coprime n p}

/-- A prime-to-`p` degree together with a residue-field basis coordinate. -/
abbrev IwasawaIndex (p f : ℕ) := IwasawaDegree p × Fin f

/-- The degrees `1 + pk` give an infinite sequence of pairwise distinct
positive degrees prime to `p`. -/
def iwasawaDegreeEmbedding (p : ℕ) (hp : 0 < p) : ℕ ↪ IwasawaDegree p where
  toFun k :=
    ⟨1 + p * k, by
      constructor
      · omega
      · exact (Nat.coprime_add_mul_left_left 1 p k).2 (by simp)⟩
  inj' := by
    intro a b h
    have hv : 1 + p * a = 1 + p * b := congrArg Subtype.val h
    apply Nat.mul_left_cancel hp
    exact Nat.add_left_cancel hv

/-- The Iwasawa index is infinite as soon as the finite basis has a vector. -/
theorem infinite_iwasawaIndex (p f : ℕ) (hp : 0 < p) (hf : 0 < f) :
    Infinite (IwasawaIndex p f) := by
  let j : ℕ ↪ IwasawaIndex p f :=
    { toFun := fun k => (iwasawaDegreeEmbedding p hp k, ⟨0, hf⟩)
      inj' := by
        intro a b h
        exact (iwasawaDegreeEmbedding p hp).injective
          (congrArg (fun z : IwasawaIndex p f => z.1) h) }
  exact Infinite.of_injective j j.injective

/-- The index used in the equal-characteristic proof is denumerable. -/
noncomputable def chosenIwasawaIndexEquivNat (p f : ℕ) (hp : 0 < p) (hf : 0 < f) :
    IwasawaIndex p f ≃ ℕ := by
  letI : Infinite (IwasawaIndex p f) := infinite_iwasawaIndex p f hp hf
  letI : Countable (IwasawaDegree p) := by
    unfold IwasawaDegree
    infer_instance
  letI : Countable (IwasawaIndex p f) := by
    change Countable (IwasawaDegree p × Fin f)
    infer_instance
  let d : Denumerable (IwasawaIndex p f) :=
    Classical.choice (nonempty_denumerable (IwasawaIndex p f))
  exact @Denumerable.eqv (IwasawaIndex p f) d

/-- Reindexing the Iwasawa product gives the canonical
`ℤ_[p]^ℕ`, both algebraically and topologically. -/
noncomputable def iwasawaPadicIntProductContinuousAddEquivNat
    (p f : ℕ) [Fact p.Prime] (hp : 0 < p) (hf : 0 < f) :
    (IwasawaIndex p f → ℤ_[p]) ≃ₜ+ (ℕ → ℤ_[p]) := by
  let e := chosenIwasawaIndexEquivNat p f hp hf
  exact ContinuousAddEquiv.mk'
    (Homeomorph.piCongrLeft (Y := fun _ : ℕ => ℤ_[p]) e)
    (by
      intro x y
      apply funext
      intro j
      obtain ⟨i, rfl⟩ := e.surjective j
      simp)

end LocalFieldTheory.DiscreteValuationField
