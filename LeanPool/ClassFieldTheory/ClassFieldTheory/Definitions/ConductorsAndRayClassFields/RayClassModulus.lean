/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.FiniteSupport.Defs
public import Mathlib.Order.Preorder.Finsupp
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization
/-!
# Ray class moduli

A modulus consists of finite-prime exponents and a finite set of real places.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- A real infinite place of a number field. -/
abbrev RayClassRealPlace
    (K : Type u) [Field K] :=
  {v : InfinitePlace K // v.IsReal}

/-- A ray modulus: finite prime exponents together with the real places at
which positivity is imposed. -/
structure RayClassModulus
    (K : Type u) [Field K] [NumberField K] where
  /-- The finite prime-power part. -/
  finitePart : HeightOneSpectrum (𝓞 K) →₀ ℕ
  /-- The selected real places. -/
  infinitePart : Finset (RayClassRealPlace K)

namespace RayClassModulus

/-- Ray moduli are equal when their finite exponents and real-place sets agree. -/
@[ext] theorem ext
    {K : Type u} [Field K] [NumberField K]
    {m n : RayClassModulus K}
    (hfinite : m.finitePart = n.finitePart)
    (hinfinite : m.infinitePart = n.infinitePart) : m = n := by
  cases m
  cases n
  cases hfinite
  cases hinfinite
  rfl

instance {K : Type u} [Field K] [NumberField K] : LE (RayClassModulus K) where
  le m n :=
    m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart

instance {K : Type u} [Field K] [NumberField K] :
    PartialOrder (RayClassModulus K) where
  le_refl m := ⟨le_rfl, fun _ hx => hx⟩
  le_trans _ _ _ hmn hnp :=
    ⟨hmn.1.trans hnp.1, fun _ hx => hnp.2 (hmn.2 hx)⟩
  le_antisymm m n hmn hnm := by
    cases m with
    | mk mfinite minfinite =>
      cases n with
      | mk nfinite ninfinite =>
        have hfinite : mfinite = nfinite :=
          le_antisymm hmn.1 hnm.1
        have hinfinite : minfinite = ninfinite := by
          apply Finset.ext
          intro x
          exact ⟨fun hx => hmn.2 hx, fun hx => hnm.2 hx⟩
        cases hfinite
        cases hinfinite
        rfl

/-- Modulus divisibility is exponentwise at finite primes and inclusion at
real places. -/
@[simp] theorem le_iff
    {K : Type u} [Field K] [NumberField K]
    (m n : RayClassModulus K) :
    m ≤ n ↔
      (∀ v, m.finitePart v ≤ n.finitePart v) ∧
        m.infinitePart ⊆ n.infinitePart := by
  rfl

/-- Meet takes the minimum finite-prime exponent and intersects the real
places; join takes the maximum exponent and unions the real places. -/
instance {K : Type u} [Field K] [NumberField K] :
    Lattice (RayClassModulus K) := by
  classical
  exact {
    inf := fun m n =>
      ⟨m.finitePart ⊓ n.finitePart, m.infinitePart ∩ n.infinitePart⟩
    inf_le_left := fun _ _ => ⟨inf_le_left, Finset.inter_subset_left⟩
    inf_le_right := fun _ _ => ⟨inf_le_right, Finset.inter_subset_right⟩
    le_inf := fun _ _ _ hmn hmp =>
      ⟨le_inf hmn.1 hmp.1, Finset.subset_inter hmn.2 hmp.2⟩
    sup := fun m n =>
      ⟨m.finitePart ⊔ n.finitePart, m.infinitePart ∪ n.infinitePart⟩
    le_sup_left := fun _ _ => ⟨le_sup_left, Finset.subset_union_left⟩
    le_sup_right := fun _ _ => ⟨le_sup_right, Finset.subset_union_right⟩
    sup_le := fun _ _ _ hmp hnp =>
      ⟨sup_le hmp.1 hnp.1, Finset.union_subset hmp.2 hnp.2⟩
  }

@[simp] theorem finitePart_inf
    {K : Type u} [Field K] [NumberField K]
    (m n : RayClassModulus K) :
    (m ⊓ n).finitePart = m.finitePart ⊓ n.finitePart := rfl

@[simp] theorem mem_infinitePart_inf
    {K : Type u} [Field K] [NumberField K]
    (m n : RayClassModulus K) (v : RayClassRealPlace K) :
    v ∈ (m ⊓ n).infinitePart ↔
      v ∈ m.infinitePart ∧ v ∈ n.infinitePart := by
  classical
  change v ∈ m.infinitePart ∩ n.infinitePart ↔ _
  exact Finset.mem_inter

@[simp] theorem finitePart_sup
    {K : Type u} [Field K] [NumberField K]
    (m n : RayClassModulus K) :
    (m ⊔ n).finitePart = m.finitePart ⊔ n.finitePart := rfl

@[simp] theorem mem_infinitePart_sup
    {K : Type u} [Field K] [NumberField K]
    (m n : RayClassModulus K) (v : RayClassRealPlace K) :
    v ∈ (m ⊔ n).infinitePart ↔
      v ∈ m.infinitePart ∨ v ∈ n.infinitePart := by
  classical
  change v ∈ m.infinitePart ∪ n.infinitePart ↔ _
  exact Finset.mem_union

end RayClassModulus

end ClassFieldTheory
