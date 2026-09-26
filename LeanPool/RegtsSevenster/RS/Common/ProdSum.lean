/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Sums through linear maps and into a product

Two small families used wherever a coordinate computation pushes a
finite sum through a bound map and then splits it across the
summands of a product: `map_sum`/`map_zero` at a bound linear map
or equivalence, and the four ways a sum can sit in `A × B`.

They are stated for bound maps because `simp` will not otherwise
rewrite under a `LinearMap` applied to a `Finset.sum`, and they
live here rather than beside their first user because two files
need them.
-/

@[expose] public section

namespace RS

variable {M N A B ι κ : Type*}

section Maps

/-- `map_sum` for a bound linear equivalence. -/
lemma equiv_sum [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) (s : Finset ι) (f : ι → M) :
    e (∑ i ∈ s, f i) = ∑ i ∈ s, e (f i) :=
  map_sum e f s

/-- `map_add` for a bound linear equivalence. -/
lemma equiv_add [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    (e : M ≃ₗ[ℂ] N) (x y : M) : e (x + y) = e x + e y :=
  map_add e x y

/-- `map_sum` for a bound linear map. -/
lemma lmap_sum [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) (s : Finset ι) (g : ι → M) :
    f (∑ i ∈ s, g i) = ∑ i ∈ s, f (g i) :=
  map_sum f g s

/-- `map_zero` for a bound linear map. -/
lemma lmap_zero [AddCommMonoid M] [Module ℂ M] [AddCommMonoid N] [Module ℂ N]
    (f : M →ₗ[ℂ] N) : f 0 = 0 :=
  map_zero f

end Maps

section Prod

/-- Addition in the left summand of a product. -/
lemma mk_add_left [AddCommMonoid A] [AddCommMonoid B]
    (a a' : A) :
    ((a + a', (0 : B)) : A × B) = (a, 0) + (a', 0) := by
  refine Prod.ext ?_ ?_ <;> simp

/-- Addition in the right summand. -/
lemma mk_add_right [AddCommMonoid A] [AddCommMonoid B]
    (b b' : B) :
    (((0 : A), b + b') : A × B) = (0, b) + (0, b') := by
  refine Prod.ext ?_ ?_ <;> simp

/-- A sum in the left summand. -/
lemma mk_sum_left [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (f : ι → A) :
    ((∑ i ∈ s, f i, (0 : B)) : A × B) = ∑ i ∈ s, ((f i, 0) : A × B) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- A sum in the right summand. -/
lemma mk_sum_right [AddCommMonoid A] [AddCommMonoid B]
    (t : Finset ι) (g : ι → B) :
    (((0 : A), ∑ j ∈ t, g j) : A × B) = ∑ j ∈ t, ((0, g j) : A × B) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]

/-- A pair of sums splits into the two summands' sums — the shape
the even and odd blocks are computed in. -/
lemma mk_sum_split [AddCommMonoid A] [AddCommMonoid B]
    (s : Finset ι) (t : Finset κ) (f : ι → A) (g : κ → B) :
    ((∑ i ∈ s, f i, ∑ j ∈ t, g j) : A × B) =
      (∑ i ∈ s, ((f i, 0) : A × B)) + ∑ j ∈ t, ((0, g j) : A × B) := by
  refine Prod.ext ?_ ?_ <;> simp [Prod.fst_sum, Prod.snd_sum]

end Prod

end RS
