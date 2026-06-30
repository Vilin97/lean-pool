/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.Definition63
import LeanPool.DomainTheory.Neighborhood.Theorem69
import LeanPool.DomainTheory.Neighborhood.Example62C
import LeanPool.DomainTheory.Neighborhood.Exercise516

/-!
# Exercise 6.17 (Scott 1981, PRG-19, §6) — the algebras for which `C` is initial

> **EXERCISE 6.17.** What are the algebras for which `C` is initial? If `A` of 6.2
is a generalization
> of `B`, what is the corresponding generalization of `C`? Prove that it exists
and explain what are
> the algebras involved.

`C` (Example 4.4: finite-or-infinite binary sequences) satisfies the domain
equation
`C ≅ {{Λ}} + C + C` (Example 6.2, `Example62C.lean`). So `C` is a solution of the
domain equation for
the functor

`T(X) = 𝟙 + X + X`   (one terminator + two successor copies).

This module proves that **`C` is the *initial* `T`-algebra**: for every
`T`-algebra `(E, k)` there is a
*unique* homomorphism `C → E`. Concretely a `T`-algebra is a strict map `k : 𝟙 + E
+ E → E`, which by
the universal property of the separated sum is the same data as

* a distinguished element `e ∈ |E|` (the image of the terminator `𝟙`), and
* two strict endomaps `f₀, f₁ : E → E` (the two successor branches);

so **the algebras for which `C` is initial are the domains carrying a point and
two strict unary
operations**, and the unique homomorphism `C → E` interprets a finite-or-infinite
binary sequence
`b₀b₁b₂…` as `f_{b₀}(f_{b₁}(… e …))`.

## Why a bespoke category of `∅`-free domains

Scott's separated sum `𝒟₀ + 𝒟₁` (Exercise 3.18) is a neighbourhood system **only**
under the standing
assumption `∅ ∉ 𝒟` (an empty neighbourhood of one summand would become a spurious
consistency witness
for the other tag, breaking `inter_mem`). Consequently the functor `T(X) = 𝟙 + X +
X` does **not**
extend to a total endofunctor of the all-systems category `DomainObj`, and the
existence Theorem 6.14
(stated over `DomainObj`) cannot be instantiated directly.

Following Scott — who restricts to the category of `∅`-free systems and *strict*
maps in Exercise 6.19
— we instantiate the abstract categorical vocabulary (Definitions 6.3–6.5) on the
bespoke object type
`StrictDomainObj` of neighbourhood systems with **no empty neighbourhood**, with
**strict approximable
maps** as morphisms. The functor `T` then reuses the existing `sum3` (Example 6.2,
the genuine
three-way separated sum) and a three-way sum map, and initiality of `C` is proved
**directly** (we
construct the homomorphism and prove its uniqueness by the finite-approximant
argument), rather than
routing through the colimit construction of Theorem 6.14.

Everything is choice-free where it is data; the homomorphism/uniqueness layer
reuses the project's
established machinery.
-/

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Domain.Neighborhood.Exercise510

universe w

/-! ## The category of `∅`-free domains and strict maps -/

/-- An object of Scott's category (Exercise 6.19): a token type, a neighbourhood
system on it,
and the
standing assumption `∅ ∉ 𝒟` (every neighbourhood is non-empty). -/
structure StrictDomainObj : Type (w + 1) where
  /-- The token type. -/
  carrier : Type w
  /-- The neighbourhood system. -/
  sys : NeighborhoodSystem carrier
  /-- Scott's standing assumption `∅ ∉ 𝒟`. -/
  nonempty : ∀ X, sys.mem X → X.Nonempty

/-- **The category of `∅`-free domains and strict maps.** Morphisms are strict
approximable maps
(`StrictMap`, Exercise 5.10); identities and associative composition come from
Theorem 2.5, and
strictness is preserved by `isStrict_idMap` / `isStrict_comp`. -/
instance : Category StrictDomainObj where
  Hom D E := StrictMap D.sys E.sys
  id D := ⟨ApproximableMap.idMap D.sys, isStrict_idMap⟩
  comp g f := ⟨g.1.comp f.1, isStrict_comp g.2 f.2⟩
  id_comp f := Subtype.ext (ApproximableMap.idMap_comp f.1)
  comp_id f := Subtype.ext (ApproximableMap.comp_idMap f.1)
  assoc h g f := Subtype.ext (ApproximableMap.comp_assoc h.1 g.1 f.1)

@[simp] theorem StrictDomainObj.id_val (D : StrictDomainObj) :
    (Category.id D : StrictMap D.sys D.sys).1 = ApproximableMap.idMap D.sys := rfl

@[simp] theorem StrictDomainObj.comp_val {D E F : StrictDomainObj}
    (g : Category.Hom E F) (f : Category.Hom D E) :
    ((g ⊚ f : StrictMap D.sys F.sys)).1 = g.1.comp f.1 := rfl

/-! ## The functor `T(X) = 𝟙 + X + X` on objects -/

open Example62C in
/-- Every neighbourhood of the three-way separated sum `sum3` is non-empty (so
`sum3` is again an
object of the `∅`-free category). -/
theorem sum3_nonempty {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
    {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty} :
    ∀ W, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W → W.Nonempty := by
  rintro W (rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩)
  · exact ⟨none, none_mem_master3⟩
  · exact j0_nonempty (h₀ X hX)
  · exact j1_nonempty (h₁ Y hY)
  · exact j2_nonempty (h₂ Z hZ)

/-- **The functor `T(X) = 𝟙 + X + X` on objects.** Over `D`, the system is the
genuine three-way
separated sum `𝟙 + D + D` (Example 6.2's `sum3`, with `𝟙 = unitSys`), again
`∅`-free by
`sum3_nonempty`. -/
def tcObj (D : StrictDomainObj.{w}) : StrictDomainObj.{w} where
  carrier := Option (Unit ⊕ D.carrier ⊕ D.carrier)
  sys := sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty
  nonempty := sum3_nonempty

@[simp] theorem tcObj_sys (D : StrictDomainObj.{w}) :
    (tcObj D).sys =
      sum3 unitSys D.sys D.sys Example62C.unitSys_nonempty D.nonempty D.nonempty := rfl

/-! ### Membership-shape lemmas for `sum3` (no nesting through the wrong tag) -/

section ShapeLemmas

open Example62C

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ} {h₀ : ∀ X, V₀.mem X → X.Nonempty}
  {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty} {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- A `sum3`-neighbourhood contained in a `0`-copy `0X` is itself a `0`-copy. -/
theorem mem_subset_j0_inv {W : Set (Option (α ⊕ β ⊕ γ))} {X : Set α}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j0 X) :
    ∃ X₂, V₀.mem X₂ ∧ W = j0 X₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j0
  · exact ⟨X₂, hX₂, rfl⟩
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0

/-- A `sum3`-neighbourhood contained in a `1`-copy `1Y` is itself a `1`-copy. -/
theorem mem_subset_j1_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Y : Set β}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j1 Y) :
    ∃ Y₂, V₁.mem Y₂ ∧ W = j1 Y₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j1
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
  · exact ⟨Y₂, hY₂, rfl⟩
  · obtain ⟨c, hc⟩ := h₂ Z₂ hZ₂; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1

/-- A `sum3`-neighbourhood contained in a `2`-copy `2Z` is itself a `2`-copy. -/
theorem mem_subset_j2_inv {W : Set (Option (α ⊕ β ⊕ γ))} {Z : Set γ}
    (hW : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W) (hsub : W ⊆ j2 Z) :
    ∃ Z₂, V₂.mem Z₂ ∧ W = j2 Z₂ := by
  rcases hW with rfl | ⟨X₂, hX₂, rfl⟩ | ⟨Y₂, hY₂, rfl⟩ | ⟨Z₂, hZ₂, rfl⟩
  · exact absurd (hsub none_mem_master3) none_not_mem_j2
  · obtain ⟨a, ha⟩ := h₀ X₂ hX₂; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
  · obtain ⟨b, hb⟩ := h₁ Y₂ hY₂; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
  · exact ⟨Z₂, hZ₂, rfl⟩

end ShapeLemmas

/-! ### The three-way sum map `f₀ + f₁ + f₂` -/

section SumMap3

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

/-- **The three-way sum map `f₀ + f₁ + f₂ : 𝒟₀+𝒟₁+𝒟₂ → 𝒟₀'+𝒟₁'+𝒟₂'`.** Routes each
tagged copy `iX`
through `fᵢ` (to `iYᵢ'`), and sends everything to the codomain master. (The
three-way analogue of
Exercise 3.19's `sumMap`.) -/
def sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    ApproximableMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) (sum3 V₀' V₁' V₂' h₀' h₁' h₂') where
  rel W W' := (sum3 V₀ V₁ V₂ h₀ h₁ h₂).mem W ∧ (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W' ∧
    (W' = master3 V₀' V₁' V₂' ∨
      (∃ X Y', W = j0 X ∧ W' = j0 Y' ∧ f₀.rel X Y') ∨
      (∃ X Y', W = j1 X ∧ W' = j1 Y' ∧ f₁.rel X Y') ∨
      (∃ X Y', W = j2 X ∧ W' = j2 Y' ∧ f₂.rel X Y'))
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨(sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem,
    Or.inl rfl⟩
  inter_right := by
    rintro W W'₁ W'₂ ⟨hW, hW'₁, hd₁⟩ ⟨_, hW'₂, hd₂⟩
    have hmem : ∀ W'' : Set (Option (α' ⊕ β' ⊕ γ')),
        (W'' = master3 V₀' V₁' V₂' ∨
          (∃ X Y', W = j0 X ∧ W'' = j0 Y' ∧ f₀.rel X Y') ∨
          (∃ X Y', W = j1 X ∧ W'' = j1 Y' ∧ f₁.rel X Y') ∨
          (∃ X Y', W = j2 X ∧ W'' = j2 Y' ∧ f₂.rel X Y')) →
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').mem W'' := by
      rintro W'' (rfl | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩ | ⟨_, Y', _, rfl, hf⟩)
      · exact (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem
      · exact Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩))
    have key : (W'₁ ∩ W'₂ = master3 V₀' V₁' V₂' ∨
        (∃ X Y', W = j0 X ∧ W'₁ ∩ W'₂ = j0 Y' ∧ f₀.rel X Y') ∨
        (∃ X Y', W = j1 X ∧ W'₁ ∩ W'₂ = j1 Y' ∧ f₁.rel X Y') ∨
        (∃ X Y', W = j2 X ∧ W'₁ ∩ W'₂ = j2 Y' ∧ f₂.rel X Y')) := by
      rcases hd₁ with rfl | ⟨X, Y'₁, hWX₁, rfl, hf₁⟩ | ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩
        | ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩
      · rw [Set.inter_eq_right.mpr (show W'₂ ⊆ master3 V₀' V₁' V₂' from
          (sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂)]; exact hd₂
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j0_subset_master3 (f₀.rel_cod hf₁))]
          exact Or.inr (Or.inl ⟨X, Y'₁, hWX₁, rfl, hf₁⟩)
        · obtain rfl : X = X' := j0_injective (hWX₁.symm.trans hWX₂)
          rw [j0_inter_j0]
          exact Or.inr (Or.inl ⟨X, Y'₁ ∩ Y'₂, hWX₁, rfl, f₀.inter_right hf₁ hf₂⟩)
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWY₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
        · obtain ⟨a, ha⟩ := h₀ X (f₀.rel_dom hf₁)
          exact absurd ((hWX₁.symm.trans hWZ₂) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j1_subset_master3 (f₁.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁, hWY₁, rfl, hf₁⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWX₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
        · obtain rfl : Y = Y' := j1_injective (hWY₁.symm.trans hWY₂)
          rw [j1_inter_j1]
          exact Or.inr (Or.inr (Or.inl ⟨Y, Y'₁ ∩ Y'₂, hWY₁, rfl, f₁.inter_right hf₁ hf₂⟩))
        · obtain ⟨b, hb⟩ := h₁ Y (f₁.rel_dom hf₁)
          exact absurd ((hWY₁.symm.trans hWZ₂) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · rcases hd₂ with rfl | ⟨X', Y'₂, hWX₂, rfl, hf₂⟩ | ⟨Y', Y'₂, hWY₂, rfl, hf₂⟩
          | ⟨Z', Y'₂, hWZ₂, rfl, hf₂⟩
        · rw [Set.inter_eq_left.mpr (j2_subset_master3 (f₂.rel_cod hf₁))]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁, hWZ₁, rfl, hf₁⟩))
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWX₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
        · obtain ⟨c, hc⟩ := h₂ Z (f₂.rel_dom hf₁)
          exact absurd ((hWZ₁.symm.trans hWY₂) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
        · obtain rfl : Z = Z' := j2_injective (hWZ₁.symm.trans hWZ₂)
          rw [j2_inter_j2]
          exact Or.inr (Or.inr (Or.inr ⟨Z, Y'₁ ∩ Y'₂, hWZ₁, rfl, f₂.inter_right hf₁ hf₂⟩))
    exact ⟨hW, hmem _ key, key⟩
  mono := by
    rintro W W₂ W' W'₂ ⟨hW, hW', hd⟩ hW₂W hW'W'₂ hW₂mem hW'₂mem
    refine ⟨hW₂mem, hW'₂mem, ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, hf⟩ | ⟨Y, Y', rfl, rfl, hf⟩ | ⟨Z, Y', rfl, rfl, hf⟩
    · exact Or.inl (eq_master3_of_subset hW'W'₂ ((sum3 V₀' V₁' V₂' h₀' h₁' h₂').sub_master hW'₂mem))
    · obtain ⟨X₂, hX₂, rfl⟩ := mem_subset_j0_inv hW₂mem hW₂W
      have hX₂X : X₂ ⊆ X := j0_subset_j0.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X₂, Y'₂, rfl, rfl,
          f₀.mono hf hX₂X (j0_subset_j0.mp hW'W'₂) hX₂ hY'₂⟩)
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y' (f₀.rel_cod hf)
        exact absurd (hW'W'₂ (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · obtain ⟨Y₂, hY₂, rfl⟩ := mem_subset_j1_inv hW₂mem hW₂W
      have hY₂Y : Y₂ ⊆ Y := j1_subset_j1.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y₂, Y'₂, rfl, rfl,
          f₁.mono hf hY₂Y (j1_subset_j1.mp hW'W'₂) hY₂ hY'₂⟩))
      · obtain ⟨b, hb⟩ := h₁' Y' (f₁.rel_cod hf)
        exact absurd (hW'W'₂ (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · obtain ⟨Z₂, hZ₂, rfl⟩ := mem_subset_j2_inv hW₂mem hW₂W
      have hZ₂Z : Z₂ ⊆ Z := j2_subset_j2.mp hW₂W
      rcases hW'₂mem with rfl | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩ | ⟨Y'₂, hY'₂, rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y' (f₂.rel_cod hf)
        exact absurd (hW'W'₂ (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z₂, Y'₂, rfl, rfl,
          f₂.mono hf hZ₂Z (j2_subset_j2.mp hW'W'₂) hZ₂ hY'₂⟩))

/-- The three-way sum map is always strict: `(f₀+f₁+f₂)(⊥) = ⊥`. (The master only
relates to the
master, since `master3` is not any tagged copy.) -/
theorem isStrict_sumMap3 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') :
    IsStrict (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
      f₀ f₁ f₂) := by
  rintro Y ⟨-, -, hd⟩
  have h0 : (none : Option (α ⊕ β ⊕ γ)) ∈ (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master := none_mem_master3
  rcases hd with rfl | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩ | ⟨X, Y', hWX, -, -⟩
  · rfl
  · exact absurd (hWX ▸ h0) none_not_mem_j0
  · exact absurd (hWX ▸ h0) none_not_mem_j1
  · exact absurd (hWX ▸ h0) none_not_mem_j2

/-- **Functoriality (identities): `I + I + I = I`.** -/
theorem sumMap3_id :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀) (h₁' := h₁) (h₂' := h₂)
      (idMap V₀) (idMap V₁) (idMap V₂) = idMap (sum3 V₀ V₁ V₂ h₀ h₁ h₂) := by
  apply ApproximableMap.ext
  intro W W'
  constructor
  · rintro ⟨hW, hW', hd⟩
    refine ⟨hW, hW', ?_⟩
    rcases hd with rfl | ⟨X, Y', rfl, rfl, _, _, hXY⟩ | ⟨Y, Y', rfl, rfl, _, _, hXY⟩
      | ⟨Z, Y', rfl, rfl, _, _, hXY⟩
    · exact (sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW
    · exact j0_subset_j0.mpr hXY
    · exact j1_subset_j1.mpr hXY
    · exact j2_subset_j2.mpr hXY
  · rintro ⟨hW, hW', hsub⟩
    refine ⟨hW, hW', ?_⟩
    rcases hW with rfl | ⟨X, hX, rfl⟩ | ⟨Y, hY, rfl⟩ | ⟨Z, hZ, rfl⟩
    · left; exact eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW')
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨X, X', rfl, rfl, hX, hX', j0_subset_j0.mp hsub⟩)
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X hX; exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hY, hY', j1_subset_j1.mp hsub⟩))
      · obtain ⟨b, hb⟩ := h₁ Y hY; exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z hZ; exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr (Or.inr (Or.inr ⟨Z, Z', rfl, rfl, hZ, hZ', j2_subset_j2.mp hsub⟩))

/-- **Functoriality (composition): `(g₀∘f₀) + (g₁∘f₁) + (g₂∘f₂) = (g₀+g₁+g₂) ∘
(f₀+f₁+f₂)`.** -/
theorem sumMap3_comp {α'' β'' γ'' : Type*} {V₀'' : NeighborhoodSystem α''}
    {V₁'' : NeighborhoodSystem β''} {V₂'' : NeighborhoodSystem γ''}
    {h₀'' : ∀ X, V₀''.mem X → X.Nonempty} {h₁'' : ∀ Y, V₁''.mem Y → Y.Nonempty}
    {h₂'' : ∀ Z, V₂''.mem Z → Z.Nonempty}
    (g₀ : ApproximableMap V₀' V₀'') (g₁ : ApproximableMap V₁' V₁'') (g₂ : ApproximableMap V₂' V₂'')
    (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁') (f₂ : ApproximableMap V₂ V₂') :
    sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
        (g₀.comp f₀) (g₁.comp f₁) (g₂.comp f₂)
      = (sumMap3 (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (h₀' := h₀'') (h₁' := h₁'') (h₂' := h₂'')
          g₀ g₁ g₂).comp
        (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (h₂' := h₂')
          f₀ f₁ f₂) := by
  apply ApproximableMap.ext
  intro W W''
  constructor
  · rintro ⟨hW, hW'', hd⟩
    rcases hd with rfl | ⟨X, Z'', rfl, rfl, Y', hf, hg⟩ | ⟨Y, Z'', rfl, rfl, Y', hf, hg⟩
      | ⟨Z, Z'', rfl, rfl, Y', hf, hg⟩
    · exact ⟨master3 V₀' V₁' V₂', ⟨hW, (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, hW'', Or.inl rfl⟩
    · exact ⟨j0 Y', ⟨hW, Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩),
        Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩,
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), hW'', Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩)⟩
    · exact ⟨j1 Y', ⟨hW, Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inl ⟨Y', Z'', rfl, rfl, hg⟩))⟩
    · exact ⟨j2 Y', ⟨hW, Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Z, Y', rfl, rfl, hf⟩))⟩,
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), hW'',
        Or.inr (Or.inr (Or.inr ⟨Y', Z'', rfl, rfl, hg⟩))⟩
  · rintro ⟨W', ⟨hW, hW', hdf⟩, _, hW'', hdg⟩
    refine ⟨hW, hW'', ?_⟩
    rcases hdg with rfl | ⟨X', Z'', hW'X', rfl, hg⟩ | ⟨Y', Z'', hW'Y', rfl, hg⟩
      | ⟨Z', Z'', hW'Z', rfl, hg⟩
    · exact Or.inl rfl
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'X'.symm) ▸ none_mem_master3) none_not_mem_j0
      · obtain rfl : Y'₀ = X' := j0_injective (hW'eq.symm.trans hW'X')
        exact Or.inr (Or.inl ⟨X, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩)
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'X') ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Y'.symm) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
      · obtain rfl : Y'₀ = Y' := j1_injective (hW'eq.symm.trans hW'Y')
        exact Or.inr (Or.inr (Or.inl ⟨Y, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))
      · obtain ⟨c, hc⟩ := h₂' Y'₀ (f₂.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Y') ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hdf with rfl | ⟨X, Y'₀, rfl, hW'eq, hf⟩ | ⟨Y, Y'₀, rfl, hW'eq, hf⟩
        | ⟨Z, Y'₀, rfl, hW'eq, hf⟩
      · exact absurd ((hW'Z'.symm) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ := h₀' Y'₀ (f₀.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
      · obtain ⟨b, hb⟩ := h₁' Y'₀ (f₁.rel_cod hf)
        exact absurd ((hW'eq.symm.trans hW'Z') ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
      · obtain rfl : Y'₀ = Z' := j2_injective (hW'eq.symm.trans hW'Z')
        exact Or.inr (Or.inr (Or.inr ⟨Z, Z'', rfl, rfl, ⟨Y'₀, hf, hg⟩⟩))

end SumMap3

/-! ### The canonical injections `D_i ↪ D₀+D₁+D₂` -/

section SumInj

open Example62C

variable {α β γ : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}

/-- The `0`-injection `D₀ ↪ D₀+D₁+D₂`: send `x₀∈|D₀|` to the sum element whose
only proper
neighbourhoods are the `0`-copies `0X` with `X∈x₀`. -/
def sinj0 (x₀ : V₀.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ X, V₀.mem X ∧ W = j0 X ∧ x₀.mem X
  sub := by
    rintro W (rfl | ⟨X, hX, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨X, hX, rfl⟩)
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) (rfl | ⟨X', hX', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨X', hX', by rw [master3_inter_j0 hX'], hx'⟩
    · exact Or.inr ⟨X, hX, by rw [Set.inter_comm, master3_inter_j0 hX], hx⟩
    · exact Or.inr ⟨X ∩ X', x₀.sub (x₀.inter_mem hx hx'), j0_inter_j0 X X', x₀.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨X, hX, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨X', hX', rfl, x₀.up_mem hx hX' (j0_subset_j0.mp hsub)⟩
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j1
      · obtain ⟨a, ha⟩ := h₀ X (x₀.sub hx); exact absurd (hsub (t0_mem_j0.mpr ha)) t0_not_mem_j2

/-- The `1`-injection `D₁ ↪ D₀+D₁+D₂`. -/
def sinj1 (x₁ : V₁.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Y, V₁.mem Y ∧ W = j1 Y ∧ x₁.mem Y
  sub := by
    rintro W (rfl | ⟨Y, hY, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) (rfl | ⟨Y', hY', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Y', hY', by rw [master3_inter_j1 hY'], hx'⟩
    · exact Or.inr ⟨Y, hY, by rw [Set.inter_comm, master3_inter_j1 hY], hx⟩
    · exact Or.inr ⟨Y ∩ Y', x₁.sub (x₁.inter_mem hx hx'), j1_inter_j1 Y Y', x₁.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Y, hY, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j0
      · exact Or.inr ⟨Y', hY', rfl, x₁.up_mem hx hY' (j1_subset_j1.mp hsub)⟩
      · obtain ⟨b, hb⟩ := h₁ Y (x₁.sub hx); exact absurd (hsub (t1_mem_j1.mpr hb)) t1_not_mem_j2

/-- The `2`-injection `D₂ ↪ D₀+D₁+D₂`. -/
def sinj2 (x₂ : V₂.Element) : (sum3 V₀ V₁ V₂ h₀ h₁ h₂).Element where
  mem W := W = master3 V₀ V₁ V₂ ∨ ∃ Z, V₂.mem Z ∧ W = j2 Z ∧ x₂.mem Z
  sub := by
    rintro W (rfl | ⟨Z, hZ, rfl, -⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr (Or.inr ⟨Z, hZ, rfl⟩))
  master_mem := Or.inl rfl
  inter_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) (rfl | ⟨Z', hZ', rfl, hx'⟩)
    · exact Or.inl (by rw [Set.inter_self])
    · exact Or.inr ⟨Z', hZ', by rw [master3_inter_j2 hZ'], hx'⟩
    · exact Or.inr ⟨Z, hZ, by rw [Set.inter_comm, master3_inter_j2 hZ], hx⟩
    · exact Or.inr ⟨Z ∩ Z', x₂.sub (x₂.inter_mem hx hx'), j2_inter_j2 Z Z', x₂.inter_mem hx hx'⟩
  up_mem := by
    rintro W W' (rfl | ⟨Z, hZ, rfl, hx⟩) hW' hsub
    · exact Or.inl (eq_master3_of_subset hsub ((sum3 V₀ V₁ V₂ h₀ h₁ h₂).sub_master hW'))
    · rcases hW' with rfl | ⟨X', hX', rfl⟩ | ⟨Y', hY', rfl⟩ | ⟨Z', hZ', rfl⟩
      · exact Or.inl rfl
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j0
      · obtain ⟨c, hc⟩ := h₂ Z (x₂.sub hx); exact absurd (hsub (t2_mem_j2.mpr hc)) t2_not_mem_j1
      · exact Or.inr ⟨Z', hZ', rfl, x₂.up_mem hx hZ' (j2_subset_j2.mp hsub)⟩

@[simp] theorem sinj0_mem_j0 {x₀ : V₀.Element} {X : Set α} (hX : V₀.mem X) :
    (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀).mem (j0 X) ↔ x₀.mem X := by
  constructor
  · rintro (h0 | ⟨X', hX', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j0
    · rw [j0_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨X, hX, rfl, hx⟩

@[simp] theorem sinj1_mem_j1 {x₁ : V₁.Element} {Y : Set β} (hY : V₁.mem Y) :
    (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁).mem (j1 Y) ↔ x₁.mem Y := by
  constructor
  · rintro (h0 | ⟨Y', hY', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j1
    · rw [j1_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Y, hY, rfl, hx⟩

@[simp] theorem sinj2_mem_j2 {x₂ : V₂.Element} {Z : Set γ} (hZ : V₂.mem Z) :
    (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂).mem (j2 Z) ↔ x₂.mem Z := by
  constructor
  · rintro (h0 | ⟨Z', hZ', heq, hx⟩)
    · exact absurd (h0 ▸ none_mem_master3) none_not_mem_j2
    · rw [j2_injective heq]; exact hx
  · intro hx; exact Or.inr ⟨Z, hZ, rfl, hx⟩

end SumInj

/-! ### Monotonicity of the injections, and the action of `f₀+f₁+f₂` on them -/

section SumInjMap

open Example62C

variable {α β γ α' β' γ' : Type*}
  {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}
  {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'} {V₂' : NeighborhoodSystem γ'}
  {h₀ : ∀ X, V₀.mem X → X.Nonempty} {h₁ : ∀ Y, V₁.mem Y → Y.Nonempty}
  {h₂ : ∀ Z, V₂.mem Z → Z.Nonempty}
  {h₀' : ∀ X, V₀'.mem X → X.Nonempty} {h₁' : ∀ Y, V₁'.mem Y → Y.Nonempty}
  {h₂' : ∀ Z, V₂'.mem Z → Z.Nonempty}

theorem sinj1_mono {x x' : V₁.Element} (hx : x ≤ x') :
    sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj1 x' := by
  rintro W (rfl | ⟨Y, hY, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Y, hY, rfl, hx Y hm⟩

theorem sinj2_mono {x x' : V₂.Element} (hx : x ≤ x') :
    sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x ≤ sinj2 x' := by
  rintro W (rfl | ⟨Z, hZ, rfl, hm⟩)
  · exact Or.inl rfl
  · exact Or.inr ⟨Z, hZ, rfl, hx Z hm⟩

/-- `(f₀+f₁+f₂)(inj₀ x) = inj₀(f₀ x)`. -/
theorem sumMap3_sinj0 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₀ : V₀.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (
      h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj0 (V₁ := V₁) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₀)
      = sinj0 (V₁ := V₁') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₀.toElementMap x₀) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · have hXX : X = X₀ := j0_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₀.rel_cod hf, rfl, ⟨X₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨a, ha⟩ :=
        h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j1
    · rcases hU with hUm | ⟨X₀, hX₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨a, ha⟩ :=
        h₀ X₀ hX₀; exact absurd ((hUeq.symm.trans hUj) ▸ t0_mem_j0.mpr ha) t0_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j0 X, Or.inr ⟨X, x₀.sub hx, rfl, hx⟩, Or.inr (Or.inl ⟨X, x₀.sub hx, rfl⟩),
        Or.inr (Or.inl ⟨Y', f₀.rel_cod hf, rfl⟩), Or.inr (Or.inl ⟨X, Y', rfl, rfl, hf⟩)⟩

/-- `(f₀+f₁+f₂)(inj₁ x) = inj₁(f₁ x)`. -/
theorem sumMap3_sinj1 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₁ : V₁.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (
      h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj1 (V₀ := V₀) (V₂ := V₂) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₁)
      = sinj1 (V₀ := V₀') (V₂ := V₂') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₁.toElementMap x₁) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨b, hb⟩ :=
        h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j0
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · have hXX : X = Y₀ := j1_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₁.rel_cod hf, rfl, ⟨Y₀, hx, hXX ▸ hf⟩⟩
    · rcases hU with hUm | ⟨Y₀, hY₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · obtain ⟨b, hb⟩ :=
        h₁ Y₀ hY₀; exact absurd ((hUeq.symm.trans hUj) ▸ t1_mem_j1.mpr hb) t1_not_mem_j2
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j1 X, Or.inr ⟨X, x₁.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inl ⟨X, x₁.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inl ⟨Y', f₁.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inl ⟨X, Y',
          rfl, rfl, hf⟩))⟩

/-- `(f₀+f₁+f₂)(inj₂ x) = inj₂(f₂ x)`. -/
theorem sumMap3_sinj2 (f₀ : ApproximableMap V₀ V₀') (f₁ : ApproximableMap V₁ V₁')
    (f₂ : ApproximableMap V₂ V₂') (x₂ : V₂.Element) :
    (sumMap3 (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) (h₀' := h₀') (h₁' := h₁') (
      h₂' := h₂') f₀ f₁ f₂).toElementMap
        (sinj2 (V₀ := V₀) (V₁ := V₁) (h₀ := h₀) (h₁ := h₁) (h₂ := h₂) x₂)
      = sinj2 (V₀ := V₀') (V₁ := V₁') (h₀ := h₀') (h₁ := h₁') (h₂ := h₂') (f₂.toElementMap x₂) := by
  apply Element.ext
  intro W'
  constructor
  · rintro ⟨U, hU, hUmem, hU'mem, hd⟩
    rcases hd with rfl | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩ | ⟨X, Y', hUj, rfl, hf⟩
    · exact Or.inl rfl
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j0
      · obtain ⟨c, hc⟩ :=
        h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j0
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j1
      · obtain ⟨c, hc⟩ :=
        h₂ Z₀ hZ₀; exact absurd ((hUeq.symm.trans hUj) ▸ t2_mem_j2.mpr hc) t2_not_mem_j1
    · rcases hU with hUm | ⟨Z₀, hZ₀, hUeq, hx⟩
      · exact absurd ((hUm.symm.trans hUj) ▸ none_mem_master3) none_not_mem_j2
      · have hXX : X = Z₀ := j2_injective (hUj.symm.trans hUeq)
        exact Or.inr ⟨Y', f₂.rel_cod hf, rfl, ⟨Z₀, hx, hXX ▸ hf⟩⟩
  · rintro (rfl | ⟨Y', hY', rfl, hm⟩)
    · exact ⟨master3 V₀ V₁ V₂, Or.inl rfl, (sum3 V₀ V₁ V₂ h₀ h₁ h₂).master_mem,
        (sum3 V₀' V₁' V₂' h₀' h₁' h₂').master_mem, Or.inl rfl⟩
    · obtain ⟨X, hx, hf⟩ := hm
      exact ⟨j2 X, Or.inr ⟨X, x₂.sub hx, rfl, hx⟩, Or.inr (Or.inr (Or.inr ⟨X, x₂.sub hx, rfl⟩)),
        Or.inr (Or.inr (Or.inr ⟨Y', f₂.rel_cod hf, rfl⟩)), Or.inr (Or.inr (Or.inr ⟨X, Y',
          rfl, rfl, hf⟩))⟩

end SumInjMap

/-! ## The functor `T(X) = 𝟙 + X + X` -/

open Example62C in
/-- The morphism action of `T`: `T(f) = I_𝟙 + f + f` (identity on the terminator,
`f` on each
successor copy). Always strict (`isStrict_sumMap3`). -/
def tcMapHom {D E : StrictDomainObj.{w}} (f : Category.Hom D E) :
    Category.Hom (tcObj D) (tcObj E) :=
  ⟨sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1, isStrict_sumMap3 _ _ _⟩

open Example62C in
/-- **Exercise 6.17 — the functor `T(X) = 𝟙 + X + X`** on the category of `∅`-free
domains and
strict
maps. On objects, `T(D) = 𝟙 + D + D` (Example 6.2's three-way sum); on maps, `T(f)
= I_𝟙 + f + f`. -/
def Tc : Endofunctor StrictDomainObj.{w} where
  obj := tcObj
  map := tcMapHom
  map_id D := Subtype.ext (by
    change sumMap3 (idMap unitSys) (idMap D.sys) (idMap D.sys) = idMap (tcObj D).sys
    exact sumMap3_id)
  map_comp {D E F} g f := Subtype.ext (by
    change sumMap3 (idMap unitSys) (g.1.comp f.1) (g.1.comp f.1)
      = (sumMap3 (idMap unitSys) g.1 g.1).comp (sumMap3 (idMap unitSys) f.1 f.1)
    have h := sumMap3_comp (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (h₀'' := Example62C.unitSys_nonempty) (h₁'' := F.nonempty) (h₂'' := F.nonempty)
      (idMap unitSys) g.1 g.1 (idMap unitSys) f.1 f.1
    rw [idMap_comp] at h
    exact h)

@[simp] theorem Tc_obj (D : StrictDomainObj.{w}) : Tc.obj D = tcObj D := rfl

@[simp] theorem Tc_map_val {D E : StrictDomainObj.{w}} (f : Category.Hom D E) :
    (Tc.map f).1 = sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := D.nonempty) (h₂ := D.nonempty)
      (h₀' := Example62C.unitSys_nonempty) (h₁' := E.nonempty) (h₂' := E.nonempty)
      (idMap unitSys) f.1 f.1 := rfl

/-! ## `C` as a `T`-algebra -/

/-- The map of an order-isomorphism is strict (an iso of domains preserves `⊥`). -/
theorem isStrict_ofIso {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
    (e : V₀.Element ≃o V₁.Element) : IsStrict (ofIso e) := by
  rw [isStrict_iff_apply_bot, toElementMap_ofIso]
  exact e.map_bot

open Example44 Example62C ExampleB in
/-- `C` (Example 4.4: finite-or-infinite binary sequences) as an object of the
`∅`-free category. -/
def Cobj : StrictDomainObj.{0} := ⟨Str, C, C_nonempty⟩

open Example44 Example62C in
/-- **The `T`-algebra structure on `C`.** `(tcObj Cobj).sys = 𝟙 + C + C`
(definitionally Example
6.2's
`CC`), and the structure map `i : 𝟙 + C + C → C` is the inverse of the
domain-equation isomorphism
`ccEquiv` (Example 6.2), realised as an approximable map by `ofIso`; it is strict
by `isStrict_ofIso`.
Concretely `i` sends the terminator to `Λ̂` and each `b`-copy of `x` to `b·x`. -/
def cStr : Category.Hom (Tc.obj Cobj) Cobj :=
  ⟨ofIso (by exact ccEquiv.symm), isStrict_ofIso _⟩

open Example44 Example62C in
/-- **`C` is a `T`-algebra**, `(C, i)` with `T(X) = 𝟙 + X + X`. -/
def Calg : TAlgebra Tc := ⟨Cobj, cStr⟩

/-! ## Initiality of `(C, i)`: the unique homomorphism into any `T`-algebra

We first relate the domain-equation isomorphism `toCC = ccEquiv` to the
separated-sum injections:
the terminator `Λ̂` lands on the `𝟙`-copy, and prepending a bit (`consMap b`)
lands on the `b`-th
`C`-copy. -/

namespace Example62C

open Example44 ExampleB Example62

@[simp] theorem ccEquiv_apply (x : C.Element) : ccEquiv x = toCC x := rfl

/-- `(b·z).mem (bX) ↔ z.mem X`: the `b`-successor's filter restricted to the
`b`-copy is `z`. -/
theorem consMap_mem_embBit {b : Bool} {z : C.Element} {X : Set Str} (hX : C.mem X) :
    ((consMap b).toElementMap z).mem (embBit b X) ↔ z.mem X := by
  constructor
  · rintro ⟨X', hzX', _, _, hsub⟩
    rw [← embBit_eq_prepend] at hsub
    exact z.up_mem hzX' hX (embBit_subset.mp hsub)
  · intro hz
    refine ⟨X, hz, z.sub hz, memC_embBit b hX, ?_⟩
    rw [← embBit_eq_prepend]

/-- `(b·z)` never meets the `(¬b)`-copy: `0z` avoids the `1`-copies and vice versa
(used to
discharge
the cross-tag cases in `toCC_consMap`). -/
theorem consMap_not_mem_embBit_ne {b c : Bool} (hbc : b ≠ c) {z : C.Element} {X : Set Str} :
    ¬ ((consMap b).toElementMap z).mem (embBit c X) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  obtain ⟨w, hw, heq⟩ := hsub ⟨a, rfl, ha⟩
  rw [List.cons.injEq] at hw; exact hbc hw.1

/-- `(b·z)` avoids the terminator `{Λ}` (since `bσ ≠ Λ`). -/
theorem consMap_not_mem_nil {b : Bool} {z : C.Element} :
    ¬ ((consMap b).toElementMap z).mem ({[]} : Set Str) := by
  rintro ⟨X', hzX', hX'mem, _, hsub⟩
  obtain ⟨a, ha⟩ := C_nonempty X' hX'mem
  rw [← embBit_eq_prepend] at hsub
  have := hsub ⟨a, rfl, ha⟩
  rw [Set.mem_singleton_iff] at this; exact absurd this (by simp)

/-- **`toCC ∘ (0·) = inj₁` and `toCC ∘ (1·) = inj₂`.** Prepending the bit `b` to
`z` is, across the
isomorphism `C ≅ 𝟙+C+C`, the injection of `z` into the `b`-th `C`-summand. -/
theorem toCC_consMap (b : Bool) (z : C.Element) :
    toCC ((consMap b).toElementMap z)
      = cond b
          (sinj2 (V₀ := unitSys) (V₁ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z)
          (sinj1 (V₀ := unitSys) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
            (h₂ := C_nonempty) z) := by
  apply NeighborhoodSystem.Element.ext
  intro W
  cases b
  · simp only [cond_false]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact Or.inr ⟨X, hX, rfl, (consMap_mem_embBit hX).mp hz⟩
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))
  · simp only [cond_true]
    constructor
    · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact absurd hz consMap_not_mem_nil
      · exact absurd hz (consMap_not_mem_embBit_ne (by decide))
      · exact Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mp hz⟩
    · rintro (rfl | ⟨Y, hY, rfl, hz⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr ⟨Y, hY, rfl, (consMap_mem_embBit hY).mpr hz⟩))

/-- **`toCC Λ̂ = inj₀`.** The finished empty sequence is the terminator (the
`𝟙`-summand). -/
theorem toCC_strElem_nil :
    toCC (strElem []) = sinj0 (V₁ := C) (V₂ := C) (h₀ := unitSys_nonempty) (h₁ := C_nonempty)
      (h₂ := C_nonempty) unitSys.bot := by
  apply NeighborhoodSystem.Element.ext
  intro W
  constructor
  · rintro (rfl | ⟨rfl, hz⟩ | ⟨X, hX, rfl, hz⟩ | ⟨Y, hY, rfl, hz⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨Set.univ, rfl, rfl, unitSys.bot.master_mem⟩
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
    · exact absurd (hz.2 (Set.mem_singleton_iff.mpr rfl)) nil_not_mem_embBit
  · rintro (rfl | ⟨X, hX, rfl, hz⟩)
    · exact Or.inl rfl
    · obtain rfl : X = Set.univ := hX
      exact Or.inr (Or.inl ⟨rfl, memC_singleton [], subset_rfl⟩)

end Example62C

/-! ### The homomorphism `desc : C → E` for a `T`-algebra `B = (E, k)` -/

section Initial

open Example44 Example62C ExampleB Exercise419 Exercise516

variable (B : TAlgebra Tc)

/-- The distinguished point `e = k(Λ)`: the image under `k` of the terminator
(`𝟙`-injection). -/
def descE : B.carrier.sys.Element :=
  B.str.1.toElementMap (sinj0 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty)
    (h₂ := B.carrier.nonempty) unitSys.bot)

/-- The `b`-th successor operation `f_b = k ∘ inj_b`: `f₀` via the `0`-copy
(`inj₁`), `f₁` via the
`1`-copy (`inj₂`). -/
def descF (b : Bool) (y : B.carrier.sys.Element) : B.carrier.sys.Element :=
  B.str.1.toElementMap (cond b
    (sinj2 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (
      h₂ := B.carrier.nonempty) y)
    (sinj1 (h₀ := Example62C.unitSys_nonempty) (h₁ := B.carrier.nonempty) (
      h₂ := B.carrier.nonempty) y))

/-- The recursion `φ(Λ)=z`, `φ(b·σ)=f_b(φ(σ))` on a finite string, with base value
`z`. -/
def descVal (z : B.carrier.sys.Element) : Str → B.carrier.sys.Element
  | [] => z
  | b :: σ => descF B b (descVal z σ)

theorem descF_mono (b : Bool) {y y' : B.carrier.sys.Element} (h : y ≤ y') :
    descF B b y ≤ descF B b y' := by
  cases b
  · exact B.str.1.toElementMap_mono (sinj1_mono h)
  · exact B.str.1.toElementMap_mono (sinj2_mono h)

theorem descVal_mono_z {z z' : B.carrier.sys.Element} (h : z ≤ z') :
    ∀ σ, descVal B z σ ≤ descVal B z' σ
  | [] => h
  | _ :: σ => descF_mono B _ (descVal_mono_z h σ)

theorem descVal_append (z : B.carrier.sys.Element) (σ ρ : Str) :
    descVal B z (σ ++ ρ) = descVal B (descVal B z ρ) σ := by
  induction σ with
  | nil => rfl
  | cons b σ ih => exact congrArg (descF B b) ih

theorem descMap_hcone {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B B.carrier.sys.bot τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

theorem descMap_hsing {σ τ : Str} (h : σ <+: τ) :
    descVal B B.carrier.sys.bot σ ≤ descVal B (descE B) τ := by
  obtain ⟨ρ, rfl⟩ := h
  rw [descVal_append]
  exact descVal_mono_z B (B.carrier.sys.bot_le _) σ

/-- **The homomorphism `C → E`.** Built by `liftC` from the head-recursion: `φ(σ⊥)
= f_{σ}(⊥)` and
`φ(σ) = f_{σ}(e)`, interpreting `b₀b₁… ↦ f_{b₀}(f_{b₁}(…))`. -/
def descMap : ApproximableMap C B.carrier.sys :=
  liftC B.carrier.sys (descVal B B.carrier.sys.bot) (descVal B (descE B))
    (fun {_ _} => descMap_hcone B) (fun {_ _} => descMap_hsing B)

@[simp] theorem descMap_strBot (σ : Str) :
    (descMap B).toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ :=
  liftC_strBot _ _ _ _ _ σ

@[simp] theorem descMap_strElem (σ : Str) :
    (descMap B).toElementMap (strElem σ) = descVal B (descE B) σ :=
  liftC_strElem _ _ _ _ _ σ

theorem C_bot_eq_strBot_nil : C.bot = strBot [] := by
  apply NeighborhoodSystem.Element.ext
  intro Y
  change (C.mem Y ∧ C.master ⊆ Y) ↔ (C.mem Y ∧ cone [] ⊆ Y)
  rw [C_master, cone_nil]

theorem descMap_strict : IsStrict (descMap B) := by
  rw [isStrict_iff_apply_bot, C_bot_eq_strBot_nil, descMap_strBot]
  rfl

/-- The bundled strict homomorphism `C → E`. -/
def descStrict : Category.Hom Cobj B.carrier := ⟨descMap B, descMap_strict B⟩

/-! ### The homomorphism square and uniqueness -/

/-- The composite `inj₀∘(...)` of `T(g)` applied to a successor reduces to the
operation `f_b`. The
single computational step behind both existence and uniqueness, for an *arbitrary*
`g`. -/
theorem genKey (g : ApproximableMap C B.carrier.sys) (b : Bool) (w : C.Element) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (
          h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap
      (toCC ((consMap b).toElementMap w)))
      = descF B b (g.toElementMap w) := by
  rw [toCC_consMap]
  cases b
  · simp only [cond_false]; rw [sumMap3_sinj1]; rfl
  · simp only [cond_true]; rw [sumMap3_sinj2]; rfl

/-- `T(g)` on the terminator is the terminator; precomposed with `k` it is `e`. -/
theorem genKey0 (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (
          h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strElem [])))
      = descE B := by
  rw [toCC_strElem_nil, sumMap3_sinj0, toElementMap_idMap]
  rfl

/-- `T(g)` on `⊥` is `⊥`; precomposed with `k` it is `⊥` (both maps are strict). -/
theorem genKeyBot (g : ApproximableMap C B.carrier.sys) :
    B.str.1.toElementMap ((sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (
          h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g).toElementMap (toCC (strBot [])))
      = B.carrier.sys.bot := by
  have hb : toCC (strBot []) = (sum3 unitSys C C Example62C.unitSys_nonempty Example62C.C_nonempty
      Example62C.C_nonempty).bot := by
    rw [← C_bot_eq_strBot_nil, ← Example62C.ccEquiv_apply]; exact ccEquiv.map_bot
  rw [hb, isStrict_iff_apply_bot.mp (isStrict_sumMap3 (h₀ := Example62C.unitSys_nonempty)
    (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (idMap unitSys) g g)]
  exact isStrict_iff_apply_bot.mp B.str.2

theorem ccEquiv_symm_comp : (ofIso ccEquiv.symm).comp (ofIso ccEquiv) = idMap C := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.symm_apply_apply x

theorem ccEquiv_comp_symm :
    (ofIso ccEquiv).comp (ofIso ccEquiv.symm) = idMap (sum3 unitSys C C Example62C.unitSys_nonempty
      Example62C.C_nonempty Example62C.C_nonempty) := by
  apply ext_of_toElementMap
  intro s
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap]
  exact ccEquiv.apply_symm_apply s

/-- **Any map satisfying the homomorphism recursion equals `descMap`.** This is
*both* the existence
witness (`descMap` satisfies it) and the uniqueness driver. -/
theorem rec_determines (g : ApproximableMap C B.carrier.sys)
    (hg : g = (B.str.1.comp
      (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) g g)).comp (ofIso ccEquiv)) :
    g = descMap B := by
  have hbot : ∀ σ, g.toElementMap (strBot σ) = descVal B B.carrier.sys.bot σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKeyBot B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strBot]
      have h := genKey B g b (strBot σ)
      rw [ih] at h
      exact h
  have helem : ∀ σ, g.toElementMap (strElem σ) = descVal B (descE B) σ := by
    intro σ
    induction σ with
    | nil =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply]
      exact genKey0 B g
    | cons b σ ih =>
      conv_lhs => rw [hg]
      rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, Example62C.ccEquiv_apply,
        ← consMap_strElem]
      have h := genKey B g b (strElem σ)
      rw [ih] at h
      exact h
  apply map_ext_C
  · intro σ; rw [hbot, descMap_strBot]
  · intro σ; rw [helem, descMap_strElem]

/-- `C`'s algebra map satisfies the recursion. -/
theorem descMap_satisfiesRec :
    descMap B = (B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty)
        (h₁ := Example62C.C_nonempty) (h₂ := Example62C.C_nonempty) (
          h₀' := Example62C.unitSys_nonempty)
        (h₁' := B.carrier.nonempty) (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B)
        (descMap B))).comp (ofIso ccEquiv) := by
  apply map_ext_C
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strBot]
    cases σ with
    | nil => exact (genKeyBot B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strBot]
      have h := genKey B (descMap B) b (strBot σ)
      rw [descMap_strBot] at h
      exact h.symm
  · intro σ
    rw [toElementMap_comp, toElementMap_comp, toElementMap_ofIso, descMap_strElem]
    cases σ with
    | nil => exact (genKey0 B (descMap B)).symm
    | cons b σ =>
      rw [Example62C.ccEquiv_apply, ← consMap_strElem]
      have h := genKey B (descMap B) b (strElem σ)
      rw [descMap_strElem] at h
      exact h.symm

/-- **The homomorphism square**, read off at the level of underlying approximable
maps:
`desc ∘ i = k ∘ T(desc)`. -/
theorem descComm : (descMap B).comp (ofIso ccEquiv.symm)
    = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
        (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (
          h₁' := B.carrier.nonempty)
        (h₂' := B.carrier.nonempty) (idMap unitSys) (descMap B) (descMap B)) := by
  conv_lhs => rw [descMap_satisfiesRec B]
  rw [comp_assoc, ccEquiv_comp_symm, comp_idMap]

/-- **The descent homomorphism `(C, i) → (E, k)`** as a `T`-algebra homomorphism. -/
def descAlgHom : AlgHom Calg B where
  hom := descStrict B
  comm := by
    apply Subtype.ext
    simp only [StrictDomainObj.comp_val, Tc_map_val]
    exact descComm B

/-- **Uniqueness.** Any `T`-algebra homomorphism out of `(C, i)` equals
`descAlgHom`. -/
theorem descAlgHom_uniq (h' : AlgHom Calg B) : h' = descAlgHom B := by
  obtain ⟨hom, comm⟩ := h'
  have hg : hom.1 = descMap B := by
    refine rec_determines B hom.1 ?_
    have hc : hom.1.comp (ofIso ccEquiv.symm)
        = B.str.1.comp (sumMap3 (h₀ := Example62C.unitSys_nonempty) (h₁ := Example62C.C_nonempty)
          (h₂ := Example62C.C_nonempty) (h₀' := Example62C.unitSys_nonempty) (
            h₁' := B.carrier.nonempty)
          (h₂' := B.carrier.nonempty) (idMap unitSys) hom.1 hom.1) := by
      have hcomm := congrArg Subtype.val comm
      exact hcomm
    have h2 := congrArg (fun m => m.comp (ofIso ccEquiv)) hc
    rw [comp_assoc] at h2
    erw [ccEquiv_symm_comp, comp_idMap] at h2
    exact h2
  have hhom : hom = descStrict B := Subtype.ext hg
  subst hhom
  rfl

end Initial

/-- **Exercise 6.17 (existence half) — `(C, i)` is an initial `T`-algebra for
`T(X) = 𝟙 + X + X`.**
The descent map `φ : C → E` is the closed-form head-recursion `φ(Λ) = e`, `φ(b·x)
= f_b(φ x)`
(`f_b = k ∘ inj_b`), built choice-free via `liftC`; it is the unique `T`-algebra
homomorphism, so `C`
is determined (up to iso, Proposition 6.6) as the initial algebra of `X ↦ 𝟙 + X +
X`. -/
def CisInitial : IsInitial Calg where
  desc := descAlgHom
  uniq := fun B h => descAlgHom_uniq B h

end Domain.Neighborhood
