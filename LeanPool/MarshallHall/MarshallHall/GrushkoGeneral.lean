/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.Grushko
import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.GroupTheory.CoprodI
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.Rank
import Mathlib.Tactic

/-!
## General free-product rank infrastructure

This file records the factorwise part of the Grushko--Neumann argument for
arbitrary groups.  The free product of finitely generated groups is finitely
generated, and the union of finite generating sets gives the upper bound.

For the lower bound, a tuple whose entries are already separated between the
two factors can be projected back to each factor.  The remaining, genuinely
Grushko-specific step is to reduce an arbitrary generating tuple to this
separated form without increasing its length.
-/

open Function Set
open Monoid.Coprod

noncomputable section

namespace MarshallHall

variable {G H : Type*} [Group G] [Group H]

namespace GeneralGrushko

/-! ### Finite generation and the easy inequality -/

instance coprod_fg [Group.FG G] [Group.FG H] : Group.FG (G ∗ H) := by
  rcases Group.fg_iff.mp (show Group.FG G from inferInstance) with ⟨S, hS, hSf⟩
  rcases Group.fg_iff.mp (show Group.FG H from inferInstance) with ⟨T, hT, hTf⟩
  refine Group.fg_iff.mpr ⟨inl '' S ∪ inr '' T, ?_, hSf.image _ |>.union (hTf.image _)⟩
  have hleftSub : Subgroup.closure ((inl : G →* G ∗ H) '' S) =
      MonoidHom.range (inl : G →* G ∗ H) := by
    rw [← MonoidHom.map_closure, hS, MonoidHom.range_eq_map]
  have hrightSub : Subgroup.closure ((inr : H →* G ∗ H) '' T) =
      MonoidHom.range (inr : H →* G ∗ H) := by
    rw [← MonoidHom.map_closure, hT, MonoidHom.range_eq_map]
  have hrangeleft : Subgroup.closure (Set.range (inl : G →* G ∗ H)) =
      MonoidHom.range (inl : G →* G ∗ H) := by
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  have hrangeright : Subgroup.closure (Set.range (inr : H →* G ∗ H)) =
      MonoidHom.range (inr : H →* G ∗ H) := by
    rw [← MonoidHom.coe_range, Subgroup.closure_eq]
  rw [← closure_range_inl_union_inr]
  rw [Subgroup.closure_union, Subgroup.closure_union,
    hleftSub, hrightSub, hrangeleft, hrangeright]

theorem rank_coprod_le_add [Group.FG G] [Group.FG H] :
    Group.rank (G ∗ H) ≤ Group.rank G + Group.rank H := by
  classical
  obtain ⟨S, hScard, hS⟩ := Group.rank_spec G
  obtain ⟨T, hTcard, hT⟩ := Group.rank_spec H
  let U : Finset (G ∗ H) := S.image inl ∪ T.image inr
  have hU : Subgroup.closure (U : Set (G ∗ H)) = ⊤ := by
    dsimp [U]
    rw [Finset.coe_union]
    rw [Subgroup.closure_union]
    rw [Finset.coe_image, Finset.coe_image]
    have hleftfin : Subgroup.closure ((inl : G →* G ∗ H) '' (S : Set G)) =
        MonoidHom.range (inl : G →* G ∗ H) := by
      rw [← MonoidHom.map_closure, hS, ← MonoidHom.range_eq_map]
    have hrightfin : Subgroup.closure ((inr : H →* G ∗ H) '' (T : Set H)) =
        MonoidHom.range (inr : H →* G ∗ H) := by
      rw [← MonoidHom.map_closure, hT, ← MonoidHom.range_eq_map]
    rw [hleftfin, hrightfin, range_inl_sup_range_inr]
  refine (Group.rank_le (S := U) hU).trans ?_
  change (S.image inl ∪ T.image inr).card ≤ _
  calc
    (S.image inl ∪ T.image inr).card ≤ (S.image inl).card + (T.image inr).card :=
      Finset.card_union_le (S.image inl) (T.image inr)
    _ = Group.rank G + Group.rank H := by
      rw [Finset.card_image_of_injective _ inl_injective,
        Finset.card_image_of_injective _ inr_injective, hScard, hTcard]

/-! ### The lower bound for separated generating tuples -/

/-- The natural embedding of a tagged factor element into the free product. -/
def separatedMap : Sum G H → G ∗ H := fun x => match x with
  | Sum.inl g => inl g
  | Sum.inr h => inr h

def leftIndex {n : ℕ} (s : Fin n → Sum G H) :=
  {i : Fin n // ∃ g : G, s i = Sum.inl g}

def rightIndex {n : ℕ} (s : Fin n → Sum G H) :=
  {i : Fin n // ¬ ∃ g : G, s i = Sum.inl g}

def leftValue {n : ℕ} (s : Fin n → Sum G H) (i : leftIndex s) : G :=
  match s i.1 with
  | Sum.inl g => g
  | Sum.inr _ => 1

def rightValue {n : ℕ} (s : Fin n → Sum G H) (i : rightIndex s) : H :=
  match s i.1 with
  | Sum.inl _ => 1
  | Sum.inr h => h

noncomputable instance leftIndexFinite {n : ℕ} (s : Fin n → Sum G H) :
    Finite (leftIndex s) :=
  Finite.of_injective (β := Fin n) (fun i : leftIndex s => i.1) Subtype.coe_injective

noncomputable instance rightIndexFinite {n : ℕ} (s : Fin n → Sum G H) :
    Finite (rightIndex s) :=
  Finite.of_injective (β := Fin n) (fun i : rightIndex s => i.1) Subtype.coe_injective

noncomputable instance leftIndexFintype {n : ℕ} (s : Fin n → Sum G H) :
    Fintype (leftIndex s) := Fintype.ofFinite _

noncomputable instance rightIndexFintype {n : ℕ} (s : Fin n → Sum G H) :
    Fintype (rightIndex s) := Fintype.ofFinite _

noncomputable def leftGenerators {n : ℕ} (s : Fin n → Sum G H) : Finset G := by
  classical
  exact Finset.univ.image (leftValue s)

noncomputable def rightGenerators {n : ℕ} (s : Fin n → Sum G H) : Finset H := by
  classical
  exact Finset.univ.image (rightValue s)

theorem separated_left_closure {n : ℕ} (s : Fin n → Sum G H)
    (hs : Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤) :
    Subgroup.closure (leftGenerators s : Set G) = ⊤ := by
  classical
  have hmap : Subgroup.closure
      ((Monoid.Coprod.fst : G ∗ H →* G) '' Set.range (separatedMap ∘ s)) = ⊤ := by
    rw [← MonoidHom.map_closure, hs, Subgroup.map_top_of_surjective]
    exact Monoid.Coprod.fst_surjective
  apply top_unique
  intro x hx
  have hx' : x ∈ Subgroup.closure
      ((Monoid.Coprod.fst : G ∗ H →* G) '' Set.range (separatedMap ∘ s)) := by
    rw [hmap]
    trivial
  have hsubset :
      (Monoid.Coprod.fst : G ∗ H →* G) '' Set.range (separatedMap ∘ s) ⊆
        Subgroup.closure (leftGenerators s : Set G) := by
    rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
    cases h : s i with
    | inl g =>
        let i' : leftIndex s := ⟨i, ⟨g, h⟩⟩
        apply Subgroup.subset_closure
        apply Finset.mem_image.mpr
        refine ⟨i', Finset.mem_univ _, ?_⟩
        simp [leftValue, separatedMap, h, i']
    | inr h' =>
        simp [separatedMap, h]
  have hmono := Subgroup.closure_mono (G := G) hsubset
  rw [Subgroup.closure_eq] at hmono
  exact hmono hx'

theorem separated_right_closure {n : ℕ} (s : Fin n → Sum G H)
    (hs : Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤) :
    Subgroup.closure (rightGenerators s : Set H) = ⊤ := by
  classical
  have hmap : Subgroup.closure
      ((Monoid.Coprod.snd : G ∗ H →* H) '' Set.range (separatedMap ∘ s)) = ⊤ := by
    rw [← MonoidHom.map_closure, hs, Subgroup.map_top_of_surjective]
    exact Monoid.Coprod.snd_surjective
  apply top_unique
  intro x hx
  have hx' : x ∈ Subgroup.closure
      ((Monoid.Coprod.snd : G ∗ H →* H) '' Set.range (separatedMap ∘ s)) := by
    rw [hmap]
    trivial
  have hsubset :
      (Monoid.Coprod.snd : G ∗ H →* H) '' Set.range (separatedMap ∘ s) ⊆
        Subgroup.closure (rightGenerators s : Set H) := by
    rintro y ⟨z, ⟨i, rfl⟩, rfl⟩
    cases h : s i with
    | inl g =>
        simp [separatedMap, h]
    | inr h' =>
        let i' : rightIndex s := ⟨i, by
          intro hleft
          rcases hleft with ⟨g', hg'⟩
          rw [h] at hg'
          cases hg'⟩
        apply Subgroup.subset_closure
        apply Finset.mem_image.mpr
        refine ⟨i', Finset.mem_univ _, ?_⟩
        simp [rightValue, separatedMap, h, i']
  have hmono := Subgroup.closure_mono (G := H) hsubset
  rw [Subgroup.closure_eq] at hmono
  exact hmono hx'

theorem rank_add_le_of_separated_generators {n : ℕ} (s : Fin n → Sum G H)
    [Group.FG G] [Group.FG H]
    (hs : Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤) :
    Group.rank G + Group.rank H ≤ n := by
  classical
  let A : Finset G := leftGenerators s
  let B : Finset H := rightGenerators s
  have hA : Subgroup.closure (A : Set G) = ⊤ := by
    simpa [A] using separated_left_closure s hs
  have hB : Subgroup.closure (B : Set H) = ⊤ := by
    simpa [B] using separated_right_closure s hs
  have hrank : Group.rank G + Group.rank H ≤ A.card + B.card :=
    Nat.add_le_add (Group.rank_le hA) (Group.rank_le hB)
  have hcardA : A.card ≤ Fintype.card (leftIndex s) := by
    dsimp [A]
    exact Finset.card_image_le
  have hcardB : B.card ≤ Fintype.card (rightIndex s) := by
    dsimp [B]
    exact Finset.card_image_le
  have hindices : Fintype.card (leftIndex s) + Fintype.card (rightIndex s) = n := by
    let p : Fin n → Prop := fun i => ∃ g : G, s i = Sum.inl g
    have hcomp := @Fintype.card_subtype_compl (Fin n) inferInstance p
      (leftIndexFintype s) (rightIndexFintype s)
    have hle := @Fintype.card_subtype_le (Fin n) inferInstance p (leftIndexFintype s)
    have hcomp' : Fintype.card (rightIndex s) = Fintype.card (Fin n) -
        Fintype.card (leftIndex s) := by
      simpa [leftIndex, rightIndex, p] using hcomp
    have hle' : Fintype.card (leftIndex s) ≤ Fintype.card (Fin n) := by
      simpa [leftIndex, p] using hle
    calc
      Fintype.card (leftIndex s) + Fintype.card (rightIndex s) =
          Fintype.card (leftIndex s) +
            (Fintype.card (Fin n) - Fintype.card (leftIndex s)) := by rw [hcomp']
      _ = Fintype.card (Fin n) := Nat.add_sub_of_le hle'
      _ = n := Fintype.card_fin n
  exact hrank.trans ((Nat.add_le_add hcardA hcardB).trans_eq hindices)

/-- One elementary Nielsen move on a finite generating tuple.  Permutations,
inversion of one entry, and multiplication of one entry by a different entry
all preserve the subgroup generated by the tuple. -/
inductive NielsenStep {A : Type*} [Group A] {n : ℕ}
    (x y : Fin n → A) : Prop
  | perm (e : Fin n ≃ Fin n) (h : y = x ∘ e) : NielsenStep x y
  | invert (i : Fin n) (h : y = Function.update x i (x i)⁻¹) :
      NielsenStep x y
  | mulRight (i j : Fin n) (hij : i ≠ j)
      (h : y = Function.update x i (x i * x j)) : NielsenStep x y

/-- The subgroup generated by a tuple is unchanged by one Nielsen move. -/
theorem nielsenStep_closure_eq {A : Type*} [Group A] {n : ℕ}
    {x y : Fin n → A} (h : NielsenStep x y) :
    Subgroup.closure (Set.range x) = Subgroup.closure (Set.range y) := by
  cases h with
  | perm e h =>
      subst y
      apply le_antisymm
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨i, rfl⟩
        refine Subgroup.subset_closure ⟨e.symm i, ?_⟩
        simp [Function.comp_apply]
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨i, rfl⟩
        refine Subgroup.subset_closure ⟨e i, ?_⟩
        simp [Function.comp_apply]
  | invert i h =>
      subst y
      apply le_antisymm
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨k, rfl⟩
        by_cases hki : k = i
        · subst k
          have hi : x i ∈ Subgroup.closure
              (Set.range (Function.update x i (x i)⁻¹)) := by
            have hi' : (x i)⁻¹ ∈ Subgroup.closure
                (Set.range (Function.update x i (x i)⁻¹)) :=
              Subgroup.subset_closure ⟨i, by simp⟩
            simpa using (Subgroup.inv_mem _ hi')
          exact hi
        · have hk : Function.update x i (x i)⁻¹ k = x k := by
            simp [hki]
          rw [← hk]
          exact Subgroup.subset_closure ⟨k, rfl⟩
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨k, rfl⟩
        by_cases hki : k = i
        · subst k
          have hi : x i ∈ Subgroup.closure (Set.range x) :=
            Subgroup.subset_closure ⟨i, rfl⟩
          simpa using (Subgroup.inv_mem _ hi)
        · have hk : Function.update x i (x i)⁻¹ k = x k := by
            simp [hki]
          rw [hk]
          exact Subgroup.subset_closure ⟨k, rfl⟩
  | mulRight i j hij h =>
      subst y
      apply le_antisymm
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨k, rfl⟩
        by_cases hki : k = i
        · subst k
          have hi : x i * x j ∈ Subgroup.closure
              (Set.range (Function.update x i (x i * x j))) :=
            Subgroup.subset_closure ⟨i, by simp⟩
          have hj : x j ∈ Subgroup.closure
              (Set.range (Function.update x i (x i * x j))) := by
            apply Subgroup.subset_closure
            exact ⟨j, by simp [hij.symm]⟩
          simpa [mul_assoc] using
            (Subgroup.mul_mem _ hi (Subgroup.inv_mem _ hj))
        · have hk : Function.update x i (x i * x j) k = x k := by
            simp [hki]
          rw [← hk]
          exact Subgroup.subset_closure ⟨k, rfl⟩
      · apply (Subgroup.closure_le _).mpr
        rintro z ⟨k, rfl⟩
        by_cases hki : k = i
        · subst k
          have hi : x i ∈ Subgroup.closure (Set.range x) :=
            Subgroup.subset_closure ⟨i, rfl⟩
          have hj : x j ∈ Subgroup.closure (Set.range x) :=
            Subgroup.subset_closure ⟨j, rfl⟩
          simpa using Subgroup.mul_mem _ hi hj
        · have hk : Function.update x i (x i * x j) k = x k := by
            simp [hki]
          rw [hk]
          exact Subgroup.subset_closure ⟨k, rfl⟩

/-- Finite sequences of elementary Nielsen moves. -/
def NielsenEquivalent {A : Type*} [Group A] {n : ℕ}
    (x y : Fin n → A) : Prop :=
  Relation.ReflTransGen (fun u v : Fin n → A => NielsenStep u v) x y

theorem nielsenEquivalent_closure_eq {A : Type*} [Group A] {n : ℕ}
    {x y : Fin n → A} (h : NielsenEquivalent x y) :
    Subgroup.closure (Set.range x) = Subgroup.closure (Set.range y) := by
  induction h using Relation.ReflTransGen.trans_induction_on with
  | refl => rfl
  | single h => exact nielsenStep_closure_eq h
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The generator-reduction statement in its stronger, classical form: every
finite generating tuple is Nielsen-equivalent to a tuple separated between the
two factors. -/
def HasNielsenSeparatedReduction : Prop :=
  ∀ (n : ℕ) (x : Fin n → G ∗ H),
    Subgroup.closure (Set.range x) = ⊤ →
      ∃ s : Fin n → Sum G H,
        NielsenEquivalent x (separatedMap ∘ s)

/-- The generator-reduction statement needed for the lower bound in the
general Grushko--Neumann theorem.  It says that every finite generating
tuple can be replaced, with the same number of entries, by a tuple whose
entries lie in the two original factors.  The fold/Nielsen argument is the
substantive theorem still to be supplied; this definition keeps its exact
interface separate from the rank bookkeeping. -/
def HasSeparatedReduction : Prop :=
  ∀ (n : ℕ) (x : Fin n → G ∗ H),
    Subgroup.closure (Set.range x) = ⊤ →
      ∃ s : Fin n → Sum G H,
        Subgroup.closure (Set.range (separatedMap ∘ s)) = ⊤

theorem hasSeparatedReduction_of_hasNielsenSeparatedReduction
    (hred : HasNielsenSeparatedReduction (G := G) (H := H)) :
    HasSeparatedReduction (G := G) (H := H) := by
  intro n x hx
  obtain ⟨s, hs⟩ := hred n x hx
  refine ⟨s, ?_⟩
  calc
    Subgroup.closure (Set.range (separatedMap ∘ s)) =
        Subgroup.closure (Set.range x) :=
      (nielsenEquivalent_closure_eq hs).symm
    _ = ⊤ := hx

/-- Once the separated-generators theorem is available, the elementary
factorwise bounds assemble into full rank additivity. -/
theorem rank_coprod_eq_add_of_separated_reduction
    [Group.FG G] [Group.FG H]
    (hred : HasSeparatedReduction (G := G) (H := H)) :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H := by
  apply le_antisymm (rank_coprod_le_add (G := G) (H := H))
  obtain ⟨S, hScard, hS⟩ := Group.rank_spec (G ∗ H)
  let eS : (↥S) ≃ Fin (Fintype.card (↥S)) := Fintype.equivFin (↥S)
  let x : Fin (Fintype.card (↥S)) → G ∗ H := fun i => eS.symm i
  have hxrange : Set.range x = (S : Set (G ∗ H)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact (eS.symm i).property
    · intro hy
      let y' : S := ⟨y, hy⟩
      refine ⟨eS y', ?_⟩
      simp [x, eS, y']
  have hx : Subgroup.closure (Set.range x) = ⊤ := by
    rw [hxrange]
    exact hS
  obtain ⟨s, hs⟩ := hred (Fintype.card (↥S)) x hx
  rw [← hScard]
  simpa only [Fintype.card_coe] using
    (rank_add_le_of_separated_generators s hs)

/-- Rank additivity follows from the stronger Nielsen-equivalence form of
generator reduction. -/
theorem rank_coprod_eq_add_of_nielsen_separated_reduction
    [Group.FG G] [Group.FG H]
    (hred : HasNielsenSeparatedReduction (G := G) (H := H)) :
    Group.rank (G ∗ H) = Group.rank G + Group.rank H :=
  rank_coprod_eq_add_of_separated_reduction
    (hasSeparatedReduction_of_hasNielsenSeparatedReduction hred)

/-! ### Finite indexed free products of free groups -/

/-- A finite indexed free product of free groups is identified with the free
group on the disjoint union of the bases.  This is the finite-family version
of the binary free-group calculation in `MarshallHall.Grushko`. -/
noncomputable def coprodIFreeGroupEquiv {ι : Type*} (α : ι → Type*)
    [∀ i, Fintype (α i)] :
    Monoid.CoprodI (fun i => FreeGroup (α i)) ≃*
      FreeGroup (Σ i, α i) :=
  (Monoid.CoprodI.FreeGroupBasis.coprodI
    (fun i => FreeGroupBasis.ofFreeGroup (α i))).repr

noncomputable instance coprodI_freeGroup_fg {ι : Type*} [Fintype ι]
    (α : ι → Type*) [∀ i, Fintype (α i)] :
    Group.FG (Monoid.CoprodI (fun i => FreeGroup (α i))) := by
  exact Group.fg_of_surjective
    (f := (coprodIFreeGroupEquiv α).symm.toMonoidHom)
    (coprodIFreeGroupEquiv α).symm.surjective

/-- Grushko rank additivity for a finite indexed free product of finite-rank
free groups.  The arbitrary-factor theorem still requires the separate
generator-reduction theorem above; this result is the fully formalized free
factor subcase. -/
theorem rank_coprodI_freeGroup {ι : Type*} [Fintype ι] (α : ι → Type*)
    [∀ i, Fintype (α i)] :
    Group.rank (Monoid.CoprodI (fun i => FreeGroup (α i))) =
      ∑ i, Fintype.card (α i) := by
  rw [Group.rank_congr (coprodIFreeGroupEquiv α)]
  rw [rank_freeGroup_finite]
  simp

/-! ### A finite-word length for the binary free product

The next step in the arbitrary-factor theorem is a reduction of a finite
generating tuple.  This gives the reduction argument an honest complexity
measure without committing to a particular normal-form implementation.  A
word is a list of tagged factor elements, and its length is the least length
of a word representing the given free-product element.  The elementary
calculus below is enough for induction on reductions: words concatenate,
factor elements have length at most one, and multiplication is subadditive.
-/

/-- Evaluation of a finite alternating-free word in the binary free product.
The list is not required to be reduced; `factorWordLength` takes the minimum
over all such representatives. -/
def factorWordProd : List (Sum G H) → G ∗ H
  | [] => 1
  | x :: xs => separatedMap x * factorWordProd xs

theorem factorWordProd_append (u v : List (Sum G H)) :
    factorWordProd (u ++ v) = factorWordProd u * factorWordProd v := by
  induction u with
  | nil => simp [factorWordProd]
  | cons x u ih =>
      simp only [List.cons_append, factorWordProd]
      rw [ih, mul_assoc]

theorem factorWordProd_surjective :
    Function.Surjective (factorWordProd (G := G) (H := H)) := by
  intro x
  induction x using Monoid.Coprod.induction_on' with
  | one => exact ⟨[], rfl⟩
  | inl_mul g x ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨Sum.inl g :: u, ?_⟩
      simp [factorWordProd, separatedMap, hu]
  | inr_mul h x ih =>
      obtain ⟨u, hu⟩ := ih
      refine ⟨Sum.inr h :: u, ?_⟩
      simp [factorWordProd, separatedMap, hu]

def factorWordRepresented (x : G ∗ H) (n : ℕ) : Prop :=
  ∃ u : List (Sum G H), u.length = n ∧ factorWordProd u = x

theorem factorWordRepresented_exists (x : G ∗ H) :
    ∃ n, factorWordRepresented x n := by
  obtain ⟨u, hu⟩ := factorWordProd_surjective x
  exact ⟨u.length, u, rfl, hu⟩

/-- The least number of factor letters needed to represent an element. -/
noncomputable def factorWordLength (x : G ∗ H) : ℕ :=
  by
    classical
    exact Nat.find (factorWordRepresented_exists x)

theorem factorWordLength_spec (x : G ∗ H) :
    factorWordRepresented x (factorWordLength x) := by
  classical
  exact Nat.find_spec (factorWordRepresented_exists x)

theorem factorWordLength_wordProd_le (u : List (Sum G H)) :
    factorWordLength (factorWordProd u) ≤ u.length := by
  classical
  exact Nat.find_min' (factorWordRepresented_exists (factorWordProd u)) ⟨u, rfl, rfl⟩

@[simp] theorem factorWordLength_one :
    factorWordLength (1 : G ∗ H) = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  simpa [factorWordProd] using
    (factorWordLength_wordProd_le (G := G) (H := H) ([] : List (Sum G H)))

@[simp] theorem factorWordLength_eq_zero_iff {x : G ∗ H} :
    factorWordLength x = 0 ↔ x = 1 := by
  classical
  constructor
  · intro hx
    obtain ⟨u, hu, hux⟩ := factorWordLength_spec x
    have hu0 : u = [] := by
      cases u with
      | nil => rfl
      | cons a u => simp_all
    rw [hu0] at hux
    simpa [factorWordProd] using hux.symm
  · rintro rfl
    exact factorWordLength_one

theorem factorWordLength_mul_le (x y : G ∗ H) :
    factorWordLength (x * y) ≤ factorWordLength x + factorWordLength y := by
  classical
  obtain ⟨u, hu, hux⟩ := factorWordLength_spec x
  obtain ⟨v, hv, hvy⟩ := factorWordLength_spec y
  have huv : factorWordRepresented (x * y) (u.length + v.length) := by
    refine ⟨u ++ v, by simp [hu, hv], ?_⟩
    rw [factorWordProd_append, hux, hvy]
  have hle := Nat.find_min' (factorWordRepresented_exists (x * y)) huv
  rw [← hu, ← hv]
  exact hle

theorem factorWordLength_inl_le_one (g : G) :
    factorWordLength (inl g : G ∗ H) ≤ 1 := by
  classical
  exact Nat.find_min' (factorWordRepresented_exists (inl g))
    ⟨[Sum.inl g], rfl, by simp [factorWordProd, separatedMap]⟩

theorem factorWordLength_inr_le_one (h : H) :
    factorWordLength (inr h : G ∗ H) ≤ 1 := by
  classical
  exact Nat.find_min' (factorWordRepresented_exists (inr h))
    ⟨[Sum.inr h], rfl, by simp [factorWordProd, separatedMap]⟩

end GeneralGrushko

end MarshallHall
