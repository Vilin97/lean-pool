/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies, Tomasz Maciosowski, Kim Morrison, Violeta Hernández Palacios
-/
module

public import LeanPool.MisereGames.GameForm.Birthday
public import LeanPool.MisereGames.Form.Classes
import Mathlib.Data.Fintype.Order

/-!
Misere combinatorial games.
-/

namespace MisereGames

/-!
# Short games

A combinatorial game is `Short` if it is finite and loopfree: it has only
finite many distinct subpositions, and every run has finite length. See
[Siegel, Definition 4.1 on p. 34][siegel:CombinatorialGameTheory:2013].
-/

universe u

public section

namespace Form

open Form
open GameForm

variable {G : Type (u + 1)} [Form G]

/-- Short forms have finitely many options, all of which are short. -/
def IsShort (x : G) : Prop :=
  ∀ p, (Moves.moves p x).Finite ∧ ∀ y ∈ Moves.moves p x, IsShort y
termination_by x
decreasing_by form_wf

theorem short_def {x : G}
    : IsShort x ↔ ∀ p, (Moves.moves p x).Finite ∧ ∀ y ∈ Moves.moves p x, IsShort y := by
  rw [IsShort]

alias ⟨_, Short.mk⟩ := short_def

namespace Short

theorem finite_moves (p : Player) {x : G} (hx : IsShort x) : (Moves.moves p x).Finite :=
  (short_def.mp hx p).left

theorem finite_moves' (p : Player) {x : G} (hx : IsShort x) : Finite ↑(moves p x) :=
  finite_moves p hx

theorem finite_setOf_isOption {x : G} (hx : IsShort x) : {y | Moves.IsOption y x}.Finite := by
  simp_rw [Moves.IsOption.iff_mem_union]
  exact (finite_moves _ hx).union (finite_moves _ hx)

protected theorem of_mem_moves {x y : G} (hx : IsShort x) {p} (hy : y ∈ Moves.moves p x) :
    IsShort y :=
  (short_def.mp hx p).right y hy

protected theorem isOption {x y : G} (hx : IsShort x) (h : Moves.IsOption y x) : IsShort y := by
  rw [Moves.IsOption.iff_mem_union] at h
  cases h with
  | inl h => exact Short.of_mem_moves hx h
  | inr h => exact Short.of_mem_moves hx h

alias _root_.Moves.IsOption.short := Short.isOption

protected theorem subposition {x y : G} (hx : IsShort x) (h : Subposition y x) : IsShort y := by
  cases h with
  | single h => exact Short.isOption hx h
  | tail IH h => have hx' := Short.isOption hx h; exact Short.subposition hx' IH
termination_by x
decreasing_by form_wf

alias _root_.Moves.IsOption.subposition := Short.subposition

theorem finite_setOf_subposition {x : G} (hx : IsShort x) : {y | Moves.Subposition y x}.Finite := by
  have : {y | Moves.Subposition y x} = {y | Moves.IsOption y x} ∪
      ⋃ y ∈ {y | Moves.IsOption y x}, {z | Moves.Subposition z y} := by
    ext
    rw [Set.mem_setOf_eq, Moves.Subposition, Relation.transGen_iff]
    simp [and_comm]
  rw [this]
  refine (finite_setOf_isOption hx).union <| (finite_setOf_isOption hx).biUnion fun y hy ↦ ?_
  exact finite_setOf_subposition (Short.isOption hx hy)
termination_by x
decreasing_by form_wf

theorem _root_.Moves.short_iff_finite_setOf_subposition {x : G} :
    IsShort x ↔ {y | Moves.Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition _ _ x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals form_wf
termination_by x
decreasing_by form_wf

protected theorem add {x y : G} (hx : IsShort x) (hy : IsShort y) : IsShort (x + y) := by
  refine Short.mk fun p ↦ ⟨?_, ?_⟩
  · rw [moves_add]
    simpa using ⟨(Short.finite_moves _ hx).image _, (Short.finite_moves _ hy).image _⟩
  · intro z hz; change z ∈ moves p (x + y) at hz; rw [moves_add] at hz
    cases hz with
    | inl h => obtain ⟨a, ha, rfl⟩ := h; exact Short.add (Short.of_mem_moves hx ha) hy
    | inr h => obtain ⟨b, hb, rfl⟩ := h; exact Short.add hx (Short.of_mem_moves hy hb)
termination_by (x, y)
decreasing_by form_wf

protected theorem neg {x : G} (hx : IsShort x) : IsShort (-x) := by
  rw [short_def]; intro p; constructor
  · rw [moves_neg]
    simpa [← Set.image_neg_eq_neg] using (Short.finite_moves _ hx).image _
  · intro y hy; change y ∈ moves p (-x) at hy; rw [moves_neg] at hy
    have h_neg_y : -y ∈ moves (-p) x := by rwa [Set.mem_neg] at hy
    simpa using Short.neg (Short.of_mem_moves hx h_neg_y)
termination_by x
decreasing_by form_wf

instance : ClosedUnderNeg (IsShort (G := G)) where
  neg_of := Short.neg

instance : Hereditary IsShort (G := G) where
  has_option := Moves.IsOption.short

protected theorem neg_iff {x : G} : IsShort (-x) ↔ IsShort x := ClosedUnderNeg.neg_iff

theorem short_iff_finite_setOf_subposition {x : G} :
    IsShort x ↔ {y | Subposition y x}.Finite := by
  constructor <;> intro h1
  · apply finite_setOf_subposition h1
  · exact Moves.short_iff_finite_setOf_subposition.mpr h1

@[simp]
protected theorem zero : IsShort (0 : G) := by
  rw [Form.short_def]
  simp

instance : HasZero IsShort (G := G) where
  has_zero := Short.zero

protected theorem ofSets {s t : Set G} [Small s] [Small t]
    (hs_fin : s.Finite) (hs_short : ∀ g ∈ s, IsShort g)
    (ht_fin : t.Finite) (ht_short : ∀ g ∈ t, IsShort g) :
    IsShort !{s | t} := by
  rw [short_def]
  intro p
  cases p
  · exact ⟨by simpa using hs_fin, by simpa using hs_short⟩
  · exact ⟨by simpa using ht_fin, by simpa using ht_short⟩

@[simp]
protected theorem star : IsShort (!{{0} | {0}} : G) := by
  apply Short.ofSets
  · exact Set.finite_singleton 0
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    exact Short.zero
  · exact Set.finite_singleton 0
  · intro g hg
    simp only [Set.mem_singleton_iff] at hg
    subst g
    exact Short.zero

@[simp]
protected theorem one : IsShort (1 : G) := by
  rw [one_def, Form.short_def]
  simp only [moves_ofSets, Player.cases, Player.forall, Set.finite_singleton, Set.mem_singleton_iff,
             forall_eq, Short.zero, and_self, Set.finite_empty, Set.mem_empty_iff_false,
             IsEmpty.forall_iff, implies_true]

protected theorem sub {x y : GameForm} (hx : IsShort x) (hy : IsShort y) : IsShort (x - y) :=
  Short.add hx (Short.neg hy)

@[simp]
protected theorem natCast : ∀ n : ℕ, IsShort (n : G)
  | 0 =>  Short.zero
  | n + 1 => Short.add (Short.natCast n) Short.one

@[simp]
protected theorem ofNat (n : ℕ) [n.AtLeastTwo] : IsShort (ofNat(n) : G) :=
  Short.natCast n

@[simp]
protected theorem intCast : ∀ n : ℤ, IsShort (n : G)
  | .ofNat n => Short.natCast n
  | .negSucc n => Short.neg (Short.natCast (n + 1))

end Short
end Form

namespace GameForm

open Form

theorem short_iff_birthday_finite {g : GameForm} :
    IsShort g ↔ birthday g < NatOrdinal.of Ordinal.omega0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have (y : {y // IsOption y g}) : ∃ n : ℕ, birthday y.val = n := by
      rw [← NatOrdinal.lt_omega0, ← short_iff_birthday_finite]
      exact Short.isOption h y.prop
    choose f hf using this
    have : Finite { y // IsOption y g } := (Short.finite_setOf_isOption h).to_subtype
    obtain ⟨n, hn⟩ := (Set.finite_range f).exists_le
    apply lt_of_le_of_lt _ (NatOrdinal.nat_lt_omega0 (n + 1))
    rw [birthday_le_iff', Nat.cast_add_one]
    simp only [Order.lt_add_one_iff]
    aesop
  · rw [NatOrdinal.lt_omega0, Form.Short.short_iff_finite_setOf_subposition]
    intro ⟨n, hn⟩
    apply (birthdayFinset n).finite_toSet.subset fun y hy ↦ ?_
    exact (mem_birthdayFinset (x := y) (n := n)).2 ((birthday_lt_of_subposition hy).le.trans_eq hn)
termination_by g
decreasing_by form_wf

theorem short_iff_birthday_nat {x : GameForm} :
    IsShort x ↔ (∃ (n : ℕ), birthday x = n) := by
  rw [short_iff_birthday_finite, NatOrdinal.lt_omega0]

end GameForm

end

end MisereGames
