/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.List.ReduceOption

public import LeanPool.PDL.Local.Tableau

/-! # PDL-Tableaux (Section 4) -/

public section

namespace PDL

open HasLength

/-! ## Projections -/

/-- Extract the continuation of an atomic box with the specified program index. -/
@[simp]
def formProjection : Nat → Formula → Option Formula
  | A, ⌈·B⌉φ => if A == B then some φ else none
  | _, _ => none

/-- Collect the continuations of matching atomic boxes in a formula list. -/
def projection : Nat → List Formula → List Formula
  | A, X => (X.map fun x => (formProjection A x)).reduceOption

@[simp]
theorem proj : g ∈ projection A X ↔ (⌈·A⌉g) ∈ X :=
  by
  induction X
  case nil =>
    simp only [projection, formProjection, beq_iff_eq, List.map_nil, List.not_mem_nil, iff_false]
    exact List.count_eq_zero.mp rfl
  case cons =>
    simp only [projection, formProjection, beq_iff_eq, List.map_cons, List.mem_cons]
    rw [List.reduceOption_mem_iff]
    aesop

/-- Collect the continuations of matching atomic boxes in a formula finset. -/
def _root_.Finset.pdlProjection : Nat → Finset Formula → Finset Formula
  | A, X => (X.image fun x => (formProjection A x).toFinset).sup id

/-- Membership in the projection of a `Finset` of formulas.
This is the `Finset` analogue of `proj`. -/
lemma Finset.mem_projection {A g} {X : Finset Formula} :
    g ∈ X.pdlProjection A ↔ (⌈·A⌉g) ∈ X := by
  constructor
  · intro h
    simp only [Finset.pdlProjection, Finset.mem_sup, Finset.mem_image, id_eq] at h
    obtain ⟨s, ⟨x, hx, rfl⟩, hg⟩ := h
    cases x <;> simp_all only [formProjection, Option.toFinset_none, Finset.notMem_empty,
      beq_iff_eq, Option.mem_toFinset, Option.mem_def]
    case box α ψ =>
      cases α <;> simp_all
  · intro h
    simp only [Finset.pdlProjection, Finset.mem_sup, Finset.mem_image, id_eq]
    exact ⟨_, ⟨_, h, rfl⟩, by simp⟩

/-! ## Histories and Repeats -/

/-- A history is a list of Sequents.
In the `Tableau` type this only tracks "big" steps, not steps happening within a `LocalTableau`.
The list is in reverse order, i.e. the *head is the newest* Sequent. -/
abbrev History : Type := List Sequent

/-- We have a repeat iff the history contains a node that is `setEqTo` the current node.
Note that this is a `Prop`, it does not carry a specific number of steps to go back. -/
@[expose] def rep (Hist : History) (X : Sequent) : Prop := ∃ Y ∈ Hist, Y = X

instance {H X} : Decidable (rep H X) := by
  unfold rep
  induction H
  · apply isFalse; simp_all
  case cons Y YS IH =>
    simp only [List.mem_cons, exists_eq_or_imp]
    exact instDecidableOr

@[simp]
lemma not_rep_empty {X : Sequent} : ¬ rep [] X := by unfold rep; grind

/-- Given `rep H X`, get the index of the companion in `H` using `List.findIdx?`. -/
def rep.toNat {H X} (rp : rep H X) : Nat :=
  match h : List.findIdx? (fun Y => decide (Y = X)) H with
  | none => by
      exfalso
      unfold rep at rp
      have := @List.findIdx?_eq_some_of_exists Sequent H (fun Y => Y = X)
      simp_all
  | some k => k

/-- Given `rep H X`, get the index of the companion in `H` using `List.findIdx?`. -/
def rep.toFin {H X} (rp : rep H X) : Fin (H.length) :=
  have : rp.toNat < H.length :=
    -- use List.findFinIdx? instead here?
    match h : List.findIdx? (fun Y => decide (Y = X)) H with
    | none => by
      exfalso
      unfold rep at rp
      have := @List.findIdx?_eq_some_of_exists Sequent H (fun Y => Y = X)
      simp_all
    | some k => by
      unfold toNat
      rw! [h]
      simp only
      exact (@List.findIdx?_eq_some_iff_findIdx_eq.mp h).1
  ⟨rp.toNat, this⟩

lemma rep.toFin_agrees (rp : rep H X) :
    H[rp.toFin] = X := by
  unfold rep.toFin rep.toNat
  unfold rep at rp
  simp
  have := @List.findIdx?_eq_some_iff_getElem _ H (fun Y ↦ decide (Y = X))
  grind

/-! ## Loaded Path Repeats -/

/-- A lpr means we can go `k` steps back in the history to
reach an equal node, and all nodes on the way are loaded.
Note: `k=0` means the first element of `Hist` is the companion. -/
@[expose] def LoadedPathRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k) = X ∧ ∀ m ≤ k, (Hist.get m).isLoaded)

lemma LoadedPathRepeat.to_rep {H X} (lpr : LoadedPathRepeat H X) : rep H X := by
  rcases lpr with ⟨k, same, all_loaded⟩
  use List.get H k
  grind

lemma LoadedPathRepeat.ext {Hist X} (lprA lprB : LoadedPathRepeat Hist X) :
    lprA.1 = lprB.1 → lprA = lprB := by
  rcases lprA with ⟨a, ha⟩
  rcases lprB with ⟨b, hb⟩
  grind

instance {Hist X} : DecidableEq (LoadedPathRepeat Hist X) := Subtype.instDecidableEq

/-- If there is any loaded path repeat, then we can compute one.
FIXME There is probably a more elegant way, avoiding `Nonempty` and `Fin.find?`.
Something like: def getLPR (H : History) (X : Sequent) : Option ... := ...
that might also give us uniqueness of LPRs? -/
def LoadedPathRepeat.choice {H X} (ne : Nonempty (LoadedPathRepeat H X)) :
    LoadedPathRepeat H X := by
  let somek := @Fin.find? (H.length)
    (fun k => (H.get k) = X ∧ ∀ m ≤ k, (H.get m).isLoaded = true)
  rcases find_def : somek with _|⟨k⟩
  · exfalso
    rw [Fin.find?_eq_none_iff] at find_def
    rcases ne with ⟨⟨k,bla⟩⟩
    specialize find_def k
    simp only [List.get_eq_getElem, eq_iff_iff, iff_true, Bool.decide_and, Bool.and_eq_false_imp,
      decide_eq_true_eq, decide_eq_false_iff_not, not_forall] at *
    simp_all
  · refine ⟨k, ?_⟩
    rw [Fin.find?_eq_some_iff] at find_def
    aesop

theorem LoadedPathRepeat_comp_isLoaded {Hist X} (lpr : LoadedPathRepeat Hist X) :
    (Hist.get lpr.val).isLoaded := by
  rcases lpr with ⟨j, claim⟩
  apply claim.2 j (le_refl j)

theorem LoadedPathRepeat_rep_isLoaded {Hist X} (lpr : LoadedPathRepeat Hist X) : X.isLoaded := by
  rcases lpr with ⟨k, claim⟩
  grind

instance {H X} : Decidable (Nonempty (LoadedPathRepeat H X)) := by
  by_cases ∃ k, (H.get k) = X ∧ ∀ m ≤ k, (H.get m).isLoaded
  case pos h =>
    apply isTrue
    rcases h with ⟨k, same, all_le_loaded⟩
    exact ⟨k, same, all_le_loaded⟩
  case neg h =>
    apply isFalse
    simp only [not_nonempty_iff]
    constructor
    rintro ⟨k, same, all_le_loaded⟩
    push Not at h
    specialize h k same
    aesop

instance {H X} : Decidable (IsEmpty (LoadedPathRepeat H X)) := by
  by_cases ∃ k, (H.get k) = X ∧ ∀ m ≤ k, (H.get m).isLoaded
  case pos h =>
    apply isFalse
    simp only [not_isEmpty_iff]
    rcases h with ⟨k, same, all_le_loaded⟩
    constructor
    exact ⟨k, by grind⟩
  case neg h =>
    apply isTrue
    constructor
    rintro ⟨k, same, all_le_loaded⟩
    absurd h
    aesop

/-! ## Free, forbidden and allowed repeats

In `Tableau` we only want to allow the application of a rule
when there is no loaded-path repeat and there is no free repeat.
For this we introduce `FreeRepeat` and the `flprep` abbreviation.
-/

/-- A free repeat is a non-loaded sequent that occured before. Values of this type are pairs:
the number of steps to go back in the history and a proof that we then find the same set. -/
def FreeRepeat (Hist : History) (X : Sequent) : Type :=
  Subtype (fun k => (Hist.get k) = X ∧ ¬ X.isLoaded)

lemma FreeRepeat_nil_impossible {X} : FreeRepeat [] X → False := by
  rintro ⟨n, n_h⟩
  grind

lemma FreeRepeat_iff_rep_and_isFree {H X} :
    Nonempty (FreeRepeat H X) ↔ rep H X ∧ X.isFree := by
  unfold rep
  constructor <;> intro hyp
  · rcases hyp with ⟨k,same, Xisl⟩
    unfold Sequent.isFree
    grind
  · rcases hyp with ⟨⟨Y, Y_in, bla⟩, Xfree⟩
    rcases List.get_of_mem Y_in with ⟨k, def_Y⟩
    constructor
    use k
    grind [Sequent.isFree]

/-- Either a free repeat or a loaded-path repeat.
Note that the negation of this is not the same as `¬ rep` because it will still allow
loaded repeats that are not loaded-path repeats, at which `Tableau` may continue.
See also `posOf` that is used to define `tableauGame` later. -/
@[grind .]
def flprep (H : History) (X : Sequent) : Prop :=
  (rep H X ∧ X.isFree) ∨ Nonempty (LoadedPathRepeat H X)

@[simp]
lemma flprep.nil_not : ¬ flprep [] X := by
  simp only [flprep, not_rep_empty, false_and, false_or, not_nonempty_iff]
  constructor
  rintro ⟨k, _, _⟩
  grind

/-! ## The PDL rules -/

/-- A rule to go from `X` to `Y`. Note the four variants of the modal rule. -/
@[grind]
inductive PdlRule : (X : Sequent) → (Y : Sequent) → Type
  -- The (L+) rule:
  | loadL {L δ α φ Y R} : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ L → ¬ φ.isBox
      → Y = (L.erase (~⌈⌈δ⌉⌉⌈α⌉φ), R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋φ)))) → PdlRule (L, R, none) Y
  | loadR {R δ α φ Y L} : (~⌈⌈δ⌉⌉⌈α⌉φ) ∈ R → ¬ φ.isBox
      → Y = (L, R.erase (~⌈⌈δ⌉⌉⌈α⌉φ), some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋φ)))) → PdlRule (L, R, none) Y
  -- The (L-) rule:
  | freeL {X L R δ α φ Y} :
        X = (L, R, some (Sum.inl (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
      → Y = (L ∪ {~⌈⌈δ⌉⌉⌈α⌉φ}, R, none)
      → PdlRule X Y
  | freeR {X L R δ α φ Y} :
        X = (L, R, some (Sum.inr (~'(⌊⌊δ⌋⌋⌊α⌋(φ : Formula)))))
      → Y = (L, R ∪ {~⌈⌈δ⌉⌉⌈α⌉φ}, none)
      → PdlRule X Y
  -- The (M) rule:
  | modL {Y L R A X ξ} :
        X = ⟨L, R, some (Sum.inl (~'⌊·A⌋(ξ : AnyFormula)))⟩
      → Y = ( match ξ with | .normal φ => ⟨{~φ} ∪ L.pdlProjection A, R.pdlProjection A, none⟩
                           | .loaded χ => ⟨L.pdlProjection A, R.pdlProjection A, some (Sum.inl
                             (~'χ))⟩ )
      → PdlRule X Y
  | modR {Y L R A X ξ} :
        X = ⟨L, R, some (Sum.inr (~'⌊·A⌋(ξ : AnyFormula)))⟩
      → Y = ( match ξ with | .normal φ => ⟨L.pdlProjection A, {~φ} ∪ R.pdlProjection A, none⟩
                           | .loaded χ => ⟨L.pdlProjection A, R.pdlProjection A, some (Sum.inr
                             (~'χ))⟩ )
      → PdlRule X Y
deriving DecidableEq

/-- Whether a PDL rule is one of the two modal rules. -/
@[expose] def PdlRule.isModal {X Y} : PdlRule X Y → Prop
| .loadL _ _ _ => False
| .loadR _ _ _ => False
| .freeL _ _ => False
| .freeR _ _ => False
| .modL _ _ => True
| .modR _ _ => True

instance instDecidablePdlRuleIsModal {X Y} {r : PdlRule X Y} : Decidable (r.isModal) := by
  cases r <;> simp only [PdlRule.isModal] <;> (try exact instDecidableFalse) <;> exact
    instDecidableTrue

/--
The `Tableau [parent, grandparent, ...] child` type.

This represents a closed tableau for `X`, constructed by either of:
- a local tableau for X followed by `Tableau` for all end nodes,
- a PDL rule application followed by `Tableau` for all results, or
- a loaded-path repeat (also called successful, see [MB1988] condition 6 in Def 14 on page 25).
-/
inductive Tableau : History → Sequent → Type
  | loc {Hist X} (nflprep : ¬ flprep Hist X) (nbas : ¬ X.basic) (lt : LocalTableau X)
            (next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y) : Tableau Hist X
  | pdl {Hist X Y} (nflprep : ¬ flprep Hist X) (bas : X.basic) (r : PdlRule X Y)
              (next : Tableau (X :: Hist) Y) : Tableau Hist X
  | lrep {Hist X} (lpr : LoadedPathRepeat Hist X) : Tableau Hist X

/-- The number of nodes in a tableau, including every local-rule continuation. -/
@[expose] def Tableau.size {Hist X} : Tableau Hist X → Nat
  | .loc _ _ lt next => 1 + ((endNodesOf lt).attach.sum (fun ⟨Y, Y_in⟩ => (next Y Y_in).size))
  | .pdl _ _ _ next => 1 + next.size
  | .lrep _ => 1

lemma Tableau.size_next_lt_of_loc {Hist X} {tab : Tableau Hist X}
    {nrep : ¬ flprep Hist X} {nbas : ¬ X.basic} {lt : LocalTableau X}
    {next : ∀ Y ∈ endNodesOf lt, Tableau (X :: Hist) Y}
    (tab_def : tab = Tableau.loc nrep nbas lt next) Y Y_in
    : (next Y Y_in).size < tab.size := by
  subst tab_def
  simp only [size]
  rw [@Nat.lt_one_add_iff]
  exact Finset.single_le_sum (f := fun x : {x // x ∈ endNodesOf lt} => (next x.1 x.2).size)
    (fun _ _ => Nat.zero_le _) (Finset.mem_attach _ ⟨Y, Y_in⟩)

lemma Tableau.size_next_lt_of_pdl {Hist X Y} {tab : Tableau Hist X}
    {nrep : ¬ flprep Hist X} {bas : X.basic} {r : PdlRule X Y}
    {next : Tableau (X :: Hist) Y}
    (tab_def : tab = Tableau.pdl nrep bas r next)
    : next.size < tab.size := by
  simp_all [Tableau.size]

/-- Decide an existential predicate over the end nodes of a local tableau. -/
def decidableExistsEndNodeOf {X} {lt : LocalTableau X}
    {f : (Y : Sequent) → Y ∈ endNodesOf lt → Prop}
    {dec : (Y : Sequent) → (Y_in : Y ∈ endNodesOf lt) → Decidable (f Y Y_in)} :
    Decidable (∃ Y, ∃ Y_in : Y ∈ endNodesOf lt, f Y Y_in) := by
  have : DecidablePred (fun x : {x // x ∈ endNodesOf lt} => f x.1 x.2) :=
    fun x => dec x.1 x.2
  refine decidable_of_iff (∃ x ∈ (endNodesOf lt).attach, f x.1 x.2) ?_
  simp

@[instance_reducible]
instance Tableau.instDecidableEq {Hist X} {tab1 tab2 : Tableau Hist X} :
    Decidable (tab1 = tab2) := by
  rcases tab1_def : tab1 with (⟨nrep1,nbas1,lt1,next1⟩|@⟨_,X2,Y2,nrep2,bas2,r2,next2⟩|_)
  all_goals
    rcases tab2 with (⟨nrep2,nbas2,lt2,next2⟩|@⟨_,X1,Y1,nrep1,bas1,r1,next1⟩|_)
  · by_cases h : lt1 = lt2
    · subst h
      simp only [loc.injEq, heq_eq_eq, true_and]
      have := fun (Y : Sequent) (Y_in : Y ∈ endNodesOf lt1) =>
        @Tableau.instDecidableEq _ _ (next1 Y Y_in) (next2 Y Y_in)
      have : Decidable (∃ Y, ∃ Y_in : Y ∈ endNodesOf lt1, next1 Y Y_in ≠ next2 Y Y_in) := by
        apply decidableExistsEndNodeOf
        intro Y Y_in
        simp only [ne_eq]
        exact @instDecidableNot _ (this Y Y_in)
      by_cases ∃ Y, ∃ Y_in : Y ∈ endNodesOf lt1, next1 Y Y_in ≠ next2 Y Y_in
      · apply isFalse; aesop
      · apply isTrue; aesop
    · apply isFalse; aesop
  all_goals
    try simp_all only [reduceCtorEq, pdl.injEq, lrep.injEq]
    try exact instDecidableFalse
    try exact instDecidableTrue
    try infer_instance
  case pdl.pdl =>
    by_cases h : Y1 = Y2
    · subst h
      simp_all only [not_false_eq_true, heq_eq_eq, true_and]
      by_cases h : r2 = r1
      · subst h
        simp only [true_and]
        apply Tableau.instDecidableEq
      · apply isFalse
        tauto
    · apply isFalse
      tauto
termination_by
  -- Note: cannot use DM ordering here, because PDL rules (L+) and (L-) do not decrease it.
  tab1.size
decreasing_by
  · exact Tableau.size_next_lt_of_loc tab1_def Y Y_in
  · exact Tableau.size_next_lt_of_pdl tab1_def

/-- Whether a tableau is a loaded-path-repeat leaf. -/
@[expose] def Tableau.isLrep {Hist X} : (Tableau Hist X) → Prop
  | .loc .. => False
  | .pdl .. => False
  | .lrep .. => True

/-- Provability witnessed by a tableau closing the negation on either side. -/
inductive provable : Formula → Prop
  | byTableauL {φ : Formula} : Tableau .nil ⟨{~φ}, {}, none⟩ → provable φ
  | byTableauR {φ : Formula} : Tableau .nil ⟨{}, {~φ}, none⟩ → provable φ

/-- A Sequent is inconsistent if there exists a closed tableau for it. -/
@[expose] def inconsistent : Sequent → Prop
  | LR => Nonempty (Tableau .nil LR)

/-- A `Sequent` is consistent iff it is not inconsistent. -/
@[expose] def consistent : Sequent → Prop
  | LR => ¬inconsistent LR

end PDL
