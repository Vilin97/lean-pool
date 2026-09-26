/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.List.ReduceOption

public import LeanPool.PDL.Local.Tableau

/-! # Generating all Local Tableaux

We show that for any `X` the type `LocalTableau` is finite.

This is needed to define `BuildTree` as a finite tree.
-/

public section

namespace PDL

/-! ## Helpers about `Finset.pdlSort` -/

namespace Finset

lemma pdlSort_toFinset (X : Finset Formula) : X.pdlSort.toFinset = X := by
  ext φ; simp [Finset.pdlSort]

@[simp]
lemma pdlSort_singleton (a : Formula) : ({a} : Finset Formula).pdlSort = [a] :=
  Finset.sort_singleton ..

lemma length_pdlSort (X : Finset Formula) : X.pdlSort.length = X.card := Finset.length_sort ..

lemma pdlSort_nodup (X : Finset Formula) : X.pdlSort.Nodup := Finset.sort_nodup ..

end Finset

lemma pdlSort_eq_singleton {X : Finset Formula} {a} (h : X.pdlSort = [a]) : X = {a} := by
  rw [← Finset.pdlSort_toFinset X, h]; simp

lemma pdlSort_eq_pair {X : Finset Formula} {a b} (h : X.pdlSort = [a, b]) : X = {a, b} := by
  rw [← Finset.pdlSort_toFinset X, h]; simp

/-- A sublist of the sorted version of `L` gives a subset of `L`. -/
lemma sublist_pdlSort_toFinset_subset {L : Finset Formula} {l : List Formula}
    (h : l.Sublist L.pdlSort) : l.toFinset ⊆ L := by
  intro x hx
  rw [List.mem_toFinset] at hx
  exact Formula.mem_pdlSort.mp (h.subset hx)

/-- Any subset of `L` arises from a sublist of the sorted version of `L`. -/
lemma exists_sublist_pdlSort_of_subset {L Lcond : Finset Formula} (h : Lcond ⊆ L) :
    ∃ l ∈ L.pdlSort.sublists, l.toFinset = Lcond := by
  refine ⟨L.pdlSort.filter (fun x => decide (x ∈ Lcond)),
          List.mem_sublists.mpr List.filter_sublist, ?_⟩
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Formula.mem_pdlSort]
  exact ⟨fun hx => hx.2, fun hx => ⟨h hx, hx⟩⟩

lemma Olf.subset_self (o : Olf) : o ⊆ o := by cases o <;> simp

lemma Olf.none_subset (o : Olf) : (none : Olf) ⊆ o := by simp

lemma Formula.ne_neg (φ : Formula) : φ ≠ ~φ := by
  intro h; have := congrArg sizeOf h; simp at this

lemma Formula.ne_neg_neg (φ : Formula) : φ ≠ ~~φ := by
  intro h; have := congrArg sizeOf h; simp at this; omega

/-- If `{φ, ~φ} = {a, b}` with `a ≠ b` then the pair is one of the two obvious ones. -/
lemma pair_neg_cases {φ a b : Formula} (h : ({φ, ~φ} : Finset Formula) = {a, b}) (hab : a ≠ b) :
    (a = φ ∧ b = ~φ) ∨ (a = ~φ ∧ b = φ) := by
  have ha : a ∈ ({φ, ~φ} : Finset Formula) := by rw [h]; simp
  have hb : b ∈ ({φ, ~φ} : Finset Formula) := by rw [h]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
  · exact absurd rfl hab
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hab

/-! ## All one-sided local rules -/

/-- Transport a `OneSidedLocalRule` along an equality of preconditions. -/
@[expose]
def osrCast {L L' B} (h : L = L') (r : OneSidedLocalRule L' B) : OneSidedLocalRule L B := by
  rw [h]; exact r

@[simp]
lemma osrCast_self {L B} (h : L = L) (r : OneSidedLocalRule L B) : osrCast h r = r := rfl

/-- Given the sorted list of the formulas in `L`, is there a `OneSidedLocalRule` for `L`?
The pair case comes first so that the equations below hold by `rfl`. -/
@[expose]
def OneSidedLocalRule.ofSorted : (L : Finset Formula) → (l : List Formula) → L.pdlSort = l →
    Option (Σ B, OneSidedLocalRule L B)
  | _, [a, b], h     => if hb : b = ~a
                        then some ⟨_, osrCast (by rw [pdlSort_eq_pair h, hb]) (.not a)⟩
                        else if ha : a = ~b
                        then some ⟨_, osrCast (by rw [pdlSort_eq_pair h, ha, Finset.pair_comm])
                                        (.not b)⟩
                        else none
  | _, [.bottom], h  => some ⟨_, osrCast (pdlSort_eq_singleton h) .bot⟩
  | _, [~~φ], h      => some ⟨_, osrCast (pdlSort_eq_singleton h) (.neg φ)⟩
  | _, [φ ⋀ ψ], h    => some ⟨_, osrCast (pdlSort_eq_singleton h) (.con φ ψ)⟩
  | _, [~(φ ⋀ ψ)], h => some ⟨_, osrCast (pdlSort_eq_singleton h) (.nCo φ ψ)⟩
  | _, [⌈α⌉φ], h     => if notAtm : ¬ α.isAtomic
                        then some ⟨_, osrCast (pdlSort_eq_singleton h) (.box α φ notAtm)⟩ else none
  | _, [~⌈α⌉φ], h    => if notAtm : ¬ α.isAtomic
                        then some ⟨_, osrCast (pdlSort_eq_singleton h) (.dia α φ notAtm)⟩ else none
  | _, _, _ => none

namespace OneSidedLocalRule

lemma ofSorted_pair {L a b} (h : L.pdlSort = [a, b]) :
    ofSorted L [a, b] h
      = if hb : b = ~a then some ⟨_, osrCast (by rw [pdlSort_eq_pair h, hb]) (.not a)⟩
        else if ha : a = ~b
        then some ⟨_, osrCast (by rw [pdlSort_eq_pair h, ha, Finset.pair_comm]) (.not b)⟩
        else none := rfl

lemma ofSorted_bot {L} (h : L.pdlSort = [⊥]) :
    ofSorted L [⊥] h = some ⟨_, osrCast (pdlSort_eq_singleton h) .bot⟩ := rfl

lemma ofSorted_neg {L φ} (h : L.pdlSort = [~~φ]) :
    ofSorted L [~~φ] h = some ⟨_, osrCast (pdlSort_eq_singleton h) (.neg φ)⟩ := rfl

lemma ofSorted_con {L φ ψ} (h : L.pdlSort = [φ ⋀ ψ]) :
    ofSorted L [φ ⋀ ψ] h = some ⟨_, osrCast (pdlSort_eq_singleton h) (.con φ ψ)⟩ := rfl

lemma ofSorted_nCo {L φ ψ} (h : L.pdlSort = [~(φ ⋀ ψ)]) :
    ofSorted L [~(φ ⋀ ψ)] h = some ⟨_, osrCast (pdlSort_eq_singleton h) (.nCo φ ψ)⟩ := rfl

lemma ofSorted_box {L α φ} (h : L.pdlSort = [⌈α⌉φ]) :
    ofSorted L [⌈α⌉φ] h
      = if notAtm : ¬ α.isAtomic
        then some ⟨_, osrCast (pdlSort_eq_singleton h) (.box α φ notAtm)⟩ else none := rfl

lemma ofSorted_dia {L α φ} (h : L.pdlSort = [~⌈α⌉φ]) :
    ofSorted L [~⌈α⌉φ] h
      = if notAtm : ¬ α.isAtomic
        then some ⟨_, osrCast (pdlSort_eq_singleton h) (.dia α φ notAtm)⟩ else none := rfl

/-- Is there a `OneSidedLocalRule` applicable to `L`? -/
@[expose]
def all (L : Finset Formula) : Option (Σ B, OneSidedLocalRule L B) := ofSorted L L.pdlSort rfl

lemma all_eq_ofSorted {L l} (h : L.pdlSort = l) : all L = ofSorted L l h := by cases h; rfl

lemma all_spec {L B} (osr : OneSidedLocalRule L B) : all L = some ⟨B, osr⟩ := by
  cases osr
  case bot => rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_bot]; simp
  case neg φ => rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_neg]; simp
  case con φ ψ => rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_con]; simp
  case nCo φ ψ => rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_nCo]; simp
  case box α φ notAtm =>
    rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_box, dite_eq_left notAtm]
    simp only [osrCast_self]
  case dia α φ notAtm =>
    rw [all_eq_ofSorted (Finset.pdlSort_singleton _), ofSorted_dia, dite_eq_left notAtm]
    simp only [osrCast_self]
  case not φ =>
    have hne : φ ≠ ~φ := Formula.ne_neg φ
    have hlen : (({φ, ~φ} : Finset Formula)).pdlSort.length = 2 := by
      rw [Finset.length_pdlSort, Finset.card_pair hne]
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    have hne2 : a ≠ b := by
      have := Finset.pdlSort_nodup ({φ, ~φ} : Finset Formula)
      rw [hab] at this; simpa using this
    have hset := pdlSort_eq_pair hab
    rw [all_eq_ofSorted hab, ofSorted_pair]
    rcases pair_neg_cases hset hne2 with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · subst ha'; subst hb'; rw [dite_eq_left rfl]; simp
    · subst hb'; subst ha'
      rw [dite_eq_right (Formula.ne_neg_neg _), dite_eq_left rfl]; simp

end OneSidedLocalRule

instance OneSidedLocalRule.fintype {L B} : Fintype (OneSidedLocalRule L B) :=
  match h_all: OneSidedLocalRule.all L with
  | some ⟨B', osr⟩ => ⟨ if h : B = B' then {h ▸ osr} else {}
                      , fun osr' => by have := OneSidedLocalRule.all_spec osr'; grind ⟩
  | none => ⟨{}, fun osr => by have := OneSidedLocalRule.all_spec osr; grind⟩

/-! ## All load rules -/

/-- Given a negated loaded formula, is there a LoadRule applicable to it? -/
def LoadRule.the : (nχ : NegLoadFormula) → Option (Σ ress, LoadRule nχ ress)
  | (~'⌊α⌋(.loaded _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia  notAtom⟩ else none
  | (~'⌊α⌋(.normal _)) => if notAtom : ¬ α.isAtomic then some ⟨_, dia' notAtom⟩ else none

lemma LoadRule.the_spec {χ ress} (lor : LoadRule (~'χ) ress) :
    some ⟨ress, lor⟩ = LoadRule.the (~'χ) := by
  cases lor
  all_goals
    simp only [List.pdlToFinFinOpt, the, dite_not, right_eq_dite_iff, reduceCtorEq, imp_false]
    assumption

instance LoadRule.fintype {nχ ress} : Fintype (LoadRule nχ ress) :=
  match h_the : LoadRule.the (~'nχ.1) with
  | some ⟨ress', lr⟩ => ⟨ if h : ress = ress' then {h ▸ lr} else {}
                        , fun lr' => by have := lr'.the_spec; grind ⟩
  | none => ⟨{}, fun lr => by have := lr.the_spec; grind⟩

/-! ## All local rules -/

/-- Transport a `LocalRule` along an equality of the conditions. -/
@[expose] def lrCast {c c' ress} (h : c = c') (r : LocalRule c' ress) : LocalRule c ress := by
  rw [h]; exact r

@[simp]
lemma lrCast_self {c ress} (h : c = c) (r : LocalRule c ress) : lrCast h r = r := rfl

/-- Helper for `LocalRule.all`, dealing with the two closing rules `LRnegL` and `LRnegR`. -/
@[expose] def LocalRule.negPairOf : (L R : Finset Formula) → (lL lR : List Formula) →
    L.pdlSort = lL → R.pdlSort = lR → Option (Σ ress, LocalRule (L, R, none) ress)
  | _, _, [φ1], [φ2], hL, hR =>
      if h : φ2 = ~φ1 then
        some ⟨_, lrCast (by rw [pdlSort_eq_singleton hL, pdlSort_eq_singleton hR, h]) (.LRnegL φ1)⟩
      else if h : φ1 = ~φ2 then
        some ⟨_, lrCast (by rw [pdlSort_eq_singleton hL, pdlSort_eq_singleton hR, h]) (.LRnegR φ2)⟩
      else none
  | _, _, _, _, _, _ => none

lemma LocalRule.negPairOf_singletons {L R φ1 φ2} (hL : L.pdlSort = [φ1]) (hR : R.pdlSort = [φ2]) :
    LocalRule.negPairOf L R [φ1] [φ2] hL hR
      = if h : φ2 = ~φ1 then
          some ⟨_, lrCast (by rw [pdlSort_eq_singleton hL, pdlSort_eq_singleton hR, h]) (.LRnegL
            φ1)⟩
        else if h : φ1 = ~φ2 then
          some ⟨_, lrCast (by rw [pdlSort_eq_singleton hL, pdlSort_eq_singleton hR, h]) (.LRnegR
            φ2)⟩
        else none := rfl

/-- Given a subsequent `cond` to be replaced, is there an applicable local rule?
Note that `cond` are only the principal formulas, not the whole sequent. -/
@[expose] def LocalRule.all : (cond : Sequent) → Option (Σ ress, LocalRule cond ress)
  | (L, R, none) =>
      if hR : R = ∅ then
        (OneSidedLocalRule.all L).map
          (fun ⟨_, orule⟩ => ⟨_, lrCast (by rw [hR]) (LocalRule.oneSidedL orule rfl)⟩)
      else if hL : L = ∅ then
        (OneSidedLocalRule.all R).map
          (fun ⟨_, orule⟩ => ⟨_, lrCast (by rw [hL]) (LocalRule.oneSidedR orule rfl)⟩)
      else LocalRule.negPairOf L R L.pdlSort R.pdlSort rfl rfl
  | (L, R, some (Sum.inl (~'⌊α⌋ξ))) =>
      if hL : L = ∅ then
        if hR : R = ∅ then
          match ξ with
          | .loaded χ => if notAtm : ¬ α.isAtomic
              then some ⟨_, lrCast (by rw [hL, hR]) (.loadedL _ (@LoadRule.dia α χ notAtm) rfl)⟩
              else none
          | .normal φ => if notAtm : ¬ α.isAtomic
              then some ⟨_, lrCast (by rw [hL, hR]) (.loadedL _ (@LoadRule.dia' α φ notAtm) rfl)⟩
              else none
        else none
      else none
  | (L, R, some (Sum.inr (~'⌊α⌋ξ))) =>
      if hL : L = ∅ then
        if hR : R = ∅ then
          match ξ with
          | .loaded χ => if notAtm : ¬ α.isAtomic
              then some ⟨_, lrCast (by rw [hL, hR]) (.loadedR _ (@LoadRule.dia α χ notAtm) rfl)⟩
              else none
          | .normal φ => if notAtm : ¬ α.isAtomic
              then some ⟨_, lrCast (by rw [hL, hR]) (.loadedR _ (@LoadRule.dia' α φ notAtm) rfl)⟩
              else none
        else none
      else none

lemma LocalRule.all_none (L R : Finset Formula) :
    LocalRule.all (L, R, none) =
      (if hR : R = ∅ then
        (OneSidedLocalRule.all L).map
          (fun ⟨_, orule⟩ => ⟨_, lrCast (by rw [hR]) (LocalRule.oneSidedL orule rfl)⟩)
      else if hL : L = ∅ then
        (OneSidedLocalRule.all R).map
          (fun ⟨_, orule⟩ => ⟨_, lrCast (by rw [hL]) (LocalRule.oneSidedR orule rfl)⟩)
      else LocalRule.negPairOf L R L.pdlSort R.pdlSort rfl rfl) := rfl

lemma LocalRule.all_inl_loaded (L R : Finset Formula) (α χ) :
    LocalRule.all (L, R, some (Sum.inl (~'⌊α⌋(AnyFormula.loaded χ)))) =
      (if hL : L = ∅ then
        if hR : R = ∅ then
          if notAtm : ¬ α.isAtomic
            then some ⟨_, lrCast (by rw [hL, hR]) (.loadedL _ (@LoadRule.dia α χ notAtm) rfl)⟩
            else none
        else none
      else none) := rfl

lemma LocalRule.all_inl_normal (L R : Finset Formula) (α φ) :
    LocalRule.all (L, R, some (Sum.inl (~'⌊α⌋(AnyFormula.normal φ)))) =
      (if hL : L = ∅ then
        if hR : R = ∅ then
          if notAtm : ¬ α.isAtomic
            then some ⟨_, lrCast (by rw [hL, hR]) (.loadedL _ (@LoadRule.dia' α φ notAtm) rfl)⟩
            else none
        else none
      else none) := rfl

lemma LocalRule.all_inr_loaded (L R : Finset Formula) (α χ) :
    LocalRule.all (L, R, some (Sum.inr (~'⌊α⌋(AnyFormula.loaded χ)))) =
      (if hL : L = ∅ then
        if hR : R = ∅ then
          if notAtm : ¬ α.isAtomic
            then some ⟨_, lrCast (by rw [hL, hR]) (.loadedR _ (@LoadRule.dia α χ notAtm) rfl)⟩
            else none
        else none
      else none) := rfl

lemma LocalRule.all_inr_normal (L R : Finset Formula) (α φ) :
    LocalRule.all (L, R, some (Sum.inr (~'⌊α⌋(AnyFormula.normal φ)))) =
      (if hL : L = ∅ then
        if hR : R = ∅ then
          if notAtm : ¬ α.isAtomic
            then some ⟨_, lrCast (by rw [hL, hR]) (.loadedR _ (@LoadRule.dia' α φ notAtm) rfl)⟩
            else none
        else none
      else none) := rfl

lemma OneSidedLocalRule.precond_ne_empty {P B} (osr : OneSidedLocalRule P B) : P ≠ ∅ := by
  cases osr <;> simp

lemma LocalRule.negPairOf_eq {L R lL lR} (hL : L.pdlSort = lL) (hR : R.pdlSort = lR) :
    LocalRule.negPairOf L R L.pdlSort R.pdlSort rfl rfl = LocalRule.negPairOf L R lL lR hL hR := by
  cases hL; cases hR; rfl

lemma LocalRule.all_spec {L B} (lr : LocalRule L B) : ⟨B, lr⟩ ∈ LocalRule.all L := by
  cases lr
  case oneSidedL precond ress orule YS_def =>
    subst YS_def
    rw [LocalRule.all_none, dite_eq_left rfl, OneSidedLocalRule.all_spec orule]
    simp
  case oneSidedR precond ress orule YS_def =>
    subst YS_def
    rw [LocalRule.all_none, dite_eq_right orule.precond_ne_empty, dite_eq_left rfl,
      OneSidedLocalRule.all_spec orule]
    simp
  case LRnegL φ =>
    rw [LocalRule.all_none, dite_eq_right (by simp), dite_eq_right (by simp),
      LocalRule.negPairOf_eq (Finset.pdlSort_singleton φ) (Finset.pdlSort_singleton (~φ)),
      LocalRule.negPairOf_singletons, dite_eq_left rfl]
    simp
  case LRnegR φ =>
    rw [LocalRule.all_none, dite_eq_right (by simp), dite_eq_right (by simp),
      LocalRule.negPairOf_eq (Finset.pdlSort_singleton (~φ)) (Finset.pdlSort_singleton φ),
      LocalRule.negPairOf_singletons, dite_eq_right (Formula.ne_neg_neg φ), dite_eq_left rfl]
    simp
  case loadedL χ lrule YS_def =>
    subst YS_def
    rcases χ with ⟨α, ξ⟩
    cases lrule
    case dia χ notAtm =>
      rw [LocalRule.all_inl_loaded, dite_eq_left rfl, dite_eq_left rfl, dite_eq_left notAtm]
      simp
    case dia' φ notAtm =>
      rw [LocalRule.all_inl_normal, dite_eq_left rfl, dite_eq_left rfl, dite_eq_left notAtm]
      simp
  case loadedR χ lrule YS_def =>
    subst YS_def
    rcases χ with ⟨α, ξ⟩
    cases lrule
    case dia χ notAtm =>
      rw [LocalRule.all_inr_loaded, dite_eq_left rfl, dite_eq_left rfl, dite_eq_left notAtm]
      simp
    case dia' φ notAtm =>
      rw [LocalRule.all_inr_normal, dite_eq_left rfl, dite_eq_left rfl, dite_eq_left notAtm]
      simp

instance LocalRule.fintype {X ress} : Fintype (LocalRule X ress) :=
  match h_the : LocalRule.all X with
  | some ⟨ress', lr⟩ => ⟨ if h : ress = ress' then {h ▸ lr} else {}
                        , fun lr' => by have := lr'.all_spec; grind ⟩
  | none => ⟨{}, fun lr => by have := lr.all_spec; grind⟩

/-! ## All local rule applications -/

/-- Given a sequent, return a list of all possible local rule applications. -/
def LocalRuleApp.all : (X : Sequent) → List LocalRuleApp
  | ⟨L, R, o⟩ =>
      -- The `preconditionProof` in `LocalRuleApp` now uses `⊆`, so we can use `Finset.powerset`.
      let conds : List Sequent :=
        (L.pdlSort.sublists.map List.toFinset).flatMap (fun Lcond =>
          (R.pdlSort.sublists.map List.toFinset).flatMap (fun Rcond =>
            ([none, o] : List Olf).map (fun Ocond => ((Lcond, Rcond, Ocond) : Sequent))))
      (conds.attach.map (fun ⟨⟨Lcond, Rcond, Ocond⟩, cond_in⟩ =>
        (LocalRule.all ⟨Lcond, Rcond, Ocond⟩).map
          (fun ⟨_, lr⟩ =>
            have h : Lcond ⊆ L ∧ Rcond ⊆ R ∧ Ocond ⊆ o := by
              simp only [conds, List.mem_flatMap, List.mem_map, List.mem_sublists,
                List.mem_cons, List.not_mem_nil, or_false] at cond_in
              obtain ⟨lL, ⟨l, l_sub, rfl⟩, lR, ⟨r, r_sub, rfl⟩, Oc, Oc_def, hcond⟩ := cond_in
              obtain ⟨rfl, rfl, rfl⟩ := hcond
              refine ⟨sublist_pdlSort_toFinset_subset l_sub, sublist_pdlSort_toFinset_subset
                r_sub, ?_⟩
              rcases Oc_def with rfl | rfl
              · exact Olf.none_subset _
              · exact Olf.subset_self _
            { L := L, R := R, O := o, preconditionProof := h, Lcond := Lcond, Rcond := Rcond,
              Ocond := Ocond, lr := lr, ress := _ }
            ))).reduceOption

lemma LocalRuleApp.all_X (X : Sequent) : ∀ lra ∈ LocalRuleApp.all X, lra.X = X := by
  intro lra lra_in
  rcases X with ⟨L, R, O⟩
  simp only [all, List.reduceOption_mem_iff, List.mem_map, List.mem_attach, true_and,
    Subtype.exists, List.mem_flatMap, List.mem_sublists, List.mem_cons,
    List.not_mem_nil, or_false] at lra_in
  grind [Option.map_eq_some_iff]

lemma LocalRuleApp.all_spec (lrA : LocalRuleApp) : lrA ∈ LocalRuleApp.all lrA.X := by
  rcases lrA with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, ⟨hL, hR, hO⟩⟩
  subst hC
  simp only [LocalRuleApp.all, List.reduceOption_mem_iff, List.mem_map,
    List.mem_attach, true_and, Subtype.exists, List.mem_flatMap, List.mem_sublists,
    List.mem_cons, List.not_mem_nil, or_false]
  obtain ⟨l, l_mem, l_def⟩ := exists_sublist_pdlSort_of_subset hL
  obtain ⟨r, r_mem, r_def⟩ := exists_sublist_pdlSort_of_subset hR
  rw [List.mem_sublists] at l_mem r_mem
  have hOc : Ocond = none ∨ Ocond = O := by
    cases Ocond with
    | none => exact Or.inl rfl
    | some x => right; cases O <;> simp_all
  refine ⟨(Lcond, Rcond, Ocond),
    ⟨Lcond, ⟨l, l_mem, l_def⟩, Rcond, ⟨r, r_mem, r_def⟩, Ocond, hOc, rfl⟩, ?_⟩
  simp only []
  rw [Option.mem_def.mp (LocalRule.all_spec lr)]
  rfl

lemma LocalRuleApp.all_nonempty_of_nonbasic {X : Sequent} (X_nonbas : ¬ X.basic) :
    LocalRuleApp.all X ≠ [] := by
  rw [@basic_iff_noLocalRuleApp X] at X_nonbas
  simp only [not_exists, not_forall, Decidable.not_not] at X_nonbas
  rcases X_nonbas with ⟨lra, def_X⟩
  have := LocalRuleApp.all_spec lra
  grind

/-! ## Termination measure for local tableaux -/

/-- The formula-length measure of the optional loading. -/
@[simp]
def lmOfOlf : Olf → Nat
| none => 0
| some (Sum.inl nlf) => lmOfFormula (negUnload nlf)
| some (Sum.inr nlf) => lmOfFormula (negUnload nlf)

/-- Local measure of a sequent: the sum of `lmOfFormula` over all three components. -/
def lmOfSequent (X : Sequent) : Nat :=
  (∑ φ ∈ X.1, lmOfFormula φ) + (∑ φ ∈ X.2.1, lmOfFormula φ) + lmOfOlf X.2.2

/-- Local measure of an optional negated loaded formula. -/
def lmOfONlf : Option NegLoadFormula → Nat
| none => 0
| some nlf => lmOfFormula (negUnload nlf)

/-! ### Helpers to show that local rules decrease the measure -/

/-- The measure sum over a union is at most the sum of the measure sums. -/
lemma lm_sum_union_le (A B : Finset Formula) :
    ∑ φ ∈ A ∪ B, lmOfFormula φ ≤ (∑ φ ∈ A, lmOfFormula φ) + ∑ φ ∈ B, lmOfFormula φ := by
  rw [← Finset.sum_sdiff (Finset.subset_union_left (s₁ := A) (s₂ := B)), add_comm]
  exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset
    (by intro x hx; simp only [Finset.mem_sdiff, Finset.mem_union] at hx; tauto)) _

/-- For `(F,δ) ∈ Dset α` the measure sum over `F` is at most the test measure of `α`. -/
lemma lm_sum_Dset_le_tests {α : Program} {F : List Formula} {δ : List Program}
    (in_D : (F, δ) ∈ Dset α) :
    ∑ ψ ∈ F.toFinset, lmOfFormula ψ
      ≤ ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum := by
  have tri : ∀ x ∈ F, x = ⊥ ∨ x ∈ testsOfProgram α ∨ lmOfFormula x = 0 := by
    intro x hx
    rcases Dset_mem_test α x in_D hx with ⟨τ, τ_in, rfl⟩
    exact Or.inr (Or.inl τ_in)
  have := finset_sum_trichotomy lmOfFormula F ⊥ (testsOfProgram α) tri
  have hbot : lmOfFormula ⊥ = 0 := by simp [Bot.bot, lmOfFormula]
  simp only [List.map_subtype, List.unattach_attach]
  simpa [hbot] using this

/-- Unfolding the measure of a diamond with a non-atomic program. -/
lemma lm_dia_eq {α : Program} {φ : Formula} (h : ¬ α.isAtomic) :
    lmOfFormula (~⌈α⌉φ)
      = 1 + lmOfFormula (~φ) + ((testsOfProgram α).attach.map (fun τ => lmOfFormula τ.1)).sum := by
  cases α <;> simp_all [Program.isAtomic]

/-- One-sided local rules strictly decrease the measure sum. -/
lemma OneSidedLocalRule.decreases_lm {precond ress} (orule : OneSidedLocalRule precond ress) :
    ∀ res ∈ ress, ∑ φ ∈ res, lmOfFormula φ < ∑ φ ∈ precond, lmOfFormula φ := by
  intro res res_in
  cases orule
  case bot => simp at res_in
  case not φ => simp at res_in
  case neg φ =>
    simp only [Finset.mem_singleton] at res_in
    subst res_in
    simp
  case con φ ψ =>
    simp only [Finset.mem_singleton] at res_in
    subst res_in
    rcases eq_or_ne φ ψ with rfl | hne
    · simp
    · rw [Finset.sum_pair hne, Finset.sum_singleton]
      simp
  case nCo φ ψ =>
    simp only [Finset.mem_insert, Finset.mem_singleton] at res_in
    rcases res_in with rfl | rfl
    · simp; omega
    · simp
  case box a φ notAtom =>
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at res_in
    obtain ⟨X, X_in, rfl⟩ := res_in
    have := (@measureProp a φ ⊥ ⊥).2.2.2.2.1 notAtom X X_in
    simpa using this
  case dia a φ notAtom =>
    simp only [List.pdlToFinFin, List.mem_toFinset, List.mem_map] at res_in
    obtain ⟨X, X_in, rfl⟩ := res_in
    have := (@measureProp a φ ⊥ ⊥).2.2.2.2.2 notAtom X X_in
    simpa using this

/-- Loaded rules strictly decrease the measure: the new formulas together with the
new loaded formula have a smaller measure than the old loaded formula. -/
lemma LoadRule.decreases_lm {χ : LoadFormula} {ress} (lrule : LoadRule (~'χ) ress) :
    ∀ Fo ∈ ress, (∑ ψ ∈ (Fo.1 : Finset Formula), lmOfFormula ψ)
        + lmOfONlf Fo.2 < lmOfFormula (~χ.unload) := by
  intro Fo Fo_in
  cases lrule
  case dia α χ0 notAtom =>
    simp only [List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, unfoldDiamondLoaded,
      YsetLoad, Prod.exists] at Fo_in
    obtain ⟨F, o, ⟨F', δ, in_D, hFo⟩, rfl⟩ := Fo_in
    cases hFo
    have hsum := lm_sum_Dset_le_tests in_D
    have hunl : (⌊α⌋(AnyFormula.loaded χ0)).unload = ⌈α⌉χ0.unload := by simp [LoadFormula.unload]
    rw [hunl, lm_dia_eq notAtom]
    simp only [lmOfONlf, negUnload, unload_boxes]
    rcases Dset_mem_sequence α in_D with rfl | ⟨a, δ', rfl⟩
    · simp only [Formula.boxes_nil]
      omega
    · rw [show lmOfFormula (~⌈⌈(·a : Program) :: δ'⌉⌉χ0.unload) = 0 by simp [Formula.boxes]]
      omega
  case dia' α φ notAtom =>
    simp only [List.pdlToFinFinOpt, List.mem_toFinset, List.mem_map, unfoldDiamondLoaded',
      Prod.exists] at Fo_in
    obtain ⟨F, o, ⟨F', δ, in_D, hFo⟩, rfl⟩ := Fo_in
    have hsum := lm_sum_Dset_le_tests in_D
    have hunl : (⌊α⌋(AnyFormula.normal φ)).unload = ⌈α⌉φ := by simp [LoadFormula.unload]
    rw [hunl, lm_dia_eq notAtom]
    rcases hsl : splitLast δ with _ | ⟨δ0, β⟩ <;> simp only [YsetLoad', hsl] at hFo <;> cases hFo
    · have hun : ((F' ∪ [~φ]).toFinset : Finset Formula) = F'.toFinset ∪ {~φ} := by simp
      have := lm_sum_union_le F'.toFinset {~φ}
      simp only [lmOfONlf, hun, Finset.sum_singleton] at *
      omega
    · have hδ := splitLast_undo_of_some hsl
      simp only at hδ
      have hzero : lmOfFormula (~⌈⌈δ0⌉⌉⌈β⌉φ) = 0 := by
        rcases Dset_mem_sequence α in_D with rfl | ⟨a, δ', rfl⟩
        · simp at hδ
        · cases δ0 with
          | nil => simp_all [Formula.boxes]
          | cons γ rest => simp_all [Formula.boxes]
      simp only [lmOfONlf, negUnload, unload_loadMulti, hzero]
      omega

theorem localRuleApp.decreases_lm (lra : LocalRuleApp) (Y : Sequent) (h : Y ∈ lra.C) :
    lmOfSequent Y < lmOfSequent lra.X := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, rule, C, hC, ⟨hL, hR, hO⟩⟩
  subst hC
  simp only [LocalRuleApp.X] at *
  cases rule
  case oneSidedL ress' orule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.mem_image] at h
    obtain ⟨Z, Z_in, rfl⟩ := h
    obtain ⟨res, res_in, rfl⟩ := Z_in
    simp only [lmOfSequent, Olf.change_old_none_none, Finset.sdiff_empty, Finset.union_empty]
    have h1 := lm_sum_union_le (L \ Lcond) res
    have h2 := Finset.sum_sdiff (f := lmOfFormula) hL
    have h3 := orule.decreases_lm res res_in
    omega
  case oneSidedR ress' orule ress_def =>
    subst ress_def
    simp only [applyLocalRule, Finset.mem_image] at h
    obtain ⟨Z, Z_in, rfl⟩ := h
    obtain ⟨res, res_in, rfl⟩ := Z_in
    simp only [lmOfSequent, Olf.change_old_none_none, Finset.sdiff_empty, Finset.union_empty]
    have h1 := lm_sum_union_le (R \ Rcond) res
    have h2 := Finset.sum_sdiff (f := lmOfFormula) hR
    have h3 := orule.decreases_lm res res_in
    omega
  case LRnegL φ => simp at h
  case LRnegR φ => simp at h
  case loadedL ress' χ lrule ress_def =>
    subst ress_def
    rw [Option.some_subseteq] at hO
    subst hO
    simp only [applyLocalRule, Finset.mem_image] at h
    obtain ⟨Z, Z_in, rfl⟩ := h
    obtain ⟨Fo, Fo_in, rfl⟩ := Z_in
    have h1 := lm_sum_union_le L Fo.1
    have h3 := lrule.decreases_lm Fo Fo_in
    rcases Fo with ⟨F, o⟩
    cases o <;>
      simp_all only [lmOfSequent, lmOfONlf, Olf.change_some_some_eq, Finset.sdiff_empty,
        Finset.union_empty, lmOfOlf, negUnload, Option.map_none, Option.map_some] <;> omega
  case loadedR ress' χ lrule ress_def =>
    subst ress_def
    rw [Option.some_subseteq] at hO
    subst hO
    simp only [applyLocalRule, Finset.mem_image] at h
    obtain ⟨Z, Z_in, rfl⟩ := h
    obtain ⟨Fo, Fo_in, rfl⟩ := Z_in
    have h1 := lm_sum_union_le R Fo.1
    have h3 := lrule.decreases_lm Fo Fo_in
    rcases Fo with ⟨F, o⟩
    cases o <;>
      simp_all only [lmOfSequent, lmOfONlf, Olf.change_some_some_eq, Finset.sdiff_empty,
        Finset.union_empty, lmOfOlf, negUnload, Option.map_none, Option.map_some] <;> omega

/-! ## Generating all local tableaux -/

/-- Convert a function returning lists into a list of functions. Helper for `LocalTableau.all`. -/
def combo {α : Type} [DecidableEq α] {q : α → Type} : {L : List α}
    → (f : (x : α) → x ∈ L → List (q x))
    → List ((x : α) → x ∈ L → q x)
  | [], _ => [ fun x x_in => by exfalso; cases x_in ]
  | (x :: xs), f =>
      let IH : (y : α) → y ∈ xs → List (q y) := fun y y_in => f y (by aesop)
      let fx_choices := f x (by simp)
      (combo IH).flatMap (fun g =>
        fx_choices.map (fun fx =>
          fun y y_in =>
            if h : y = x then h ▸ fx else g y (by aesop)))

/-- Characterization of members of `combo` result. Could be strengthened to ↔ later. -/
lemma combo_mem_of_forall_in {α : Type} [DecidableEq α] {q : α → Type} {L : List α}
    (f : (x : α) → x ∈ L → List (q x))
    (g : (x : α) → x ∈ L → q x)
    : (∀ x x_in, g x x_in ∈ f x x_in) → g ∈ combo f := by
  intro hyp
  induction L
  · simp only [List.not_mem_nil, combo, List.mem_cons, or_false]
    ext x x_in
    cases x_in
  case cons x xs IH =>
    simp only [combo, List.mem_flatMap, List.mem_map]
    specialize IH (fun y y_in => f y (by aesop))
    exact ⟨fun y y_in => g _ (by simp_all), IH _ (by grind), (by grind)⟩

/-- Version of `combo` for `Finset`s. -/
def comboF {q : Sequent → Type} (s : Finset Sequent)
    (f : (x : Sequent) → x ∈ s → List (q x)) : List ((x : Sequent) → x ∈ s → q x) :=
  (combo (L := s.pdlSeqSort) (fun x hx => f x (by simp_all))).map
    (fun g x hx => g x (by simp_all))

lemma comboF_mem_of_forall_in {q : Sequent → Type} {s : Finset Sequent}
    (f : (x : Sequent) → x ∈ s → List (q x)) (g : (x : Sequent) → x ∈ s → q x)
    (h : ∀ x x_in, g x x_in ∈ f x x_in) : g ∈ comboF s f := by
  simp only [comboF, List.mem_map]
  exact ⟨fun x hx => g x (by simp_all),
         combo_mem_of_forall_in _ _ (fun x hx => h x _), rfl⟩

/-- Enumerate all local tableaux rooted at a sequent. -/
def LocalTableau.all : (X : Sequent) → List (LocalTableau X) := fun X =>
  if bas : X.basic
  then [ .sim bas ]
  else do
    let ⟨lra, lra_mem⟩ <- (LocalRuleApp.all X).attach
    have def_X := LocalRuleApp.all_X X _ lra_mem
    let tabsFor (Y : Sequent) (h : Y ∈ lra.C) : List (LocalTableau Y) := by
      have _forTermination := localRuleApp.decreases_lm lra _ h
      apply LocalTableau.all
    let nexts : List ((Y : Sequent) → Y ∈ lra.C → LocalTableau Y) := comboF lra.C tabsFor
    let next <- nexts
    return @byLocalRule X lra def_X.symm next
termination_by
  X => lmOfSequent X
decreasing_by
  exact def_X ▸ _forTermination

lemma LocalTableau.all_nonempty (X : Sequent) : LocalTableau.all X ≠ [] := by
  by_cases Xbas : X.basic
  · simp_all [LocalTableau.all]
  · unfold LocalTableau.all
    have := LocalRuleApp.all_nonempty_of_nonbasic Xbas
    simp_all only [ne_eq, ↓reduceDIte, List.pure_def, List.bind_eq_flatMap,
      List.flatMap_eq_nil_iff, List.mem_attach, List.cons_ne_self, imp_false, forall_const,
      Subtype.forall, not_forall, not_not]
    rcases List.exists_mem_of_ne_nil _ this with ⟨lra, lra_in⟩
    refine ⟨lra, lra_in, ?_⟩
    refine ⟨ (fun Y Y_in => (LocalTableau.all Y).head (LocalTableau.all_nonempty Y))
           , comboF_mem_of_forall_in _ _ ?_⟩
    intro Y Y_in
    exact List.head_mem (LocalTableau.all_nonempty Y)
termination_by
  lmOfSequent X
decreasing_by
  all_goals
    rw [← LocalRuleApp.all_X X lra lra_in]
    exact localRuleApp.decreases_lm lra Y Y_in

lemma LocalTableau.all_spec {X} {ltX : LocalTableau X} : ltX ∈ LocalTableau.all X := by
  by_cases Xbas : X.basic
  · unfold LocalTableau.all
    cases ltX
    case pos.byLocalRule lra next X_def =>
      absurd Xbas
      exact X_def ▸ nonbasic_of_localRuleApp lra
    · simp_all
  · unfold LocalTableau.all
    simp_all only [↓reduceDIte, List.pure_def, List.bind_eq_flatMap, List.mem_flatMap,
      List.mem_attach, List.mem_cons, List.not_mem_nil, or_false, true_and, Subtype.exists]
    cases ltX
    case neg.byLocalRule lra next X_def =>
      refine ⟨lra, X_def ▸ LocalRuleApp.all_spec lra, ?_⟩
      simp only [byLocalRule.injEq, heq_eq_eq, true_and, exists_eq_right']
      apply comboF_mem_of_forall_in
      intro Y Y_in
      apply LocalTableau.all_spec -- IH
    case neg.sim =>
      simp_all

instance LocalTableau.fintype {X} : Fintype (LocalTableau X) := by
  refine ⟨(LocalTableau.all X).toFinset, ?_⟩
  intro ltX
  rw [List.mem_toFinset]
  exact LocalTableau.all_spec

/-! # Generating all Open Local Tableaux -/

/-- Enumerate all local tableaux with at least one end node. -/
def OpenLocalTableau.all (X : Sequent) : List (OpenLocalTableau X) :=
  ((LocalTableau.all X).filter (endNodesOf · ≠ {})).attach.map (fun ⟨lt,h⟩ => ⟨lt, by simp_all⟩)

lemma OpenLocalTableau.all_spec {X : Sequent} {ltX : OpenLocalTableau X} :
    ltX ∈ OpenLocalTableau.all X := by
  rcases ltX with ⟨lt, lt_has_ends⟩
  have hmem : lt ∈ (LocalTableau.all X).filter (endNodesOf · ≠ {}) :=
    List.mem_filter.mpr ⟨LocalTableau.all_spec, decide_eq_true lt_has_ends⟩
  exact List.mem_map_of_mem (List.mem_attach _ ⟨lt, hmem⟩)

end PDL
