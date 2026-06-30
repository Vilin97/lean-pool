/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Misere.Universe

/-!
Misere combinatorial games.
-/

namespace MisereGames

universe u

variable {G : Type (u + 1)} [Form G]

open Form

public section

namespace Form

namespace Misere

namespace Preservation

/-!
## Preservation of closure properties

There are some preservation properties between the closure operators of
`CombinatorialGames.Misere.Closures`: for example, the hereditary closure of a
conjugate closed set is still conjugate closed. In particular, the four closure
properties can be chained together to obtain a universe
(`closureChain_universe`), and this chain in fact computes the universal
closure (`closureChain_eq_universeClosure`).
-/

-- Conjugating an option gives an option of the conjugate.
private theorem neg_isOption_of_isOption {g g' : G} (h : Moves.IsOption g' g) :
    Moves.IsOption (-g') (-g) := by
  rw [Moves.IsOption.iff_mem_union] at h ⊢
  simpa [moves_neg, Set.mem_neg, Set.union_comm] using h

-- Conjugating a subposition gives a subposition of the conjugate.
private theorem neg_subposition_of_subposition {g h : G} (hsub : Subposition h g) :
    Subposition (-h) (-g) := by
  induction hsub with
  | single hopt =>
      exact Relation.TransGen.single (neg_isOption_of_isOption hopt)
  | tail hsub hopt ih =>
      exact Relation.TransGen.tail ih (neg_isOption_of_isOption hopt)

-- An option of a sum comes from an option of one summand.
private theorem isOption_add_cases {g h x : G} (hx : Moves.IsOption x (g + h)) :
    (∃ g', Moves.IsOption g' g ∧ x = g' + h) ∨
      (∃ h', Moves.IsOption h' h ∧ x = g + h') := by
  rw [Moves.IsOption.iff_mem_union] at hx
  rcases hx with hx | hx <;>
    (rw [moves_add] at hx
     rcases hx with ⟨g', hg', hx⟩ | ⟨h', hh', hx⟩
     · exact Or.inl ⟨g', Moves.IsOption.of_mem_moves hg', hx.symm⟩
     · exact Or.inr ⟨h', Moves.IsOption.of_mem_moves hh', hx.symm⟩)

/-!
### The closures preservations
-/

/--
The hereditary closure of a conjugate closed set is conjugate closed.
-/
instance hereditaryClosure_closedUnderNeg {A : G → Prop} [ClosedUnderNeg A] :
    ClosedUnderNeg (Hereditary.closure A) where
  neg_of {g} hg := by
    let B : G → Prop := fun g => Hereditary.closure A (-g)
    haveI : Hereditary B := {
      has_option {g g'} hg h :=
        Hereditary.has_option_mem_closure hg (neg_isOption_of_isOption h)
    }
    have hAB : A ≤ B := by
      intro g hg
      exact Hereditary.mem_closure_of_mem (ClosedUnderNeg.neg_of hg)
    exact Hereditary.closure_min hAB g hg

/--
The conjugate closure of a hereditary set is hereditary.
-/
instance closedUnderNegClosure_hereditary {A : G → Prop} [Hereditary A] :
    Hereditary (ClosedUnderNeg.closure A) where
  has_option {g g'} hg h := by
    let B : G → Prop := fun g => ∀ g', Moves.IsOption g' g → ClosedUnderNeg.closure A g'
    haveI : ClosedUnderNeg B := {
      neg_of {g} hg g' h' := by
        have hneg : Moves.IsOption (-g') g := by
          simpa using neg_isOption_of_isOption h'
        simpa using ClosedUnderNeg.neg_mem_closure (hg (-g') hneg)
    }
    have hAB : A ≤ B := by
      intro g hg g' h'
      exact ClosedUnderNeg.mem_closure_of_mem (Hereditary.has_option hg h')
    exact ClosedUnderNeg.closure_min hAB g hg g' h

/--
Conjugate closure commutes with hereditary closure.
-/
theorem closedUnderNegClosure_hereditaryClosure_comm (A : G → Prop) :
    ClosedUnderNeg.closure (Hereditary.closure A) =
      Hereditary.closure (ClosedUnderNeg.closure A) := by
  apply le_antisymm
  · exact ClosedUnderNeg.closure_min
      (Hereditary.closure_mono (ClosedUnderNeg.subset_closure A))
  · exact Hereditary.closure_min
      (ClosedUnderNeg.closure_mono (Hereditary.subset_closure A))

/--
The additive closure of a hereditary set is hereditary.
-/
instance closedUnderSumClosure_hereditary {A : G → Prop} [Hereditary A] :
    Hereditary (ClosedUnderAdd.closure A) where
  has_option {g g'} hg h := by
    let B : G → Prop := fun g =>
      ClosedUnderAdd.closure A g ∧ ∀ g', Moves.IsOption g' g → ClosedUnderAdd.closure A g'
    haveI : ClosedUnderAdd B := {
      has_add g h hg hh := by
        constructor
        · exact ClosedUnderAdd.add_mem_closure hg.1 hh.1
        · intro x hx
          rcases isOption_add_cases hx with ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
          · exact ClosedUnderAdd.add_mem_closure (hg.2 g' hg') hh.1
          · exact ClosedUnderAdd.add_mem_closure hg.1 (hh.2 h' hh')
    }
    have hAB : A ≤ B := by
      intro g hg
      exact ⟨ClosedUnderAdd.mem_closure_of_mem hg, fun g' h' =>
        ClosedUnderAdd.mem_closure_of_mem (Hereditary.has_option hg h')⟩
    exact (ClosedUnderAdd.closure_min hAB g hg).2 g' h

/--
The additive closure of a conjugate closed set is conjugate closed.
-/
instance closedUnderSumClosure_closedUnderNeg {A : G → Prop} [ClosedUnderNeg A] :
    ClosedUnderNeg (ClosedUnderAdd.closure A) where
  neg_of {g} hg := by
    let B : G → Prop := fun g => ClosedUnderAdd.closure A (-g)
    haveI : ClosedUnderAdd B := {
      has_add g h hg hh := by
        change ClosedUnderAdd.closure A (-(g + h))
        rw [neg_add']
        exact ClosedUnderAdd.add_mem_closure hg hh
    }
    have hAB : A ≤ B := by
      intro g hg
      exact ClosedUnderAdd.mem_closure_of_mem (ClosedUnderNeg.neg_of hg)
    exact ClosedUnderAdd.closure_min hAB g hg

/--
The dicotic closure of a hereditary set is hereditary.
-/
instance closedUnderDicoticClosure_hereditary {IsAmbient A : G → Prop} [Hereditary A] :
    Hereditary (ClosedUnderDicotic.closure IsAmbient A) where
  has_option {g g'} hg h := by
    let B' : G → Prop := fun g =>
      ClosedUnderDicotic.closure IsAmbient A g ∧
        ∀ g', Moves.IsOption g' g → ClosedUnderDicotic.closure IsAmbient A g'
    haveI : ClosedUnderDicotic IsAmbient B' := {
      closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
        constructor
        · exact ClosedUnderDicotic.dicotic_mem_closure B C
            (fun b hb => (hB b hb).1) (fun c hc => (hC c hc).1) hBne hCne hAmbient
        · intro g' h'
          rw [Moves.IsOption.iff_mem_union] at h'
          rcases h' with h' | h'
          · rw [leftMoves_ofSets] at h'
            exact (hB g' h').1
          · rw [rightMoves_ofSets] at h'
            exact (hC g' h').1
    }
    have hAB : A ≤ B' := by
      intro g hg
      exact ⟨ClosedUnderDicotic.mem_closure_of_mem hg, fun g' h' =>
        ClosedUnderDicotic.mem_closure_of_mem (Hereditary.has_option hg h')⟩
    exact (ClosedUnderDicotic.closure_min hAB g hg).2 g' h

/--
The dicotic closure of a conjugate closed set is conjugate closed (when the
ambient set is conjugate closed).
-/
instance closedUnderDicoticClosure_closedUnderNeg {IsAmbient A : G → Prop}
    [ClosedUnderNeg IsAmbient] [ClosedUnderNeg A] :
    ClosedUnderNeg (ClosedUnderDicotic.closure IsAmbient A) where
  neg_of {g} hg := by
    let B' : G → Prop := fun g => ClosedUnderDicotic.closure IsAmbient A (-g)
    haveI : ClosedUnderDicotic IsAmbient B' := {
      closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
        change ClosedUnderDicotic.closure IsAmbient A (-!{B | C})
        rw [neg_ofSets]
        refine ClosedUnderDicotic.dicotic_mem_closure (-C) (-B) ?_ ?_ ?_ ?_ ?_
        · intro c hc
          rw [Set.mem_neg] at hc
          simpa [B'] using hC (-c) hc
        · intro b hb
          rw [Set.mem_neg] at hb
          simpa [B'] using hB (-b) hb
        · rcases hCne with ⟨c, hc⟩
          exact ⟨-c, by rw [Set.mem_neg]; simpa using hc⟩
        · rcases hBne with ⟨b, hb⟩
          exact ⟨-b, by rw [Set.mem_neg]; simpa using hb⟩
        · simpa [neg_ofSets] using ClosedUnderNeg.neg_of hAmbient
    }
    have hAB : A ≤ B' := by
      intro g hg
      exact ClosedUnderDicotic.mem_closure_of_mem (ClosedUnderNeg.neg_of hg)
    exact ClosedUnderDicotic.closure_min hAB g hg

/-!
### Dicotic closure preserves addition

This is slightly delicate: a sum need not be dicotic, so we consider cases
where it is end-like and recurse on options otherwise.
-/

-- A dicotic closure is contained in its ambient set when the generating set
-- is.
private theorem closedUnderDicoticClosure_le_ambient {IsAmbient A : G → Prop}
    (hA : A ≤ IsAmbient) :
    ClosedUnderDicotic.closure IsAmbient A ≤ IsAmbient := by
  haveI : ClosedUnderDicotic IsAmbient IsAmbient := {
    closed_dicotic _ _ _ _ _ _ _ _ hAmbient := hAmbient
  }
  exact ClosedUnderDicotic.closure_min hA

-- End-like positions in the dicotic closure of a hereditary set already lie in
-- the generating set.
private theorem mem_of_mem_closedUnderDicoticClosure_of_isEndLike {IsAmbient A : G → Prop}
    [Hereditary A] {g : G} {p : Player}
    (hg : ClosedUnderDicotic.closure IsAmbient A g) (hEnd : IsEndLike p g) : A g := by
  let B' : G → Prop := fun g =>
    ClosedUnderDicotic.closure IsAmbient A g ∧ (IsEndLike p g → A g)
  haveI : ClosedUnderDicotic IsAmbient B' := {
    closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
      constructor
      · exact ClosedUnderDicotic.dicotic_mem_closure B C
          (fun b hb => (hB b hb).1) (fun c hc => (hC c hc).1) hBne hCne hAmbient
      · -- A non-zero dicotic form has moves for both players, so it is never
        -- end-like.
        intro hEnd
        rw [ofSets_isEndLike_iff, isEnd_def] at hEnd
        cases p
        · rw [leftMoves_ofSets] at hEnd
          exact absurd hBne (Set.not_nonempty_iff_eq_empty.mpr hEnd)
        · rw [rightMoves_ofSets] at hEnd
          exact absurd hCne (Set.not_nonempty_iff_eq_empty.mpr hEnd)
  }
  have hAB : A ≤ B' := by
    intro g hg
    exact ⟨ClosedUnderDicotic.mem_closure_of_mem hg, fun _ => hg⟩
  exact (ClosedUnderDicotic.closure_min hAB g hg).2 hEnd

-- A position that is not end-like has at least one move.
private theorem moves_nonempty_of_not_isEndLike {g : G} {p : Player}
    (hg : ¬ IsEndLike p g) : (moves p g).Nonempty :=
  not_isEnd_exists_move (mt isEndLike_of_isEnd hg)

-- An element of the dicotic closure outside the generating set is not end-like
-- for either player.
private theorem not_isEndLike_of_mem_closedUnderDicoticClosure_of_not_mem
    {IsAmbient A : G → Prop} [Hereditary A] {g : G}
    (hg : ClosedUnderDicotic.closure IsAmbient A g) (hnot : ¬ A g) :
    ∀ p, ¬ IsEndLike p g := by
  intro p hEnd
  exact hnot (mem_of_mem_closedUnderDicoticClosure_of_isEndLike hg hEnd)

-- The dicotic closure of an additively closed hereditary set is additively
-- closed.
private theorem closedUnderDicoticClosure_add_mem {IsAmbient A : G → Prop}
    [ClosedUnderAdd IsAmbient] [ClosedUnderAdd A] [Hereditary A] (hA : A ≤ IsAmbient)
    {g h : G} (hg : ClosedUnderDicotic.closure IsAmbient A g)
    (hh : ClosedUnderDicotic.closure IsAmbient A h) :
    ClosedUnderDicotic.closure IsAmbient A (g + h) := by
  by_cases hgh : A g ∧ A h
  · exact ClosedUnderDicotic.mem_closure_of_mem (ClosedUnderAdd.has_add g h hgh.1 hgh.2)
  · have hNo : ∀ p, ¬ IsEndLike p (g + h) := by
      intro p hEnd
      rw [IsEndLike.add_iff] at hEnd
      rcases not_and_or.mp hgh with hgA | hhA
      · exact not_isEndLike_of_mem_closedUnderDicoticClosure_of_not_mem hg hgA p hEnd.1
      · exact not_isEndLike_of_mem_closedUnderDicoticClosure_of_not_mem hh hhA p hEnd.2
    have hEq : !{moves .left (g + h) | moves .right (g + h)} = g + h := by
      rw [← ofSets_eq_ofSets_cases (fun p => moves p (g + h))]
      exact ofSets_moves_of_not_isEndLike hNo
    -- Rebuild `g + h` from its moves and check the dicotic closure conditions.
    rw [← hEq]
    refine ClosedUnderDicotic.dicotic_mem_closure
      (moves .left (g + h)) (moves .right (g + h)) ?_ ?_
      (moves_nonempty_of_not_isEndLike (hNo .left))
      (moves_nonempty_of_not_isEndLike (hNo .right))
      (by rw [hEq]
          exact ClosedUnderAdd.has_add g h
            (closedUnderDicoticClosure_le_ambient hA g hg)
            (closedUnderDicoticClosure_le_ambient hA h hh))
    -- Each option of `g + h` is an option of one summand, so we recurse.
    all_goals
      intro x hx
      rcases isOption_add_cases (Moves.IsOption.of_mem_moves hx) with
        ⟨g', hg', rfl⟩ | ⟨h', hh', rfl⟩
      · exact closedUnderDicoticClosure_add_mem hA (Hereditary.has_option hg hg') hh
      · exact closedUnderDicoticClosure_add_mem hA hg (Hereditary.has_option hh hh')
termination_by (g, h)
decreasing_by
  all_goals
    first
    | exact Prod.Lex.left h h (Relation.TransGen.single hg')
    | exact Prod.Lex.right g (Relation.TransGen.single hh')

/--
The dicotic closure of an additively closed hereditary set is additively
closed.
-/
theorem closedUnderDicoticClosure_closedUnderSum {IsAmbient A : G → Prop}
    [ClosedUnderAdd IsAmbient] [ClosedUnderAdd A] [Hereditary A] (hA : A ≤ IsAmbient) :
    ClosedUnderAdd (ClosedUnderDicotic.closure IsAmbient A) :=
  { has_add := fun _ _ hg hh => closedUnderDicoticClosure_add_mem hA hg hh }

/-!
### The closure chain
-/

/--
The set obtained by applying the conjugate, hereditary, additive, and dicotic
closures in that order.
-/
noncomputable abbrev closureChain (IsAmbient A : G → Prop) : G → Prop :=
  ClosedUnderDicotic.closure IsAmbient
    (ClosedUnderAdd.closure (Hereditary.closure (ClosedUnderNeg.closure A)))

/--
The conjugate–hereditary–additive–dicotic closure chain yields a universe.
-/
theorem closureChain_universe {IsAmbient A : G → Prop} [Universe IsAmbient IsAmbient]
    (hA : A ≤ IsAmbient) (h0 : A 0) :
    Universe IsAmbient (closureChain IsAmbient A) := by
  have hB2 : ClosedUnderAdd.closure (Hereditary.closure (ClosedUnderNeg.closure A))
      ≤ IsAmbient :=
    ClosedUnderAdd.closure_min (Hereditary.closure_min (ClosedUnderNeg.closure_min hA))
  haveI : ClosedUnderAdd (closureChain IsAmbient A) :=
    closedUnderDicoticClosure_closedUnderSum hB2
  exact {
    zero_mem := ClosedUnderDicotic.mem_closure_of_mem
      (ClosedUnderAdd.mem_closure_of_mem (Hereditary.mem_closure_of_mem
        (ClosedUnderNeg.mem_closure_of_mem h0)))
    isAmbient_of_mem := fun hg => closedUnderDicoticClosure_le_ambient hB2 _ hg
  }

/--
The closure chain agrees with the universal closure operator.
-/
theorem closureChain_eq_universeClosure {IsAmbient A : G → Prop} [Universe IsAmbient IsAmbient]
    (hA : A ≤ IsAmbient) (h0 : A 0) :
    closureChain IsAmbient A = Universe.closure IsAmbient A hA := by
  apply le_antisymm
  · exact ClosedUnderDicotic.closure_min (ClosedUnderAdd.closure_min
      (Hereditary.closure_min (ClosedUnderNeg.closure_min
        (Universe.subset_closure IsAmbient hA))))
  · haveI : Universe IsAmbient (closureChain IsAmbient A) :=
      closureChain_universe hA h0
    exact Universe.closure_min IsAmbient hA fun g hg =>
      ClosedUnderDicotic.mem_closure_of_mem (ClosedUnderAdd.mem_closure_of_mem
        (Hereditary.mem_closure_of_mem (ClosedUnderNeg.mem_closure_of_mem hg)))

/--
The conjugate–hereditary–additive–dicotic closure chain yields a long universe.
-/
theorem closureChain_longUniverse
    {A : G → Prop} (h0 : A 0) :
    LongUniverse (closureChain IsLong A) where
  toUniverse :=
    closureChain_universe (IsAmbient := IsLong)
      (fun _ _ => isLong _) h0

/--
The long closure chain agrees with the long universal closure operator.
-/
theorem closureChain_eq_longUniverseClosure
    {A : G → Prop} (h0 : A 0) :
    closureChain IsLong A = LongUniverse.closure A :=
  closureChain_eq_universeClosure (IsAmbient := IsLong)
    (fun _ _ => isLong _) h0

/--
The conjugate–hereditary–additive–dicotic closure chain yields a short
universe.
-/
theorem closureChain_shortUniverse
    {A : G → Prop} (hA : A ≤ IsShort) (h0 : A 0) :
    ShortUniverse (closureChain IsShort A) where
  toUniverse :=
    closureChain_universe (IsAmbient := IsShort) hA h0

/--
The short closure chain agrees with the short universal closure operator.
-/
theorem closureChain_eq_shortUniverseClosure
    {A : G → Prop} (hA : A ≤ IsShort) (h0 : A 0) :
    closureChain IsShort A = ShortUniverse.closure A hA :=
  closureChain_eq_universeClosure (IsAmbient := IsShort) hA h0

/-!
## Seed correspondence

A universe is recovered from its `p` end-like positions: the universal closure
gives a bijection between the bounded `p` seeds and the universes within a
fixed ambient set.
-/

/--
The `p` end-like part of a set of games.
-/
def endLikePart (p : Player) (A : G → Prop) : G → Prop :=
  fun g => A g ∧ IsEndLike p g

theorem endLikePart_le (p : Player) (A : G → Prop) : endLikePart p A ≤ A :=
  fun _ hg => hg.1

theorem endLikePart_le_ambient (p : Player) {IsAmbient A : G → Prop}
    [Universe IsAmbient A] : endLikePart p A ≤ IsAmbient :=
  fun _ hg => Universe.isAmbient_of_mem hg.1

/--
A set of games closed under taking relevant end-like subpositions for player
`p`.
-/
class EndLikeClosed (p : Player) (A : G → Prop) where
  neg_mem_of_isEndLike_neg {g : G} (hg : A g) (hEnd : IsEndLike (-p) g) : A (-g)
  mem_of_subposition_isEndLike {g h : G} (hg : A g) (hsub : Subposition h g)
    (hEnd : IsEndLike p h) : A h
  neg_mem_of_subposition_isEndLike_neg {g h : G} (hg : A g) (hsub : Subposition h g)
    (hEnd : IsEndLike (-p) h) : A (-h)

/--
A `p` seed: an additive set of `p` end-like games containing zero and its
relevant end-like subpositions.
-/
class EndLikeSeed (p : Player) (A : G → Prop) extends EndLikeClosed p A, ClosedUnderAdd A where
  zero_mem : A 0
  isEndLike_of_mem {g : G} : A g → IsEndLike p g

section EndLikeSeed

variable {p : Player} {A : G → Prop}

-- A `p` end-like element of the conjugate closure of a seed lies in the seed.
private theorem mem_of_mem_closedUnderNegClosure_of_isEndLike [EndLikeClosed p A] {g : G}
    (hg : ClosedUnderNeg.closure A g) (hEnd : IsEndLike p g) : A g := by
  let C : G → Prop := fun g => A g ∨ A (-g)
  haveI : ClosedUnderNeg C := {
    neg_of {g} hg := by
      rcases hg with hg | hg
      · exact Or.inr (by simpa)
      · exact Or.inl (by simpa using hg)
  }
  have hAC : A ≤ C := fun g hg => Or.inl hg
  rcases ClosedUnderNeg.closure_min hAC g hg with hgA | hnegA
  · exact hgA
  · have hnegEnd : IsEndLike (-p) (-g) := by
      simpa [IsEndLike.neg_iff_neg] using hEnd
    simpa using EndLikeClosed.neg_mem_of_isEndLike_neg (p := p) hnegA hnegEnd

-- Relevant end-like subpositions of the conjugate closure of a seed lie in the
-- seed.
private theorem subposition_mem_of_mem_closedUnderNegClosure [EndLikeClosed p A] {g : G}
    (hg : ClosedUnderNeg.closure A g) :
    (∀ h, Subposition h g → IsEndLike p h → A h) ∧
      (∀ h, Subposition h g → IsEndLike (-p) h → A (-h)) := by
  let C : G → Prop := fun g => A g ∨ ∃ a, A a ∧ g = -a
  haveI : ClosedUnderNeg C := {
    neg_of {g} hg := by
      rcases hg with hg | ⟨a, ha, rfl⟩
      · exact Or.inr ⟨g, hg, rfl⟩
      · exact Or.inl (by simpa using ha)
  }
  have hAC : A ≤ C := fun g hg => Or.inl hg
  rcases ClosedUnderNeg.closure_min hAC g hg with hgA | ⟨a, ha, rfl⟩
  · constructor
    · intro h hsub hEnd
      exact EndLikeClosed.mem_of_subposition_isEndLike hgA hsub hEnd
    · intro h hsub hEnd
      exact EndLikeClosed.neg_mem_of_subposition_isEndLike_neg hgA hsub hEnd
  · constructor
    · intro h hsub hEnd
      have hnegSub : Subposition (-h) a := by
        simpa using neg_subposition_of_subposition hsub
      have hnegEnd : IsEndLike (-p) (-h) := by
        simpa [IsEndLike.neg_iff_neg] using hEnd
      simpa using EndLikeClosed.neg_mem_of_subposition_isEndLike_neg ha hnegSub hnegEnd
    · intro h hsub hEnd
      have hnegSub : Subposition (-h) a := by
        simpa using neg_subposition_of_subposition hsub
      have hnegEnd : IsEndLike p (-h) := by
        simpa [IsEndLike.neg_iff_neg] using hEnd
      exact EndLikeClosed.mem_of_subposition_isEndLike ha hnegSub hnegEnd

-- A `p` end-like element of the hereditary conjugate closure of a seed lies in
-- the seed.
private theorem mem_of_mem_hereditaryClosure_of_isEndLike [EndLikeClosed p A] {g : G}
    (hg : Hereditary.closure (ClosedUnderNeg.closure A) g) (hEnd : IsEndLike p g) : A g := by
  let D : G → Prop := fun g =>
    (IsEndLike p g → A g) ∧
      (∀ h, Subposition h g → IsEndLike p h → A h) ∧
        (∀ h, Subposition h g → IsEndLike (-p) h → A (-h))
  haveI : Hereditary D := {
    has_option {g g'} hg hopt := by
      constructor
      · intro hEnd
        exact hg.2.1 g' (Relation.TransGen.single hopt) hEnd
      · constructor
        · intro h hsub hEnd
          exact hg.2.1 h (Relation.TransGen.tail hsub hopt) hEnd
        · intro h hsub hEnd
          exact hg.2.2 h (Relation.TransGen.tail hsub hopt) hEnd
  }
  have hD : ClosedUnderNeg.closure A ≤ D := by
    intro g hg
    obtain ⟨hsub, hsubneg⟩ := subposition_mem_of_mem_closedUnderNegClosure (p := p) hg
    exact ⟨mem_of_mem_closedUnderNegClosure_of_isEndLike hg, hsub, hsubneg⟩
  exact (Hereditary.closure_min hD g hg).1 hEnd

-- A `p` end-like element of the additive hereditary conjugate closure of a
-- seed lies in the seed.
private theorem mem_of_mem_closedUnderSumClosure_of_isEndLike [EndLikeSeed p A] {g : G}
    (hg : ClosedUnderAdd.closure (Hereditary.closure (ClosedUnderNeg.closure A)) g)
    (hEnd : IsEndLike p g) : A g := by
  let C : G → Prop := fun g => IsEndLike p g → A g
  haveI : ClosedUnderAdd C := {
    has_add g h hg hh hEnd :=
      ClosedUnderAdd.has_add g h
        (hg (IsEndLike.add_iff.mp hEnd).1)
        (hh (IsEndLike.add_iff.mp hEnd).2)
  }
  have hC : Hereditary.closure (ClosedUnderNeg.closure A) ≤ C := fun g hg =>
    mem_of_mem_hereditaryClosure_of_isEndLike hg
  exact ClosedUnderAdd.closure_min hC g hg hEnd

end EndLikeSeed

/--
The `p` end-like part of the universe closure of a bounded `p` seed is the
seed.
-/
theorem endLikePart_universeClosure_eq_of_seed {p : Player} {IsAmbient A : G → Prop}
    [Universe IsAmbient IsAmbient] [EndLikeSeed p A] (hA : A ≤ IsAmbient) :
    endLikePart p (Universe.closure IsAmbient A hA) = A := by
  rw [← closureChain_eq_universeClosure hA
    (EndLikeSeed.zero_mem (p := p) (A := A))]
  apply le_antisymm
  · intro g hg
    exact mem_of_mem_closedUnderSumClosure_of_isEndLike
      (mem_of_mem_closedUnderDicoticClosure_of_isEndLike hg.1 hg.2) hg.2
  · intro g hg
    exact ⟨ClosedUnderDicotic.mem_closure_of_mem
      (ClosedUnderAdd.mem_closure_of_mem
        (Hereditary.mem_closure_of_mem
          (ClosedUnderNeg.mem_closure_of_mem hg))),
      EndLikeSeed.isEndLike_of_mem hg⟩

/--
The `p` end-like part of a universe is a `p` seed.
-/
theorem endLikePart_seed_of_universe {p : Player} {IsAmbient A : G → Prop}
    [Universe IsAmbient A] : EndLikeSeed p (endLikePart p A) := by
  have sub_mem {g h : G} (hg : A g) (hsub : Subposition h g) : A h := by
    induction hsub with
    | single hopt =>
        exact Hereditary.has_option hg hopt
    | tail hsub hopt ih =>
        exact ih (Hereditary.has_option hg hopt)
  exact {
    neg_mem_of_isEndLike_neg := fun hg hEnd =>
      ⟨ClosedUnderNeg.neg_of hg.1, by simpa [IsEndLike.neg_iff_neg] using hEnd⟩
    mem_of_subposition_isEndLike := fun hg hsub hEnd => ⟨sub_mem hg.1 hsub, hEnd⟩
    neg_mem_of_subposition_isEndLike_neg := fun hg hsub hEnd =>
      ⟨ClosedUnderNeg.neg_of (sub_mem hg.1 hsub), by simpa [IsEndLike.neg_iff_neg] using hEnd⟩
    has_add := fun g h hg hh =>
      ⟨ClosedUnderAdd.has_add g h hg.1 hh.1, IsEndLike.add_iff.mpr ⟨hg.2, hh.2⟩⟩
    zero_mem := ⟨Universe.zero_mem IsAmbient (A := A), isEndLike_of_isEnd isEnd_zero⟩
    isEndLike_of_mem := fun hg => hg.2
  }

-- Every element of a universe is generated by the universal closure of its
-- end-like part.
private theorem mem_universeClosure_endLikePart_of_mem_universe {p : Player}
    {IsAmbient A : G → Prop} [Universe IsAmbient IsAmbient] [Universe IsAmbient A]
    {g : G} (hg : A g) :
    Universe.closure IsAmbient (endLikePart p A) (endLikePart_le_ambient p) g := by
  let U : G → Prop := Universe.closure IsAmbient (endLikePart p A) (endLikePart_le_ambient p)
  change U g
  haveI : Universe IsAmbient U :=
    Universe.closure_universe IsAmbient (endLikePart_le_ambient p)
  by_cases hp : IsEndLike p g
  · exact Universe.mem_closure_of_mem IsAmbient (endLikePart_le_ambient p) ⟨hg, hp⟩
  · by_cases hnp : IsEndLike (-p) g
    · have hneg : U (-g) :=
        Universe.mem_closure_of_mem IsAmbient (endLikePart_le_ambient p)
          ⟨ClosedUnderNeg.neg_of hg, by
            simpa [IsEndLike.neg_iff_neg] using hnp⟩
      simpa using (ClosedUnderNeg.neg_of hneg : U (-(-g)))
    · have hNo : ∀ q, ¬ IsEndLike q g := by
        intro q
        rcases eq_or_ne q p with rfl | hq
        · exact hp
        · rw [Player.ne_iff_eq_neg.mp hq]
          exact hnp
      -- `g` isn't end-like, so rebuild it from its options and apply dicotic
      -- closure.
      have hEq : !{fun q => moves q g} = g := ofSets_moves_of_not_isEndLike hNo
      rw [← hEq, ofSets_eq_ofSets_cases (fun q => moves q g)]
      refine ClosedUnderDicotic.closed_dicotic
        (IsAmbient := IsAmbient) (A := U)
        (moves .left g) (moves .right g) ?_ ?_
        (moves_nonempty_of_not_isEndLike (hNo .left))
        (moves_nonempty_of_not_isEndLike (hNo .right))
        (by
          have hEq' : !{moves .left g | moves .right g} = g := by
            simpa [ofSets_eq_ofSets_cases (fun q => moves q g)] using hEq
          simpa [hEq'] using Universe.isAmbient_of_mem (IsAmbient := IsAmbient) (A := A) hg)
      -- Each option lies in the closure by recursion.
      all_goals
        intro x hx
        exact mem_universeClosure_endLikePart_of_mem_universe
          (Hereditary.has_option hg (Moves.IsOption.of_mem_moves hx))
termination_by g
decreasing_by
  all_goals exact Moves.Subposition.of_mem_moves (by assumption)

/--
A universe is the universal closure of its `p` end-like part.
-/
theorem universeClosure_endLikePart_eq_of_universe {p : Player} {IsAmbient A : G → Prop}
    [Universe IsAmbient IsAmbient] [Universe IsAmbient A] :
    Universe.closure IsAmbient (endLikePart p A) (endLikePart_le_ambient p) = A := by
  apply le_antisymm
  · exact Universe.closure_min IsAmbient (endLikePart_le_ambient p) (endLikePart_le p A)
  · intro g hg
    exact mem_universeClosure_endLikePart_of_mem_universe hg

/-!
### The seed–universe bijection
-/

/--
The type of `p` seeds contained in an ambient set.
-/
def AmbientEndLikeSeed (G : Type (u + 1)) [Form G] (IsAmbient : G → Prop)
    (p : Player) :=
  {A : G → Prop // EndLikeSeed p A ∧ A ≤ IsAmbient}

/--
The type of universes with a fixed ambient set.
-/
def AmbientUniverse (G : Type (u + 1)) [Form G] (IsAmbient : G → Prop) :=
  {A : G → Prop // Universe IsAmbient A}

/--
Sending a bounded `p` seed to its universe closure.
-/
noncomputable def endLikeSeedToUniverse (G : Type (u + 1)) [Form G]
    (IsAmbient : G → Prop) [Universe IsAmbient IsAmbient] (p : Player) :
    AmbientEndLikeSeed G IsAmbient p → AmbientUniverse G IsAmbient :=
  fun A => ⟨Universe.closure IsAmbient A.1 A.2.2,
    Universe.closure_universe IsAmbient A.2.2⟩

/--
Sending a universe to its `p` end-like part.
-/
noncomputable def universeToEndLikeSeed (G : Type (u + 1)) [Form G]
    (IsAmbient : G → Prop) (p : Player) :
    AmbientUniverse G IsAmbient → AmbientEndLikeSeed G IsAmbient p :=
  fun A =>
    haveI : Universe IsAmbient A.1 := A.2
    ⟨endLikePart p A.1, endLikePart_seed_of_universe (IsAmbient := IsAmbient),
      endLikePart_le_ambient p⟩

/--
Universe closure is an equivalence from bounded `p` seeds to universes, with
inverse taking the `p` end-like part.
-/
noncomputable def endLikeSeedEquivUniverse {IsAmbient : G → Prop}
    [Universe IsAmbient IsAmbient] (p : Player) :
    AmbientEndLikeSeed G IsAmbient p ≃ AmbientUniverse G IsAmbient where
  toFun := endLikeSeedToUniverse G IsAmbient p
  invFun := universeToEndLikeSeed G IsAmbient p
  left_inv A := by
    haveI : EndLikeSeed p A.1 := A.2.1
    apply Subtype.ext
    dsimp [universeToEndLikeSeed, endLikeSeedToUniverse]
    exact endLikePart_universeClosure_eq_of_seed A.2.2
  right_inv U := by
    haveI : Universe IsAmbient U.1 := U.2
    apply Subtype.ext
    dsimp [universeToEndLikeSeed, endLikeSeedToUniverse]
    exact universeClosure_endLikePart_eq_of_universe

/--
Universal closure gives a bijection from bounded `p` seeds to universes.
-/
theorem endLikeSeedToUniverse_bijective {IsAmbient : G → Prop}
    [Universe IsAmbient IsAmbient] (p : Player) :
    Function.Bijective (endLikeSeedToUniverse G IsAmbient p) :=
  (endLikeSeedEquivUniverse p).bijective

/--
The `p` end-like part of the long universal closure of a `p` seed is the seed.
-/
theorem endLikePart_longUniverseClosure_eq_of_seed {p : Player} {A : G → Prop}
    [EndLikeSeed p A] : endLikePart p (LongUniverse.closure A) = A :=
  endLikePart_universeClosure_eq_of_seed (IsAmbient := IsLong)
    (fun _ _ => isLong _)

/--
The `p` end-like part of a long universe is a `p` seed.
-/
theorem endLikePart_seed_of_longUniverse {p : Player} {A : G → Prop} [LongUniverse A] :
    EndLikeSeed p (endLikePart p A) :=
  endLikePart_seed_of_universe (IsAmbient := IsLong) (A := A)

/--
A long universe is the long universal closure of its `p` end-like part.
-/
theorem longUniverseClosure_endLikePart_eq_of_longUniverse {p : Player} {A : G → Prop}
    [LongUniverse A] : LongUniverse.closure (endLikePart p A) = A :=
  universeClosure_endLikePart_eq_of_universe
    (IsAmbient := IsLong) (A := A)

/--
Long universal closure gives a bijection from `p` seeds to long universes.
-/
theorem endLikeSeedToLongUniverse_bijective (p : Player) :
    Function.Bijective (endLikeSeedToUniverse G IsLong p) :=
  endLikeSeedToUniverse_bijective (IsAmbient := IsLong) p

/--
The `p` end-like part of the short universal closure of a short `p` seed is the
seed.
-/
theorem endLikePart_shortUniverseClosure_eq_of_seed {p : Player} {A : G → Prop}
    [EndLikeSeed p A] (hA : A ≤ IsShort) :
    endLikePart p (ShortUniverse.closure A hA) = A :=
  endLikePart_universeClosure_eq_of_seed (IsAmbient := IsShort) hA

/--
The `p` end-like part of a short universe is a `p` seed.
-/
theorem endLikePart_seed_of_shortUniverse {p : Player} {A : G → Prop} [ShortUniverse A] :
    EndLikeSeed p (endLikePart p A) :=
  endLikePart_seed_of_universe (IsAmbient := IsShort) (A := A)

/--
A short universe is the short universal closure of its `p` end-like part.
-/
theorem shortUniverseClosure_endLikePart_eq_of_shortUniverse {p : Player} {A : G → Prop}
    [ShortUniverse A] :
    ShortUniverse.closure (endLikePart p A) (endLikePart_le_ambient p) = A :=
  universeClosure_endLikePart_eq_of_universe (IsAmbient := IsShort) (A := A)

/--
Short universal closure gives a bijection from short `p` seeds to short
universes.
-/
theorem endLikeSeedToShortUniverse_bijective (p : Player) :
    Function.Bijective (endLikeSeedToUniverse G (IsShort (G := G)) p) :=
  endLikeSeedToUniverse_bijective (IsAmbient := IsShort) p

end Preservation

end Misere

end Form

end

end MisereGames
