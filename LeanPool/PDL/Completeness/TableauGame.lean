/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Functor
public import LeanPool.PDL.Interpolation.Uniformity

public import LeanPool.PDL.General.Game
public import LeanPool.PDL.Local.AllLocalTab
public import LeanPool.PDL.Completeness.Modelgraphs
public import LeanPool.PDL.StayingInFL

/-! # The Tableau Game (Section 6.2) -/

public section

namespace PDL

open Lean4GlCoalgebras

/-!
Different from the paper proof, here we directly set up the tableau game such that we
also get a *uniform* tableau: Prover is not free to choose *any* local tableau: at a
non-basic sequent `X` the only move available is the one to the canonical local
tableau `uniLocalTab X` defined in `Pdl.Interpolation.Uniformity`.
The gain is in `gameP_general`: a winning strategy for Prover yields a tableau with
the property `Tableau.IsUni` (and hence `Tableau.isUniform` for the empty history)
because at every `loc` step the canonical local tableau is used.
-/

/-! ## Prover and Builder positions -/

-- Renaming the players for the tableau game:
/-- The player who chooses tableau rules. -/
scoped notation "Prover" => Player.A
/-- The player who chooses branches of local tableaux. -/
scoped notation "Builder" => Player.B

/-- Prover should make a move. -/
inductive ProverPos (H : History) (X : Sequent) : Type where
  | frep : (rep H X ∧ X.isFree) → ProverPos H X -- Prover loses at free repeats.
  | bas : ¬ flprep H X → X.basic → ProverPos H X -- Prover must apply a PDL rule
  | nbas : ¬ flprep H X → ¬ X.basic → ProverPos H X -- Prover must make a local LocalTableau
  deriving DecidableEq

/-- Builder should make a move. -/
inductive BuilderPos (H : History) (X : Sequent) : Type where
  | lpr : LoadedPathRepeat H X → BuilderPos H X -- no moves, Prover wins.
  | ltab : ¬ flprep H X → ¬ X.basic → LocalTableau X → BuilderPos H X -- Builder picks endNodesOf
  deriving DecidableEq

/-- Game position where either Prover (`isLeft`) or Builder (`isRight`) should make a move. -/
@[implicit_reducible]
def GamePos := Σ H X, (ProverPos H X ⊕ BuilderPos H X)
  deriving DecidableEq

/-- If we reach this sequent, what is the next game position? Includes winning positions. -/
def posOf (H : History) (X : Sequent) : ProverPos H X ⊕ BuilderPos H X :=
  if h_neNlp : Nonempty (LoadedPathRepeat H X)
  then .inr (.lpr (.choice h_neNlp)) -- BuilderPos with no moves to let Prover win at lpr
  else
    if h_frep : rep H X ∧ X.isFree
    then .inl (.frep h_frep) -- ProverPos with no moves to let Builder win at (non-lp) repeat
    else
      if bas : X.basic
      then .inl (.bas (by grind) bas) -- actual ProverPos to choose a PDL rule
      else .inl (.nbas (by grind) bas) -- actual ProverPos to make LocalTab

lemma posOf_eq_inr_then_lpr {H X p} :
    posOf H X = Sum.inr p → ∃ lpr, p = .lpr lpr := by
  unfold posOf
  grind

/-! ## Moves -/

/-- The relation `Move old next` says that we can move from `old` to `next`.
There are three kinds of moves.

Note that in the `prLocTab` move Prover has no choice:
the local tableau must be the canonical uniform one, `uniLocalTab X`. -/
inductive Move : (old : GamePos) → (new : GamePos) → Type
/-- When the sequent is basic and no repeat, let prover apply a PDL rule. -/
| prPdl {X Y Hist nrep Xbasic} : PdlRule X Y →
    Move ⟨Hist, X, .inl (.bas nrep Xbasic)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩
/-- If not basic, Prover must move to the uniform local tableau `uniLocalTab X`. -/
| prLocTab {Hist X nrep nbas} :
    Move ⟨Hist, X, .inl (.nbas nrep nbas)⟩
         ⟨Hist, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩
/-- Let Builder pick an end node of `ltab` -/
| buEnd {X ltab Y Hist nrep nbas} : Y ∈ endNodesOf (ltab : LocalTableau X) →
    Move ⟨Hist, X, .inr (.ltab nrep nbas ltab)⟩
         ⟨(X :: Hist), Y, posOf (X :: Hist) Y⟩

/-- Whether a game move applies a modal PDL rule. -/
def Move.isModal {pos newPos : GamePos} : Move pos newPos → Prop
| .prPdl r => r.isModal
| .prLocTab => False
| .buEnd _ => False

/-- Existence of a legal move between two game positions. -/
def move (old : GamePos) (new : GamePos) : Prop := Nonempty (Move old new)

lemma move_then_no_frep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ (rep H X ∧ X.isFree) := by
  simp only [move, Nonempty.forall]
  intro next_p hyp
  cases next_p <;> grind

/-- The finite set of moves, given as a function instead of a relation.
With `move_of_mem_theMoves` and `mem_theMoves_of_move` this agrees with `move`. -/
@[expose, simp] def theMoves : GamePos → Finset GamePos
  -- ProverPos:
  | ⟨H, X, .inl (.frep _)⟩ => ∅ -- no moves ⇒ Builder wins
  | ⟨H, X, .inl (.bas _ Xbasic)⟩ =>
      -- need to choose PDL rule application:
      match X with
      | ⟨L, R, none⟩ => -- (L+) if X is not loaded, choice of formula
            -- We want to catch a negation and all boxes (≥ 1) after it to be loaded.
            (L.sup (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              { ⟨ _, _, posOf (X::H) (L.erase (~φ), R
                                , some (Sum.inl (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ }
                            | ([],_) => {}
                        | _ => {} ))
            ∪
            (R.sup (fun | ~φ => match boxesOf φ with
                            | (δ@h:(_::_), ψ) =>
                              { ⟨ _, _, posOf (X::H) (L, R.erase (~φ)
                                , some (Sum.inr (~'(⌊⌊δ.dropLast⌋⌋⌊δ.getLast (by grind)⌋ψ))))⟩ }
                            | ([],_) => {}
                        | _ => {} ))
      | ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨{~φ} ∪ L.pdlProjection a, R.pdlProjection a,
                none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ L.pdlProjection a, R.pdlProjection a
                                                 , some (Sum.inl (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L ∪ {~(⌊·a⌋ξ).unload}, R, none)⟩ }
      | ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩ =>
              ( match ξ with -- (M) rule, deterministic:
              | .normal φ => { ⟨_,_,posOf (X::H) ⟨L.pdlProjection a, {~φ} ∪ R.pdlProjection a,
                none⟩⟩ }
              | .loaded χ => { ⟨_,_,posOf (X::H) ⟨ L.pdlProjection a, R.pdlProjection a
                                                 , some (Sum.inr (~'χ))⟩⟩ } )
              ∪ -- (L-) rule, deterministic:
              { ⟨_, _, posOf (X::H) (L, R ∪ {~(⌊·a⌋ξ).unload}, none)⟩ }
      -- Somewhat repetitive. Is there pattern matching with "did not match before" proofs?
      | ⟨L, R, some (.inl (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inl (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊α;'β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α;'β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊?'τ⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊?'τ⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊α ⋓ β⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊α ⋓ β⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
      | ⟨L, R, some (.inr (~'⌊∗α⌋χ))⟩ => by
          exfalso; have := Xbasic.1 (~(⌊∗α⌋χ).unload)
          cases χ <;> simp [LoadFormula.unload,Sequent.basic,Sequent.toFinset] at *
  | ⟨H, X, .inl (.nbas nrep nbas)⟩ =>
      -- If not basic, Prover must move to the uniform local tableau `uniLocalTab X`.
      { ⟨H, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩ }
  -- BuilderPos:
  | ⟨H, X, .inr (.lpr lpr)⟩ => ∅ -- no moves ⇒ Prover wins
  | ⟨H, X, .inr (.ltab _ _ ltab)⟩ =>
      -- Let Builder pick an end node of `ltab`:
      ((endNodesOf ltab).image (fun Y => ⟨(X :: H), Y, posOf (X :: H) Y⟩))

/-- A basic loaded position offers a modal step or an unloading step on its loaded side. -/
private theorem theMoves_loaded_forward {H : History} {next : GamePos}
    (L R : Finset Formula) (χ : NegLoadFormula ⊕ NegLoadFormula)
    (nrep : ¬ flprep H (L, R, some χ)) (basic : Sequent.basic (L, R, some χ))
    (mv : next ∈ theMoves ⟨H, (L, R, some χ), Sum.inl (.bas nrep basic)⟩) :
    let X : Sequent := (L, R, some χ)
    ∃ a ξ,
      (χ = Sum.inl (~'⌊·a⌋ξ) ∧
        (next = ⟨X :: H, _, posOf (X :: H) (match ξ with
          | .normal φ => ({~φ} ∪ L.pdlProjection a, R.pdlProjection a, none)
          | .loaded ψ => (L.pdlProjection a, R.pdlProjection a, some (Sum.inl (~'ψ))))⟩ ∨
          next = ⟨X :: H, _, posOf (X :: H) (L ∪ {~(⌊·a⌋ξ).unload}, R, none)⟩)) ∨
      (χ = Sum.inr (~'⌊·a⌋ξ) ∧
        (next = ⟨X :: H, _, posOf (X :: H) (match ξ with
          | .normal φ => (L.pdlProjection a, {~φ} ∪ R.pdlProjection a, none)
          | .loaded ψ => (L.pdlProjection a, R.pdlProjection a, some (Sum.inr (~'ψ))))⟩ ∨
          next = ⟨X :: H, _, posOf (X :: H) (L, R ∪ {~(⌊·a⌋ξ).unload}, none)⟩)) := by
  dsimp only
  unfold theMoves at mv
  rcases χ with (⟨⟨χ⟩⟩|⟨⟨χ⟩⟩) <;> rcases χ with ⟨δ,φ|χ⟩ <;> cases δ <;> simp_all
  all_goals grind

/-- Characterization of `theMoves`. -/
lemma theMoves_iff {H X} {p : ProverPos H X ⊕ BuilderPos H X} {next : GamePos} :
    next ∈ theMoves ⟨H, X, p⟩
    ↔
    -- ProverPos:
    ( ∃ nrep Xbasic, p = .inl (.bas nrep Xbasic)
      ∧ ∃ L R, ( -- need to choose PDL rule application:
        ( X = ⟨L, R, none⟩ -- (L+) rule, choosing formula to load
          ∧ ( ( ∃ δs δ ψ, ¬ ψ.isBox ∧ (~⌈⌈δs⌉⌉⌈δ⌉ψ) ∈ L
                ∧ next = ⟨_, _, posOf (X::H) ( L.erase (~⌈⌈δs⌉⌉⌈δ⌉ψ), R
                                             , some (Sum.inl (~'(⌊⌊δs⌋⌋⌊δ⌋ψ))))⟩)
              ∨
              ( ∃ δs δ ψ, ¬ ψ.isBox ∧ (~⌈⌈δs⌉⌉⌈δ⌉ψ) ∈ R
                ∧ next = ⟨_, _, posOf (X::H) ( L, R.erase (~⌈⌈δs⌉⌉⌈δ⌉ψ)
                                             , some (Sum.inr (~'(⌊⌊δs⌋⌋⌊δ⌋ψ))))⟩)
            )
        )
        ∨
        ( ∃ a ξ, X = ⟨L, R, some (.inl (~'⌊·a⌋ξ))⟩
          ∧ ( ( ∃ φ, ξ = .normal φ -- (M) rule, deterministic
                ∧ next = ⟨_,_,posOf (X::H) ⟨{~φ} ∪ L.pdlProjection a, R.pdlProjection a, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.pdlProjection a, R.pdlProjection a, some (Sum.inl
                  (~'χ))⟩⟩ )
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L ∪ {~(⌊·a⌋ξ).unload}, R, none)⟩ )
            )
        )
        ∨
        ( ∃ a ξ, X = ⟨L, R, some (.inr (~'⌊·a⌋ξ))⟩
          ∧ ( ( ∃ φ, ξ = .normal φ -- (M) rule, deterministic
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.pdlProjection a, {~φ} ∪ R.pdlProjection a, none⟩⟩ )
              ∨
              ( ∃ χ, ξ = .loaded χ
                ∧ next = ⟨_,_,posOf (X::H) ⟨L.pdlProjection a, R.pdlProjection a, some (Sum.inr
                  (~'χ))⟩⟩)
              ∨
              ( -- (L-) rule, deterministic
                next = ⟨_, _, posOf (X::H) (L, R ∪ {~(⌊·a⌋ξ).unload}, none)⟩
              )
            )
        )
      )
    )
    ∨
    ( ∃ nrep nbas, p = .inl (.nbas nrep nbas) -- not basic, prover must take `uniLocalTab X`
      ∧ next = ⟨H, X, .inr (.ltab nrep nbas (uniLocalTab X))⟩
    )
    ∨
    -- BuilderPos:
    ( ∃ nrep nbas ltab, p = .inr (.ltab nrep nbas ltab) -- builds picks end node
      ∧ ∃ Y ∈ endNodesOf ltab, next = ⟨(X :: H), Y, posOf (X :: H) Y⟩) := by
  constructor
  · intro mv
    unfold move theMoves at mv
    rcases p with (_|_|_) | (_|_) <;> rcases X with ⟨L,R,_|χ⟩
    · simp at *
    · simp at *
    · simp_all only [Finset.mem_union, Finset.mem_sup, Finset.singleton_union, true_and,
      nonempty_prop, exists_const, not_false_eq_true, Sum.inl.injEq, reduceCtorEq, false_and,
      not_true_eq_false, IsEmpty.exists_iff, exists_false, or_self, or_false] -- bas none case
      -- use L, R
      rcases mv with ⟨ψ, ψ_in, next_in⟩ | ⟨ψ, ψ_in, next_in⟩
      · cases ψ -- L
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp only [bxs_def, Finset.mem_singleton] at next_in
            refine ⟨L, R, Or.inl ⟨ rfl, Or.inl ⟨(head :: tail).dropLast
                                 , (head :: tail).getLast (by simp), ψ, ?_⟩⟩⟩
            rw [← boxes_last, List.dropLast_append_getLast]
            have := def_of_boxesOf_def bxs_def; grind
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
      · cases ψ -- R, analogous
        case neg φ =>
          by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
          · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
            simp only [bxs_def, Finset.mem_singleton] at next_in
            refine ⟨L, R, Or.inl ⟨ rfl, Or.inr ⟨(head :: tail).dropLast
                                 , (head :: tail).getLast (by simp), ψ, ?_⟩⟩⟩
            rw [← boxes_last, List.dropLast_append_getLast]
            have := def_of_boxesOf_def bxs_def; grind
          · exfalso
            cases φ <;> simp_all [boxesOf]
        all_goals
          exfalso; simp at *
    · -- Here we have a loaded formula in X already, and are basic.
      -- So the only applicable rules are (M) and (L-).
      obtain ⟨a, ξ, h⟩ := theMoves_loaded_forward L R χ _ _ mv
      rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩
      · refine Or.inl ⟨_, _, rfl, L, R, Or.inr (Or.inl ⟨a, ξ, rfl, ?_⟩)⟩
        cases ξ <;> simpa using h
      · refine Or.inl ⟨_, _, rfl, L, R, Or.inr (Or.inr ⟨a, ξ, rfl, ?_⟩)⟩
        cases ξ <;> simpa using h
    all_goals
      simp at *
      try grind
  · unfold theMoves
    rintro (⟨_, _, p_def, hyp⟩ | ⟨_, _, p_def, hyp⟩ | ⟨_, _, lt, p_def, hyp⟩) <;> subst p_def
    · rcases hyp with ⟨L, R, (⟨X_def, hyp⟩ | _ | _) ⟩
      · subst X_def
        simp only [Finset.mem_union, Finset.mem_sup]
        rcases hyp with ⟨δs, δ, ψ, ψ_noBox, _in_L, next_def⟩
                      | ⟨δs, δ, ψ, ψ_noBox, _in_R, next_def⟩
        · left
          use (~⌈⌈δs⌉⌉⌈δ⌉ψ)
          have := @boxesOf_def_of_def_of_nonBox _ (δs ++ [δ]) ψ rfl ψ_noBox
          rw [boxes_last] at this
          simp_all only [true_and]
          have e1 : ∀ (x : Program) (l : List Program),
              (x :: (l ++ [δ])).dropLast = x :: l :=
            fun x l => List.dropLast_concat (l₁ := x :: l) (b := δ)
          have e2 : ∀ (x : Program) (l : List Program) (h), (x :: (l ++ [δ])).getLast h = δ :=
            fun x l _ => List.getLast_concat (l := x :: l) (a := δ)
          cases δs
          · simp
            grind
          · simp only [List.cons_append, Finset.mem_singleton]
            rw [e1, e2]
        · right
          use (~⌈⌈δs⌉⌉⌈δ⌉ψ)
          have := @boxesOf_def_of_def_of_nonBox _ (δs ++ [δ]) ψ rfl ψ_noBox
          rw [boxes_last] at this
          simp_all only [true_and]
          have e1 : ∀ (x : Program) (l : List Program),
              (x :: (l ++ [δ])).dropLast = x :: l :=
            fun x l => List.dropLast_concat (l₁ := x :: l) (b := δ)
          have e2 : ∀ (x : Program) (l : List Program) (h), (x :: (l ++ [δ])).getLast h = δ :=
            fun x l _ => List.getLast_concat (l := x :: l) (a := δ)
          cases δs
          · simp
            grind
          · simp only [List.cons_append, Finset.mem_singleton]
            rw [e1, e2]
      · grind
      · grind
    · simp
      subst hyp
      simp
    · simp
      grind

attribute [local simp] flprep in
lemma no_moves_of_rep {H X pos} (h : rep H X ∧ X.isFree) :
    theMoves ⟨H, X, pos⟩ = ∅ := by
  by_contra hyp
  rw [Finset.eq_empty_iff_forall_notMem] at hyp
  push Not at hyp
  rcases hyp with ⟨p, p_in⟩
  unfold theMoves at p_in
  rcases X with ⟨L,R,_|o⟩ <;> rcases pos with (_|_|_)|(_|_) <;> aesop

/-- The finite set given by `theMoves` indeed agrees with the relation `move`.
Other direction is `mem_theMoves_of_move`. -/
lemma move_of_mem_theMoves {pos next} :
    next ∈ theMoves pos → move pos next := by
  rcases pos with ⟨Hist, X, p⟩
  intro mv
  unfold theMoves at mv
  rcases p with (_|_|_) | (_|_) <;> rcases X with ⟨L,R,_|χ⟩ <;> simp_all only [Finset.notMem_empty,
    Finset.mem_union, Finset.mem_sup, Finset.singleton_union, Finset.union_singleton,
    Finset.mem_singleton, Finset.mem_image]
  case inl.bas.none =>
    rcases mv with ⟨ψ, ψ_in, next_in⟩ | ⟨ψ, ψ_in, next_in⟩
    · cases ψ -- L
      case neg φ =>
        by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
        · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
          simp only [bxs_def, Finset.mem_singleton] at next_in
          subst next
          have : ∀ h, φ = ⌈⌈(head :: tail).dropLast⌉⌉⌈(head :: tail).getLast h⌉ψ := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, def_of_boxesOf_def bxs_def,
              Formula.boxes_cons, forall_true_left]
            rw [← boxes_last, List.dropLast_append_getLast, Formula.boxes_cons]
          rw [this (by simp)]
          simp only [move]
          constructor
          apply Move.prPdl
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
          subst this
          exact PdlRule.loadL ψ_in ψ_nonBox rfl
        · exfalso
          cases φ <;> simp_all [boxesOf]
      all_goals
        exfalso; simp at *
    · cases ψ -- R, analogous
      case neg φ =>
        by_cases h: ∃ head tail ψ, ¬ ψ.isBox ∧ boxesOf φ = ((head :: tail), ψ)
        · rcases h with ⟨head, tail, ψ, ψ_nonBox, bxs_def⟩
          simp only [bxs_def, Finset.mem_singleton] at next_in
          subst next
          have : ∀ h, φ = ⌈⌈(head :: tail).dropLast⌉⌉⌈(head :: tail).getLast h⌉ψ := by
            simp only [ne_eq, reduceCtorEq, not_false_eq_true, def_of_boxesOf_def bxs_def,
              Formula.boxes_cons, forall_true_left]
            rw [← boxes_last, List.dropLast_append_getLast, Formula.boxes_cons]
          rw [this (by simp)]
          simp only [move]
          constructor
          apply Move.prPdl
          simp only [ne_eq, reduceCtorEq, not_false_eq_true, forall_true_left] at this
          subst this
          exact PdlRule.loadR ψ_in ψ_nonBox rfl
        · exfalso
          cases φ <;> simp_all [boxesOf]
      all_goals
        exfalso; simp at *
  · -- Here we have a loaded formula in X already, and are basic.
    -- So the only applicable rules are (M) and (L-).
    rcases χ with (⟨⟨χ⟩⟩|⟨⟨χ⟩⟩) <;> rcases χ with ⟨δ,φ|χ⟩ <;> cases δ <;> simp_all only
      [LoadFormula.unload,
      Finset.mem_insert, Finset.mem_singleton]
    case inl.bas.some.inl.normal.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · constructor; apply Move.prPdl; apply @PdlRule.freeL _ L R [] (·a) φ _ rfl; simp
      · constructor; apply Move.prPdl; apply PdlRule.modL rfl rfl
    case inl.bas.some.inl.loaded.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
        subst χ
        rw [unload_loadMulti]
        constructor; apply Move.prPdl;
        convert @PdlRule.freeL _ L R (·a :: δ) α φ _ rfl rfl using 1 <;>
          simp [loadMulti, LoadFormula.boxes]
      · constructor; apply Move.prPdl (PdlRule.modL rfl rfl)
    case inl.bas.some.inr.normal.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · constructor; apply Move.prPdl; apply @PdlRule.freeR _ L R [] (·a) φ _ rfl; simp
      · constructor; apply Move.prPdl (PdlRule.modR rfl rfl)
    case inl.bas.some.inr.loaded.atom_prog a nrep bas =>
      cases mv <;> subst_eqs
      · rcases LoadFormula.exists_loadMulti χ with ⟨δ, α, φ, χ_def⟩
        subst χ
        rw [unload_loadMulti]
        constructor; apply Move.prPdl;
        convert @PdlRule.freeR _ L R (·a :: δ) α φ _ rfl rfl using 1 <;>
          simp [loadMulti, LoadFormula.boxes]
      · constructor; apply Move.prPdl; apply PdlRule.modR rfl rfl
    all_goals
      grind
  · subst mv
    exact ⟨Move.prLocTab⟩
  · subst mv
    exact ⟨Move.prLocTab⟩
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.buEnd lt_in
  · rcases mv with ⟨lt, lt_in, def_next⟩
    subst def_next
    constructor; apply Move.buEnd lt_in

lemma mem_theMoves_of_move {pos next} :
    move pos next → next ∈ theMoves pos := by
  intro mov
  rcases pos with ⟨H, X, p⟩
  rw [theMoves_iff]
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl Y bas r nrep =>
    simp_all only [true_and, exists_const, not_false_eq_true, Sum.inl.injEq, reduceCtorEq,
      false_and, not_true_eq_false, IsEmpty.exists_iff, exists_false, or_self, or_false]
    use X.1, X.2.1
    rcases X with ⟨L,R,_|χ⟩ <;> cases r <;> try subst_eqs
    case none.loadL δs δ ψ notBox in_L =>
      simp_all only [true_and]
      left; left
      use δs, δ, ψ
    case none.loadR δs δ ψ notBox in_L =>
      simp_all only [true_and]
      left; right
      use δs, δ, ψ
    case some.freeL δs δ ψ  =>
      simp_all only
      right
      left -- L
      cases δs
      · simp_all only [LoadFormula.boxes_nil]
        cases δ
        case atom_prog a =>
          use a, AnyFormula.normal ψ
          simp only [AnyFormula.normal.injEq, exists_eq_left', reduceCtorEq, false_and,
            exists_false, LoadFormula.unload, false_or, true_and]
          aesop
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inl, negUnload, LoadFormula.unload,
            Option.toFinset_some, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
      case cons α δs =>
        cases α
        case atom_prog a =>
          use a
          use ⌊⌊δs⌋⌋⌊δ⌋AnyFormula.normal ψ
          simp only [LoadFormula.boxes_cons, reduceCtorEq, false_and, exists_const,
            AnyFormula.loaded.injEq, exists_eq_left', LoadFormula.unload, false_or, true_and]
          right
          convert rfl using 5
          simp
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inl, negUnload, unload_boxes,
            LoadFormula.unload, Formula.boxes_cons, Option.toFinset_some, Finset.union_singleton,
            Finset.mem_insert, Finset.mem_union, Formula.basic, decide_false, decide_true,
            forall_eq_or_imp, Bool.false_eq_true, false_and] at bas
    case some.freeR δs δ ψ =>
      right
      right -- R, this is the only change here!
      cases δs
      · simp_all only [LoadFormula.boxes_nil]
        cases δ
        case atom_prog a =>
          use a, AnyFormula.normal ψ
          simp only [AnyFormula.normal.injEq, exists_eq_left', reduceCtorEq, false_and,
            exists_false, LoadFormula.unload, false_or, true_and]
          aesop
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inr, negUnload, LoadFormula.unload,
            Option.toFinset_some, Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
      case cons α δs =>
        cases α
        case atom_prog a =>
          use a
          use ⌊⌊δs⌋⌋⌊δ⌋AnyFormula.normal ψ
          simp only [LoadFormula.boxes_cons, reduceCtorEq, false_and, exists_const,
            AnyFormula.loaded.injEq, exists_eq_left', LoadFormula.unload, false_or, true_and]
          right
          convert rfl using 5
          simp
        all_goals
          absurd bas
          rintro ⟨bas, nclos⟩
          simp only [Sequent.toFinset, Option.map_some, Sum.elim_inr, negUnload, unload_boxes,
            LoadFormula.unload, Formula.boxes_cons, Option.toFinset_some,
            Finset.union_singleton, Finset.mem_insert, Finset.mem_union,
            Formula.basic, decide_false, decide_true, forall_eq_or_imp, Bool.false_eq_true,
            false_and] at bas
    case some.modL a ξ =>
      right
      left
      use a, ξ
      simp only [true_and]
      cases ξ <;> grind
    case some.modR =>
    · grind -- sus that this works but did not in `modL` case?!
  case prLocTab nbas nrep =>
    grind
  case buEnd Y ltX nbas Y_in nrep =>
    grind

lemma move.hist {Hist next pos} (mov : move ⟨Hist, X, pos⟩ next) :
      (∃ newPos, next = ⟨Hist, X, newPos⟩) -- this is for the annoying `prLocTab` case;-)
    ∨ (∃ Y newPos, next = ⟨X :: Hist, Y, newPos⟩)  := by
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl => right; grind
  case prLocTab => left; grind
  case buEnd => right; grind

lemma move.hist_suffix {Hist next pos} (mov : move ⟨Hist, X, pos⟩ next) : Hist <:+ next.1 := by
  have := move.hist mov
  grind

lemma move.trans_hist_suffix {pX pZ} (movt : Relation.TransGen move pX pZ) :
    pX.1 <:+ pZ.1 := by
  induction movt
  case single hm => exact move.hist_suffix hm
  case tail steps hm IH =>
    have := move.hist_suffix hm
    apply List.IsSuffix.trans IH this

/-- Along the transitive closure of `move` either the history stays the same or the old
sequent and history form a prefix of the new history
(where "prefix" is actually "suffix" because the history has the newest element first). -/
lemma move.trans_hist {pX pY} (movt : Relation.TransGen move pX pY) :
      (pX.1 = pY.1 ∧ pX.2.1 = pY.2.1)
    ∨ ((pX.2.1 :: pX.1) <:+ pY.1) := by
  induction movt -- would like induction here
  case single hm =>
    rcases hm.hist  with ⟨newP, HXP_eq⟩ | ⟨Z, newP, Y_def⟩
    · left
      cases HXP_eq
      simp
    · grind
  case tail pW pZ steps hm IH =>
    rcases IH with ⟨IH_same_H, IH_same_X⟩ | IH_change
      <;> rcases hm.hist  with ⟨newP, HXP_eq⟩ | ⟨Z, newP, Y_def⟩
    · left
      cases HXP_eq
      simp_all
    · cases Y_def
      simp
      aesop
    · cases HXP_eq
      simp at *
      aesop
    · cases Y_def
      simp only [] at *
      rcases pX with ⟨X, H, p⟩
      rcases pW with ⟨Y', H', p'⟩
      simp at *
      grind

/-! ## Lemmas about double moves -/

/-- After two moves the history must grow. -/
lemma move_twice_hist_length {A B C : GamePos} (A_B : move A B) (B_C : move B C) :
    A.1.length < C.1.length := by
  rcases A with ⟨HA, A, pA⟩
  rcases B with ⟨HB, B, pB⟩
  rcases C with ⟨HC, C, pC⟩
  simp only
  rcases A_B with ⟨A_B⟩
  rcases B_C with ⟨B_C⟩
  cases A_B
  case prPdl Xbasic nrep r =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all
  case prLocTab ltA nrep =>
    cases B_C -- must be buEnd :-)
    case buEnd nbas nrep' C_in =>
      have := endNodesOf_nonbasic_non_eq (uniLocalTab A) nbas C_in
      grind
  case buEnd ltA nbas nrep B_in =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all

/-- Insert obligatory "We like to move it move it" joke here. -/
abbrev movemove := Relation.Comp move move

lemma movemove.hist {A B C : GamePos} (A_B : move A B) (B_C : move B C) :
    ((A.2.1 :: A.1) <:+ C.1)  := by
  rcases A with ⟨HA, A, pA⟩
  rcases B with ⟨HB, B, pB⟩
  rcases C with ⟨HC, C, pC⟩
  simp only
  rcases A_B with ⟨A_B⟩
  rcases B_C with ⟨B_C⟩
  cases A_B
  case prPdl Xbasic nrep r =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all
  case prLocTab ltA nrep =>
    cases B_C -- must be buEnd :-)
    case buEnd nbas nrep' C_in =>
      have := endNodesOf_nonbasic_non_eq (uniLocalTab A) nbas C_in
      grind
  case buEnd ltA nbas nrep B_in =>
    generalize h : posOf (A :: HA) B = stepP at *
    cases B_C <;> simp_all

/-- After any number of double moves the history gets extended. -/
lemma movemove_trans_hist {A B : GamePos} (A_B : Relation.TransGen movemove A B) :
    ((A.2.1 :: A.1) <:+ B.1)  := by
  induction A_B
  case single C mvmv =>
    rcases mvmv with ⟨B, A_B, B_C⟩
    exact movemove.hist A_B B_C
  case tail B C A__B B_C IH =>
    rcases B_C with ⟨X, B_X, X_C⟩
    have := movemove.hist B_X X_C
    cases IH
    cases this
    grind

/-! ## Termination via finite FL closure

See also `StayingInFL.lean` where`Sequent.subseteqFL` is defined.

We are working with lists (or, by ignoring their order, multisets) and thus staying in
the FL closure does not imply that there are only finitely many sequents reachable: by repeating
the same formulas the length of the list may increase.
To tackle this we want to use that `rep` is defined with `setEqTo` that ignores multiplicity, so
that even if there are infinitely many different lists and thus sequents in principle reachable,
we still cannot have an infinite chain because that would mean we must have a "set-repeat" that
is not allowed.

-/

lemma move_inside_FL {p next} (mov : move p next) : next.2.1.subseteqFL p.2.1 := by
  rcases mov with ⟨mov⟩
  cases mov
  case prPdl r => apply PdlRule.stays_in_FL r
  case buEnd ltX _ _ _ _ Y_in => simp only []; apply LocalTableau.stays_in_FL ltX _ Y_in
  case prLocTab => simp

/-- Given `~⌈α₁⌉…⌈αₙ⌉φ`, return the list of `~⌊α₁⌋…⌊αₖ⌋⌈αₖ₊₁⌉…⌈αₙ⌉φ` for all k. -/
def Formula.allNegLoads : Formula → List NegLoadFormula
| ~φ => match boxesOf φ with
    | ([], _) => []
    | (α :: αs, ψ) => do
        let k ← (List.range' 1 (α :: αs).length).attach
        have : (α :: αs).take k ≠ [] := by aesop
        return ~'(loadMultiNonEmpty ((α :: αs).take k) this (⌈⌈(α :: αs).drop k⌉⌉ψ))
| _ => []

lemma Formula.allNegLoads_spec {nχ φ} : nχ ∈ φ.allNegLoads → negUnload nχ = φ := by
  cases φ <;> try (simp [allNegLoads]; done)
  case neg χ =>
  cases χ <;> try (simp [allNegLoads,boxesOf]; done)
  case box α φ =>
    rcases nχ with ⟨χ⟩
    simp only [allNegLoads, List.length_cons, List.pure_def, List.bind_eq_flatMap, negUnload,
      neg.injEq]
    split
    next h => exfalso; cases h
    next β βs ψ h =>
      simp only [List.mem_flatMap, List.mem_attach, List.mem_cons, NegLoadFormula.neg.injEq,
        List.not_mem_nil, or_false, true_and, Subtype.exists, List.mem_range'_1,
        forall_exists_index, forall_and_index]
      intro k one_le_k k_lt χ_def
      have := def_of_boxesOf_def h
      rw [this]; clear this
      subst χ_def
      simp only [loadMulti_nonEmpty_unload, boxes_cons]
      rw [← @boxes_append]
      rw [@List.take_append_drop]
      rfl

lemma Formula.allNegLoads_complete {nχ φ} : negUnload nχ = φ → nχ ∈ φ.allNegLoads := by
  rcases nχ with ⟨χ⟩
  simp only [negUnload]
  intro def_φ
  subst def_φ
  have := LoadFormula.exists_loadMulti χ
  rcases this with ⟨αs, α, φ, def_χ⟩
  have := @loadMulti_nonEmpty_eq_loadMulti αs α (by simp) φ
  rw [← this] at def_χ; clear this
  rw [def_χ]; clear def_χ
  simp only [allNegLoads, loadMulti_nonEmpty_unload, List.length_cons, List.pure_def,
    List.bind_eq_flatMap]
  split
  · exfalso
    cases αs <;> simp_all [boxesOf]
  next β βs ψ boxes_def =>
    simp only [List.mem_flatMap, List.mem_attach, List.mem_cons, NegLoadFormula.neg.injEq,
      List.not_mem_nil, or_false, true_and, Subtype.exists, List.mem_range'_1]
    use (αs ++ [α]).length
    simp only [List.length_append, List.length_cons, List.length_nil, zero_add, List.take_succ_cons,
      List.drop_succ_cons, le_add_iff_nonneg_left, zero_le, true_and]
    have := Formula.boxesOf_boxes_prefix (αs ++ [α]) φ
    rcases this with ⟨γs, αs_α_γs_eq_boxes⟩
    simp only [List.append_assoc, List.cons_append, List.nil_append, boxes_def] at αs_α_γs_eq_boxes
    refine ⟨?_, ?_⟩
    · have : (αs ++ α :: γs).length = (β :: βs).length := by simp_all
      simp only [List.length_append, List.length_cons] at this
      omega
    · -- This was tricky.
      rw [@loadMulti_nonEmpty_eq_loadMulti]
      have := def_of_boxesOf_def boxes_def
      cases αs
      · simp_all
      case cons β αs =>
      simp only [loadMulti_cons, List.length_cons]
      simp only [List.cons_append, boxes_cons, box.injEq] at this
      rcases this with ⟨β_, this⟩
      subst β_
      simp only [List.cons_append, List.cons.injEq, true_and] at αs_α_γs_eq_boxes
      subst αs_α_γs_eq_boxes
      simp only [List.drop_length_add_append, List.drop_succ_cons, List.drop_zero, ne_eq,
        List.take_eq_nil_iff, Nat.add_eq_zero_iff, List.length_eq_zero_iff, one_ne_zero, and_false,
        List.append_eq_nil_iff, reduceCtorEq, or_self, not_false_eq_true, loadMulti_nonEmpty_box,
        LoadFormula.box.injEq, AnyFormula.loaded.injEq, true_and]
      -- Doable from here.
      simp only [boxes_append, boxes_cons, boxes_nil, boxes_injective, box.injEq, true_and] at this
      rw [this]
      apply LoadFormula.split_eq_loadMulti_nonEmpty (loadMulti αs α (⌈⌈γs⌉⌉ψ))
      rw [loadMulti_split]
      simp [List.take_length_add_append]

open Classical in -- needed for `Finset.instMonad`, but why actually?
/-- A list of sequents that are all FL-subsequents of the given sequent.
Defined using `Finset.instMonad`.
-/
noncomputable def Sequent.allSubseteqFL (Y : Sequent) :
    Finset { X : Sequent // Sequent.subseteqFL X Y } := do
  -- QUESTION: any way to do sublist and permutation in one go?
  -- Never mind, removed `.flatMap List.permutations` again which really should not be needed.
  -- Trying out different orders `.sublists.attach` and `.attach.sublists` here.
  let XL  ← ((Y.L ∪ Y.O.L).FL).powerset.attach
  let XOL ← ((Y.L ∪ Y.O.L).FL).powerset.attach
  let XR  ← ((Y.R ∪ Y.O.R).FL).powerset.attach
  let XOR ← ((Y.R ∪ Y.O.R).FL).powerset.attach
  -- Now we still need to generate all possible `XO : Olf` from `XOL` and `XOR`.
  let OLs : Finset Olf:= XOL.1.sup (fun φ => φ.allNegLoads.toFinset.image (some ∘ Sum.inl))
  let ORs : Finset Olf:= XOR.1.sup (fun φ => φ.allNegLoads.toFinset.image (some ∘ Sum.inr))
  let XO ← ({(none : Olf)} ∪ OLs ∪ ORs).attach
  let X : Sequent := ⟨XL.1, XR.1, XO.1⟩
  have h : X.subseteqFL Y := by
    unfold X
    rcases Y with ⟨L',R',O'⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Finset.singleton_union, L_eq, O_eq, R_eq]
    · have := XL.2
      simp only [Finset.mem_powerset, Sequent.L_eq, Sequent.O_eq] at this
      exact this
    · simp only [Olf.L]
      rcases XO with ⟨none|⟨(nχ|_)⟩, XO_in⟩ <;> try simp_all only [Finset.empty_subset,
        Finset.singleton_subset_iff]
      simp only [Finset.singleton_union, Finset.insert_union, Finset.mem_insert, reduceCtorEq,
        Finset.mem_union, Finset.mem_sup, Finset.mem_image, List.mem_toFinset, Function.comp_apply,
        Option.some.injEq, Sum.inl.injEq, exists_eq_right, and_false, exists_false,
        or_false, false_or, OLs, ORs] at XO_in
      rcases XO_in with ⟨φ, φ_in, nχ_in⟩
      have := Formula.allNegLoads_spec nχ_in
      simp only [negUnload] at this
      rw [this]
      suffices φ ∈ (L' ∪ O'.L).FL by aesop
      have := XOL.2
      simp only [Finset.mem_powerset, L_eq, O_eq] at this
      exact this φ_in
    · have := XR.2
      simp only [Finset.mem_powerset, R_eq, O_eq] at this
      exact this
    · simp only [Olf.R]
      rcases XO with ⟨none|⟨(nχ|_)⟩, XO_in⟩ <;> try simp_all only [Finset.empty_subset,
        Finset.singleton_subset_iff]
      simp only [Finset.singleton_union, Finset.insert_union, Finset.mem_insert, reduceCtorEq,
        Finset.mem_union, Finset.mem_sup, Finset.mem_image, List.mem_toFinset, Function.comp_apply,
        Option.some.injEq, and_false, exists_false, Sum.inr.injEq, exists_eq_right,
        false_or, OLs, ORs] at XO_in
      rcases XO_in with ⟨φ, φ_in, nχ_in⟩
      have := Formula.allNegLoads_spec nχ_in
      simp only [negUnload] at this
      rw [this]
      suffices φ ∈ (R' ∪ O'.R).FL by aesop
      have := XOR.2
      simp only [Finset.mem_powerset, R_eq, O_eq] at this
      exact this φ_in
  return ⟨X, h⟩

/-! The following only hold because there we are now working with `Finset`. -/

/-- Any `Olf` is among those generated from its own left and right parts.
This is the key step to show that `Sequent.allSubseteqFL` generates all `Olf` values. -/
lemma Olf.mem_allNegLoads_of_L_R (YO : Olf) :
    YO ∈ ({none} ∪ (YO.L).sup fun φ ↦ Finset.image (some ∘ Sum.inl) φ.allNegLoads.toFinset) ∪
      (YO.R).sup fun φ ↦ Finset.image (some ∘ Sum.inr) φ.allNegLoads.toFinset := by
  rcases YO with _|(χ|χ)
  · simp
  · rcases χ with ⟨lf⟩
    simp only [Olf.L, Finset.mem_union, Finset.mem_singleton, Finset.mem_sup, Finset.mem_image,
      List.mem_toFinset, Function.comp_apply]
    exact Or.inl (Or.inr ⟨_, rfl, ~'lf, Formula.allNegLoads_complete rfl, rfl⟩)
  · rcases χ with ⟨lf⟩
    simp only [Olf.R, Finset.mem_union, Finset.mem_singleton, Finset.mem_sup, Finset.mem_image,
      List.mem_toFinset, Function.comp_apply]
    exact Or.inr ⟨_, rfl, ~'lf, Formula.allNegLoads_complete rfl, rfl⟩

lemma Sequent.all_subseteq_FL_complete (X Y : Sequent) (h : Y.subseteqFL X) :
    ⟨Y,h⟩ ∈ Sequent.allSubseteqFL X := by
  unfold Sequent.allSubseteqFL
  simp only [bind]
  refine (@Finset.mem_sup _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mpr
    ⟨⟨Y.L, Finset.mem_powerset.mpr h.1⟩, Finset.mem_attach _ _, ?_⟩
  refine (@Finset.mem_sup _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mpr
    ⟨⟨Y.O.L, Finset.mem_powerset.mpr h.2.1⟩, Finset.mem_attach _ _, ?_⟩
  refine (@Finset.mem_sup _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mpr
    ⟨⟨Y.R, Finset.mem_powerset.mpr h.2.2.1⟩, Finset.mem_attach _ _, ?_⟩
  refine (@Finset.mem_sup _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mpr
    ⟨⟨Y.O.R, Finset.mem_powerset.mpr h.2.2.2⟩, Finset.mem_attach _ _, ?_⟩
  refine (@Finset.mem_sup _ _ (fun a b => Classical.propDecidable (a = b)) _ _ _).mpr
    ⟨⟨Y.O, Olf.mem_allNegLoads_of_L_R Y.O⟩, Finset.mem_attach _ _, ?_⟩
  rcases Y with ⟨YL, YR, YO⟩
  simp [pure]

noncomputable instance Sequent.subseteqFLFintype {X : Sequent} :
    Fintype { Y // Sequent.subseteqFL Y X } :=
  ⟨ Sequent.allSubseteqFL X, fun ⟨Y, Y_in⟩ => X.all_subseteq_FL_complete Y Y_in ⟩

/-- The finite set of sequents contained in the Fischer-Ladner closure of a sequent. -/
noncomputable def Sequent.allSeqtSubseteqFL (X : Sequent) : Finset Sequent :=
  (X.allSubseteqFL.image (fun x => x.1))

/-! ## New stuff, now about Sequent instead of Seqt -/

/-- There are only finitely many FL-subset Sequents for a given Sequent.
This means "there are only finitely many "sequents modulo `setEq`" that are subseteqFL Y. -/
lemma Seqt.subseteq_FL_finite {X : Sequent} : Finite { Y // Sequent.subseteqFL Y X } :=
  @Finite.of_fintype { Y // Sequent.subseteqFL Y X } Sequent.subseteqFLFintype

/-- Helper lemma for `matchesFinite`: If we have enumerate infinitely many values, and all of them
have a certain property, but we also know that there are only finitely many values with that
property, then there must be identical values in the enumeration. -/
lemma exist_duplicates_of_infinite_among_fintype {α : Type} {f : ℕ → α} {p : α → Prop}
    (h_p : ∀ n, p (f n)) (h_fin : Finite {x // p x})
    : ∃ k1 k2, k1 ≠ k2 ∧ f k1 = f k2 := by
  -- Because {x // p x} is finite, also Set.range f is finite.
  have range_finite : Finite (Set.range f) := by
    apply Set.Finite.subset h_fin
    intro x ⟨n, def_x⟩
    subst def_x
    exact h_p n
  -- ℕ is infinite, so f cannot be injective
  have not_injective : ¬Function.Injective f := by
    intro hinj
    -- If f were injective, then Set.range f would be infinite (bijective with ℕ)
    have : Infinite (Set.range f) := by
      rw [@Set.infinite_coe_iff]
      have := Infinite.of_injective f hinj
      exact Set.infinite_range_of_injective hinj
    exact this.not_finite range_finite
  -- Non-injective means there exist distinct inputs with same output
  rw [Function.Injective] at not_injective
  push Not at not_injective
  tauto

/-! ### Infinite chains of moves

Towards `matchesFinite` we here collect facts about an infinite chain `g : ℕ → GamePos` with
`move (g n) (g (n+1))` for all `n`, following the proof idea for the `matchesFinite` lemma:

- at each position of the chain a move is possible, hence there is no forbidden repeat,
  i.e. `¬ flprep` (see `moveChain_not_flprep`);
- all sequents along the chain stay inside the FL closure of the first one
  (see `moveChain_inside_FL`), of which there are only finitely many modulo `setEqTo`
  (see `Seqt.subseteq_FL_finite`);
- the history at a later position contains the sequents of all earlier positions
  (see `moveChain_hist_accum` and `moveChain_hist_split`);
- hence a sequent that is `setEqTo` an earlier one must be loaded, because a free repeat
  would have ended the match (see `moveChain_setEq_isLoaded`), and thus from some point
  onwards *all* sequents in the chain are loaded (see `moveChain_eventually_loaded`);
- a repeat in this loaded part gives a loaded-path repeat, which also ends the match
  (see `moveChain_hist_index` and `moveChain_multisetEq_absurd`).

This section is from aristotle.harmonic.fun -/

/-- If a move from `⟨H, X, p⟩` is possible, then `X` is neither a free repeat nor a
loaded-path repeat in `H`. Note this is stronger than `move_then_no_frep`. -/
lemma move_then_not_flprep {H X next} {p : (ProverPos H X ⊕ BuilderPos H X)} :
    move ⟨H, X, p⟩ next → ¬ flprep H X := by
  simp only [move, Nonempty.forall]
  intro next_p hyp
  cases next_p <;> grind

/-- Helper lemma for `matchesFinite`: if a property of natural numbers holds arbitrarily late,
then we can enumerate witnesses for it with gaps of at least two. -/
lemma exists_spread_subsequence {P : ℕ → Prop} (hS : ∀ N, ∃ n, N ≤ n ∧ P n) :
    ∃ e : ℕ → ℕ, (∀ k, P (e k)) ∧ ∀ k1 k2, k1 < k2 → e k1 + 2 ≤ e k2 := by
  classical
  let e : ℕ → ℕ := fun k => Nat.rec (Classical.choose (hS 0))
    (fun _ prev => Classical.choose (hS (prev + 2))) k
  have e_succ : ∀ k, e (k + 1) = Classical.choose (hS (e k + 2)) := fun _ => rfl
  have hP : ∀ k, P (e k) := by
    intro k
    cases k with
    | zero => exact (Classical.choose_spec (hS 0)).2
    | succ k => rw [e_succ]; exact (Classical.choose_spec (hS (e k + 2))).2
  have step : ∀ k, e k + 2 ≤ e (k + 1) := by
    intro k
    rw [e_succ]
    exact (Classical.choose_spec (hS (e k + 2))).1
  refine ⟨e, hP, ?_⟩
  intro k1 k2 hk
  induction k2 with
  | zero => omega
  | succ k IH =>
    rcases Nat.lt_or_ge k1 k with h | h
    · have := IH h
      have := step k
      omega
    · have : k1 = k := by omega
      subst this
      exact step k1

section MoveChain

variable {g : ℕ → GamePos} (g_rel : ∀ n, move (g n) (g (n + 1)))
include g_rel

/-- Because a move is possible, no position in the chain is a forbidden repeat. -/
lemma moveChain_not_flprep (n : ℕ) : ¬ flprep (g n).1 (g n).2.1 := by
  have h := g_rel n
  rcases hn : g n with ⟨H, X, p⟩
  rw [hn] at h
  exact move_then_not_flprep h

/-- One step in the chain either keeps history and sequent (the `prLocTab` case)
or adds the current sequent to the history. -/
lemma moveChain_hist_step (n : ℕ) :
    ((g (n + 1)).1 = (g n).1 ∧ (g (n + 1)).2.1 = (g n).2.1)
    ∨ (g (n + 1)).1 = (g n).2.1 :: (g n).1 := by
  have h := g_rel n
  rcases hn : g n with ⟨H, X, p⟩
  rw [hn] at h
  rcases move.hist h with ⟨newPos, h'⟩ | ⟨Y, newPos, h'⟩
  · left; rw [h']; simp
  · right; rw [h']

/-- The history only grows, and everything added to it are sequents from the chain. -/
lemma moveChain_hist_accum (m : ℕ) :
    ∀ n, m ≤ n → ∃ pre : List Sequent, (g n).1 = pre ++ (g m).1
      ∧ ∀ Y ∈ pre, ∃ j, m ≤ j ∧ j < n ∧ Y = (g j).2.1 := by
  intro n
  induction n with
  | zero =>
    intro h
    have : m = 0 := by omega
    subst this
    exact ⟨[], by simp, by simp⟩
  | succ k IH =>
    intro h
    by_cases hmk : m ≤ k
    · obtain ⟨pre, hpre, hall⟩ := IH hmk
      rcases moveChain_hist_step g_rel k with ⟨h1, _⟩ | h1
      · refine ⟨pre, by rw [h1, hpre], fun Y hY => ?_⟩
        obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
        exact ⟨j, hj1, by omega, hj3⟩
      · refine ⟨(g k).2.1 :: pre, ?_, ?_⟩
        · rw [h1, List.cons_append]
          exact congrArg (fun l => (g k).2.1 :: l) hpre
        · rintro Y hY
          rcases List.mem_cons.mp hY with rfl | hY
          · exact ⟨k, hmk, by omega, rfl⟩
          · obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
            exact ⟨j, hj1, by omega, hj3⟩
    · have : m = k + 1 := by omega
      subst this
      exact ⟨[], by simp, by simp⟩

/-- After at least two moves the sequent of the earlier position is in the later history,
and all newer entries of that history are sequents from strictly in between. -/
lemma moveChain_hist_split {m n : ℕ} (h : m + 2 ≤ n) :
    ∃ pre : List Sequent, (g n).1 = pre ++ ((g m).2.1 :: (g m).1)
      ∧ ∀ Y ∈ pre, ∃ j, m < j ∧ j < n ∧ Y = (g j).2.1 := by
  rcases moveChain_hist_step g_rel m with ⟨h1, hX1⟩ | h1
  · -- The step from `m` did not change the history, hence the next one must do so.
    have h2 : (g (m + 2)).1 = (g m).2.1 :: (g m).1 := by
      rcases moveChain_hist_step g_rel (m + 1) with ⟨h2, _⟩ | h2
      · exfalso
        have := move_twice_hist_length (g_rel m) (g_rel (m + 1))
        rw [show m + 1 + 1 = m + 2 from rfl] at h2
        rw [h2, h1] at this
        omega
      · rw [show m + 2 = m + 1 + 1 from rfl, h2]
        exact congrArg₂ (· :: ·) hX1 h1
    obtain ⟨pre, hpre, hall⟩ := moveChain_hist_accum g_rel (m + 2) n (by omega)
    refine ⟨pre, by rw [hpre, h2], fun Y hY => ?_⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
    exact ⟨j, by omega, hj2, hj3⟩
  · obtain ⟨pre, hpre, hall⟩ := moveChain_hist_accum g_rel (m + 1) n (by omega)
    refine ⟨pre, by rw [hpre, h1], fun Y hY => ?_⟩
    obtain ⟨j, hj1, hj2, hj3⟩ := hall Y hY
    exact ⟨j, by omega, hj2, hj3⟩

/-- All sequents in the chain stay inside the FL closure of the first sequent. -/
lemma moveChain_inside_FL (n : ℕ) : Sequent.subseteqFL (g n).2.1 (g 0).2.1 := by
  simp only [Sequent.subseteqFL]
  induction n
  · exact Sequent.subseteq_FL_refl _
  case succ k IH =>
    apply Sequent.subseteq_FL_trans _ _ _ ?_ IH
    apply move_inside_FL (g_rel k)

/-- A sequent in the chain that is `setEqTo` an earlier one must be loaded,
because otherwise we would have a free repeat and the match would have ended. -/
lemma moveChain_setEq_isLoaded {m n : ℕ} (h : m + 2 ≤ n) (hs : (g m).2.1 = (g n).2.1) :
    (g n).2.1.isLoaded := by
  obtain ⟨pre, hpre, _⟩ := moveChain_hist_split g_rel h
  have h_rep : rep (g n).1 (g n).2.1 := by
    refine ⟨(g m).2.1, ?_, hs⟩
    rw [hpre]
    simp
  by_contra hfree
  exact moveChain_not_flprep g_rel n (Or.inl ⟨h_rep, by simp [Sequent.isFree, hfree]⟩)

/-- Because there are only finitely many sequents modulo `setEqTo` inside the FL closure,
arbitrarily late in the chain we find two positions with `setEqTo` sequents. -/
lemma moveChain_exists_setEq_late (N : ℕ) :
    ∃ m n, N ≤ m ∧ m + 2 ≤ n ∧ (g m).2.1 = (g n).2.1 := by
  obtain ⟨e, hP, hgap⟩ := exists_spread_subsequence (P := fun n => N ≤ n)
    (fun M => ⟨max M N, le_max_left _ _, le_max_right _ _⟩)
  obtain ⟨k1, k2, hne, hsame⟩ := @exist_duplicates_of_infinite_among_fintype _
    (fun k => ((g (e k)).2.1 : Sequent)) (Sequent.subseteqFL · (g 0).2.1)
    (fun k => moveChain_inside_FL g_rel (e k)) Seqt.subseteq_FL_finite
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · exact ⟨e k1, e k2, hP k1, hgap k1 k2 hlt, hsame⟩
  · exact ⟨e k2, e k1, hP k2, hgap k2 k1 (by omega), Eq.symm hsame⟩

/-- From some point onwards all sequents in the chain are loaded: there are only finitely
many sequents modulo `setEqTo`, and free ones can never come back. -/
lemma moveChain_eventually_loaded : ∃ N, ∀ n, N ≤ n → (g n).2.1.isLoaded := by
  by_contra hyp
  push Not at hyp
  obtain ⟨e, hP, hgap⟩ := exists_spread_subsequence hyp
  obtain ⟨k1, k2, hne, hsame⟩ := @exist_duplicates_of_infinite_among_fintype _
    (fun k => ((g (e k)).2.1 : Sequent)) (Sequent.subseteqFL · (g 0).2.1)
    (fun k => moveChain_inside_FL g_rel (e k)) Seqt.subseteq_FL_finite
  rcases Nat.lt_or_ge k1 k2 with hlt | hge
  · exact absurd (moveChain_setEq_isLoaded g_rel (hgap k1 k2 hlt) hsame) (hP k2)
  · exact absurd (moveChain_setEq_isLoaded g_rel (hgap k2 k1 (by omega))
      (Eq.symm hsame)) (hP k1)

/-- If all sequents from `N` onwards are loaded and `N ≤ m` with `m + 2 ≤ n`, then the sequent
of position `m` occurs in the history of position `n` at an index such that all entries up to
and including that index are loaded. This is what is needed for a loaded-path repeat. -/
lemma moveChain_hist_index {N m n : ℕ} (hN : ∀ j, N ≤ j → (g j).2.1.isLoaded)
    (hm : N ≤ m) (h : m + 2 ≤ n) :
    ∃ k : Fin (g n).1.length,
      (g n).1.get k = (g m).2.1 ∧ ∀ i ≤ k, ((g n).1.get i).isLoaded := by
  obtain ⟨pre, hpre, hall⟩ := moveChain_hist_split g_rel h
  have hlen : pre.length < (g n).1.length := by
    rw [hpre]; simp
  refine ⟨⟨pre.length, hlen⟩, ?_, ?_⟩
  · simp only [List.get_eq_getElem]
    rw [List.getElem_of_eq hpre, List.getElem_append_right (by omega)]
    simp
  · rintro ⟨i, hi⟩ hik
    simp only [List.get_eq_getElem, Fin.mk_le_mk] at *
    rcases Nat.lt_or_ge i pre.length with hlt | hge
    · have hmem : (g n).1[i] ∈ pre := by
        rw [List.getElem_of_eq hpre, List.getElem_append_left hlt]
        exact List.getElem_mem hlt
      obtain ⟨j, hj1, hj2, hj3⟩ := hall _ hmem
      rw [hj3]
      exact hN j (by omega)
    · have hieq : i = pre.length := by omega
      have : (g n).1[i] = (g m).2.1 := by
        rw [List.getElem_of_eq hpre, List.getElem_append_right (by omega)]
        simp [hieq]
      rw [this]
      exact hN m hm

/-- A `setEqTo` repeat in the loaded part of the chain is impossible:
it would be a loaded-path repeat, at which the match ends. -/
lemma moveChain_setEq_absurd {N m n : ℕ} (hN : ∀ j, N ≤ j → (g j).2.1.isLoaded)
    (hm : N ≤ m) (h : m + 2 ≤ n) (hs : (g m).2.1 = (g n).2.1) : False := by
  obtain ⟨k, hk1, hk2⟩ := moveChain_hist_index g_rel hN hm h
  exact moveChain_not_flprep g_rel n (Or.inr ⟨⟨k, by rw [hk1]; exact hs, hk2⟩⟩)

end MoveChain

/-- Lemma 6.11. The move relation is converse wellfounded (and thus all matches must be finite).
This is similar to the proof that PDL-tableaux are finite (Lemma 4.10), relying on the finiteness
of the Fischer-Ladner closure.
In Lean we never needed to say 4.10 because values of the inductive type `Tableau` are always
finite by constriction. But we do need a proof here, as this lemma is about `move`, not `Match`.

The whole argument is done in the `MoveChain` section above. -/
lemma matchesFinite : WellFounded (Function.swap move) := by
  -- If it's not wellfounded, then there must be an infinite sequence of moves.
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hyp
  simp only [not_isEmpty_iff, nonempty_subtype] at hyp
  rcases hyp with ⟨g, g_rel⟩
  simp only [Function.swap] at g_rel
  -- From some point `N` onwards all sequents in the chain are loaded.
  obtain ⟨N, hN⟩ := moveChain_eventually_loaded g_rel
  -- In this loaded part we find a repeat, which is a loaded-path repeat, ending the match.
  obtain ⟨m, n, hm, hmn, hs⟩ := moveChain_exists_setEq_late g_rel N
  exact moveChain_setEq_absurd g_rel hN hm hmn hs

/-! ## Actual Game Definition -/

/-- The game defined in Section 6.2. -/
@[instance_reducible]
def tableauGame : Game where
  Pos := GamePos
  turn | ⟨_, _, .inl _⟩ => Prover
       | ⟨_, _, .inr _⟩ => Builder
  moves := theMoves
  wf := ⟨fun x y => move y x, matchesFinite⟩
  move_rel := by grind [move_of_mem_theMoves]

/-- This helps to pick up the derived instance `DecidableEq GamePos` above. -/
instance instDecidableEqPos : DecidableEq tableauGame.Pos := by
  change DecidableEq GamePos
  exact instDecidableEqOfLawfulBEq

@[simp]
lemma tableauGame_turn_Prover {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inl lpr⟩ = Prover := by
  unfold Game.turn
  unfold tableauGame
  simp

@[simp]
lemma tableauGame_turn_Builder {Hist X lpr} :
    tableauGame.turn ⟨Hist, X, .inr lpr⟩ = Builder := by
  unfold Game.turn tableauGame
  simp

@[simp]
lemma tableauGame_winner_nlpRep_eq_Builder {Hist X} {h : rep Hist X ∧ X.isFree}
    {sI : Strategy tableauGame i} {sJ : Strategy tableauGame (other i)} :
    @winner i tableauGame sI sJ ⟨Hist, X, .inl (.frep h)⟩ = Builder := by
  have hm : tableauGame.moves ⟨Hist, X, .inl (.frep h)⟩ = ∅ := rfl
  rw [winner]
  simp [hm]

@[simp]
lemma tableauGame_winner_lpr_eq_Prover {Hist lpr sI sJ} :
    @winner i tableauGame sI sJ ⟨Hist, X, .inr (.lpr lpr)⟩ = Prover := by
  have hm : tableauGame.moves ⟨Hist, X, .inr (.lpr lpr)⟩ = ∅ := rfl
  rw [winner]
  simp [hm]

/-! ## From Prover winning strategies to tableau -/
/-- A game position is *uniform* if any local tableau in it is the canonical one. -/
def GamePos.IsUni : GamePos → Prop
  | ⟨_, X, .inr (.ltab _ _ lt)⟩ => lt = uniLocalTab X
  | _ => True

/-- Positions given by `posOf` are uniform: they are never `ltab` positions. -/
lemma posOf_isUni (H : History) (X : Sequent) : GamePos.IsUni ⟨H, X, posOf H X⟩ := by
  unfold posOf
  split
  · trivial
  · split
    · trivial
    · split <;> trivial

/-- All moves lead to uniform positions. -/
lemma theMoves_isUni {p next : GamePos} (h : next ∈ theMoves p) : GamePos.IsUni next := by
  rcases move_of_mem_theMoves h with ⟨mov⟩
  cases mov
  case prPdl => exact posOf_isUni _ _
  case prLocTab => rfl
  case buEnd => exact posOf_isUni _ _

/-! ## From Prover winning strategies to uniform tableaux -/

/-- Helper for `gameP_general`: prefixing a uniform tableau with a PDL rule keeps it uniform. -/
lemma exists_isUni_of_pdl {Hist X Y} (nrep : ¬ flprep Hist X) (bas : X.basic) (r : PdlRule X Y)
    {next : Tableau (X :: Hist) Y} (h : next.IsUni) : ∃ tab : Tableau Hist X, tab.IsUni :=
  ⟨.pdl nrep bas r next, h⟩

/-- After history `Hist`, if Prover has a winning strategy then there is a closed tableau,
and moreover that tableau is uniform in the sense of `Tableau.IsUni`, because
Prover has to play the canonical local tableau `uniLocalTab`.
Note: we skip Definition 6.9 (Strategy Tree for Prover) and just use the `Strategy` type.
This is the induction loading for `gameP`. -/
theorem gameP_general Hist (X : Sequent) (sP : Strategy tableauGame Prover) (pos : _)
    (pos_uni : GamePos.IsUni ⟨Hist, X, pos⟩)
    (h : winning sP ⟨Hist, X, pos⟩)
    : ∃ tab : Tableau Hist X, tab.IsUni := by
  rcases pos_def : pos with proPos|builPos
  -- ProverPos:
  · cases proPos
    · -- free repeat, but then Prover loses, which contradicts h.
      absurd h
      simp [pos_def,winning]
    case bas nrep Xbas =>
      -- basic, Prover should choose PDL rule
      rw [pos_def] at h
      have P_turn : tableauGame.turn ⟨Hist, ⟨X, pos⟩⟩ = Prover := by
        rw [pos_def]
        simp
      -- Ask `sP` say which move to make / what rule to apply.
      let the_move := sP ⟨_ ,_, pos⟩ ?_ ?_
      case refine_1 => rw [pos_def]; unfold Game.turn tableauGame; simp
      case refine_2 => by_contra hyp; exfalso; unfold winning winner at h; simp_all
      -- Using lemma that if sP is winning here then sP is still winning after sP moves.
      have still_winning : winning sP the_move := winning_of_winning_move P_turn (pos_def ▸ h)
      -- Now use IH to get the remaining tableau.
      have IH := gameP_general _ _ sP _ (theMoves_isUni the_move.2) still_winning -- okay ??
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp only at IH
      obtain ⟨new_tab_from_IH, new_uni⟩ := IH
      simp only [Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      rcases X with ⟨L,R,_|(⟨⟨χ⟩⟩|⟨⟨χ⟩⟩)⟩ <;> simp only [theMoves, Finset.mem_union,
        Finset.mem_sup, Finset.singleton_union, Finset.union_singleton] at *
      · -- no loaded formula yet, the only PDL rule we can apply is (L+)
        rcases nextPosIn with ⟨χ, χ_in⟩|⟨χ, χ_in⟩
        · cases χ
          case neg φ =>
            have notBox : ¬ (boxesOf φ).2.isBox := boxesOf_output_not_isBox
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, Finset.mem_singleton]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              refine exists_isUni_of_pdl nrep Xbas
                (@PdlRule.loadL _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_) new_uni
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
                simp_all only [Formula.boxes_cons]
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
          all_goals -- other formulas, cannot have empty boxesOf
            exfalso
            simp at χ_in
        -- COPY-PASTA only changed loadL to loadR
        · cases χ
          case neg φ =>
            have notBox : ¬ (boxesOf φ).2.isBox := boxesOf_output_not_isBox
            rcases boxesOf_def : boxesOf φ with ⟨_|⟨δ,αs⟩, ψ⟩
            · exfalso; simp [boxesOf_def] at χ_in
            · simp_all only [tableauGame_turn_Prover, Finset.mem_singleton]
              rcases χ_in with ⟨ψ_in, ⟨_⟩⟩
              have : φ = ⌈⌈δ :: αs⌉⌉ψ := def_of_boxesOf_def boxesOf_def
              subst this
              refine exists_isUni_of_pdl nrep Xbas
                (@PdlRule.loadR _ ((δ :: αs).dropLast)
                  ((δ :: αs).getLast (by simp)) ψ _ _ ?_ notBox ?_) new_uni
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
                simp_all only [Formula.boxes_cons]
              · rw [← boxes_last]
                rw [@List.dropLast_append_getLast]
          all_goals -- other formulas, cannot have empty boxesOf
            exfalso
            simp at χ_in
      · -- already have loaded formula in left, PDL rule must be (M) or (L-)
        rcases χ with ⟨α, (ψ : AnyFormula)⟩
        cases α
        case atom_prog a in_moves =>
          simp_all only [tableauGame_turn_Prover, Finset.mem_insert]
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (L-)
            cases nextPosIn
            cases ψ
            case normal φ0 =>
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeL _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeL _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp only [Finset.mem_singleton] at nextPosIn <;> cases nextPosIn
            all_goals
              exact exists_isUni_of_pdl nrep Xbas (PdlRule.modL rfl rfl) new_uni
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
      · -- COPY PASTA only changed L to R
        rcases χ with ⟨α, (ψ : AnyFormula)⟩
        cases α
        case atom_prog a in_moves =>
          simp_all only [tableauGame_turn_Prover, Finset.mem_insert]
          -- rule here could be (M) or (L-)
          rcases nextPosIn with nextPosIn|nextPosIn
          · -- applying (L-)
            cases nextPosIn
            cases ψ
            case normal φ0 =>
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeR _ L R [] _ φ0 _ _ rfl
              simp
            case loaded χ =>
              rcases LoadFormula.exists_loadMulti χ with ⟨δ,α,φ,χ_def⟩
              subst χ_def
              refine exists_isUni_of_pdl nrep Xbas ?_ new_uni
              apply @PdlRule.freeR _ L R (·a :: δ) _ _ _ rfl
              simp
          · -- applying (M)
            cases ψ <;> simp only [Finset.mem_singleton] at nextPosIn <;> cases nextPosIn
            all_goals
              exact exists_isUni_of_pdl nrep Xbas (by apply PdlRule.modR <;> rfl) new_uni
        all_goals
          -- non-atomic program is impossible, X would not have been basic then
          exfalso
          grind
    case nbas nrep X_nbas =>
      -- not basic, Prover must move to the uniform local tableau
      -- COPY PASTA from bas case ...
      rw [pos_def] at h
      have P_turn : tableauGame.turn ⟨Hist, ⟨X, pos⟩⟩ = Prover := by
        rw [pos_def]
        simp
      -- Ask `sP` say which move to make / what rule to apply.
      let the_move := sP ⟨_ ,_, pos⟩ ?_ ?_
      case refine_1 => rw [pos_def]; unfold Game.turn tableauGame; simp
      case refine_2 => by_contra hyp; exfalso; unfold winning winner at h; simp_all
      -- Using lemma that if sP is winning here then sP is still winning after sP moves.
      have still_winning : winning sP the_move := winning_of_winning_move P_turn (pos_def ▸ h)
      -- Now use IH to get the remaining tableau.
      have IH := gameP_general _ _ sP _ (theMoves_isUni the_move.2) still_winning -- okay ??
      rcases the_move with ⟨⟨newHist, newX, newPos⟩, nextPosIn⟩
      simp only at IH
      simp only [Game.Pos.moves, pos_def, Game.moves] at nextPosIn
      --- ... until here
      -- No need to look into the local tableau here, we use the IH for the `BuilderPos` case!
      simp only [theMoves, Finset.mem_singleton] at nextPosIn
      obtain ⟨rfl, rfl, -⟩ := nextPosIn
      exact IH
  -- BuilderPos:
  · rw [pos_def] at pos_uni
    rcases builPos with ⟨lpr⟩|⟨nrep, nbas, ltX⟩
    · exact ⟨Tableau.lrep lpr, trivial⟩
    · -- We have a local tableau and it is the turn of Builder.
      -- Now each `Y : endNodesOf lt` is a possible move.
      -- Because `sP` wins against all moves by Builder we can use `sP` to define `next`.
      -- Note that all is non-constructive here via choice.
      have ltX_def : ltX = uniLocalTab X := pos_uni
      subst ltX_def
      have next' : ∀ Y (_ : Y ∈ endNodesOf (uniLocalTab X)),
          ∃ t : Tableau (X :: Hist) Y, t.IsUni := by
        intro Y Y_in
        apply gameP_general (X :: Hist) Y sP (posOf (X :: Hist) Y) (posOf_isUni _ _) -- the IH
        subst pos_def
        -- The main work is done by the following lemma
        have := winning_of_whatever_other_move (by simp) h
        simp only [Game.moves, theMoves, Subtype.forall, Finset.mem_image, forall_exists_index,
          and_imp, forall_apply_eq_imp_iff₂] at this
        exact this _ Y_in
      choose next next_uni using next'
      exact ⟨Tableau.loc nrep nbas (uniLocalTab X) next, uniLocalTab_isUni X, next_uni⟩
termination_by
  tableauGame.wf.2.wrap ⟨Hist, X, pos⟩ -- note `pos`, not `posOf` here.
decreasing_by
  all_goals
    apply tableauGame.move_rel
    simp only [WellFounded.wrap, Sigma.eta, SetLike.coe_mem]
  · subst pos_def
    simp only [Game.moves, theMoves, Finset.mem_image]
    use Y

/-- The starting position for the given sequent.
With an empty history and using `posOf` to determine the first `GamePos`. -/
@[expose] def startPos (X : Sequent) : GamePos := ⟨[], X, posOf [] X⟩

/-- We start with a prover position, because when the history is empty we can't have any repeat. -/
lemma posOf_for_startPos (X : Sequent) : ∃ proPos, posOf [] X = Sum.inl proPos := by
  unfold posOf
  by_cases Nonempty (LoadedPathRepeat [] X)
  case pos h => rcases h with ⟨⟨_⟩⟩; grind
  case neg h =>
    simp only [h, ↓reduceDIte, not_rep_empty]
    by_cases X.basic <;> simp_all

/-- If Prover has a winning strategy then there is a closed tableau, and it is uniform. -/
theorem gameP (X : Sequent) (s : Strategy tableauGame Prover) (h : winning s (startPos X)) :
    ∃ tab : Tableau [] X, tab.IsUni := gameP_general [] X s _ (posOf_isUni _ _) h

/-- If Prover has a winning strategy then there is a *uniform* closed tableau,
i.e. one satisfying the conditions U1 and U2. -/
theorem gameP_isUniform (X : Sequent) (s : Strategy tableauGame Prover)
    (h : winning s (startPos X)) : ∃ tab : Tableau [] X, tab.isUniform := by
  obtain ⟨tab, tab_uni⟩ := gameP X s h
  exact ⟨tab, tab_uni.isUniform⟩

end PDL
