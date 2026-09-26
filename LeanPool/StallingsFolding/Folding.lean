/-
Copyright (c) 2026 Arthur Freitas Ramos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos
-/
module

public import LeanPool.StallingsFolding.InverseAutomaton
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Finset.Max

/-!
# Finite folding of labelled inverse multigraphs

This module implements the quotient step at the heart of Stallings folding.
The implementation is deliberately finite and exhaustive: it intersects all
equivalence relations that make the labelled multigraph deterministic. This
is a simple reference algorithm; a union-find implementation can later replace
it without changing the correctness interface.
-/

@[expose] public section

namespace Stallings

/-- An inverse-labelled multigraph with finite sets of outgoing targets.
Multiple edges with the same source
and label are allowed before folding. -/
structure InverseMultigraph (V : Type*) where
  /-- The finite collection of targets with a given source and label. -/
  edges : V → Letter → Finset V
  inverse_edges : ∀ (v : V) (x : Letter) (w : V),
    w ∈ edges v x ↔ v ∈ edges w (letterInv x)

/-- A Boolean relation is a fold congruence if it is an equivalence relation
and equivalent vertices have equivalent targets along equally-labelled edges. -/
def IsFoldCongruence {V : Type*}
    (G : InverseMultigraph V)
    (r : V → V → Bool) : Prop :=
  (∀ v, r v v = true) ∧
  (∀ v w, r v w = true → r w v = true) ∧
  (∀ u v w, r u v = true → r v w = true → r u w = true) ∧
  (∀ v w x u t, r v w = true → u ∈ G.edges v x → t ∈ G.edges w x → r u t = true)

instance foldCongruenceDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : InverseMultigraph V)
    (r : V → V → Bool) : Decidable (IsFoldCongruence G r) := by
  unfold IsFoldCongruence
  infer_instance

/-- Vertices are equivalent after all possible folds have been performed.

For a finite vertex type, the quantification is over a finite type of Boolean
relations, so this relation is decidable and executable. -/
def foldRel {V : Type*}
    (G : InverseMultigraph V) (v w : V) : Prop :=
  ∀ r : V → V → Bool, IsFoldCongruence G r → r v w = true

instance foldRelDecidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : InverseMultigraph V) (v w : V) :
    Decidable (foldRel G v w) := by
  unfold foldRel
  infer_instance

namespace foldRel

variable {V : Type*} (G : InverseMultigraph V)

theorem refl (v : V) : foldRel G v v := by
  intro r hr
  exact hr.1 v

theorem symm {v w : V} (h : foldRel G v w) : foldRel G w v := by
  intro r hr
  exact hr.2.1 v w (h r hr)

theorem trans {u v w : V} (huv : foldRel G u v) (hvw : foldRel G v w) :
    foldRel G u w := by
  intro r hr
  exact hr.2.2.1 u v w (huv r hr) (hvw r hr)

theorem edge_congr {v w u t : V} {x : Letter}
    (hvw : foldRel G v w) (hu : u ∈ G.edges v x) (ht : t ∈ G.edges w x) :
    foldRel G u t := by
  intro r hr
  exact hr.2.2.2 v w x u t (hvw r hr) hu ht

end foldRel

/-- The least representative of a fold-equivalence class. -/
def foldRep {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (v : V) : V :=
  ((Finset.univ : Finset V).filter fun w => foldRel G w v).min'
    ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, foldRel.refl G v⟩⟩

theorem foldRep_rel {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (v : V) :
    foldRel G (foldRep G v) v := by
  exact (Finset.mem_filter.mp
    (Finset.min'_mem ((Finset.univ : Finset V).filter fun w => foldRel G w v) _)).2

theorem foldRep_eq_of_rel {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) {v w : V}
    (h : foldRel G v w) : foldRep G v = foldRep G w := by
  have hsets :
      ((Finset.univ : Finset V).filter fun z => foldRel G z v) =
      ((Finset.univ : Finset V).filter fun z => foldRel G z w) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hz
      exact foldRel.trans G hz h
    · intro hz
      exact foldRel.trans G hz (foldRel.symm G h)
  simp only [foldRep, hsets]

theorem foldRep_idem {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (v : V) :
    foldRep G (foldRep G v) = foldRep G v :=
  foldRep_eq_of_rel G (foldRep_rel G v)

/-- All original targets reachable from any vertex in the current fold class. -/
def foldTargets {V : Type*} [Fintype V] [DecidableEq V]
    (G : InverseMultigraph V) (v : V) (x : Letter) :
    Finset V :=
  (Finset.univ : Finset V).filter fun t => ∃ u, foldRel G u v ∧ t ∈ G.edges u x

/-- Two targets of the same labelled edge out of a fold class are themselves
fold-equivalent. -/
theorem foldTargets_pair {V : Type*} [Fintype V] [DecidableEq V]
    (G : InverseMultigraph V) (v : V)
    (x : Letter) {u t : V} (hu : u ∈ foldTargets G v x)
    (ht : t ∈ foldTargets G v x) : foldRel G u t := by
  rcases Finset.mem_filter.mp hu with ⟨_, a, hav, hedgeA⟩
  rcases Finset.mem_filter.mp ht with ⟨_, b, hbv, hedgeB⟩
  exact foldRel.edge_congr G (foldRel.trans G hav (foldRel.symm G hbv)) hedgeA hedgeB

/-- A deterministic representative transition before restricting to canonical
representatives. -/
def foldedNextCore {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (v : V) (x : Letter) :
    Option V :=
  if h : (foldTargets G v x).Nonempty then
    some (foldRep G ((foldTargets G v x).min' h))
  else none

/-- The deterministic transition produced by folding. -/
def foldedNext {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (v : V) (x : Letter) :
    Option V :=
  if v = foldRep G v then foldedNextCore G v x else none

/-- The deterministic inverse automaton obtained by quotienting the multigraph. -/
def foldAutomaton {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (base : V) :
    InverseAutomaton V where
  base := foldRep G base
  next := foldedNext G
  inverse_next := by
    intro v x w h
    have hv : v = foldRep G v := by
      unfold foldedNext at h
      split at h
      · assumption
      · simp at h
    have hcore : foldedNextCore G v x = some w := by
      change (if v = foldRep G v then foldedNextCore G v x else none) = some w at h
      rw [ite_eq_left hv] at h
      exact h
    unfold foldedNextCore at hcore
    split_ifs at hcore with hne
    · simp only [Option.some.injEq] at hcore
      subst w
      let q := (foldTargets G v x).min' hne
      have hq : q ∈ foldTargets G v x := by
        exact Finset.min'_mem _ _
      rcases Finset.mem_filter.mp hq with ⟨_, u, huv, hedge⟩
      have hinv : u ∈ G.edges q (letterInv x) :=
        (G.inverse_edges u x q).mp hedge
      have huBack : u ∈ foldTargets G (foldRep G q) (letterInv x) := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, q, ?_, hinv⟩
        exact foldRel.symm G (foldRep_rel G q)
      have hqBack : (foldTargets G (foldRep G q) (letterInv x)).Nonempty :=
        ⟨u, huBack⟩
      have hminBack :
          foldRel G ((foldTargets G (foldRep G q) (letterInv x)).min' hqBack) u :=
        foldTargets_pair G (foldRep G q) (letterInv x)
          (Finset.min'_mem _ _) huBack
      have huv : foldRel G u v := huv
      have hbackRep :
          foldRep G ((foldTargets G (foldRep G q) (letterInv x)).min' hqBack) = v := by
        calc
          _ = foldRep G u := foldRep_eq_of_rel G hminBack
          _ = foldRep G v := foldRep_eq_of_rel G huv
          _ = v := hv.symm
      have hbackCore : foldedNextCore G (foldRep G q) (letterInv x) = some v := by
        unfold foldedNextCore
        rw [dite_eq_left hqBack]
        exact congrArg some hbackRep
      have hqCanonical : foldRep G q = foldRep G (foldRep G q) :=
        (foldRep_idem G q).symm
      change (if foldRep G q = foldRep G (foldRep G q) then
        foldedNextCore G (foldRep G q) (letterInv x) else none) = some v
      rw [ite_eq_left hqCanonical]
      exact hbackCore

namespace InverseMultigraph

variable {V : Type*} (G : InverseMultigraph V)

/-- A path in a multigraph records one chosen edge for each letter. -/
inductive Walk : V → Word → V → Prop where
  | nil (v : V) : Walk v [] v
  | cons {v u z : V} {x : Letter} {w : Word}
      (edge : u ∈ G.edges v x) (tail : Walk u w z) : Walk v (x :: w) z

/-- The subgroup generated by labels of based loops in the multigraph. -/
def loopSubgroup (base : V) : Subgroup Free :=
  Subgroup.closure {g : Free | ∃ w : Word, wordEval w = g ∧ G.Walk base w base}

end InverseMultigraph

/-- Every original edge induces the corresponding transition between fold
representatives. -/
theorem foldedNext_of_edge {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) {v t : V}
    {x : Letter} (hedge : t ∈ G.edges v x) :
    foldedNext G (foldRep G v) x = some (foldRep G t) := by
  have hcanonical : foldRep G v = foldRep G (foldRep G v) :=
    (foldRep_idem G v).symm
  change (if foldRep G v = foldRep G (foldRep G v) then
    foldedNextCore G (foldRep G v) x else none) = some (foldRep G t)
  rw [ite_eq_left hcanonical]
  have ht : t ∈ foldTargets G (foldRep G v) x := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, v, foldRel.symm G (foldRep_rel G v), hedge⟩
  have hne : (foldTargets G (foldRep G v) x).Nonempty := ⟨t, ht⟩
  unfold foldedNextCore
  rw [dite_eq_left hne]
  have hmin : (foldTargets G (foldRep G v) x).min' hne ∈
      foldTargets G (foldRep G v) x := Finset.min'_mem _ _
  have hrel := foldTargets_pair G (foldRep G v) x hmin ht
  have hrep := foldRep_eq_of_rel G hrel
  rw [hrep]

/-- Folding preserves every path in the original multigraph, after mapping its
endpoints to their canonical representatives. -/
theorem foldWalk {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (base v z : V)
    {w : Word} (h : G.Walk v w z) :
    (foldAutomaton G base).run (foldRep G v) w = some (foldRep G z) := by
  induction h with
  | nil v => rfl
  | @cons v u z x w edge tail ih =>
      simp only [InverseAutomaton.run]
      change ((foldedNext G (foldRep G v) x).bind
        fun q => (foldAutomaton G base).run q w) = some (foldRep G z)
      rw [foldedNext_of_edge G edge]
      exact ih

/-- Equality of right cosets of a subgroup, in element form. -/
def CosetEquivalent (H : Subgroup Free) (g h : Free) : Prop := g * h⁻¹ ∈ H

namespace CosetEquivalent

theorem refl (H : Subgroup Free) (g : Free) : CosetEquivalent H g g := by
  simp [CosetEquivalent]

theorem symm {H : Subgroup Free} {g h : Free}
    (gh : CosetEquivalent H g h) : CosetEquivalent H h g := by
  change g * h⁻¹ ∈ H at gh
  change h * g⁻¹ ∈ H
  simpa using H.inv_mem gh

theorem trans {H : Subgroup Free} {g h k : Free}
    (gh : CosetEquivalent H g h) (hk : CosetEquivalent H h k) :
    CosetEquivalent H g k := by
  change g * h⁻¹ ∈ H at gh
  change h * k⁻¹ ∈ H at hk
  change g * k⁻¹ ∈ H
  have hmul : (g * h⁻¹) * (h * k⁻¹) ∈ H := H.mul_mem gh hk
  simpa [mul_assoc] using hmul

theorem mem_of_mem_and_rel {H : Subgroup Free} {g h : Free}
    (hgh : CosetEquivalent H g h) (hg : g ∈ H) : h ∈ H := by
  change g * h⁻¹ ∈ H at hgh
  have hhinv : h⁻¹ ∈ H := by
    have hm := H.mul_mem (H.inv_mem hg) hgh
    simpa [mul_assoc] using hm
  simpa using H.inv_mem hhinv

theorem right_mul {H : Subgroup Free} {g h : Free}
    (gh : CosetEquivalent H g h) (x : Free) : CosetEquivalent H (g * x) (h * x) := by
  change g * h⁻¹ ∈ H at gh
  change (g * x) * (h * x)⁻¹ ∈ H
  simpa [mul_assoc] using gh

end CosetEquivalent

/-- A potential assigns a free-group value to each vertex, consistently up to
left multiplication by `H` along every labelled edge. -/
def HasCosetPotential {V : Type*}
    (G : InverseMultigraph V) (H : Subgroup Free)
    (potential : V → Free) : Prop :=
  ∀ {v : V} {x : Letter} {w : V}, w ∈ G.edges v x →
    CosetEquivalent H (potential w) (potential v * letterEval x)

/-- Along any path, a coset potential changes by the value of the path label. -/
theorem InverseMultigraph.walk_cosetPotential {V : Type*}
    (G : InverseMultigraph V) (H : Subgroup Free)
    (potential : V → Free) (hpotential : HasCosetPotential G H potential) :
    ∀ {v z : V} {w : Word}, G.Walk v w z →
      CosetEquivalent H (potential z) (potential v * wordEval w) := by
  intro v z w hwalk
  induction hwalk with
  | nil v =>
      simpa [wordEval_nil] using CosetEquivalent.refl H (potential v)
  | @cons v u z x w edge tail ih =>
      have hedge : CosetEquivalent H (potential u) (potential v * letterEval x) :=
        hpotential edge
      simpa [wordEval_cons, mul_assoc] using
        CosetEquivalent.trans ih (CosetEquivalent.right_mul hedge (wordEval w))

private noncomputable def cosetBool (H : Subgroup Free) (g h : Free) : Bool :=
  by
    classical
    exact decide (CosetEquivalent H g h)

private theorem cosetBool_eq_true (H : Subgroup Free) (g h : Free) :
    cosetBool H g h = true ↔ CosetEquivalent H g h := by
  classical
  exact decide_eq_true_iff

/-- A fold never identifies vertices with different subgroup cosets, whenever
the input graph has a compatible coset potential. -/
theorem foldRel_cosetPotential {V : Type*}
    (G : InverseMultigraph V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v w : V}
    (hvw : foldRel G v w) : CosetEquivalent H (potential v) (potential w) := by
  classical
  let r : V → V → Bool := fun a b => cosetBool H (potential a) (potential b)
  have hr : IsFoldCongruence G r := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a
      exact (cosetBool_eq_true H _ _).2 (CosetEquivalent.refl H (potential a))
    · intro a b hab
      apply (cosetBool_eq_true H _ _).2
      exact CosetEquivalent.symm ((cosetBool_eq_true H _ _).1 hab)
    · intro a b c hab hbc
      apply (cosetBool_eq_true H _ _).2
      exact CosetEquivalent.trans ((cosetBool_eq_true H _ _).1 hab)
        ((cosetBool_eq_true H _ _).1 hbc)
    · intro a b x u t hab hedgeU hedgeT
      apply (cosetBool_eq_true H _ _).2
      have hab' : CosetEquivalent H (potential a) (potential b) :=
        (cosetBool_eq_true H _ _).1 hab
      have hu : CosetEquivalent H (potential u) (potential a * letterEval x) :=
        hpotential hedgeU
      have ht : CosetEquivalent H (potential t) (potential b * letterEval x) :=
        hpotential hedgeT
      exact CosetEquivalent.trans hu <| CosetEquivalent.trans
        (CosetEquivalent.right_mul hab' (letterEval x)) (CosetEquivalent.symm ht)
  exact (cosetBool_eq_true H _ _).1 (hvw r hr)

/-- Each transition made by the folded automaton respects the subgroup
potential. -/
theorem foldedNext_cosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V)
    (base : V) (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) {v t : V} {x : Letter}
    (hnext : (foldAutomaton G base).next v x = some t) :
    CosetEquivalent H (potential t) (potential v * letterEval x) := by
  change foldedNext G v x = some t at hnext
  have hv : v = foldRep G v := by
    unfold foldedNext at hnext
    split at hnext
    · assumption
    · simp at hnext
  have hcore : foldedNextCore G v x = some t := by
    change (if v = foldRep G v then foldedNextCore G v x else none) = some t at hnext
    rw [ite_eq_left hv] at hnext
    exact hnext
  by_cases hne : (foldTargets G v x).Nonempty
  · unfold foldedNextCore at hcore
    rw [dite_eq_left hne] at hcore
    have ht : foldRep G ((foldTargets G v x).min' hne) = t := by
      injection hcore
    subst t
    let q := (foldTargets G v x).min' hne
    have hq : q ∈ foldTargets G v x := Finset.min'_mem _ _
    rcases Finset.mem_filter.mp hq with ⟨_, u, huv, hedge⟩
    have hqPot : CosetEquivalent H (potential (foldRep G q)) (potential q) :=
      foldRel_cosetPotential G H potential hpotential (foldRep_rel G q)
    have hedgePot : CosetEquivalent H (potential q) (potential u * letterEval x) :=
      hpotential hedge
    have huvPot : CosetEquivalent H (potential u) (potential v) :=
      foldRel_cosetPotential G H potential hpotential huv
    exact CosetEquivalent.trans hqPot <| CosetEquivalent.trans hedgePot
      (CosetEquivalent.right_mul huvPot (letterEval x))
  · unfold foldedNextCore at hcore
    rw [dite_eq_right hne] at hcore
    simp at hcore

/-- A successful folded traversal transports the potential by the value of its
label word. -/
theorem run_cosetPotential {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V) (base : V)
    (H : Subgroup Free) (potential : V → Free)
    (hpotential : HasCosetPotential G H potential) :
    ∀ {v t : V} {w : Word},
      (foldAutomaton G base).run v w = some t →
      CosetEquivalent H (potential t) (potential v * wordEval w) := by
  intro v t w hrun
  induction w generalizing v t with
  | nil =>
      simp only [InverseAutomaton.run, Option.some.injEq] at hrun
      subst t
      simp [CosetEquivalent]
  | cons x w ih =>
      simp only [InverseAutomaton.run] at hrun
      cases hnext : (foldAutomaton G base).next v x with
      | none => simp [hnext] at hrun
      | some u =>
          have htail : (foldAutomaton G base).run u w = some t := by
            simpa [hnext] using hrun
          have hstep := foldedNext_cosetPotential G base H potential hpotential hnext
          have htailPotential := ih htail
          have hcombined := CosetEquivalent.trans htailPotential
            (CosetEquivalent.right_mul hstep (wordEval w))
          simpa [wordEval_cons, mul_assoc] using hcombined

/-- Folding preserves the subgroup generated by based loop labels, provided
the original graph carries the canonical coset potential. -/
theorem foldAutomaton_loopSubgroup_eq {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : InverseMultigraph V)
    (base : V) (potential : V → Free)
    (hpotential : HasCosetPotential G (G.loopSubgroup base) potential)
    (hbase : potential base = 1) :
    (foldAutomaton G base).loopSubgroup = G.loopSubgroup base := by
  apply le_antisymm
  · intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    have hrun : (foldAutomaton G base).run (foldRep G base) w = some (foldRep G base) :=
      (InverseAutomaton.run_eq_some_iff_walk (foldAutomaton G base)).2 hwalk
    have hword := run_cosetPotential G base (G.loopSubgroup base) potential hpotential hrun
    have hrepBase : potential (foldRep G base) ∈ G.loopSubgroup base := by
      have hcoset : CosetEquivalent (G.loopSubgroup base) (potential (foldRep G base)) 1 := by
        simpa [hbase] using foldRel_cosetPotential G (G.loopSubgroup base) potential hpotential
          (foldRep_rel G base)
      simpa [CosetEquivalent] using hcoset
    have hprod : potential (foldRep G base) * wordEval w ∈ G.loopSubgroup base :=
      CosetEquivalent.mem_of_mem_and_rel hword hrepBase
    have hwordMem : wordEval w ∈ G.loopSubgroup base := by
      have := (G.loopSubgroup base).mul_mem ((G.loopSubgroup base).inv_mem hrepBase) hprod
      simpa [mul_assoc] using this
    rw [← hw]
    exact hwordMem
  · change Subgroup.closure
      {g : Free | ∃ w : Word, wordEval w = g ∧ G.Walk base w base} ≤
      (foldAutomaton G base).loopSubgroup
    apply (Subgroup.closure_le ((foldAutomaton G base).loopSubgroup)).2
    intro g hg
    rcases hg with ⟨w, hw, hwalk⟩
    refine ⟨w, hw, ?_⟩
    have hfold := foldWalk G base base base hwalk
    exact (InverseAutomaton.run_eq_some_iff_walk (foldAutomaton G base)).mp hfold

end Stallings
