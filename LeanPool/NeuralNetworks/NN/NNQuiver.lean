/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.Quiver.Path.Weight
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

open Finset

universe uR uU uσ

/--
Quiver–based neural network (refactored from Digraph version).

NOTE:
We separate the declarations of `κ1` and `κ2` (do NOT write `κ1 κ2 : U → ℕ`)
to avoid Lean mis‑inferring a curried arity (`U → U → ℕ`) inside subsequent
dependent fields..
-/
structure NeuralNetwork (R : Type uR) (U : Type uU) (σ : Type uσ)
    [Zero R] [Quiver U] where
  /-- Adjacency: at least one arrow from `u` to `v`. -/
  Adj : U → U → Prop := fun u v => Nonempty (u ⟶ v)
  /-- The set of input neurons. -/
  Ui : Set U
  /-- The set of output neurons. -/
  Uo : Set U
  /-- The set of hidden neurons. -/
  Uh : Set U
  /-- The input set is nonempty. -/
  hUi : Ui.Nonempty
  /-- The output set is nonempty. -/
  hUo : Uo.Nonempty
  /-- The three neuron sets cover the whole vertex type. -/
  hU : Set.univ = Ui ∪ Uo ∪ Uh
  /-- Hidden neurons are disjoint from input and output neurons. -/
  hhio : Uh ∩ (Ui ∪ Uo) = ∅
  /-- Input fan-in parameter dimension. -/
  κ1 : U → ℕ
  /-- Activation parameter dimension. -/
  κ2 : U → ℕ
  /-- Net input function:
      u, row of weights for u, current numeric outputs, exogenous σ-vector → scalar net. -/
  fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R
  /-- Activation update (stateful): neuron u, current σ_u, net input (R),
      parameter vector (θ) → next σ_u. -/
  fact : ∀ u : U, σ → R → Vector R (κ2 u) → σ
  /-- Numeric readout from σ (can depend on neuron). -/
  fout : ∀ _ : U, σ → R
  /-- Auxiliary numeric map on σ (often equal to fout u). -/
  m : σ → R
  /-- Admissible activations predicate. -/
  pact : σ → Prop
  /-- Admissible weight matrices predicate. -/
  pw : Matrix U U R → Prop
  /-- Closure of pact under one (synchronous) layer of `fact` updates given
      masked weights & structural predicates. -/
  hpact :
    ∀ (w : Matrix U U R)
      (_hwMask : ∀ u v, ¬ Adj u v → w u v = 0)
      (_hw' : pw w)
      (σv : (u : U) → Vector R (κ1 u))
      (θ  : (u : U) → Vector R (κ2 u))
      (current : U → σ),
        (∀ u, pact (current u)) →
        ∀ u, pact (fact u (current u)
                       (fnet u (w u) (fun v => fout v (current v)) (σv u))
                       (θ u))

namespace NeuralNetwork

variable {R : Type uR} {U : Type uU} {σ : Type uσ} [Zero R] [Quiver U]

/-- If this network's adjacency is the default (`Nonempty (u ⟶ v)`), unfold it. -/
@[simp] lemma Adj_iff_default (NN : NeuralNetwork R U σ)
    (h : NN.Adj = fun u v => Nonempty (u ⟶ v)) {u v : U} :
    NN.Adj u v ↔ Nonempty (u ⟶ v) := by
  simp [h]

/-- Parameter bundle (weights + per-neuron parameter vectors). -/
structure Params (NN : NeuralNetwork R U σ) where
  /-- The weight matrix of the network. -/
  w : Matrix U U R
  /-- Weights vanish on non-adjacent pairs of neurons. -/
  hw : ∀ u v, ¬ NN.Adj u v → w u v = 0
  /-- The weights satisfy the network's structural predicate `pw`. -/
  hw' : NN.pw w
  /-- Per-neuron net-input parameter vectors. -/
  σ : ∀ u : U, Vector R (NN.κ1 u)
  /-- Per-neuron activation parameter vectors. -/
  θ : ∀ u : U, Vector R (NN.κ2 u)

/-- Network state with invariance certificate. -/
structure State (NN : NeuralNetwork R U σ) where
  /-- The activation value carried by each neuron. -/
  act : U → σ
  /-- Each activation satisfies the network's activation predicate `pact`. -/
  hp : ∀ u, NN.pact (act u)

namespace State

@[ext] lemma ext {NN : NeuralNetwork R U σ} {s₁ s₂ : NN.State}
    (h : ∀ u, s₁.act u = s₂.act u) : s₁ = s₂ := by
  cases s₁ with
  | mk act₁ hp₁ =>
    cases s₂ with
    | mk act₂ hp₂ =>
      have : act₁ = act₂ := funext h
      simp [this]

end State

namespace State

variable {NN : NeuralNetwork R U σ}
variable {p : Params NN} {s : NN.State}

/-- Numeric output of neuron `u` in the current state. -/
def out (u : U) : R := NN.fout u (s.act u)

/-- Net input arriving at neuron `u` in the current state. -/
def net (u : U) : R :=
  NN.fnet u (p.w u) (fun v => NN.fout v (s.act v)) (p.σ u)

/-- The state is determined outside the input set: all non-input neurons share a
common activation value. -/
def onlyUi : Prop := ∃ σ0 : σ, ∀ u : U, u ∉ NN.Ui → s.act u = σ0

variable [DecidableEq U]

/-- Single-site asynchronous update. -/
def Up (s : NN.State) (p : Params NN) (u : U) : NN.State :=
{ act := fun v =>
    if hv : v = u then
      NN.fact u (s.act u)
        (NN.fnet u (p.w u) (fun n => NN.fout n (s.act n)) (p.σ u))
        (p.θ u)
    else
      s.act v
, hp := by
    intro v
    by_cases hv : v = u
    · subst hv
      have clos := NN.hpact p.w p.hw p.hw' p.σ p.θ s.act s.hp
      simpa using clos v
    · simpa [hv] using s.hp v }

/-- Batch a finite list of update sites (left fold). -/
def workPhase (ext : NN.State) (uOrder : List U) (p : Params NN) : NN.State :=
  uOrder.foldl (fun st u => Up st p u) ext

/-- Iterated asynchronous single-site trajectory along a schedule. -/
def seqStates (s : NN.State) (p : Params NN) (useq : ℕ → U) : ℕ → NN.State
  | 0     => s
  | n + 1 => Up (seqStates s p useq n) p (useq n)

/-- Asynchronous fixed point. -/
def isStable (s : NN.State) (p : Params NN) : Prop := ∀ u, (Up s p u).act u = s.act u

/-- Synchronous (parallel) update. -/
def UpSync (s : NN.State) (p : Params NN) : NN.State :=
{ act := fun u =>
    NN.fact u (s.act u)
      (NN.fnet u (p.w u) (fun n => NN.fout n (s.act n)) (p.σ u))
      (p.θ u)
, hp := by
    intro u
    exact NN.hpact p.w p.hw p.hw' p.σ p.θ s.act s.hp u }

/-- Iterated synchronous trajectory. -/
def seqStatesSync (p : Params NN) (s : NN.State) : ℕ → NN.State
  | 0     => s
  | n + 1 => UpSync (seqStatesSync p s n) p

/-- Synchronous fixed point. -/
def isStableSync (p : Params NN) (s : NN.State) : Prop := UpSync s p = s

end State

/-! ### Quiver–level structural predicates (feed‑forward scaffolding)

These lightweight abstractions illustrate how to start exploiting the `Quiver`
API for architectural constraints (e.g. DAG / layered networks). They are kept
orthogonal to the main dynamics so they can be adopted incrementally. -/

/-- A quiver (on the vertex set of a neural network) is acyclic if every loop path is trivial. -/
class Acyclic (U : Type uU) [Quiver U] : Prop where
  no_nontrivial_cycle :
    ∀ (u : U) {p : Quiver.Path u u}, p.length = 0

/-- A layering function `ℓ` certifies feed‑forward structure if every edge goes from
lower to strictly higher layer index. -/
structure Layering (U : Type uU) [Quiver U] where
  /-- The layer index assigned to each vertex. -/
  ℓ : U → ℕ
  /-- Each edge strictly increases the layer index. -/
  mono : ∀ {a b}, (a ⟶ b) → ℓ a < ℓ b

namespace Layering
--variable {U}

/-- Along any non-empty path, the layer strictly increases. -/
private lemma strict_of_length_pos (L : Layering U)
  {a b : U} (p : Quiver.Path a b) (hpos : 0 < p.length) :
  L.ℓ a < L.ℓ b := by
  induction p with
  | nil =>
      cases hpos
  | @cons b' c p e ih =>
      by_cases hzero : p.length = 0
      · -- Prefix has length zero, so `p` is trivial and the inequality comes from the last edge.
        have h_ab : a = b' := Quiver.Path.eq_of_length_zero p hzero
        subst h_ab
        simpa using L.mono e
      · -- Nontrivial prefix: chain inequalities.
        have hpos' : 0 < p.length := Nat.pos_of_ne_zero hzero
        have h_ab : L.ℓ a < L.ℓ b' := ih hpos'
        have h_bc : L.ℓ b' < L.ℓ c := L.mono e
        exact lt_trans h_ab h_bc

/-- A layering immediately yields acyclicity: any loop path must be trivial. -/
lemma toAcyclic (L : Layering U) : Acyclic U := by
  refine ⟨?_⟩
  intro u p
  by_contra hne
  have hpos : 0 < p.length := Nat.pos_of_ne_zero hne
  have : L.ℓ u < L.ℓ u := strict_of_length_pos L p hpos
  exact lt_irrefl _ this
/-- Relation induced by a layering: strictly increasing layer index. -/
def rel (L : Layering U) : U → U → Prop := fun a b => L.ℓ a < L.ℓ b

/-- Well-founded order by increasing layer index (suitable for recursion). -/
lemma wfMeasure (L : Layering U) : WellFounded (fun a b => L.ℓ a < L.ℓ b) :=
  -- Use the inverse image of the well-founded `<` on Nat under `L.ℓ`.
  (InvImage.wf (fun x => L.ℓ x) Nat.lt_wfRel.wf)

end Layering


end NeuralNetwork

/-
Extended quiver-based abstractions: weights on arrows, topological evaluation, residuals.
Placed in a separate namespace to avoid disturbing existing API.
-/
namespace NeuralNetwork.QuiverExt

open Quiver

universe u v w

variable {U : Type u} [Quiver U]

/-- Edge-weighted quiver (multiplicative / additive semantics delegated to `R`). -/
class WeightedQuiver (U : Type u) [Quiver U] (R : Type v) where
  /-- The weight assigned to each arrow. -/
  weight : ∀ {a b : U}, (a ⟶ b) → R

export WeightedQuiver (weight)

/-- Optional residual marking on arrows (e.g. identity / skip connections). -/
class HasResidual (U : Type u) [Quiver U] where
  /-- Predicate marking an arrow as a residual (skip) connection. -/
  isResidual : ∀ {a b : U}, (a ⟶ b) → Prop

export HasResidual (isResidual)

/-- Arrow-level parameter bundle (per-edge + per-vertex). -/
structure ArrowParams (U : Type u) [Quiver U] (R : Type v) where
  /-- The weight assigned to each arrow. -/
  w : ∀ {a b : U}, (a ⟶ b) → R
  /-- A simple per-vertex scalar bias. -/
  θ : U → R

attribute [simp] ArrowParams.w

/-- (Refined) feed‑forward evaluation over a layered DAG quiver.

Requirements:
* Layering `L` (gives well‑founded measure).
* Finite vertex set & finite hom types (for summations).
* `inputs` supplies external input activation for each vertex (used additively at every vertex;
  you can specialize to only input layer by zeroing elsewhere).

Recurrence:
  out a = φ ( inputs a + (∑_{p,e : p ⟶ a} P.w e * out p ) + P.θ a )

The recursion is justified since every edge `p ⟶ a` satisfies `ℓ p < ℓ a`. -/
noncomputable
def forwardEval
    {R : Type v} [Semiring R]
    [Fintype U]
    [∀ a b : U, Fintype (a ⟶ b)]
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R)
    (φ : R → R)
    (inputs : U → R) : U → R :=
  WellFounded.fix L.wfMeasure
    (fun a rec =>
      -- accumulate over all predecessors p with every arrow e : p ⟶ a
      let incoming :=
        ∑ p : U, ∑ e : (p ⟶ a), (P.w e) * rec p (by exact L.mono e)
      φ (inputs a + incoming + P.θ a))

/-- Multiplicative weight of a path using `WeightedQuiver`. -/
def pathWeight
    {R : Type v} [Monoid R] [WeightedQuiver U R]
    {a b : U} (p : Quiver.Path a b) : R :=
  Quiver.Path.weight (fun e => weight e) p

/-- Residual-aware combination example (noncomputable due to classical choice on the Prop). -/
noncomputable
def combineResidual
    {R : Type v} [Semiring R] [WeightedQuiver U R] [HasResidual U]
    {a b : U} (e : a ⟶ b) (x : R) : R :=
  by
    classical
    exact if h : isResidual e then x + weight e else weight e * x

/-- Alternate residual combinator with an explicit decision hypothesis (computable form). -/
def combineResidualDec
    {R : Type v} [Semiring R] [WeightedQuiver U R] [HasResidual U]
    {a b : U} (e : a ⟶ b) (x : R)
    (h : Decidable (isResidual e)) : R :=
  match h with
  | isTrue _  => x + weight e
  | isFalse _ => weight e * x

/-- Expand a layer’s output by one synchronous step from an already evaluated
    prefix of lower layers. Useful for staged constructions without full recursion. -/
noncomputable
def extendEval
    {R : Type v} [Semiring R]
    [Fintype U] [∀ a b : U, Fintype (a ⟶ b)]
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R) (φ : R → R)
    (inputs : U → R)
    (a : U) : R :=
  -- For simplicity here we still recompute via `forwardEval`; in practice one may refine.
  forwardEval (L := L) P φ inputs a

/-- Sum of weights over all paths of fixed length `n` from `a` to `b`.
    (Illustrative; exponential blowup — suitable only for small finite quivers.) -/
noncomputable
def totalPathWeightLen
    {R : Type v} [Semiring R] [WeightedQuiver U R]
    [Fintype U] [DecidableEq U] [∀ a b : U, Fintype (a ⟶ b)]
    (a b : U) : ℕ → R
  | 0 =>
      -- Length‑0 path contributes 1 iff a = b, else 0.
      if a = b then 1 else 0
  | n+1 =>
      -- Sum over all one‑step predecessors c of b and all edges c ⟶ b.
      ∑ c : U, ∑ e : (c ⟶ b), totalPathWeightLen a c n * weight e

/-- All-length total path weight (formal power series style, truncated at `N`). -/
noncomputable
def totalPathWeightUpTo
    {R : Type v} [Semiring R] [WeightedQuiver U R]
    [Fintype U] [DecidableEq U] [∀ a b : U, Fintype (a ⟶ b)]
    (N : ℕ) (a b : U) : R :=
  ∑ n : Fin (N+1), totalPathWeightLen (U := U) (R := R) a b n.val

end NeuralNetwork.QuiverExt

namespace NeuralNetwork

variable {R : Type uR} {U : Type uU} {σ : Type uσ}
variable [Zero R] [Quiver U]

/-- Predicate: every target has *at most* one incoming arrow (structural tree in-degree ≤ 1). -/
def indegreeAtMostOne : Prop :=
  ∀ ⦃a b c : U⦄ (e₁ : a ⟶ c) (e₂ : b ⟶ c), a = b ∧ HEq e₁ e₂

/-- Predicate: every non-root vertex has *some* incoming arrow (except chosen root `r`). -/
def hasIncomingExcept (r : U) : Prop :=
  ∀ b, b = r ∨ ∃ a, Nonempty (a ⟶ b)

namespace Layering

/-- From a layering + (tree-like in-degree) + coverage you obtain an `Arborescence`.
    (Uses `ℓ` as the height function.) -/
@[reducible]
noncomputable
def toArborescence
    (L : Layering U) (r : U)
    (hInUni : indegreeAtMostOne (U := U))
    (hCover : hasIncomingExcept (U := U) r) :
    Quiver.Arborescence U :=
  Quiver.arborescenceMk (V := U) r (L.ℓ)
    (by intro a b e; exact L.mono e)
    (by
      intro a b c e₁ e₂
      rcases hInUni e₁ e₂ with ⟨h, hheq⟩
      subst h
      cases hheq
      exact ⟨rfl, by constructor⟩)
    (by intro b; simpa [hasIncomingExcept] using hCover b)

end Layering

/-- Convenience lemma: any path loop under a layering must be trivial
    (acyclicity follows from strictly increasing layer indices). -/
lemma no_cycle_of_layering
    (L : Layering U)
    {u : U} (p : Quiver.Path u u) :
    p.length = 0 := by
  have := L.toAcyclic.no_nontrivial_cycle u (p := p)
  exact this

end NeuralNetwork

namespace NeuralNetwork.QuiverExt
open NeuralNetwork

universe u v
variable {U : Type u} [Quiver U]

/-- Path-product (gradient skeleton) for an arborescent quiver:
    unique path weight from the canonical root to `b`. -/
noncomputable def rootToWeight
    {R : Type v} [Monoid R] [WeightedQuiver U R] [Quiver.Arborescence U]
    (b : U) : R :=
  pathWeight (U := U) (R := R) (default : Quiver.Path (Quiver.root U) b)

/-- In an arborescence any two linear evaluations satisfying the same edge relations
    and agreeing at the root are equal. -/
lemma arborescent_linear_eval_unique
    {R : Type v} [Semiring R] [WeightedQuiver U R] [Quiver.Arborescence U]
    (f g : ∀ _ : U, R) (hroot : f (Quiver.root U) = g (Quiver.root U))
    (hStep :
      ∀ {a b} (e : a ⟶ b), f b = weight e * f a ∧ g b = weight e * g a) :
    f = g := by
  classical
  funext b
  -- Auxiliary: propagate equality along the (unique) root-to-b path via induction on the path.
  have aux :
      ∀ {b} (p : Quiver.Path (Quiver.root U) b),
        f (Quiver.root U) = g (Quiver.root U) → f b = g b := by
    intro b p
    induction p with
    | nil =>
        intro h; simpa using h
    | cons p e ih =>
        intro h
        have ih' := ih h
        obtain ⟨hf, hg⟩ := hStep e
        -- Use the edge relations plus the inductive equality.
        calc
          f _ = weight e * f _ := hf
          _   = weight e * g _ := by simp [ih']
          _   = g _ := (hg).symm
  simpa using aux (default : Quiver.Path (Quiver.root U) b) hroot

end NeuralNetwork.QuiverExt

namespace NeuralNetwork.QuiverExt
open Quiver
open scoped BigOperators

universe u v
variable {U : Type u} [Quiver U]

/-! # Gradient Path Product (Arborescent Case) -/
section GradientPathProduct

variable {R : Type v} [Monoid R] [WeightedQuiver U R] [Quiver.Arborescence U]

/-- Fold of (φ'(target) * weight edge) along a path. Mirrors `Quiver.Path.weight` style. -/
def gradFold (φ' : U → R) : ∀ {r b : U}, Quiver.Path r b → R
  | _, _, Quiver.Path.nil        => 1
  | _, b, Quiver.Path.cons p e   => gradFold φ' p * (φ' b * weight e)

omit [Arborescence U] in
@[simp] lemma gradFold_nil (φ' : U → R) {r : U} :
  gradFold (U := U) (R := R) φ' (Quiver.Path.nil : Quiver.Path r r) = 1 := by
  simp [gradFold]

omit [Arborescence U] in
@[simp] lemma gradFold_cons (φ' : U → R) {r a b : U}
    (p : Quiver.Path r a) (e : a ⟶ b) :
    gradFold (U := U) (R := R) φ' (p.cons e) =
      gradFold (U := U) (R := R) φ' p * (φ' b * weight e) := by
  simp [gradFold]

/-- Sensitivity (symbolic ∂ out / ∂ out_root) at vertex `b`
as product of φ' and edge weights along the unique root→b path. -/
noncomputable
def rootSensitivity (φ' : U → R) (b : U) : R :=
  gradFold (U := U) (R := R) φ' (default : Quiver.Path (Quiver.root U) b)

/-- Definitional unfolding of `rootSensitivity`. -/
@[simp] lemma gradient_path_product (φ' : U → R) (b : U) :
    rootSensitivity (U := U) (R := R) φ' b =
      gradFold (U := U) (R := R) φ' (default : Quiver.Path (Quiver.root U) b) := rfl

omit [Arborescence U] in
/-- Helper: when φ' ≡ 1, `gradFold` reduces to multiplicative path weight. -/
lemma gradFold_one :
  ∀ {r b : U} (p : Quiver.Path r b),
    gradFold (U := U) (R := R) (fun _ => (1 : R)) p
      = Quiver.Path.weight (fun e => weight e) p
  | _, _, Quiver.Path.nil => by simp [Quiver.Path.weight_nil]
  | _, _, Quiver.Path.cons p e =>
      by
        simp [gradFold_one (p := p),
              Quiver.Path.weight_cons,
              one_mul]

/-- If φ' is constantly 1, sensitivity collapses to plain path weight. -/
lemma rootSensitivity_const_one (b : U) :
    rootSensitivity (U := U) (R := R) (fun _ => (1 : R)) b =
      rootToWeight (U := U) (R := R) b := by
  -- rootToWeight = pathWeight of the unique (default) path
  simp [rootSensitivity, rootToWeight, pathWeight, gradFold_one]

end GradientPathProduct

end NeuralNetwork.QuiverExt

/-! # Pruning Correctness (Arborescent Case)

In an arborescent quiver each vertex has at most one incoming arrow; removing
any *non-existent* "extra" edges does nothing. We model pruning by an identity
re-weighting to show the shape of a future refinement where masking matters.
-/

namespace NeuralNetwork.QuiverExt

open Quiver
open scoped BigOperators

universe u v
variable {U : Type u} [Quiver U]
variable {R : Type v} [Semiring R]
variable [Fintype U] [DecidableEq U] [∀ a b : U, Fintype (a ⟶ b)]
variable [WeightedQuiver U R] [Quiver.Arborescence U]

/-- Identity pruning mask: keeps all existing (unique) incoming edges.
(Placeholder for a future mask selecting e.g. geodesic edges in a non-tree DAG.)
Uses classical choice to decide `keep e`. -/
noncomputable
def prunedWeights
    (keep : ∀ {a b : U}, (a ⟶ b) → Prop)
    (w : ∀ {a b : U}, (a ⟶ b) → R)
    {a b : U} (e : a ⟶ b) : R :=
  by
    classical
    exact if h : keep e then w e else 0

omit [DecidableEq U] [WeightedQuiver U R] [Arborescence U] in
/-- Under arborescence (unique parent), any mask that keeps every existing edge
trivializes the forward evaluation (pruning correctness). -/
lemma forwardEval_prune_id
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R)
    (φ : R → R)
    (inputs : U → R)
    (keep : ∀ {a b : U} (_ : a ⟶ b), Prop)
    (hkeep : ∀ {a b : U} (e : a ⟶ b), keep e) :
    forwardEval L
      ({ w := (fun {_ _ : U} e => prunedWeights (keep := keep) (w := P.w) e)
         θ := P.θ } : ArrowParams U R)
      φ inputs
    =
    forwardEval L P φ inputs := by
  have hw :
    (fun {a b : U} (e : a ⟶ b) => prunedWeights (keep := keep) (w := P.w) e)
      =
    (fun {a b : U} (e : a ⟶ b) => P.w e) := by
      funext a b e; simp [prunedWeights, hkeep]
  cases P with
  | mk w θ =>
      simp [forwardEval, prunedWeights, hkeep]

end NeuralNetwork.QuiverExt

variable {U : Type uU} {R : Type uR}

/-- Shapes (currently illustrative; not required for `Expr` evaluation). -/
inductive Shape
  | scalar
  | vec  (n : ℕ)
  | mat  (m n : ℕ)
deriving DecidableEq

/-- Semantic (host language) type denotation for a `Shape`. -/
def DenoteShape (R : Type uR) : Shape → Type _
  | .scalar     => R
  | .vec n      => Fin n → R
  | .mat m n    => Fin m → Fin n → R

/-- Core expression language for neuron update formulas. -/
inductive Expr (U : Type uU) (R : Type uR) : Type (max uU uR)
  | var        : U → Expr U R
  | const      : R → Expr U R
  | add        : Expr U R → Expr U R → Expr U R
  | mul        : Expr U R → Expr U R → Expr U R
  | weight     : U → U → Expr U R              -- symbolic reference to weight W (i,j)
  | activation : (R → R) → Expr U R → Expr U R -- unary nonlinearity
deriving Inhabited

namespace Expr

end Expr

/-- Environment: current numerical values (e.g. neuron outputs). -/
def Env (U : Type uU) (R : Type uR) := U → R

/-- Interpreter from syntax to semantics. -/
def eval [Add R] [Mul R] (weights : U → U → R) (env : Env U R) :
    Expr U R → R
  | .var i            => env i
  | .const c          => c
  | .add e₁ e₂        => eval weights env e₁ + eval weights env e₂
  | .mul e₁ e₂        => eval weights env e₁ * eval weights env e₂
  | .weight i j       => weights i j
  | .activation φ e   => φ (eval weights env e)

/-- Mathematical specification (kept identical for now; useful if `eval` later optimized). -/
def denote [Add R] [Mul R] (w : U → U → R) (env : Env U R) :
    Expr U R → R
  | .var i            => env i
  | .const c          => c
  | .add e₁ e₂        => denote w env e₁ + denote w env e₂
  | .mul e₁ e₂        => denote w env e₁ * denote w env e₂
  | .weight i j       => w i j
  | .activation φ e   => φ (denote w env e)

/-- Correctness (interpreter matches spec). -/
lemma eval_eq_denote [Add R] [Mul R]
    (w : U → U → R) (env : Env U R) (e : Expr U R) :
    eval (U := U) (R := R) w env e = denote w env e := by
  induction e with
  | var _        => simp [eval, denote]
  | const _      => simp [eval, denote]
  | add _ _ ih₁ ih₂ => simp [eval, denote, ih₁, ih₂]
  | mul _ _ ih₁ ih₂ => simp [eval, denote, ih₁, ih₂]
  | weight _ _   => simp [eval, denote]
  | activation _ _ ih => simp [eval, denote, ih]

/-- A “dense layer” style expression: relu ( W * x + b ).
We model:
* W : weight references resolved externally (so here we accept already‑built expressions)
* x, b : vector expressions (encoded elementwise via sums of weighted vars in simple demos).
For this minimal core we just treat them as scalar expressions and rely on downstream
vector extension if needed. -/
def dense (relu : R → R) (W x b : Expr U R) : Expr U R :=
  .activation relu (.add (.mul W x) b)

/-! ### Concrete Example Instantiation (finite index set) -/

namespace Examples

open Expr

/-- Example index set. -/
inductive ExampleU
  | u₁ | u₂ | u₃ | bias
deriving DecidableEq, Inhabited

open ExampleU

instance : Fintype ExampleU :=
  { elems := {u₁, u₂, u₃, bias}
    , complete := by intro x; cases x <;> simp }

/-- Sample weights (sparse). -/
noncomputable def exampleWeights : ExampleU → ExampleU → ℝ
  | u₃, u₁   => (1 : ℝ) / 2
  | u₃, u₂   => -1
  | u₃, bias => 1
  | _,   _   => 0

/-- Sample environment (current activations). -/
def exampleEnv : Env ExampleU ℝ
  | u₁   => 1
  | u₂   => 2
  | bias => 1
  | u₃   => 0

/-- Net input expression: w₃₁ * out₁ + w₃₂ * out₂. -/
def netInputExpr : Expr ExampleU ℝ :=
  .add (.mul (.weight u₃ u₁) (.var u₁))
       (.mul (.weight u₃ u₂) (.var u₂))

/-- ReLU wrapper. -/
def reluExpr (e : Expr ExampleU ℝ) : Expr ExampleU ℝ :=
  .activation (fun x => max 0 x) e

/-- Full neuron update: ReLU( net + bias ). -/
def neuronUpdateExpr : Expr ExampleU ℝ :=
  reluExpr (.add netInputExpr (.weight u₃ bias))

@[simp] lemma eval_var (i : ExampleU) :
  eval exampleWeights exampleEnv (.var i) = exampleEnv i := rfl

@[simp] lemma eval_weight (i j : ExampleU) :
  eval exampleWeights exampleEnv (.weight i j) = exampleWeights i j := rfl

@[simp] lemma eval_const (c : ℝ) :
  eval exampleWeights exampleEnv (.const c) = c := rfl

/-- Closed form of the net input. -/
lemma eval_netInput :
  eval exampleWeights exampleEnv netInputExpr
    =
  exampleWeights u₃ u₁ * exampleEnv u₁
    + exampleWeights u₃ u₂ * exampleEnv u₂ := by
  simp [netInputExpr, eval, exampleWeights, exampleEnv, mul_comm]

/-- Numeric value of the net input: (1/2)*1 + (-1)*2 = -3/2. -/
lemma eval_netInput_value :
  eval exampleWeights exampleEnv netInputExpr = - (3 : ℝ) / 2 := by
  have h := eval_netInput
  simp [eval_netInput, exampleWeights, exampleEnv,
        mul_comm, one_div] at *
  norm_num

/-- Evaluate full update (ReLU(net + bias)) = 0 since net + 1 = -1/2. -/
lemma eval_neuronUpdate_value :
  eval exampleWeights exampleEnv neuronUpdateExpr = 0 := by
  have hle : 1 + ((2 : ℝ)⁻¹ + -2) ≤ 0 := by norm_num
  simp [neuronUpdateExpr, reluExpr, netInputExpr, eval,
         exampleWeights, exampleEnv,
         add_comm, mul_comm, max_eq_left hle]

/-- Symbolic correctness (net input). -/
lemma eval_netInput_correct :
  eval exampleWeights exampleEnv netInputExpr
    =
  exampleWeights u₃ u₁ * exampleEnv u₁
    + exampleWeights u₃ u₂ * exampleEnv u₂ :=
  eval_netInput

/-- Symbolic correctness (activated). -/
lemma eval_neuronUpdate_correct :
  eval exampleWeights exampleEnv neuronUpdateExpr
    =
  let net :=
    exampleWeights u₃ u₁ * exampleEnv u₁
      + exampleWeights u₃ u₂ * exampleEnv u₂
  let bias := exampleWeights u₃ bias
  max 0 (net + bias) := by
  simp [neuronUpdateExpr, reluExpr, netInputExpr, eval,
        exampleWeights, exampleEnv,
        add_comm,
        mul_comm]

end Examples

/-!
# Refactor TODO

Goal: Separate (1) pure architecture (graph + interface sets) from
(2) dynamics (update rules / parameter typing) and (3) semantic layers
(e.g. deterministic vs probabilistic vs compiled).

This scaffold is non‑intrusive: current code continues to work.
Later files can supply concrete instances.
-/

namespace NeuralArch

--universe uU uR uσ

variable {U : Type uU}

/-- Pure architectural shape: graph + (optional) interface partition. -/
structure Architecture (U : Type uU) [Quiver U] where
  /-- The set of input neurons. -/
  Ui : Set U
  /-- The set of output neurons. -/
  Uo : Set U
  /-- The set of hidden neurons. -/
  Uh : Set U
  /-- Coverage (may later relax to `Ui ∪ Uh ⊆ carriers`, etc.). -/
  cover : Set.univ = Ui ∪ Uo ∪ Uh
  /-- Hidden disjoint from inputs/outputs. -/
  hid_disj : Uh ∩ (Ui ∪ Uo) = ∅

/-- Structural property: acyclic under some layering. -/
structure HasLayering (U : Type uU) [Quiver U] where
  /-- A layering witnessing acyclicity of the architecture. -/
  L : NeuralNetwork.Layering U

end NeuralArch

namespace NeuralDyn

--universe uU uR uσ

variable {U : Type uU} {R : Type uR} {σ : Type uσ} [Quiver U] [Zero R]

/-- Abstract (deterministic, synchronous) dynamics over an architecture.

Parameterizes:
* state type σ
* observable numeric carrier R
* per‑neuron fan‑in/out parameter families (κ₁ / κ₂)
* net / activation / readout

Does NOT assume any invariants (can layer them via separate predicates). -/
structure Dynamics (Architecture : NeuralArch.Architecture U)
    (R : Type uR) (σ : Type uσ) where
  /-- Input fan-in parameter dimension of each neuron. -/
  κ₁ : U → ℕ
  /-- Activation parameter dimension of each neuron. -/
  κ₂ : U → ℕ
  /-- Net-input function at each neuron. -/
  fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ₁ u) → R
  /-- Stateful activation update at each neuron. -/
  fact : ∀ u : U, σ → R → Vector R (κ₂ u) → σ
  /-- Numeric readout from the state of each neuron. -/
  fout : ∀ _ : U, σ → R

/-- Parameter bundle (weights + per‑neuron parameter vectors) independent of invariants. -/
structure Params
    {Architecture : NeuralArch.Architecture U}
    (D : Dynamics Architecture R σ) where
  /-- The weight matrix of the dynamics. -/
  w : Matrix U U R
  /-- Per-neuron net-input parameter vectors. -/
  σv : (u : U) → Vector R (D.κ₁ u)
  /-- Per-neuron activation parameter vectors. -/
  θv : (u : U) → Vector R (D.κ₂ u)

/-- Raw state. -/
structure State
    {Architecture : NeuralArch.Architecture U}
    (D : Dynamics Architecture R σ) where
  /-- The activation value carried by each neuron. -/
  act : U → σ

/-- One synchronous step (no invariance assumptions). -/
def step
    {Architecture : NeuralArch.Architecture U}
    (D : Dynamics Architecture R σ)
    (p : Params (D := D)) (s : State (D := D)) : State (D := D) :=
{ act := fun u =>
    let outs : U → R := fun v => D.fout v (s.act v)
    let net  := D.fnet u (p.w u) outs (p.σv u)
    D.fact u (s.act u) net (p.θv u) }

/-- n synchronous iterations. -/
def iterate
    {Architecture : NeuralArch.Architecture U}
    (D : Dynamics Architecture R σ)
    (p : Params (D := D)) :
    ℕ → State (D := D) → State (D := D)
  | 0     , s => s
  | (n+1) , s => iterate D p n (step D p s)

/-- Fixed point predicate (synchronous). -/
def isFixed
    {Architecture : NeuralArch.Architecture U}
    (D : Dynamics Architecture R σ)
    (p : Params (D := D)) (s : State (D := D)) : Prop :=
  step D p s = s

end NeuralDyn

/-!
1. Monolithic reduction: `NeuralArch.Architecture` + `NeuralDyn.Dynamics`.
2. Future: probabilistic variant: replace `σ` with `PMF σ` or `StateM τ σ`.
3. Linear algebra bridge: introduce `(U → R)` as `Module R _` via `Fintype` and derive a
   `LinearMap` wrapper from matrices (to connect to `fderiv` later).
4. Deep embedding interpreter: reuse `Expr` semantics targeting a `(Params × State) → R`
   functional meaning and state theorem relating one `step` to interpretation of a layer `Expr`.
-/

/-!
## Linear Algebra Bridge

Prereqs:
* `U` finite.
* `R` a (semi)ring.
We expose the matrix-as-linear-map view and show a simple correspondence
for a purely linear (identity activation, zero extra parameters) network
step. This is the algebraic hook needed for future `fderiv` / analysis results.
-/
namespace NeuralNetwork.Linear

open NeuralDyn

variable {U : Type uU} {R : Type uR} {σ : Type uσ}
variable [Fintype U] [DecidableEq U] [CommSemiring R]

/-- Linear state space: functions `U → R` form an `R`-module (reuse existing instance). -/
instance instModuleFun : Module R (U → R) := inferInstance

/-- Wrap a square matrix as an `R`-linear endomorphism `(U → R) →ₗ[R] (U → R)`. -/
def weightLinear (W : Matrix U U R) : (U → R) →ₗ[R] (U → R) :=
  Matrix.mulVecLin W

omit [DecidableEq U] in
@[simp] lemma weightLinear_apply (W : Matrix U U R) (x : U → R) :
  weightLinear (U := U) (R := R) W x = W.mulVec x := rfl

/-- A minimal linear dynamics specialization: state carrier is `(U → R)`,
activation is identity, net is matrix row · current outputs. -/
structure LinearSpec (U : Type uU) [Fintype U] [DecidableEq U] (R : Type uR) [CommSemiring R] where
  -- no per‑neuron auxiliary parameter dimensions needed (set to 0)
  /-- One synchronous linear step is just `W.mulVec`. -/
  step : Matrix U U R → (U → R) → (U → R)
  step_def : ∀ (W : Matrix U U R) (x : U → R), step W x = W.mulVec x

/-- Canonical instance of the linear spec. -/
def canonicalLinearSpec : LinearSpec U R :=
{ step := fun W x => W.mulVec x
, step_def := by intro W x; rfl }

/-- Show that `canonicalLinearSpec.step` matches the linear map induced by `W`. -/
lemma canonical_step_linear (W : Matrix U U R) (x : U → R) :
  (canonicalLinearSpec (U := U) (R := R)).step W x
    = (weightLinear (U := U) (R := R) W) x := by
  simp [canonicalLinearSpec, weightLinear_apply]

/-- Recursive (right-associated) power of a square matrix (local definition to avoid dependence
on a global `Matrix.pow`). -/
def matrixPow (W : Matrix U U R) : ℕ → Matrix U U R
  | 0     => 1
  | n + 1 => matrixPow W n * W

@[simp] lemma matrixPow_zero (W : Matrix U U R) :
  matrixPow (U := U) (R := R) W 0 = 1 := rfl

@[simp] lemma matrixPow_succ (W : Matrix U U R) (n : ℕ) :
  matrixPow (U := U) (R := R) W (n+1) = matrixPow W n * W := rfl

/-- If a (future) shallow dynamics instance encodes a purely linear identity activation
with no extra parameters, its `iterate` under params `W` coincides with the action of
the recursive `matrixPow W n` on the initial vector. -/
lemma iterate_matches_matrix_pow
    (W : Matrix U U R) (x : U → R) (n : ℕ) :
    (Nat.iterate (fun v => W.mulVec v) n) x
      = (matrixPow (U := U) (R := R) W n).mulVec x := by
  -- Generalize over x so the induction hypothesis applies to W.mulVec x in the succ case.
  induction n generalizing x with
  | zero =>
      simp [Nat.iterate, matrixPow]
  | succ n ih =>
      simp [Nat.iterate, matrixPow, ih, Matrix.mulVec_mulVec]

end NeuralNetwork.Linear

/-!
## Architectural / Dynamics Further Abstractions

* Factor architecture vs dynamics vs invariants.
* Provide a probability / monadic hook.
* Prepare for deep embedding + differentiation.

We only add *interfaces* here to keep the existing code stable.
-/
namespace NeuralNetwork.Future

/-- Monadic (e.g. probabilistic / nondeterministic) dynamics hook. -/
structure MDynamics
    {U : Type uU} [Quiver U]
    (Arch : NeuralArch.Architecture U)
    (M : Type _ → Type _) [Monad M]
    (R : Type uR) (σ : Type uσ) where
  /-- Input arity (number of incoming signals) of each neuron. -/
  κ₁ : U → ℕ
  /-- Parameter arity (number of activation parameters) of each neuron. -/
  κ₂ : U → ℕ
  /-- Net-input function combining weights, outputs, and inputs at a neuron. -/
  fnet : ∀ u, (U → R) → (U → R) → Vector R (κ₁ u) → R
  /-- Monadic activation function updating the state of a neuron. -/
  fact : ∀ u, σ → R → Vector R (κ₂ u) → M σ
  /-- Output function reading off the scalar output from a neuron's state. -/
  fout : ∀ _ : U, σ → R

namespace MDynamics

/-- One monadic synchronous layer update (no invariants yet). -/
def step
    {U : Type uU} [Quiver U]
    {Arch : NeuralArch.Architecture U}
    {M : Type _ → Type _} [Monad M]
    {R : Type uR} {σ : Type uσ}
    (D : MDynamics (U := U) Arch M R σ)
    (W : Matrix U U R)
    (σv : (u : U) → Vector R (D.κ₁ u))
    (θv : (u : U) → Vector R (D.κ₂ u))
    (s : U → σ) : U → M σ :=
  -- We return a per‑neuron monadic result `(U → M σ)` instead of lifting the whole
  -- function into the monad (`M (U → σ)`), avoiding the universe mismatch and
  -- making the (currently unsequenced) independent effects explicit.
  fun u =>
    let outs : U → R := fun v => D.fout v (s v)
    let net  := D.fnet u (W u) outs (σv u)
    D.fact u (s u) net (θv u)

end MDynamics

/-- Placeholder symbolic differentiation signature:
Given an `Expr` (scalar) produce a derivative AST; correctness theorem will
relate it to `fderiv` after tensor generalization. -/
def symbolicGrad
    {U : Type uU} {R : Type uR}
    (e : Expr U R) : Expr U R :=
  -- identity placeholder: future work
  e

end NeuralNetwork.Future

/-!
## Roadmap Summary (concise, per reviewer action points)

1. Linear bridge: `weightLinear` + `iterate_matches_matrix_pow` introduced.
2. Architecture vs monadic dynamics: `MDynamics` skeleton.
3. Probabilistic / effectful extension point via generic Monad.
4. Symbolic differentiation placeholder (`symbolicGrad`) to be tied to `fderiv`.
5. Future work: tensor `Expr` (typed shapes) + correctness lemmas `matMul_eval`.
-/

namespace NeuralNetwork.QuiverExt

open NeuralNetwork
open scoped BigOperators

universe u v
variable {U : Type u} [Quiver U]

/-!
These theorems isolate: (1) local recursive law, (2) uniqueness of linear
solutions on layered DAGs, forming the bedrock for path‑based / pruning /
gradient results already present (`arborescent_linear_eval_unique`,
`rootSensitivity_const_one`).
-/

section ForwardEvalEquations

variable {R : Type v}
variable [Semiring R]
variable [Fintype U] [∀ a b : U, Fintype (a ⟶ b)]

/-- Fundamental recursive equation (unfold) for `forwardEval`. -/
lemma forwardEval_equation
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R) (φ : R → R) (inputs : U → R) (a : U) :
  forwardEval (U := U) (R := R) L P φ inputs a =
    φ (inputs a +
        (∑ p : U, ∑ e : (p ⟶ a), P.w e * forwardEval (U := U) (R := R) L P φ inputs p)
        + P.θ a) := by
  unfold forwardEval
  dsimp [WellFounded.fix_eq, Function.comp]
  exact
    WellFounded.fix_eq (Layering.wfMeasure L)
      (fun a rec => φ (inputs a + ∑ p, ∑ e, P.w e * rec p (L.mono e) + P.θ a)) a

/-- Linear specialization (identity activation, zero biases): the computed map
is a solution of the linear recurrence system. -/
lemma forwardEval_linear_sol
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R) (inputs : U → R)
    (hθ : P.θ = fun _ => 0) :
    ∀ a,
      forwardEval (U := U) (R := R) L P (fun x => x) inputs a =
        (inputs a +
          ∑ p : U, ∑ e : (p ⟶ a),
            P.w e * forwardEval (U := U) (R := R) L P (fun x => x) inputs p) := by
  intro a
  have h := forwardEval_equation (U := U) (R := R) L P (fun x => x) inputs a
  simpa [hθ] using h

/-- Uniqueness of the linear solution: any function satisfying the same
recurrence (with identity activation and zero biases) must coincide with
`forwardEval`. -/
lemma forwardEval_linear_unique
    (L : NeuralNetwork.Layering U)
    (P : ArrowParams U R) (inputs : U → R)
    (hθ : P.θ = fun _ => 0)
    (f : U → R)
    (hrec : ∀ a,
      f a =
        inputs a +
          ∑ p : U, ∑ e : (p ⟶ a), P.w e * f p) :
    f = forwardEval (U := U) (R := R) L P (fun x => x) inputs := by
  have h_all : ∀ a, f a = forwardEval (U := U) (R := R) L P (fun x => x) inputs a := by
    intro a
    refine (L.wfMeasure.induction
      (C := fun a => f a = forwardEval (U := U) (R := R) L P (fun x => x) inputs a)
      a ?step)
    intro a ih
    have h_f := hrec a
    have h_eval :=
      forwardEval_equation (U := U) (R := R) L P (fun x => x) inputs a
    have hsubst :
      (∑ p : U, ∑ e : (p ⟶ a), P.w e * f p)
        =
      (∑ p : U, ∑ e : (p ⟶ a),
          P.w e * forwardEval (U := U) (R := R) L P (fun x => x) inputs p) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      refine Finset.sum_congr rfl ?_
      intro e he
      have hlt : L.ℓ p < L.ℓ a := L.mono e
      specialize ih p hlt
      simp_rw [ih]
    have : f a = forwardEval (U := U) (R := R) L P (fun x => x) inputs a := by
      have h_eval' := h_eval
      rw [hθ] at h_eval'
      simp_rw [h_f, hsubst] at *
      exact Eq.symm (forwardEval_linear_sol L P inputs hθ a)
    exact this
  funext a; exact h_all a

end ForwardEvalEquations

end NeuralNetwork.QuiverExt

namespace NeuralNetwork.QuiverExt

open NeuralNetwork
open Quiver
open scoped BigOperators

variable {U : Type u} [Quiver U]

section PathExpansion
variable {R : Type v}
variable [Semiring R]
variable [Fintype U] [DecidableEq U] [∀ a b : U, Fintype (a ⟶ b)]

/-- Finite-length truncated sum of path weights from `s` to `a`
(using the ArrowParams `P` as edge weights). -/
noncomputable
def pathWeightUpTo
    (P : ArrowParams U R) (N : ℕ) (s a : U) : R :=
  letI : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩
  ∑ n ∈ Finset.range (N+1), totalPathWeightLen (U := U) (R := R) s a n

private lemma pathWeightUpTo_zero_len
    (P : ArrowParams U R) (s a : U) :
    pathWeightUpTo (U := U) (R := R) P 0 s a = (if s = a then 1 else 0) := by
  dsimp [pathWeightUpTo]
  simp [totalPathWeightLen]

/-- Fundamental “length-truncated” expansion:
for any `N`, the truncated sum up to `N` splits into (length 0) + (one-step extensions), using the
`totalPathWeightLen` recurrence. -/
private lemma pathWeightUpTo_succ_split
    (P : ArrowParams U R) (N : ℕ) (s a : U) :
    pathWeightUpTo (U := U) (R := R) P N.succ s a
      =
    (if s = a then 1 else 0)
    +
    ∑ i ∈ Finset.range (N+1),
      ∑ c : U, ∑ e : (c ⟶ a),
        (letI : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩;
         totalPathWeightLen (U := U) (R := R) s c i * P.w e) := by
  let _ : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩
  have shift_general :
      ∀ n,
        ∑ k ∈ Finset.range (n+1),
          totalPathWeightLen (U := U) (R := R) s a k
          =
          (if s = a then 1 else 0)
            + ∑ k ∈ Finset.range n,
                totalPathWeightLen (U := U) (R := R) s a (k+1) := by
    intro n
    induction n with
    | zero => simp [totalPathWeightLen]
    | succ n ih =>
      have hsum :
        ∑ k ∈ Finset.range (n+2),
          totalPathWeightLen (U := U) (R := R) s a k
          =
        ∑ k ∈ Finset.range (n+1),
          totalPathWeightLen (U := U) (R := R) s a k
        + totalPathWeightLen (U := U) (R := R) s a (n+1) := by
        simpa using
          (Finset.sum_range_succ
            (f := fun k => totalPathWeightLen (U := U) (R := R) s a k) (n+1))
      calc
        ∑ k ∈ Finset.range (n+2),
          totalPathWeightLen (U := U) (R := R) s a k
            = ∑ k ∈ Finset.range (n+1),
                totalPathWeightLen (U := U) (R := R) s a k
              + totalPathWeightLen (U := U) (R := R) s a (n+1) := hsum
        _ = ((if s = a then 1 else 0)
              + ∑ k ∈ Finset.range n,
                  totalPathWeightLen (U := U) (R := R) s a (k+1))
              + totalPathWeightLen (U := U) (R := R) s a (n+1) := by
              simp [ih]
        _ = (if s = a then 1 else 0)
              + (∑ k ∈ Finset.range n,
                  totalPathWeightLen (U := U) (R := R) s a (k+1)
                 + totalPathWeightLen (U := U) (R := R) s a (n+1)) := by
              simp [add_comm, add_left_comm]
        _ = (if s = a then 1 else 0)
              + ∑ k ∈ Finset.range (n+1),
                  totalPathWeightLen (U := U) (R := R) s a (k+1) := by
              simpa using
                congrArg (fun t =>
                  (if s = a then 1 else 0) + t)
                  ((Finset.sum_range_succ
                    (f := fun k => totalPathWeightLen (U := U) (R := R) s a (k+1)) n).symm)
  have hshift := shift_general (N+1)
  simpa [pathWeightUpTo, totalPathWeightLen] using hshift

/-- If the layering strictly increases along edges, no path from `s` to `a` can have
length greater than `L.ℓ a - L.ℓ s`. Hence the length-`n` total weight vanishes for `n`
beyond that bound. -/
private lemma totalPathWeightLen_vanish_of_too_long
    (L : NeuralNetwork.Layering U) (P : ArrowParams U R)
    (s a : U) :
    ∀ n, L.ℓ a - L.ℓ s < n →
      (letI : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩;
       totalPathWeightLen (U := U) (R := R) s a n) = 0 := by
  let _ : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩
  intro n
  induction n generalizing a with
  | zero =>
    intro hlt
    exact (Nat.not_lt_zero _ hlt).elim
  | succ n ih =>
    intro hlt
    have hGap_le : L.ℓ a - L.ℓ s ≤ n := Nat.lt_succ_iff.mp hlt
    simp only [totalPathWeightLen]
    have hInnerZero :
        ∀ c : U, ∑ e : (c ⟶ a),
          totalPathWeightLen (U := U) (R := R) s c n * P.w e = 0 := by
      intro c
      by_cases hn0 : n = 0
      · have hA_le_S : L.ℓ a ≤ L.ℓ s := by
          have : L.ℓ a - L.ℓ s = 0 := by aesop
          exact (Nat.sub_eq_zero_iff_le).1 (by exact this)
        by_cases hEmpty : IsEmpty (c ⟶ a)
        · haveI := hEmpty
          simp
        · haveI := Classical.decEq (c ⟶ a)
          obtain ⟨e₀⟩ := not_isEmpty_iff.mp hEmpty
          have hc_lt : L.ℓ c < L.ℓ a := L.mono e₀
          have hsc_ne : s ≠ c := by
            intro hsc; subst hsc
            exact (lt_of_le_of_lt hA_le_S hc_lt).false.elim
          have hzero : totalPathWeightLen (U := U) (R := R) s c 0 = 0 := by
            simp [totalPathWeightLen, hsc_ne]
          aesop
      · -- General case: n ≥ 1. Show `L.ℓ c - L.ℓ s < n` to use IH.
        by_cases hEmpty : IsEmpty (c ⟶ a)
        · haveI := hEmpty
          simp
        · haveI := Classical.decEq (c ⟶ a)
          obtain ⟨e₀⟩ := not_isEmpty_iff.mp hEmpty
          have hc_lt : L.ℓ c < L.ℓ a := L.mono e₀
          have h_cgap_lt_n : L.ℓ c - L.ℓ s < n := by
            by_cases hsc : L.ℓ s ≤ L.ℓ c
            · -- Strictness is preserved under subtracting the same amount on ℕ here.
              have : L.ℓ c - L.ℓ s < L.ℓ a - L.ℓ s :=
                Nat.sub_lt_sub_right hsc hc_lt
              exact lt_of_lt_of_le this hGap_le
            · -- Then `L.ℓ c - L.ℓ s = 0` and `0 < n` because `n ≠ 0`.
              have : L.ℓ c ≤ L.ℓ s := le_of_lt (lt_of_le_of_ne (le_of_not_ge hsc) (by aesop))
              have hcz : L.ℓ c - L.ℓ s = 0 := Nat.sub_eq_zero_of_le this
              have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
              simpa [hcz]
          have hzero : totalPathWeightLen (U := U) (R := R) s c n = 0 := ih (a := c) h_cgap_lt_n
          simp [hzero]
    simp [hInnerZero]

/-- Extend the range of the truncated sum without changing its value,
thanks to the vanishing property beyond the layer gap bound. -/
private lemma pathWeightUpTo_extend_to
    (L : NeuralNetwork.Layering U) (P : ArrowParams U R)
    (s c : U) (N : ℕ) (hN : L.ℓ c - L.ℓ s ≤ N) :
    pathWeightUpTo (U := U) (R := R) P N s c
      =
    pathWeightUpTo (U := U) (R := R) P (L.ℓ c - L.ℓ s) s c := by
  classical
  -- Fix the weight instance used by `totalPathWeightLen`.
  let _ : WeightedQuiver U R := ⟨fun {x y} (e : x ⟶ y) => P.w e⟩
  -- Abbreviate the bound M := L.ℓ c - L.ℓ s.
  set M := L.ℓ c - L.ℓ s with hM
  -- Work with the definition of `pathWeightUpTo`.
  dsimp [pathWeightUpTo]
  -- We will shrink `range (N+1)` down to `range (M+1)` using that
  -- terms with index k > M vanish (no path can be that long).
  have hsubset : Finset.range (M + 1) ⊆ Finset.range (N + 1) := by
    intro k hk
    exact Finset.mem_range.2
      (lt_of_lt_of_le (Finset.mem_range.1 hk) (Nat.succ_le_succ hN))
  -- Define the summand.
  have hvanish :
      ∀ {k}, k ∈ Finset.range (N + 1) → k ∉ Finset.range (M + 1) →
        totalPathWeightLen (U := U) (R := R) s c k = 0 := by
    intro k hkN hkNot
    -- From `k ∉ range (M+1)` and naturals, deduce `M < k`.
    have hMk : M < k := by
      -- `k ∉ range (M+1)` ↔ ¬ k < M+1 ↔ M+1 ≤ k
      simp_all only [tsub_le_iff_right, range_subset_range, add_le_add_iff_right,
        mem_range, not_lt, M]
      exact hkNot
    -- Apply the vanishing lemma at level k.
    exact totalPathWeightLen_vanish_of_too_long
      (U := U) (R := R) L P s c k hMk
  -- Now `sum_subset` folds away the vanishing tail (orient result with `.symm` to match goal).
  refine (Finset.sum_subset hsubset (fun k hkN hkNot => by simp [hvanish hkN hkNot])).symm

/- ### (Skeleton) Prefunctor Invariance

Future theorem: evaluation invariant under quiver isomorphisms (weight preserving
bijections). This will leverage `Prefunctor.ext` and transport of sums over
predecessors. -/
-- structure WeightIso {U V} [Quiver U] [Quiver V] (R) :=
-- (F : U ⥤q V) (Finv : V ⥤q U)
-- (left  : Finv.comp F = 𝟭q _) (right : F.comp Finv = 𝟭q _)
-- (wU : ∀ {a b} (e : a ⟶ b), ?wV (F.map e) = ?wU e)

-- TODO: lemma forwardEval_congr_weightIso ...

end PathExpansion

end NeuralNetwork.QuiverExt
