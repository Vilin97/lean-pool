/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/
module


public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Data.List.Chain
public import LeanPool.InflationTermination.TriangleInflation.Defs

/-!
# Inflation for pair-source graphs: definitions

Definitions for the pair-source generalization of `TriangleInflation`: a finite simple
graph `G` without isolated vertices, one binary observed variable per vertex, one independent
latent source per edge. The triangle of `TriangleInflation` is the case `G = C₃`.

The mathematics formalized here is the 2026-09-13 packet as corrected in
`papers/inflation-nontermination/research-handoffs/2026-09-13/claude-code/review/AUDIT-NOTES.md`,
items A1–A7 and B; the source is `sources/B5-pair-source-classification.md` (§1, §3, §5).
This file carries definitions only. The statements live in
the per-topic modules of this directory (proved) and `InflationGraphOpen/` (statements not
yet proved).

## Representational decisions

* **Reuse of the triangle file.** `IsLaw`, `pushforward`, `prodLaw`, `bern`, `respMass`,
  `ThreeBit`, and the triangle hierarchies are imported from `TriangleInflation.Defs`
  rather than redefined. Laws stay bare real weight functions with the predicate `IsLaw`,
  for the reasons given in that file's header.

* **A scenario is a bundled `PairGraph`.** The vertex type, its `Fintype` and `DecidableEq`
  instances, the `SimpleGraph`, decidable adjacency and the no-isolated-vertex condition are
  fields of one structure, so that a scenario can be quantified over. Edges are the subtype
  `{e : Sym2 V // e ∈ G.edgeFinset}`; incidence `PairGraph.inc v` is the `Finset` of edges
  containing `v`.

* **Copied observations are dependent pairs.** `GObs Γ t = Σ v : Γ.V, (Γ.inc v → Fin t)`: a
  copied observation is a vertex together with one copy index per incident edge. For the
  triangle this has `3t²` elements, matching `TriangleInflation.Obs t`, but the
  identification is a
  theorem (`Statements.exists_triObsEquiv`) and not a definitional coincidence: `GObs`
  carries the incidence structure in its second component, `TriangleInflation.Obs` in its
  constructor names.

* **Bit convention and signs.** Outcomes are `Bool`; `false` is the paper's `0`. The sign of
  a bit is `sgn false = 1`, `sgn true = -1`, the convention of AUDIT-NOTES ("signs ±1 with
  false = 0 ↔ +1").

* **`d`-separation is the trail criterion for the depth-one inflation DAG**, not a general
  Pearl definition; see the docstring of `dsep`. AUDIT-NOTES A2 corrects the packet's stated
  criterion, and `dsep` formalizes the corrected one.

* **Finite latent alphabets.** `GCompatible` quantifies over a `GModel`, whose latent spaces
  are arbitrary `Fintype`s, while the mathematics allows arbitrary measurable latent spaces.
  As AUDIT-NOTES D1 phrases it: the formal incompatibility statements are for the
  finite-latent compatible set; the arbitrary-latent statement needs either the
  Rosset–Gisin–Wolfe cardinality reduction (quoted, not formalized) or a direct
  measure-theoretic proof. So the finite-latent compatible set is a *subset* of the general
  one, and a Lean theorem `¬ GCompatible Γ P` is the *weaker* statement: it does not by
  itself say that `P` has no model with an infinite latent alphabet.

* **Division conventions.** Real division by zero is zero in Lean. `glueLaw` nonetheless
  branches explicitly on `0 < μ_Z(z)`, because Definition 7 of Wolfe–Spekkens–Fritz
  prescribes the value `0` on null fibres and the branch records that prescription rather
  than relying on the junk value. `fivePathCorr` does rely on it, and every statement about
  it assumes the conditioning cell is positive.
-/

@[expose] public section

namespace TriangleInflation.Graph

open Finset TriangleInflation

/-! ## Pair-source scenarios -/

/-- A pair-source scenario (AUDIT-NOTES A1): a finite simple graph without isolated
vertices. Each vertex carries one binary observed variable, each edge one independent latent
source shared by its two endpoints. -/
structure PairGraph where
  /-- The observed vertices. -/
  V : Type
  fintypeV : Fintype V
  decEqV : DecidableEq V
  /-- The source graph; an edge is an independent latent source. -/
  G : SimpleGraph V
  decAdj : DecidableRel G.Adj
  /-- No isolated vertices: an observation with no source has no copying convention. -/
  no_isolated : ∀ v : V, ∃ w : V, G.Adj v w

attribute [instance] PairGraph.fintypeV PairGraph.decEqV PairGraph.decAdj

/-- The latent sources of a pair-source scenario: the edges of its graph. -/
abbrev PairGraph.Edge (Γ : PairGraph) := {e : Sym2 Γ.V // e ∈ Γ.G.edgeFinset}

/-- The sources incident to a vertex. -/
def PairGraph.inc (Γ : PairGraph) (v : Γ.V) : Finset Γ.Edge :=
  Finset.univ.filter (fun e => v ∈ (e.1 : Sym2 Γ.V))

/-- A target law: a weight function on the binary observed vertices. -/
abbrev GTarget (Γ : PairGraph) := (Γ.V → Bool) → ℝ

/-! ## Order-`t` copied observations -/

/-- The copied observations of the order-`t` inflation (AUDIT-NOTES A1): one observation for
each vertex `v` and each choice of a copy index for every source incident to `v`. -/
abbrev GObs (Γ : PairGraph) (t : ℕ) := Σ v : Γ.V, (Γ.inc v → Fin t)

/-- A deterministic assignment of all copied observations. -/
abbrev GAssign (Γ : PairGraph) (t : ℕ) := GObs Γ t → Bool

/-- The copied latent sources: a source together with a copy index. -/
abbrev GLatent (Γ : PairGraph) (t : ℕ) := Γ.Edge × Fin t

variable {Γ : PairGraph} {t : ℕ}

/-- The action of a per-source permutation of copy indices on copied observations. -/
def gPerm (π : Γ.Edge → Equiv.Perm (Fin t)) (o : GObs Γ t) : GObs Γ t :=
  ⟨o.1, fun e => π e.1 (o.2 e)⟩

/-- The induced action on assignments. -/
def gRelabel (π : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t) : GAssign Γ t :=
  fun o => ω (gPerm π o)

/-- Symmetry of a witness under independent permutations of the copy indices of each source
(AUDIT-NOTES A1; the pair-source form of `TriangleInflation.SymmetricLaw`). -/
def GSymmetric (t : ℕ) (Δ : GAssign Γ t → ℝ) : Prop :=
  ∀ (π : Γ.Edge → Equiv.Perm (Fin t)) (ω : GAssign Γ t), Δ (gRelabel π ω) = Δ ω

/-! ## The copied original scenarios -/

/-- The copied observation of the vertex `v` in the copy of the original scenario selected by
the index vector `ι`. -/
def copyObs (ι : Γ.Edge → Fin t) (v : Γ.V) : GObs Γ t := ⟨v, fun e => ι e.1⟩

/-- The copied original scenario selected by `ι`: one copied observation per vertex. -/
def copySet (ι : Γ.Edge → Fin t) : Finset (GObs Γ t) := Finset.univ.image (copyObs ι)

/-- The observed outcome that an assignment gives to the copied scenario selected by `ι`. -/
def readCopy (ι : Γ.Edge → Fin t) (ω : GAssign Γ t) : Γ.V → Bool := fun v => ω (copyObs ι v)

/-- The `t` diagonal rows: row `r` takes the copy index `r` on every source
(AUDIT-NOTES A1). -/
def readDiag (ω : GAssign Γ t) : Fin t → (Γ.V → Bool) := fun r => readCopy (fun _ => r) ω

/-- The `t`-fold tensor power of a target law. -/
def gTensorPow (t : ℕ) (P : GTarget Γ) : (Fin t → (Γ.V → Bool)) → ℝ :=
  fun v => ∏ r : Fin t, P (v r)

/-! ## Ancestry -/

/-- The copied latent ancestors of a copied observation: for each incident source, the copy
selected by that observation. -/
def gAncestors (o : GObs Γ t) : Finset (GLatent Γ t) :=
  (Finset.univ : Finset (Γ.inc o.1)).image (fun e => (e.1, o.2 e))

/-- The copied latent ancestors of a set of copied observations. -/
def gAncestorsOf (S : Finset (GObs Γ t)) : Finset (GLatent Γ t) := S.biUnion gAncestors

/-- Two sets of copied observations are ancestrally independent when their copied latent
ancestors are disjoint (`TriangleInflation.AncestrallyIndependent` for a general pair
graph). -/
def GAncestrallyIndependent (S T : Finset (GObs Γ t)) : Prop :=
  Disjoint (gAncestorsOf S) (gAncestorsOf T)

/-- The sources that a set of copied observations touches, ignoring copy indices. Two blocks
with disjoint `edgesOf` are the "source-disjoint blocks" of AUDIT-NOTES A3(i). -/
def edgesOf (S : Finset (GObs Γ t)) : Finset Γ.Edge := S.biUnion (fun o => Γ.inc o.1)

/-! ## Injectable sets -/

/-- The working definition of injectability: a set of copied observations lies inside one
copied original scenario. -/
def GInjectable (S : Finset (GObs Γ t)) : Prop := ∃ ι : Γ.Edge → Fin t, S ⊆ copySet ι

/-- Two copied observations agree in the copy index of every source incident to both. -/
def GSharedAgree (o p : GObs Γ t) : Prop :=
  ∀ (e : Γ.Edge) (ho : e ∈ Γ.inc o.1) (hp : e ∈ Γ.inc p.1), o.2 ⟨e, ho⟩ = p.2 ⟨e, hp⟩

/-- The primitive Wolfe–Spekkens–Fritz condition (Definition 4) for a pair-source scenario:
erasing copy indices is injective on the set, and any two members agree in the copy index of
every shared source. `Statements.gInjectable_iff_raw` records the equivalence with
`GInjectable`, as `TriangleInflation.injectable_iff_injectableRaw` does for the triangle. -/
def GInjectableRaw (S : Finset (GObs Γ t)) : Prop :=
  (∀ o ∈ S, ∀ p ∈ S, o.1 = p.1 → o = p) ∧ (∀ o ∈ S, ∀ p ∈ S, GSharedAgree o p)

/-- The restriction of an assignment to a set of copied observations. -/
def gRestrict (S : Finset (GObs Γ t)) (ω : GAssign Γ t) : S → Bool := fun o => ω o.1

/-- The outcome pattern that a target law prescribes on a set of copied observations: each
member reads the bit of the vertex it is a copy of. -/
def gPartyRead (S : Finset (GObs Γ t)) (w : Γ.V → Bool) : S → Bool := fun o => w o.1.1

/-- The restriction map between laws on nested sets of copied observations. -/
def subRestrict {S T : Finset (GObs Γ t)} (h : S ⊆ T) (φ : T → Bool) : S → Bool :=
  fun o => φ ⟨o.1, h o.2⟩

/-- Reading a block inside an ambient set. When `B ⊆ S` this is `subRestrict`; the `else`
branch is unreachable and is present only so that the block may be given as a bare `Finset`,
without carrying the inclusion proof. -/
def readOnBlock (B S : Finset (GObs Γ t)) (φ : S → Bool) : B → Bool :=
  fun o => if h : o.1 ∈ S then φ ⟨o.1, h⟩ else false

/-! ## The finite inflation tests -/

/-- Every injectable set carries the corresponding marginal of the target. -/
def GInjectableMarginals (t : ℕ) (Δ : GAssign Γ t → ℝ) (P : GTarget Γ) : Prop :=
  ∀ S : Finset (GObs Γ t), GInjectable S →
    pushforward Δ (gRestrict S) = pushforward P (gPartyRead S)

/-- Every finite family of pairwise ancestrally independent injectable sets carries the
product of the corresponding marginals. -/
def GAncestralProducts (t : ℕ) (Δ : GAssign Γ t → ℝ) (P : GTarget Γ) : Prop :=
  ∀ (n : ℕ) (S : Fin n → Finset (GObs Γ t)), (∀ m, GInjectable (S m)) →
    (∀ m m', m ≠ m' → GAncestrallyIndependent (S m) (S m')) →
    pushforward Δ (fun ω m => gRestrict (S m) ω)
      = fun φ : ∀ m : Fin n, (S m) → Bool =>
          ∏ m : Fin n, pushforward P (gPartyRead (S m)) (φ m)

/-- The Navascués–Wolfe feasible set of a pair-source scenario (AUDIT-NOTES A1): a symmetric
law on the copied observations whose diagonal law is the tensor power of the target. -/
def GNWFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) : Prop :=
  ∃ Δ : GAssign Γ t → ℝ, IsLaw Δ ∧ GSymmetric t Δ ∧ pushforward Δ readDiag = gTensorPow t P

/-- The ancestral-independence feasible set of a pair-source scenario (AUDIT-NOTES A1). -/
def GAIFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) : Prop :=
  ∃ Δ : GAssign Γ t → ℝ, IsLaw Δ ∧ GSymmetric t Δ ∧
    pushforward Δ readDiag = gTensorPow t P ∧
    GInjectableMarginals t Δ P ∧ GAncestralProducts t Δ P

/-! ## Recursive expressibility

The inflation DAG of a pair-source scenario has depth one: the copied latent sources are
roots, the copied observations are sinks, and the parents of a copied observation are exactly
its `gAncestors`. -/

/-- Two copied observations share a copied latent parent. -/
def SharesParent (o p : GObs Γ t) : Prop := ¬ Disjoint (gAncestors o) (gAncestors p)

/-- A trail from `X` to `Y` that is active given `Z`: a sequence of copied observations
`o₀ ∈ X`, `mid`, `o₁ ∈ Y` (so of length at least two) in which consecutive members share a
copied latent parent and every internal member lies in `Z`. -/
def ActiveTrail (X Y Z : Finset (GObs Γ t)) (o₀ : GObs Γ t) (mid : List (GObs Γ t))
    (o₁ : GObs Γ t) : Prop :=
  o₀ ∈ X ∧ o₁ ∈ Y ∧ (∀ o ∈ mid, o ∈ Z) ∧ List.IsChain SharesParent (o₀ :: (mid ++ [o₁]))

/-- `d`-separation in the order-`t` inflation DAG, by the trail criterion.

This is the specialization of Pearl `d`-separation to a DAG in which every latent node is a
root and every observed node is a sink. In such a DAG a trail between two observed nodes
alternates observed node, shared latent parent, observed node; every latent on it is a fork
and every internal observed node is a collider; and no node has descendants, so a collider is
unblocked exactly when it is itself conditioned on. Hence a trail is active given `Z` exactly
when all of its internal observed nodes lie in `Z`, and `X ⊥_d Y | Z` exactly when no such
trail exists.

AUDIT-NOTES A2 corrects the packet's stated criterion ("no component of the shared-parent
graph on `X ∪ Y ∪ Z` meets both `X` and `Y`", which is only sufficient); this definition is
the corrected trail criterion, and the component statement becomes a theorem for AI sets
(`Statements.expressible_iff_ai`). -/
def dsep (X Y Z : Finset (GObs Γ t)) : Prop := ∀ o₀ mid o₁, ¬ ActiveTrail X Y Z o₀ mid o₁

theorem sub_left_union (X Y Z : Finset (GObs Γ t)) : X ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro a ha; simp only [Finset.mem_union] at *; tauto

theorem sub_right_union (X Y Z : Finset (GObs Γ t)) : Y ∪ Z ⊆ X ∪ Y ∪ Z := by
  intro a ha; simp only [Finset.mem_union] at *; tauto

theorem sub_mid_union (X Y Z : Finset (GObs Γ t)) : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right

theorem sub_mid_left (X Z : Finset (GObs Γ t)) : Z ⊆ X ∪ Z := Finset.subset_union_right

noncomputable
section

/-- The glued law of Wolfe–Spekkens–Fritz Definition 7:
`μ(x,y,z) = μ₁(x,z) μ₂(y,z) / μ_Z(z)` when the common `Z`-marginal `μ_Z(z)` is positive, and
`0` otherwise. `μ_Z` is taken as the `Z`-marginal of `μ₁`; on the sets where the rule is
applied the two marginals agree. -/
def glueLaw (X Y Z : Finset (GObs Γ t))
    (μ₁ : ((X ∪ Z : Finset (GObs Γ t)) → Bool) → ℝ)
    (μ₂ : ((Y ∪ Z : Finset (GObs Γ t)) → Bool) → ℝ) :
    ((X ∪ Y ∪ Z : Finset (GObs Γ t)) → Bool) → ℝ := fun φ =>
  let mz := pushforward μ₁ (subRestrict (sub_mid_left X Z)) (subRestrict (sub_mid_union X Y Z) φ)
  if 0 < mz then
    μ₁ (subRestrict (sub_left_union X Y Z) φ) * μ₂ (subRestrict (sub_right_union X Y Z) φ) / mz
  else 0

/-- The recursively expressible sets of the order-`t` inflation, each with its prescribed
law (paper Definition 2.5, Wolfe–Spekkens–Fritz Definition 7). `Expressible t P S μ` says
that the closure prescribes the law `μ` on the set `S` of copied observations.

The three rules are: an injectable set carries the pushforward of the target under the
party-read map; two prescribed sets `X ∪ Z` and `Y ∪ Z` with `X`, `Y`, `Z` pairwise disjoint
and `dsep X Y Z` glue to `X ∪ Y ∪ Z`; and marginals of prescribed sets are prescribed.

This is the definition that `TriangleInflation.Defs` deliberately omits. -/
inductive Expressible (t : ℕ) (P : GTarget Γ) :
    (S : Finset (GObs Γ t)) → ((S → Bool) → ℝ) → Prop
  | inj {S : Finset (GObs Γ t)} (h : GInjectable S) :
      Expressible t P S (pushforward P (gPartyRead S))
  | glue {X Y Z : Finset (GObs Γ t)} {μ₁ μ₂}
      (h₁ : Expressible t P (X ∪ Z) μ₁) (h₂ : Expressible t P (Y ∪ Z) μ₂)
      (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hYZ : Disjoint Y Z)
      (hd : dsep X Y Z) :
      Expressible t P (X ∪ Y ∪ Z) (glueLaw X Y Z μ₁ μ₂)
  | marg {S T : Finset (GObs Γ t)} {μ} (hST : S ⊆ T) (h : Expressible t P T μ) :
      Expressible t P S (pushforward μ (subRestrict hST))

end

/-- The recursively expressible feasible set of a pair-source scenario (paper
Definition 2.3). -/
def GExpFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) : Prop :=
  ∃ Δ : GAssign Γ t → ℝ, IsLaw Δ ∧ GSymmetric t Δ ∧
    pushforward Δ readDiag = gTensorPow t P ∧
    ∀ (S : Finset (GObs Γ t)) (μ : (S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ

/-! ## AI sets

The sets and laws that the ancestral-independence prescriptions cover. AUDIT-NOTES A2
identifies these with the recursively expressible ones. -/

/-- Connectivity in the shared-parent graph on a set of copied observations. -/
def sharedComponent (S : Finset (GObs Γ t)) : S → S → Prop :=
  Relation.ReflTransGen (fun a b : S => SharesParent a.1 b.1)

/-- An AI set: every connected component of the shared-parent graph on `S` is injectable
(AUDIT-NOTES A2). The component of `o` is described by its membership predicate rather than
constructed, so that no decidability of `sharedComponent` is needed. -/
def IsAISet (S : Finset (GObs Γ t)) : Prop :=
  ∀ o : S, ∃ B : Finset (GObs Γ t),
    (∀ p, p ∈ B ↔ ∃ h : p ∈ S, sharedComponent S o ⟨p, h⟩) ∧ GInjectable B

/-- A presentation of a set of copied observations as a union of pairwise ancestrally
independent injectable blocks. -/
structure AIDecomposition (S : Finset (GObs Γ t)) where
  /-- The number of blocks. -/
  n : ℕ
  /-- The blocks. -/
  block : Fin n → Finset (GObs Γ t)
  inj : ∀ m, GInjectable (block m)
  ai : ∀ m m', m ≠ m' → GAncestrallyIndependent (block m) (block m')
  cover : S = (Finset.univ : Finset (Fin n)).biUnion block

/-- The AI product law of a decomposition: the product of the injectable marginals of the
blocks. -/
def aiProduct (S : Finset (GObs Γ t)) (D : AIDecomposition S) (P : GTarget Γ) :
    (S → Bool) → ℝ :=
  fun φ => ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m)) (readOnBlock (D.block m) S φ)

/-! ## Compatibility -/

/-- A model of a pair-source scenario with finite latent alphabets: one latent alphabet and
source law per edge, and for each vertex the probability `resp v` of the outcome
`false = 0` given the values of the sources incident to it. -/
structure GModel (Γ : PairGraph) where
  /-- The latent alphabet of each source. -/
  L : Γ.Edge → Type
  fintypeL : ∀ e, Fintype (L e)
  /-- The law of each source. -/
  μ : ∀ e, L e → ℝ
  /-- `resp v c = Pr(outcome at v is 0 | incident sources take the values c)`. -/
  resp : ∀ v : Γ.V, ((e : Γ.inc v) → L e.1) → ℝ

attribute [instance] GModel.fintypeL

/-- A model is valid when every source law is a law and every response probability lies in
`[0,1]`. -/
def GModel.Valid (M : GModel Γ) : Prop :=
  (∀ e, IsLaw (M.μ e)) ∧ (∀ v c, 0 ≤ M.resp v c ∧ M.resp v c ≤ 1)

/-- The observed law of a model: the sources are independent and the responses are
conditionally independent given the sources. -/
def GModel.law (M : GModel Γ) : GTarget Γ := fun w =>
  ∑ x : (∀ e : Γ.Edge, M.L e),
    (∏ e : Γ.Edge, M.μ e (x e)) * ∏ v : Γ.V, respMass (M.resp v (fun e => x e.1)) (w v)

/-- The compatible set `C_G` of a pair-source scenario, with the finite-latent-alphabet
boundary described in the file header (AUDIT-NOTES D1). -/
def GCompatible (Γ : PairGraph) (P : GTarget Γ) : Prop :=
  ∃ M : GModel Γ, M.Valid ∧ M.law = P

/-! ## Named scenarios -/

/-- The path `P_k` on `Fin k`. -/
def pathAdj (k : ℕ) : SimpleGraph (Fin k) where
  Adj a b := a.val + 1 = b.val ∨ b.val + 1 = a.val
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨by intro a h; omega⟩

instance (k : ℕ) (a b : Fin k) : Decidable ((pathAdj k).Adj a b) :=
  inferInstanceAs (Decidable (a.val + 1 = b.val ∨ b.val + 1 = a.val))

theorem path_no_isolated {k : ℕ} (hk : 2 ≤ k) (v : Fin k) : ∃ w, (pathAdj k).Adj v w := by
  rcases lt_or_ge (v.val + 1) k with h | h
  · exact ⟨⟨v.val + 1, h⟩, Or.inl rfl⟩
  · have hv : 1 ≤ v.val := by omega
    exact ⟨⟨v.val - 1, by omega⟩, Or.inr (by simp; omega)⟩

/-- The cycle `C_m` on `Fin m`. For `m ≥ 3` the adjacency `a ≠ b ∧ (a+1 ≡ b ∨ b+1 ≡ a)` is
the `m`-cycle; the explicit `a ≠ b` makes the relation irreflexive for every `m`. -/
def cycleAdj (m : ℕ) : SimpleGraph (Fin m) where
  Adj a b := a ≠ b ∧ ((a.val + 1) % m = b.val ∨ (b.val + 1) % m = a.val)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance (m : ℕ) (a b : Fin m) : Decidable ((cycleAdj m).Adj a b) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem cycle_no_isolated {m : ℕ} (hm : 3 ≤ m) (v : Fin m) : ∃ w, (cycleAdj m).Adj v w := by
  have hlt : (v.val + 1) % m < m := Nat.mod_lt _ (by omega)
  refine ⟨⟨(v.val + 1) % m, hlt⟩, ?_, Or.inl rfl⟩
  intro h
  have hv : (v.val + 1) % m = v.val := congrArg Fin.val h.symm
  rcases lt_or_ge (v.val + 1) m with hl | hl
  · rw [Nat.mod_eq_of_lt hl] at hv; omega
  · have he : v.val + 1 = m := by omega
    rw [he, Nat.mod_self] at hv
    omega

/-- The vertices of a double star: two centres and their leaves. -/
inductive DoubleStarV (p q : ℕ)
  | left | right | leftLeaf (i : Fin p) | rightLeaf (j : Fin q)
  deriving DecidableEq, Fintype

open DoubleStarV in
/-- Adjacency of the double star: the centre edge, and each leaf to its centre. -/
def doubleStarRel (p q : ℕ) : DoubleStarV p q → DoubleStarV p q → Prop
  | left, right => True
  | right, left => True
  | left, leftLeaf _ => True
  | leftLeaf _, left => True
  | right, rightLeaf _ => True
  | rightLeaf _, right => True
  | _, _ => False

instance (p q : ℕ) (a b : DoubleStarV p q) : Decidable (doubleStarRel p q a b) := by
  cases a <;> cases b <;> unfold doubleStarRel <;> infer_instance

/-- The double star with `p` left leaves and `q` right leaves. -/
def doubleStarAdj (p q : ℕ) : SimpleGraph (DoubleStarV p q) where
  Adj := doubleStarRel p q
  symm := ⟨by intro a b h; cases a <;> cases b <;> simp_all [doubleStarRel]⟩
  loopless := ⟨by intro a h; cases a <;> simp_all [doubleStarRel]⟩

instance (p q : ℕ) (a b : DoubleStarV p q) : Decidable ((doubleStarAdj p q).Adj a b) :=
  inferInstanceAs (Decidable (doubleStarRel p q a b))

theorem doubleStar_no_isolated (p q : ℕ) (v : DoubleStarV p q) :
    ∃ w, (doubleStarAdj p q).Adj v w := by
  cases v
  · exact ⟨DoubleStarV.right, trivial⟩
  · exact ⟨DoubleStarV.left, trivial⟩
  · exact ⟨DoubleStarV.left, trivial⟩
  · exact ⟨DoubleStarV.right, trivial⟩

/-- The path scenario `P_k`, `k ≥ 2`. -/
def path (k : ℕ) (hk : 2 ≤ k) : PairGraph :=
  ⟨Fin k, inferInstance, inferInstance, pathAdj k, inferInstance, path_no_isolated hk⟩

/-- The cycle scenario `C_m`, `m ≥ 3`. -/
def cycle (m : ℕ) (hm : 3 ≤ m) : PairGraph :=
  ⟨Fin m, inferInstance, inferInstance, cycleAdj m, inferInstance, cycle_no_isolated hm⟩

/-- The double-star scenario with `p` and `q` leaves. -/
def doubleStar (p q : ℕ) : PairGraph :=
  ⟨DoubleStarV p q, inferInstance, inferInstance, doubleStarAdj p q, inferInstance,
    doubleStar_no_isolated p q⟩

/-- The triangle scenario, `C₃`. -/
def triangleGraph : PairGraph := cycle 3 (by norm_num)

/-- The square scenario, `C₄`. -/
def squareGraph : PairGraph := cycle 4 (by norm_num)

/-- The five-observer path `P₅` (AUDIT-NOTES A4). -/
def fivePathGraph : PairGraph := path 5 (by norm_num)

/-- A double-star forest: every connected component is a tree of diameter at most three
(AUDIT-NOTES A3). Stated as acyclicity together with a diameter bound inside each
component. -/
def IsDoubleStarForest {V : Type} (G : SimpleGraph V) : Prop :=
  G.IsAcyclic ∧ ∀ u v : V, G.Reachable u v → G.dist u v ≤ 3

/-! ## Signs, flips and explicit laws -/

/-- The sign of a bit: `sgn false = 1`, `sgn true = -1` (AUDIT-NOTES convention). -/
def sgn (b : Bool) : ℝ := if b then -1 else 1

/-- The kernel of independent flips with probability `η` at every coordinate. -/
def flipKernel {ι : Type} [Fintype ι] (η : ℝ) (x y : ι → Bool) : ℝ :=
  ∏ i, (if x i = y i then 1 - η else η)

/-- A law after independent flips of each coordinate with probability `η`. Applied to a
target on `Γ.V → Bool` it is the noisy target of AUDIT-NOTES A7; applied to a witness on
`GObs Γ t → Bool` it is the local flip of every copied observation. -/
def flipLaw {ι : Type} [Fintype ι] [DecidableEq ι] (η : ℝ) (P : (ι → Bool) → ℝ) :
    (ι → Bool) → ℝ := fun y => ∑ x, P x * flipKernel η x y

noncomputable
section

/-- The total variation distance, half the `ℓ¹` distance. -/
def dTV {α : Type*} [Fintype α] (P Q : α → ℝ) : ℝ := (1 / 2) * ∑ a, |P a - Q a|

/-- The total variation distance from a target to the compatible set. -/
def distToCompatible (Γ : PairGraph) (P : GTarget Γ) : ℝ :=
  sInf {d : ℝ | ∃ Q : GTarget Γ, GCompatible Γ Q ∧ d = dTV P Q}

/-- The five-path target of AUDIT-NOTES A4 (packet equation (1)):
`P_h(x,b,c,d,z) = (1/32)[1 + bcd (1+h)/4 (1 + (−1)^{x+z})]`, with vertex `0` the left
endpoint `A`, vertices `1,2,3` the middle observations `B,C,D` and vertex `4` the right
endpoint `E`. -/
def fivePathTarget (h : ℝ) : (Fin 5 → Bool) → ℝ := fun w =>
  (1 / 32) *
    (1 + sgn (w 1) * sgn (w 2) * sgn (w 3) * ((1 + h) / 4) * (1 + sgn (w 0) * sgn (w 4)))

/-- The conditional correlator `f_{xz} = E[BCD | A = x, E = z]` of AUDIT-NOTES A4. The
denominator is the conditioning cell; the value is junk `0` when that cell is null, and every
statement about it assumes the cell is positive. -/
def fivePathCorr (P : (Fin 5 → Bool) → ℝ) (x z : Bool) : ℝ :=
  (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then sgn (w 1) * sgn (w 2) * sgn (w 3) * P w else 0)
    / (∑ w : Fin 5 → Bool, if w 0 = x ∧ w 4 = z then P w else 0)

/-- `I = ¼ Σ_{x,z} f_{xz}` (AUDIT-NOTES A4). -/
def fivePathI (P : (Fin 5 → Bool) → ℝ) : ℝ :=
  (1 / 4) * ∑ x : Bool, ∑ z : Bool, fivePathCorr P x z

/-- `J = ¼ Σ_{x,z} (−1)^{x+z} f_{xz}` (AUDIT-NOTES A4). -/
def fivePathJ (P : (Fin 5 → Bool) → ℝ) : ℝ :=
  (1 / 4) * ∑ x : Bool, ∑ z : Bool, sgn x * sgn z * fivePathCorr P x z

/-- The source boundary `∂F` of a set of vertices of the cycle `C_m`, encoded by its lower
endpoint: the edge `{v, v+1}` is recorded by `v`, and lies in `∂F` exactly when exactly one
of `v`, `v+1` lies in `F` (AUDIT-NOTES A5). -/
def cycleBoundary (m : ℕ) (F : Finset (Fin m)) : Finset (Fin m) :=
  Finset.univ.filter
    (fun v : Fin m => (v ∈ F) ≠ (⟨(v.val + 1) % m, Nat.mod_lt _ v.pos⟩ ∈ F))

/-- The cycle target `P_{m,q}` of AUDIT-NOTES A5, given by its Fourier expansion: the
character of `F ⊆ V` has moment `(−q)^{|∂F|/2}`. The boundary has even size, so the natural
division is exact. -/
def cycleTarget (m : ℕ) (q : ℝ) : (Fin m → Bool) → ℝ := fun w =>
  (1 / 2 : ℝ) ^ m *
    ∑ F : Finset (Fin m), (-q) ^ ((cycleBoundary m F).card / 2) * ∏ v ∈ F, sgn (w v)

/-- The square parity target of AUDIT-NOTES B2(i): the case `m = 4` of `cycleTarget`. -/
def squareTarget (q : ℝ) : (Fin 4 → Bool) → ℝ := cycleTarget 4 q

/-- The parity-perfect triangle target `Π(−q,−q,−q)` of AUDIT-NOTES B2(ii): supported on the
even-parity triples, where it equals `(1 − q(α+β+γ))/4` with `α,β,γ` the signs of the three
bits. All one- and two-point moments are `−q` and the triple moment is `1`. Stated in the
three-bit type of `TriangleInflation`. -/
def triParity (q : ℝ) : ThreeBit → ℝ := fun w =>
  if (xor (xor w.1 w.2.1) w.2.2) = false then
    (1 - q * (sgn w.1 + sgn w.2.1 + sgn w.2.2)) / 4
  else 0

/-- `E[A]` for a three-bit law, in the sign convention. -/
def triMeanA (P : ThreeBit → ℝ) : ℝ := ∑ w : ThreeBit, sgn w.1 * P w

/-- `E[B]` for a three-bit law. -/
def triMeanB (P : ThreeBit → ℝ) : ℝ := ∑ w : ThreeBit, sgn w.2.1 * P w

/-- `E[C]` for a three-bit law. -/
def triMeanC (P : ThreeBit → ℝ) : ℝ := ∑ w : ThreeBit, sgn w.2.2 * P w

/-- The transported target of AUDIT-NOTES A6: the `H`-target on the image of an induced
embedding, tensored with fair bits on the remaining vertices of `G`. -/
def transportTarget (G H : PairGraph) (φ : H.V → G.V) (P : GTarget H) : GTarget G :=
  fun w => P (fun u => w (φ u)) * (1 / 2 : ℝ) ^ (Fintype.card G.V - Fintype.card H.V)

end

/-! ## The triangle re-encoding

The triangle scenario `triangleGraph` has vertex type `Fin 3`; the triangle file uses
`ThreeBit = Bool × Bool × Bool`. Under the identification below, vertex `0` is the party `A`
(sources `{0,1}` and `{2,0}`, the paper's `X` and `Z`), vertex `1` is `B` (sources `{0,1}`
and `{1,2}`, the paper's `X` and `Y`) and vertex `2` is `C` (sources `{1,2}` and `{2,0}`, the
paper's `Y` and `Z`). -/

/-- The re-encoding of a three-bit outcome as a function on `Fin 3`. -/
def threeBitEquiv : (Fin 3 → Bool) ≃ ThreeBit where
  toFun w := (w 0, w 1, w 2)
  invFun x := ![x.1, x.2.1, x.2.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv x := rfl

end TriangleInflation.Graph
