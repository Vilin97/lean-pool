/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module

public import LeanPool.BrillNoetherGraphs.TwiceMarkedBananas.CoreVocabulary

/-!
# Standalone marked-banana statement vocabulary

Marked divisors, transmission permutations, exceptional configurations, and
finite counting expressions used by the paper-facing theorem statements.
-/

@[expose] public section

namespace TMB

universe u v

open Multiset Finset

namespace Banana

variable {g : ℕ} (B : Banana g)

/-- Replace every labelled strand by a path of its specified length. -/
def graph : CFGraph where
  V := B.Vertex
  instNonempty := ⟨B.coreVertex 0⟩
  edges := (Finset.univ : Finset B.Step).val.map B.unitEdge
  loopless := by
    intro z hz
    rw [Multiset.mem_map] at hz
    obtain ⟨step, _, hstep⟩ := hz
    exact B.stepLeft_ne_stepRight step.1 step.2
      ((congrArg Prod.fst hstep).trans (congrArg Prod.snd hstep).symm)

/-- The vertex at a path position along a strand, measured from the
strand's tail. -/
def pathVertex (α : Fin (g + 1)) (i : B.PathPosition α) : B.Vertex :=
  if hzero : i.val = 0 then B.coreVertex (B.tail α)
  else if hlast : i.val = B.length α then B.coreVertex (B.head α)
  else B.interiorVertex α ⟨i.val - 1, by have := i.isLt; omega⟩

/-- Interior positions exclude the two shared endpoints. -/
def IsInteriorPosition (α : Fin (g + 1)) (i : B.PathPosition α) : Prop :=
  0 < i.val ∧ i.val < B.length α

end Banana

/-- Construct a banana from positive strand lengths, every strand oriented
from `0` to `1`. -/
def bananaOfLengths (g : ℕ) (length : Fin (g + 1) → ℕ)
    (hpos : ∀ α, 0 < length α) : Banana g where
  tail := fun _ => 0
  head := fun _ => 1
  length := length
  core_loopless := fun _ => by decide
  length_pos := hpos

/-- The vertex `v_{α,i}` at normalized position `i` along strand `α`,
measured from multivalent vertex `0`; the stored orientation of the strand is
reversed when necessary. -/
def strandVertex {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) : B.graph.V :=
  B.pathVertex α
    (if B.tail α = 0 then i else
      ⟨B.length α - i.val, by have := i.isLt; omega⟩)

/-- Reflection of a strand coordinate. -/
def strandMirror {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) : B.PathPosition α :=
  ⟨B.length α - i.val, by have := i.isLt; omega⟩

/-- The two multivalent vertices. -/
def leftEndpoint {g : ℕ} (B : Banana g) : B.graph.V := B.coreVertex 0
/-- The multivalent banana endpoint corresponding to core pole 1. -/
def rightEndpoint {g : ℕ} (B : Banana g) : B.graph.V := B.coreVertex 1

namespace TwoPathCycle

/-- A two-path cycle is the genus-one banana with the prescribed lengths. -/
def spec (length : Fin 2 → ℕ) (hLength : ∀ edge, 0 < length edge) :
    Banana 1 where
  tail := fun _ => 0
  head := fun _ => 1
  length := length
  core_loopless := fun _ => by decide
  length_pos := hLength

end TwoPathCycle

/-! ### Twice-marked graphs and transmission -/

/-- A graph with two ordered marked vertices. -/
structure TwiceMarked where
  /-- The underlying graph carrying the two ordered marks used for rank differences and
  transmission. -/
  graph : CFGraph
  /-- The first marked vertex, used for the first one-chip subtraction in the rank difference. -/
  u : graph.V
  /-- The second marked vertex, used for the second one-chip subtraction in the rank difference. -/
  v : graph.V

/-- Mark two vertices. -/
abbrev mark (G : CFGraph) (u v : G.V) : TwiceMarked := ⟨G, u, v⟩

/-- The marked second difference of divisor rank. -/
noncomputable def rankDelta (M : TwiceMarked) (D : CFDiv M.graph) : ℤ :=
  rank M.graph D - rank M.graph (D - oneChip M.u) -
    rank M.graph (D - oneChip M.v) +
      rank M.graph (D - oneChip M.u - oneChip M.v)

/-- A two-point twist of a divisor. -/
def twist (M : TwiceMarked) (D : CFDiv M.graph) (a b : ℤ) : CFDiv M.graph :=
  D + a • oneChip M.u + b • oneChip M.v

/-- Submodularity of every marked twist. -/
def Submodular (M : TwiceMarked) (D : CFDiv M.graph) : Prop :=
  ∀ a b : ℤ, 0 ≤ rankDelta M (twist M D a b)

/-- Every divisor is submodular. -/
def AllSubmodular (M : TwiceMarked) : Prop :=
  ∀ D : CFDiv M.graph, Submodular M D

/-- A positive multiple killing the marked difference. -/
def TorsionWitness (M : TwiceMarked) (k : ℕ) : Prop :=
  0 < k ∧ linearEquiv M.graph
    ((k : ℤ) • (oneChip M.u - oneChip M.v)) 0

/-- The least positive torsion witness. -/
def IsTorsionOrder (M : TwiceMarked) (k : ℕ) : Prop :=
  TorsionWitness M k ∧ ∀ m : ℕ, TorsionWitness M m → k ≤ m

/-- Rank-difference characterization of a transmission permutation. -/
def IsTransmissionPermutation (M : TwiceMarked) (D : CFDiv M.graph)
    (τ : ℤ → ℤ) : Prop :=
  Function.Bijective τ ∧ ∀ a b : ℤ,
    (if τ b = a then (1 : ℤ) else 0) =
      rankDelta M (D + a • oneChip M.u - b • oneChip M.v)

/-- Period-`k` affine permutations. -/
def IsKAffine (k : ℕ) (τ : ℤ → ℤ) : Prop :=
  ∀ n : ℤ, τ (n + k) = τ n + k

/-- Fundamental-domain representatives of affine inversions. -/
def kInversions (k : ℕ) (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | p.1 < p.2 ∧ τ p.1 > τ p.2 ∧ 0 ≤ p.1 ∧ p.1 < k }

/-- Number of affine inversions. -/
noncomputable def kInversionCount (k : ℕ) (τ : ℤ → ℤ) : ℕ :=
  (kInversions k τ).ncard

/-- `k`-general transmission. -/
def KGeneralTransmission (M : TwiceMarked) (k : ℕ) : Prop :=
  TorsionWitness M k ∧ AllSubmodular M ∧
    ∀ D : CFDiv M.graph, ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
        (kInversions k τ).Finite ∧
          kInversionCount k τ ≤ Int.toNat (genus M.graph)

/-- Brill--Noether generality in the nonexistence direction. -/
def BrillNoetherGeneral (G : CFGraph) : Prop :=
  ∀ r d : ℤ, 0 ≤ r → BNExists G r d → 0 ≤ bnNumber G r d

/-- The exceptional same-strand position set from Theorem 3.4. -/
def thetaExceptionalPositions {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i j : B.PathPosition α) : Set (B.PathPosition α) :=
  { q | (q.val : ℤ) ≠ (B.length α : ℤ) - (i.val : ℤ) ∧
      (q.val : ℤ) ≠ (j.val : ℤ) ∧
      (j.val : ℤ) - (i.val : ℤ) ≤ (q.val : ℤ) ∧
      (q.val : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) + (B.length α : ℤ) }

/-- Even marking on two distinct theta strands, by cross multiplication. -/
def EvenlyMarkedTheta (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧ 0 < i.val ∧ i.val < B.length α ∧ 0 < j.val ∧ j.val < B.length β ∧
    i.val * B.length β = j.val * B.length α

/-! ### Chains of factors -/

/-- One factor in a mixed-torsion chain. -/
structure KGeneralChainFactor where
  /-- The connected marked graph forming this factor of the mixed-torsion chain. -/
  marked : MarkedGraph
  /-- The period parameter for the factor's certified general transmission property. -/
  period : ℕ
  connected : graphConnected marked.graph
  kGeneral : KGeneralTransmission
    (mark marked.graph marked.left marked.right) period

/-- Prefix-genus period inequalities. -/
def ChainPrefixBudget : ℤ → List KGeneralChainFactor → Prop
  | _, [] => True
  | g, F :: rest =>
      g + genus F.marked.graph < (F.period : ℤ) ∧
        ChainPrefixBudget (g + genus F.marked.graph) rest

/-- Total genus of a list of chain factors. -/
def chainFactorGenus (L : List KGeneralChainFactor) : ℤ :=
  (L.map fun F => genus F.marked.graph).sum

/-- Sharp two-sided torsion budget for a chain. -/
def ChainMinBudget (L : List KGeneralChainFactor) : Prop :=
  ∀ (i : ℕ) (hi : i < L.length),
    min (chainFactorGenus (L.take (i + 1)))
        (chainFactorGenus (L.drop i)) <
      ((L.get ⟨i, hi⟩).period : ℤ)

/-! ### Weierstrass partitions and the once-marked census -/

/-- Twists at the marked point having rank at least `i`. -/
def poleOrderSet (G : CFGraph) (v : G.V) (D : CFDiv G) (i : ℕ) : Set ℤ :=
  {ell | (i : ℤ) ≤ rank G (D + ell • oneChip v)}

/-- Pole order `s_i(D, v)`: the least twist of rank at least `i`. -/
noncomputable def poleOrder (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℤ :=
  sInf (poleOrderSet G v D i)

/-- The `i`th Weierstrass part `i + g - deg D - s_i(D, v)`, over `ℤ`. -/
noncomputable def weierstrassPartInt (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℤ :=
  (i : ℤ) + genus G - deg D - poleOrder G v D i

/-- The `i`th Weierstrass part as a natural number. -/
noncomputable def weierstrassPart (G : CFGraph) (v : G.V) (D : CFDiv G)
    (i : ℕ) : ℕ :=
  (weierstrassPartInt G v D i).toNat

/-- Size `|λ(D, v)|` of the Weierstrass partition: the sum of its parts.  On
a connected graph only the first `g` parts can be nonzero, so the sum is
taken over those. -/
noncomputable def weierstrassSize {G : CFGraph}
    (_hconn : graphConnected G) (v : G.V) (D : CFDiv G) : ℕ :=
  ∑ i ∈ Finset.range (genus G).toNat, weierstrassPart G v D i

/-- The `i`th part of a Young diagram, extended by zero. -/
def onceMarkedPart (lambda : YoungDiagram) (i : ℕ) : ℕ :=
  lambda.rowLens.getD i 0

/-- Membership of a partition in the divisor census of a once-marked graph:
some divisor has `λ_i(D, v) ≥ λ_i` for every `i`, written as the rank test
`r(D + (i + g - deg D - λ_i) v) ≥ i`. -/
def OnceMarkedCensusContains (G : CFGraph) (v : G.V)
    (lambda : YoungDiagram) : Prop :=
  ∃ D : CFDiv G,
    ∀ i : ℕ,
      rank G
        (D + ((i : ℤ) + genus G - deg D - (onceMarkedPart lambda i : ℤ)) •
          oneChip v) ≥ (i : ℤ)

/-- Once-marked Brill--Noether generality: every partition in the divisor
census has size at most the genus. -/
def OnceMarkedBrillNoetherGeneral (G : CFGraph) (v : G.V) : Prop :=
  ∀ lambda : YoungDiagram,
    OnceMarkedCensusContains G v lambda → (lambda.card : ℤ) ≤ genus G

/-! ### Support complexes and rank determining sets -/

/-- Support on which deleting one chip leaves nonnegative rank. -/
def rankSupport (G : CFGraph) (D : CFDiv G) : Set G.V :=
  {x | 0 ≤ rank G (D - oneChip x)}

/-- A divisor is supported on `A`. -/
def DivisorSupportedOn {G : CFGraph} (A : Set G.V) (E : CFDiv G) : Prop :=
  ∀ x, E x ≠ 0 → x ∈ A

/-- Restricted rank lower bound. -/
def restrictedRankGeq (G : CFGraph) (A : Set G.V)
    (D : CFDiv G) (r : ℤ) : Prop :=
  ∀ E : CFDiv G, effective E → deg E = r → DivisorSupportedOn A E →
    winnable G (D - E)

/-- A set tests every divisor-rank lower bound. -/
def RankDetermining (G : CFGraph) (A : Set G.V) : Prop :=
  ∀ (D : CFDiv G) (r : ℤ), restrictedRankGeq G A D r ↔ rankGeq G D r

/-! ### Banana normal forms and exceptional families -/

/-- A semibreak divisor has at most one chosen interior chip per strand. -/
def semibreakDivisor {g : ℕ} (B : Banana g)
    (chips : ∀ α : Fin (g + 1), Option (Fin (B.length α - 1))) : CFDiv B.graph
  | Sum.inl _ => 0
  | Sum.inr ⟨α, offset⟩ => if chips α = some offset then 1 else 0

/-- Membership in the semibreak family. -/
def IsSemibreak {g : ℕ} (B : Banana g) (E : CFDiv B.graph) : Prop :=
  ∃ chips : ∀ α : Fin (g + 1), Option (Fin (B.length α - 1)),
    E = semibreakDivisor B chips

/-- Endpoint/semibreak normal form. -/
def bananaNormalForm {g : ℕ} (B : Banana g) (a b : ℤ)
    (E : CFDiv B.graph) : CFDiv B.graph :=
  a • oneChip (leftEndpoint B) + b • oneChip (rightEndpoint B) + E

/-- The endpoint hyperelliptic pencil. -/
def endpointPencilDivisor {g : ℕ} (B : Banana g) : CFDiv B.graph :=
  oneChip (leftEndpoint B) + oneChip (rightEndpoint B)

/-- A position at distance at least two from both endpoints. -/
def FarFromBananaEndpoints {g : ℕ} (B : Banana g)
    (α : Fin (g + 1)) (i : B.PathPosition α) : Prop :=
  2 ≤ i.val ∧ i.val + 2 ≤ B.length α

/-- Corrected exceptional family for Theorem 1.16. -/
def CorrectedBananaSimpleException {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  (α ≠ β ∧ B.length β = 2 ∧ j.val = 1) ∨
  (α ≠ β ∧ B.length α = 2 ∧ i.val = 1)

/-- Corrected midpoint exception in high genus. -/
def CorrectedMidpointException {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧ 2 * i.val = B.length α ∧ 2 * j.val = B.length β ∧
    (B.length α = 2 ∨ B.length β = 2)

/-- A vertex lies on a normalized banana strand. -/
def VertexOnBananaStrand {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (x : B.graph.V) : Prop :=
  ∃ i : B.PathPosition α, x = strandVertex B α i

/-- Three vertices lie on one common strand. -/
def VerticesOnCommonBananaStrand {g : ℕ} (B : Banana g)
    (x y z : B.graph.V) : Prop :=
  ∃ α : Fin (g + 1),
    VertexOnBananaStrand B α x ∧
      VertexOnBananaStrand B α y ∧
      VertexOnBananaStrand B α z

/-- The corrected cross-strand exceptional coordinates of Theorem 3.9 for
two strictly interior marks. -/
def NSMForBananaInteriorException {g : ℕ} (B : Banana g)
    (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧
    ((i.val = 1 ∧ j.val + 1 = B.length β) ∨
      (i.val + 1 = B.length α ∧ j.val = 1) ∨
      (B.length α = 2 ∧ i.val = 1) ∨
      (B.length β = 2 ∧ j.val = 1))

/-- Endpoint-safe exceptional alternatives in corrected Theorem 3.9. -/
def NSMForBananaException {g : ℕ} (B : Banana g) (u v : B.graph.V) : Prop :=
    (u = leftEndpoint B ∧ v = rightEndpoint B) ∨
    (u = rightEndpoint B ∧ v = leftEndpoint B) ∨
    (∃ (α : Fin (g + 1)) (p : B.PathPosition α), B.IsInteriorPosition α p ∧
      ((u = leftEndpoint B ∧ v = strandVertex B α p ∧ p.val + 1 = B.length α) ∨
       (u = rightEndpoint B ∧ v = strandVertex B α p ∧ p.val = 1) ∨
       (v = leftEndpoint B ∧ u = strandVertex B α p ∧ p.val + 1 = B.length α) ∨
       (v = rightEndpoint B ∧ u = strandVertex B α p ∧ p.val = 1))) ∨
    (∃ (α β : Fin (g + 1)) (i : B.PathPosition α) (j : B.PathPosition β),
      B.IsInteriorPosition α i ∧ B.IsInteriorPosition β j ∧
      u = strandVertex B α i ∧ v = strandVertex B β j ∧
      NSMForBananaInteriorException B α β i j)

/-- Coordinate alternatives for all-submodular theta markings. -/
def ThetaAllSubmodularCoordinates
    (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  (α ≠ β ∧ B.IsInteriorPosition α i ∧
      B.IsInteriorPosition β j) ∨
    ∃ (γ : Fin 3) (p q : B.PathPosition γ),
      p.val < q.val ∧
      ((p.val = 0 ∧
          (q.val + 1 = B.length γ ∨ q.val = B.length γ)) ∨
        (p.val = 1 ∧ q.val = B.length γ)) ∧
      ((strandVertex B α i = strandVertex B γ p ∧
          strandVertex B β j = strandVertex B γ q) ∨
        (strandVertex B α i = strandVertex B γ q ∧
          strandVertex B β j = strandVertex B γ p))

/-- The four exceptional transmission rows in genus two. -/
def ThetaTransmissionSubTwoCase
    (B : Banana 2) (u : B.graph.V) (X : CFDiv B.graph) : Prop :=
  linearEquiv B.graph X (2 • oneChip u)

/-- The theta-graph case where `X` is equivalent to a chip at `u` plus a chip at some `w`, and
the degree-zero differences from `w` to either mark are nonprincipal. -/
def ThetaTransmissionSubOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linearEquiv B.graph X (oneChip u + oneChip w) ∧
    ¬ linearEquiv B.graph (oneChip w - oneChip u) 0 ∧
    ¬ linearEquiv B.graph (oneChip w - oneChip v) 0

/-- The theta-graph case where `X` is equivalent to a chip at `v` plus a chip at `w`, and
neither marked two-chip divisor with `w` is canonical. -/
def ThetaTransmissionAddOneCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  ∃ w : B.graph.V,
    linearEquiv B.graph X (oneChip v + oneChip w) ∧
    ¬ linearEquiv B.graph
      (oneChip u + oneChip w) (canonicalDivisor B.graph) ∧
    ¬ linearEquiv B.graph
      (oneChip v + oneChip w) (canonicalDivisor B.graph)

/-- The theta-graph case where `X` is equivalent to the canonical divisor shifted by a chip from
`u` to `v`. -/
def ThetaTransmissionAddTwoCase
    (B : Banana 2) (u v : B.graph.V) (X : CFDiv B.graph) : Prop :=
  linearEquiv B.graph X
    (canonicalDivisor B.graph - oneChip u + oneChip v)

/-- Concrete finite-residue nonrecurrence. -/
def NonRecurrent (M : TwiceMarked) (k : ℕ) : Prop :=
  ∀ (w : M.graph.V) (n m : Fin k), n.val ≠ 0 → m.val ≠ 0 →
    0 ≤ rank M.graph
      (oneChip w + (n.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    0 ≤ rank M.graph
      (oneChip w + (m.val : ℤ) • (oneChip M.u - oneChip M.v)) →
    n = m

/-- The three coordinate families in the theta branch of Theorem 4.13. -/
def ThetaKGeneralCoordinates
    {k : ℕ} (B : Banana 2) (alpha beta : Fin 3)
    (i : B.PathPosition alpha) (j : B.PathPosition beta) : Prop :=
  (alpha ≠ beta ∧ B.IsInteriorPosition alpha i ∧
    B.IsInteriorPosition beta j ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k) ∨
  (∃ (gamma : Fin 3) (p q : B.PathPosition gamma),
    p.val < q.val ∧ p.val = 0 ∧ q.val + 1 = B.length gamma ∧
    ((strandVertex B alpha i = strandVertex B gamma p ∧
        strandVertex B beta j = strandVertex B gamma q) ∨
      (strandVertex B alpha i = strandVertex B gamma q ∧
        strandVertex B beta j = strandVertex B gamma p)) ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k) ∨
  (∃ (gamma : Fin 3) (p q : B.PathPosition gamma),
    p.val < q.val ∧ p.val = 1 ∧ q.val = B.length gamma ∧
    ((strandVertex B alpha i = strandVertex B gamma p ∧
        strandVertex B beta j = strandVertex B gamma q) ∨
      (strandVertex B alpha i = strandVertex B gamma q ∧
        strandVertex B beta j = strandVertex B gamma p)) ∧
    NonRecurrent (mark B.graph (strandVertex B alpha i)
      (strandVertex B beta j)) k)

/-- The six ordered placements that can have general transmission on a
rigid wedge of two genus-one factors. -/
def WedgeKGeneralPlacement
    (G H : CFGraph) (x : G.V) (y : H.V)
    (u v : (vertexWedge G H x y).V) (k : ℕ) : Prop :=
  (∃ a : G.V, u = Sum.inl x ∧ v = Sum.inl a ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, u = Sum.inl a ∧ v = Sum.inl x ∧ a ≠ x ∧
    Fintype.card G.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y y ∧
    v = wedgeRightVertex G H x y p ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = wedgeRightVertex G H x y y ∧ p ≠ y ∧
    Fintype.card H.V = 2 ∧ k = 2) ∨
  (∃ a : G.V, ∃ p : H.V, u = Sum.inl a ∧
    v = wedgeRightVertex G H x y p ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r) ∨
  (∃ a : G.V, ∃ p : H.V, u = wedgeRightVertex G H x y p ∧
    v = Sum.inl a ∧ a ≠ x ∧ p ≠ y ∧
    ∃ r : ℕ, IsTorsionOrder (mark G a x) r ∧
      IsTorsionOrder (mark H y p) r ∧ k = r)

/-- The isomorphism-invariant theta-or-wedge classification in genus two. -/
def BridgelessGenusTwoKGeneralCharacterization
    (G : CFGraph.{0}) (u v : G.V) (k : ℕ) : Prop :=
  (∃ (B : Banana 2) (φ : CFGraphIso G B.graph)
      (alpha beta : Fin 3) (i : B.PathPosition alpha) (j : B.PathPosition beta),
      φ.vertexEquiv u = strandVertex B alpha i ∧
      φ.vertexEquiv v = strandVertex B beta j ∧
      ThetaKGeneralCoordinates (k := k) B alpha beta i j) ∨
  (∃ (base factor : CFGraph.{0}) (attachment : base.V) (root : factor.V)
      (φ : CFGraphIso G (vertexWedge base factor attachment root)),
      PointedGenusOneRigid base attachment ∧
      PointedGenusOneRigid factor root ∧
      TwoEdgeCutCondition base ∧ TwoEdgeCutCondition factor ∧
      TwoEdgeCutCondition (vertexWedge base factor attachment root) ∧
      WedgeKGeneralPlacement base factor attachment root
        (φ.vertexEquiv u) (φ.vertexEquiv v) k)

/-- Pairwise disjointness of the canonical marked supports at the nonzero
torsion residues. -/
def CanonicalMarkedSupportsPairwiseDisjoint (M : TwiceMarked) (k : ℕ) : Prop :=
  ∀ n m : Fin k, n.val ≠ 0 → m.val ≠ 0 → n ≠ m →
    Disjoint
      (rankSupport M.graph
        (canonicalDivisor M.graph - (n.val : ℤ) • (oneChip M.u - oneChip M.v)))
      (rankSupport M.graph
        (canonicalDivisor M.graph - (m.val : ℤ) • (oneChip M.u - oneChip M.v)))

/-- Degree-`d` representative at a marked-difference index. -/
noncomputable def degreeTwistInt
    (M : TwiceMarked) (D : CFDiv M.graph) (d b : ℤ) : CFDiv M.graph :=
  D + (d - deg D + b) • oneChip M.u - b • oneChip M.v

/-- Effective degree-one torsion residues. -/
def effectiveDegreeOneTwistResidues
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) : Set (Fin k) :=
  {b | 0 ≤ rank M.graph (degreeTwistInt M D 1 b.val)}

open Classical in
/-- Correction term in Lemma 4.10. -/
noncomputable def invTauCorrection (M : TwiceMarked) (D : CFDiv M.graph) : ℤ :=
  if (∃ b : ℤ, linearEquiv M.graph (degreeTwistInt M D 0 b) 0) ∧
      linearEquiv M.graph (oneChip M.u + oneChip M.v)
        (canonicalDivisor M.graph)
    then 1 else 0

/-- Southeast and northwest quadrant index sets. -/
def southeastSet (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | n ≤ k ∧ τ k < m }

/-- The northwest quadrant of an integer function at thresholds `(m, n)`: indices below `n`
whose image is at least `m`. -/
def northwestSet (τ : ℤ → ℤ) (m n : ℤ) : Set ℤ := { k : ℤ | k < n ∧ m ≤ τ k }

/-- Set-theoretic inverse of an integer function. -/
noncomputable def rawInverse (τ : ℤ → ℤ) : ℤ → ℤ :=
  Function.invFun τ

/-- Conjugation by negation. -/
def rawAffineReflection (τ : ℤ → ℤ) : ℤ → ℤ :=
  fun n => -τ (-n)

/-- Reflected inverse used when swapping marks. -/
noncomputable def swapTransmissionPermutation (τ : ℤ → ℤ) : ℤ → ℤ :=
  rawAffineReflection (rawInverse τ)

/-- Riemann--Roch dual divisor with both marks restored. -/
def transmissionDualDivisor {G : CFGraph} (u v : G.V) (D : CFDiv G) : CFDiv G :=
  canonicalDivisor G - D + oneChip u + oneChip v

/-- Sign-changing inversions and their number. -/
def sciSet (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | p.1 < p.2 ∧ 0 < τ p.1 ∧ τ p.2 ≤ 0 }

/-- The natural cardinality of inversion pairs crossing zero in the images: the earlier image is
positive and the later image is nonpositive. -/
noncomputable def sci (τ : ℤ → ℤ) : ℕ := (sciSet τ).ncard

/-- Mark-preserving and mark-swapping graph automorphisms. -/
structure MarkedPointAutomorphism (M : TwiceMarked) where
  /-- The graph automorphism whose vertex bijection preserves the set of the two marked
  vertices. -/
  iso : CFGraphIso M.graph M.graph
  preserves_marked_set (x : M.graph.V) :
    (x = M.u ∨ x = M.v) ↔
      (iso.vertexEquiv x = M.u ∨ iso.vertexEquiv x = M.v)

structure MarkedPointSwap (M : TwiceMarked) extends MarkedPointAutomorphism M where
  map_u : toMarkedPointAutomorphism.iso.vertexEquiv M.u = M.v
  map_v : toMarkedPointAutomorphism.iso.vertexEquiv M.v = M.u

/-- Finite rank-drop sum from Section 5. -/
noncomputable def sectionFiveRankDropSum
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) : ℤ :=
  ∑ m : Fin k,
    (rank M.graph
        (D + ((((m : ℕ) : ℤ) - 1) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v) -
      rank M.graph
        (D + ((((m : ℕ) : ℤ) - 2) • oneChip M.u) -
          ((m : ℕ) : ℤ) • oneChip M.v))

/-- A transmission permutation with a specified inversion lower bound. -/
def HasInversionLowerBound (M : TwiceMarked) (k q : ℕ) : Prop :=
  ∃ D : CFDiv M.graph, ∃ τ : ℤ → ℤ,
    IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
      (kInversions k τ).Finite ∧ q ≤ kInversionCount k τ

/-- Arithmetic functions used by the one-off and cross-one-off blocks. -/
def crossOneOffCutoff (g n : ℕ) : ℕ := g + g / (n - 1)

/-- The cross one-off length condition requiring `n₀` to be at least `g + 1 + g / (n₁ - 1)`,
with natural-number division. -/
def CrossOneOffLongEnough (g n₀ n₁ : ℕ) : Prop :=
  g + 1 + g / (n₁ - 1) ≤ n₀

/-- The one-off row value at index `b`, computed separately for residues zero, `n - 1`, and all
remaining residues modulo `n`. -/
def oneOffRow (g n b : ℕ) : ℕ :=
  if b % n = 0 then b / n
  else if b % n = n - 1 then g + b / n + 1
  else g + 2 * (b / n) + 1 - b

/-- The cross one-off row value at index `b`, with its extra unit in the zero-residue and
interior-residue cases. -/
def crossOneOffRow (g n b : ℕ) : ℕ :=
  if b % n = 0 then b / n + 1
  else if b % n = n - 1 then g + b / n + 1
  else g + 2 * (b / n) + 2 - b

/-- The corrected forced-count formula: `choose g 2` at period two, and `choose (g - 1) 2 + g /
(n - 1)` otherwise. -/
def correctedCrossOneOffForcedCount (g n : ℕ) : ℕ :=
  if n = 2 then Nat.choose g 2
  else Nat.choose (g - 1) 2 + g / (n - 1)

end TMB
