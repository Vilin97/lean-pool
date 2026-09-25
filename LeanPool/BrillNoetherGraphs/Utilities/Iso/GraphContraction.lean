/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.StrongSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LaplacianEquiv
import Mathlib.Tactic

/-!
# Controlled graph-contraction certificates

This is a deliberately one-way quotient interface.  A certificate records a
surjective vertex map whose *inter-fibre* edge multiplicities agree exactly
with the target graph.  Edges inside one fibre are intentionally unconstrained:
they are the contracted edges and disappear from the quotient Laplacian.

The resulting pushforward transports explicit chip-firing witnesses from the
source to the target.  It does **not** assert that arbitrary divisor rank is
preserved by contraction.
-/

namespace Utilities.Certificate

open Finset

universe u v w

/-- Passive data for a graph quotient/contraction.  The validity predicate,
rather than the data structure, records the quotient equations. -/
structure GraphContractionCertificate (G : CFGraph.{u}) (H : CFGraph.{v}) where
  vertexMap : G.V → H.V

namespace GraphContractionCertificate

variable {G : CFGraph.{u}} {H : CFGraph.{v}}

/-- Reindex the source of a contraction certificate along a checked
Laplacian-preserving relabeling.  The quotient target is left unchanged.

This is a change of names on source vertices, not a rank-transport claim
through a contraction. -/
def precomposeLaplacianEquiv {G' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv G' G) :
    GraphContractionCertificate G' H where
  vertexMap := c.vertexMap ∘ equivalence

@[simp] theorem precomposeLaplacianEquiv_vertexMap
    {G' : CFGraph.{w}} (c : GraphContractionCertificate G H)
    (equivalence : LaplacianEquiv G' G) (x : G'.V) :
    (c.precomposeLaplacianEquiv equivalence).vertexMap x =
      c.vertexMap (equivalence x) := rfl

/-- Reindex the target of a contraction certificate along a checked
Laplacian-preserving relabeling.  This only changes the names of quotient
vertices; it is not a claim that rank descends through a contraction. -/
def postcomposeLaplacianEquiv {H' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv H H') :
    GraphContractionCertificate G H' where
  vertexMap := equivalence ∘ c.vertexMap

@[simp] theorem postcomposeLaplacianEquiv_vertexMap
    {H' : CFGraph.{w}} (c : GraphContractionCertificate G H)
    (equivalence : LaplacianEquiv H H') (x : G.V) :
    (c.postcomposeLaplacianEquiv equivalence).vertexMap x =
      equivalence (c.vertexMap x) := rfl

/-- The exact quotient condition.  It is imposed only for distinct target
vertices: source edges internal to one fibre are precisely the edges which
are contracted, so no equation is required on the diagonal. -/
def Valid (c : GraphContractionCertificate G H) : Prop :=
  Function.Surjective c.vertexMap ∧
  ∀ a b : H.V, a ≠ b →
    numEdges H a b =
      ∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x = a ∧ c.vertexMap y = b then numEdges G x y else 0

/-- Validity is invariant under a checked reindexing of the source graph.
The proof uses the vertex equivalence twice to reindex the two source sums;
edge multiplicities are then exactly `LaplacianEquiv.num_edges_eq`. -/
theorem valid_precomposeLaplacianEquiv {G' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv G' G)
    (hValid : c.Valid) :
    (c.precomposeLaplacianEquiv equivalence).Valid := by
  classical
  constructor
  · intro b
    obtain ⟨x, hx⟩ := hValid.1 b
    refine ⟨equivalence.toEquiv.symm x, ?_⟩
    simpa [precomposeLaplacianEquiv] using hx
  · intro a b hab
    rw [hValid.2 a b hab]
    apply Fintype.sum_equiv equivalence.toEquiv.symm
    intro x
    apply Fintype.sum_equiv equivalence.toEquiv.symm
    intro y
    rw [← equivalence.num_edges_eq]
    simp [precomposeLaplacianEquiv]

/-- Validity is invariant under a checked relabeling of the quotient target.
The source fibres are unchanged; the proof only rewrites their two target
labels through the vertex equivalence. -/
theorem valid_postcomposeLaplacianEquiv {H' : CFGraph.{w}}
    (c : GraphContractionCertificate G H) (equivalence : LaplacianEquiv H H')
    (hValid : c.Valid) :
    (c.postcomposeLaplacianEquiv equivalence).Valid := by
  classical
  constructor
  · intro target
    obtain ⟨source, hSource⟩ := hValid.1 (equivalence.toEquiv.symm target)
    refine ⟨source, ?_⟩
    simpa [postcomposeLaplacianEquiv] using congrArg equivalence hSource
  · intro a b hDistinct
    have hDistinctPreimage : equivalence.toEquiv.symm a ≠ equivalence.toEquiv.symm b := by
      intro hEqual
      apply hDistinct
      exact equivalence.toEquiv.symm.injective hEqual
    calc
      numEdges H' a b =
          numEdges H' (equivalence (equivalence.toEquiv.symm a))
            (equivalence (equivalence.toEquiv.symm b)) := by simp
      _ = numEdges H (equivalence.toEquiv.symm a) (equivalence.toEquiv.symm b) :=
        equivalence.num_edges_eq _ _
      _ = ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = equivalence.toEquiv.symm a ∧
              c.vertexMap y = equivalence.toEquiv.symm b then numEdges G x y else 0 :=
        hValid.2 _ _ hDistinctPreimage
      _ = ∑ x : G.V, ∑ y : G.V,
          if (c.postcomposeLaplacianEquiv equivalence).vertexMap x = a ∧
              (c.postcomposeLaplacianEquiv equivalence).vertexMap y = b then
            numEdges G x y else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        have hx : c.vertexMap x = equivalence.toEquiv.symm a ↔
            equivalence (c.vertexMap x) = a := by
          constructor
          · intro h
            rw [h]
            exact equivalence.toEquiv.apply_symm_apply a
          · intro h
            apply equivalence.toEquiv.injective
            rw [h]
            exact (equivalence.toEquiv.apply_symm_apply a).symm
        have hy : c.vertexMap y = equivalence.toEquiv.symm b ↔
            equivalence (c.vertexMap y) = b := by
          constructor
          · intro h
            rw [h]
            exact equivalence.toEquiv.apply_symm_apply b
          · intro h
            apply equivalence.toEquiv.injective
            rw [h]
            exact (equivalence.toEquiv.apply_symm_apply b).symm
        simp only [postcomposeLaplacianEquiv_vertexMap, hx, hy]
        rfl

/-- Boolean replay of the finite quotient conditions. -/
def check (c : GraphContractionCertificate G H) : Bool :=
  (@decide (Function.Surjective c.vertexMap)
    Fintype.decidableForallFintype) &&
  (@decide (∀ p : H.V × H.V, p.1 ≠ p.2 →
    numEdges H p.1 p.2 =
      ∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x = p.1 ∧ c.vertexMap y = p.2 then numEdges G x y else 0)
    Fintype.decidableForallFintype)
@[simp] theorem check_eq_true_iff (c : GraphContractionCertificate G H) :
    c.check = true ↔ c.Valid := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, Valid, Prod.forall]
  exact and_congr (@decide_eq_true_eq (Function.Surjective c.vertexMap) _).to_iff Iff.rfl

/-- Push a divisor forward by summing it over fibres. -/
def pushDiv (c : GraphContractionCertificate G H) (D : CFDiv G) : CFDiv H :=
  fun b => ∑ x : G.V, if c.vertexMap x = b then D x else 0

/-- Pull a firing script back by composition with the quotient map. -/
def pullScript (c : GraphContractionCertificate G H)
    (tau : firingScript H) : firingScript G :=
  fun x => tau (c.vertexMap x)

@[simp] theorem pushDiv_apply (c : GraphContractionCertificate G H)
    (D : CFDiv G) (b : H.V) :
    c.pushDiv D b = ∑ x : G.V, if c.vertexMap x = b then D x else 0 := rfl

@[simp] theorem pullScript_apply (c : GraphContractionCertificate G H)
    (tau : firingScript H) (x : G.V) :
    c.pullScript tau x = tau (c.vertexMap x) := rfl

@[simp] theorem pushDiv_zero (c : GraphContractionCertificate G H) :
    c.pushDiv (0 : CFDiv G) = 0 := by
  funext b
  simp [pushDiv]

@[simp] theorem pushDiv_add (c : GraphContractionCertificate G H)
    (D E : CFDiv G) :
    c.pushDiv (D + E) = c.pushDiv D + c.pushDiv E := by
  funext b
  simp only [pushDiv, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : c.vertexMap x = b <;> simp [hx]

@[simp] theorem pushDiv_sub (c : GraphContractionCertificate G H)
    (D E : CFDiv G) :
    c.pushDiv (D - E) = c.pushDiv D - c.pushDiv E := by
  funext b
  simp only [pushDiv, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : c.vertexMap x = b <;> simp [hx]

/-- Fibre summation sends one chip to the one chip at its image. -/
@[simp] theorem pushDiv_one_chip (c : GraphContractionCertificate G H)
    (x : G.V) :
    c.pushDiv (oneChip x) = oneChip (c.vertexMap x) := by
  funext b
  by_cases hb : c.vertexMap x = b
  · subst b
    rw [pushDiv]
    rw [Finset.sum_eq_single x]
    · simp [oneChip]
    · intro y _ hy
      simp [oneChip, hy]
    · simp
  · have hbx : b ≠ c.vertexMap x := Ne.symm hb
    rw [pushDiv]
    simp only [oneChip, if_neg hbx]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : y = x
    · subst y
      simp [hb]
    · simp [hy]

/-- Fibre summation preserves effectivity. -/
theorem effective_pushDiv (c : GraphContractionCertificate G H)
    {D : CFDiv G} (hD : effective D) :
    effective (c.pushDiv D) := by
  intro b
  simp only [pushDiv]
  apply Finset.sum_nonneg
  intro x _
  by_cases hx : c.vertexMap x = b <;> simp [hx, hD x]

/-- Summing a function over all target fibres returns the original total. -/
private theorem sum_fibres (c : GraphContractionCertificate G H)
    (f : G.V → ℤ) :
    (∑ b : H.V, ∑ x : G.V,
      if c.vertexMap x = b then f x else 0) = ∑ x : G.V, f x := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

/-- Fibre summation preserves total degree. -/
@[simp] theorem deg_pushDiv (c : GraphContractionCertificate G H)
    (D : CFDiv G) :
    deg (c.pushDiv D) = deg D := by
  change (∑ b : H.V, ∑ x : G.V,
    if c.vertexMap x = b then D x else 0) = ∑ x : G.V, D x
  exact c.sum_fibres D

/-- The same fibre partition, in the orientation used to group a source sum
by the image of its summation variable. -/
private theorem sum_by_target (c : GraphContractionCertificate G H)
    (f : G.V → ℤ) :
    (∑ x : G.V, f x) =
      ∑ b : H.V, ∑ x : G.V,
        if c.vertexMap x = b then f x else 0 :=
  (c.sum_fibres f).symm

/-- The off-diagonal quotient equation after casting multiplicities to
integers. -/
private theorem edgeMultiplicity_int (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (a b : H.V) (hab : a ≠ b) :
    (numEdges H a b : ℤ) =
      ∑ x : G.V, ∑ y : G.V,
        if c.vertexMap x = a ∧ c.vertexMap y = b then
          (numEdges G x y : ℤ) else 0 := by
  exact_mod_cast hValid.2 a b hab

/-- A weighted version of the quotient equation.  On the diagonal the
coefficient vanishes, which is exactly why the certificate need not constrain
contracted internal edges. -/
private theorem weighted_edgeMultiplicity (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (b : H.V) (tau : firingScript H) :
    (∑ a : H.V, (tau a - tau b) * (numEdges H b a : ℤ)) =
      ∑ a : H.V, (tau a - tau b) *
        (∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = b ∧ c.vertexMap y = a then
            (numEdges G x y : ℤ) else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : a = b
  · subst a
    simp
  · rw [c.edgeMultiplicity_int hValid b a (Ne.symm h)]

/-- The quotient Laplacian identity.  Only pulled-back scripts are claimed to
commute with contraction; this is the precise amount of compatibility needed
to push explicit reachability certificates forward. -/
theorem pushDiv_prin_pullScript (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (tau : firingScript H) :
    c.pushDiv (prin G (c.pullScript tau)) = prin H tau := by
  funext b
  change
    (∑ x : G.V, if c.vertexMap x = b then
      (∑ y : G.V,
        (tau (c.vertexMap y) - tau (c.vertexMap x)) *
          (numEdges G x y : ℤ)) else 0) =
      ∑ a : H.V, (tau a - tau b) * (numEdges H b a : ℤ)
  calc
    (∑ x : G.V, if c.vertexMap x = b then
      (∑ y : G.V,
        (tau (c.vertexMap y) - tau (c.vertexMap x)) *
          (numEdges G x y : ℤ)) else 0) =
        ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = b then
            (tau (c.vertexMap y) - tau b) * (numEdges G x y : ℤ) else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          by_cases hx : c.vertexMap x = b <;> simp [hx]
    _ = ∑ x : G.V, ∑ a : H.V, ∑ y : G.V,
          if c.vertexMap y = a then
            if c.vertexMap x = b then
              (tau a - tau b) * (numEdges G x y : ℤ) else 0
          else 0 := by
          apply Finset.sum_congr rfl
          intro x _
          rw [c.sum_by_target]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro y _
          by_cases hy : c.vertexMap y = a <;> simp [hy]
    _ = ∑ a : H.V, ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = b ∧ c.vertexMap y = a then
            (tau a - tau b) * (numEdges G x y : ℤ) else 0 := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro x _
          apply Finset.sum_congr rfl
          intro y _
          by_cases hx : c.vertexMap x = b <;>
            by_cases hy : c.vertexMap y = a <;> simp [hx, hy]
    _ = ∑ a : H.V, (tau a - tau b) *
          (∑ x : G.V, ∑ y : G.V,
            if c.vertexMap x = b ∧ c.vertexMap y = a then
              (numEdges G x y : ℤ) else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          symm
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro y _
          by_cases hxy : c.vertexMap x = b ∧ c.vertexMap y = a <;>
            simp [hxy]
    _ = ∑ a : H.V, (tau a - tau b) * (numEdges H b a : ℤ) :=
          (c.weighted_edgeMultiplicity hValid b tau).symm

/-- An explicit source winnability witness whose script is pulled back from
the target.  This is the reusable certificate-level notion: it is stronger
than merely being winnable on `G`, and therefore has a sound quotient image. -/
def PushableWinnable (c : GraphContractionCertificate G H) (X : CFDiv G) : Prop :=
  ∃ tau : firingScript H,
    effective (X + prin G (c.pullScript tau))

/-- A pulled-back source witness pushes to an ordinary winnability witness on
the quotient. -/
theorem winnable_pushDiv_of_pushableWinnable
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    {X : CFDiv G} (hX : c.PushableWinnable X) :
    winnable H (c.pushDiv X) := by
  obtain ⟨tau, hEffective⟩ := hX
  rw [winnable_iff_exists_effective]
  refine ⟨c.pushDiv X + prin H tau, ?_,
    StrongSeparator.linearEquiv_add_prin (c.pushDiv X) tau⟩
  rw [← c.pushDiv_prin_pullScript hValid tau, ← c.pushDiv_add]
  exact c.effective_pushDiv hEffective

/-- The source divisor reaches `x` by a script that descends to the quotient.
The definition deliberately retains the source representative: different
vertices of one contracted fibre may have different source witnesses. -/
def PushableReaches (c : GraphContractionCertificate G H)
    (D : CFDiv G) (x : G.V) : Prop :=
  c.PushableWinnable (D - oneChip x)

/-- A fibre-wise certificate: every chosen target fibre has one source
representative with a pushable removed-chip witness.  This is the minimal
condition needed for rank one on the quotient. -/
def PushableReachabilityAtRepresentatives
    (c : GraphContractionCertificate G H) (D : CFDiv G) : Prop :=
  ∀ b : H.V, ∃ x : G.V,
    c.vertexMap x = b ∧ c.PushableReaches D x

/-- A stronger, fibre-constant form useful when certificates are generated by
one rule per target fibre rather than by a selected representative. -/
def FibreConstantPushableReachability
    (c : GraphContractionCertificate G H) (D : CFDiv G) : Prop :=
  ∀ b : H.V, ∀ x : G.V,
    c.vertexMap x = b → c.PushableReaches D x

theorem pushableReachabilityAtRepresentatives_of_fibreConstant
    (c : GraphContractionCertificate G H) (hValid : c.Valid) (D : CFDiv G)
    (hFibre : c.FibreConstantPushableReachability D) :
    c.PushableReachabilityAtRepresentatives D := by
  intro b
  obtain ⟨x, hx⟩ := hValid.1 b
  exact ⟨x, hx, hFibre b x hx⟩

/-- A pushable removed-chip witness at `x` proves reachability at its quotient
vertex. -/
theorem reaches_pushDiv_of_pushableReaches
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    {D : CFDiv G} {x : G.V} (hReach : c.PushableReaches D x) :
    StrongSeparator.Reaches H (c.pushDiv D) (c.vertexMap x) := by
  unfold StrongSeparator.Reaches
  unfold PushableReaches at hReach
  have hWin := c.winnable_pushDiv_of_pushableWinnable hValid hReach
  simpa only [pushDiv_sub, pushDiv_one_chip] using hWin

/-- Reachability at representatives gives reachability at every target
vertex after contraction. -/
theorem reaches_all_pushDiv_of_pushableRepresentatives
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    {D : CFDiv G} (hReach : c.PushableReachabilityAtRepresentatives D) :
    ∀ b : H.V, StrongSeparator.Reaches H (c.pushDiv D) b := by
  intro b
  obtain ⟨x, hx, hPushable⟩ := hReach b
  simpa [hx] using c.reaches_pushDiv_of_pushableReaches hValid hPushable

/-- Reaching every vertex is exactly the rank-one test, spelled out here so
the contraction interface has no hidden dependence on a rank-preservation
claim. -/
theorem rank_ge_one_of_reaches_all {K : CFGraph} {D : CFDiv K}
    (hReach : ∀ q : K.V, StrongSeparator.Reaches K D q) :
    rank K D ≥ 1 := by
  apply (rank_geq_iff K D 1).mp
  intro E hE
  obtain ⟨q, hq⟩ := effective_degree_one_eq_one_chip hE.1 hE.2
  rw [hq]
  exact hReach q

/-- Rank one on the quotient from pushable source reachability at target
representatives. -/
theorem rank_ge_one_pushDiv_of_pushableRepresentatives
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    {D : CFDiv G} (hReach : c.PushableReachabilityAtRepresentatives D) :
    rank H (c.pushDiv D) ≥ 1 :=
  rank_ge_one_of_reaches_all
    (c.reaches_all_pushDiv_of_pushableRepresentatives hValid hReach)

/-- A compact one-way Brill--Noether package for quotient certificates. -/
theorem bnExists_pushDiv_of_pushableRepresentatives
    (c : GraphContractionCertificate G H) (hValid : c.Valid)
    (D : CFDiv G) (d : ℤ) (hDegree : deg D = d)
    (hReach : c.PushableReachabilityAtRepresentatives D) :
    BNExists H 1 d :=
  ⟨c.pushDiv D, (c.deg_pushDiv D).trans hDegree,
    c.rank_ge_one_pushDiv_of_pushableRepresentatives hValid hReach⟩

/-- A valid surjective contraction carries connected graphs to connected
graphs.  The proof pulls a target cut back to the full preimage cut in the
source; a source crossing edge contributes a positive summand to the exact
off-diagonal fibre-multiplicity equation. -/
theorem graphConnected (c : GraphContractionCertificate G H)
    (hValid : c.Valid) (hConnected : graphConnected G) :
    graphConnected H := by
  classical
  intro S hSplit
  let pulled : Finset G.V := Finset.univ.filter fun x => c.vertexMap x ∈ S
  obtain ⟨a, b, ha, hb⟩ := hSplit
  obtain ⟨x, hx⟩ := hValid.1 a
  obtain ⟨y, hy⟩ := hValid.1 b
  have hPulledSplit : ∃ p q : G.V, p ∈ pulled ∧ q ∉ pulled := by
    refine ⟨x, y, ?_, ?_⟩
    · simpa [pulled, hx] using ha
    · simpa [pulled, hy] using hb
  obtain ⟨p, hp, q, hq, hpq⟩ := hConnected pulled hPulledSplit
  refine ⟨c.vertexMap p, ?_, c.vertexMap q, ?_, ?_⟩
  · simpa [pulled] using hp
  · simpa [pulled] using hq
  · have hpS : c.vertexMap p ∈ S := by simpa [pulled] using hp
    have hqS : c.vertexMap q ∉ S := by simpa [pulled] using hq
    have hpqImage : c.vertexMap p ≠ c.vertexMap q := by
      intro h
      exact hqS (h ▸ hpS)
    rw [hValid.2 (c.vertexMap p) (c.vertexMap q) hpqImage]
    have hleInner : numEdges G p q ≤
        ∑ y : G.V,
          if c.vertexMap p = c.vertexMap p ∧ c.vertexMap y = c.vertexMap q then
            numEdges G p y else 0 := by
      have hSingle := Finset.single_le_sum
        (fun z _ => Nat.zero_le _)
        (Finset.mem_univ q)
        (s := Finset.univ)
        (f := fun y : G.V =>
          if c.vertexMap p = c.vertexMap p ∧ c.vertexMap y = c.vertexMap q then
            numEdges G p y else 0)
      simpa using hSingle
    have hle : numEdges G p q ≤
        ∑ x : G.V, ∑ y : G.V,
          if c.vertexMap x = c.vertexMap p ∧ c.vertexMap y = c.vertexMap q then
            numEdges G x y else 0 := by
      calc
        numEdges G p q ≤ ∑ y : G.V,
            if c.vertexMap p = c.vertexMap p ∧ c.vertexMap y = c.vertexMap q then
              numEdges G p y else 0 := hleInner
        _ ≤ ∑ x : G.V, ∑ y : G.V,
            if c.vertexMap x = c.vertexMap p ∧ c.vertexMap y = c.vertexMap q then
              numEdges G x y else 0 := by
              have hSingle := Finset.single_le_sum
                (fun z _ => Finset.sum_nonneg fun y _ => Nat.zero_le _)
                (Finset.mem_univ p)
                (s := Finset.univ)
                (f := fun x : G.V => ∑ y : G.V,
                  if c.vertexMap x = c.vertexMap p ∧
                      c.vertexMap y = c.vertexMap q then
                    numEdges G x y else 0)
              simpa using hSingle
    exact lt_of_lt_of_le hpq hle

end GraphContractionCertificate

end Utilities.Certificate
