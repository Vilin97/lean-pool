/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContraction
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.SeparatingEdgeCut
import LeanPool.BrillNoetherGraphs.Utilities.Gluing.SeparatingEdgePath
import Mathlib.Tactic

/-!
# The fossil of a chip-firing graph

In this library, **fossil** is a deliberately short name for the graph's
degree-one Abel--Jacobi image.  For a connected graph this is the construction
usually called its **2-edge-connectivization**: contract every separating edge,
map the remaining edge occurrences across the quotient, and discard the loops
created by contraction.  “Fossil” is local terminology, not a replacement for
either standard name in mathematical prose.

Concretely, two vertices have the same fossil image when their one-chip
divisors are linearly equivalent.

This module begins with the quotient construction and its canonical divisor
pushforward.  The main objective is to prove that this pushforward identifies
the divisor class groups, hence preserves winnability, rank, and
Brill--Noether existence.  Unlike a chosen sequence of bridge contractions,
the fossil is canonical and can therefore serve as a common target for
constructions which differ only by attached trees.
-/

namespace Utilities

open Finset

universe u

/-! ## Vertex classes and the quotient graph -/

/-- Two vertices belong to the same fossil class when their one-chip
divisors are linearly equivalent. -/
def chipEquivalent (G : CFGraph.{u}) (v w : G.V) : Prop :=
  linearEquiv G (oneChip v) (oneChip w)

/-- Linear equivalence of one-chip divisors, packaged as a setoid. -/
def chipSetoid (G : CFGraph.{u}) : Setoid G.V where
  r := chipEquivalent G
  iseqv := by
    constructor
    · intro v
      exact linearEquiv.refl G (oneChip v)
    · intro v w h
      exact linearEquiv.symm h
    · intro v w z hvw hwz
      exact linearEquiv.trans hvw hwz

/-- A vertex of the fossil is a linear-equivalence class of vertices. -/
abbrev FossilVertex (G : CFGraph.{u}) := Quotient (chipSetoid G)

/-- The canonical map from the original vertex set to its fossil classes. -/
def fossilVertex (G : CFGraph.{u}) (v : G.V) : FossilVertex G :=
  Quotient.mk (chipSetoid G) v

instance fossilVertexNonempty (G : CFGraph.{u}) :
    Nonempty (FossilVertex G) :=
  ⟨fossilVertex G (Classical.choice (inferInstance : Nonempty G.V))⟩

noncomputable instance fossilVertexDecidableEq (G : CFGraph.{u}) :
    DecidableEq (FossilVertex G) := Classical.decEq _

noncomputable instance fossilVertexFintype (G : CFGraph.{u}) :
    Fintype (FossilVertex G) := Fintype.ofFinite _

@[simp] theorem fossilVertex_eq_iff (G : CFGraph.{u}) (v w : G.V) :
    fossilVertex G v = fossilVertex G w ↔ chipEquivalent G v w := by
  exact Quotient.eq

/-- Map the two endpoints of an edge to their fossil classes. -/
def fossilEdge (G : CFGraph.{u}) (edge : G.V × G.V) :
    FossilVertex G × FossilVertex G :=
  (fossilVertex G edge.1, fossilVertex G edge.2)

/-- The fossil of `G`: its degree-one Abel--Jacobi image, equivalently (when
`G` is connected) its 2-edge-connectivization.  It quotients vertices by
one-chip divisor class and discards edge occurrences that become loops. -/
noncomputable def fossil (G : CFGraph.{u}) : CFGraph.{u} where
  V := FossilVertex G
  instDecidableEq := fossilVertexDecidableEq G
  instFintype := fossilVertexFintype G
  instNonempty := inferInstance
  edges := (G.edges.map (fossilEdge G)).filter fun edge => edge.1 ≠ edge.2
  loopless := by
    intro v hv
    exact (Multiset.mem_filter.mp hv).2 rfl

@[simp] theorem fossil_edges (G : CFGraph.{u}) :
    (fossil G).edges =
      (G.edges.map (fossilEdge G)).filter fun edge => edge.1 ≠ edge.2 := rfl

/-! ## Canonical contraction and divisor pushforward -/

/-- The quotient map, viewed as a graph-contraction certificate. -/
noncomputable def fossilContraction (G : CFGraph.{u}) :
    Certificate.GraphContractionCertificate G (fossil G) where
  vertexMap := fossilVertex G

@[simp] theorem fossilContraction_vertexMap (G : CFGraph.{u}) (v : G.V) :
    (fossilContraction G).vertexMap v = fossilVertex G v := rfl

private theorem sum_single_edge_between_fibres
    {V Q : Type*} [Fintype V] [DecidableEq V] [DecidableEq Q]
    (f : V → Q) (left right : V) (a b : Q) (hab : a ≠ b) :
    (∑ x : V, ∑ y : V,
      if f x = a ∧ f y = b then
        if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0
      else 0) =
        if (f left = a ∧ f right = b) ∨
            (f right = a ∧ f left = b) then 1 else 0 := by
  by_cases h₁ : f left = a ∧ f right = b
  · rcases h₁ with ⟨hl, hr⟩
    have h₂ : ¬(f right = a ∧ f left = b) := by
      rintro ⟨hr', hl'⟩
      exact hab (hl.symm.trans hl')
    have hZero (x y : V) (hxy : x ≠ left ∨ y ≠ right) :
        (if f x = a ∧ f y = b then
          if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0
        else 0) = 0 := by
      by_cases hf : f x = a ∧ f y = b
      · by_cases he : (left, right) = (x, y) ∨ (left, right) = (y, x)
        · rcases he with he | he
          · have hx : x = left := (congrArg Prod.fst he).symm
            have hy : y = right := (congrArg Prod.snd he).symm
            exact (hxy.elim (fun h => h hx) (fun h => h hy)).elim
          · have hx : x = right := (congrArg Prod.snd he).symm
            have hy : y = left := (congrArg Prod.fst he).symm
            exact (h₂ ⟨by simpa [hx] using hf.1, by simpa [hy] using hf.2⟩).elim
        · rw [if_pos hf, if_neg he]
      · simp [hf]
    have hCross :
        (f left = a ∧ f right = b) ∨ (f right = a ∧ f left = b) :=
      Or.inl ⟨hl, hr⟩
    rw [if_pos hCross]
    rw [Finset.sum_eq_single left]
    · rw [Finset.sum_eq_single right]
      · simp [hl, hr]
      · intro y _ hy
        exact hZero left y (Or.inr hy)
      · simp
    · intro x _ hx
      apply Finset.sum_eq_zero
      intro y _
      exact hZero x y (Or.inl hx)
    · simp
  · by_cases h₂ : f right = a ∧ f left = b
    · rcases h₂ with ⟨hr, hl⟩
      have hZero (x y : V) (hxy : x ≠ right ∨ y ≠ left) :
          (if f x = a ∧ f y = b then
            if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0
          else 0) = 0 := by
        by_cases hf : f x = a ∧ f y = b
        · by_cases he : (left, right) = (x, y) ∨ (left, right) = (y, x)
          · rcases he with he | he
            · have hx : x = left := (congrArg Prod.fst he).symm
              have hy : y = right := (congrArg Prod.snd he).symm
              exact (h₁ ⟨by simpa [hx] using hf.1, by simpa [hy] using hf.2⟩).elim
            · have hx : x = right := (congrArg Prod.snd he).symm
              have hy : y = left := (congrArg Prod.fst he).symm
              exact (hxy.elim (fun h => h hx) (fun h => h hy)).elim
          · rw [if_pos hf, if_neg he]
        · simp [hf]
      have hCross :
          (f left = a ∧ f right = b) ∨ (f right = a ∧ f left = b) :=
        Or.inr ⟨hr, hl⟩
      rw [if_pos hCross]
      rw [Finset.sum_eq_single right]
      · rw [Finset.sum_eq_single left]
        · simp [hl, hr]
        · intro y _ hy
          exact hZero right y (Or.inr hy)
        · simp
      · intro x _ hx
        apply Finset.sum_eq_zero
        intro y _
        exact hZero x y (Or.inl hx)
      · simp
    · have hZero (x y : V) :
          (if f x = a ∧ f y = b then
            if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0
          else 0) = 0 := by
        by_cases hf : f x = a ∧ f y = b
        · by_cases he : (left, right) = (x, y) ∨ (left, right) = (y, x)
          · rcases he with he | he
            · have hx : x = left := (congrArg Prod.fst he).symm
              have hy : y = right := (congrArg Prod.snd he).symm
              exact (h₁ ⟨by simpa [hx] using hf.1, by simpa [hy] using hf.2⟩).elim
            · have hx : x = right := (congrArg Prod.snd he).symm
              have hy : y = left := (congrArg Prod.fst he).symm
              exact (h₂ ⟨by simpa [hx] using hf.1, by simpa [hy] using hf.2⟩).elim
          · rw [if_pos hf, if_neg he]
        · simp [hf]
      have hNoCross :
          ¬((f left = a ∧ f right = b) ∨ (f right = a ∧ f left = b)) :=
        not_or_intro h₁ h₂
      rw [if_neg hNoCross]
      apply Finset.sum_eq_zero
      intro x _
      apply Finset.sum_eq_zero
      intro y _
      exact hZero x y

private theorem mapped_edge_count_eq_fibre_sum
    {V Q : Type*} [Fintype V] [DecidableEq V] [DecidableEq Q]
    (edges : Multiset (V × V)) (f : V → Q) (a b : Q) (hab : a ≠ b) :
    (((edges.map fun edge => (f edge.1, f edge.2)).filter
        fun edge => edge.1 ≠ edge.2).filter
          fun edge => edge = (a, b) ∨ edge = (b, a)).card =
      ∑ x : V, ∑ y : V,
        if f x = a ∧ f y = b then
          (edges.filter fun edge => edge = (x, y) ∨ edge = (y, x)).card
        else 0 := by
  induction edges using Multiset.induction_on with
  | empty => simp
  | cons edge edges ih =>
      rcases edge with ⟨left, right⟩
      rw [Multiset.map_cons, Multiset.filter_cons, Multiset.filter_add]
      simp only [Multiset.card_add]
      simp_rw [Multiset.filter_cons]
      simp_rw [Multiset.card_add, apply_ite, Multiset.card_singleton,
        Multiset.card_zero]
      have hSplit (x y : V) :
          (if f x = a ∧ f y = b then
              (if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0) +
                (edges.filter fun edge => edge = (x, y) ∨ edge = (y, x)).card
            else 0) =
            (if f x = a ∧ f y = b then
              if (left, right) = (x, y) ∨ (left, right) = (y, x) then 1 else 0
            else 0) +
            (if f x = a ∧ f y = b then
              (edges.filter fun edge => edge = (x, y) ∨ edge = (y, x)).card
            else 0) := by
        by_cases h : f x = a ∧ f y = b <;> simp [h]
      simp_rw [hSplit]
      simp_rw [Finset.sum_add_distrib]
      rw [ih]
      have hIncrement := sum_single_edge_between_fibres f left right a b hab
      rw [hIncrement]
      by_cases hloop : f left = f right
      · have hNoCross :
          ¬((f left = a ∧ f right = b) ∨ (f right = a ∧ f left = b)) := by
          rintro (h | h)
          · exact hab (h.1.symm.trans (hloop.trans h.2))
          · exact hab (h.1.symm.trans (hloop.symm.trans h.2))
        rw [if_neg (by simpa using hloop), if_neg hNoCross]
        rfl
      · have hPairCross :
            ((f left, f right) = (a, b) ∨ (f left, f right) = (b, a)) ↔
              ((f left = a ∧ f right = b) ∨
                (f right = a ∧ f left = b)) := by
          simp [Prod.ext_iff, and_comm]
        by_cases hCross :
            (f left = a ∧ f right = b) ∨ (f right = a ∧ f left = b)
        · have hPair := hPairCross.mpr hCross
          rw [if_pos hloop, if_pos hCross]
          rw [Multiset.filter_singleton, if_pos hPair]
          rfl
        · have hPair :
              ¬((f left, f right) = (a, b) ∨
                (f left, f right) = (b, a)) :=
            fun h => hCross (hPairCross.mp h)
          rw [if_pos hloop, if_neg hCross]
          rw [Multiset.filter_singleton, if_neg hPair]
          rfl

/-- The fossil really is the quotient graph associated to its vertex map:
between two distinct classes its multiplicity is the sum of all source
multiplicities between the two fibres. -/
theorem fossilContraction_valid (G : CFGraph.{u}) :
    (fossilContraction G).Valid := by
  classical
  constructor
  · intro q
    induction q using Quotient.inductionOn with
    | _ v => exact ⟨v, rfl⟩
  · intro a b hab
    change
      ((((G.edges.map fun edge =>
          (fossilVertex G edge.1, fossilVertex G edge.2)).filter
            fun edge => edge.1 ≠ edge.2).filter
              fun edge => edge = (a, b) ∨ edge = (b, a)).card) =
        ∑ x : G.V, ∑ y : G.V,
          if fossilVertex G x = a ∧ fossilVertex G y = b then
            (G.edges.filter fun edge =>
              edge = (x, y) ∨ edge = (y, x)).card
          else 0
    exact mapped_edge_count_eq_fibre_sum G.edges (fossilVertex G) a b hab

/-- Push a divisor to the fossil by summing its coefficients over each
linear-equivalence class of vertices. -/
noncomputable def fossilPushforward (G : CFGraph.{u}) (D : CFDiv G) :
    CFDiv (fossil G) :=
  (fossilContraction G).pushDiv D

@[simp] theorem fossilPushforward_apply (G : CFGraph.{u}) (D : CFDiv G)
    (q : FossilVertex G) :
    fossilPushforward G D q =
      ∑ v : G.V, if fossilVertex G v = q then D v else 0 := rfl

@[simp] theorem fossilPushforward_zero (G : CFGraph.{u}) :
    fossilPushforward G (0 : CFDiv G) = 0 := by
  exact (fossilContraction G).pushDiv_zero

@[simp] theorem fossilPushforward_add (G : CFGraph.{u}) (D E : CFDiv G) :
    fossilPushforward G (D + E) =
      fossilPushforward G D + fossilPushforward G E := by
  exact (fossilContraction G).pushDiv_add D E

@[simp] theorem fossilPushforward_sub (G : CFGraph.{u}) (D E : CFDiv G) :
    fossilPushforward G (D - E) =
      fossilPushforward G D - fossilPushforward G E := by
  exact (fossilContraction G).pushDiv_sub D E

@[simp] theorem fossilPushforward_one_chip (G : CFGraph.{u}) (v : G.V) :
    fossilPushforward G (oneChip v) = oneChip (fossilVertex G v) := by
  exact (fossilContraction G).pushDiv_one_chip v

theorem effective_fossilPushforward (G : CFGraph.{u}) {D : CFDiv G}
    (hD : effective D) : effective (fossilPushforward G D) :=
  (fossilContraction G).effective_pushDiv hD

@[simp] theorem deg_fossilPushforward (G : CFGraph.{u}) (D : CFDiv G) :
    deg (fossilPushforward G D) = deg D :=
  (fossilContraction G).deg_pushDiv D

/-- Fibre summation, packaged as an additive homomorphism. -/
noncomputable def fossilPushforwardHom (G : CFGraph.{u}) :
    CFDiv G →+ CFDiv (fossil G) where
  toFun := fossilPushforward G
  map_zero' := fossilPushforward_zero G
  map_add' := fossilPushforward_add G

@[simp] theorem fossilPushforwardHom_apply (G : CFGraph.{u}) (D : CFDiv G) :
    fossilPushforwardHom G D = fossilPushforward G D := rfl

@[simp] theorem fossilPushforward_zsmul (G : CFGraph.{u})
    (n : ℤ) (D : CFDiv G) :
    fossilPushforward G (n • D) = n • fossilPushforward G D := by
  exact (fossilPushforwardHom G).map_zsmul n D

/-! ## A canonical section on divisors -/

/-- A noncomputably chosen original vertex in each fossil class.  The
mathematical statements below do not depend on this choice. -/
noncomputable def fossilRepresentative (G : CFGraph.{u})
    (q : FossilVertex G) : G.V :=
  Classical.choose ((fossilContraction_valid G).1 q)

@[simp] theorem fossilVertex_representative (G : CFGraph.{u})
    (q : FossilVertex G) :
    fossilVertex G (fossilRepresentative G q) = q :=
  Classical.choose_spec ((fossilContraction_valid G).1 q)

/-- Every divisor is the coefficient-weighted sum of its one-chip divisors. -/
theorem divisor_eq_sum_smul_oneChip {K : CFGraph.{u}} (D : CFDiv K) :
    D = ∑ v : K.V, D v • oneChip v := by
  classical
  funext w
  simp [oneChip]

/-- Lift a fossil divisor by placing the coefficient of each class at its
chosen representative. -/
noncomputable def fossilLift (G : CFGraph.{u})
    (D : CFDiv (fossil G)) : CFDiv G :=
  ∑ q : FossilVertex G, D q • oneChip (fossilRepresentative G q)

/-- The chosen lift is a right inverse to fibre summation. -/
@[simp] theorem fossilPushforward_lift (G : CFGraph.{u})
    (D : CFDiv (fossil G)) :
    fossilPushforward G (fossilLift G D) = D := by
  classical
  change fossilPushforwardHom G
      (∑ q : FossilVertex G,
        D q • oneChip (fossilRepresentative G q)) = D
  rw [map_sum]
  simp_rw [map_zsmul, fossilPushforwardHom_apply,
    fossilPushforward_one_chip, fossilVertex_representative]
  exact (divisor_eq_sum_smul_oneChip D).symm

/-- Pull a fossil firing script back to the original graph. -/
noncomputable def fossilPullScript (G : CFGraph.{u})
    (tau : firingScript (fossil G)) : firingScript G :=
  (fossilContraction G).pullScript tau

@[simp] theorem fossilPullScript_apply (G : CFGraph.{u})
    (tau : firingScript (fossil G)) (v : G.V) :
    fossilPullScript G tau v = tau (fossilVertex G v) := rfl

/-- The quotient Laplacian identity for the fossil. -/
theorem fossilPushforward_prin_pullScript (G : CFGraph.{u})
    (tau : firingScript (fossil G)) :
    fossilPushforward G (prin G (fossilPullScript G tau)) =
      prin (fossil G) tau :=
  (fossilContraction G).pushDiv_prin_pullScript
    (fossilContraction_valid G) tau

/-! ## The easy half of divisor-class invariance -/

/-- Linear equivalence is preserved by integer scaling. -/
theorem linear_equiv_zsmul {K : CFGraph.{u}} {D E : CFDiv K}
    (h : linearEquiv K D E) (n : ℤ) :
    linearEquiv K (n • D) (n • E) := by
  unfold linearEquiv at h ⊢
  simpa [smul_sub] using (principalDivisors K).zsmul_mem h n

/-- A finite sum of termwise linearly equivalent divisors is linearly
equivalent. -/
theorem linear_equiv_sum {K : CFGraph.{u}} {ι : Type*} [Fintype ι]
    {D E : ι → CFDiv K} (h : ∀ i, linearEquiv K (D i) (E i)) :
    linearEquiv K (∑ i, D i) (∑ i, E i) := by
  classical
  unfold linearEquiv at h ⊢
  rw [← Finset.sum_sub_distrib]
  exact (principalDivisors K).sum_mem (fun i _ => h i)

/-- Each vertex is linearly equivalent, as a one-chip divisor, to the chosen
representative of its fossil class. -/
theorem linear_equiv_one_chip_representative (G : CFGraph.{u}) (v : G.V) :
    linearEquiv G (oneChip v)
      (oneChip (fossilRepresentative G (fossilVertex G v))) := by
  apply (fossilVertex_eq_iff G _ _).mp
  rw [fossilVertex_representative]

private theorem sum_smul_representative_eq_lift_pushforward
    (G : CFGraph.{u}) (D : CFDiv G) :
    (∑ v : G.V, D v •
      oneChip (fossilRepresentative G (fossilVertex G v))) =
        fossilLift G (fossilPushforward G D) := by
  classical
  funext w
  simp only [fossilLift, fossilPushforward_apply, Finset.sum_apply,
    Pi.smul_apply, oneChip]
  simp_rw [Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_eq_single (fossilVertex G v)]
  · simp
  · intro q _ hq
    by_cases hw : w = fossilRepresentative G q
    · rw [if_pos hw, if_neg (Ne.symm hq)]
      simp
    · rw [if_neg hw]
      simp
  · simp

/-- Every divisor is linearly equivalent to the chosen lift of its
pushforward: redistributing chips inside a fossil fibre only moves them
between linearly equivalent vertices. -/
theorem linear_equiv_lift_fossilPushforward (G : CFGraph.{u}) (D : CFDiv G) :
    linearEquiv G D (fossilLift G (fossilPushforward G D)) := by
  conv_lhs => rw [divisor_eq_sum_smul_oneChip D]
  rw [← sum_smul_representative_eq_lift_pushforward G D]
  apply linear_equiv_sum
  intro v
  exact linear_equiv_zsmul (linear_equiv_one_chip_representative G v) (D v)

/-- Divisors with the same fossil pushforward are linearly equivalent.
Their only difference is redistribution inside the quotient fibres. -/
theorem linear_equiv_of_fossilPushforward_eq (G : CFGraph.{u})
    {D E : CFDiv G} (h : fossilPushforward G D = fossilPushforward G E) :
    linearEquiv G D E := by
  apply linearEquiv.trans (linear_equiv_lift_fossilPushforward G D)
  rw [h]
  exact (linear_equiv_lift_fossilPushforward G E).symm

/-- Reflection of linear equivalence through the fossil.  This is the
formal version of pulling a quotient firing script back and observing that
the remaining discrepancy only moves chips inside quotient fibres. -/
theorem linear_equiv_of_fossilPushforward (G : CFGraph.{u})
    {D E : CFDiv G}
    (h : linearEquiv (fossil G)
      (fossilPushforward G D) (fossilPushforward G E)) :
    linearEquiv G D E := by
  unfold linearEquiv at h ⊢
  obtain ⟨tau, hTau⟩ :=
    (principal_iff_eq_prin (fossil G)
      (fossilPushforward G E - fossilPushforward G D)).mp h
  let P : CFDiv G := prin G (fossilPullScript G tau)
  have hPush : fossilPushforward G (E - D) = fossilPushforward G P := by
    calc
      fossilPushforward G (E - D) =
          fossilPushforward G E - fossilPushforward G D :=
        fossilPushforward_sub G E D
      _ = prin (fossil G) tau := hTau
      _ = fossilPushforward G P := by
        symm
        exact fossilPushforward_prin_pullScript G tau
  have hKernel : linearEquiv G (E - D) P :=
    linear_equiv_of_fossilPushforward_eq G hPush
  have hP : P ∈ principalDivisors G := by
    apply (principal_iff_eq_prin G P).mpr
    exact ⟨fossilPullScript G tau, rfl⟩
  have hDifference : P - (E - D) ∈ principalDivisors G := hKernel
  have hRecovered := (principalDivisors G).sub_mem hP hDifference
  convert hRecovered using 1
  abel

/-- The fossil has no further degree-one vertex identifications: two of
its vertices carry equivalent one-chip divisors exactly when they are the
same quotient class. -/
theorem fossil_chipEquivalent_iff_eq (G : CFGraph.{u})
    (q r : (fossil G).V) :
    chipEquivalent (fossil G) q r ↔ q = r := by
  induction q using Quotient.inductionOn with
  | _ v =>
      induction r using Quotient.inductionOn with
      | _ w =>
          constructor
          · intro hEquivalent
            change linearEquiv (fossil G)
              (oneChip (fossilVertex G v))
              (oneChip (fossilVertex G w)) at hEquivalent
            apply (fossilVertex_eq_iff G v w).2
            apply linear_equiv_of_fossilPushforward G
            simpa only [fossilPushforward_one_chip] using hEquivalent
          · intro hEqual
            rw [hEqual]
            exact linearEquiv.refl (fossil G) (oneChip (fossilVertex G w))

/-- Consequently the second fossil quotient has singleton fibres. -/
theorem fossilVertex_fossil_injective (G : CFGraph.{u}) :
    Function.Injective (fossilVertex (fossil G)) := by
  intro q r h
  exact (fossil_chipEquivalent_iff_eq G q r).1
    ((fossilVertex_eq_iff (fossil G) q r).1 h)

/-! ## Script descent and class-group invariance -/

/-- Adding the correcting constant on one side of a separating bridge does
not change the fossil pushforward of the principal divisor. -/
theorem fossilPushforward_prin_normalizeScript (G : CFGraph.{u})
    {x y : G.V} (cut : SeparatingEdgeCut G x y)
    (sigma : firingScript G) :
    fossilPushforward G (prin G (cut.normalizeScript sigma)) =
      fossilPushforward G (prin G sigma) := by
  rw [cut.prin_normalizeScript, fossilPushforward_add,
    fossilPushforward_zsmul, fossilPushforward_sub,
    fossilPushforward_one_chip, fossilPushforward_one_chip]
  have hClass : fossilVertex G x = fossilVertex G y :=
    (fossilVertex_eq_iff G x y).2 cut.chipEquivalent
  rw [hClass, sub_self, smul_zero, add_zero]

/-- Ordered separating-edge pairs on which a script has unequal endpoint
values.  Orienting both ways is harmless and avoids making an arbitrary
orientation part of the API. -/
noncomputable def separatingBadPairs (G : CFGraph.{u})
    (sigma : firingScript G) : Finset (G.V × G.V) := by
  classical
  exact Finset.univ.filter fun pair =>
    Nonempty (SeparatingEdgeCut G pair.1 pair.2) ∧
      sigma pair.1 ≠ sigma pair.2

@[simp] theorem mem_separatingBadPairs_iff (G : CFGraph.{u})
    (sigma : firingScript G) (pair : G.V × G.V) :
    pair ∈ separatingBadPairs G sigma ↔
      Nonempty (SeparatingEdgeCut G pair.1 pair.2) ∧
        sigma pair.1 ≠ sigma pair.2 := by
  classical
  simp [separatingBadPairs]

/-- Repeatedly applying the one-side constant correction produces a script
whose values agree across every separating edge.  The corrections never
destroy an equality already achieved, because separating cuts do not cross;
therefore the finite set of bad endpoint pairs strictly shrinks. -/
theorem exists_separating_normalization (G : CFGraph.{u})
    (sigma : firingScript G) :
    ∃ normalized : firingScript G,
      (∀ {x y : G.V}, (cut : SeparatingEdgeCut G x y) →
        normalized x = normalized y) ∧
      fossilPushforward G (prin G normalized) =
        fossilPushforward G (prin G sigma) := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ rho : firingScript G, (separatingBadPairs G rho).card = n →
      ∃ normalized : firingScript G,
        (∀ {x y : G.V}, (cut : SeparatingEdgeCut G x y) →
          normalized x = normalized y) ∧
        fossilPushforward G (prin G normalized) =
          fossilPushforward G (prin G rho)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro rho hCard
        by_cases hNormalized :
            ∀ {x y : G.V}, (cut : SeparatingEdgeCut G x y) → rho x = rho y
        · exact ⟨rho, hNormalized, rfl⟩
        · push Not at hNormalized
          obtain ⟨x, y, cut, hxy⟩ := hNormalized
          let rho' : firingScript G := cut.normalizeScript rho
          have hSubset : separatingBadPairs G rho' ⊆ separatingBadPairs G rho := by
            intro pair hPair
            rw [mem_separatingBadPairs_iff] at hPair ⊢
            refine ⟨hPair.1, ?_⟩
            intro hOldEqual
            obtain ⟨other⟩ := hPair.1
            exact hPair.2
              (cut.normalizeScript_preserves_endpoints_eq other rho hOldEqual)
          have hOldMem : (x, y) ∈ separatingBadPairs G rho := by
            rw [mem_separatingBadPairs_iff]
            exact ⟨⟨cut⟩, hxy⟩
          have hNewNotMem : (x, y) ∉ separatingBadPairs G rho' := by
            rw [mem_separatingBadPairs_iff]
            intro h
            exact h.2 (cut.normalizeScript_endpoints_eq rho)
          have hStrict : separatingBadPairs G rho' ⊂ separatingBadPairs G rho :=
            Finset.ssubset_iff_subset_ne.mpr ⟨hSubset, by
              intro hEqual
              exact hNewNotMem (hEqual ▸ hOldMem)⟩
          have hSmaller : (separatingBadPairs G rho').card < n := by
            rw [← hCard]
            exact Finset.card_lt_card hStrict
          obtain ⟨normalized, hNormalized', hPush⟩ :=
            ih _ hSmaller rho' rfl
          refine ⟨normalized, hNormalized', hPush.trans ?_⟩
          exact fossilPushforward_prin_normalizeScript G cut rho
  exact hP (separatingBadPairs G sigma).card sigma rfl

/-- On a connected graph, every source firing script can be normalized along
separating-edge cuts so that it is constant on fossil fibres.  Pushing its
principal divisor then gives the principal divisor of the descended script. -/
theorem exists_fossilScript_pushforward_prin (G : CFGraph.{u})
    (hConnected : graphConnected G) (sigma : firingScript G) :
    ∃ tau : firingScript (fossil G),
      fossilPushforward G (prin G sigma) = prin (fossil G) tau := by
  obtain ⟨normalized, hNormalized, hPush⟩ :=
    exists_separating_normalization G sigma
  let tau : firingScript (fossil G) := fun q =>
    normalized (fossilRepresentative G q)
  have hFactor : normalized = fossilPullScript G tau := by
    funext v
    change normalized v = normalized
      (fossilRepresentative G (fossilVertex G v))
    exact eq_of_chipEquivalent_of_separating_normalized
      hConnected normalized hNormalized
      (linear_equiv_one_chip_representative G v)
  refine ⟨tau, ?_⟩
  calc
    fossilPushforward G (prin G sigma) =
        fossilPushforward G (prin G normalized) := hPush.symm
    _ = fossilPushforward G (prin G (fossilPullScript G tau)) := by
      rw [← hFactor]
    _ = prin (fossil G) tau :=
      fossilPushforward_prin_pullScript G tau

/-- Linear equivalence descends to the fossil. -/
theorem linear_equiv_fossilPushforward (G : CFGraph.{u})
    (hConnected : graphConnected G)
    {D E : CFDiv G} (h : linearEquiv G D E) :
    linearEquiv (fossil G)
      (fossilPushforward G D) (fossilPushforward G E) := by
  unfold linearEquiv at h ⊢
  obtain ⟨sigma, hSigma⟩ :=
    (principal_iff_eq_prin G (E - D)).mp h
  obtain ⟨tau, hTau⟩ :=
    exists_fossilScript_pushforward_prin G hConnected sigma
  apply (principal_iff_eq_prin (fossil G)
    (fossilPushforward G E - fossilPushforward G D)).mpr
  refine ⟨tau, ?_⟩
  calc
    fossilPushforward G E - fossilPushforward G D =
        fossilPushforward G (E - D) :=
      (fossilPushforward_sub G E D).symm
    _ = fossilPushforward G (prin G sigma) := congrArg _ hSigma
    _ = prin (fossil G) tau := hTau

/-- On a connected graph, the fossil pushforward identifies divisor classes
exactly. -/
theorem linear_equiv_fossil_iff (G : CFGraph.{u})
    (hConnected : graphConnected G) (D E : CFDiv G) :
    linearEquiv G D E ↔
      linearEquiv (fossil G)
        (fossilPushforward G D) (fossilPushforward G E) :=
  ⟨linear_equiv_fossilPushforward G hConnected,
    linear_equiv_of_fossilPushforward G⟩

/-- Lifting an effective fossil divisor at chosen representatives remains
effective. -/
theorem effective_fossilLift (G : CFGraph.{u})
    {D : CFDiv (fossil G)} (hD : effective D) :
    effective (fossilLift G D) := by
  classical
  intro v
  unfold fossilLift
  simp only [Finset.sum_apply, Pi.smul_apply, oneChip]
  apply Finset.sum_nonneg
  intro q _
  by_cases hv : v = fossilRepresentative G q
  · simp [hv, hD q]
  · simp [hv]

/-- Winnability is invariant under passage to the fossil. -/
theorem winnable_fossil_iff (G : CFGraph.{u})
    (hConnected : graphConnected G) (D : CFDiv G) :
    winnable G D ↔ winnable (fossil G) (fossilPushforward G D) := by
  constructor
  · rintro ⟨E, hEEffective, hDE⟩
    exact ⟨fossilPushforward G E,
      effective_fossilPushforward G hEEffective,
      linear_equiv_fossilPushforward G hConnected hDE⟩
  · rintro ⟨E, hEEffective, hDE⟩
    refine ⟨fossilLift G E, effective_fossilLift G hEEffective, ?_⟩
    exact linearEquiv.trans
      (linear_equiv_lift_fossilPushforward G D)
      (linear_equiv_of_fossilPushforward G (by simpa using hDE))

/-- Every rank inequality is invariant under passage to the fossil. -/
theorem rank_geq_fossil_iff (G : CFGraph.{u})
    (hConnected : graphConnected G) (D : CFDiv G) (k : ℤ) :
    rankGeq G D k ↔ rankGeq (fossil G) (fossilPushforward G D) k := by
  constructor
  · intro hRank E hE
    have hLiftE : fossilLift G E ∈ effOfDegree G k := by
      exact ⟨effective_fossilLift G hE.1, by
        rw [← deg_fossilPushforward G (fossilLift G E),
          fossilPushforward_lift]
        exact hE.2⟩
    have hWin := hRank (fossilLift G E) hLiftE
    have hPushWin := (winnable_fossil_iff G hConnected
      (D - fossilLift G E)).mp hWin
    simpa only [fossilPushforward_sub, fossilPushforward_lift] using hPushWin
  · intro hRank E hE
    have hPushE : fossilPushforward G E ∈
        effOfDegree (fossil G) k :=
      ⟨effective_fossilPushforward G hE.1, by simpa using hE.2⟩
    have hWin := hRank (fossilPushforward G E) hPushE
    apply (winnable_fossil_iff G hConnected (D - E)).mpr
    simpa only [fossilPushforward_sub] using hWin

/-- Baker--Norine rank is unchanged by passing to the fossil. -/
theorem rank_fossilPushforward (G : CFGraph.{u})
    (hConnected : graphConnected G) (D : CFDiv G) :
    rank (fossil G) (fossilPushforward G D) = rank G D := by
  apply le_antisymm
  · apply (rank_geq_iff G D
      (rank (fossil G) (fossilPushforward G D))).mp
    apply (rank_geq_fossil_iff G hConnected D _).mpr
    exact (rank_geq_iff (fossil G) (fossilPushforward G D)
      (rank (fossil G) (fossilPushforward G D))).mpr le_rfl
  · apply (rank_geq_iff (fossil G) (fossilPushforward G D)
      (rank G D)).mp
    apply (rank_geq_fossil_iff G hConnected D _).mp
    exact (rank_geq_iff G D (rank G D)).mpr le_rfl

/-- Brill--Noether existence is invariant under passage to the fossil. -/
theorem BNExists_fossil_iff (G : CFGraph.{u})
    (hConnected : graphConnected G) (r d : ℤ) :
    BNExists G r d ↔ BNExists (fossil G) r d := by
  constructor
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨fossilPushforward G D, by simpa using hDegree, ?_⟩
    rw [rank_fossilPushforward G hConnected D]
    exact hRank
  · rintro ⟨D, hDegree, hRank⟩
    refine ⟨fossilLift G D, ?_, ?_⟩
    · rw [← deg_fossilPushforward G (fossilLift G D),
        fossilPushforward_lift]
      exact hDegree
    · rw [← rank_fossilPushforward G hConnected (fossilLift G D),
        fossilPushforward_lift]
      exact hRank

end Utilities
