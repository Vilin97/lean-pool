/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Basics.BananaSameStrandLemma
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaCounterexampleNormalForm
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaExceptionalArithmetic

/-!
# Negative divisor classes on an interior-marked theta strand

This file formalizes the divisor-class bijection asserted in paper Theorem
3.4.  The source library exposes linear equivalence as an equivalence relation
but does not package its quotient, so we first introduce the corresponding
divisor-class type.  The main `Set.BijOn` theorem is stated in the raw
subdivision orientation, the coordinate system consumed by the existing exact
interval theorem.  Generic divisor-algebra wrappers keep its surjectivity
proof away from the concrete `oneChip` elaboration blowup.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- Linear equivalence regarded as a setoid on graph divisors. -/
def divisorLinearEquivSetoid (G : CFGraph) : Setoid (CFDiv G) where
  r := linearEquiv G
  iseqv := linear_equiv_is_equivalence G

/-- The Picard quotient of all divisors on `G`.  Degree components can be
recovered because linear equivalence preserves degree. -/
abbrev DivisorClass (G : CFGraph) := Quotient (divisorLinearEquivSetoid G)

/-- The linear-equivalence class of a divisor. -/
def divisorClass (G : CFGraph) (D : CFDiv G) : DivisorClass G :=
  Quotient.mk (divisorLinearEquivSetoid G) D

@[simp] theorem divisorClass_eq_iff_linearEquiv
    (G : CFGraph) (D E : CFDiv G) :
    divisorClass G D = divisorClass G E ↔ linearEquiv G D E :=
  Quotient.eq_iff_equiv

/-- Classes which possess a representative with negative marked rank
difference.  This is literally the paper's set `{[D] : Δ(D) < 0}`. -/
def negativeRankDeltaClasses (M : TwiceMarked) : Set (DivisorClass M.graph) :=
  {c | ∃ D : CFDiv M.graph, divisorClass M.graph D = c ∧ rankDelta M D < 0}

private theorem linearEquiv_pair_cancel_right
    {G : CFGraph} {A B C : CFDiv G}
    (h : linearEquiv G (A + C) (B + C)) : linearEquiv G A B := by
  unfold linearEquiv at h ⊢
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

private theorem linearEquiv_add_of_sub
    {G : CFGraph} {D A E : CFDiv G}
    (h : linearEquiv G (D - A) E) : linearEquiv G D (E + A) := by
  unfold linearEquiv at h ⊢
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

private theorem linearEquiv_sub_common_generic
    {G : CFGraph} {D E A : CFDiv G}
    (h : linearEquiv G D E) : linearEquiv G (D - A) (E - A) := by
  unfold linearEquiv at h ⊢
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

private theorem linearEquiv_double_sub_pair_zero
    {G : CFGraph} {D A B : CFDiv G}
    (h : linearEquiv G D (B + A)) : linearEquiv G (D - A - B) 0 := by
  unfold linearEquiv at h ⊢
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h

/-- The missing forward direction of the displayed map in Theorem 3.4, in
the raw path orientation used by the interval calculation.

Every exceptional position `k` gives precisely the advertised negative
divisor `v_k + v_i`.  The endpoint `k = length` is included; its one-chip
deletion calculation is the subinterval-reflection firing script. -/
theorem rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions
    (B : Banana 2) (alpha : Fin 3)
    (i j k : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val)
    (hkExceptional : k ∈ thetaExceptionalPositions B alpha i j) :
    rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j))
      (oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i)) < 0 := by
  rcases hkExceptional with ⟨hkReflect, hkj, hkLower, hkUpper⟩
  have hiBound : i.val ≤ B.length alpha := by omega
  have hjBound : j.val ≤ B.length alpha := by omega
  have hkReflectNat : k.val ≠ B.length alpha - i.val := by
    intro h
    apply hkReflect
    rw [h]
    push_cast
    omega
  have hkjNat : k.val ≠ j.val := by
    intro h
    exact hkj (by exact_mod_cast h)
  have hkLowerNat : j.val - i.val ≤ k.val := by
    omega
  have hkUpperNat : k.val ≤ j.val - i.val + B.length alpha := by
    omega
  let D : CFDiv B.graph :=
    oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i)
  have hRankD : rank B.graph D = 0 := by
    dsimp [D]
    apply rank_same_strand_pair_zero_of_not_reflection_generic
      (by omega : 2 ≤ 2) B alpha k i
    omega
  have hRankU : rank B.graph
      (D - oneChip (B.pathVertex alpha i)) = 0 := by
    have hCancel : D - oneChip (B.pathVertex alpha i) =
        oneChip (G := B.graph) (B.pathVertex alpha k) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact rank_one_chip_zero_banana_two B _
  have hkPos : 0 < k.val := by
    omega
  have hRankV : rank B.graph
      (D - oneChip (B.pathVertex alpha j)) = 0 := by
    have hInside : i.val + k.val - B.length alpha ≤ j.val ∧
        j.val ≤ i.val + k.val := by
      omega
    by_cases hkEnd : k.val = B.length alpha
    · have hkEq : k = ⟨B.length alpha, by omega⟩ := Fin.ext hkEnd
      have hPrin := prin_subinterval_reflection (spec := B) (star := alpha)
        (lo := i.val) (hi := B.length alpha) (target := j.val)
        hij hj.2 (by omega)
      let q : B.PathPosition alpha :=
        ⟨i.val + B.length alpha - j.val, by omega⟩
      have hEquiv : linearEquiv B.graph
          (oneChip (B.pathVertex alpha i) +
            oneChip (B.pathVertex alpha ⟨B.length alpha, by omega⟩) -
              oneChip (B.pathVertex alpha j))
          (oneChip (B.pathVertex alpha q)) := by
        unfold linearEquiv
        apply (principal_iff_eq_prin B.graph _).mpr
        refine ⟨segScript B alpha i.val (B.length alpha) j.val, ?_⟩
        rw [hPrin]
        dsimp [q]
        abel
      have hRankEq := rank_eq_of_linear_equiv B.graph hEquiv
      rw [rank_one_chip_zero_banana_two] at hRankEq
      dsimp [D]
      rw [hkEq]
      simpa only [add_comm] using hRankEq
    · have hkInterior : B.IsInteriorPosition alpha k := by
        change 0 < k.val ∧ k.val < B.length alpha
        exact ⟨hkPos, by omega⟩
      dsimp [D]
      simpa only [add_comm] using
        rank_same_path_pair_sub_of_sum_inside_full B alpha i k j
          hi hkInterior hj hInside
  have hRankUV : rank B.graph
      (D - oneChip (B.pathVertex alpha i) -
        oneChip (B.pathVertex alpha j)) = -1 := by
    have hVertices : B.pathVertex alpha k ≠ B.pathVertex alpha j := by
      intro h
      apply hkjNat
      exact congrArg Fin.val (B.pathVertex_injective alpha h)
    have hRank := rank_one_chip_sub_one_chip_eq_neg_one_of_ne_banana
      B (B.pathVertex alpha k) (B.pathVertex alpha j) hVertices
    have hCancel :
        D - oneChip (B.pathVertex alpha i) -
            oneChip (B.pathVertex alpha j) =
          oneChip (B.pathVertex alpha k) -
            oneChip (B.pathVertex alpha j) := by
      dsimp [D]
      abel
    rw [hCancel]
    exact hRank
  exact (rankDelta_neg_iff_rank_zero_deletions
    (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D
      hRankD).mpr ⟨hRankU, hRankV, hRankUV⟩

/-- The advertised class-valued map of Theorem 3.4, restricted to its
interior same-strand branch and written in raw path coordinates. -/
def thetaPairDivisorClass
    (B : Banana 2) (alpha : Fin 3) (i k : B.PathPosition alpha) :
    DivisorClass B.graph :=
  divisorClass B.graph
    (oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i))

/-- The advertised map takes the exceptional set into the negative-class
set. -/
theorem thetaPairDivisorClass_mapsTo_negative
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    Set.MapsTo (thetaPairDivisorClass B alpha i)
      (thetaExceptionalPositions B alpha i j)
      (negativeRankDeltaClasses
        (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j))) := by
  intro k hk
  refine ⟨oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i),
    rfl, ?_⟩
  exact rankDelta_path_pair_neg_of_mem_thetaExceptionalPositions
    B alpha i j k hi hj hij hk

/-- Distinct path positions give distinct divisor classes after adding the
fixed marked chip. -/
theorem thetaPairDivisorClass_injective
    (B : Banana 2) (alpha : Fin 3) (i : B.PathPosition alpha) :
    Function.Injective (thetaPairDivisorClass B alpha i) := by
  intro k l hClasses
  unfold thetaPairDivisorClass at hClasses
  have hPairs := (divisorClass_eq_iff_linearEquiv B.graph _ _).mp hClasses
  have hChips : linearEquiv B.graph
      (oneChip (B.pathVertex alpha k))
      (oneChip (B.pathVertex alpha l)) :=
    linearEquiv_pair_cancel_right hPairs
  have hVertices : B.pathVertex alpha k = B.pathVertex alpha l :=
    one_chip_representative_unique_on_banana (by omega) B
      (linearEquiv.refl B.graph _) hChips
  exact B.pathVertex_injective alpha hVertices

/-- A negative divisor has the degree-one normal-form auxiliary vertex used
in the paper, after adding the first marked chip back abstractly. -/
theorem theta_negative_path_pair_equiv_auxiliary
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0) :
    ∃ w : B.graph.V, linearEquiv B.graph D
      (oneChip w + oneChip (B.pathVertex alpha i)) := by
  have huv : B.pathVertex alpha i ≠ B.pathVertex alpha j := by
    intro h
    have hVal := congrArg Fin.val (B.pathVertex_injective alpha h)
    omega
  obtain ⟨w, hw, _⟩ := theta_negative_rankDelta_normal_form
    B (B.pathVertex alpha i) (B.pathVertex alpha j) huv D hNeg
  exact ⟨w, linearEquiv_add_of_sub hw⟩

/-- Rank zero and the three deletion ranks supplied by a negative theta
divisor.  Factoring this away keeps later coordinate proofs syntactic. -/
theorem theta_negative_path_pair_rank_data
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0) :
    rank B.graph D = 0 ∧
      rank B.graph (D - oneChip (B.pathVertex alpha i)) = 0 ∧
      rank B.graph (D - oneChip (B.pathVertex alpha j)) = 0 ∧
      rank B.graph
        (D - oneChip (B.pathVertex alpha i) -
          oneChip (B.pathVertex alpha j)) = -1 := by
  have huv : B.pathVertex alpha i ≠ B.pathVertex alpha j := by
    intro h
    have hVal := congrArg Fin.val (B.pathVertex_injective alpha h)
    omega
  let M := mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)
  have hDistinct : ¬ linearEquiv B.graph
      (oneChip (B.pathVertex alpha i) - oneChip (B.pathVertex alpha j)) 0 :=
    marks_not_linearEquiv (by omega) B huv
  have hReduced := degree_and_rank_eq_of_rankDelta_neg_genus_two M D
    (graphConnected B) B.genus_graph hDistinct hNeg
  change deg D = 2 ∧ rank B.graph D = 0 at hReduced
  have hRankD : rank B.graph D = 0 := hReduced.2
  have hDeletions :=
    (rankDelta_neg_iff_rank_zero_deletions M D hRankD).mp hNeg
  dsimp [M] at hDeletions
  exact ⟨hRankD, hDeletions⟩

/-- The normal-form auxiliary vertex satisfies exactly the two rank-zero
conditions consumed by the same-strand interval theorem, and is not the
second marked vertex. -/
theorem theta_negative_path_pair_auxiliary_rank_data
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha) (hij : i.val < j.val)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0) :
    ∃ w : B.graph.V,
      w ≠ B.pathVertex alpha j ∧
      rank B.graph (oneChip w + oneChip (B.pathVertex alpha i)) = 0 ∧
      rank B.graph
        (oneChip w + oneChip (B.pathVertex alpha i) -
          oneChip (B.pathVertex alpha j)) = 0 ∧
      linearEquiv B.graph D
        (oneChip w + oneChip (B.pathVertex alpha i)) := by
  obtain ⟨w, hPairEquiv⟩ :=
    theta_negative_path_pair_equiv_auxiliary B alpha i j hij D hNeg
  obtain ⟨hRankD, _hRankU, hRankV, hRankUV⟩ :=
    theta_negative_path_pair_rank_data B alpha i j hij D hNeg
  have hPair : rank B.graph
      (oneChip w + oneChip (B.pathVertex alpha i)) = 0 := by
    have hRanks := rank_eq_of_linear_equiv B.graph hPairEquiv
    omega
  have hSubEquiv : linearEquiv B.graph
      (D - oneChip (B.pathVertex alpha j))
      (oneChip w + oneChip (B.pathVertex alpha i) -
        oneChip (B.pathVertex alpha j)) :=
    linearEquiv_sub_common_generic hPairEquiv
  have hSub : rank B.graph
      (oneChip w + oneChip (B.pathVertex alpha i) -
        oneChip (B.pathVertex alpha j)) = 0 := by
    have hRanks := rank_eq_of_linear_equiv B.graph hSubEquiv
    omega
  have hwv : w ≠ B.pathVertex alpha j := by
    intro hwv
    subst w
    have hZeroEquiv : linearEquiv B.graph
        (D - oneChip (B.pathVertex alpha i) -
          oneChip (B.pathVertex alpha j)) 0 :=
      linearEquiv_double_sub_pair_zero hPairEquiv
    have hRanks := rank_eq_of_linear_equiv B.graph hZeroEquiv
    rw [zero_divisor_rank] at hRanks
    omega
  exact ⟨w, hwv, hPair, hSub, hPairEquiv⟩

/-- Representative-level surjectivity of the displayed Theorem 3.4 map.
Every negative divisor is equivalent to `v_k + v_i` for an exceptional
position `k`. -/
theorem negative_path_pair_has_exceptional_representative
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val)
    (D : CFDiv B.graph)
    (hNeg : rankDelta
      (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j)) D < 0) :
    ∃ k : B.PathPosition alpha,
      k ∈ thetaExceptionalPositions B alpha i j ∧
      linearEquiv B.graph D
        (oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i)) := by
  obtain ⟨w, hwv, hPair, hSub, hPairEquiv⟩ :=
    theta_negative_path_pair_auxiliary_rank_data B alpha i j hij D hNeg
  obtain ⟨k, hwk, hkReflect, hkLower, hkUpper⟩ :=
    same_strand_auxiliary_vertex_interval B alpha i j hi hj hij w hwv hPair hSub
  have hkj : k.val ≠ j.val := by
    intro h
    apply hwv
    rw [hwk]
    exact congrArg (B.pathVertex alpha) (Fin.ext h)
  have hkExceptional : k ∈ thetaExceptionalPositions B alpha i j := by
    change (k.val : ℤ) ≠ (B.length alpha : ℤ) - (i.val : ℤ) ∧
      (k.val : ℤ) ≠ (j.val : ℤ) ∧
      (j.val : ℤ) - (i.val : ℤ) ≤ (k.val : ℤ) ∧
      (k.val : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) + (B.length alpha : ℤ)
    constructor
    · intro h
      apply hkReflect
      omega
    constructor
    · intro h
      apply hkj
      omega
    constructor <;> omega
  have hWChip : oneChip w =
      (oneChip (B.pathVertex alpha k) : CFDiv B.graph) :=
    congrArg (oneChip (G := B.graph)) hwk
  have hPairEquiv' : linearEquiv B.graph D
      (oneChip (B.pathVertex alpha k) + oneChip (B.pathVertex alpha i)) := by
    simpa only [hWChip] using hPairEquiv
  exact ⟨k, hkExceptional, hPairEquiv'⟩

/-- The class map is surjective from exceptional positions onto negative
divisor classes. -/
theorem thetaPairDivisorClass_surjOn_negative
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    Set.SurjOn (thetaPairDivisorClass B alpha i)
      (thetaExceptionalPositions B alpha i j)
      (negativeRankDeltaClasses
        (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j))) := by
  intro c hc
  obtain ⟨D, hClassD, hNeg⟩ := hc
  obtain ⟨k, hkExceptional, hPairEquiv⟩ :=
    negative_path_pair_has_exceptional_representative
      B alpha i j hi hj hij D hNeg
  have hClass : thetaPairDivisorClass B alpha i k = c := by
    unfold thetaPairDivisorClass
    rw [← hClassD]
    exact (divisorClass_eq_iff_linearEquiv B.graph _ _).mpr hPairEquiv.symm
  exact ⟨k, hkExceptional, hClass⟩

/-- **Theorem 3.4, class-valued bijection (raw-coordinate interior branch).**

The displayed map `k ↦ [v_k + v_i]` restricts to a bijection from the paper's
exceptional set onto the set of linear-equivalence classes with negative
marked rank difference. -/
theorem thetaPairDivisorClass_bijOn_negative
    (B : Banana 2) (alpha : Fin 3)
    (i j : B.PathPosition alpha)
    (hi : B.IsInteriorPosition alpha i)
    (hj : B.IsInteriorPosition alpha j)
    (hij : i.val < j.val) :
    Set.BijOn (thetaPairDivisorClass B alpha i)
      (thetaExceptionalPositions B alpha i j)
      (negativeRankDeltaClasses
        (mark B.graph (B.pathVertex alpha i) (B.pathVertex alpha j))) :=
  ⟨thetaPairDivisorClass_mapsTo_negative B alpha i j hi hj hij,
    (thetaPairDivisorClass_injective B alpha i).injOn,
    thetaPairDivisorClass_surjOn_negative B alpha i j hi hj hij⟩

end Bananas
