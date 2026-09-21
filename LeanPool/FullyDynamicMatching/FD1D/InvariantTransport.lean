/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.Transport
import LeanPool.FullyDynamicMatching.FD1D.ConcreteTransport
import LeanPool.FullyDynamicMatching.FD1D.Symmetry
import LeanPool.FullyDynamicMatching.FD1D.Initialization
import LeanPool.FullyDynamicMatching.FD1D.Averaging

/-! # Invariant Transport -/

namespace FD1D

noncomputable section

open scoped BigOperators

/-!
# Invariant concrete transport coefficients

This module supplies the child-swap symmetries needed to cancel the
off-diagonal terms in the complete-tree Haar expansion.
-/

/-- Distinct complete-tree nodes at the same depth have disjoint tent
interiors. -/
theorem completeHaarNode_intervalsSeparated_of_depth_eq
    {L : ℕ} (i j : CompleteHaarNode L) (hdepth : i.1 = j.1)
    (hij : i ≠ j) :
    IntervalsSeparated haarNodeLeft haarNodeWidth i j := by
  rcases i with ⟨d, i⟩
  rcases j with ⟨e, j⟩
  change d = e at hdepth
  subst e
  have hval : i.val ≠ j.val := by
    intro h
    apply hij
    congr
    exact Fin.ext h
  simp only [IntervalsSeparated, haarNodeLeft, haarNodeWidth]
  have hden : (0 : ℝ) < (2 ^ d.val : ℕ) := by positivity
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · left
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hden).2
    exact_mod_cast hlt
  · right
    rw [← add_div]
    apply (div_le_div_iff_of_pos_right hden).2
    exact_mod_cast hgt

namespace FiniteLaw

/-- An invariant equivalence which negates one factor and fixes the other
makes their product an odd observable. -/
theorem oddSymmetry_mul_of_invariant_neg_fixed
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (e : Equiv.Perm Ω)
    (hμ : FiniteKernel.LawInvariant μ e) (f g : Ω → ℝ)
    (hf : ∀ ω, f (e ω) = -f ω) (hg : ∀ ω, g (e ω) = g ω) :
    μ.OddSymmetry (fun ω => f ω * g ω) := by
  refine ⟨e, hμ, ?_⟩
  intro ω
  change f (e ω) * g (e ω) = -(f ω * g ω)
  rw [hf, hg]
  ring

/-- Symmetric version of `oddSymmetry_mul_of_invariant_neg_fixed`. -/
theorem oddSymmetry_mul_of_invariant_fixed_neg
    {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (e : Equiv.Perm Ω)
    (hμ : FiniteKernel.LawInvariant μ e) (f g : Ω → ℝ)
    (hf : ∀ ω, f (e ω) = f ω) (hg : ∀ ω, g (e ω) = -g ω) :
    μ.OddSymmetry (fun ω => f ω * g ω) := by
  refine ⟨e, hμ, ?_⟩
  intro ω
  change f (e ω) * g (e ω) = -(f ω * g ω)
  rw [hf, hg]
  ring

end FiniteLaw

namespace TreeSymmetry

/-- The inventory lift used by the symmetry module agrees with the canonical
lift used by refreshed initialization. -/
theorem inventoryPerm_eq_inventoryStatePerm
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (e : Equiv.Perm ι) :
    inventoryPerm (m := m) e = inventoryStatePerm (m := m) e := by
  apply Equiv.ext
  intro x
  apply InventoryState.ext
  intro i
  rfl

end TreeSymmetry

/-- Abstract complete-tree cancellation criterion.  A swap at a node negates
that node's coefficient and fixes every strictly shallower coefficient. -/
theorem completeHaar_crossTerm_symmetry_of_invariant_swaps
    {L : ℕ} {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (b : Ω → CompleteHaarNode L → ℝ)
    (swap : ∀ d : Fin L, DyadicNode d.val → Equiv.Perm Ω)
    (hinv : ∀ d v, FiniteKernel.LawInvariant μ (swap d v))
    (hflip : ∀ d v ω, b (swap d v ω) ⟨d, v⟩ = -b ω ⟨d, v⟩)
    (hshallower : ∀ d v k w, k.val < d.val →
      ∀ ω, b (swap d v ω) ⟨k, w⟩ = b ω ⟨k, w⟩) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun ω => b ω i * b ω j) := by
  intro i j hij
  rcases lt_trichotomy i.1.val j.1.val with hlt | heq | hgt
  · right
    exact FiniteLaw.oddSymmetry_mul_of_invariant_fixed_neg
      μ (swap j.1 j.2) (hinv j.1 j.2)
      (fun ω => b ω i) (fun ω => b ω j)
      (hshallower j.1 j.2 i.1 i.2 hlt)
      (hflip j.1 j.2)
  · left
    exact completeHaarNode_intervalsSeparated_of_depth_eq
      i j (Fin.ext heq) hij
  · right
    exact FiniteLaw.oddSymmetry_mul_of_invariant_neg_fixed
      μ (swap i.1 i.2) (hinv i.1 i.2)
      (fun ω => b ω i) (fun ω => b ω j)
      (hflip i.1 i.2)
      (hshallower i.1 i.2 j.1 j.2 hgt)

namespace HierarchicalDynamics

/-- Swapping the children of `i` negates its concrete Haar coefficient. -/
theorem concrete_haarCoefficient_swapNode
    {L m : ℕ} (a : ℝ) (ha : 0 < a)
    (i : CompleteHaarNode L)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a
        (TreeSymmetry.inventorySwap i.1.isLt i.2 x)).nodeCoefficient i =
      -(stateDyadicMass a x).nodeCoefficient i := by
  rw [stateDyadicMass_nodeCoefficient a ha,
    stateDyadicMass_nodeCoefficient a ha]
  exact TreeSymmetry.concrete_imbalance_swapNode
    i.1.isLt i.2 x a

/-- A child swap at `i` fixes every concrete Haar coefficient at a strictly
shallower depth. -/
theorem concrete_haarCoefficient_strictAncestor
    {L m : ℕ} (a : ℝ) (ha : 0 < a)
    (i j : CompleteHaarNode L) (hji : j.1.val < i.1.val)
    (x : InventoryState (DyadicNode L) m) :
    (stateDyadicMass a
        (TreeSymmetry.inventorySwap i.1.isLt i.2 x)).nodeCoefficient j =
      (stateDyadicMass a x).nodeCoefficient j := by
  rw [stateDyadicMass_nodeCoefficient a ha,
    stateDyadicMass_nodeCoefficient a ha]
  exact TreeSymmetry.concrete_imbalance_strictAncestor
    i.1.isLt i.2 x a hji j.2

/-- Cross-term symmetry for the canonical node coefficients of the concrete
dyadic mass. -/
theorem concrete_nodeCoefficient_crossTerm_symmetry_of_swapInvariant
    {L m : ℕ} (a : ℝ) (ha : 0 < a)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (TreeSymmetry.inventorySwap d.isLt v)) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun x =>
          (stateDyadicMass a x).nodeCoefficient i *
            (stateDyadicMass a x).nodeCoefficient j) := by
  apply completeHaar_crossTerm_symmetry_of_invariant_swaps
    μ (fun x i => (stateDyadicMass a x).nodeCoefficient i)
    (fun d v => TreeSymmetry.inventorySwap d.isLt v) hinv
  · exact fun d v x => concrete_haarCoefficient_swapNode
      a ha ⟨d, v⟩ x
  · exact fun d v k w hkd x =>
      concrete_haarCoefficient_strictAncestor
        a ha ⟨d, v⟩ ⟨k, w⟩ hkd x

/-- The exact `stateHaarCoefficient` symmetry premise used by
`transport_cost_equation_three`, for any law invariant under every child
swap. -/
theorem concrete_haar_crossTerm_symmetry_of_swapInvariant
    {L m : ℕ} (a : ℝ) (ha : 0 < a)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (TreeSymmetry.inventorySwap d.isLt v)) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun x =>
          stateHaarCoefficient a x i * stateHaarCoefficient a x j) := by
  simpa only [stateHaarCoefficient, stateDyadicMass_nodeCoefficient a ha] using
    concrete_nodeCoefficient_crossTerm_symmetry_of_swapInvariant
      a ha μ hinv

/-- The concrete stationary law satisfies the complete Haar cross-term
symmetry premise in `transport_cost_equation_three`. -/
theorem concrete_stationary_haar_crossTerm_symmetry
    {L m : ℕ} (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hirr : (kernel (L := L) (m := m) a ha hm).Irreducible)
    (hstationary : (kernel (L := L) (m := m) a ha hm).IsStationary μ) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        μ.OddSymmetry (fun x =>
          stateHaarCoefficient a x i * stateHaarCoefficient a x j) := by
  apply concrete_haar_crossTerm_symmetry_of_swapInvariant a ha μ
  intro d v
  exact TreeSymmetry.concrete_stationary_lawInvariant
    d.isLt v a ha hm hirr hstationary

/-- Every iterate of the concrete kernel from the refreshed law is invariant
under a specified child swap. -/
theorem concrete_iterate_refreshedLaw_lawInvariant
    {L m : ℕ} (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (n : ℕ) (d : Fin L) (v : DyadicNode d.val) :
    FiniteKernel.LawInvariant
      ((kernel (L := L) (m := m) a ha hm).iterate n
        (refreshedLaw L m))
      (TreeSymmetry.inventorySwap d.isLt v) := by
  apply iterate_refreshedLaw_lawInvariant_of_compatible
    (kernel (L := L) (m := m) a ha hm)
    (TreeSymmetry.leafSwap d.isLt v)
    (TreeSymmetry.inventorySwap d.isLt v)
  · intro ω
    calc
      assignmentState
          (assignmentPerm (TreeSymmetry.leafSwap d.isLt v) ω) =
          inventoryStatePerm (TreeSymmetry.leafSwap d.isLt v)
            (assignmentState ω) :=
        assignmentState_perm (TreeSymmetry.leafSwap d.isLt v) ω
      _ = TreeSymmetry.inventorySwap d.isLt v
          (assignmentState ω) := by
        rw [TreeSymmetry.inventorySwap,
          TreeSymmetry.inventoryPerm_eq_inventoryStatePerm]
  · exact TreeSymmetry.concrete_kernel_equivariant
      d.isLt v a ha hm

/-- Every refreshed iterate satisfies the complete Haar cross-term symmetry
premise in `transport_cost_equation_three`. -/
theorem concrete_refreshed_iterate_haar_crossTerm_symmetry
    {L m : ℕ} (a : ℝ) (ha : 0 < a) (hm : 0 < m) (n : ℕ) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        ((kernel (L := L) (m := m) a ha hm).iterate n
          (refreshedLaw L m)).OddSymmetry (fun x =>
            stateHaarCoefficient a x i *
              stateHaarCoefficient a x j) := by
  apply concrete_haar_crossTerm_symmetry_of_swapInvariant a ha
  exact fun d v =>
    concrete_iterate_refreshedLaw_lawInvariant a ha hm n d v

/-- The uniform mixture of the first `T` refreshed iterates has one
time-preserving odd symmetry for every nonseparated coefficient pair. -/
theorem concrete_refreshed_timeAverage_haar_crossTerm_symmetry
    {L m T : ℕ} (a : ℝ) (ha : 0 < a) (hm : 0 < m) (hT : 0 < T) :
    ∀ i j, i ≠ j →
      IntervalsSeparated (haarNodeLeft (L := L))
          (haarNodeWidth (L := L)) i j ∨
        (FiniteLaw.timeAverage hT (fun t : Fin T =>
          (kernel (L := L) (m := m) a ha hm).iterate t.val
            (refreshedLaw L m))).OddSymmetry (fun z =>
              stateHaarCoefficient a z.2 i *
                stateHaarCoefficient a z.2 j) := by
  apply completeHaar_crossTerm_symmetry_of_invariant_swaps
    (FiniteLaw.timeAverage hT (fun t : Fin T =>
      (kernel (L := L) (m := m) a ha hm).iterate t.val
        (refreshedLaw L m)))
    (fun z i => stateHaarCoefficient a z.2 i)
    (fun d v => FiniteLaw.timeLiftPerm (T := T)
      (TreeSymmetry.inventorySwap d.isLt v))
  · intro d v
    apply FiniteLaw.timeAverage_lawInvariant
    intro t
    exact concrete_iterate_refreshedLaw_lawInvariant
      a ha hm t.val d v
  · intro d v z
    rcases z with ⟨t, x⟩
    change stateHaarCoefficient a
        (TreeSymmetry.inventorySwap d.isLt v x) ⟨d, v⟩ =
      -stateHaarCoefficient a x ⟨d, v⟩
    simpa only [stateHaarCoefficient,
      stateDyadicMass_nodeCoefficient a ha] using
        concrete_haarCoefficient_swapNode a ha ⟨d, v⟩ x
  · intro d v k w hkd z
    rcases z with ⟨t, x⟩
    change stateHaarCoefficient a
        (TreeSymmetry.inventorySwap d.isLt v x) ⟨k, w⟩ =
      stateHaarCoefficient a x ⟨k, w⟩
    simpa only [stateHaarCoefficient,
      stateDyadicMass_nodeCoefficient a ha] using
        concrete_haarCoefficient_strictAncestor
          a ha ⟨d, v⟩ ⟨k, w⟩ hkd x

end HierarchicalDynamics

end

end FD1D
