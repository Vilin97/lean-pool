/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Markov
public import LeanPool.FullyDynamicMatching.FD1D.Tree

/-! # Initialization -/

@[expose] public section

namespace FD1D

noncomputable section

open scoped BigOperators

/-!
# Refreshed inventory initialization

The refreshed inventory is obtained from `m` labeled, independently uniform
leaf assignments by forgetting the labels and retaining only the fiber
cardinalities. The resulting law is invariant under every leaf relabeling.
-/

/-- Assignments of `m` labeled inventory items to a finite set of locations. -/
abbrev Assignment (ι : Type*) (m : ℕ) := Fin m → ι

/-- Assignments of `m` labeled inventory items to the depth-`L` leaves. -/
abbrev DyadicAssignment (L m : ℕ) := Assignment (DyadicNode L) m

/-- Number of labels assigned to one location. -/
def assignmentCount {ι : Type*} [DecidableEq ι] {m : ℕ}
    (ω : Assignment ι m) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => ω j = i).card

/-- Fiber cardinalities partition all `m` assignment labels. -/
theorem sum_assignmentCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (ω : Assignment ι m) :
    ∑ i, assignmentCount ω i = m := by
  classical
  simp only [assignmentCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- The fixed-total inventory state formed from assignment fiber cardinalities. -/
def assignmentState {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (ω : Assignment ι m) : InventoryState ι m :=
  ⟨assignmentCount ω, sum_assignmentCount ω⟩

@[simp]
theorem assignmentState_count {ι : Type*} [Fintype ι]
    [DecidableEq ι] {m : ℕ} (ω : Assignment ι m) (i : ι) :
    (assignmentState ω).1 i = assignmentCount ω i :=
  rfl

/-- Postcompose every assignment with a location permutation. -/
def assignmentPerm {ι : Type*} {m : ℕ} (e : Equiv.Perm ι) :
    Equiv.Perm (Assignment ι m) :=
  Equiv.arrowCongr (Equiv.refl (Fin m)) e

@[simp]
theorem assignmentPerm_apply {ι : Type*} {m : ℕ}
    (e : Equiv.Perm ι) (ω : Assignment ι m) (j : Fin m) :
    assignmentPerm e ω j = e (ω j) :=
  rfl

/-- Push a fixed-total count vector forward along a location permutation. -/
def inventoryStatePerm {ι : Type*} [Fintype ι] {m : ℕ}
    (e : Equiv.Perm ι) : Equiv.Perm (InventoryState ι m) where
  toFun x :=
    ⟨fun i => x.1 (e.symm i), by
      calc
        ∑ i, x.1 (e.symm i) = ∑ i, x.1 i :=
          Equiv.sum_comp e.symm x.1
        _ = m := x.2⟩
  invFun x :=
    ⟨fun i => x.1 (e i), by
      calc
        ∑ i, x.1 (e i) = ∑ i, x.1 i :=
          Equiv.sum_comp e x.1
        _ = m := x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp

@[simp]
theorem inventoryStatePerm_count {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 i = x.1 (e.symm i) :=
  rfl

theorem inventoryStatePerm_image_count {ι : Type*} [Fintype ι]
    {m : ℕ} (e : Equiv.Perm ι) (x : InventoryState ι m) (i : ι) :
    (inventoryStatePerm e x).1 (e i) = x.1 i := by
  simp

/-- Relabeling an assignment relabels its fiber-count state. -/
@[simp]
theorem assignmentCount_perm {ι : Type*} [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) (i : ι) :
    assignmentCount (assignmentPerm e ω) (e i) = assignmentCount ω i := by
  simp [assignmentCount]

/-- The assignment-to-state map is equivariant for the canonical lifts. -/
theorem assignmentState_perm {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ℕ} (e : Equiv.Perm ι) (ω : Assignment ι m) :
    assignmentState (assignmentPerm e ω) =
      inventoryStatePerm e (assignmentState ω) := by
  apply InventoryState.ext
  intro i
  change assignmentCount (assignmentPerm e ω) i =
    assignmentCount ω (e.symm i)
  rw [← assignmentCount_perm e ω (e.symm i)]
  simp

/-- A uniform pushforward is invariant under any compatible permutations of
its source and target. -/
theorem uniform_map_lawInvariant
    {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [DecidableEq B]
    (f : A → B) (ea : Equiv.Perm A) (eb : Equiv.Perm B)
    (h : ∀ a, f (ea a) = eb (f a)) :
    FiniteKernel.LawInvariant
      ((FiniteLaw.uniform : FiniteLaw A).map f) eb := by
  intro b
  simp only [FiniteLaw.mass_map, FiniteLaw.mass_uniform]
  simp_rw [Finset.sum_filter]
  rw [← Equiv.sum_comp ea
    (fun a => if f a = eb b then
      (1 / Fintype.card A : ℝ) else 0)]
  apply Finset.sum_congr rfl
  intro a _
  rw [h]
  simp

/-- The refreshed inventory law: choose every labeled item's leaf uniformly
and independently, then forget the labels and retain only fiber counts. -/
def refreshedLaw (L m : ℕ) :
    FiniteLaw (InventoryState (DyadicNode L) m) :=
  (FiniteLaw.uniform : FiniteLaw (DyadicAssignment L m)).map assignmentState

@[simp]
theorem refreshedLaw_mass (L m : ℕ)
    (x : InventoryState (DyadicNode L) m) :
    (refreshedLaw L m).mass x =
      ∑ ω : DyadicAssignment L m with assignmentState ω = x,
        (1 / Fintype.card (DyadicAssignment L m) : ℝ) :=
  rfl

/-- A form parameterized by the target-state permutation, for clients that
already define their own lift of a leaf permutation. -/
theorem refreshedLaw_lawInvariant_of_compatible
    {L m : ℕ} (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω)) :
    FiniteKernel.LawInvariant (refreshedLaw L m) statePerm :=
  uniform_map_lawInvariant assignmentState (assignmentPerm leafPerm)
    statePerm hcompat

/-- The refreshed law is invariant under the canonical lift of every leaf
permutation to inventory states. -/
theorem refreshedLaw_lawInvariant {L m : ℕ}
    (leafPerm : Equiv.Perm (DyadicNode L)) :
    FiniteKernel.LawInvariant (refreshedLaw L m)
      (inventoryStatePerm leafPerm) :=
  refreshedLaw_lawInvariant_of_compatible leafPerm
    (inventoryStatePerm leafPerm) (assignmentState_perm leafPerm)

/-- Kernel equivariance preserves refreshed-law invariance through every
iterate, for any compatible state-space lift. -/
theorem iterate_refreshedLaw_lawInvariant_of_compatible
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (statePerm : Equiv.Perm (InventoryState (DyadicNode L) m))
    (hcompat : ∀ ω : DyadicAssignment L m,
      assignmentState (assignmentPerm leafPerm ω) =
        statePerm (assignmentState ω))
    (hK : K.Equivariant statePerm) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m)) statePerm :=
  FiniteKernel.iterate_lawInvariant hK
    (refreshedLaw_lawInvariant_of_compatible leafPerm statePerm hcompat) n

/-- If a kernel is equivariant under the canonical lift of a leaf
permutation, every iterate from the refreshed law remains invariant. -/
theorem iterate_refreshedLaw_lawInvariant
    {L m : ℕ} (K : FiniteKernel (InventoryState (DyadicNode L) m))
    (leafPerm : Equiv.Perm (DyadicNode L))
    (hK : K.Equivariant (inventoryStatePerm leafPerm)) (n : ℕ) :
    FiniteKernel.LawInvariant (K.iterate n (refreshedLaw L m))
      (inventoryStatePerm leafPerm) :=
  FiniteKernel.iterate_lawInvariant hK
    (refreshedLaw_lawInvariant leafPerm) n

end

end FD1D
