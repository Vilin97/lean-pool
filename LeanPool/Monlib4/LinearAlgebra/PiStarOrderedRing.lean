/-
Copyright (c) 2024 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Complex.Basic

/-!
  # pi.star_ordered_ring

  This file contains the definition of `pi.star_ordered_ring`.
-/

/-- Coordinate projection of a set of dependent functions along `Pi.single`. -/
def Set.ofPi {ι : Type _} {B : ι → Type _} [DecidableEq ι] [∀ i, Zero (B i)] (s : Set (∀ i, B i)) :
    ∀ i, Set (B i) := fun i x => Pi.single i x ∈ s

theorem Set.piOfPi {ι : Type _} {B : ι → Type _} [DecidableEq ι] [∀ i, AddZeroClass (B i)]
    {s : ∀ i, Set (B i)} (h : ∀ i, s i 0) : (Set.univ.pi s).ofPi = s := by
  ext i x
  change Pi.single i x ∈ Set.univ.pi s ↔ x ∈ s i
  constructor
  · intro hi
    specialize hi i
    rw [Pi.single_eq_same] at hi
    exact hi (Set.mem_univ i)
  · intro hx j _
    by_cases hj : j = i
    · rw [hj]
      rwa [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hj]
      exact h j

/-- Coordinate projection of an additive submonoid of dependent functions along `Pi.single`. -/
def AddSubmonoid.ofPi {ι : Type _} {B : ι → Type _} [DecidableEq ι] [∀ i, AddZeroClass (B i)] :
    AddSubmonoid (∀ i, B i) → ∀ i, AddSubmonoid (B i) := fun h i =>
  { carrier := fun x => x ∈ Set.ofPi h.carrier i
    zero_mem' := by
      change Pi.single i 0 ∈ h.carrier
      rw [Pi.single_zero]
      exact h.zero_mem'
    add_mem' := fun x y => by
      have := h.add_mem' x y
      simp only [AddSubmonoid.mem_carrier, ← Pi.single_add] at this ⊢
      exact this }

theorem AddSubmonoid.piOfPi {ι : Type _} {B : ι → Type _} [DecidableEq ι] [∀ i, AddZeroClass (B i)]
    (h : ∀ i, AddSubmonoid (B i)) : (AddSubmonoid.pi Set.univ h).ofPi = h := by
  ext i x
  change Pi.single i x ∈ AddSubmonoid.pi Set.univ h ↔ x ∈ h i
  rw [AddSubmonoid.mem_pi]
  constructor
  · intro hx
    simpa using hx i
  · intro hx j
    by_cases hj : j = i
    · rw [hj, Pi.single_eq_same]
      intro _
      exact hx
    · simp [Pi.single_eq_of_ne hj, (h j).zero_mem]

theorem Set.ofPi_mem' {ι : Type _} {B : ι → Type _} [DecidableEq ι] [∀ i, AddZeroClass (B i)]
    {s : ∀ i, Set (B i)} {S : Set (∀ i, B i)} (hs : Set.univ.pi s ⊆ S) (h : ∀ i, s i 0) (i : ι) :
    s i ⊆ S.ofPi i := by
  intro x hx
  change Pi.single i x ∈ S
  apply hs
  intro j _
  by_cases hj : j = i
  · rw [hj]
    rwa [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hj]
    exact h j

theorem AddSubmonoid.mem_closure_pi {ι : Type _} {B : ι → Type _}
    [∀ i, AddZeroClass (B i)] {s : ∀ i, Set (B i)} {x : ∀ i, B i} :
    x ∈ AddSubmonoid.closure (Set.univ.pi fun i => s i) → ∀ i, x i ∈ AddSubmonoid.closure (s i) :=
  by
  simp_rw [AddSubmonoid.mem_closure]
  intro h i S hS
  specialize h (AddSubmonoid.pi Set.univ fun i => AddSubmonoid.closure (s i))
  simp_rw [Set.subset_def, Set.mem_univ_pi, AddSubmonoid.pi, SetLike.mem_coe,
    AddSubmonoid.mem_mk] at h
  simp only [AddSubsemigroup.mem_mk, Set.mem_pi, Set.mem_univ, AddSubsemigroup.mem_carrier,
    mem_toSubsemigroup, forall_true_left, AddSubmonoid.mem_closure] at h
  exact h (fun y hy j K hK => hK (hy j)) i S hS

theorem Pi.StarOrderedRing.nonneg_def {ι : Type _} {α : ι → Type _} [∀ i, NonUnitalSemiring (α i)]
    [∀ i, PartialOrder (α i)] [∀ i, StarRing (α i)] [∀ i, StarOrderedRing (α i)]
    (h : ∀ (i : ι) (x : α i), 0 ≤ x ↔ ∃ y, star y * y = x) (x : ∀ i, α i) :
    0 ≤ x ↔ ∃ y, star y * y = x := by
  simp_rw [Pi.le_def, Pi.zero_apply, funext_iff, Pi.mul_apply, Pi.star_apply, h]
  exact
    ⟨fun hx => ⟨fun i => (hx i).choose, fun i => (hx i).choose_spec⟩,
    fun ⟨y, hy⟩ i => ⟨y i, hy i⟩⟩

instance {ι : Type _} {α : ι → Type _} [∀ i, Ring (α i)]
    [∀ i, PartialOrder (α i)] [∀ i, StarRing (α i)] [∀ i, StarOrderedRing (α i)] :
  CovariantClass ((i : ι) → α i) ((i : ι) → α i)
      (Function.swap fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1 :=
⟨fun x y z h j => by simp_rw [Function.swap, Pi.add_apply, add_le_add_iff_right, h j]⟩

theorem Pi.StarOrderedRing.le_def {ι : Type _} {α : ι → Type _} [∀ i, Ring (α i)]
    [∀ i, PartialOrder (α i)] [∀ i, StarRing (α i)] [∀ i, StarOrderedRing (α i)]
    (h : ∀ (i : ι) (x : α i), 0 ≤ x ↔ ∃ y, star y * y = x) (x y : ∀ i, α i) :
    x ≤ y ↔ ∃ z, star z * z = y - x := by
  rwa [← sub_nonneg, ← Pi.StarOrderedRing.nonneg_def]

/-- Dependent functions over star-ordered rings are star-ordered coordinatewise. -/
theorem Pi.starOrderedRing {ι : Type _} {B : ι → Type _} [∀ i, Ring (B i)] [∀ i, PartialOrder (B i)]
    [∀ i, StarRing (B i)] [∀ i, StarOrderedRing (B i)]
    (h : ∀ (i : ι) (x : B i), 0 ≤ x ↔ ∃ y, star y * y = x) :
    StarOrderedRing (∀ i, B i) :=
StarOrderedRing.of_le_iff
  (fun a b => by
    rw [Pi.StarOrderedRing.le_def h]
    simp_rw [eq_sub_iff_add_eq', eq_comm])
