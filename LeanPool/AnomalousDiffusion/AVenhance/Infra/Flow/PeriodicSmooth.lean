/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.LatticeShift
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Floor.Ring

/-! Smooth jointly time-space periodic fields have globally bounded derivatives
of each fixed order. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

/-- A simultaneous integer shift in time and in the two spatial coordinates. -/
def jointLatticeShift (z : ℤ × (Fin 2 → ℤ)) : ℝ × Vec 2 :=
  ((z.1 : ℝ), AVenhance.latticeShift z.2)

/-- Joint `ℤ × ℤ²` periodicity of a time-dependent vector field. -/
def IsJointPeriodicField (b : ℝ → Vec 2 → Vec 2) : Prop :=
  ∀ (m : ℤ) (k : Fin 2 → ℤ) (t : ℝ) (x : Vec 2),
    b (t + (m : ℝ)) (x + AVenhance.latticeShift k) = b t x

/-- A smooth jointly periodic field. In Mathlib's `ContDiff` order,
`∞` is the coercion of `(⊤ : ℕ∞)`, the C-infinity order used in the flow estimates. -/
structure SmoothPeriodicField (b : ℝ → Vec 2 → Vec 2) : Prop where
  smooth : ContDiff ℝ ∞ (Function.uncurry b)
  periodic : IsJointPeriodicField b

/-- Closed time-space unit cell used for smooth periodic field estimates. -/
def PeriodicSmooth.jointUnitCell : Set (ℝ × Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem PeriodicSmooth.isCompact_jointUnitCell : IsCompact PeriodicSmooth.jointUnitCell := by
  apply IsCompact.prod isCompact_Icc
  exact isCompact_univ_pi (fun _ => isCompact_Icc)

theorem PeriodicSmooth.mem_jointUnitCell_normalize (p : ℝ × Vec 2) :
    (p - jointLatticeShift (Int.floor p.1, fun i => Int.floor (p.2 i))) ∈
      PeriodicSmooth.jointUnitCell := by
  rw [PeriodicSmooth.jointUnitCell, Set.mem_prod, Set.mem_Icc]
  constructor
  · constructor
    · change 0 ≤ p.1 - (Int.floor p.1 : ℝ)
      linarith [Int.floor_le p.1]
    · change p.1 - (Int.floor p.1 : ℝ) ≤ 1
      linarith [Int.lt_floor_add_one p.1]
  · intro i _
    rw [Set.mem_Icc]
    constructor
    · change 0 ≤ p.2 i - (Int.floor (p.2 i) : ℝ)
      linarith [Int.floor_le (p.2 i)]
    · change p.2 i - (Int.floor (p.2 i) : ℝ) ≤ 1
      linarith [Int.lt_floor_add_one (p.2 i)]

theorem PeriodicSmooth.joint_normalize_add_shift (p : ℝ × Vec 2) :
    p - jointLatticeShift (Int.floor p.1, fun i => Int.floor (p.2 i)) +
      jointLatticeShift (Int.floor p.1, fun i => Int.floor (p.2 i)) = p := by
  exact sub_add_cancel _ _

/-- Iterated derivatives inherit the same lattice periodicity as the field. -/
theorem iteratedFDeriv_jointPeriodic
    {b : ℝ → Vec 2 → Vec 2} (hb : IsJointPeriodicField b)
    (n : ℕ) (z : ℤ × (Fin 2 → ℤ)) (p : ℝ × Vec 2) :
    iteratedFDeriv ℝ n (Function.uncurry b) (p + jointLatticeShift z) =
      iteratedFDeriv ℝ n (Function.uncurry b) p := by
  have hfun : (fun q : ℝ × Vec 2 => Function.uncurry b
      (q + jointLatticeShift z)) = Function.uncurry b := by
    funext q
    rcases q with ⟨t, x⟩
    exact hb z.1 z.2 t x
  have hderiv := congrArg (fun f : (ℝ × Vec 2) → Vec 2 =>
    iteratedFDeriv ℝ n f p) hfun
  simpa only [iteratedFDeriv_comp_add_right] using hderiv

/-- Every fixed-order mixed derivative of a smooth jointly periodic field is
bounded on all of space-time. The bound may depend on the derivative order. -/
theorem exists_global_iteratedFDeriv_bound
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × Vec 2,
      ‖iteratedFDeriv ℝ n (Function.uncurry b) p‖ ≤ C := by
  let F : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let g : ℝ × Vec 2 → ℝ := fun p => ‖iteratedFDeriv ℝ n F p‖
  have hg : Continuous g := by
    exact continuous_norm.comp
      (hb.smooth.continuous_iteratedFDeriv (m := n) (by simp))
  have hupper : BddAbove (g '' PeriodicSmooth.jointUnitCell) :=
    PeriodicSmooth.isCompact_jointUnitCell.bddAbove_image hg.continuousOn
  let C : ℝ := sSup (g '' PeriodicSmooth.jointUnitCell)
  have hcell_nonempty : (g '' PeriodicSmooth.jointUnitCell).Nonempty := by
    refine ⟨g (0, fun _ => 0), ?_⟩
    refine ⟨(0, fun _ => 0), ?_, rfl⟩
    constructor
    · simp [Set.mem_Icc]
    · intro i hi
      simp [Set.mem_Icc]
  have hcell_bound (p : ℝ × Vec 2) (hp : p ∈ PeriodicSmooth.jointUnitCell) : g p ≤ C := by
    exact le_csSup hupper ⟨p, hp, rfl⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p
  let z : ℤ × (Fin 2 → ℤ) := (Int.floor p.1, fun i => Int.floor (p.2 i))
  let q : ℝ × Vec 2 := p - jointLatticeShift z
  have hq : q ∈ PeriodicSmooth.jointUnitCell := by
    simpa [q, z] using PeriodicSmooth.mem_jointUnitCell_normalize p
  have hpq : q + jointLatticeShift z = p := by
    dsimp [q, z]
    exact PeriodicSmooth.joint_normalize_add_shift p
  have hper := iteratedFDeriv_jointPeriodic hb.periodic n z q
  have hgp : g p = g q := by
    rw [← hpq]
    exact congrArg norm hper
  calc
    ‖iteratedFDeriv ℝ n F p‖ = g q := by rw [← hgp]
    _ ≤ C := hcell_bound q hq
    _ ≤ max C 0 := le_max_left _ _

end AVenhance.Infra.Flow
