/-
Copyright (c) 2026 David Muñoz-Lahoz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Muñoz-Lahoz
-/

module

public import LeanPool.OrderClosures.BanLat.Normed
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.Lattice


/-!
# `C(K, ℝ)` as a Banach lattice

For a compact topological space `K`, the space `C(K, ℝ)` of continuous
real-valued functions equipped with the supremum norm and the pointwise order
is a Banach lattice.
-/

@[expose] public section

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-! ### Lattice and order structure

Mathlib provides `Lattice C(K, ℝ)` (pointwise, via
`ContinuousMap.instLatticeOfTopologicalLattice`) and `IsOrderedAddMonoid C(K, ℝ)`
(via `ContinuousMap.instIsOrderedAddMonoid`). The norm comes from
`ContinuousMap.instNormedAddCommGroup`.
-/

/-! ### Vector lattice -/

/-- `C(K, ℝ)` is a vector lattice: a real module whose positive cone is closed
under scalar multiplication by non-negative reals. -/
noncomputable instance instVectorLatticeCofK : VectorLattice C(K, ℝ) where
  smul_le_smul_of_nonneg_left {a} ha {b₁ b₂} hb := by
    rw [ContinuousMap.le_def] at hb ⊢
    intro x; simp only [ContinuousMap.smul_apply]
    exact smul_le_smul_of_nonneg_left (hb x) ha

/-! ### Normed vector lattice -/

/-- The sup norm on `C(K, ℝ)` is solid: `|f| ≤ |g|` pointwise implies
`‖f‖ ≤ ‖g‖`. -/
instance instHasSolidNormCofK : HasSolidNorm C(K, ℝ) where
  solid {f g} h := by
    simp only [ContinuousMap.norm_eq_iSup_norm]
    apply ciSup_mono ⟨‖g‖, Set.forall_mem_range.mpr
      (fun x => ContinuousMap.norm_coe_le_norm g x)⟩
    intro x
    have := ContinuousMap.le_def.mp h x
    rw [ContinuousMap.abs_apply, ContinuousMap.abs_apply] at this
    exact HasSolidNorm.solid this

/-- `C(K, ℝ)` is a normed vector lattice. -/
noncomputable instance instNormedVectorLatticeCofK :
    NormedVectorLattice C(K, ℝ) where

/-! ### Banach lattice -/

/-- `C(K, ℝ)` is a Banach lattice: a complete normed vector lattice. -/
noncomputable instance instBanachLatticeCofK : BanachLattice C(K, ℝ) where
