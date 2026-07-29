/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.BilinearForm.DualLattice

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module Submodule
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E]

theorem innerBilin_nondegenerate [InnerProductSpace ℝ E] :
    (innerₗ E).Nondegenerate := by
  constructor
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)
  · intro x hx
    exact inner_self_eq_zero.mp (hx x)

/-- A dual real basis used in the Odlyzko-bound argument. -/
noncomputable def dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℝ E :=
  LinearMap.BilinForm.dualBasis (innerₗ E) innerBilin_nondegenerate
    (b.ofZLatticeBasis ℝ L)

theorem inner_dualRealBasis_apply [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) (x : E) :
    inner ℝ (dualRealBasis L b i) x =
      (b.ofZLatticeBasis ℝ L).repr x i := by
  change (innerₗ E) (dualRealBasis L b i) x = _
  simp [dualRealBasis, LinearMap.BilinForm.dualBasis,
    Basis.coe_dualBasis]

/-- A dual lattice used in the Odlyzko-bound argument. -/
noncomputable def dualLattice [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) : Submodule ℤ E :=
  LinearMap.BilinForm.dualSubmodule (innerₗ E) L

theorem mem_dualLattice_iff [InnerProductSpace ℝ E]
    (L : Submodule ℤ E) (y : E) :
    y ∈ dualLattice L ↔ ∀ x : L, ∃ n : ℤ, inner ℝ y (x : E) = n := by
  constructor
  · intro hy x
    obtain ⟨n, hn⟩ := Submodule.mem_one.mp (hy x x.2)
    exact ⟨n, hn.symm⟩
  · intro hy x hx
    obtain ⟨n, hn⟩ := hy ⟨x, hx⟩
    simp_all

theorem span_range_dualRealBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    span ℤ (Set.range (dualRealBasis L b)) = dualLattice L := by
  unfold dualLattice dualRealBasis
  calc
    span ℤ (Set.range (LinearMap.BilinForm.dualBasis (innerₗ E)
      innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L))) =
        LinearMap.BilinForm.dualSubmodule (innerₗ E)
          (span ℤ (Set.range (b.ofZLatticeBasis ℝ L))) :=
      (LinearMap.BilinForm.dualSubmodule_span_of_basis
        (innerₗ E) innerBilin_nondegenerate (b.ofZLatticeBasis ℝ L)).symm
    _ = LinearMap.BilinForm.dualSubmodule (innerₗ E) L := by
      rw [b.ofZLatticeBasis_span ℝ]

instance dualLattice.instDiscreteTopology [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    DiscreteTopology (dualLattice L) := by
  classical
  rw [← span_range_dualRealBasis L (Free.chooseBasis ℤ L)]
  infer_instance

/-- A dual lattice basis used in the Odlyzko-bound argument. -/
noncomputable def dualLatticeBasis [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L) :
    Basis ι ℤ (dualLattice L) :=
  ((dualRealBasis L b).restrictScalars ℤ).map
    (LinearEquiv.ofEq _ _ (span_range_dualRealBasis L b))

@[simp]
theorem dualLatticeBasis_apply_coe [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
    {ι : Type*} [Finite ι] [DecidableEq ι] (b : Basis ι ℤ L)
    (i : ι) :
    ((dualLatticeBasis L b i : dualLattice L) : E) =
      dualRealBasis L b i := by
  rw [dualLatticeBasis, Basis.map_apply]
  simp

end NumberField.Odlyzko
