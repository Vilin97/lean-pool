/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.ThetaSeries

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module
open scoped RealInnerProductSpace

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A lattice point used in the Odlyzko-bound argument. -/
noncomputable def latticePoint (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  (b.equivFun.symm n : L)

/-- A dual lattice point used in the Odlyzko-bound argument. -/
noncomputable def dualLatticePoint (b : Basis ι ℤ L) (n : ι → ℤ) : E :=
  ((dualLatticeBasis L b).equivFun.symm n : dualLattice L)

theorem inner_dualLatticePoint_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) (n : ι → ℤ) (x : ι → ℝ) :
    inner ℝ (dualLatticePoint L b n)
        ((b.ofZLatticeBasis ℝ L).equivFun.symm x) =
      ∑ i, (n i : ℝ) * x i := by
  rw [dualLatticePoint, Basis.equivFun_symm_apply]
  have hn :
      ((↑(∑ i, n i • dualLatticeBasis L b i) :
          dualLattice L) : E) =
        ∑ i, (n i : ℝ) • dualRealBasis L b i := by
    change (dualLattice L).subtype
      (∑ i, n i • dualLatticeBasis L b i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_zsmul]
    have hd :
        (dualLattice L).subtype (dualLatticeBasis L b i) =
          dualRealBasis L b i :=
      dualLatticeBasis_apply_coe L b i
    rw [hd]
    exact (Int.cast_smul_eq_zsmul ℝ (n i)
      (dualRealBasis L b i)).symm
  rw [hn, sum_inner]
  have hrepr (i : ι) :
      (b.ofZLatticeBasis ℝ L).repr
          ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i := by
    change (b.ofZLatticeBasis ℝ L).equivFun
      ((b.ofZLatticeBasis ℝ L).equivFun.symm x) i = x i
    rw [LinearEquiv.apply_symm_apply]
  simp_rw [real_inner_smul_left,
    inner_dualRealBasis_apply, hrepr]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [DiscreteTopology ↥L] [IsZLattice ℝ L] [DecidableEq ι] in
theorem latticeTheta_eq_tsum_coordinates
    (b : Basis ι ℤ L) (a : ℝ) :
    latticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (latticePoint L b n) := by
  symm
  simpa [latticeTheta, latticePoint] using
    (Equiv.tsum_eq b.equivFun.toEquiv.symm
      (fun x : L ↦ latticeGaussian a (x : E)))

theorem dualLatticeTheta_eq_tsum_coordinates
    (b : Basis ι ℤ L) (a : ℝ) :
    dualLatticeTheta L a =
      ∑' n : ι → ℤ, latticeGaussian a (dualLatticePoint L b n) := by
  symm
  simpa [dualLatticeTheta, latticeTheta, dualLatticePoint] using
    (Equiv.tsum_eq (dualLatticeBasis L b).equivFun.toEquiv.symm
      (fun x : dualLattice L ↦ latticeGaussian a (x : E)))

end NumberField.Odlyzko
