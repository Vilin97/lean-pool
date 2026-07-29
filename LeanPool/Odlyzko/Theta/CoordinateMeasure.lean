/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.Theta.FourierCoefficientUnfolding
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Module MeasureTheory

namespace NumberField.Odlyzko

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem map_ofZLatticeBasis_equivFun_symm_volume
    (b : Basis ι ℤ L) :
    Measure.map (b.ofZLatticeBasis ℝ L).equivFun.symm volume =
      (b.ofZLatticeBasis ℝ L).addHaar := by
  classical
  let e : (ι → ℝ) ≃L[ℝ] E :=
    LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm
  have hcoord : (Pi.basisFun ℝ ι).addHaar =
      (volume : Measure (ι → ℝ)) := by
    rw [Basis.addHaar_def, Basis.parallelepiped_basisFun,
      addHaarMeasure_eq_volume_pi]
  rw [← hcoord]
  change Measure.map e (Pi.basisFun ℝ ι).addHaar =
    (b.ofZLatticeBasis ℝ L).addHaar
  rw [Basis.map_addHaar (Pi.basisFun ℝ ι) e]
  congr 1
  ext i
  simp [e]

omit [DecidableEq ι] in
theorem covolume_eq_volumeReal_parallelepiped
    (b : Basis ι ℤ L) :
    ZLattice.covolume L =
      volume.real
        ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) := by
  classical
  rw [ZLattice.covolume_eq_det_mul_measureReal L volume b
    (b.ofZLatticeBasis ℝ L)]
  have hfun :
      ((fun x : L ↦ (x : E)) ∘ b) =
        (b.ofZLatticeBasis ℝ L : ι → E) := by
    funext i
    simp
  rw [hfun, Basis.det_self, abs_one, one_mul]
  exact measureReal_congr
    (ZSpan.fundamentalDomain_ae_parallelepiped
      (b.ofZLatticeBasis ℝ L) volume)

omit [DecidableEq ι] in
theorem volume_parallelepiped_ofZLatticeBasis
    (b : Basis ι ℤ L) :
    volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) =
      ENNReal.ofReal (ZLattice.covolume L) := by
  classical
  have hfinite :
      volume ((b.ofZLatticeBasis ℝ L).parallelepiped : Set E) < ⊤ :=
    (b.ofZLatticeBasis ℝ L).parallelepiped.isCompact.measure_lt_top
  rw [covolume_eq_volumeReal_parallelepiped L b]
  exact (ENNReal.ofReal_toReal hfinite.ne).symm

omit [DecidableEq ι] in
theorem addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume
    (b : Basis ι ℤ L) :
    (b.ofZLatticeBasis ℝ L).addHaar =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ • volume := by
  classical
  rw [Basis.addHaar_eq_iff]
  rw [Measure.smul_apply,
    volume_parallelepiped_ofZLatticeBasis L b]
  have hc : Real.toNNReal (ZLattice.covolume L) ≠ 0 := by
    rw [ne_eq, Real.toNNReal_eq_zero]
    exact not_le_of_gt (ZLattice.covolume_pos L)
  change
    (↑((Real.toNNReal (ZLattice.covolume L))⁻¹) : ENNReal) *
        ENNReal.ofReal (ZLattice.covolume L) = 1
  rw [ENNReal.coe_inv hc, ENNReal.ofNNReal_toNNReal]
  exact ENNReal.inv_mul_cancel
    (ENNReal.ofReal_ne_zero_iff.mpr (ZLattice.covolume_pos L))
    ENNReal.ofReal_ne_top

omit [DecidableEq ι] in
theorem integral_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) (f : E → ℂ) :
    (∫ x : ι → ℝ,
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) =
      (Real.toNNReal (ZLattice.covolume L))⁻¹ •
        ∫ y : E, f y := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change (∫ x : ι → ℝ, f (e x)) = _
  rw [← integral_map_equiv (μ := volume) e f]
  change (∫ y : E, f y ∂Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume) = _
  rw [map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b,
    integral_smul_nnreal_measure]

omit [DecidableEq ι] in
theorem integrable_comp_ofZLatticeBasis_equivFun_symm
    (b : Basis ι ℤ L) {f : E → ℂ} (hf : Integrable f) :
    Integrable
      (fun x : ι → ℝ ↦
        f ((b.ofZLatticeBasis ℝ L).equivFun.symm x)) := by
  classical
  let e : (ι → ℝ) ≃ᵐ E :=
    (LinearEquiv.toContinuousLinearEquiv
      (b.ofZLatticeBasis ℝ L).equivFun.symm).toHomeomorph.toMeasurableEquiv
  change Integrable (f ∘ e)
  rw [← integrable_map_equiv e f]
  change Integrable f (Measure.map
    (b.ofZLatticeBasis ℝ L).equivFun.symm volume)
  rw [
    map_ofZLatticeBasis_equivFun_symm_volume L b,
    addHaar_ofZLatticeBasis_eq_inv_covolume_smul_volume L b]
  exact hf.smul_measure_nnreal

end NumberField.Odlyzko
