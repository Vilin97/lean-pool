/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamClassicalReal
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification
public import Mathlib.Tactic

/-!
# Spectrum of the real free-beam realization

This file runs the compact-resolvent/Fredholm argument directly on the real Section 9 model.
It proves that every real spectral point is an eigenvalue, classifies the positive spectrum by
the free-beam characteristic equation, and obtains the source gap `{0} ∪ (500, ∞)`.
-/

@[expose] public section

open scoped InnerProductSpace ENNReal
open MeasureTheory TauCeti

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real

noncomputable section

/-! ## Compact variational resolvent -/

/-- The variational resolvent is the embedding composed with its adjoint. -/
theorem beamResolvent_eq :
    beamCoerciveFormData.resolvent =
      beamEmbed.comp (ContinuousLinearMap.adjoint beamEmbed) := by
  have h1 : beamCoerciveFormData.resolvent =
      beamCoerciveFormData.embed ∘L beamCoerciveFormData.solutionOperator := rfl
  have h2 : beamCoerciveFormData.solutionOperator =
      beamCoerciveFormData.formInverse ∘L
        ContinuousLinearMap.adjoint beamCoerciveFormData.embed := rfl
  have h3 : beamCoerciveFormData.formInverse = 1 := by
    rw [show beamCoerciveFormData.formInverse =
      Ring.inverse beamCoerciveFormData.formOperator from rfl]
    rw [show beamCoerciveFormData.formOperator = ContinuousLinearMap.id ℝ BeamV from rfl]
    exact Ring.inverse_one _
  rw [h1, h2, h3]
  rfl

/-- The real variational resolvent is compact. -/
theorem isCompactOperator_beamResolvent :
    IsCompactOperator beamCoerciveFormData.resolvent := by
  rw [beamResolvent_eq]
  exact isCompactOperator_beamEmbed.comp_clm (ContinuousLinearMap.adjoint beamEmbed)

/-- Invert a nonzero resolvent eigenvalue into a beam-operator eigenvalue. -/
theorem exists_beamOperator_apply_of_beamResolvent_smul {mu : ℝ} (hmu : mu ≠ 0)
    {u : BeamL2} (huv : beamCoerciveFormData.resolvent u = mu • u) :
    ∃ h : u ∈ beamOperator.domain,
      beamOperator ⟨u, h⟩ = (mu⁻¹ - 1) • u := by
  set R := beamCoerciveFormData.resolvent with hR
  have humem : u ∈ beamOperator.domain := by
    have hmem : u ∈ LinearMap.range ((R : BeamL2 →ₗ[ℝ] BeamL2)) := by
      refine ⟨mu⁻¹ • u, ?_⟩
      rw [show ((R : BeamL2 →ₗ[ℝ] BeamL2)) (mu⁻¹ • u) = R (mu⁻¹ • u) from rfl,
        map_smul, huv, smul_smul, inv_mul_cancel₀ hmu, one_smul]
    exact hmem
  refine ⟨humem, ?_⟩
  have hRmu : R (mu⁻¹ • u) = u := by
    rw [map_smul, huv, smul_smul, inv_mul_cancel₀ hmu, one_smul]
  have hshift : beamShiftedFormData.shiftedOperator ⟨u, humem⟩ =
      mu⁻¹ • u := by
    have happ := Abstract.inversePartialMap_apply_R R
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective (mu⁻¹ • u)
    have hsub : (⟨R (mu⁻¹ • u), LinearMap.mem_range_self _ _⟩ :
        beamShiftedFormData.shiftedOperator.domain) = ⟨u, humem⟩ := Subtype.ext hRmu
    exact (congrArg beamShiftedFormData.shiftedOperator hsub).symm.trans happ
  have h : beamOperator ⟨u, humem⟩ =
      beamShiftedFormData.shiftedOperator ⟨u, humem⟩ - u :=
    beamShiftedFormData.beamOperator_apply _
  rw [h, hshift, sub_smul, one_smul]

/-- A fixed vector of the resolvent is an affine zero mode. -/
theorem exists_affine_of_beamResolvent_eq_self {u : BeamL2}
    (huv : beamCoerciveFormData.resolvent u = u) :
    ∃ a b : ℝ, u = affineLp a b := by
  obtain ⟨humem, hbeam⟩ :=
    exists_beamOperator_apply_of_beamResolvent_smul (mu := 1) one_ne_zero
      (by simpa using huv)
  refine exists_affine_of_beamOperator_eq_zero (x := ⟨u, humem⟩) ?_
  rw [hbeam, inv_one, sub_self, zero_smul]

/-- Nonzero real eigenvalues of the variational resolvent are either the affine value `1` or
`(1 + beta^4)⁻¹` for a positive free-beam characteristic root. -/
theorem beamResolvent_eigenvalue_classify {mu : ℝ} (hmu : mu ≠ 0)
    {u : BeamL2} (hu0 : u ≠ 0)
    (huv : beamCoerciveFormData.resolvent u = mu • u) :
    mu = 1 ∨ ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧
      mu = (1 + beta ^ 4)⁻¹ := by
  obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu huv
  set nu : ℝ := mu⁻¹ - 1 with hnu
  have hnu_nonneg : 0 ≤ nu := by
    apply nonneg_of_beamOperator_eigen (x := ⟨u, humem⟩) hu0
    simpa [nu] using hbeam
  rcases eq_or_lt_of_le hnu_nonneg with hzero | hpos
  · left
    have h1 : mu⁻¹ = 1 := by
      rw [hnu] at hzero
      linarith
    exact inv_eq_one.mp h1
  · right
    have heig : beamOperator ⟨u, humem⟩ = nu • u := by
      simpa [nu] using hbeam
    obtain ⟨beta, hβ, hchar, hnueq⟩ :=
      exists_characteristic_of_eigen hpos (x := ⟨u, humem⟩) hu0 heig
    refine ⟨beta, hβ, hchar, ?_⟩
    have hmuinv : mu⁻¹ = 1 + beta ^ 4 := by
      rw [hnu] at hnueq
      linarith
    rw [← hmuinv, inv_inv]

/-! ## Fredholm bridge -/

/-- Every real spectral point of the real free beam is an eigenvalue. -/
theorem exists_eigenvector_of_mem_realSpectrum_beamOperator {lam : ℝ}
    (hlam : lam ∈ TauCeti.LinearPMap.realSpectrum beamOperator) :
    ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
      beamOperator x = lam • (x : BeamL2) := by
  by_contra hcon
  push Not at hcon
  set R := beamCoerciveFormData.resolvent with hRdef
  set c : ℝ := 1 + lam with hcdef
  have hunit : IsUnit ((1 : BeamL2 →L[ℝ] BeamL2) - c • R) := by
    by_cases hc : c = 0
    · rw [hc, zero_smul, sub_zero]
      exact isUnit_one
    · have hmu : c⁻¹ ≠ 0 := inv_ne_zero hc
      rcases isCompactOperator_beamResolvent.hasEigenvalue_or_mem_resolventSet hmu with
        hev | hres
      · exfalso
        obtain ⟨v, hvmem, hv0⟩ := hev.exists_hasEigenvector
        have hveq : R v = c⁻¹ • v := by
          have hv := hvmem
          simp only [Module.End.mem_genEigenspace_one] at hv
          exact hv
        obtain ⟨hvdom, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu hveq
        have hcc : c⁻¹⁻¹ - 1 = lam := by
          rw [inv_inv, hcdef]
          ring
        refine hcon ⟨v, hvdom⟩ hv0 ?_
        rw [← hcc]
        exact hbeam
      · have hres' := spectrum.mem_resolventSet_iff.mp hres
        have hkey : (1 : BeamL2 →L[ℝ] BeamL2) - c • R =
            c • (algebraMap ℝ (BeamL2 →L[ℝ] BeamL2) c⁻¹ - R) := by
          rw [smul_sub]
          congr 1
          rw [Algebra.algebraMap_eq_smul_one, smul_smul, mul_inv_cancel₀ hc, one_smul]
        rw [hkey]
        have hcu : IsUnit (algebraMap ℝ (BeamL2 →L[ℝ] BeamL2) c) :=
          IsUnit.map _ (isUnit_iff_ne_zero.mpr hc)
        have hprod := hcu.mul hres'
        rwa [show algebraMap ℝ (BeamL2 →L[ℝ] BeamL2) c *
              (algebraMap ℝ (BeamL2 →L[ℝ] BeamL2) c⁻¹ - R) =
            c • (algebraMap ℝ (BeamL2 →L[ℝ] BeamL2) c⁻¹ - R) from by
          rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]] at hprod
  obtain ⟨U, hU⟩ := hunit
  set S : BeamL2 →L[ℝ] BeamL2 := ↑U⁻¹ with hSdef
  have hcommU : Commute R ↑U := by
    rw [hU]
    change R * ((1 : BeamL2 →L[ℝ] BeamL2) - c • R) =
      ((1 : BeamL2 →L[ℝ] BeamL2) - c • R) * R
    rw [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc]
  have hSU : S * ↑U = 1 := U.inv_mul
  have hUS : (↑U : BeamL2 →L[ℝ] BeamL2) * S = 1 := U.mul_inv
  refine hlam ⟨R * S, ?_, ?_⟩
  · intro x
    have hz := Abstract.R_inversePartialMap_apply R
      beamCoerciveFormData.resolvent_isSelfAdjoint
      beamCoerciveFormData.resolvent_injective x
    set z : BeamL2 := beamShiftedFormData.shiftedOperator x with hzdef
    have hRz : R z = (x : BeamL2) := hz
    have hBx : beamOperator x - lam • (x : BeamL2) =
        (↑U : BeamL2 →L[ℝ] BeamL2) z := by
      have h1 : beamOperator x =
          beamShiftedFormData.shiftedOperator x - (x : BeamL2) :=
        beamShiftedFormData.beamOperator_apply x
      have hUz : ((1 : BeamL2 →L[ℝ] BeamL2) - c • R) z =
          z - c • (x : BeamL2) := by
        rw [sub_apply]
        rw [show ((1 : BeamL2 →L[ℝ] BeamL2)) z = z from rfl,
          show (c • R) z = c • (R z) from rfl, hRz]
      rw [h1, hU, hUz, hcdef]
      rw [add_smul, one_smul]
      abel
    calc
      (R * S) (beamOperator x - lam • (x : BeamL2)) =
          (R * S) ((↑U : BeamL2 →L[ℝ] BeamL2) z) := congrArg (R * S) hBx
      _ = R ((S * ↑U) z) := rfl
      _ = R z := by rw [hSU]; rfl
      _ = (x : BeamL2) := hRz
  · intro y
    have hmem : (R * S) y ∈ beamOperator.domain := by
      change R (S y) ∈ beamOperator.domain
      exact LinearMap.mem_range_self _ _
    refine ⟨hmem, ?_⟩
    have hshifted : beamShiftedFormData.shiftedOperator
        ⟨(R * S) y, hmem⟩ = S y := by
      have happ := Abstract.inversePartialMap_apply_R R
        beamCoerciveFormData.resolvent_isSelfAdjoint
        beamCoerciveFormData.resolvent_injective (S y)
      have hsub : (⟨R (S y), LinearMap.mem_range_self _ _⟩ :
          beamShiftedFormData.shiftedOperator.domain) = ⟨(R * S) y, hmem⟩ :=
        Subtype.ext rfl
      exact (congrArg beamShiftedFormData.shiftedOperator hsub).symm.trans happ
    have h1 : beamOperator ⟨(R * S) y, hmem⟩ =
        beamShiftedFormData.shiftedOperator ⟨(R * S) y, hmem⟩ - (R * S) y :=
      beamShiftedFormData.beamOperator_apply _
    have hfinal : S y - (R * S) y - lam • (R * S) y =
        ((↑U : BeamL2 →L[ℝ] BeamL2) * S) y := by
      rw [hU]
      rw [show (((1 : BeamL2 →L[ℝ] BeamL2) - c • R) * S) y =
          S y - c • (R (S y)) from by
        rw [sub_mul, one_mul]
        rfl]
      rw [show ((R * S) y : BeamL2) = R (S y) from rfl, hcdef]
      rw [add_smul, one_smul]
      abel
    calc
      beamOperator ⟨(R * S) y, hmem⟩ - lam • ((R * S) y) =
          beamShiftedFormData.shiftedOperator ⟨(R * S) y, hmem⟩ -
            (R * S) y - lam • ((R * S) y) := by rw [h1]
      _ = S y - (R * S) y - lam • (R * S) y := by rw [hshifted]
      _ = ((↑U : BeamL2 →L[ℝ] BeamL2) * S) y := hfinal
      _ = y := by rw [hUS]; rfl

/-- The real spectrum consists only of zero and characteristic fourth powers. -/
theorem realSpectrum_beamOperator_subset :
    TauCeti.LinearPMap.realSpectrum beamOperator ⊆
      {0} ∪ {lam : ℝ | ∃ beta : ℝ,
        0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4} := by
  intro lam hlam
  obtain ⟨x, hx0, heig⟩ := exists_eigenvector_of_mem_realSpectrum_beamOperator hlam
  rcases eq_or_lt_of_le (nonneg_of_beamOperator_eigen hx0 heig) with h0 | hpos
  · exact Or.inl (Set.mem_singleton_iff.mpr h0.symm)
  · exact Or.inr (exists_characteristic_of_eigen hpos hx0 heig)

/-- Source spectral gap: every nonzero spectral point of the real free beam exceeds `500`. -/
theorem realSpectrum_beamOperator_subset_gap :
    TauCeti.LinearPMap.realSpectrum beamOperator ⊆ ({0} : Set ℝ) ∪ Set.Ioi 500 := by
  intro lam hlam
  rcases realSpectrum_beamOperator_subset hlam with h0 | ⟨beta, hβ, hchar, hlameq⟩
  · exact Or.inl h0
  · refine Or.inr ?_
    rw [Set.mem_Ioi, hlameq]
    exact Classical.five_hundred_lt_pow_four_of_characteristic_eq_zero hβ hchar

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
