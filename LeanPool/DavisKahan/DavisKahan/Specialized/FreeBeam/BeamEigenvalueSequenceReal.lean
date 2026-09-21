/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTrialReal
import LeanPool.DavisKahan.ForTauCeti.MeasureTheory.LpInfiniteDimensional
import LeanPool.DavisKahan.ForTauCeti.Order.DiscreteEnumeration

/-!
# The real free beam's increasing eigenvalue sequence

The real Section 9 beam has compact injective variational resolvent on an infinite-dimensional
real Hilbert space.  Its positive eigenvalues are unbounded and locally finite, hence admit the
strictly increasing enumeration printed by Davis--Kahan.  The full real spectrum is exactly
zero together with those positive eigenvalues.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model
namespace Real

noncomputable section

/-- The paper's real `L²(0,1)` space is infinite-dimensional. -/
theorem not_finiteDimensional_beamL2 : ¬ FiniteDimensional ℝ BeamL2 :=
  TauCeti.not_finiteDimensional_lpTwo_unitIocMeasure (𝕜 := ℝ)

/-- The injective variational resolvent has trivial zero eigenspace. -/
theorem eigenspace_beamResolvent_zero_eq_bot :
    Module.End.eigenspace beamCoerciveFormData.resolvent.toLinearMap 0 = ⊥ := by
  rw [Module.End.eigenspace_zero]
  exact LinearMap.ker_eq_bot.mpr beamCoerciveFormData.resolvent_injective

/-- The real beam has a positive eigenvalue above every prescribed bound. -/
theorem exists_pos_eigenpair_beamOperator_gt (M : ℝ) :
    ∃ (lam : ℝ) (x : beamOperator.domain), M < lam ∧ 0 < lam ∧
      (x : BeamL2) ≠ 0 ∧ beamOperator x = lam • (x : BeamL2) := by
  set N : ℝ := max M 0 with hNdef
  have hMN : M ≤ N := le_max_left _ _
  have hN0 : (0 : ℝ) ≤ N := le_max_right _ _
  have hNpos : (0 : ℝ) < 1 + N := by linarith
  have hc : (0 : ℝ) < (1 + N)⁻¹ := inv_pos.mpr hNpos
  have hNinv : (1 + N)⁻¹ * (1 + N) = 1 := inv_mul_cancel₀ hNpos.ne'
  obtain ⟨mu, hev, hmu0, hmunorm⟩ :=
    TauCeti.exists_hasEigenvalue_norm_lt isCompactOperator_beamResolvent
      beamCoerciveFormData.resolvent_isSelfAdjoint eigenspace_beamResolvent_zero_eq_bot
      not_finiteDimensional_beamL2 hc
  obtain ⟨u, hu, hu0⟩ := hev.exists_hasEigenvector
  have hRu : beamCoerciveFormData.resolvent u = mu • u := Module.End.mem_eigenspace_iff.mp hu
  rcases beamResolvent_eigenvalue_classify hmu0 hu0 hRu with
    h1 | ⟨beta, hbeta, hchar, hmueq⟩
  · exfalso
    rw [h1, Real.norm_eq_abs, abs_one] at hmunorm
    have hstep : 1 * (1 + N) < (1 + N)⁻¹ * (1 + N) :=
      mul_lt_mul_of_pos_right hmunorm hNpos
    rw [hNinv, one_mul] at hstep
    linarith
  · have hb4 : (0 : ℝ) < 1 + beta ^ 4 := by positivity
    have hbinv : (1 + beta ^ 4)⁻¹ * (1 + beta ^ 4) = 1 := inv_mul_cancel₀ hb4.ne'
    have hbpos : (0 : ℝ) < (1 + beta ^ 4)⁻¹ := inv_pos.mpr hb4
    have hnorm : ‖mu‖ = (1 + beta ^ 4)⁻¹ := by
      rw [hmueq, Real.norm_eq_abs, abs_of_pos hbpos]
    rw [hnorm] at hmunorm
    have hxB : (1 + beta ^ 4)⁻¹ * (1 + N) < 1 := by
      have hstep := mul_lt_mul_of_pos_right hmunorm hNpos
      rwa [hNinv] at hstep
    have hAB : (1 + N) < 1 + beta ^ 4 :=
      lt_of_mul_lt_mul_left (by rw [hbinv]; exact hxB) (le_of_lt hbpos)
    have hkey : M < beta ^ 4 := lt_of_le_of_lt hMN (by linarith)
    have hb4pos : (0 : ℝ) < beta ^ 4 := by positivity
    obtain ⟨humem, hbeam⟩ := exists_beamOperator_apply_of_beamResolvent_smul hmu0 hRu
    have hinv : mu⁻¹ - 1 = beta ^ 4 := by
      rw [hmueq, inv_inv]
      ring
    refine ⟨beta ^ 4, ⟨u, humem⟩, hkey, hb4pos, hu0, ?_⟩
    rw [hbeam, hinv]

/-- A real spectral point above every bound, necessarily above `500`. -/
theorem exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator (M : ℝ) :
    ∃ alpha : ℝ, M < alpha ∧ 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨lam, x, hM, hlam, hx0, heig⟩ := exists_pos_eigenpair_beamOperator_gt M
  exact ⟨lam, hM, eigenvalue_gt_five_hundred hlam hx0 heig,
    TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
      (x := x) hx0 heig⟩

/-- The positive real spectrum is nonempty. -/
theorem exists_five_hundred_lt_mem_realSpectrum_beamOperator :
    ∃ alpha : ℝ, 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨alpha, -, h500, hmem⟩ :=
    exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator 500
  exact ⟨alpha, h500, hmem⟩

/-- The positive real spectrum contains a nonzero point. -/
theorem exists_mem_realSpectrum_beamOperator_ne_zero :
    ∃ alpha : ℝ, alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator ∧ alpha ≠ 0 := by
  obtain ⟨alpha, h500, hmem⟩ := exists_five_hundred_lt_mem_realSpectrum_beamOperator
  exact ⟨alpha, hmem, by linarith⟩

/-- The real spectrum is unbounded above. -/
theorem not_bddAbove_realSpectrum_beamOperator : ¬ BddAbove (TauCeti.LinearPMap.realSpectrum beamOperator) := by
  rintro ⟨b, hb⟩
  obtain ⟨alpha, hM, -, hmem⟩ := exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator b
  exact absurd (hb hmem) (not_le.mpr hM)

/-! ## Positive point spectrum -/

/-- Set of positive real beam eigenvalues. -/
def beamEigenvalues : Set ℝ :=
  {lam : ℝ | 0 < lam ∧ ∃ x : beamOperator.domain, (x : BeamL2) ≠ 0 ∧
    beamOperator x = lam • (x : BeamL2)}

/-- Every positive characteristic root contributes its fourth power to the real beam point
spectrum. -/
theorem pow_four_mem_beamEigenvalues_of_characteristic {beta : ℝ} (hbeta : 0 < beta)
    (hroot : characteristic beta = 0) : beta ^ 4 ∈ beamEigenvalues := by
  refine ⟨by positivity, ?_⟩
  exact exists_eigenpair_of_characteristic hbeta hroot

/-- The positive real beam eigenvalues are exactly the fourth powers of the positive roots of
the free-beam characteristic equation. -/
theorem beamEigenvalues_eq_characteristicFourthPowers :
    beamEigenvalues =
      {lam : ℝ | ∃ beta : ℝ, 0 < beta ∧ characteristic beta = 0 ∧ lam = beta ^ 4} := by
  ext lam
  constructor
  · intro hlam
    obtain ⟨hpos, x, hx0, heig⟩ := hlam
    exact exists_characteristic_of_eigen hpos hx0 heig
  · rintro ⟨beta, hbeta, hroot, rfl⟩
    exact pow_four_mem_beamEigenvalues_of_characteristic hbeta hroot

/-- Every listed beam eigenvalue exceeds five hundred. -/
theorem five_hundred_lt_of_mem_beamEigenvalues {lam : ℝ} (hlam : lam ∈ beamEigenvalues) :
    500 < lam := by
  obtain ⟨hpos, x, hx0, heig⟩ := hlam
  exact eigenvalue_gt_five_hundred hpos hx0 heig

/-- Every listed beam eigenvalue is in the real spectrum of the beam
operator. -/
theorem mem_realSpectrum_of_mem_beamEigenvalues {lam : ℝ} (hlam : lam ∈ beamEigenvalues) :
    lam ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨-, x, hx0, heig⟩ := hlam
  exact TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
    (x := x) hx0 heig

/-- Invert a beam eigenpair back into an eigenpair of the variational resolvent. -/
theorem beamResolvent_apply_of_beamOperator_eigen {lam : ℝ} (hlam : 0 < lam)
    {x : beamOperator.domain} (heig : beamOperator x = lam • (x : BeamL2)) :
    beamCoerciveFormData.resolvent (x : BeamL2) = (1 + lam)⁻¹ • (x : BeamL2) := by
  have hne : 1 + lam ≠ 0 := by linarith
  have hz := Abstract.R_inversePartialMap_apply beamCoerciveFormData.resolvent
    beamCoerciveFormData.resolvent_isSelfAdjoint beamCoerciveFormData.resolvent_injective x
  have hsplit : beamShiftedFormData.shiftedOperator x =
      beamOperator x + (x : BeamL2) := shifted_apply_of_beam
  have hshift : beamShiftedFormData.shiftedOperator x =
      (1 + lam) • (x : BeamL2) := by
    rw [hsplit, heig, add_smul, one_smul]
    abel
  have hRx : (1 + lam) • beamCoerciveFormData.resolvent (x : BeamL2) = (x : BeamL2) := by
    rw [← map_smul, ← hshift]
    exact hz
  have hcancel := congrArg (fun v : BeamL2 => (1 + lam)⁻¹ • v) hRx
  simp only [smul_smul, inv_mul_cancel₀ hne, one_smul] at hcancel
  exact hcancel

/-- Finitely many positive eigenvalues lie below any fixed bound. -/
theorem finite_beamEigenvalues_inter_Iic (M : ℝ) :
    (beamEigenvalues ∩ Set.Iic M).Finite := by
  rcases le_or_gt M 0 with hM | hM
  · refine Set.Finite.subset Set.finite_empty ?_
    rintro lam ⟨⟨hpos, -⟩, hle⟩
    exact absurd (lt_of_lt_of_le hpos hle) (not_lt.mpr hM)
  · have hMpos : (0 : ℝ) < 1 + M := by linarith
    have hc : (0 : ℝ) < (1 + M)⁻¹ := inv_pos.mpr hMpos
    set F : ℝ → ℝ := fun lam => (1 + lam)⁻¹ with hFdef
    have hfinS := TauCeti.finite_setOf_hasEigenvalue_le_norm
      isCompactOperator_beamResolvent beamCoerciveFormData.resolvent_isSelfAdjoint hc
    have himg : F '' (beamEigenvalues ∩ Set.Iic M) ⊆
        {mu : ℝ | Module.End.HasEigenvalue beamCoerciveFormData.resolvent.toLinearMap mu ∧
          (1 + M)⁻¹ ≤ ‖mu‖} := by
      rintro _ ⟨lam, ⟨⟨hpos, x, hx0, heig⟩, hle⟩, rfl⟩
      have hlpos : (0 : ℝ) < 1 + lam := by linarith
      have hres := beamResolvent_apply_of_beamOperator_eigen hpos heig
      have hmem : (x : BeamL2) ∈
          Module.End.eigenspace beamCoerciveFormData.resolvent.toLinearMap (F lam) :=
        Module.End.mem_eigenspace_iff.mpr hres
      refine ⟨?_, ?_⟩
      · rw [Module.End.hasEigenvalue_iff]
        intro hbot
        exact hx0 (Submodule.mem_bot ℝ |>.mp (hbot ▸ hmem))
      · have hFnorm : ‖F lam‖ = (1 + lam)⁻¹ := by
          rw [hFdef, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hlpos)]
        rw [hFnorm]
        have hden : (1 : ℝ) + lam ≤ 1 + M := by
          simpa [add_comm] using (add_le_add_right hle (1 : ℝ))
        simpa only [one_div] using one_div_le_one_div_of_le hlpos hden
    have hinj : Set.InjOn F (beamEigenvalues ∩ Set.Iic M) := by
      rintro a ⟨⟨ha, -⟩, -⟩ b ⟨⟨hb, -⟩, -⟩ hab
      rw [hFdef] at hab
      have hsum : (1 : ℝ) + a = 1 + b := by
        have h := congrArg (fun t : ℝ => t⁻¹) hab
        simpa only [inv_inv] using h
      linarith
    exact Set.Finite.of_finite_image (hfinS.subset himg) hinj

/-- Positive eigenvalues occur above every real bound. -/
theorem exists_lt_mem_beamEigenvalues (M : ℝ) : ∃ lam ∈ beamEigenvalues, M < lam := by
  obtain ⟨lam, x, hM, hpos, hx0, heig⟩ := exists_pos_eigenpair_beamOperator_gt M
  exact ⟨lam, ⟨hpos, x, hx0, heig⟩, hM⟩

/-! ## Full real spectrum and enumeration -/

/-- A strictly increasing unbounded sequence of real spectral points above `500`. -/
theorem exists_strictMono_mem_realSpectrum_beamOperator :
    ∃ f : ℕ → ℝ, StrictMono f ∧ ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  classical
  set g : ℝ → ℝ := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose with hgdef
  have hg1 : ∀ M : ℝ, M < g M := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.1
  have hg2 : ∀ M : ℝ, 500 < g M := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.2.1
  have hg3 : ∀ M : ℝ, g M ∈ TauCeti.LinearPMap.realSpectrum beamOperator := fun M =>
    (exists_lt_five_hundred_lt_mem_realSpectrum_beamOperator M).choose_spec.2.2
  refine ⟨fun n => Nat.rec (motive := fun _ => ℝ) (g 500) (fun _ prev => g prev) n, ?_, ?_⟩
  · exact strictMono_nat_of_lt_succ fun _ => hg1 _
  · intro n
    cases n with
    | zero => exact ⟨hg2 500, hg3 500⟩
    | succ k => exact ⟨hg2 _, hg3 _⟩

/-- Zero belongs to the real spectrum through the nonzero constant mode. -/
theorem zero_mem_realSpectrum_beamOperator : (0 : ℝ) ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨hmem, hzero⟩ := beamOperator_affine_mem_and_zero 1 0
  set x : beamOperator.domain := ⟨affineLp 1 0, hmem⟩ with hxdef
  have hne : (x : BeamL2) ≠ 0 := by
    rw [hxdef]
    simpa [affineLp] using beamOneLp_ne_zero
  have heig : beamOperator x = (0 : ℝ) • (x : BeamL2) := by
    rw [hzero, zero_smul]
  exact TauCeti.LinearPMap.mem_realSpectrum_of_eigenvector (A := beamOperator)
    (x := x) hne heig

/-- The real spectrum is exactly zero together with the positive point spectrum. -/
theorem realSpectrum_beamOperator_eq_insert_zero :
    TauCeti.LinearPMap.realSpectrum beamOperator = insert 0 beamEigenvalues := by
  apply Set.Subset.antisymm
  · intro lam hlam
    obtain ⟨x, hx0, heig⟩ := exists_eigenvector_of_mem_realSpectrum_beamOperator hlam
    rcases eq_or_lt_of_le (nonneg_of_beamOperator_eigen hx0 heig) with h0 | hpos
    · exact Set.mem_insert_iff.mpr (Or.inl h0.symm)
    · exact Set.mem_insert_iff.mpr (Or.inr ⟨hpos, x, hx0, heig⟩)
  · intro lam hlam
    rcases Set.mem_insert_iff.mp hlam with rfl | hlam'
    · exact zero_mem_realSpectrum_beamOperator
    · exact mem_realSpectrum_of_mem_beamEigenvalues hlam'

/-- The full real spectrum is finite below every fixed bound. -/
theorem finite_realSpectrum_beamOperator_inter_Iic (M : ℝ) :
    (TauCeti.LinearPMap.realSpectrum beamOperator ∩ Set.Iic M).Finite := by
  refine Set.Finite.subset (Set.Finite.insert 0 (finite_beamEigenvalues_inter_Iic M)) ?_
  rw [realSpectrum_beamOperator_eq_insert_zero]
  rintro lam ⟨hlam, hle⟩
  rcases Set.mem_insert_iff.mp hlam with rfl | hlam'
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_iff.mpr (Or.inr ⟨hlam', hle⟩)

/-- Positive beam eigenvalues are order-isomorphic to `Nat`. -/
theorem nonempty_orderIso_nat_beamEigenvalues : Nonempty (↥beamEigenvalues ≃o ℕ) :=
  TauCeti.nonempty_orderIso_nat_of_unbounded_of_finite_inter_Iic
    exists_lt_mem_beamEigenvalues finite_beamEigenvalues_inter_Iic

/-- Davis--Kahan's printed `alpha_3 < alpha_4 < ...` as an exact enumeration. -/
theorem exists_strictMono_range_eq_beamEigenvalues :
    ∃ f : ℕ → ℝ, StrictMono f ∧ Set.range f = beamEigenvalues ∧
      ∀ n, 500 < f n ∧ f n ∈ TauCeti.LinearPMap.realSpectrum beamOperator := by
  obtain ⟨f, hmono, hrange⟩ :=
    TauCeti.exists_strictMono_range_eq_of_unbounded_of_finite_inter_Iic
      exists_lt_mem_beamEigenvalues finite_beamEigenvalues_inter_Iic
  refine ⟨f, hmono, hrange, fun n => ?_⟩
  have hmem : f n ∈ beamEigenvalues := by
    rw [← hrange]
    exact Set.mem_range_self n
  exact ⟨five_hundred_lt_of_mem_beamEigenvalues hmem,
    mem_realSpectrum_of_mem_beamEigenvalues hmem⟩

/-- There are infinitely many real spectral points above `500`. -/
theorem infinite_five_hundred_lt_mem_realSpectrum_beamOperator :
    {alpha : ℝ | 500 < alpha ∧ alpha ∈ TauCeti.LinearPMap.realSpectrum beamOperator}.Infinite := by
  obtain ⟨f, hf, hmem⟩ := exists_strictMono_mem_realSpectrum_beamOperator
  exact Set.infinite_of_injective_forall_mem hf.injective hmem

end

end Real
end Model
end FreeBeam
end DavisKahan
end TauCeti
