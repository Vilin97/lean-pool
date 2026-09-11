/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.Basic

/-! Local residue maps for height-one primes of Dedekind domains. -/

@[expose] public section

open scoped nonZeroDivisors WithZero

noncomputable section

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- The residue map from the valuation ring at a height-one prime. -/
noncomputable def residueHom (v : HeightOneSpectrum R) :
    valuationSubringAtPrime K v →+* v.asIdeal.ResidueField :=
  IsLocalization.lift (S := valuationSubringAtPrime K v)
    (g := algebraMap R v.asIdeal.ResidueField)
    fun y : v.asIdeal.primeCompl => isUnit_iff_ne_zero.mpr <| by
      rw [ne_eq, Ideal.algebraMap_residueField_eq_zero]
      exact Ideal.mem_primeCompl_iff.mp y.property

/-- An element has zero residue exactly when its valuation is strictly less than one. -/
theorem residueHom_eq_zero_iff (v : HeightOneSpectrum R)
    (z : valuationSubringAtPrime K v) :
    residueHom (K := K) v z = 0 ↔ v.valuation K (z : K) < 1 := by
  obtain ⟨n, d, hnd⟩ := IsLocalization.exists_mk'_eq v.asIdeal.primeCompl z
  rw [← hnd, residueHom, IsLocalization.lift_mk']
  simp only [mul_eq_zero, Units.ne_zero, or_false]
  rw [Ideal.algebraMap_residueField_eq_zero]
  rw [← valuation_lt_one_iff_mem (K := K) v]
  rw [show (↑(IsLocalization.mk' (valuationSubringAtPrime K v) n d) : K) =
      algebraMap R K n / algebraMap R K d by
    have hd0 : (d : R) ≠ 0 := by
      intro hd
      exact (Ideal.mem_primeCompl_iff.mp d.property) (hd ▸ v.asIdeal.zero_mem)
    have hdK : algebraMap R K (d : R) ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective R K).ne hd0
    apply (eq_div_iff hdK).2
    have h := congrArg (fun y : valuationSubringAtPrime K v => (y : K))
      (IsLocalization.mk'_spec (valuationSubringAtPrime K v) n d)
    change (↑(IsLocalization.mk' (valuationSubringAtPrime K v) n d) : K) *
      algebraMap R K d = algebraMap R K n at h
    exact h]
  rw [(v.valuation K).map_div]
  have hvd : v.valuation K (algebraMap R K d) = 1 :=
    (valuation_eq_one_iff_notMem (K := K) (v := v)).2
      (Ideal.mem_primeCompl_iff.mp d.property)
  rw [hvd, div_one]

/-- The localization at a height-one prime is algebra-equivalent to its valuation subring. -/
noncomputable def localizationAlgEquiv (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal ≃ₐ[R] valuationSubringAtPrime K v :=
  IsLocalization.algEquiv v.asIdeal.primeCompl (Localization.AtPrime v.asIdeal)
    (valuationSubringAtPrime K v)

/-- `residueHom` on a localized fraction agrees with the quotient map. -/
theorem residueHom_mk' (v : HeightOneSpectrum R) (n : R) (d : v.asIdeal.primeCompl) :
    residueHom (K := K) v (IsLocalization.mk' (valuationSubringAtPrime K v) n d) =
      algebraMap R v.asIdeal.ResidueField n *
        (algebraMap R v.asIdeal.ResidueField (d : R))⁻¹ := by
  dsimp [residueHom]
  simp [IsLocalization.lift_mk', IsUnit.coe_liftRight]

/-- `residueHom` on a localized fraction agrees with the residue map on `AtPrime`. -/
theorem residueHom_mk'_residue (v : HeightOneSpectrum R) (n : R) (d : v.asIdeal.primeCompl) :
    residueHom (K := K) v (IsLocalization.mk' (valuationSubringAtPrime K v) n d) =
      IsLocalRing.residue (Localization.AtPrime v.asIdeal)
        (IsLocalization.mk' (Localization.AtPrime v.asIdeal) n d) := by
  have hd0 : algebraMap R v.asIdeal.ResidueField (d : R) ≠ 0 :=
    Ideal.algebraMap_residueField_eq_zero.not.mpr (Ideal.mem_primeCompl_iff.mp d.property)
  have hdunit : IsUnit (algebraMap R v.asIdeal.ResidueField (d : R)) :=
    isUnit_iff_ne_zero.mpr hd0
  rw [residueHom_mk', IsLocalRing.residue_def]
  have h := congrArg (IsLocalRing.residue (Localization.AtPrime v.asIdeal))
    (IsLocalization.mk'_spec (S := Localization.AtPrime v.asIdeal) n d)
  simp only [map_mul, IsLocalRing.residue_def] at h
  exact ((eq_mul_inv_iff_mul_eq₀ hd0).mpr h).symm

/-- `residueHom` agrees with the residue map on the localization model. -/
theorem residueHom_apply_localizationAlgEquiv (v : HeightOneSpectrum R)
    (x : Localization.AtPrime v.asIdeal) :
    residueHom (K := K) v (localizationAlgEquiv (K := K) v x) =
      IsLocalRing.residue (Localization.AtPrime v.asIdeal) x := by
  obtain ⟨n, d, hx⟩ := IsLocalization.exists_mk'_eq v.asIdeal.primeCompl x
  rw [← hx]
  simp [localizationAlgEquiv, residueHom_mk'_residue]

end IsDedekindDomain.HeightOneSpectrum
