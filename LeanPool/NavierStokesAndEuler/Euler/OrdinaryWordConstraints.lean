/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinarySmoothWords
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryPressureCancellation

@[expose] public section

/-! Every genuine derivative word preserves the ordinary Helmholtz
constraint, and consequently the pressure pairing vanishes at every order. -/

noncomputable section

namespace EulerOrdinarySobolev

open MeasureTheory InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerParameterWordGevrey EulerMeanSolenoidal
open scoped ContDiff

theorem word_toLp_eq_orbit (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    (wordField A w).toLp = wordDerivative axis
      (fun a : Space => EulerLpTranslation.translation a A.toLp) w 0 := by
  apply Lp.ext
  filter_upwards [(wordField A w).toLp_ae,A.iteratedFDeriv_translation_ae n 0 (axis ∘ w)]
    with x ha hb
  rw [ha,wordField_field]
  simpa only [wordDerivative,Function.comp_def,add_zero] using hb.symm

theorem projection_word (A : SmoothL2Field Space) {n : ℕ} (w : Fin n → Fin 3) :
    solenoidalProjection (wordField A w).toLp = wordDerivative axis
      (fun a : Space => EulerLpTranslation.translation a (solenoidalProjection A.toLp)) w 0 := by
  rw [word_toLp_eq_orbit,← wordDerivative_comp_clm axis solenoidalProjection _
    A.translation_contDiff]
  congr 2
  funext a
  exact (solenoidalProjection_translation a A.toLp).symm

theorem word_solenoidal (A : SmoothL2Field Space) (hA : A.toLp ∈ solenoidalSpace)
    {n : ℕ} (w : Fin n → Fin 3) : (wordField A w).toLp ∈ solenoidalSpace := by
  apply solenoidalSpace.starProjection_eq_self_iff.mp
  change solenoidalProjection (wordField A w).toLp = _
  rw [projection_word]
  have he : solenoidalProjection A.toLp=A.toLp := solenoidalSpace.starProjection_eq_self_iff.mpr hA
  rw [he,word_toLp_eq_orbit]

theorem word_gradient (A : SmoothL2Field Space) (hA : A.toLp ∈ gradientSpace)
    {n : ℕ} (w : Fin n → Fin 3) : (wordField A w).toLp ∈ gradientSpace := by
  apply (solenoidalProjection_eq_zero_iff _).mp
  rw [projection_word,(solenoidalProjection_eq_zero_iff _).mpr hA]
  simp only [map_zero]
  change (iteratedFDeriv ℝ n (0 : Space → L2) 0) (fun j => axis (w j))=0
  rw [iteratedFDeriv_zero]
  rfl

theorem word_pressure_pairing_zero (P U : SmoothL2Field Space)
    (hP : P.toLp ∈ gradientSpace) (hU : U.toLp ∈ solenoidalSpace)
    {n : ℕ} (w : Fin n → Fin 3) :
    ⟪(wordField P w).toLp,(wordField U w).toLp⟫_ℝ=0 :=
  pressure_pairing_zero (word_gradient P hP w) (word_solenoidal U hU w)

end EulerOrdinarySobolev
