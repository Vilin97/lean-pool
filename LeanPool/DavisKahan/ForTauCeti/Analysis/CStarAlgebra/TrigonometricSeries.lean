/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI GPT-5.6 Sol
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Algebra.TrigonometricSeries
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# Trigonometric power series and the continuous functional calculus

For a self-adjoint element of a real continuous functional calculus, this module identifies the
norm-convergent Banach-algebra cosine and sine series with the calculus of `Real.cos` and
`Real.sin`.

The proof has two reusable steps. First, evaluation transports the Banach-algebra series on a
continuous real-valued function to the corresponding scalar series. Second, continuity of
`cfcHom` and functoriality of the series transport that identity into the target algebra.

## Main results

* `TauCeti.cosSeries_continuousMap_eq`: cosine series are computed pointwise on `C(X, ℝ)`.
* `TauCeti.sinSeries_continuousMap_eq`: sine series are computed pointwise on `C(X, ℝ)`.
* `TauCeti.cfc_real_cos_eq_cosSeries`: `cfc Real.cos a = cosSeries a`.
* `TauCeti.cfc_real_sin_eq_sinSeries`: `cfc Real.sin a = sinSeries a`.

## Provenance

The transport argument follows the same continuous-homomorphism pattern used by Mathlib for
`CFC.exp_eq_normedSpace_exp`, but for the even and odd trigonometric power series supplied by
`ForTauCeti.Analysis.Normed.Algebra.TrigonometricSeries`.
-/

public section

namespace TauCeti

open scoped ContinuousFunctionalCalculus

noncomputable section

section ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The cosine power series of a real-valued continuous function is computed pointwise. -/
theorem cosSeries_continuousMap_eq (f : C(X, ℝ)) :
    cosSeries (𝕜 := ℝ) f =
      (⟨Real.cos ∘ f, Real.continuous_cos.comp f.continuous⟩ : C(X, ℝ)) := by
  ext x
  change (cosSeries (𝕜 := ℝ) f) x = Real.cos (f x)
  have hmap :=
    (hasSum_cosSeries (𝕜 := ℝ) f).map
      (ContinuousMap.evalCLM ℝ x) (ContinuousMap.evalCLM ℝ x).continuous
  have hmap' :
      HasSum (fun n : ℕ => cosSeriesTerm (𝕜 := ℝ) (f x) n)
        ((cosSeries (𝕜 := ℝ) f) x) := by
    refine hmap.congr fun n => ?_
    simp [Function.comp_apply, cosSeriesTerm]
  calc
    (cosSeries (𝕜 := ℝ) f) x = cosSeries (𝕜 := ℝ) (f x) :=
      hmap'.unique (hasSum_cosSeries (𝕜 := ℝ) (f x))
    _ = Real.cos (f x) := cosSeries_real (f x)

/-- The sine power series of a real-valued continuous function is computed pointwise. -/
theorem sinSeries_continuousMap_eq (f : C(X, ℝ)) :
    sinSeries (𝕜 := ℝ) f =
      (⟨Real.sin ∘ f, Real.continuous_sin.comp f.continuous⟩ : C(X, ℝ)) := by
  ext x
  change (sinSeries (𝕜 := ℝ) f) x = Real.sin (f x)
  have hmap :=
    (hasSum_sinSeries (𝕜 := ℝ) f).map
      (ContinuousMap.evalCLM ℝ x) (ContinuousMap.evalCLM ℝ x).continuous
  have hmap' :
      HasSum (fun n : ℕ => sinSeriesTerm (𝕜 := ℝ) (f x) n)
        ((sinSeries (𝕜 := ℝ) f) x) := by
    refine hmap.congr fun n => ?_
    simp [Function.comp_apply, sinSeriesTerm]
  calc
    (sinSeries (𝕜 := ℝ) f) x = sinSeries (𝕜 := ℝ) (f x) :=
      hmap'.unique (hasSum_sinSeries (𝕜 := ℝ) (f x))
    _ = Real.sin (f x) := sinSeries_real (f x)

end ContinuousMap

section CFC

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [CompleteSpace A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The real continuous functional calculus of cosine agrees with the Banach-algebra cosine
power series. -/
theorem cfc_real_cos_eq_cosSeries {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.cos a = cosSeries (𝕜 := ℝ) a := by
  rw [cfc_apply Real.cos a ha]
  let idC : C(spectrum ℝ a, ℝ) :=
    (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hcont := cfcHom_continuous (R := ℝ) (A := A)
    (p := IsSelfAdjoint) (a := a) ha
  have hid : (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) idC = a := by
    simpa [idC] using (cfcHom_id (R := ℝ) (p := IsSelfAdjoint) ha)
  have hmap := map_cosSeries (𝕜 := ℝ)
    (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha).toAlgHom hcont idC
  calc
    _ = (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha)
        (cosSeries (𝕜 := ℝ) idC) := by
      apply congrArg (fun g : C(spectrum ℝ a, ℝ) =>
        (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) g)
      rw [cosSeries_continuousMap_eq idC]
      ext x
      simp [idC, Function.comp_apply]
    _ = cosSeries (𝕜 := ℝ) ((cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) idC) := by
      simpa using hmap
    _ = cosSeries (𝕜 := ℝ) a := by rw [hid]

/-- The real continuous functional calculus of sine agrees with the Banach-algebra sine
power series. -/
theorem cfc_real_sin_eq_sinSeries {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.sin a = sinSeries (𝕜 := ℝ) a := by
  rw [cfc_apply Real.sin a ha]
  let idC : C(spectrum ℝ a, ℝ) :=
    (ContinuousMap.id ℝ).restrict (spectrum ℝ a)
  have hcont := cfcHom_continuous (R := ℝ) (A := A)
    (p := IsSelfAdjoint) (a := a) ha
  have hid : (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) idC = a := by
    simpa [idC] using (cfcHom_id (R := ℝ) (p := IsSelfAdjoint) ha)
  have hmap := map_sinSeries (𝕜 := ℝ)
    (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha).toAlgHom hcont idC
  calc
    _ = (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha)
        (sinSeries (𝕜 := ℝ) idC) := by
      apply congrArg (fun g : C(spectrum ℝ a, ℝ) =>
        (cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) g)
      rw [sinSeries_continuousMap_eq idC]
      ext x
      simp [idC, Function.comp_apply]
    _ = sinSeries (𝕜 := ℝ) ((cfcHom (R := ℝ) (p := IsSelfAdjoint) ha) idC) := by
      simpa using hmap
    _ = sinSeries (𝕜 := ℝ) a := by rw [hid]

/-- Euler's identity in a real continuous-functional-calculus algebra.  The relation
`J * J * T = -T` is deliberately only required on the support reached by `T`; no global
complex-structure identity `J * J = -1` is assumed. -/
theorem exp_mul_eq_cfc_real_cos_add_mul_cfc_real_sin
    {J T : A} (hT : IsSelfAdjoint T) (hcomm : Commute J T)
    (hsq : J * J * T = -T) :
    NormedSpace.exp (J * T) = cfc Real.cos T + J * cfc Real.sin T := by
  rw [exp_mul_eq_cosSeries_add_mul_sinSeries (𝕜 := ℝ) hcomm hsq]
  rw [← cfc_real_cos_eq_cosSeries hT, ← cfc_real_sin_eq_sinSeries hT]

end CFC

end

end TauCeti

end
