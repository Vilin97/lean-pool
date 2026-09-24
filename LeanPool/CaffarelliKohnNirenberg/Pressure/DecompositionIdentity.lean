/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials

/-!
# Decomposition Identity

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN

private theorem decomposition_setIntegral_eq_integral_of_support
    {Ω : Set Vec3} {g : Vec3 → ℝ} (_ : Integrable g volume)
    (hΩ : tsupport g ⊆ Ω) : ∫ x in Ω, g x = ∫ x, g x := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  exact image_eq_zero_of_notMem_tsupport (fun hxt => hx (hΩ hxt))

private theorem decomposition_integral_seven {f₁ f₂ f₃ f₄ f₅ f₆ f₇ : Vec3 → ℝ}
    (h₁ : Integrable f₁ volume) (h₂ : Integrable f₂ volume)
    (h₃ : Integrable f₃ volume) (h₄ : Integrable f₄ volume)
    (h₅ : Integrable f₅ volume) (h₆ : Integrable f₆ volume)
    (h₇ : Integrable f₇ volume) :
    ∫ x, f₁ x + f₂ x + f₃ x + f₄ x + f₅ x + f₆ x + f₇ x =
      (∫ x, f₁ x) + (∫ x, f₂ x) + (∫ x, f₃ x) + (∫ x, f₄ x) +
        (∫ x, f₅ x) + (∫ x, f₆ x) + (∫ x, f₇ x) := by
  let F : Fin 7 → Vec3 → ℝ := ![f₁, f₂, f₃, f₄, f₅, f₆, f₇]
  have hF : ∀ i, Integrable (F i) volume := by
    intro i
    fin_cases i <;> simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      F] <;> assumption
  have hsum := integral_finsetSum (μ := volume) (Finset.univ : Finset (Fin 7))
    (fun i hi => hF i)
  have hsum' := hsum
  simp only [Matrix.cons_val', Matrix.cons_val_fin_one, Fin.sum_univ_succ, Fin.isValue,
    Matrix.cons_val_zero,
    Matrix.cons_val_succ, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_const,
      Finset.card_singleton, one_smul,
    F] at hsum'
  calc
    _ = ∫ x, f₁ x + (f₂ x + (f₃ x + (f₄ x +
        (f₅ x + (f₆ x + f₇ x))))) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := hsum'
    _ = _ := by ring

/-- Integral identities and integrability data assembling the first pressure component. -/
structure PressureP1DistributionalData
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {η ψ : Vec3 → ℝ} (s : ℝ) : Prop where
  hcut : ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) =
      (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η i x * spatialDeriv ψ j x)) +
        (∫ x in Ω, ∑ i, ∑ j,
          pressureUTensor u c (x, s) i j *
            (spatialDeriv η j x * spatialDeriv ψ i x)) -
        (∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x)) -
        2 * (∫ x in Ω, (spatialGradDot η ψ x) * p (x, s)) -
        (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) -
        (∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x))
  hA : Integrable (fun x => η x * p (x, s) * spatialLaplacian ψ x) volume
  hAΩ : tsupport (fun x => η x * p (x, s) * spatialLaplacian ψ x) ⊆ Ω
  hB0 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume
  hB0Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) ⊆ Ω
  hB1 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume
  hB1Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) ⊆ Ω
  hB2 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) volume
  hB2Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)) ⊆ Ω
  hB3 : Integrable (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) volume
  hB3Ω : tsupport (fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)) ⊆ Ω
  hC5 : Integrable (fun x => p (x, s) *
    (ψ x * spatialLaplacian η x)) volume
  hC5Ω : tsupport (fun x => p (x, s) *
    (ψ x * spatialLaplacian η x)) ⊆ Ω
  hC6 : Integrable (fun x => spatialGradDot η ψ x * p (x, s)) volume
  hC6Ω : tsupport (fun x => spatialGradDot η ψ x * p (x, s)) ⊆ Ω
  hF7 : Integrable (fun x => ∑ i,
    f (x, s) i * (η x * spatialDeriv ψ i x)) volume
  hF7Ω : tsupport (fun x => ∑ i,
    f (x, s) i * (η x * spatialDeriv ψ i x)) ⊆ Ω
  hF8 : Integrable (fun x => ∑ i,
    f (x, s) i * (ψ x * spatialDeriv η i x)) volume
  hF8Ω : tsupport (fun x => ∑ i,
    f (x, s) i * (ψ x * spatialDeriv η i x)) ⊆ Ω
  hQ : Integrable (fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
    pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
    pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x) volume
  hP2 : Integrable (fun x => pressureP2 η u c s x * spatialLaplacian ψ x) volume
  hP3 : Integrable (fun x => pressureP3 η u c s x * spatialLaplacian ψ x) volume
  hP4 : Integrable (fun x => pressureP4 η u c s x * spatialLaplacian ψ x) volume
  hP5 : Integrable (fun x => pressureP5 η p s x * spatialLaplacian ψ x) volume
  hP6 : Integrable (fun x => pressureP6 η p s x * spatialLaplacian ψ x) volume
  hP7 : Integrable (fun x => pressureP7 η f s x * spatialLaplacian ψ x) volume
  hP8 : Integrable (fun x => pressureP8 η f s x * spatialLaplacian ψ x) volume
  hPair2 : ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (mixedSecond η i j x * ψ x)
  hPair3 : ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (spatialDeriv η i x * spatialDeriv ψ j x)
  hPair4 : ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x =
    ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
      (spatialDeriv η j x * spatialDeriv ψ i x)
  hPair5 : ∫ x, pressureP5 η p s x * spatialLaplacian ψ x =
    -∫ x, p (x, s) * (ψ x * spatialLaplacian η x)
  hPair6 : ∫ x, pressureP6 η p s x * spatialLaplacian ψ x =
    -2 * ∫ x, spatialGradDot η ψ x * p (x, s)
  hPair7 : ∫ x, pressureP7 η f s x * spatialLaplacian ψ x =
    -∫ x, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)
  hPair8 : ∫ x, pressureP8 η f s x * spatialLaplacian ψ x =
    -∫ x, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)

theorem pressureP1_distributional_identity_of_cutoff
    {Ω : Set Vec3} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    {η ψ : Vec3 → ℝ}
    (hcut : ∫ x in Ω, p (x, s) * (η x * spatialLaplacian ψ x) =
        (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η i x * spatialDeriv ψ j x)) +
          (∫ x in Ω, ∑ i, ∑ j,
            pressureUTensor u c (x, s) i j *
              (spatialDeriv η j x * spatialDeriv ψ i x)) -
          (∫ x in Ω, p (x, s) * (ψ x * spatialLaplacian η x)) -
          2 * (∫ x in Ω, (spatialGradDot η ψ x) * p (x, s)) -
          (∫ x in Ω, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)) -
          (∫ x in Ω, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)))
    (hA : Integrable (fun x => η x * p (x, s) * spatialLaplacian ψ x) volume)
    (hAΩ : tsupport (fun x => η x * p (x, s) * spatialLaplacian ψ x) ⊆ Ω)
    (hB0 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) volume)
    (hB0Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)) ⊆ Ω)
    (hB1 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) volume)
    (hB1Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)) ⊆ Ω)
    (hB2 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x)) volume)
    (hB2Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x)) ⊆ Ω)
    (hB3 : Integrable (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x)) volume)
    (hB3Ω : tsupport (fun x => ∑ i, ∑ j,
      pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x)) ⊆ Ω)
    (hC5 : Integrable (fun x => p (x, s) *
      (ψ x * spatialLaplacian η x)) volume)
    (hC5Ω : tsupport (fun x => p (x, s) *
      (ψ x * spatialLaplacian η x)) ⊆ Ω)
    (hC6 : Integrable (fun x => spatialGradDot η ψ x * p (x, s)) volume)
    (hC6Ω : tsupport (fun x => spatialGradDot η ψ x * p (x, s)) ⊆ Ω)
    (hF7 : Integrable (fun x => ∑ i,
      f (x, s) i * (η x * spatialDeriv ψ i x)) volume)
    (hF7Ω : tsupport (fun x => ∑ i,
      f (x, s) i * (η x * spatialDeriv ψ i x)) ⊆ Ω)
    (hF8 : Integrable (fun x => ∑ i,
      f (x, s) i * (ψ x * spatialDeriv η i x)) volume)
    (hF8Ω : tsupport (fun x => ∑ i,
      f (x, s) i * (ψ x * spatialDeriv η i x)) ⊆ Ω)
    (hQ : Integrable (fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
      pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
      pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x) volume)
    (hP2 : Integrable (fun x => pressureP2 η u c s x * spatialLaplacian ψ x) volume)
    (hP3 : Integrable (fun x => pressureP3 η u c s x * spatialLaplacian ψ x) volume)
    (hP4 : Integrable (fun x => pressureP4 η u c s x * spatialLaplacian ψ x) volume)
    (hP5 : Integrable (fun x => pressureP5 η p s x * spatialLaplacian ψ x) volume)
    (hP6 : Integrable (fun x => pressureP6 η p s x * spatialLaplacian ψ x) volume)
    (hP7 : Integrable (fun x => pressureP7 η f s x * spatialLaplacian ψ x) volume)
    (hP8 : Integrable (fun x => pressureP8 η f s x * spatialLaplacian ψ x) volume)
    (hPair2 : ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (mixedSecond η i j x * ψ x))
    (hPair3 : ∫ x, pressureP3 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (spatialDeriv η i x * spatialDeriv ψ j x))
    (hPair4 : ∫ x, pressureP4 η u c s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, pressureUTensor u c (x, s) i j *
        (spatialDeriv η j x * spatialDeriv ψ i x))
    (hPair5 : ∫ x, pressureP5 η p s x * spatialLaplacian ψ x =
      -∫ x, p (x, s) * (ψ x * spatialLaplacian η x))
    (hPair6 : ∫ x, pressureP6 η p s x * spatialLaplacian ψ x =
      -2 * ∫ x, spatialGradDot η ψ x * p (x, s))
    (hPair7 : ∫ x, pressureP7 η f s x * spatialLaplacian ψ x =
      -∫ x, ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x))
    (hPair8 : ∫ x, pressureP8 η f s x * spatialLaplacian ψ x =
      -∫ x, ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)) :
    ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
      ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
        mixedSecond ψ i j x := by
  let A : Vec3 → ℝ := fun x => η x * p (x, s) * spatialLaplacian ψ x
  let B0 : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (η x * mixedSecond ψ i j x)
  let B1 : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (mixedSecond η i j x * ψ x)
  let B2 : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (spatialDeriv η i x * spatialDeriv ψ j x)
  let B3 : Vec3 → ℝ := fun x => ∑ i, ∑ j,
    pressureUTensor u c (x, s) i j * (spatialDeriv η j x * spatialDeriv ψ i x)
  let C5 : Vec3 → ℝ := fun x => p (x, s) * (ψ x * spatialLaplacian η x)
  let C6 : Vec3 → ℝ := fun x => spatialGradDot η ψ x * p (x, s)
  let F7 : Vec3 → ℝ := fun x => ∑ i, f (x, s) i * (η x * spatialDeriv ψ i x)
  let F8 : Vec3 → ℝ := fun x => ∑ i, f (x, s) i * (ψ x * spatialDeriv η i x)
  have hAe := decomposition_setIntegral_eq_integral_of_support hA hAΩ
  have hB0e := decomposition_setIntegral_eq_integral_of_support hB0 hB0Ω
  have hB1e := decomposition_setIntegral_eq_integral_of_support hB1 hB1Ω
  have hB2e := decomposition_setIntegral_eq_integral_of_support hB2 hB2Ω
  have hB3e := decomposition_setIntegral_eq_integral_of_support hB3 hB3Ω
  have hC5e := decomposition_setIntegral_eq_integral_of_support hC5 hC5Ω
  have hC6e := decomposition_setIntegral_eq_integral_of_support hC6 hC6Ω
  have hF7e := decomposition_setIntegral_eq_integral_of_support hF7 hF7Ω
  have hF8e := decomposition_setIntegral_eq_integral_of_support hF8 hF8Ω
  have hcut' : (∫ x in Ω, A x) = (∫ x in Ω, B0 x) +
      (∫ x in Ω, B1 x) + (∫ x in Ω, B2 x) + (∫ x in Ω, B3 x) -
      (∫ x in Ω, C5 x) - 2 * (∫ x in Ω, C6 x) -
      (∫ x in Ω, F7 x) - (∫ x in Ω, F8 x) := by
    calc
      (∫ x in Ω, A x) = ∫ x in Ω, p (x, s) *
          (η x * spatialLaplacian ψ x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        dsimp [A]
        ring
      _ = _ := hcut
      _ = (∫ x in Ω, B0 x) + (∫ x in Ω, B1 x) +
          (∫ x in Ω, B2 x) + (∫ x in Ω, B3 x) -
          (∫ x in Ω, C5 x) - 2 * (∫ x in Ω, C6 x) -
          (∫ x in Ω, F7 x) - (∫ x in Ω, F8 x) := by
        rfl
  have hglobal : (∫ x, A x) = (∫ x, B0 x) + (∫ x, B1 x) +
      (∫ x, B2 x) + (∫ x, B3 x) - (∫ x, C5 x) -
      2 * (∫ x, C6 x) - (∫ x, F7 x) - (∫ x, F8 x) := by
    calc
      (∫ x, A x) = ∫ x in Ω, A x := hAe.symm
      _ = (∫ x in Ω, B0 x) + (∫ x in Ω, B1 x) +
          (∫ x in Ω, B2 x) + (∫ x in Ω, B3 x) -
          (∫ x in Ω, C5 x) - 2 * (∫ x in Ω, C6 x) -
          (∫ x in Ω, F7 x) - (∫ x in Ω, F8 x) := hcut'
      _ = (∫ x, B0 x) + (∫ x, B1 x) + (∫ x, B2 x) +
          (∫ x, B3 x) - (∫ x, C5 x) - 2 * (∫ x, C6 x) -
          (∫ x, F7 x) - (∫ x, F8 x) := by rw [hB0e, hB1e, hB2e,
            hB3e, hC5e, hC6e, hF7e, hF8e]
  have hLap : (∫ x, A x) = (∫ x, B0 x) +
      ∫ x, (pressureP2 η u c s x + pressureP3 η u c s x +
        pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
        pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x := by
    have hPairSum : (∫ x, B1 x) + (∫ x, B2 x) + (∫ x, B3 x) -
        (∫ x, C5 x) - 2 * (∫ x, C6 x) - (∫ x, F7 x) -
        (∫ x, F8 x) =
        (∫ x, pressureP2 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP3 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP4 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP5 η p s x * spatialLaplacian ψ x) +
        (∫ x, pressureP6 η p s x * spatialLaplacian ψ x) +
        (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
        (∫ x, pressureP8 η f s x * spatialLaplacian ψ x) := by
      rw [hPair2, hPair3, hPair4, hPair5, hPair6, hPair7, hPair8]
      ring
    have hQexpand : ∫ x, (pressureP2 η u c s x + pressureP3 η u c s x +
        pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
        pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x =
        (∫ x, pressureP2 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP3 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP4 η u c s x * spatialLaplacian ψ x) +
        (∫ x, pressureP5 η p s x * spatialLaplacian ψ x) +
        (∫ x, pressureP6 η p s x * spatialLaplacian ψ x) +
        (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
        (∫ x, pressureP8 η f s x * spatialLaplacian ψ x) := by
      calc
        _ = ∫ x, pressureP2 η u c s x * spatialLaplacian ψ x +
            pressureP3 η u c s x * spatialLaplacian ψ x +
            pressureP4 η u c s x * spatialLaplacian ψ x +
            pressureP5 η p s x * spatialLaplacian ψ x +
            pressureP6 η p s x * spatialLaplacian ψ x +
            pressureP7 η f s x * spatialLaplacian ψ x +
            pressureP8 η f s x * spatialLaplacian ψ x := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = _ := decomposition_integral_seven hP2 hP3 hP4 hP5 hP6 hP7 hP8
    calc
      (∫ x, A x) = (∫ x, B0 x) + (∫ x, B1 x) + (∫ x, B2 x) +
          (∫ x, B3 x) - (∫ x, C5 x) - 2 * (∫ x, C6 x) -
          (∫ x, F7 x) - (∫ x, F8 x) := hglobal
      _ = (∫ x, B0 x) + (∫ x, pressureP2 η u c s x *
          spatialLaplacian ψ x) + (∫ x, pressureP3 η u c s x *
          spatialLaplacian ψ x) + (∫ x, pressureP4 η u c s x *
          spatialLaplacian ψ x) + (∫ x, pressureP5 η p s x *
          spatialLaplacian ψ x) + (∫ x, pressureP6 η p s x *
          spatialLaplacian ψ x) + (∫ x, pressureP7 η f s x *
          spatialLaplacian ψ x) + (∫ x, pressureP8 η f s x *
          spatialLaplacian ψ x) := by
        calc
          _ = (∫ x, B0 x) +
              ((∫ x, B1 x) + (∫ x, B2 x) + (∫ x, B3 x) -
                (∫ x, C5 x) - 2 * (∫ x, C6 x) -
                (∫ x, F7 x) - (∫ x, F8 x)) := by ring
          _ = _ := congrArg (fun z => (∫ x, B0 x) + z) hPairSum
          _ = _ := by ring
      _ = (∫ x, B0 x) + ∫ x, (pressureP2 η u c s x +
          pressureP3 η u c s x + pressureP4 η u c s x + pressureP5 η p s x +
          pressureP6 η p s x + pressureP7 η f s x + pressureP8 η f s x) *
          spatialLaplacian ψ x := by
        calc
          _ = (∫ x, B0 x) +
              ((∫ x, pressureP2 η u c s x * spatialLaplacian ψ x) +
                (∫ x, pressureP3 η u c s x * spatialLaplacian ψ x) +
                (∫ x, pressureP4 η u c s x * spatialLaplacian ψ x) +
                (∫ x, pressureP5 η p s x * spatialLaplacian ψ x) +
                (∫ x, pressureP6 η p s x * spatialLaplacian ψ x) +
                (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
                (∫ x, pressureP8 η f s x * spatialLaplacian ψ x)) := by ring
          _ = _ := congrArg (fun z => (∫ x, B0 x) + z) hQexpand.symm
  let Q : Vec3 → ℝ := fun x => (pressureP2 η u c s x + pressureP3 η u c s x +
      pressureP4 η u c s x + pressureP5 η p s x + pressureP6 η p s x +
      pressureP7 η f s x + pressureP8 η f s x) * spatialLaplacian ψ x
  have hfun : (fun x => pressureP1 η u c p f s x * spatialLaplacian ψ x) =
      A - Q := by
    funext x
    simp only [pressureP1, A, Q, Pi.sub_apply]
    ring
  have hIntSub : (∫ x, (A - Q) x) = (∫ x, A x) - (∫ x, Q x) := by
    simpa only [Pi.sub_apply] using (integral_sub hA hQ)
  have hP1B0 : ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x =
      ∫ x, B0 x := by
    rw [hfun, hIntSub]
    rw [hLap]
    simp only [Q]
    ring
  calc
    ∫ x, pressureP1 η u c p f s x * spatialLaplacian ψ x = ∫ x, B0 x := hP1B0
    _ = ∫ x, ∑ i, ∑ j, η x * pressureUTensor u c (x, s) i j *
        mixedSecond ψ i j x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [B0]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

end CKN
