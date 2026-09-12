/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothLimit
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! Genuine ordinary-space L² translations and closedness of their full derivative. -/

@[expose] public section


noncomputable section


namespace EulerLpTranslation

open MeasureTheory EulerSmoothLimit Filter
open scoped Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- L² space: an abbreviation for `Lp V 2 (volume : Measure Space)`. -/
abbrev L2Space (V : Type*) [NormedAddCommGroup V] := Lp V 2 (volume : Measure Space)

/-- Translation, given by `Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => x+a)
(measurePreserving_add_right volume a)`. -/
def translation (a : Space) : L2Space V →ₗᵢ[ℝ] L2Space V :=
  Lp.compMeasurePreservingₗᵢ ℝ (fun x : Space => x+a) (measurePreserving_add_right volume a)

theorem translation_ae (a : Space) (u : L2Space V) :
    translation a u =ᵐ[volume] fun x => u (x+a) :=
  Lp.coeFn_compMeasurePreserving u (measurePreserving_add_right volume a)

@[simp] theorem translation_zero (u : L2Space V) : translation 0 u = u := by
  apply Lp.ext
  filter_upwards [translation_ae 0 u] with x hx
  simpa only [add_zero] using hx

theorem translation_add (a b : Space) (u : L2Space V) :
    translation a (translation b u) = translation (a+b) u := by
  apply Lp.ext
  filter_upwards [translation_ae a (translation b u),
    (measurePreserving_add_right (volume : Measure Space) a).quasiMeasurePreserving.ae
        (translation_ae b u),
    translation_ae (a+b) u] with x ha hb hab
  rw [ha, hb, hab, add_assoc]

theorem translation_continuous (u : L2Space V) : Continuous (fun a : Space => translation a u) := by
  let g : Space → C(Space, Space) := fun a => ⟨fun x => x+a, continuous_id.add continuous_const⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g
    (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hg
    (fun a => measurePreserving_add_right (volume : Measure Space) a) (by norm_num)

theorem translation_norm_le (a : Space) :
    ‖(translation (V := V) a).toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map, one_mul, le_refl]

theorem translation_hasFDerivAt_all (u : L2Space V) (D : Space →L[ℝ] L2Space V)
    (h : HasFDerivAt (fun a : Space => translation a u) D 0) (a : Space) :
    HasFDerivAt (fun b : Space => translation b u)
      ((translation a).toContinuousLinearMap.comp D) a :=
  EulerIsometricAction.hasFDerivAt_all translation translation_add u D h a

theorem translation_orbits_tendstoUniformly {ι : Type*} {l : Filter ι}
    (u : ι → L2Space V) (v : L2Space V) (hu : Tendsto u l (𝓝 v)) :
    TendstoUniformly (fun n a => translation a (u n)) (fun a => translation a v) l :=
  EulerIsometricAction.orbits_tendstoUniformly translation u v hu

theorem translation_derivatives_tendstoUniformly {ι : Type*} {l : Filter ι}
    (D : ι → Space →L[ℝ] L2Space V) (D₀ : Space →L[ℝ] L2Space V)
    (hD : Tendsto D l (𝓝 D₀)) :
    TendstoUniformly (fun n a => (translation a).toContinuousLinearMap.comp (D n))
      (fun a => (translation a).toContinuousLinearMap.comp D₀) l :=
  EulerIsometricAction.derivatives_tendstoUniformly translation D D₀ hD

/-- Convergent ordinary L² fields and their actual translation derivatives have the expected
derivative in the limit. -/
theorem translation_hasFDerivAt_limit (u : ℕ → L2Space V)
    (D : ℕ → Space →L[ℝ] L2Space V) (u₀ : L2Space V) (D₀ : Space →L[ℝ] L2Space V)
    (h : ∀ n, HasFDerivAt (fun a : Space => translation a (u n)) (D n) 0)
    (hu : Tendsto u atTop (𝓝 u₀)) (hD : Tendsto D atTop (𝓝 D₀)) :
    HasFDerivAt (fun a : Space => translation a u₀) D₀ 0 :=
  EulerIsometricAction.hasFDerivAt_limit translation translation_add translation_zero u D u₀ D₀ h
      hu hD

end EulerLpTranslation
