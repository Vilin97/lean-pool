/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevSpace
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
import LeanPool.NavierStokesAndEuler.Euler.Foundations.SmoothPressureRepresentative
import LeanPool.NavierStokesAndEuler.Euler.IsometricActionCalculus

/-!
# Genuine cylinder Sobolev jets and smooth representatives from mixed L² orbits

The parameter orbit is the actual R³×R covering action on cylinder L². Every
angular derivative is retained. Its genuine strong derivatives construct the
existing Sobolev arrays and a smooth representative; no spatial regularity of
the solution is assumed separately.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerSpatialSobolevInverse EulerCylinderSobolev EulerPressureSpatialRegularity
      EulerMetricTransport
  EulerLpCylinderTranslation EulerCylinderSobolevSpace EulerParameterWordGevrey
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]

/-- Smoothness of the actual full mixed L² translation orbit. -/
abbrev SmoothOrbit (u : LiftL2 period) : Prop :=
  ContDiff ℝ ∞ (fun a : LiftTangent => translate period a u)

/-- The actual L² derivative in a covering-space direction. -/
def orbitDerivative (u : LiftL2 period) (v : LiftTangent) : LiftL2 period :=
  fderiv ℝ (fun a : LiftTangent => translate period a u) 0 v

/-- An actual orbit derivative transforms by actual cylinder translation. -/
theorem orbitDerivative_translation (u : LiftL2 period) (hu : SmoothOrbit period u)
    (v a : LiftTangent) :
    translate period a (orbitDerivative period u v) =
      fderiv ℝ (fun b : LiftTangent => translate period b u) a v := by
  have h := EulerIsometricAction.hasFDerivAt_all (translate period) (translate_add period) u
    (fderiv ℝ (fun b : LiftTangent => translate period b u) 0)
    ((hu.differentiable (by simp) (0 : LiftTangent)).hasFDerivAt) a
  exact (congrArg (fun D : LiftTangent →L[ℝ] LiftL2 period => D v) h.fderiv).symm

theorem orbitDerivative_smooth (u : LiftL2 period) (hu : SmoothOrbit period u) (v : LiftTangent) :
    SmoothOrbit period (orbitDerivative period u v) := by
  have he : (fun a : LiftTangent => translate period a (orbitDerivative period u v)) =
      fun a : LiftTangent => fderiv ℝ (fun b : LiftTangent => translate period b u) a v :=
    funext (fun a => orbitDerivative_translation period u hu v a)
  change ContDiff ℝ ∞ _
  rw [he]
  exact (hu.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-- These derivatives are exactly the existing strong cylinder directional derivatives. -/
theorem orbitDerivative_hasDerivAt (u : LiftL2 period) (hu : SmoothOrbit period u) (v :
    LiftTangent) :
    HasDerivAt (fun t : ℝ => EulerLiftedGradientSpace.translation period (translationPath period v
        t) u)
      (orbitDerivative period u v) 0 := by
  have h := (hu.differentiable (by simp) (0 : LiftTangent)).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ => t • v) v 0 := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const v
  have hd := h.comp_hasDerivAt_of_eq (0 : ℝ) ht (by simp)
  exact hd

/-- Every finite tree of genuine mixed strong derivatives is constructed. -/
def spatialJet (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) :
    SpatialJet period standardDirection q u :=
  match q with
  | 0 => .zero u
  | n+1 => .succ
      (fun i => orbitDerivative period u (standardDirection i))
      (fun i => spatialJet n (orbitDerivative period u (standardDirection i))
        (orbitDerivative_smooth period u hu (standardDirection i)))
      (fun i => orbitDerivative_hasDerivAt period u hu (standardDirection i))

/-- The exact fixed-Hq jet sum equals the full mixed word base norm, with no dimension factor. -/
theorem spatialJet_norm (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) :
    (spatialJet period q u hu).sobolevNorm =
      baseSize standardDirection q (fun a : LiftTangent => translate period a u) 0 := by
  induction q generalizing u with
  | zero => simp only [spatialJet,SpatialJet.sobolevNorm,baseSize_zero,translate_zero]
  | succ q ih =>
    rw [baseSize_succ standardDirection q _ hu]
    change ‖u‖ + ∑ i, (spatialJet period q (orbitDerivative period u (standardDirection i))
      (orbitDerivative_smooth period u hu (standardDirection i))).sobolevNorm = _
    rw [translate_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    rw [ih]
    congr 1
    funext a
    exact orbitDerivative_translation period u hu (standardDirection i) a

/-- Actual mixed orbit smoothness supplies an existing genuine cylinder Sobolev element. -/
def sobolev (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) : SobolevSpace period q :=
  ofJet period (spatialJet period q u hu)

@[simp] theorem sobolev_value (q : ℕ) (u : LiftL2 period) (hu : SmoothOrbit period u) :
    value period (sobolev period q u hu) = u := value_ofJet period _

/-- The existing reconstruction theorem now applies to actual full mixed translation derivatives. -/
theorem exists_smooth_representative (u : LiftL2 period) (hu : SmoothOrbit period u) :
    ∃ g : LiftDomain period → Space,
      (∀ x, ContDiff ℝ ∞ (localFieldLift period g x)) ∧
      (u : LiftDomain period → Space) =ᵐ[liftMeasure period] g :=
  EulerSmoothPressureRepresentative.exists_smooth_representative period u (fun q => spatialJet
      period q u hu)

/-- A genuine smooth cylinder representative of the solved L² field. -/
def representative (u : LiftL2 period) (hu : SmoothOrbit period u) : LiftDomain period → Space :=
  Classical.choose (exists_smooth_representative period u hu)

theorem representative_smooth (u : LiftL2 period) (hu : SmoothOrbit period u) (x : LiftDomain
    period) :
    ContDiff ℝ ∞ (localFieldLift period (representative period u hu) x) :=
  (Classical.choose_spec (exists_smooth_representative period u hu)).1 x

theorem representative_ae (u : LiftL2 period) (hu : SmoothOrbit period u) :
    (u : LiftDomain period → Space) =ᵐ[liftMeasure period] representative period u hu :=
  (Classical.choose_spec (exists_smooth_representative period u hu)).2

end EulerCylinderSmoothOrbit
