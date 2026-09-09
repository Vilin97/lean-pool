/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderAngleEvolution
public import LeanPool.NavierStokesAndEuler.Euler.PacketPeriodicPotential
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangular
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevCoefficient
import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveMap
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRectangularRegularity

/-! The literal periodic vector potential as an actual continuous cylinder L² path. -/

@[expose] public section


noncomputable section

namespace EulerCylinderPotential

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerMetricTransport EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerCylinderAnglePrimitive EulerMeanCoefficients
  EulerPacketCrossProduct EulerParameterWordGevrey EulerGevrey
open scoped ContDiff BoundedContinuousFunction

variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]
  (B : C(K, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))

/-- Potential path, given by `fullMultiplierMap P B (pathPrimitive P p)`. -/
def potentialPath : C(K,LiftL2 P) := fullMultiplierMap P B (pathPrimitive P p)

include hB hp in
theorem potentialPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (potentialPath P B p)) :=
  product_orbit_contDiff P B hB (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp)

/-- Potential field, given by `pointField P (potentialPath P B p) (potentialPath_orbit P B hB p
hp) t`. -/
def potentialField (t : K) : LiftDomain P → Space :=
  pointField P (potentialPath P B p) (potentialPath_orbit P B hB p hp) t

theorem potentialPath_ae (t : K) :
    (potentialPath P B p t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => B t x.1 (pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t x)
          := by
  filter_upwards [EulerLpOperatorField.full_ae (liftMeasure P) (fieldLift P (B t))
      (pathPrimitive P p t),
    pointField_ae P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t] with x hB hp
  exact hB.trans (congrArg (B t x.1) hp)

/-- The canonical representative is the coefficient times the literal angular primitive. -/
theorem potentialField_formula
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (t : K) (y : Space) (θ : ℝ) :
    potentialField P B hB p hp t (y,(θ : AddCircle P)) =
      B t y (EulerAngleMeanZeroPrimitive.primitive P
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ) := by
  have he : potentialField P B hB p hp t = fun x =>
      B t x.1 (pointField P (pathPrimitive P p) (pathPrimitive_orbit_contDiff P p hp) t x) := by
    apply Measure.eq_of_ae_eq
      ((pointField_ae P (potentialPath P B p) (potentialPath_orbit P B hB p hp) t).symm.trans
        (potentialPath_ae P B p hp t))
    · exact smoothField_continuous P _ (pointField_smooth P _ _ t)
    · exact ((B t).continuous.comp continuous_fst).clm_apply
        (smoothField_continuous P _ (pointField_smooth P _ _ t))
  rw [he]
  change B t y (pointField P (pathPrimitive P p)
    (pathPrimitive_orbit_contDiff P p hp) t (y,(θ : AddCircle P))) = _
  rw [pointField_primitive_formula P p hp hmean t y θ]

theorem potentialField_source_formula
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (m : K → Space → Space) (hBm : ∀ t y, B t y = potentialMultiplier (m t y))
    (t : K) (y : Space) (θ : ℝ) :
    potentialField P B hB p hp t (y,(θ : AddCircle P)) =
      EulerPacketAngularPotential.potential P (m t y)
        (fun s => pointField P p hp t (y,(s : AddCircle P))) θ := by
  rw [potentialField_formula P B hB p hp hmean t y θ, hBm]
  exact EulerAngleMeanZeroPrimitive.primitive_map _ P _
    ((smoothField_continuous P _ (pointField_smooth P p hp t)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' P))) θ

/-- The L² construction is the same actual field used in the compact Piola construction. -/
theorem potentialField_eq_periodic
    (hmean : ∀ t y, (∫ s in (0 : ℝ)..P, pointField P p hp t (y, (s : AddCircle P))) = 0)
    (m : K → Space → Space) (hBm : ∀ t y, B t y = potentialMultiplier (m t y))
    (t : K) :
    potentialField P B hB p hp t = EulerPacketPeriodicPotential.field P (m t) (pointField P p hp t)
        := by
  funext x
  obtain ⟨θ,hθ⟩ := QuotientAddGroup.mk_surjective x.2
  have hx : x=(x.1,(θ : AddCircle P)) := by
    apply Prod.ext
    · rfl
    · exact hθ.symm
  rw [hx, potentialField_source_formula P B hB p hp hmean m hBm t x.1 θ]
  have h := EulerPacketPeriodicPotential.field_cover P (m t) (pointField P p hp t)
    (smoothField_continuous P _ (pointField_smooth P p hp t)) (hmean t) (x.1,θ)
  simpa only [coveringMap, EulerPacketPiola.coveringPotential, localFieldLift,
    Prod.fst_zero, Prod.snd_zero, zero_add] using h.symm

include hB hp in
/-- Angular integration and multiplication retain the input radius and external shift. -/
theorem potentialPath_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤
      D*majorant R d n) (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate P a (potentialPath P B p)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  apply product_orbit_block_bound P B hB directions hd q (pathPrimitive P p)
    (pathPrimitive_orbit_contDiff P p hp) Rc C R (P*D) hRc hC
    (mul_nonneg (le_of_lt (Fact.out : 0 < P)) hD) hR hbB d _ n
  intro j
  have h := pathPrimitive_block_bound P directions q
    (fun a : LiftTangent => pathTranslate P a p) hp j 0
  simp only [pathPrimitive_translation] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (hbp j) (le_of_lt (Fact.out : 0 < P))).trans_eq
    (mul_assoc P D _).symm)

end EulerCylinderPotential
