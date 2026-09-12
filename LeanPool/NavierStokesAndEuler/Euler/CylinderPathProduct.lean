/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSobolevOrbit
public import LeanPool.NavierStokesAndEuler.Euler.SobolevProduct
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathCalculus
public import LeanPool.NavierStokesAndEuler.Euler.CylinderTimeRegularity
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl
import LeanPool.NavierStokesAndEuler.Euler.ContinuousPathComposition

/-!
# Actual nonlinear products of smooth continuous cylinder paths

The existing complete H6 multiplication constructs the product. Its real
mixed translation orbit is smooth because each input has a smooth H6 orbit.
The output representative is the literal pointwise product at every point.
-/

@[expose] public section


noncomputable section

namespace EulerCylinderPathProduct

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSobolevSpace EulerCylinderSmoothOrbit EulerLpCylinderTranslation
  EulerSobolevL2Product EulerContinuousPathCalculus EulerContinuousTimeIntegral
  EulerContinuousPathComposition EulerMetricTransport
open scoped ContDiff

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

section Bilinear

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Cache the standard `NormedAddCommGroup (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct1 : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedSpace ℝ (F →L[ℝ] G)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct2 : NormedSpace ℝ (F →L[ℝ] G) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,E)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct3 : NormedAddCommGroup C(K,E) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,E)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct4 : NormedSpace ℝ C(K,E) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,F)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct5 : NormedAddCommGroup C(K,F) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,F)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct6 : NormedSpace ℝ C(K,F) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(K,G)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct7 : NormedAddCommGroup C(K,G) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(K,G)` instance to shorten typeclass synthesis. -/
local instance instCylinderPathProduct8 : NormedSpace ℝ C(K,G) := inferInstance
/-- Cache the standard `NormedAddCommGroup (C(K,F) →L[ℝ] C(K,G))` instance to shorten typeclass
synthesis. -/
local instance instCylinderPathProduct9 : NormedAddCommGroup (C(K,F) →L[ℝ] C(K,G)) := inferInstance
/-- Cache the standard `NormedSpace ℝ (C(K,F) →L[ℝ] C(K,G))` instance to shorten typeclass
synthesis. -/
local instance instCylinderPathProduct10 : NormedSpace ℝ (C(K,F) →L[ℝ] C(K,G)) := inferInstance

/-- A genuine bounded bilinear map acts pointwise on continuous paths. -/
def pathBilinear (B : E →L[ℝ] F →L[ℝ] G) : C(K,E) →L[ℝ] C(K,F) →L[ℝ] C(K,G) :=
  coefficientMap.comp (B.compLeftContinuous ℝ K)

@[simp] theorem pathBilinear_apply (B : E →L[ℝ] F →L[ℝ] G)
    (p : C(K, E)) (q : C(K, F)) (t : K) : pathBilinear B p q t = B (p t) (q t) := rfl

theorem pathBilinear_norm (B : E →L[ℝ] F →L[ℝ] G) :
    ‖pathBilinear (K := K) B‖ ≤ ‖B‖ :=
  (opNorm_comp_le _ _).trans ((mul_le_mul coefficientMap_norm (postcomposition_norm B)
    (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))

theorem contDiff_pathBilinear {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (B : E →L[ℝ] F →L[ℝ] G) (f : X → C(K, E)) (g : X → C(K, F))
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun x => pathBilinear B (f x) (g x)) :=
  ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,E)) (F := C(K,F) →L[ℝ] C(K,G)) (pathBilinear (K := K) B)).comp hf).clm_apply hg

end Bilinear

variable (P : ℝ) [Fact (0 < P)] (L : Space →L[ℝ] ℝ) (hL : ‖L‖ ≤ 1)
  (p q : C(K, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hq : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a q))

/-- The actual continuous L² product, constructed in the complete H6 algebra. -/
def scalarProductPath : C(K,LiftL2 P) :=
  (valueOperator P 6).compLeftContinuous ℝ K
    (pathBilinear (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)
      (sobolevPath P 6 p hp) (sobolevPath P 6 q hq))

theorem scalarProductPath_apply (t : K) :
    scalarProductPath P L hL p q hp hq t = scalarProduct P (by norm_num : 3 ≤ 6) L
      (sobolevPath P 6 p hp t) (q t) := by
  change value P (productHq P (by norm_num : 6 ≤ 6) L hL
    (sobolevPath P 6 p hp t) (sobolevPath P 6 q hq t)) = _
  rw [productHq_value, sobolevPath_value]

theorem scalarProductPath_orbit_formula (a : LiftTangent) :
    pathTranslate P a (scalarProductPath P L hL p q hp hq) =
      (valueOperator P 6).compLeftContinuous ℝ K
        (pathBilinear (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)
          (sobolevOrbit P 6 p hp a) (sobolevOrbit P 6 q hq a)) := by
  apply ContinuousMap.ext
  intro t
  change translate P a (scalarProductPath P L hL p q hp hq t) =
    value P (productHq P (by norm_num : 6 ≤ 6) L hL
      (sobolevOrbit P 6 p hp a t) (sobolevOrbit P 6 q hq a t))
  rw [scalarProductPath_apply, productHq_value, sobolevOrbit_value]
  exact (scalarProduct_translation P (by norm_num : 3 ≤ 6) L (coveringMap P a)
    (sobolevPath P 6 p hp t) (q t)).symm

/-- Smoothness is for the actual output translation orbit, not an auxiliary family. -/
theorem scalarProductPath_orbit :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a (scalarProductPath P L hL p q hp hq)) :=
        by
  have he := funext (scalarProductPath_orbit_formula P L hL p q hp hq)
  rw [he]
  apply (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (E := C(K,SobolevSpace P 6)) (F := C(K,LiftL2 P))
    ((valueOperator P 6).compLeftContinuous ℝ K)).comp
  exact contDiff_pathBilinear (productHqBilinear P (by norm_num : 6 ≤ 6) L hL)
    (sobolevOrbit P 6 p hp) (sobolevOrbit P 6 q hq)
    (sobolevOrbit_contDiff P 6 p hp) (sobolevOrbit_contDiff P 6 q hq)

theorem scalarProductPath_ae (t : K) :
    (scalarProductPath P L hL p q hp hq t : LiftDomain P → Space) =ᵐ[liftMeasure P]
      fun x => L (pointField P p hp t x) • pointField P q hq t x := by
  rw [scalarProductPath_apply]
  filter_upwards [scalarProduct_ae P (by norm_num : 3 ≤ 6) L (sobolevPath P 6 p hp t) (q t),
    pointField_ae P p hp t, pointField_ae P q hq t] with x hs hp hq
  simpa only [sobolevPath_value, hp, hq] using hs

/-- The output smooth representative equals the literal nonlinear product everywhere. -/
theorem pointField_scalarProductPath (t : K) (x : LiftDomain P) :
    pointField P (scalarProductPath P L hL p q hp hq) (scalarProductPath_orbit P L hL p q hp hq) t
        x =
      L (pointField P p hp t x) • pointField P q hq t x := by
  have he := Measure.eq_of_ae_eq
    ((pointField_ae P _ (scalarProductPath_orbit P L hL p q hp hq) t).symm.trans
      (scalarProductPath_ae P L hL p q hp hq t))
    (smoothField_continuous P _ (pointField_smooth P _ _ t))
    ((L.continuous.comp (smoothField_continuous P _ (pointField_smooth P p hp t))).smul
      (smoothField_continuous P _ (pointField_smooth P q hq t)))
  exact congrFun he x

end EulerCylinderPathProduct
