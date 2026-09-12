/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-! Continuous coefficient data for the correction source, with proved uniform ball bounds. -/

section

/-! Quantitative bounds for the actual projected linear-plus-quadratic source of the correction
equation. -/

@[expose] public section

noncomputable section

namespace EulerQuadraticSource

open Set
open scoped Topology

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- A pressure-projected source with actual forcing, linear terms, and quadratic terms. -/
def source (P : Y →L[ℝ] Y) (r : Y) (A : X →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y) (u : X) : Y :=
  -(P (r + A u + B u u))

/-- The actual quadratic source is jointly continuous in every coefficient and its unknown. -/
theorem source_continuous {T : Type*} [TopologicalSpace T]
    (P : T → Y →L[ℝ] Y) (r : T → Y) (A : T → X →L[ℝ] Y) (B : T → X →L[ℝ] X →L[ℝ] Y)
    (hP : Continuous P) (hr : Continuous r) (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun p : T × X => source (P p.1) (r p.1) (A p.1) (B p.1) p.2) := by
  exact ((hP.comp continuous_fst).clm_apply (((hr.comp continuous_fst).add
    ((hA.comp continuous_fst).clm_apply continuous_snd)).add
      (((hB.comp continuous_fst).clm_apply continuous_snd).clm_apply continuous_snd))).neg

/-- The exact product difference identity needs no symmetry of the bilinear source. -/
theorem quadratic_sub (B : X →L[ℝ] X →L[ℝ] Y) (u v : X) :
    B u u - B v v = B (u-v) u + B v (u-v) := by
  simp only [map_sub, sub_apply]
  abel

/-- The quadratic source has the genuine pointwise bound used for Picard existence. -/
theorem source_bound (P : Y →L[ℝ] Y) (r : Y) (A : X →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y)
    (R : ℝ) (hR : 0 ≤ R) (u : X) (hu : ‖u‖ ≤ R) :
    ‖source P r A B u‖ ≤ ‖P‖ * (‖r‖ + ‖A‖ * R + ‖B‖ * R^2) := by
  have hA := (A.le_opNorm u).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg A))
  have hB := (B.le_opNorm₂ u u).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left hu (norm_nonneg B)) hu (norm_nonneg u)
      (mul_nonneg (norm_nonneg B) hR))
  have hs : ‖r + A u + B u u‖ ≤ ‖r‖ + ‖A‖ * R + ‖B‖ * R^2 := by
    calc
      ‖r + A u + B u u‖ ≤ ‖r‖ + ‖A u‖ + ‖B u u‖ := (norm_add_le _ _).trans (add_le_add (norm_add_le
          _ _) le_rfl)
      _ ≤ ‖r‖ + ‖A‖ * R + ‖B‖ * R * R := add_le_add (add_le_add le_rfl hA) hB
      _ = _ := by ring
  simpa only [source, norm_neg] using (P.le_opNorm (r + A u + B u u)).trans
    (mul_le_mul_of_nonneg_left hs (norm_nonneg P))

/-- The quadratic source is Lipschitz on each norm ball, with an explicit finite constant. -/
theorem source_sub_bound (P : Y →L[ℝ] Y) (r : Y) (A : X →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y)
    (R : ℝ) (_hR : 0 ≤ R) (u v : X) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖source P r A B u - source P r A B v‖ ≤ ‖P‖ * (‖A‖ + 2 * ‖B‖ * R) * ‖u-v‖ := by
  have he : source P r A B u - source P r A B v = -(P (A (u-v) + B (u-v) u + B v (u-v))) := by
    simp only [source, map_add, map_sub, sub_apply]
    abel
  have h1 : ‖B (u-v) u‖ ≤ ‖B‖ * ‖u-v‖ * R := (B.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_left hu (mul_nonneg (norm_nonneg B) (norm_nonneg _)))
  have h2 : ‖B v (u-v)‖ ≤ ‖B‖ * R * ‖u-v‖ := (B.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hv (norm_nonneg B)) (norm_nonneg _))
  have hs : ‖A (u-v) + B (u-v) u + B v (u-v)‖ ≤ (‖A‖ + 2 * ‖B‖ * R) * ‖u-v‖ := by
    calc
      ‖A (u-v) + B (u-v) u + B v (u-v)‖ ≤ ‖A (u-v)‖ + ‖B (u-v) u‖ + ‖B v (u-v)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ ‖A‖ * ‖u-v‖ + ‖B‖ * ‖u-v‖ * R + ‖B‖ * R * ‖u-v‖ := add_le_add (add_le_add (A.le_opNorm _)
          h1) h2
      _ = _ := by ring
  rw [he, norm_neg]
  exact (P.le_opNorm _).trans ((mul_le_mul_of_nonneg_left hs (norm_nonneg P)).trans_eq (mul_assoc _
      _ _).symm)

/-- Uniform pointwise coefficient bounds imply the actual source bound on every ball. -/
theorem source_uniform_bound (P : Y →L[ℝ] Y) (r : Y) (A : X →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y)
    (p₀ r₀ a₀ b₀ R : ℝ) (hp : ‖P‖ ≤ p₀) (hr : ‖r‖ ≤ r₀) (ha : ‖A‖ ≤ a₀) (hb : ‖B‖ ≤ b₀)
    (hR : 0 ≤ R) (u : X) (hu : ‖u‖ ≤ R) :
    ‖source P r A B u‖ ≤ p₀ * (r₀ + a₀*R + b₀*R^2) := by
  apply (source_bound P r A B R hR u hu).trans
  apply mul_le_mul hp
    (add_le_add (add_le_add hr (mul_le_mul_of_nonneg_right ha hR)) (mul_le_mul_of_nonneg_right hb
        (sq_nonneg R)))
  · positivity
  · exact (norm_nonneg P).trans hp

/-- Uniform coefficient bounds imply the required local Lipschitz constant. -/
theorem source_uniform_sub_bound (P : Y →L[ℝ] Y) (r : Y) (A : X →L[ℝ] Y) (B : X →L[ℝ] X →L[ℝ] Y)
    (p₀ a₀ b₀ R : ℝ) (hp : ‖P‖ ≤ p₀) (ha : ‖A‖ ≤ a₀) (hb : ‖B‖ ≤ b₀)
    (hR : 0 ≤ R) (u v : X) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖source P r A B u - source P r A B v‖ ≤ p₀ * (a₀ + 2*b₀*R) * ‖u-v‖ := by
  apply (source_sub_bound P r A B R hR u v hu hv).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply mul_le_mul hp
    (add_le_add ha (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) hR))
  · positivity
  · exact (norm_nonneg P).trans hp

end EulerQuadraticSource

end
end

end

@[expose] public section

noncomputable section

namespace EulerQuadraticSource

open Set
open scoped Topology

variable {X Y T : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [TopologicalSpace T]

/-- Actual continuous data for the pressure-projected quadratic source. -/
structure Coefficients (T : Type*) [TopologicalSpace T] (X Y : Type*)
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] where
  /-- Projection of `Coefficients`, of type `C(T, Y →L[ℝ] Y)`. -/
  projection : C(T, Y →L[ℝ] Y)
  /-- Forcing of `Coefficients`, of type `C(T, Y)`. -/
  forcing : C(T, Y)
  /-- Linear of `Coefficients`, of type `C(T, X →L[ℝ] Y)`. -/
  linear : C(T, X →L[ℝ] Y)
  /-- Quadratic of `Coefficients`, of type `C(T, X →L[ℝ] X →L[ℝ] Y)`. -/
  quadratic : C(T, X →L[ℝ] X →L[ℝ] Y)

/-- Evaluate the genuine projected source. -/
def Coefficients.apply (C : Coefficients T X Y) (t : T) (u : X) : Y :=
  source (C.projection t) (C.forcing t) (C.linear t) (C.quadratic t) u

/-- The source is jointly continuous in time and the Sobolev unknown. -/
theorem Coefficients.continuous (C : Coefficients T X Y) :
    Continuous (fun p : T × X => C.apply p.1 p.2) :=
  source_continuous _ _ _ _ C.projection.continuous C.forcing.continuous C.linear.continuous
      C.quadratic.continuous

/-- Restrict coefficient data along any continuous parameter map. -/
def Coefficients.comp {U : Type*} [TopologicalSpace U] (C : Coefficients T X Y) (f : C(U, T)) :
    Coefficients U X Y where
  projection := C.projection.comp f
  forcing := C.forcing.comp f
  linear := C.linear.comp f
  quadratic := C.quadratic.comp f

@[simp] theorem Coefficients.comp_apply {U : Type*} [TopologicalSpace U]
    (C : Coefficients T X Y) (f : C(U, T)) (t : U) (u : X) : (C.comp f).apply t u = C.apply (f t) u
        := rfl

/-- Cache the standard `SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y)` instance to shorten
typeclass synthesis. -/
local instance nestedGroup : SeminormedAddCommGroup (X →L[ℝ] X →L[ℝ] Y) := inferInstance

variable [CompactSpace T]

/-- A uniform norm bound for the actual source on a ball. -/
def Coefficients.ballBound (C : Coefficients T X Y) (R : ℝ) : ℝ :=
  ‖C.projection‖ * (‖C.forcing‖ + ‖C.linear‖*R + ‖C.quadratic‖*R^2)

/-- A uniform Lipschitz constant for the actual source on a ball. -/
def Coefficients.ballLipschitz (C : Coefficients T X Y) (R : ℝ) : ℝ :=
  ‖C.projection‖ * (‖C.linear‖ + 2*‖C.quadratic‖*R)

theorem Coefficients.ballBound_nonneg (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ C.ballBound R := by unfold Coefficients.ballBound; positivity

theorem Coefficients.ballLipschitz_nonneg (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ C.ballLipschitz R := by unfold Coefficients.ballLipschitz; positivity

/-- The uniform source bound follows from actual operator norms, with no assumed nonlinear estimate.
-/
theorem Coefficients.apply_bound (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R)
    (t : T) (u : X) (hu : ‖u‖ ≤ R) : ‖C.apply t u‖ ≤ C.ballBound R :=
  source_uniform_bound _ _ _ _ _ _ _ _ R
    (C.projection.norm_coe_le_norm t) (C.forcing.norm_coe_le_norm t)
    (C.linear.norm_coe_le_norm t) (C.quadratic.norm_coe_le_norm t) hR u hu

/-- The uniform local Lipschitz estimate follows from the proved quadratic difference identity. -/
theorem Coefficients.apply_sub_bound (C : Coefficients T X Y) (R : ℝ) (hR : 0 ≤ R)
    (t : T) (u v : X) (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) :
    ‖C.apply t u-C.apply t v‖ ≤ C.ballLipschitz R * ‖u-v‖ :=
  source_uniform_sub_bound _ _ _ _ _ _ _ R
    (C.projection.norm_coe_le_norm t) (C.linear.norm_coe_le_norm t)
    (C.quadratic.norm_coe_le_norm t) hR u v hu hv

end EulerQuadraticSource
