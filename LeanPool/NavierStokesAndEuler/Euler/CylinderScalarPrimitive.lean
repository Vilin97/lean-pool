/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderConstantMap
public import LeanPool.NavierStokesAndEuler.Euler.CylinderAnglePrimitive

@[expose] public section

/-!
# The genuine scalar angular primitive on cylinder L²

A fixed unit scalar embedding and its norm-one projection transfer the
constructed vector primitive to scalar pressure. Its mixed-translation
commutation and fixed-Hq external-word bound have no radius loss.
-/

noncomputable section

namespace EulerCylinderScalarPrimitive

open Set MeasureTheory ContinuousLinearMap InnerProductSpace EulerSmoothLimit
  EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerCylinderConstantMap EulerParameterWordGevrey
open scoped ContDiff

def unitVector : Space := EuclideanSpace.single 0 1

theorem unitVector_norm : ‖unitVector‖ = 1 := by simp [unitVector]

def scalarEmbed : ℝ →L[ℝ] Space := toSpanSingleton ℝ unitVector
def scalarProject : Space →L[ℝ] ℝ := innerSL ℝ unitVector

theorem scalarEmbed_norm : ‖scalarEmbed‖ = 1 := by
  rw [scalarEmbed,norm_toSpanSingleton,unitVector_norm]

theorem scalarProject_norm : ‖scalarProject‖ = 1 := by
  rw [scalarProject,innerSL_apply_norm,unitVector_norm]

@[simp] theorem project_embed (r : ℝ) : scalarProject (scalarEmbed r) = r := by
  change ⟪unitVector,r • unitVector⟫_ℝ = r
  rw [inner_smul_right,real_inner_self_eq_norm_sq,unitVector_norm,one_pow,mul_one]

variable (period : ℝ) [Fact (0 < period)]

def embed : CylinderL2 period ℝ →L[ℝ] LiftL2 period := EulerCylinderConstantMap.map period
  scalarEmbed
def project : LiftL2 period →L[ℝ] CylinderL2 period ℝ := EulerCylinderConstantMap.map period
  scalarProject

theorem embed_norm : ‖embed period‖ ≤ 1 :=
  (map_norm period scalarEmbed).trans_eq scalarEmbed_norm

theorem project_norm : ‖project period‖ ≤ 1 :=
  (map_norm period scalarProject).trans_eq scalarProject_norm

def primitive : CylinderL2 period ℝ →L[ℝ] CylinderL2 period ℝ :=
  (project period).comp ((EulerCylinderAnglePrimitive.primitive period).comp (embed period))

theorem primitive_norm : ‖primitive period‖ ≤ period := by
  have hP : 0 < period := Fact.out
  apply opNorm_le_bound _ hP.le
  intro u
  change ‖project period (EulerCylinderAnglePrimitive.primitive period (embed period u))‖ ≤
    period*‖u‖
  calc
    _ ≤ ‖EulerCylinderAnglePrimitive.primitive period (embed period u)‖ :=
      ((project period).le_opNorm _).trans (by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (project_norm period) (norm_nonneg _))
    _ ≤ period*‖embed period u‖ := ((EulerCylinderAnglePrimitive.primitive period).le_opNorm
      _).trans
      (mul_le_mul_of_nonneg_right (EulerCylinderAnglePrimitive.primitive_norm period) (norm_nonneg
        _))
    _ ≤ period*‖u‖ := mul_le_mul_of_nonneg_left (((embed period).le_opNorm u).trans (by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (embed_norm period) (norm_nonneg u)))
        hP.le

/-- All mixed translations commute with the actual scalar primitive. -/
theorem primitive_translation (a : LiftTangent) (u : CylinderL2 period ℝ) :
    primitive period (translate period a u) = translate period a (primitive period u) := by
  change EulerCylinderConstantMap.map period scalarProject
      (EulerCylinderAnglePrimitive.primitive period (EulerCylinderConstantMap.map period scalarEmbed
        (translate period a u))) = _
  rw [map_translation]
  have hv : EulerCylinderAnglePrimitive.primitive period
      (translate period a (EulerCylinderConstantMap.map period scalarEmbed u)) =
      translate period a (EulerCylinderAnglePrimitive.primitive period
        (EulerCylinderConstantMap.map period scalarEmbed u)) :=
    EulerCylinderAnglePrimitive.primitive_translation period (coveringMap period a)
      (EulerCylinderConstantMap.map period scalarEmbed u)
  rw [hv,map_translation]
  rfl

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

private local instance : NormedAddCommGroup (CylinderL2 period ℝ) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period ℝ) := inferInstance
private local instance : NormedAddCommGroup C(K,CylinderL2 period ℝ) := inferInstance
private local instance : NormedSpace ℝ C(K,CylinderL2 period ℝ) := inferInstance

def pathPrimitive : C(K,CylinderL2 period ℝ) →L[ℝ] C(K,CylinderL2 period ℝ) :=
  (primitive period).compLeftContinuous ℝ K

theorem pathPrimitive_norm : ‖pathPrimitive (K := K) period‖ ≤ period := by
  have hP : 0 < period := Fact.out
  apply opNorm_le_bound _ hP.le
  intro u
  apply (ContinuousMap.norm_le _ (mul_nonneg hP.le (norm_nonneg u))).2
  intro t
  exact ((primitive period).le_opNorm (u t)).trans
    ((mul_le_mul_of_nonneg_right (primitive_norm period) (norm_nonneg (u t))).trans
      (mul_le_mul_of_nonneg_left (u.norm_coe_le_norm t) hP.le))

omit [CompactSpace K] in
theorem pathPrimitive_translation (a : LiftTangent) (u : C(K,CylinderL2 period ℝ)) :
    pathPrimitive period (pathTranslate period a u) = pathTranslate period a (pathPrimitive period
      u) := by
  apply ContinuousMap.ext
  intro t
  exact primitive_translation period a (u t)

theorem pathPrimitive_orbit_contDiff (u : C(K,CylinderL2 period ℝ))
    (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a u)) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (pathPrimitive period u)) := by
  have he : (fun a : LiftTangent => pathTranslate period a (pathPrimitive period u)) =
      (fun a => pathPrimitive period (pathTranslate period a u)) :=
    funext (fun a => (pathPrimitive_translation period a u).symm)
  rw [he]
  exact (pathPrimitive period).contDiff.comp hu

theorem pathPrimitive_block_le {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (q : ℕ)
    (u : C(K,CylinderL2 period ℝ)) (hu : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period
      a u))
    (n : ℕ) (a : LiftTangent) :
    block directions q (fun b : LiftTangent => pathTranslate period b (pathPrimitive period u)) n a
      ≤
      period*block directions q (fun b : LiftTangent => pathTranslate period b u) n a := by
  have he : (fun b : LiftTangent => pathTranslate period b (pathPrimitive period u)) =
      (fun b => pathPrimitive period (pathTranslate period b u)) :=
    funext (fun b => (pathPrimitive_translation period b u).symm)
  rw [he]
  exact (block_comp_clm_le (P := LiftTangent) (E := C(K,CylinderL2 period ℝ))
    (F := C(K,CylinderL2 period ℝ)) directions q (pathPrimitive (K := K) period)
    (fun b : LiftTangent => pathTranslate period b u) hu n a).trans
    (mul_le_mul_of_nonneg_right (pathPrimitive_norm (K := K) period)
      (block_nonneg directions q (fun b : LiftTangent => pathTranslate period b u) n a))

end EulerCylinderScalarPrimitive
