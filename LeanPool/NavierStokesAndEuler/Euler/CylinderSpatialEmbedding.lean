/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderTranslation
public import LeanPool.NavierStokesAndEuler.Euler.LpBochnerRealization
public import Mathlib.MeasureTheory.Function.LpSeminorm.Prod

@[expose] public section

/-! The genuine constant-angle embedding of ordinary spatial L² into cylinder L². -/

noncomputable section

namespace EulerCylinderSpatialEmbedding

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpCylinderTranslation EulerLpBochnerRealization

variable (P : ℝ) [Fact (0 < P)]

abbrev SpatialL2 (V : Type*) [NormedAddCommGroup V] := Lp V 2 (volume : Measure Space)

section Embedding

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

omit [NormedSpace ℝ V] in
theorem lifted_memLp (u : SpatialL2 V) :
    MemLp (fun z : LiftDomain P => u z.1) 2 (liftMeasure P) :=
  (Lp.memLp u).comp_fst (volume : Measure (AddCircle P))

def lift (u : SpatialL2 V) : CylinderL2 P V :=
  (lifted_memLp P u).toLp (fun z : LiftDomain P => u z.1)

omit [NormedSpace ℝ V] in
theorem lift_ae (u : SpatialL2 V) :
    (lift P u : LiftDomain P → V) =ᵐ[liftMeasure P] (fun z => u z.1) :=
  (lifted_memLp P u).coeFn_toLp

omit [NormedSpace ℝ V] in
theorem lift_add (u v : SpatialL2 V) : lift P (u+v) = lift P u+lift P v := by
  apply Lp.ext
  filter_upwards [lift_ae P (u+v), lift_ae P u, lift_ae P v,
    Lp.coeFn_add (lift P u) (lift P v),
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae (Lp.coeFn_add u v)] with z huv hu hv ha hs
  change (lift P (u+v)) z = (lift P u+lift P v) z
  rw [huv, ha]
  change (u+v) z.1 = (lift P u) z+(lift P v) z
  rw [hu,hv]
  exact hs

theorem lift_smul (r : ℝ) (u : SpatialL2 V) : lift P (r • u) = r • lift P u := by
  apply Lp.ext
  filter_upwards [lift_ae P (r • u), lift_ae P u, Lp.coeFn_smul r (lift P u),
    (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure Space))
      (ν := (volume : Measure (AddCircle P)))).ae (Lp.coeFn_smul r u)] with z hru hu ha hs
  change (lift P (r • u)) z = (r • lift P u) z
  rw [hru,ha]
  change (r • u) z.1 = r • (lift P u) z
  rw [hu]
  exact hs

omit [NormedSpace ℝ V] in
/-- The angle factor in the true product-space L² norm is exactly the period. -/
theorem lift_norm_sq (u : SpatialL2 V) : ‖lift P u‖^2 = P*‖u‖^2 := by
  have hP : 0 ≤ P := le_of_lt (Fact.out : 0 < P)
  calc
    _ = ∫ z, ‖(lift P u) z‖^2 ∂liftMeasure P := norm_sq_eq_integral (lift P u)
    _ = ∫ z : LiftDomain P, ‖u z.1‖^2 ∂liftMeasure P := by
      apply integral_congr_ae
      filter_upwards [lift_ae P u] with z hz
      rw [hz]
    _ = ∫ x : Space, ∫ θ : AddCircle P, ‖u x‖^2 := by
      exact integral_prod _ ((memLp_two_iff_integrable_sq_norm
        (lifted_memLp P u).aestronglyMeasurable).mp (lifted_memLp P u))
    _ = P*(∫ x : Space, ‖u x‖^2) := by
      simp only [integral_const, measureReal_def, AddCircle.measure_univ,
        ENNReal.toReal_ofReal hP, smul_eq_mul]
      exact integral_const_mul P (fun x : Space => ‖u x‖^2)
    _ = _ := congrArg (P * ·) (norm_sq_eq_integral u).symm

omit [NormedSpace ℝ V] in
theorem lift_norm_le (u : SpatialL2 V) : ‖lift P u‖ ≤ Real.sqrt P*‖u‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg P) (norm_nonneg u))).mp
  rw [mul_pow, Real.sq_sqrt (le_of_lt (Fact.out : 0 < P))]
  exact le_of_eq (lift_norm_sq P u)

def embeddingLinear : SpatialL2 V →ₗ[ℝ] CylinderL2 P V where
  toFun := lift P
  map_add' := lift_add P
  map_smul' := lift_smul P

def embedding : SpatialL2 V →L[ℝ] CylinderL2 P V :=
  (embeddingLinear P).mkContinuous (Real.sqrt P) (lift_norm_le P)

@[simp] theorem embedding_apply (u : SpatialL2 V) : embedding P u = lift P u := rfl

theorem embedding_norm : ‖embedding (V := V) P‖ ≤ Real.sqrt P :=
  opNorm_le_bound _ (Real.sqrt_nonneg P) (lift_norm_le P)

end Embedding

section Inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem embedding_inner (u v : SpatialL2 V) :
    inner ℝ (embedding P u) (embedding P v) = P*inner ℝ u v := by
  have h := lift_norm_sq P (u+v)
  rw [lift_add, norm_add_sq_real, norm_add_sq_real, lift_norm_sq, lift_norm_sq] at h
  change inner ℝ (lift P u) (lift P v) = _
  nlinarith

end Inner
end EulerCylinderSpatialEmbedding
