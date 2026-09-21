/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothHomeomorphInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.UnitPolarCoordinates
public import Mathlib.Geometry.Manifold.Instances.Sphere

/-! # The intrinsic diffeomorphism underlying a round metric embedding -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A] {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I : M → Type _)]

omit [FiniteDimensional ℝ A] in
/-- Normalizing a radius-`R` metric embedding gives a diffeomorphism to the
standard unit sphere. Rescaling its ambient inclusion recovers the original
map exactly, and therefore recovers the radius-`R` induced metric. -/
theorem exists_round_metric_diffeomorph
    {R : ℝ} (hR : 0 < R) (hDim : Module.finrank ℝ E = n)
    (Q : Metric.sphere (0 : A) R ≃ₜ M)
    (hf : ContMDiff I 𝓘(ℝ, A) ∞ (fun y : M => (Q.symm y : A)))
    (hm : ∀ (x : M) (v w : TangentSpace I x),
      inner ℝ (mvfderiv I (fun y : M => (Q.symm y : A)) x v)
        (mvfderiv I (fun y : M => (Q.symm y : A)) x w) = inner ℝ v w) :
    ∃ d : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : A) 1,
      (∀ x, R • (d x : A) = (Q.symm x : A)) ∧
      ∀ (x : M) (v w : TangentSpace I x),
        inner ℝ (mvfderiv I (fun y : M => R • (d y : A)) x v)
          (mvfderiv I (fun y : M => R • (d y : A)) x w) = inner ℝ v w := by
  let T := fun y : M => (Q.symm y : A)
  let U : M ≃ₜ Metric.sphere (0 : A) 1 := Q.symm.trans (unitSphereScale R hR).symm
  have hco : ContMDiff I 𝓘(ℝ, A) ∞ (fun y : M => (U y : A)) := by
    exact ((R⁻¹ • ContinuousLinearMap.id ℝ A).contDiff.contMDiff).comp hf
  have hU : ContMDiff I (𝓡 n) ∞ U := by
    exact hco.codRestrict_sphere (fun y => (U y).property)
  let B : Metric.sphere (0 : A) 1 → A := fun u => R • (u : A)
  have hB : ContMDiff (𝓡 n) 𝓘(ℝ, A) ∞ B :=
    ((R • ContinuousLinearMap.id ℝ A).contDiff.contMDiff).comp contMDiff_coe_sphere
  have hBU : B ∘ U = T := by
    funext y
    simp [B, U, T, unitSphereScale, smul_smul, hR.ne']
  have hinj : ∀ x, Function.Injective (mfderiv I (𝓡 n) U x) := by
    intro x v w hvw
    have hc := mfderiv_comp (f := (U : M → Metric.sphere (0 : A) 1)) (g := B) x
      ((hB _).mdifferentiableAt (by norm_num)) ((hU x).mdifferentiableAt (by norm_num))
    rw [hBU] at hc
    have he : mvfderiv I T x v = mvfderiv I T x w := by
      change mfderiv I 𝓘(ℝ, A) T x v = mfderiv I 𝓘(ℝ, A) T x w
      rw [hc]
      exact congrArg (mfderiv (𝓡 n) 𝓘(ℝ, A) B (U x)) hvw
    have hz : mvfderiv I T x (v - w) = 0 := by rw [map_sub, he, sub_self]
    have hh := hm x (v - w) (v - w)
    change inner ℝ (mvfderiv I T x (v - w)) (mvfderiv I T x (v - w)) = _ at hh
    rw [hz, inner_zero_left] at hh
    exact sub_eq_zero.mp (inner_self_eq_zero.mp hh.symm)
  have hdimension : Module.finrank ℝ E = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa using hDim
  obtain ⟨d, hd, _⟩ := exists_diffeomorph_of_homeomorphic_immersion U hdimension hU hinj
  have hscale : (fun y : M => R • (d y : A)) = T := by
    rw [hd]
    exact hBU
  refine ⟨d, fun x => congrFun hscale x, ?_⟩
  intro x v w
  rw [hscale]
  exact hm x v w

end LichnerowiczObata
