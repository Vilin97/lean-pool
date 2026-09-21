/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundMetricDiffeomorph

/-! # Canonical Euclidean targets for round-metric diffeomorphisms -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]
  {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)] [Fact (Module.finrank ℝ B = n + 1)]

/-- An ambient linear isometry restricts to a smooth sphere diffeomorphism
in the standard sphere charts, in both directions. -/
def sphereLinearIsometryDiffeomorph (L : A ≃ₗᵢ[ℝ] B) :
    Metric.sphere (0 : A) 1 ≃ₘ⟮𝓡 n, 𝓡 n⟯ Metric.sphere (0 : B) 1 := by
  let e : Metric.sphere (0 : A) 1 ≃ Metric.sphere (0 : B) 1 :=
    { toFun := fun u => ⟨L (u : A), by
        rw [mem_sphere_zero_iff_norm, L.norm_map, norm_eq_of_mem_sphere]⟩
      invFun := fun u => ⟨L.symm (u : B), by
        rw [mem_sphere_zero_iff_norm, L.symm.norm_map, norm_eq_of_mem_sphere]⟩
      left_inv := by intro u; apply Subtype.ext; exact L.symm_apply_apply _
      right_inv := by intro u; apply Subtype.ext; exact L.apply_symm_apply _ }
  have hf : ContMDiff (𝓡 n) (𝓡 n) ∞ e :=
    (L.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
      (fun u => (e u).property)
  have hg : ContMDiff (𝓡 n) (𝓡 n) ∞ e.symm :=
    (L.symm.toContinuousLinearEquiv.contDiff.contMDiff.comp contMDiff_coe_sphere).codRestrict_sphere
      (fun u => (e.symm u).property)
  exact ⟨e, hf, hg⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (TangentSpace I : M → Type _)]

omit [Fact (Module.finrank ℝ B = n + 1)] [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
/-- The choice of an auxiliary ambient inner-product space can be removed
without changing the radius or induced metric. -/
theorem exists_standard_round_metric_diffeomorph [FiniteDimensional ℝ A]
    {R : ℝ} (d : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : A) 1)
    (hm : ∀ (x : M) (v w : TangentSpace I x),
      inner ℝ (mvfderiv I (fun y : M => R • (d y : A)) x v)
        (mvfderiv I (fun y : M => R • (d y : A)) x w) = inner ℝ v w) :
    ∃ d' : M ≃ₘ⟮I, 𝓡 n⟯ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
      ∀ (x : M) (v w : TangentSpace I x),
        inner ℝ (mvfderiv I (fun y : M => R • (d' y : EuclideanSpace ℝ (Fin (n + 1)))) x v)
          (mvfderiv I (fun y : M => R • (d' y : EuclideanSpace ℝ (Fin (n + 1)))) x w) =
            inner ℝ v w := by
  let B := EuclideanSpace ℝ (Fin (n + 1))
  let : Fact (Module.finrank ℝ B = n + 1) := ⟨by simp [B]⟩
  let L : A ≃ₗᵢ[ℝ] B :=
    ((stdOrthonormalBasis ℝ A).reindex (finCongr (show Module.finrank ℝ A = n + 1 from Fact.out))).repr
  let s := sphereLinearIsometryDiffeomorph (n := n) L
  let d' := d.trans s
  let F := fun y : M => R • (d y : A)
  have hF : ContMDiff I 𝓘(ℝ, A) ∞ F :=
    ((R • ContinuousLinearMap.id ℝ A).contDiff.contMDiff).comp
      (contMDiff_coe_sphere.comp d.contMDiff)
  have he : (fun y : M => R • (d' y : B)) = (L : A → B) ∘ F := by
    funext y
    exact (L.map_smul R (d y : A)).symm
  refine ⟨d', ?_⟩
  intro x v w
  rw [he]
  have hL : ContMDiff 𝓘(ℝ, A) 𝓘(ℝ, B) ∞ (L : A → B) :=
    L.toContinuousLinearEquiv.contDiff.contMDiff
  have hd := mfderiv_comp (I := I) (I' := 𝓘(ℝ, A)) (I'' := 𝓘(ℝ, B))
    (f := F) (g := (L : A → B)) x (hL.mdifferentiable (by decide) (F x))
      (hF.mdifferentiable (by decide) x)
  have hLD : fderiv ℝ (L : A → B) (F x) = L.toContinuousLinearEquiv.toContinuousLinearMap :=
    L.toContinuousLinearEquiv.hasFDerivAt.fderiv
  simp only [mfderiv_eq_fderiv] at hd
  rw [hLD] at hd
  change inner ℝ (mfderiv I 𝓘(ℝ, B) ((L : A → B) ∘ F) x v)
    (mfderiv I 𝓘(ℝ, B) ((L : A → B) ∘ F) x w) = _
  rw [hd]
  change inner ℝ (L (mvfderiv I F x v)) (L (mvfderiv I F x w)) = inner ℝ v w
  rw [L.inner_map_map]
  exact hm x v w

end LichnerowiczObata
