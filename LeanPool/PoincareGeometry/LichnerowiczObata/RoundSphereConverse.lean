/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereHeightHessian
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundMetricDiffeomorph
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaConnection

/-! # The round-sphere converse: an actual extremal eigenfunction -/

@[expose] public noncomputable section
open Bundle Set AlmostSchur
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [Nonempty M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A] [FiniteDimensional ℝ A]
  [Fact (Module.finrank ℝ A = Module.finrank ℝ E + 1)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "LC" => (leviCivitaConnection (I := I) (M := M))

/-- A round-metric diffeomorphism produces a smooth nonconstant height
eigenfunction. The Hessian and Laplacian equations are proved for the actual
Levi-Civita connection of the source metric. -/
theorem round_metric_diffeomorph_exists_extremal_eigenfunction
    {K : ℝ} (hK : 0 < K)
    (d : M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ Metric.sphere (0 : A) 1)
    (hm : ∀ (x : M) (v w : TM x),
      inner ℝ (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : A)) x v)
        (mvfderiv I (fun y : M => (1 / Real.sqrt K) • (d y : A)) x w) = inner ℝ v w) :
    ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧ (∃ x y, f x ≠ f y) ∧
      (∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w) ∧
      ∀ x, laplacian LC f x = -((Module.finrank ℝ E : ℝ) * K) * f x := by
  let R := 1 / Real.sqrt K
  have hR : 0 < R := one_div_pos.mpr (Real.sqrt_pos.mpr hK)
  let F := fun y : M => R • (d y : A)
  have hF : ContMDiff I 𝓘(ℝ, A) ∞ F :=
    ((R • ContinuousLinearMap.id ℝ A).contDiff.contMDiff).comp
      (contMDiff_coe_sphere.comp d.contMDiff)
  have hn : ∀ y, ‖F y‖ = R := by
    intro y
    simp only [F, norm_smul, Real.norm_eq_abs, abs_of_pos hR, norm_eq_of_mem_sphere, mul_one]
  let x₀ : M := Classical.choice ‹Nonempty M›
  let a := F x₀
  let f := fun y => inner ℝ a (F y)
  have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := (innerSL ℝ a).contDiff.contMDiff.comp hF
  let q : Metric.sphere (0 : A) 1 := ⟨-(d x₀ : A), by
    rw [mem_sphere_zero_iff_norm, norm_neg, norm_eq_of_mem_sphere]⟩
  have hneg : F (d.symm q) = -F x₀ := by
    simp only [F, d.apply_symm_apply, q, smul_neg]
  have hnon : ∃ x y, f x ≠ f y := by
    refine ⟨x₀, d.symm q, ?_⟩
    intro he
    change inner ℝ (F x₀) (F x₀) = inner ℝ (F x₀) (F (d.symm q)) at he
    rw [hneg, inner_neg_right, real_inner_self_eq_norm_sq, hn] at he
    nlinarith [sq_pos_of_pos hR]
  have hscale : (R ^ 2)⁻¹ = K := by
    dsimp [R]
    rw [one_div, inv_pow, inv_inv, Real.sq_sqrt hK.le]
  have hH : ∀ (x : M) (v w : TM x), hessian LC f x v w = -K * f x * inner ℝ v w := by
    intro x v w
    have hh := hessian_height_of_sphere_metric_immersion LC
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
      (hF.of_le (by decide)) hR hn hm Fact.out a x v w
    change hessian LC f x v w = -(f x / R ^ 2) * inner ℝ v w at hh
    rw [hh, div_eq_mul_inv, hscale]
    ring
  refine ⟨f, hf, hnon, hH, ?_⟩
  intro x
  let : FiniteDimensional ℝ (TM x) := inferInstanceAs (FiniteDimensional ℝ E)
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [laplacian_eq_sum_hessian LC f x b]
  simp only [hH, real_inner_self_eq_norm_sq, b.orthonormal.norm_eq_one,
    one_pow, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [VectorBundle.finrank_eq ℝ E TM x]
  ring

end LichnerowiczObata
