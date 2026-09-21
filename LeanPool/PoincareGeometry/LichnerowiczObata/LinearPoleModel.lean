/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.NormalChartRadialFlow
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! # Transporting Cartesian pole models alongAlmostSchur a linear isometry -/

@[expose] public noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace LichnerowiczObata
/-- Changing angular coordinates by a linear isometry preserves the
Cartesian pole model and its isometric derivative. -/
theorem HasRadialPoleModel.precompose_linearIsometry
    {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    {Ψ : V × ℝ → M} {p : M} (hmodel : HasRadialPoleModel I Ψ p)
    (L : P ≃ₗᵢ[ℝ] V) :
    HasRadialPoleModel I (fun q : P × ℝ => Ψ (L q.1, q.2)) p := by
  obtain ⟨χ, hχ0, hχ, hm, δ, hδ, hpolar⟩ := hmodel
  have hL : ContMDiff 𝓘(ℝ, P) 𝓘(ℝ, V) ∞ L := L.contDiff.contMDiff
  have hc : ContMDiffAt 𝓘(ℝ, V) I ∞ χ (L 0) := by simpa only [map_zero] using hχ
  refine ⟨χ ∘ L, by simpa only [Function.comp_apply, map_zero] using hχ0,
    hc.comp 0 (hL 0), ?_, δ, hδ, ?_⟩
  · intro v w
    have hdL : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, V) L 0 := (hL 0).mdifferentiableAt (by norm_num)
    have he (v : P) : mfderiv 𝓘(ℝ, P) 𝓘(ℝ, V) L 0 v = L v := by
      rw [mfderiv_eq_fderiv]
      change fderiv ℝ L 0 v = L v
      convert congrArg (fun D : P →L[ℝ] V => D v) (L.toContinuousLinearEquiv.fderiv (x := (0 : P)))
        using 1 <;> rfl
    have he' (a : P) :
        mfderiv 𝓘(ℝ, P) 𝓘(ℝ, V) L 0 ((NormedSpace.fromTangentSpace (0 : P)).symm a) =
          (NormedSpace.fromTangentSpace (L (0 : P))).symm (L a) := by
      convert! he a
    change inner ℝ
      (mfderiv 𝓘(ℝ, P) I (χ ∘ L) 0 ((NormedSpace.fromTangentSpace (0 : P)).symm v))
      (mfderiv 𝓘(ℝ, P) I (χ ∘ L) 0 ((NormedSpace.fromTangentSpace (0 : P)).symm w)) =
        inner ℝ v w
    rw [mfderiv_comp_apply _ (hc.mdifferentiableAt (by norm_num)) hdL,
      mfderiv_comp_apply _ (hc.mdifferentiableAt (by norm_num)) hdL,
      he', he', map_zero]
    rw [show (χ ∘ L) (0 : P) = χ (0 : V) by simp only [Function.comp_apply, map_zero]]
    exact (hm (L v) (L w)).trans (L.inner_map_map v w)
  · intro u r hr
    let v : Metric.sphere (0 : V) 1 := ⟨L (u : P), by
      rw [mem_sphere_zero_iff_norm, L.norm_map]
      exact mem_sphere_zero_iff_norm.mp u.property⟩
    simpa only [Function.comp_apply, map_smul] using hpolar v r hr

end LichnerowiczObata
