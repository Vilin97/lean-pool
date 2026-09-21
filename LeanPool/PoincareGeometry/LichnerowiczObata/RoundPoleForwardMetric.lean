/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothIsometricInverse
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPoleGraph

/-! # Forward metric derivatives at either round pole -/

@[expose] public noncomputable section
open Bundle Set
open scoped Manifold ContDiff Topology
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]

/-- A tangent-isometric ambient inverse extension at a signed round pole
implies smoothness and metric preservation of the actual forward
comparison there. The comparison itself is used, not a replacement map. -/
theorem round_pole_forward_metric
    (hDim : Module.finrank ℝ P = Module.finrank ℝ E)
    {R ε : ℝ} (hR : 0 < R) (hε : ε ^ 2 = 1)
    (b : Metric.sphere (0 : RoundAmbient P) R)
    (hb : (b : RoundAmbient P) = (ε * R) • roundNorth)
    (Q : Metric.sphere (0 : RoundAmbient P) R ≃ₜ M) (N : RoundAmbient P → M)
    (hN0 : N (b : RoundAmbient P) = Q b)
    (hNd : ContMDiffAt 𝓘(ℝ, RoundAmbient P) I ∞ N (b : RoundAmbient P))
    (hNm : ∀ v w : P,
      inner ℝ (mfderiv 𝓘(ℝ, RoundAmbient P) I N (b : RoundAmbient P) (roundAngularInclusion v))
        (mfderiv 𝓘(ℝ, RoundAmbient P) I N (b : RoundAmbient P) (roundAngularInclusion w)) = inner ℝ v w)
    (hNeq : (fun z : Metric.sphere (0 : RoundAmbient P) R => N (z : RoundAmbient P)) =ᶠ[𝓝 b] Q) :
    let T := fun y : M => (Q.symm y : RoundAmbient P)
    ContMDiffAt I 𝓘(ℝ, RoundAmbient P) ∞ T (Q b) ∧
      ∀ v w : TangentSpace I (Q b),
        inner ℝ (mvfderiv I T (Q b) v) (mvfderiv I T (Q b) w) = inner ℝ v w := by
  let χ := N ∘ roundPoleGraph ε R
  let g := fun y : M => (WithLp.fstL 2 ℝ P ℝ) (Q.symm y : RoundAmbient P)
  have hgraph0 : roundPoleGraph ε R (0 : P) = (b : RoundAmbient P) :=
    (roundPoleGraph_zero ε hR.le).trans hb.symm
  have hχN0 : χ (0 : P) = N (b : RoundAmbient P) := by
    change N (roundPoleGraph ε R 0) = N (b : RoundAmbient P)
    rw [hgraph0]
  have hχ0 : χ (0 : P) = Q b := hχN0.trans hN0
  have hg0 : g (Q b) = 0 := by
    change (WithLp.fstL 2 ℝ P ℝ) (Q.symm (Q b) : RoundAmbient P) = 0
    rw [Q.symm_apply_apply, hb]
    simp [roundNorth]
  have hgraph := hasFDerivAt_roundPoleGraph_zero (P := P) ε hR
  have hgraphd : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, RoundAmbient P) (roundPoleGraph ε R) (0 : P) :=
    mdifferentiableAt_iff_differentiableAt.mpr hgraph.differentiableAt
  have hNgraph : MDifferentiableAt 𝓘(ℝ, RoundAmbient P) I N (roundPoleGraph ε R (0 : P)) := by
    rw [hgraph0]
    exact hNd.mdifferentiableAt (by norm_num)
  have hgraphSmooth : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, RoundAmbient P) ∞
      (roundPoleGraph ε R) (0 : P) :=
    contMDiffAt_iff_contDiffAt.mpr (contDiffAt_roundPoleGraph ε hR 0 (by simpa using hR))
  have hNSmooth : ContMDiffAt 𝓘(ℝ, RoundAmbient P) I ∞ N (roundPoleGraph ε R (0 : P)) := by
    rw [hgraph0]
    exact hNd
  have hχSmooth : ContMDiffAt 𝓘(ℝ, P) I ∞ χ 0 := hNSmooth.comp 0 hgraphSmooth
  have hχm : ∀ v w : P, inner ℝ (mfderiv 𝓘(ℝ, P) I χ 0 v)
      (mfderiv 𝓘(ℝ, P) I χ 0 w) = inner ℝ v w := by
    have hj (v : P) : mfderiv 𝓘(ℝ, P) 𝓘(ℝ, RoundAmbient P) (roundPoleGraph ε R) (0 : P) v =
        roundAngularInclusion v := by
      rw [mfderiv_eq_fderiv, hgraph.fderiv]
      rfl
    intro v w
    change inner ℝ (mfderiv 𝓘(ℝ, P) I (N ∘ roundPoleGraph ε R) 0 v)
      (mfderiv 𝓘(ℝ, P) I (N ∘ roundPoleGraph ε R) 0 w) = _
    rw [mfderiv_comp_apply _ hNgraph hgraphd, mfderiv_comp_apply _ hNgraph hgraphd,
      hj, hj, hgraph0]
    rw [show (N ∘ roundPoleGraph ε R) (0 : P) = N (b : RoundAmbient P) from hχN0]
    exact hNm v w
  have hgc : Continuous g := by dsimp [g]; fun_prop
  have ht : Filter.Tendsto Q.symm (𝓝 (Q b)) (𝓝 b) := by
    simpa only [Q.symm_apply_apply] using Q.symm.continuous.tendsto (Q b)
  have hsign0 : ε * inner ℝ roundNorth (Q.symm (Q b) : RoundAmbient P) = R := by
    rw [Q.symm_apply_apply, hb, real_inner_smul_right,
      real_inner_self_eq_norm_sq, roundNorth_norm]
    nlinarith [hε]
  have hsignc : Continuous (fun y : M => ε * inner ℝ roundNorth (Q.symm y : RoundAmbient P)) := by
    fun_prop
  have hpos0 : 0 < ε * inner ℝ roundNorth (Q.symm (Q b) : RoundAmbient P) := by
    rw [hsign0]
    exact hR
  have hsign : ∀ᶠ y in 𝓝 (Q b), 0 < ε * inner ℝ roundNorth (Q.symm y : RoundAmbient P) :=
    hsignc.continuousAt.eventually (lt_mem_nhds hpos0)
  have hrecon : ∀ᶠ y in 𝓝 (Q b), roundPoleGraph ε R (g y) = (Q.symm y : RoundAmbient P) := by
    filter_upwards [hsign] with y hy
    exact roundPoleGraph_reconstruct hε _ (mem_sphere_zero_iff_norm.mp (Q.symm y).property) hy.le
  have hfg : ∀ᶠ y in 𝓝 (χ (0 : P)), χ (g y) = y := by
    rw [hχ0]
    filter_upwards [hrecon, ht.eventually hNeq] with y hy he
    change N (roundPoleGraph ε R (g y)) = y
    rw [hy]
    exact he.trans (Q.apply_symm_apply y)
  obtain ⟨hgSmooth, hgm⟩ := smooth_local_inverse_of_metric_derivative χ g 0 hDim hχSmooth hχm
    hgc.continuousAt (by rw [hχ0]; exact hg0) hfg
  rw [hχ0] at hgSmooth hgm
  have hgd := hgSmooth.mdifferentiableAt (by norm_num)
  have hgraphg : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, RoundAmbient P)
      (roundPoleGraph ε R) (g (Q b)) := by rw [hg0]; exact hgraphd
  have hlocal : (fun y : M => (Q.symm y : RoundAmbient P)) =ᶠ[𝓝 (Q b)]
      (roundPoleGraph ε R ∘ g) := hrecon.mono (fun _ hy => hy.symm)
  have hgraphgSmooth : ContMDiffAt 𝓘(ℝ, P) 𝓘(ℝ, RoundAmbient P) ∞
      (roundPoleGraph ε R) (g (Q b)) := by rw [hg0]; exact hgraphSmooth
  refine ⟨(hgraphgSmooth.comp (Q b) hgSmooth).congr_of_eventuallyEq hlocal, ?_⟩
  intro v w
  have hd (v : TangentSpace I (Q b)) :
      mvfderiv I (fun y : M => (Q.symm y : RoundAmbient P)) (Q b) v =
        roundAngularInclusion (mvfderiv I g (Q b) v) := by
    have hh := hlocal.mfderiv_eq (I := I) (I' := 𝓘(ℝ, RoundAmbient P))
    rw [mfderiv_comp (Q b) hgraphg hgd, hg0, mfderiv_eq_fderiv, hgraph.fderiv] at hh
    convert congrArg (fun D => D v) hh using 1 <;> rfl
  rw [hd, hd, roundAngularInclusion_inner]
  exact hgm v w

end LichnerowiczObata
