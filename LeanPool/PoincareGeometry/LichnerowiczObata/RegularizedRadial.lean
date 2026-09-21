/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ScalarDistanceBound
public import LeanPool.PoincareGeometry.LichnerowiczObata.EikonalConnection

/-! # Smooth nonexpanding approximations to the radial coordinate

Increasing the amplitude in the arccosine formula removes both endpoint
singularities while preserving the gradient bound needed for intrinsic distance.
-/

@[expose] public noncomputable section
open Bundle Set AlmostSchur Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace LichnerowiczObata

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
/-- An enlarged amplitude makes the radial gradient nonexpanding everywhere. -/
theorem norm_gradient_obataRadial_le_one {K a b : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hab : a < b)
    {f : M → ℝ} {x : M} (hf : MDifferentiableAt I 𝓘(ℝ, ℝ) f x)
    (hx : -a ≤ f x ∧ f x ≤ a)
    (hn : ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2)) :
    ‖gradient (I := I) (obataRadial K b f) x‖ ≤ 1 := by
  have hb : 0 < b := ha.trans hab
  have hm : -1 < f x / b := (lt_div_iff₀ hb).2 (by nlinarith [hx.1])
  have hp : f x / b < 1 := (div_lt_iff₀ hb).2 (by nlinarith [hx.2])
  have hsq : 0 < 1 - (f x / b) ^ 2 := by nlinarith
  have hden : 0 < b ^ 2 - f x ^ 2 := by nlinarith [hx.1, hx.2]
  have he : ‖gradient (I := I) (obataRadial K b f) x‖ ^ 2 =
      (a ^ 2 - f x ^ 2) / (b ^ 2 - f x ^ 2) := by
    rw [gradient_obataRadial hf (ne_of_gt hm) (ne_of_lt hp), norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs, hn]
    simp only [div_pow, mul_pow, neg_sq, one_pow]
    rw [Real.sq_sqrt (by simpa only [div_pow] using hsq.le), Real.sq_sqrt hK.le]
    field_simp [hb.ne', hK.ne', hden.ne']
  have hle : (a ^ 2 - f x ^ 2) / (b ^ 2 - f x ^ 2) ≤ 1 :=
    (div_le_one hden).2 (by nlinarith)
  nlinarith [norm_nonneg (gradient (I := I) (obataRadial K b f) x)]

/-- The enlarged-amplitude radial function contracts intrinsic distances. -/
theorem edist_regularized_obataRadial_le {K a b : ℝ}
    (hK : 0 < K) (ha : 0 < a) (hab : a < b)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2))
    (x y : M) : edist (obataRadial K b f x) (obataRadial K b f y) ≤ riemannianEDist I x y := by
  apply edist_le_riemannianEDist_of_gradient_bound
  · intro z
    have hbp : 0 < b := ha.trans hab
    have hm : -1 < f z / b := (lt_div_iff₀ hbp).2 (by nlinarith [(hb z).1])
    have hp : f z / b < 1 := (div_lt_iff₀ hbp).2 (by nlinarith [(hb z).2])
    have hc : ContDiffAt ℝ 1 (fun t : ℝ => Real.arccos (t / b) / Real.sqrt K) (f z) :=
      ((Real.contDiffAt_arccos hm.ne' hp.ne).comp (f z) (contDiffAt_id.div_const b)).div_const _
    exact hc.comp_contMDiffAt (hf z)
  · intro z
    exact norm_gradient_obataRadial_le_one hK ha hab
      (hf.mdifferentiable (by norm_num) z) (hb z) (hn z)

/-- The radial coordinate is globally nonexpanding, including at the singular
levels, by taking the limit of the smooth enlarged-amplitude coordinates. -/
theorem edist_obataRadial_le {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) 1 f)
    (hb : ∀ x, -a ≤ f x ∧ f x ≤ a)
    (hn : ∀ x, ‖gradient (I := I) f x‖ ^ 2 = K * (a ^ 2 - f x ^ 2))
    (x y : M) : edist (obataRadial K a f x) (obataRadial K a f y) ≤ riemannianEDist I x y := by
  have hc (z : M) : ContinuousAt (fun b : ℝ => obataRadial K b f z) a :=
    (Real.continuous_arccos.continuousAt.comp
      (continuousAt_const.div continuousAt_id ha.ne')).div_const _
  apply le_of_tendsto (f := fun b : ℝ => edist (obataRadial K b f x) (obataRadial K b f y))
    (x := 𝓝[>] a) (((hc x).edist (hc y)).mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with b hb'
  exact edist_regularized_obataRadial_le hK ha hb' hf hb hn x y

end LichnerowiczObata
