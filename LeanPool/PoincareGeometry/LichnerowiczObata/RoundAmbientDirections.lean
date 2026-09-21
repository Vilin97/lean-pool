/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarHomeomorph
public import LeanPool.PoincareGeometry.LichnerowiczObata.RoundPolarJointMetric

/-! # A concrete round ambient space for intrinsic angular directions -/

@[expose] public noncomputable section
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

abbrev RoundAmbient (P : Type*) := WithLp 2 (P × ℝ)

def roundNorth : RoundAmbient P := WithLp.toLp 2 (0, 1)

def roundAngularInclusion : P →L[ℝ] RoundAmbient P :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ P ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ P ℝ)

@[simp] theorem roundAngularInclusion_apply (u : P) :
    roundAngularInclusion u = WithLp.toLp 2 (u, 0) := rfl

@[simp] theorem roundAngularInclusion_inner (u v : P) :
    inner ℝ (roundAngularInclusion u) (roundAngularInclusion v) = inner ℝ u v := by
  simp [roundAngularInclusion_apply, WithLp.prod_inner_apply]

@[simp] theorem roundAngularInclusion_norm (u : P) : ‖roundAngularInclusion u‖ = ‖u‖ := by
  simp [roundAngularInclusion_apply, WithLp.norm_toLp_fst]

omit [InnerProductSpace ℝ P] in
@[simp] theorem roundNorth_norm : ‖(roundNorth : RoundAmbient P)‖ = 1 := by
  simp [roundNorth, WithLp.norm_toLp_snd]

@[simp] theorem roundNorth_inner (x : RoundAmbient P) :
    inner ℝ roundNorth x = (WithLp.ofLp x).2 := by
  simp [roundNorth, WithLp.prod_inner_apply]

@[simp] theorem roundNorth_inner_angular (u : P) :
    inner ℝ roundNorth (roundAngularInclusion u) = 0 := by
  rw [roundNorth_inner]
  rfl

/-- Unit intrinsic vectors are precisely the unit directions orthogonal to
the north pole in the Euclidean product ambient space. -/
def roundAngularHomeomorph : Metric.sphere (0 : P) 1 ≃ₜ
    RoundPolarDirections (roundNorth : RoundAmbient P) where
  toFun u := ⟨roundAngularInclusion u, by
    exact ⟨(roundAngularInclusion_norm (u : P)).trans (mem_sphere_zero_iff_norm.mp u.property),
      roundNorth_inner_angular (u : P)⟩⟩
  invFun x := ⟨(WithLp.ofLp (x : RoundAmbient P)).1, by
    have hx : (WithLp.ofLp (x : RoundAmbient P)).2 = 0 := by
      exact (roundNorth_inner (x : RoundAmbient P)).symm.trans x.property.2
    have he : roundAngularInclusion (WithLp.ofLp (x : RoundAmbient P)).1 = x := by
      apply (WithLp.equiv 2 (P × ℝ)).injective
      exact Prod.ext rfl hx.symm
    rw [mem_sphere_zero_iff_norm, ← roundAngularInclusion_norm, he]
    exact x.property.1⟩
  left_inv u := by apply Subtype.ext; rfl
  right_inv x := by
    apply Subtype.ext
    apply (WithLp.equiv 2 (P × ℝ)).injective
    change ((WithLp.ofLp (x : RoundAmbient P)).1, (0 : ℝ)) = WithLp.ofLp (x : RoundAmbient P)
    refine Prod.ext ?_ ?_
    · rfl
    have hx := x.property.2
    exact ((roundNorth_inner (x : RoundAmbient P)).symm.trans hx).symm
  continuous_toFun := by
    exact (roundAngularInclusion.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((WithLp.fstL 2 ℝ P ℝ).continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem roundAngularHomeomorph_apply (u : Metric.sphere (0 : P) 1) :
    (roundAngularHomeomorph u : RoundAmbient P) = roundAngularInclusion (u : P) := rfl

/-- The punctured round sphere in the concrete ambient space has precisely
the intrinsic unit-sphere angular parameter used by the Obata construction. -/
def intrinsicRoundPolarHomeomorph {R : ℝ} (hR : 0 < R) :
    Metric.sphere (0 : P) 1 × Set.Ioo (0 : ℝ) (Real.pi * R) ≃ₜ
      RoundPuncturedSphere R (roundNorth : RoundAmbient P) :=
  (roundAngularHomeomorph.prodCongr (Homeomorph.refl _)).trans
    (roundPolarHomeomorph hR roundNorth roundNorth_norm)

@[simp] theorem intrinsicRoundPolarHomeomorph_apply {R : ℝ} (hR : 0 < R)
    (q : Metric.sphere (0 : P) 1 × Set.Ioo (0 : ℝ) (Real.pi * R)) :
    (((intrinsicRoundPolarHomeomorph hR q).1 : Metric.sphere (0 : RoundAmbient P) R) :
    RoundAmbient P) = roundPolarCurve R roundNorth (roundAngularInclusion (q.1 : P)) q.2 := rfl

/-- The actual round polar map in intrinsic angular coordinates has the
same full derivative metric as the constructed unit-angular Obata product. -/
theorem intrinsicRoundPolar_metric {K : ℝ} (hK : 0 < K)
    (u w v : P) (hu : ‖u‖ = 1) (hw : inner ℝ u w = 0) (hv : inner ℝ u v = 0)
    (r s t : ℝ) :
    let Ψ := fun q : P × ℝ => roundPolarCurve (1 / Real.sqrt K)
      roundNorth (roundAngularInclusion q.1) q.2
    inner ℝ (fderiv ℝ Ψ (u, r) (w, s)) (fderiv ℝ Ψ (u, r) (v, t)) =
      (Real.sin (Real.sqrt K * r) ^ 2 / K) * inner ℝ w v + s * t := by
  let Γ := fun q : RoundAmbient P × ℝ =>
    roundPolarCurve (1 / Real.sqrt K) roundNorth q.1 q.2
  let A : P × ℝ →L[ℝ] RoundAmbient P × ℝ :=
    roundAngularInclusion.prodMap (ContinuousLinearMap.id ℝ ℝ)
  have hd : DifferentiableAt ℝ Γ (A (u, r)) := by
    dsimp [Γ, roundPolarCurve]
    fun_prop
  change inner ℝ (fderiv ℝ (Γ ∘ A) (u, r) (w, s))
    (fderiv ℝ (Γ ∘ A) (u, r) (v, t)) = _
  rw [fderiv_comp (u, r) hd A.differentiableAt, A.fderiv]
  have hh := roundPolarCurve_joint_metric_curvature hK r
    (roundNorth : RoundAmbient P) (roundAngularInclusion u)
    (roundAngularInclusion w) (roundAngularInclusion v)
    roundNorth_norm ((roundAngularInclusion_norm u).trans hu)
    (roundNorth_inner_angular u) (roundNorth_inner_angular w)
    ((roundAngularInclusion_inner u w).trans hw) (roundNorth_inner_angular v)
    ((roundAngularInclusion_inner u v).trans hv) s t
  simpa only [A, Γ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_prodMap',
    Prod.map_apply, ContinuousLinearMap.id_apply, roundAngularInclusion_inner] using hh

/-- Curvature-normalized polar coordinates use the identical radial interval
as the Obata construction. -/
def curvatureRoundPolarHomeomorph {K : ℝ} (hK : 0 < K) :
    Metric.sphere (0 : P) 1 × Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt K) ≃ₜ
      RoundPuncturedSphere (1 / Real.sqrt K) (roundNorth : RoundAmbient P) :=
  ((Homeomorph.refl _).prodCongr (Homeomorph.setCongr
    (show Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt K) =
      Set.Ioo (0 : ℝ) (Real.pi * (1 / Real.sqrt K)) by
        simp [div_eq_mul_inv]))).trans
    (intrinsicRoundPolarHomeomorph (one_div_pos.mpr (Real.sqrt_pos.mpr hK)))

@[simp] theorem curvatureRoundPolarHomeomorph_apply {K : ℝ} (hK : 0 < K)
    (q : Metric.sphere (0 : P) 1 × Set.Ioo (0 : ℝ) (Real.pi / Real.sqrt K)) :
    (((curvatureRoundPolarHomeomorph hK q).1 :
      Metric.sphere (0 : RoundAmbient P) (1 / Real.sqrt K)) : RoundAmbient P) =
      roundPolarCurve (1 / Real.sqrt K) roundNorth (roundAngularInclusion (q.1 : P)) q.2 := rfl

end LichnerowiczObata
