/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerSpatialRescaling

@[expose] public section

/-! The genuine Euler time/amplitude scaling. A solution starting from
ε u₀ on [0,1] gives a solution starting from u₀ on [0,ε]. -/

noncomputable section

namespace EulerTimeRescaling

open Set ContinuousLinearMap InnerProductSpace EulerLagrangian

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def coordinates (ε : ℝ) : (ℝ × E) →L[ℝ] (ℝ × E) :=
  ((ε⁻¹ • ContinuousLinearMap.id ℝ ℝ).comp (fst ℝ ℝ E)).prod (snd ℝ ℝ E)

omit [CompleteSpace E] in
@[simp] theorem coordinates_apply (ε : ℝ) (q : ℝ × E) :
    coordinates ε q=(ε⁻¹*q.1,q.2) := rfl

def velocity (ε : ℝ) (u : ℝ × E → E) (q : ℝ × E) : E :=
  ε⁻¹ • u (coordinates ε q)

def pressure (ε : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E) : ℝ :=
  (ε⁻¹)^2*p (coordinates ε q)

omit [CompleteSpace E] in
theorem velocity_hasFDerivAt (ε : ℝ) (u : ℝ × E → E) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q)) :
    HasFDerivAt (velocity ε u)
      (ε⁻¹ • (fderiv ℝ u (coordinates ε q)).comp (coordinates ε)) q :=
  (hu.hasFDerivAt.comp q (coordinates (E := E) ε).hasFDerivAt).const_smul ε⁻¹

theorem pressure_gradient (ε : ℝ) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹*q.1,y)) q.2) :
    gradient (fun y => pressure ε p (q.1,y)) q.2 =
      (ε⁻¹)^2 • gradient (fun y => p (ε⁻¹*q.1,y)) q.2 := by
  have hs := hp.hasFDerivAt.const_smul ((ε⁻¹)^2)
  change HasFDerivAt (fun y => (ε⁻¹)^2 • p (ε⁻¹*q.1,y)) _ q.2 at hs
  apply ext_inner_right ℝ
  intro v
  change inner ℝ (gradient (fun y => (ε⁻¹)^2 • p (ε⁻¹*q.1,y)) q.2) v = _
  rw [inner_gradient_left,real_inner_smul_left,inner_gradient_left,hs.fderiv]
  rfl

theorem momentumResidual_eq (ε : ℝ) (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q))
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹*q.1,y)) q.2) :
    momentumResidual (velocity ε u) (pressure ε p) q =
      (ε⁻¹)^2 • momentumResidual u p (coordinates ε q) := by
  unfold momentumResidual
  rw [(velocity_hasFDerivAt ε u q hu).fderiv,pressure_gradient ε p q hp]
  simp only [smul_apply,comp_apply]
  have hd : coordinates ε ((1 : ℝ),velocity ε u q) =
      ε⁻¹ • (1,u (coordinates ε q)) := by
    simp only [coordinates_apply,velocity,Prod.smul_mk,smul_eq_mul,mul_one]
  rw [hd,map_smul,smul_smul,← pow_two,← smul_add]
  rfl

theorem momentumResidual_zero (ε : ℝ) (u : ℝ × E → E) (p : ℝ × E → ℝ) (q : ℝ × E)
    (hu : DifferentiableAt ℝ u (coordinates ε q))
    (hp : DifferentiableAt ℝ (fun y => p (ε⁻¹*q.1,y)) q.2)
    (he : momentumResidual u p (coordinates ε q)=0) :
    momentumResidual (velocity ε u) (pressure ε p) q=0 := by
  rw [momentumResidual_eq ε u p q hu hp,he,smul_zero]

omit [CompleteSpace E] in
theorem spatial_derivative (ε : ℝ) (u : ℝ × E → E) (t : ℝ) (x : E)
    (hu : DifferentiableAt ℝ (fun y => u (ε⁻¹*t,y)) x) :
    fderiv ℝ (fun y => velocity ε u (t,y)) x =
      ε⁻¹ • fderiv ℝ (fun y => u (ε⁻¹*t,y)) x :=
  (hu.hasFDerivAt.const_smul ε⁻¹).fderiv

def timeMap (ε : ℝ) (hε : 0 < ε) : C(Icc (0 : ℝ) ε,Icc (0 : ℝ) 1) where
  toFun t := ⟨t/ε,div_nonneg t.property.1 hε.le,(div_le_one hε).mpr t.property.2⟩
  continuous_toFun := (continuous_subtype_val.div_const ε).subtype_mk _

theorem timeMap_initial (ε : ℝ) (hε : 0 < ε) :
    timeMap ε hε ⟨0,le_rfl,hε.le⟩=⟨0,le_rfl,by norm_num⟩ := by
  apply Subtype.ext
  exact zero_div ε

theorem scaled_time_interior (ε : ℝ) (hε : 0 < ε) (t : ℝ) (ht : t ∈ Ioo 0 ε) :
    ε⁻¹*t ∈ Ioo (0 : ℝ) 1 := by
  rw [mul_comm,← div_eq_mul_inv]
  exact ⟨div_pos ht.1 hε,(div_lt_one hε).mpr ht.2⟩

end EulerTimeRescaling
