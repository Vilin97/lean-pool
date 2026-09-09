/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPrimaryPressureShear

@[expose] public section

/-! The low-order estimates behind source (20).  The upper quadratic-form
bound uses only the negative part of the angular derivative.  Its cost
therefore retains the narrow-profile factor which is absent from the
absolute Hessian bound. -/

noncomputable section

namespace EulerPacketPhysicalLowBounds

open InnerProductSpace ContinuousLinearMap EulerSmoothLimit EulerPeriodicProfile

abbrev Matrix := Space →L[ℝ] Space

def shearTerm (amp slope : ℝ) (r w : Space) : Matrix :=
  (amp*slope) • rankOne ℝ w r

def pressureTerm (amp slope : ℝ) (M : Matrix) (r w : Space) : Matrix :=
  (-2*amp*⟪r,M w⟫_ℝ*slope/‖r‖^2) • rankOne ℝ r r

theorem profile_deriv_abs (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (θ : ℝ) :
    |deriv (profile δ) θ| ≤ δ⁻¹ := by
  have hi : 1 ≤ δ⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hδ).2 (by simpa only [one_mul] using hδ1)
  exact abs_le.mpr ⟨by linarith only [profile_deriv_lower δ hδ θ,hi],profile_deriv_upper δ hδ θ⟩

theorem flux_abs_le (M : Matrix) (r w : Space) :
    |⟪r,M w⟫_ℝ| ≤ ‖M‖*(‖r‖*‖w‖) := by
  have h := norm_inner_le_norm (𝕜 := ℝ) r (M w)
  calc
    _ ≤ ‖r‖*‖M w‖ := by simpa only [Real.norm_eq_abs] using h
    _ ≤ ‖r‖*(‖M‖*‖w‖) := mul_le_mul_of_nonneg_left (M.le_opNorm w) (norm_nonneg r)
    _ = _ := by ring

theorem quadratic_le_norm (M : Matrix) (z : Space) :
    ⟪M z,z⟫_ℝ ≤ ‖M‖*‖z‖^2 := by
  have h := (le_abs_self ⟪M z,z⟫_ℝ).trans
    (by simpa only [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) (M z) z)
  exact h.trans ((mul_le_mul_of_nonneg_right (M.le_opNorm z) (norm_nonneg z)).trans_eq (by ring))

theorem shearTerm_norm (amp slope : ℝ) (r w : Space) :
    ‖shearTerm amp slope r w‖=|amp| *|slope| *(‖r‖*‖w‖) := by
  simp only [shearTerm,norm_smul,Real.norm_eq_abs,abs_mul,norm_rankOne]
  ring

theorem pressureTerm_norm (amp slope : ℝ) (M : Matrix) (r w : Space) :
    ‖pressureTerm amp slope M r w‖=2*|amp| *|⟪r,M w⟫_ℝ| *|slope| := by
  by_cases hr : r=0
  · simp [pressureTerm,hr]
  have hn : ‖r‖ ≠ 0 := norm_ne_zero_iff.mpr hr
  simp only [pressureTerm,norm_smul,Real.norm_eq_abs,abs_div,abs_mul,abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_pow,abs_norm,norm_rankOne]
  field_simp

theorem shearTerm_norm_le (amp slope δ : ℝ) (r w : Space)
    (hamp : 0 ≤ amp) (hslope : |slope| ≤ δ⁻¹) :
    ‖shearTerm amp slope r w‖ ≤ (amp*(‖r‖*‖w‖))/δ := by
  rw [shearTerm_norm,abs_of_nonneg hamp]
  calc
    _ ≤ amp*δ⁻¹*(‖r‖*‖w‖) := by gcongr
    _ = _ := by ring

theorem pressureTerm_norm_le (amp slope δ : ℝ) (M : Matrix) (r w : Space)
    (hamp : 0 ≤ amp) (hslope : |slope| ≤ δ⁻¹) :
    ‖pressureTerm amp slope M r w‖ ≤ 2*‖M‖*(amp*(‖r‖*‖w‖))/δ := by
  rw [pressureTerm_norm,abs_of_nonneg hamp]
  have hi : 0 ≤ δ⁻¹ := (abs_nonneg slope).trans hslope
  calc
    _ ≤ 2*amp*(‖M‖*(‖r‖*‖w‖))*δ⁻¹ := by gcongr; exact flux_abs_le M r w
    _ = _ := by ring

theorem pressureTerm_quadratic (amp slope : ℝ) (M : Matrix) (r w z : Space) :
    ⟪pressureTerm amp slope M r w z,z⟫_ℝ =
      (-2*amp*⟪r,M w⟫_ℝ*slope)*(⟪r,z⟫_ℝ^2/‖r‖^2) := by
  simp only [pressureTerm,smul_apply,rankOne_apply,real_inner_smul_left]
  ring

theorem normal_projection_quadratic_le (r z : Space) :
    ⟪r,z⟫_ℝ^2/‖r‖^2 ≤ ‖z‖^2 := by
  by_cases hr : r=0
  · simp [hr]
  have hn : 0 < ‖r‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hr)
  have h := norm_inner_le_norm (𝕜 := ℝ) r z
  have hsq := pow_le_pow_left₀ (norm_nonneg ⟪r,z⟫_ℝ) h 2
  rw [Real.norm_eq_abs,sq_abs] at hsq
  exact (div_le_iff₀ hn).2 (by nlinarith only [hsq])

theorem pressureTerm_nonpos (amp slope : ℝ) (M : Matrix) (r w z : Space)
    (hamp : 0 ≤ amp) (hslope : 0 ≤ slope) (hflux : 0 ≤ ⟪r,M w⟫_ℝ) :
    ⟪pressureTerm amp slope M r w z,z⟫_ℝ ≤ 0 := by
  rw [pressureTerm_quadratic]
  exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith [mul_nonneg (mul_nonneg hamp hflux) hslope])
    (div_nonneg (sq_nonneg _) (sq_nonneg _))

theorem pressureTerm_upper_flux (amp slope : ℝ) (M : Matrix) (r w z : Space)
    (hamp : 0 ≤ amp) (hslope : -1 ≤ slope) (hflux : 0 ≤ ⟪r,M w⟫_ℝ) :
    ⟪pressureTerm amp slope M r w z,z⟫_ℝ ≤ 2*amp*⟪r,M w⟫_ℝ*‖z‖^2 := by
  have hc : 0 ≤ 2*amp*⟪r,M w⟫_ℝ := by positivity
  have hs : -2*amp*⟪r,M w⟫_ℝ*slope ≤ 2*amp*⟪r,M w⟫_ℝ := by
    nlinarith only [mul_le_mul_of_nonneg_left hslope hc]
  rw [pressureTerm_quadratic]
  exact (mul_le_mul_of_nonneg_right hs (div_nonneg (sq_nonneg _) (sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left (normal_projection_quadratic_le r z) hc)

theorem pressureTerm_upper (amp slope : ℝ) (M : Matrix) (r w z : Space)
    (hamp : 0 ≤ amp) (hslope : -1 ≤ slope) (hflux : 0 ≤ ⟪r,M w⟫_ℝ) :
    ⟪pressureTerm amp slope M r w z,z⟫_ℝ ≤
      2*‖M‖*(amp*(‖r‖*‖w‖))*‖z‖^2 := by
  apply (pressureTerm_upper_flux amp slope M r w z hamp hslope hflux).trans
  have hf := (le_abs_self ⟪r,M w⟫_ℝ).trans (flux_abs_le M r w)
  calc
    _ ≤ 2*amp*(‖M‖*(‖r‖*‖w‖))*‖z‖^2 := by gcongr
    _ = _ := by ring

theorem norm_of_remainder (A B Q : Matrix) (e : ℝ) (he : ‖A-B-Q‖ ≤ e) :
    ‖A‖ ≤ ‖B‖+‖Q‖+e := by
  have h : A=B+Q+(A-B-Q) := by module
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _)) he)

theorem quadratic_of_remainder (A B Q : Matrix) (e K C : ℝ)
    (he : ‖A-B-Q‖ ≤ e) (hB : ∀ z, ⟪B z,z⟫_ℝ ≤ K*‖z‖^2)
    (hQ : ∀ z, ⟪Q z,z⟫_ℝ ≤ C*‖z‖^2) (z : Space) :
    ⟪A z,z⟫_ℝ ≤ (K+C+e)*‖z‖^2 := by
  have hE := (quadratic_le_norm (A-B-Q) z).trans
    (mul_le_mul_of_nonneg_right he (sq_nonneg _))
  have h : A=B+Q+(A-B-Q) := by module
  calc
    _ = ⟪B z,z⟫_ℝ+⟪Q z,z⟫_ℝ+⟪(A-B-Q) z,z⟫_ℝ := by
      conv_lhs => rw [h]
      simp only [add_apply,inner_add_left]
    _ ≤ K*‖z‖^2+C*‖z‖^2+e*‖z‖^2 := add_le_add (add_le_add (hB z) (hQ z)) hE
    _ = _ := by ring

/-- On a good interval the upper pressure cost uses amp*size, whereas
absolute velocity and Hessian costs use amp*size/delta. -/
theorem good_step_bounds (A B H J M : Matrix) (r w : Space)
    (amp δ θ ev ep V P K size : ℝ)
    (hamp : 0 ≤ amp) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : amp*(‖r‖*‖w‖) ≤ δ*size) (hM : ‖M‖ ≤ V)
    (hB : ‖B‖ ≤ P) (hJ : ‖J‖ ≤ K)
    (hev : ‖A-B-shearTerm amp (deriv (profile δ) θ) r w‖ ≤ ev)
    (hep : ‖H-J-pressureTerm amp (deriv (profile δ) θ) M r w‖ ≤ ep)
    (hflux : 0 ≤ ⟪r,M w⟫_ℝ) (Kupper : ℝ)
    (hupper : ∀ z, ⟪J z,z⟫_ℝ ≤ Kupper*‖z‖^2) :
    ‖A‖ ≤ P+size+ev ∧ ‖H‖ ≤ K+2*V*size+ep ∧
      ∀ z, ⟪H z,z⟫_ℝ ≤ (Kupper+2*V*δ*size+ep)*‖z‖^2 := by
  have hslope := profile_deriv_abs δ hδ hδ1 θ
  have hs : 0 ≤ size := by nlinarith only [hδ,hsize,mul_nonneg hamp (mul_nonneg (norm_nonneg r)
    (norm_nonneg w))]
  have hV : 0 ≤ V := (norm_nonneg _).trans hM
  have hv : ‖shearTerm amp (deriv (profile δ) θ) r w‖ ≤ size :=
    (shearTerm_norm_le amp _ δ r w hamp hslope).trans ((div_le_iff₀ hδ).2 (by nlinarith only
      [hsize]))
  have hp : ‖pressureTerm amp (deriv (profile δ) θ) M r w‖ ≤ 2*V*size :=
    (pressureTerm_norm_le amp _ δ M r w hamp hslope).trans
    ((div_le_iff₀ hδ).2 (by nlinarith only [mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤
      2*‖M‖),
      mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2*δ*size)]))
  refine ⟨(norm_of_remainder A B _ ev hev).trans (by linarith only [hB,hv]),
    (norm_of_remainder H J _ ep hep).trans (by linarith only [hJ,hp]),?_⟩
  apply quadratic_of_remainder H J _ ep Kupper (2*V*δ*size) hep hupper
  intro z
  have hh := pressureTerm_upper amp _ M r w z hamp (profile_deriv_lower δ hδ θ) hflux
  have hcost : 2*‖M‖*(amp*(‖r‖*‖w‖)) ≤ 2*V*δ*size := by
    nlinarith only [mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 2*‖M‖),
      mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2*δ*size)]
  exact hh.trans (mul_le_mul_of_nonneg_right hcost (sq_nonneg _))

/-- Without a sign assertion the same absolute estimate controls the
positive Hessian cost. This is used on history and early forward times. -/
theorem absolute_step_bounds (A B H J M : Matrix) (r w : Space)
    (amp δ θ ev ep V P K size : ℝ)
    (hamp : 0 ≤ amp) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hsize : amp*(‖r‖*‖w‖) ≤ δ*size) (hM : ‖M‖ ≤ V)
    (hB : ‖B‖ ≤ P) (hJ : ‖J‖ ≤ K)
    (hev : ‖A-B-shearTerm amp (deriv (profile δ) θ) r w‖ ≤ ev)
    (hep : ‖H-J-pressureTerm amp (deriv (profile δ) θ) M r w‖ ≤ ep)
    (Kupper : ℝ) (hupper : ∀ z, ⟪J z,z⟫_ℝ ≤ Kupper*‖z‖^2) :
    ‖A‖ ≤ P+size+ev ∧ ‖H‖ ≤ K+2*V*size+ep ∧
      ∀ z, ⟪H z,z⟫_ℝ ≤ (Kupper+2*V*size+ep)*‖z‖^2 := by
  have hslope := profile_deriv_abs δ hδ hδ1 θ
  have hs : 0 ≤ size := by
    nlinarith only [hδ,hsize,mul_nonneg hamp (mul_nonneg (norm_nonneg r) (norm_nonneg w))]
  have hV : 0 ≤ V := (norm_nonneg _).trans hM
  have hv : ‖shearTerm amp (deriv (profile δ) θ) r w‖ ≤ size :=
    (shearTerm_norm_le amp _ δ r w hamp hslope).trans
      ((div_le_iff₀ hδ).2 (by nlinarith only [hsize]))
  have hp : ‖pressureTerm amp (deriv (profile δ) θ) M r w‖ ≤ 2*V*size :=
    (pressureTerm_norm_le amp _ δ M r w hamp hslope).trans
      ((div_le_iff₀ hδ).2 (by nlinarith only [
        mul_le_mul_of_nonneg_left hsize (by positivity : 0 ≤ 2*‖M‖),
        mul_le_mul_of_nonneg_right hM (by positivity : 0 ≤ 2*δ*size)]))
  refine ⟨(norm_of_remainder A B _ ev hev).trans (by linarith only [hB,hv]),
    (norm_of_remainder H J _ ep hep).trans (by linarith only [hJ,hp]),?_⟩
  apply quadratic_of_remainder H J _ ep Kupper (2*V*size) hep hupper
  intro z
  exact (quadratic_le_norm _ z).trans (mul_le_mul_of_nonneg_right hp (sq_nonneg _))

end EulerPacketPhysicalLowBounds
