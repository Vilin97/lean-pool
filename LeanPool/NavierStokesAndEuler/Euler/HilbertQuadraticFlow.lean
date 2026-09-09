/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BoundedLipschitzFlow
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! A bounded quadratic vector field whose radial energy vanishes has
a genuine global flow on a real Hilbert space. Radial normalization
first gives a globally Lipschitz equation; its conserved norm then
removes the normalization by a constant rescaling of time. -/

noncomputable section

namespace EulerHilbertQuadraticFlow

open Filter ContinuousLinearMap InnerProductSpace
open scoped Topology

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radial (x : E) : E := (1+‖x‖)⁻¹ • x

theorem radial_norm (x : E) : ‖radial x‖ ≤ 1 := by
  rw [radial,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (by positivity)),← div_eq_inv_mul]
  exact (div_le_one (by positivity)).mpr (by linarith [norm_nonneg x])

theorem radial_sub_norm (x y : E) : ‖radial x-radial y‖ ≤ 2*‖x-y‖ := by
  have hx : 0 < 1+‖x‖ := by positivity
  have hy : 0 < 1+‖y‖ := by positivity
  have ha : 0 ≤ (1+‖x‖)⁻¹ := (inv_pos.mpr hx).le
  have ha1 : (1+‖x‖)⁻¹ ≤ 1 := (inv_le_one₀ hx).mpr (by linarith [norm_nonneg x])
  have he : (1+‖x‖)⁻¹-(1+‖y‖)⁻¹ =
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖))*(1+‖y‖)⁻¹ := by
    field_simp
    ring
  have hv : radial x-radial y = (1+‖x‖)⁻¹ • (x-y)+
      ((1+‖x‖)⁻¹*(‖y‖-‖x‖)) • radial y := by
    calc
      _ = (1+‖x‖)⁻¹ • (x-y)+((1+‖x‖)⁻¹-(1+‖y‖)⁻¹) • y := by
        dsimp [radial]
        module
      _ = _ := by rw [he,radial,smul_smul]
  have hd : |‖y‖-‖x‖| ≤ ‖x-y‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le y x
  rw [hv]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,norm_mul,
    Real.norm_of_nonneg ha,Real.norm_eq_abs]
  have h1 : (1+‖x‖)⁻¹*‖x-y‖ ≤ ‖x-y‖ :=
    mul_le_of_le_one_left (norm_nonneg _) ha1
  have h2 : ((1+‖x‖)⁻¹*|‖y‖-‖x‖|)*‖radial y‖ ≤ ‖x-y‖ := by
    calc
      _ ≤ ((1+‖x‖)⁻¹*‖x-y‖)*1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hd ha) (radial_norm y)
          (norm_nonneg _) (mul_nonneg ha (norm_nonneg _))
      _ ≤ _ := by simpa only [mul_one] using h1
  linarith

theorem radial_lipschitz : LipschitzWith 2 (radial : E → E) :=
  lipschitzWith_iff_norm_sub_le.mpr radial_sub_norm

def normalized (B : E →L[ℝ] E →L[ℝ] E) (x : E) : E := B (radial x) (radial x)

theorem bilinear_bound (B : E →L[ℝ] E →L[ℝ] E) (x y : E) :
    ‖B x y‖ ≤ ‖B‖*‖x‖*‖y‖ :=
  ((B x).le_opNorm y).trans (mul_le_mul_of_nonneg_right (B.le_opNorm x) (norm_nonneg y))

theorem normalized_lipschitz (B : E →L[ℝ] E →L[ℝ] E) :
    LipschitzWith (4*‖B‖₊) (normalized B) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro x y
  have he : normalized B x-normalized B y =
      B (radial x-radial y) (radial x)+B (radial y) (radial x-radial y) := by
    simp only [normalized,map_sub,sub_apply]
    abel
  rw [he]
  apply (norm_add_le _ _).trans
  have h1 : ‖B (radial x-radial y) (radial x)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_sub_norm x y) (norm_nonneg B))
      (radial_norm x) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have h2 : ‖B (radial y) (radial x-radial y)‖ ≤ ‖B‖*(2*‖x-y‖) := by
    apply (bilinear_bound B _ _).trans
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (radial_norm y) (norm_nonneg B))
      (radial_sub_norm x y) (norm_nonneg _) (by positivity)).trans_eq (by ring)
  exact (add_le_add h1 h2).trans_eq (by simp only [NNReal.coe_mul,NNReal.coe_ofNat,coe_nnnorm];
    ring)

theorem normalized_eq (B : E →L[ℝ] E →L[ℝ] E) (x : E) :
    normalized B x=((1+‖x‖)⁻¹)^2 • B x x := by
  simp only [normalized,radial,map_smul,smul_apply,smul_smul,pow_two]

end Normed

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem exists_global_quadratic (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ x, ⟪x,B x x⟫_ℝ=0) (x : E) :
    ∃ u : ℝ → E, u 0=x ∧ (∀ t, HasDerivAt u (B (u t) (u t)) t) ∧
      ∀ t, ‖u t‖=‖x‖ := by
  have hc : Continuous (Function.uncurry (fun _t : ℝ => normalized B)) :=
    (normalized_lipschitz B).continuous.comp continuous_snd
  obtain ⟨v,hv0,hv⟩ := EulerPacketExistence.exists_global_solution hc
    (fun _t => normalized_lipschitz B) x
  have hd (t : ℝ) : HasDerivAt (fun s => ‖v s‖^2) 0 t := by
    have h := (hv t).norm_sq
    simpa only [normalized_eq,real_inner_smul_right,hB,mul_zero] using h
  have hn (t : ℝ) : ‖v t‖=‖x‖ := by
    have he := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
      (fun s => (hd s).deriv) t 0
    rw [hv0] at he
    nlinarith [norm_nonneg (v t),norm_nonneg x]
  let c := (1+‖x‖)^2
  refine ⟨fun t => v (c*t),by simpa only [mul_zero] using hv0,?_,fun t => hn (c*t)⟩
  intro t
  have hi : HasDerivAt (fun r : ℝ => c*r) c t := by
    simpa only [id_eq,mul_one] using (hasDerivAt_id t).const_mul c
  have h := (hv (c*t)).scomp t hi
  have he : c • normalized B (v (c*t))=B (v (c*t)) (v (c*t)) := by
    rw [normalized_eq,hn,smul_smul]
    have hp : c*((1+‖x‖)⁻¹)^2=1 := by
      dsimp [c]
      field_simp
    rw [hp,one_smul]
  simpa only [he,Function.comp_def] using h

end Hilbert
end EulerHilbertQuadraticFlow
