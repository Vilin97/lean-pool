/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The actual slot phase and its material defect

This module uses the phase in equation (26), with independent slot coordinates
`((R,(Z,T)),(θ,v))`. The base frequencies `F,G` depend on the slow coordinates
`(R,Z,T)`. All derivatives of these functions below are actual Fréchet derivatives.
The primary material operator uses the manuscript's backward-time convention
`∂v - ε ∂T` from equation (25).
-/

noncomputable section

namespace NavierStokes.PhaseCalculus

open scoped ContDiff

abbrev Slow := ℝ × (ℝ × ℝ)
abbrev Slot := Slow × (ℝ × ℝ)
abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def eR : Slot := ((1, (0, 0)), (0, 0))
def eZ : Slot := ((0, (1, 0)), (0, 0))
def eT : Slot := ((0, (0, 1)), (0, 0))
def eTheta : Slot := ((0, (0, 0)), (1, 0))
def eV : Slot := ((0, (0, 0)), (0, 1))

def slowR (F : Slow → ℝ) (s : Slow) : ℝ := fderiv ℝ F s (1, (0, 0))
def slowZ (F : Slow → ℝ) (s : Slow) : ℝ := fderiv ℝ F s (0, (1, 0))
def slowT (F : Slow → ℝ) (s : Slow) : ℝ := fderiv ℝ F s (0, (0, 1))

/-- Equation (26). The axial term `(pz/ε)*Z` equals `pz*Z/ε`. -/
def phase (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot) : ℝ :=
  p * q.2.1 + (pz / ε) * q.1.2.1 + x0 * q.1.1 -
    q.2.2 * (p * F q.1 + pz * G q.1)

/-- The full differential of the phase, with no abstract derivative variables. -/
theorem fderiv_phase_apply (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q w : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q w =
      p * w.2.1 + (pz / ε) * w.1.2.1 + x0 * w.1.1 -
        (w.2.2 * (p * F q.1 + pz * G q.1) +
          q.2.2 * (p * fderiv ℝ F q.1 w.1 + pz * fderiv ℝ G q.1 w.1)) := by
  have hi := hasFDerivAt_id (𝕜 := ℝ) q
  have hFl := hF.hasFDerivAt.comp q hi.fst
  have hGl := hG.hasFDerivAt.comp q hi.fst
  have hd := (((hi.snd.fst.const_mul p).fun_add
    (hi.fst.snd.fst.const_mul (pz / ε))).fun_add (hi.fst.fst.const_mul x0)).fun_sub
      (hi.snd.snd.fun_mul ((hFl.const_mul p).fun_add (hGl.const_mul pz)))
  dsimp only [id_eq, Function.comp_apply] at hd
  unfold phase
  rw [hd.fderiv]
  simp only [_root_.sub_apply, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul]
  dsimp
  ring

theorem phase_dR (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q eR =
      x0 - q.2.2 * (p * slowR F q.1 + pz * slowR G q.1) := by
  simpa [eR, slowR] using fderiv_phase_apply ε p pz x0 F G q eR hF hG

theorem phase_dTheta (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q eTheta = p := by
  have hzeroF : fderiv ℝ F q.1 (0, 0, 0) = 0 := map_zero _
  have hzeroG : fderiv ℝ G q.1 (0, 0, 0) = 0 := map_zero _
  simpa [eTheta, hzeroF, hzeroG] using fderiv_phase_apply ε p pz x0 F G q eTheta hF hG

theorem phase_dZ (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q eZ =
      pz / ε - q.2.2 * (p * slowZ F q.1 + pz * slowZ G q.1) := by
  simpa [eZ, slowZ] using fderiv_phase_apply ε p pz x0 F G q eZ hF hG

theorem phase_dT (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q eT =
      -q.2.2 * (p * slowT F q.1 + pz * slowT G q.1) := by
  simpa [eT, slowT] using fderiv_phase_apply ε p pz x0 F G q eT hF hG

theorem phase_dV (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    fderiv ℝ (phase ε p pz x0 F G) q eV = -(p * F q.1 + pz * G q.1) := by
  have hzeroF : fderiv ℝ F q.1 (0, 0, 0) = 0 := map_zero _
  have hzeroG : fderiv ℝ G q.1 (0, 0, 0) = 0 := map_zero _
  simpa [eV, hzeroF, hzeroG] using fderiv_phase_apply ε p pz x0 F G q eV hF hG

/-- The cylindrical chart gradient `(∂R Φ, R⁻¹∂θ Φ, ε∂Z Φ)`. -/
def phaseNormal (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot) : Vec3 :=
  !₂[fderiv ℝ (phase ε p pz x0 F G) q eR,
    fderiv ℝ (phase ε p pz x0 F G) q eTheta / q.1.1,
    ε * fderiv ℝ (phase ε p pz x0 F G) q eZ]

/-- The exact normal vector in equation (26), derived from the actual phase. -/
theorem phaseNormal_formula (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hε : ε ≠ 0) (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    phaseNormal ε p pz x0 F G q =
      !₂[x0 - q.2.2 * (p * slowR F q.1 + pz * slowR G q.1),
        p / q.1.1,
        pz - ε * q.2.2 * (p * slowZ F q.1 + pz * slowZ G q.1)] := by
  ext i
  fin_cases i
  · simp [phaseNormal, phase_dR ε p pz x0 F G q hF hG]
  · simp [phaseNormal, phase_dTheta ε p pz x0 F G q hF hG]
  · simp [phaseNormal, phase_dZ ε p pz x0 F G q hF hG]
    field_simp

/-- Joint regularity in every slot coordinate, at any differentiability order. -/
theorem contDiff_phase {n : WithTop ℕ∞} (ε p pz x0 : ℝ) (F G : Slow → ℝ)
    (hF : ContDiff ℝ n F) (hG : ContDiff ℝ n G) :
    ContDiff ℝ n (phase ε p pz x0 F G) := by
  unfold phase
  exact (((contDiff_const.mul contDiff_snd.fst).add
    (contDiff_const.mul contDiff_fst.snd.fst)).add
      (contDiff_const.mul contDiff_fst.fst)).sub
        (contDiff_snd.snd.mul
          ((contDiff_const.mul (hF.comp contDiff_fst)).add
            (contDiff_const.mul (hG.comp contDiff_fst))))

/-- The chart angular velocity is `V = R F`. -/
def baseV (F : Slow → ℝ) (s : Slow) : ℝ := s.1 * F s

/-- `σ=-1` is the backward slow-time convention of (25); `σ=1` describes
the forward slow-time convention. The differential operators are real ones. -/
def signedMaterialOp (σ ε : ℝ) (b F G : Slow → ℝ) (f : Slot → ℝ) (q : Slot) : ℝ :=
  fderiv ℝ f q eV + σ * ε * fderiv ℝ f q eT +
    b q.1 * fderiv ℝ f q eR + (baseV F q.1 / q.1.1) * fderiv ℝ f q eTheta +
      ε * G q.1 * fderiv ℝ f q eZ

def backwardMaterialOp (ε : ℝ) (b F G : Slow → ℝ) (f : Slot → ℝ) (q : Slot) : ℝ :=
  signedMaterialOp (-1) ε b F G f q

/-- Exact cancellation of the fast-time and leading angular/axial terms. -/
theorem signedMaterialOp_phase (σ ε p pz x0 : ℝ) (b F G : Slow → ℝ) (q : Slot)
    (hε : ε ≠ 0) (hR : 0 < q.1.1)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    signedMaterialOp σ ε b F G (phase ε p pz x0 F G) q =
      b q.1 * x0 - q.2.2 *
        (b q.1 * (p * slowR F q.1 + pz * slowR G q.1) +
          σ * ε * (p * slowT F q.1 + pz * slowT G q.1) +
          ε * G q.1 * (p * slowZ F q.1 + pz * slowZ G q.1)) := by
  unfold signedMaterialOp
  rw [phase_dV ε p pz x0 F G q hF hG, phase_dT ε p pz x0 F G q hF hG,
    phase_dR ε p pz x0 F G q hF hG, phase_dTheta ε p pz x0 F G q hF hG,
    phase_dZ ε p pz x0 F G q hF hG]
  unfold baseV
  field_simp [hε, ne_of_gt hR] ; ring

/-- The manuscript convention `t* = ∂v - ε∂T` gives the MINUS sign
inside the slow-time part of the bracket (equivalently a positive term
`+ ε v (p F_T + pz G_T)` after expansion). -/
theorem backwardMaterialOp_phase (ε p pz x0 : ℝ) (b F G : Slow → ℝ) (q : Slot)
    (hε : ε ≠ 0) (hR : 0 < q.1.1)
    (hF : DifferentiableAt ℝ F q.1) (hG : DifferentiableAt ℝ G q.1) :
    backwardMaterialOp ε b F G (phase ε p pz x0 F G) q =
      b q.1 * x0 - q.2.2 *
        (b q.1 * (p * slowR F q.1 + pz * slowR G q.1) -
          ε * (p * slowT F q.1 + pz * slowT G q.1) +
          ε * G q.1 * (p * slowZ F q.1 + pz * slowZ G q.1)) := by
  unfold backwardMaterialOp
  rw [signedMaterialOp_phase (-1) ε p pz x0 b F G q hε hR hF hG]
  ring

def angularShift (h : ℝ) (q : Slot) : Slot := (q.1, (q.2.1 + h, q.2.2))

theorem phase_angularShift (ε p pz x0 h : ℝ) (F G : Slow → ℝ) (q : Slot) :
    phase ε p pz x0 F G (angularShift h q) = phase ε p pz x0 F G q + p * h := by
  unfold phase angularShift
  dsimp
  ring

/-- The actual complex carrier `exp(i k j Φ)`, with integer harmonic `j`. -/
def harmonic (k : ℝ) (j : ℤ) (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot) : ℂ :=
  Complex.exp ((↑(k * (j : ℝ) * phase ε p pz x0 F G q) : ℂ) * Complex.I)

/-- Rounding `k*p` to an integer makes every integer harmonic single-valued
under one full turn of the angular coordinate. -/
theorem harmonic_angularShift_two_pi (k : ℝ) (j m : ℤ) (ε p pz x0 : ℝ)
    (F G : Slow → ℝ) (q : Slot) (hkp : k * p = (m : ℝ)) :
    harmonic k j ε p pz x0 F G (angularShift (2 * Real.pi) q) =
      harmonic k j ε p pz x0 F G q := by
  have ha : k * (j : ℝ) * phase ε p pz x0 F G (angularShift (2 * Real.pi) q) =
      k * (j : ℝ) * phase ε p pz x0 F G q + ((j * m : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [phase_angularShift]
    calc
      k * (j : ℝ) * (phase ε p pz x0 F G q + p * (2 * Real.pi)) =
          k * (j : ℝ) * phase ε p pz x0 F G q + (j : ℝ) * (k * p) * (2 * Real.pi) := by
            ring
      _ = _ := by rw [hkp, Int.cast_mul]
  unfold harmonic
  rw [ha, Complex.ofReal_add, add_mul, Complex.exp_add]
  have hexp : Complex.exp
      ((↑(((j * m : ℤ) : ℝ) * (2 * Real.pi)) : ℂ) * Complex.I) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_intCast, Complex.ofReal_ofNat,
      mul_assoc] using Complex.exp_int_mul_two_pi_mul_I (j * m)
  rw [hexp, mul_one]

theorem harmonic_theta_periodic (k : ℝ) (j m : ℤ) (ε p pz x0 : ℝ)
    (F G : Slow → ℝ) (s : Slow) (v : ℝ) (hkp : k * p = (m : ℝ)) :
    Function.Periodic (fun θ => harmonic k j ε p pz x0 F G (s, (θ, v))) (2 * Real.pi) := by
  intro θ
  exact harmonic_angularShift_two_pi k j m ε p pz x0 F G (s, (θ, v)) hkp

/-- The complex harmonic is jointly smooth whenever the base frequencies are. -/
theorem contDiff_harmonic {n : WithTop ℕ∞} (k : ℝ) (j : ℤ) (ε p pz x0 : ℝ)
    (F G : Slow → ℝ) (hF : ContDiff ℝ n F) (hG : ContDiff ℝ n G) :
    ContDiff ℝ n (harmonic k j ε p pz x0 F G) := by
  unfold harmonic
  exact ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul (contDiff_phase ε p pz x0 F G hF hG))).mul contDiff_const).cexp

/-- The actual cylindrical normal is jointly `C∞` away from the axis. -/
theorem contDiffAt_phaseNormal (ε p pz x0 : ℝ) (F G : Slow → ℝ) (q : Slot)
    (hR : q.1.1 ≠ 0) (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ ∞ G) :
    ContDiffAt ℝ ∞ (phaseNormal ε p pz x0 F G) q := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (phase ε p pz x0 F G)) :=
    (contDiff_phase ε p pz x0 F G hF hG).fderiv_right (by simp)
  have hp (w : Slot) : ContDiff ℝ ∞ (fun z => fderiv ℝ (phase ε p pz x0 F G) z w) :=
    hD.clm_apply contDiff_const
  apply (EuclideanSpace.equiv (Fin 3) ℝ).comp_contDiffAt_iff.mp
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ ∞ (fun z => fderiv ℝ (phase ε p pz x0 F G) z eR) q
    exact (hp eR).contDiffAt
  · change ContDiffAt ℝ ∞ (fun z => fderiv ℝ (phase ε p pz x0 F G) z eTheta / z.1.1) q
    exact (hp eTheta).contDiffAt.div contDiffAt_fst.fst hR
  · change ContDiffAt ℝ ∞ (fun z => ε * fderiv ℝ (phase ε p pz x0 F G) z eZ) q
    exact contDiffAt_const.mul (hp eZ).contDiffAt

/-- The exact fast-slot derivative of `nΦ` used by the tangent ODE. -/
def normalSlotDerivative (ε p pz : ℝ) (F G : Slow → ℝ) (s : Slow) : Vec3 :=
  !₂[-(p * slowR F s + pz * slowR G s), 0,
    -ε * (p * slowZ F s + pz * slowZ G s)]

theorem hasDerivAt_phaseNormal_slot (ε p pz x0 θ v : ℝ) (F G : Slow → ℝ) (s : Slow)
    (hε : ε ≠ 0) (hF : DifferentiableAt ℝ F s) (hG : DifferentiableAt ℝ G s) :
    HasDerivAt (fun w => phaseNormal ε p pz x0 F G (s, (θ, w)))
      (normalSlotDerivative ε p pz F G s) v := by
  let n0 : Vec3 := !₂[x0, p / s.1, pz]
  have heq : (fun w => phaseNormal ε p pz x0 F G (s, (θ, w))) =
      (fun w => n0 + w • normalSlotDerivative ε p pz F G s) := by
    funext w
    rw [phaseNormal_formula ε p pz x0 F G (s, (θ, w)) hε hF hG]
    ext i
    fin_cases i <;> simp [n0, normalSlotDerivative] <;> ring
  rw [heq]
  simpa only [one_smul, zero_add, id_eq] using (hasDerivAt_const v n0).fun_add
    ((hasDerivAt_id v).smul_const (normalSlotDerivative ε p pz F G s))

/-- The comparison vector `B (s,K)` used after equation (26). -/
def referenceNormal (B s Kθ Kz : ℝ) : Vec3 := !₂[B * s, B * Kθ, B * Kz]

theorem vec3_norm_sq (w : Vec3) :
    ‖w‖ ^ 2 = (w 0) ^ 2 + (w 1) ^ 2 + (w 2) ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]

/-- A unit tangential direction forces the reference vector to have norm at least `B`. -/
theorem referenceNormal_norm_ge (B s Kθ Kz : ℝ)
    (hK : Kθ ^ 2 + Kz ^ 2 = 1) :
    B ≤ ‖referenceNormal B s Kθ Kz‖ := by
  have hn : ‖referenceNormal B s Kθ Kz‖ ^ 2 =
      (B * s) ^ 2 + (B * Kθ) ^ 2 + (B * Kz) ^ 2 := by
    simpa [referenceNormal] using vec3_norm_sq (referenceNormal B s Kθ Kz)
  have htan : (B * Kθ) ^ 2 + (B * Kz) ^ 2 = B ^ 2 := by
    calc
      (B * Kθ) ^ 2 + (B * Kz) ^ 2 = B ^ 2 * (Kθ ^ 2 + Kz ^ 2) := by ring
      _ = B ^ 2 := by rw [hK, mul_one]
  have hsq : B ^ 2 ≤ ‖referenceNormal B s Kθ Kz‖ ^ 2 := by
    nlinarith [sq_nonneg (B * s)]
  nlinarith [norm_nonneg (referenceNormal B s Kθ Kz)]

/-- An explicit reference-vector error bound gives a quantitative lower bound
for the actual phase normal. The comparison estimate itself is a hypothesis. -/
theorem phaseNormal_norm_lower (ε p pz x0 B s Kθ Kz δ : ℝ)
    (F G : Slow → ℝ) (q : Slot) (hK : Kθ ^ 2 + Kz ^ 2 = 1)
    (hclose : ‖phaseNormal ε p pz x0 F G q - referenceNormal B s Kθ Kz‖ ≤ δ) :
    B - δ ≤ ‖phaseNormal ε p pz x0 F G q‖ := by
  have href := referenceNormal_norm_ge B s Kθ Kz hK
  have htriangle := norm_sub_norm_le (referenceNormal B s Kθ Kz)
    (phaseNormal ε p pz x0 F G q)
  rw [norm_sub_rev] at htriangle
  linarith

/-- Half-scale closeness ensures the denominator in the projected pulse
equation is nonzero for this actual phase normal. -/
theorem phaseNormal_ne_zero_of_close (ε p pz x0 B s Kθ Kz : ℝ)
    (F G : Slow → ℝ) (q : Slot) (hB : 0 < B) (hK : Kθ ^ 2 + Kz ^ 2 = 1)
    (hclose : ‖phaseNormal ε p pz x0 F G q - referenceNormal B s Kθ Kz‖ ≤ B / 2) :
    phaseNormal ε p pz x0 F G q ≠ 0 := by
  have hlow := phaseNormal_norm_lower ε p pz x0 B s Kθ Kz (B / 2) F G q hK hclose
  intro hz
  rw [hz, norm_zero] at hlow
  linarith

end NavierStokes.PhaseCalculus
