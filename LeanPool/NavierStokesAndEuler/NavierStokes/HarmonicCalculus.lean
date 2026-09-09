/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.GraphCalculus
public import LeanPool.NavierStokesAndEuler.NavierStokes.JetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

/-!
# Actual differential calculus of a single harmonic

All directional operators below are evaluations of the Fréchet derivative.
The direction fields may vary with the point, so their derivatives are included
in the iterated operators.  The cylindrical formulas use the unscaled angular
direction, with its factors of `R⁻¹` and `R⁻²` displayed explicitly.
-/

noncomputable section

namespace NavierStokes.HarmonicCalculus

open Set Filter
open scoped Topology ContDiff BigOperators


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual derivative in a prescribed, possibly varying direction field. -/
noncomputable def along (V : E → E) (f : E → F) (x : E) : F :=
  fderiv ℝ f x (V x)

theorem contDiffOn_along {U : Set E} {V : E → E} {f : E → F}
    (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U) (hf : ContDiffOn ℝ ∞ f U) :
    ContDiffOn ℝ ∞ (along V f) U :=
  (hf.fderiv_of_isOpen hU (by simp)).clm_apply hV

theorem along_congr {U : Set E} {V : E → E} {f g : E → F} {x : E}
    (hU : IsOpen U) (hfg : EqOn f g U) (hx : x ∈ U) :
    along V f x = along V g x := by
  have he : f =ᶠ[𝓝 x] g := eventually_of_mem (hU.mem_nhds hx) hfg
  exact congrArg (fun L : E →L[ℝ] F => L (V x)) he.fderiv_eq

theorem along_add (V : E → E) {f g : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along V (fun y => f y + g y) x = along V f x + along V g x := by
  simp only [along, fderiv_fun_add hf hg, _root_.add_apply]

theorem along_mul (V : E → E) {f g : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    along V (fun y => f y * g y) x = along V f x * g x + f x * along V g x := by
  simp only [along, fderiv_fun_mul hf hg, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

theorem along_const_mul (V : E → E) (c : ℂ) {f : E → ℂ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    along V (fun y => c * f y) x = c * along V f x := by
  simp only [along, fderiv_const_mul hf c, _root_.smul_apply, smul_eq_mul]

theorem along_ofReal (V : E → E) {f : E → ℝ} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    along V (fun y => (f y : ℂ)) x = Complex.ofReal (along V f x) := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp x hf.hasFDerivAt
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun y => Complex.ofRealCLM (f y)) x (V x) = _
  rw [hd.fderiv]
  rfl

/-- The imaginary frequency `i κ`. -/
noncomputable def phaseFactor (κ : ℝ) : ℂ := (κ : ℂ) * Complex.I

theorem phaseFactor_sq (κ : ℝ) : phaseFactor κ ^ 2 = -(κ : ℂ) ^ 2 := by
  simp [phaseFactor, mul_pow, Complex.I_sq]

@[simp] theorem norm_phaseFactor (κ : ℝ) : ‖phaseFactor κ‖ = |κ| := by
  simp [phaseFactor, Real.norm_eq_abs]

/-- `κ = k*j` gives the carrier in the manuscript. -/
noncomputable def carrier (κ : ℝ) (Φ : E → ℝ) (x : E) : ℂ :=
  Complex.exp (phaseFactor κ * (Φ x : ℂ))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem carrier_ne_zero (κ : ℝ) (Φ : E → ℝ) (x : E) :
    carrier κ Φ x ≠ 0 := Complex.exp_ne_zero _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
@[simp] theorem norm_carrier (κ : ℝ) (Φ : E → ℝ) (x : E) :
    ‖carrier κ Φ x‖ = 1 := by
  have he : phaseFactor κ * (Φ x : ℂ) = ((κ * Φ x : ℝ) : ℂ) * Complex.I := by
    simp only [phaseFactor, Complex.ofReal_mul]
    ring
  rw [carrier, he, Complex.norm_exp_ofReal_mul_I]

theorem contDiffOn_carrier {U : Set E} (κ : ℝ) {Φ : E → ℝ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) : ContDiffOn ℝ ∞ (carrier κ Φ) U := by
  exact (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hΦ)).cexp

theorem differentiableAt_carrier (κ : ℝ) {Φ : E → ℝ} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) : DifferentiableAt ℝ (carrier κ Φ) x := by
  exact ((Complex.ofRealCLM.hasFDerivAt.comp x hΦ.hasFDerivAt).const_mul
    (phaseFactor κ)).cexp.differentiableAt

theorem along_carrier (V : E → E) (κ : ℝ) {Φ : E → ℝ} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) :
    along V (carrier κ Φ) x =
      phaseFactor κ * Complex.ofReal (along V Φ x) * carrier κ Φ x := by
  have hd := ((Complex.ofRealCLM.hasFDerivAt.comp x hΦ.hasFDerivAt).const_mul
    (phaseFactor κ)).cexp
  dsimp only [Function.comp_def] at hd
  change fderiv ℝ (fun y => Complex.exp (phaseFactor κ * Complex.ofRealCLM (Φ y))) x
      (V x) = _
  rw [hd.fderiv]
  simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, carrier, along]
  ring

/-- A coefficient multiplied by one actual complex harmonic. -/
noncomputable def mode (κ : ℝ) (Φ : E → ℝ) (a : E → ℂ) (x : E) : ℂ :=
  a x * carrier κ Φ x

theorem contDiffOn_mode {U : Set E} (κ : ℝ) {Φ : E → ℝ} {a : E → ℂ}
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U) :
    ContDiffOn ℝ ∞ (mode κ Φ a) U := ha.mul (contDiffOn_carrier κ hΦ)

/-- First product formula, with the phase derivative and the coefficient
derivative separated. -/
theorem along_mode (V : E → E) (κ : ℝ) {Φ : E → ℝ} {a : E → ℂ} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x) (ha : DifferentiableAt ℝ a x) :
    along V (mode κ Φ a) x =
      (along V a x + phaseFactor κ * Complex.ofReal (along V Φ x) * a x) *
        carrier κ Φ x := by
  unfold mode
  rw [along_mul V ha (differentiableAt_carrier κ hΦ), along_carrier V κ hΦ]
  ring

/-- Second product formula. Because the direction field is inside `along`,
its derivative is present in both `along V (along V a)` and the second phase
derivative; no constancy of the field is assumed. -/
theorem along_along_mode {U : Set E} {V : E → E} (κ : ℝ)
    {Φ : E → ℝ} {a : E → ℂ} {x : E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hΦ : ContDiffOn ℝ ∞ Φ U) (ha : ContDiffOn ℝ ∞ a U) (hx : x ∈ U) :
    along V (along V (mode κ Φ a)) x =
      (along V (along V a) x +
        2 * phaseFactor κ * Complex.ofReal (along V Φ x) * along V a x +
        (phaseFactor κ * Complex.ofReal (along V (along V Φ) x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (along V Φ x) ^ 2) * a x) * carrier κ Φ x := by
  let b : E → ℂ := fun y =>
    along V a y + phaseFactor κ * Complex.ofReal (along V Φ y) * a y
  have hDa := contDiffOn_along hU hV ha
  have hDΦ := contDiffOn_along hU hV hΦ
  have hDc : ContDiffOn ℝ ∞ (fun y => Complex.ofReal (along V Φ y)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hDΦ
  have hb : ContDiffOn ℝ ∞ b U := hDa.add ((contDiffOn_const.mul hDc).mul ha)
  have hfirst : EqOn (along V (mode κ Φ a)) (mode κ Φ b) U := by
    intro y hy
    exact along_mode V κ ((hΦ.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
      ((ha.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp))
  have da := (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dDa := (hDa.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dΦ := (hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dDΦ := (hDΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dDc := (hDc.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have db := (hb.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [along_congr hU hfirst hx, along_mode V κ dΦ db]
  have hDb : along V b x = along V (along V a) x +
      phaseFactor κ * Complex.ofReal (along V (along V Φ) x) * a x +
      phaseFactor κ * Complex.ofReal (along V Φ x) * along V a x := by
    dsimp only [b]
    rw [along_add V dDa ((differentiableAt_const _).fun_mul dDc |>.fun_mul da),
      along_mul V ((differentiableAt_const _).fun_mul dDc) da,
      along_const_mul V (phaseFactor κ) dDc, along_ofReal V dDΦ]
    ring
  rw [hDb]
  dsimp only [b]
  have hs := phaseFactor_sq κ
  ring_nf at hs ⊢
  rw [hs]
  ring

/-! ## Cylindrical scalar operators -/

/-- The scalar cylindrical Laplacian, also valid on prescribed graph
directions. `Vθ` is the unscaled angular direction. -/
noncomputable def cylindricalLaplacian (R : E → ℝ) (Vr Vθ Vz : E → E)
    (f : E → F) (x : E) : F :=
  along Vr (along Vr f) x + (R x)⁻¹ • along Vr f x +
    ((R x) ^ 2)⁻¹ • along Vθ (along Vθ f) x + along Vz (along Vz f) x

/-- The actual phase gradient in the orthonormal cylindrical frame. -/
noncomputable def phaseNormal (R : E → ℝ) (Vr Vθ Vz : E → E)
    (Φ : E → ℝ) (x : E) : EuclideanSpace ℝ (Fin 3) :=
  !₂[along Vr Φ x, along Vθ Φ x / R x, along Vz Φ x]

/-- The phase-square coefficient before rewriting it as a normal norm. -/
noncomputable def phaseSquare (R : E → ℝ) (Vr Vθ Vz : E → E)
    (Φ : E → ℝ) (x : E) : ℝ :=
  (along Vr Φ x) ^ 2 + ((R x) ^ 2)⁻¹ * (along Vθ Φ x) ^ 2 +
    (along Vz Φ x) ^ 2

theorem phaseSquare_eq_norm_sq (R : E → ℝ) (Vr Vθ Vz : E → E)
    (Φ : E → ℝ) (x : E) :
    phaseSquare R Vr Vθ Vz Φ x = ‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2 := by
  rw [PhaseCalculus.vec3_norm_sq]
  simp [phaseSquare, phaseNormal, div_eq_mul_inv]
  ring

/-- The phase/coefficient cross term in the scalar Laplacian. -/
noncomputable def phaseCross (R : E → ℝ) (Vr Vθ Vz : E → E)
    (Φ : E → ℝ) (a : E → ℂ) (x : E) : ℂ :=
  Complex.ofReal (along Vr Φ x) * along Vr a x +
    Complex.ofReal (((R x) ^ 2)⁻¹) * Complex.ofReal (along Vθ Φ x) * along Vθ a x +
    Complex.ofReal (along Vz Φ x) * along Vz a x

/-- Exact phase-square, cross, and phase-divergence decomposition. -/
theorem cylindricalLaplacian_mode {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} (κ : ℝ) {Φ : E → ℝ} {a : E → ℂ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (mode κ Φ a) x =
      (cylindricalLaplacian R Vr Vθ Vz a x +
        2 * phaseFactor κ * phaseCross R Vr Vθ Vz Φ a x +
        (phaseFactor κ * Complex.ofReal (cylindricalLaplacian R Vr Vθ Vz Φ x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (phaseSquare R Vr Vθ Vz Φ x)) * a x) *
        carrier κ Φ x := by
  have da := (ha.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have dΦ := (hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  unfold cylindricalLaplacian
  rw [along_along_mode κ hU hr hΦ ha hx, along_along_mode κ hU hθ hΦ ha hx,
    along_along_mode κ hU hz hΦ ha hx, along_mode Vr κ dΦ da]
  simp only [phaseCross, phaseSquare, Complex.real_smul, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- Equivalent formulation using the squared Euclidean length of the actual normal. -/
theorem cylindricalLaplacian_mode_normal {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} (κ : ℝ) {Φ : E → ℝ} {a : E → ℂ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (mode κ Φ a) x =
      (cylindricalLaplacian R Vr Vθ Vz a x +
        2 * phaseFactor κ * phaseCross R Vr Vθ Vz Φ a x +
        (phaseFactor κ * Complex.ofReal (cylindricalLaplacian R Vr Vθ Vz Φ x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2)) * a x) *
        carrier κ Φ x := by
  rw [← phaseSquare_eq_norm_sq]
  exact cylindricalLaplacian_mode R κ hU hr hθ hz hΦ ha hx

/-- An angular derivative which is constant near the point has zero next
angular derivative. This applies to the affine angular phase and to angularly
independent stripped coefficients. -/
theorem along_along_eq_zero_of_const {U : Set E} {V : E → E} {f : E → F}
    {c : F} {x : E} (hU : IsOpen U) (hf : EqOn (along V f) (fun _ => c) U)
    (hx : x ∈ U) : along V (along V f) x = 0 := by
  rw [along_congr hU hf hx]
  simp [along]

/-- With no angular coefficient dependence, its scalar Laplacian contains
only radial and axial coefficient derivatives. -/
theorem cylindricalLaplacian_angular_independent {U : Set E} (R : E → ℝ)
    (Vr Vθ Vz : E → E) {f : E → F} {x : E}
    (hU : IsOpen U) (hf : EqOn (along Vθ f) (fun _ => 0) U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz f x =
      along Vr (along Vr f) x + (R x)⁻¹ • along Vr f x + along Vz (along Vz f) x := by
  simp only [cylindricalLaplacian, along_along_eq_zero_of_const hU hf hx,
    smul_zero, add_zero]

/-- For an affine angular phase, the phase-divergence term is exactly
`Dr n_r + n_r/R + Dz n_z`. -/
theorem cylindricalLaplacian_phase {U : Set E} (R : E → ℝ)
    (Vr Vθ Vz : E → E) {Φ : E → ℝ} {p : ℝ} {x : E}
    (hU : IsOpen U) (hΦθ : EqOn (along Vθ Φ) (fun _ => p) U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz Φ x =
      along Vr (fun y => phaseNormal R Vr Vθ Vz Φ y 0) x +
        phaseNormal R Vr Vθ Vz Φ x 0 / R x +
        along Vz (fun y => phaseNormal R Vr Vθ Vz Φ y 2) x := by
  simp [cylindricalLaplacian, along_along_eq_zero_of_const hU hΦθ hx,
    phaseNormal, smul_eq_mul, div_eq_mul_inv]
  ring

/-- The scalar part of the manuscript's no-slow-angular-dependence formula.
Both the absent angular coefficient derivative and the affine angular phase
are hypotheses on actual derivatives on an open set. -/
theorem cylindricalLaplacian_mode_angular_independent {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} (κ : ℝ) {Φ : E → ℝ} {a : E → ℂ} {p : ℝ} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ContDiffOn ℝ ∞ a U) (haθ : EqOn (along Vθ a) (fun _ => 0) U)
    (hΦθ : EqOn (along Vθ Φ) (fun _ => p) U) (hx : x ∈ U) :
    cylindricalLaplacian R Vr Vθ Vz (mode κ Φ a) x =
      (along Vr (along Vr a) x + (R x)⁻¹ • along Vr a x + along Vz (along Vz a) x +
        2 * phaseFactor κ *
          (Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 0) * along Vr a x +
            Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 2) * along Vz a x) +
        (phaseFactor κ * Complex.ofReal
          (along Vr (fun y => phaseNormal R Vr Vθ Vz Φ y 0) x +
            phaseNormal R Vr Vθ Vz Φ x 0 / R x +
            along Vz (fun y => phaseNormal R Vr Vθ Vz Φ y 2) x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2)) * a x) *
        carrier κ Φ x := by
  rw [cylindricalLaplacian_mode_normal R κ hU hr hθ hz hΦ ha hx,
    cylindricalLaplacian_angular_independent R Vr Vθ Vz hU haθ hx,
    cylindricalLaplacian_phase R Vr Vθ Vz hU hΦθ hx]
  simp only [phaseCross, haθ hx, mul_zero, add_zero]
  rfl

/-! ## Divergence and the longitudinal gain -/

abbrev ComplexVector := Fin 3 → ℂ

/-- Complex-bilinear contraction with a real normal. -/
noncomputable def normalDot (n : EuclideanSpace ℝ (Fin 3)) (a : ComplexVector) : ℂ :=
  (n 0 : ℂ) * a 0 + (n 1 : ℂ) * a 1 + (n 2 : ℂ) * a 2

noncomputable def vectorMode (κ : ℝ) (Φ : E → ℝ) (a : E → ComplexVector)
    (x : E) : ComplexVector := fun i => mode κ Φ (fun y => a y i) x

/-- The derivative of the cylindrical frame with respect to angle. -/
noncomputable def angularGenerator (a : ComplexVector) : ComplexVector :=
  ![-a 1, a 0, 0]

theorem angularGenerator_sq (a : ComplexVector) :
    angularGenerator (angularGenerator a) = ![-a 0, -a 1, 0] := by
  ext i
  fin_cases i <;> simp [angularGenerator]

/-- The scalar component Laplacians plus the two cylindrical frame
connections. Its identification with Cartesian vector Laplacian belongs to
the cylindrical coordinate calculus. -/
noncomputable def cylindricalVectorLaplacian (R : E → ℝ) (Vr Vθ Vz : E → E)
    (a : E → ComplexVector) (x : E) : ComplexVector := fun i =>
  cylindricalLaplacian R Vr Vθ Vz (fun y => a y i) x + ((R x) ^ 2)⁻¹ •
    (2 * angularGenerator (fun j => along Vθ (fun y => a y j) x) i +
      angularGenerator (angularGenerator (a x)) i)

/-- Harmonic vector Laplacian, including the additional angular frame
term `2 i κ (n_θ/R) J a`. All coefficient and phase derivatives remain actual
directional Fréchet derivatives. -/
theorem cylindricalVectorLaplacian_vectorMode {U : Set E} (R : E → ℝ)
    {Vr Vθ Vz : E → E} (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hU : IsOpen U) (hr : ContDiffOn ℝ ∞ Vr U) (hθ : ContDiffOn ℝ ∞ Vθ U)
    (hz : ContDiffOn ℝ ∞ Vz U) (hΦ : ContDiffOn ℝ ∞ Φ U)
    (ha : ∀ i, ContDiffOn ℝ ∞ (fun y => a y i) U) (hx : x ∈ U) :
    cylindricalVectorLaplacian R Vr Vθ Vz (vectorMode κ Φ a) x = fun i =>
      (cylindricalVectorLaplacian R Vr Vθ Vz a x i +
        2 * phaseFactor κ * phaseCross R Vr Vθ Vz Φ (fun y => a y i) x +
        (phaseFactor κ * Complex.ofReal (cylindricalLaplacian R Vr Vθ Vz Φ x) -
          (κ : ℂ) ^ 2 * Complex.ofReal (‖phaseNormal R Vr Vθ Vz Φ x‖ ^ 2)) * a x i +
        2 * phaseFactor κ * Complex.ofReal (phaseNormal R Vr Vθ Vz Φ x 1 / R x) *
          angularGenerator (a x) i) * carrier κ Φ x := by
  have dΦ := (hΦ.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have da i := ((ha i).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
  have hL i := cylindricalLaplacian_mode_normal R κ hU hr hθ hz hΦ (ha i) hx
  have hD (i : Fin 3) : along Vθ (fun y => a y i * carrier κ Φ y) x =
      (along Vθ (fun y => a y i) x +
        phaseFactor κ * Complex.ofReal (along Vθ Φ x) * a x i) * carrier κ Φ x :=
    along_mode Vθ κ dΦ (da i)
  funext i
  change cylindricalLaplacian R Vr Vθ Vz (mode κ Φ (fun y => a y i)) x + _ = _
  rw [hL i]
  fin_cases i <;>
    simp [cylindricalVectorLaplacian, angularGenerator, vectorMode, hD 0, hD 1,
      mode, phaseNormal, Complex.real_smul, div_eq_mul_inv, pow_two] <;> ring

/-- Angularly independent coefficients retain only the `J² a/R²`
connection, namely `-(a_r,a_θ,0)/R²`. -/
theorem cylindricalVectorLaplacian_angular_independent {U : Set E} (R : E → ℝ)
    (Vr Vθ Vz : E → E) {a : E → ComplexVector} {x : E}
    (hU : IsOpen U)
    (haθ : ∀ i, EqOn (along Vθ (fun y => a y i)) (fun _ => 0) U) (hx : x ∈ U) :
    cylindricalVectorLaplacian R Vr Vθ Vz a x = fun i =>
      along Vr (along Vr (fun y => a y i)) x +
        (R x)⁻¹ • along Vr (fun y => a y i) x +
        along Vz (along Vz (fun y => a y i)) x +
        ((R x) ^ 2)⁻¹ • angularGenerator (angularGenerator (a x)) i := by
  funext i
  unfold cylindricalVectorLaplacian
  rw [cylindricalLaplacian_angular_independent R Vr Vθ Vz hU (haθ i) hx]
  have he : (fun j => along Vθ (fun y => a y j) x) = 0 := by
    funext j
    exact haθ j hx
  rw [he]
  have hzero : angularGenerator 0 = 0 := by
    funext j
    fin_cases j <;> simp [angularGenerator]
  simp only [hzero, Pi.zero_apply, mul_zero, zero_add]

/-- Divergence of physical cylindrical components in prescribed directions. -/
noncomputable def cylindricalDivergence (R : E → ℝ) (Vr Vθ Vz : E → E)
    (a : E → ComplexVector) (x : E) : ℂ :=
  along Vr (fun y => a y 0) x + (R x)⁻¹ • a x 0 +
    (R x)⁻¹ • along Vθ (fun y => a y 1) x + along Vz (fun y => a y 2) x

/-- The divergence of a coefficient with no angular dependence. -/
noncomputable def strippedDivergence (R : E → ℝ) (Vr Vz : E → E)
    (a : E → ComplexVector) (x : E) : ℂ :=
  along Vr (fun y => a y 0) x + (R x)⁻¹ • a x 0 + along Vz (fun y => a y 2) x

theorem cylindricalDivergence_vectorMode (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x) :
    cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) x =
      (cylindricalDivergence R Vr Vθ Vz a x +
        phaseFactor κ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x)) * carrier κ Φ x := by
  unfold cylindricalDivergence vectorMode
  rw [along_mode Vr κ hΦ (ha 0), along_mode Vθ κ hΦ (ha 1),
    along_mode Vz κ hΦ (ha 2)]
  simp [normalDot, phaseNormal, mode, Complex.real_smul, div_eq_mul_inv]
  ring

/-- Exact harmonic divergence forces the longitudinal identity. The only
coefficient angular derivative used by divergence is that of `a_θ`. -/
theorem longitudinal_identity (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) x = 0) :
    phaseFactor κ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) =
      -strippedDivergence R Vr Vz a x := by
  rw [cylindricalDivergence_vectorMode R Vr Vθ Vz κ hΦ ha] at hdiv
  have he := (mul_eq_zero.mp hdiv).resolve_right (carrier_ne_zero κ Φ x)
  have he' : strippedDivergence R Vr Vz a x +
      phaseFactor κ * normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x) = 0 := by
    simpa only [cylindricalDivergence, strippedDivergence, haθ, smul_zero, add_zero] using he
  exact eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using he')

/-- The complex coefficient in the direction of the unit real normal. -/
noncomputable def longitudinalCoefficient (n : EuclideanSpace ℝ (Fin 3))
    (a : ComplexVector) : ℂ := normalDot n a / (‖n‖ : ℂ)

@[simp] theorem norm_longitudinalCoefficient (n : EuclideanSpace ℝ (Fin 3))
    (a : ComplexVector) :
    ‖longitudinalCoefficient n a‖ = ‖normalDot n a‖ / ‖n‖ := by
  simp [longitudinalCoefficient]

theorem norm_strippedDivergence_le (R : E → ℝ) (Vr Vz : E → E)
    (a : E → ComplexVector) (x : E) :
    ‖strippedDivergence R Vr Vz a x‖ ≤
      ‖along Vr (fun y => a y 0) x‖ + ‖a x 0‖ / |R x| +
        ‖along Vz (fun y => a y 2) x‖ := by
  calc
    ‖strippedDivergence R Vr Vz a x‖ ≤
        ‖along Vr (fun y => a y 0) x + (R x)⁻¹ • a x 0‖ +
          ‖along Vz (fun y => a y 2) x‖ := norm_add_le _ _
    _ ≤ (‖along Vr (fun y => a y 0) x‖ + ‖(R x)⁻¹ • a x 0‖) +
          ‖along Vz (fun y => a y 2) x‖ := add_le_add_left (norm_add_le _ _) _
    _ = _ := by simp only [norm_smul, norm_inv, Real.norm_eq_abs, div_eq_mul_inv]; ring

/-- Exact divergence supplies the frequency gain; the identity is proved
above from the actual harmonic derivative, not assumed here. -/
theorem normalDot_norm_eq_div (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hκ : κ ≠ 0) (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) x = 0) :
    ‖normalDot (phaseNormal R Vr Vθ Vz Φ x) (a x)‖ =
      ‖strippedDivergence R Vr Vz a x‖ / |κ| := by
  have he := congrArg norm (longitudinal_identity R Vr Vθ Vz κ hΦ ha haθ hdiv)
  simp only [norm_mul, norm_phaseFactor, norm_neg] at he
  apply (eq_div_iff (abs_ne_zero.mpr hκ)).mpr
  simpa only [mul_comm] using he

/-- Quantitative pointwise gain using actual radial and axial derivatives
of the coefficient. -/
theorem longitudinalCoefficient_bound (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    (hκ : κ ≠ 0) (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) x = 0) :
    ‖longitudinalCoefficient (phaseNormal R Vr Vθ Vz Φ x) (a x)‖ ≤
      (‖along Vr (fun y => a y 0) x‖ + ‖a x 0‖ / |R x| +
        ‖along Vz (fun y => a y 2) x‖) /
        (|κ| * ‖phaseNormal R Vr Vθ Vz Φ x‖) := by
  rw [norm_longitudinalCoefficient, normalDot_norm_eq_div R Vr Vθ Vz κ hκ hΦ ha haθ hdiv,
    div_div]
  exact div_le_div_of_nonneg_right (norm_strippedDivergence_le R Vr Vz a x)
    (mul_nonneg (abs_nonneg κ) (norm_nonneg _))

/-- A lower bound on radius and normal, together with bounds on the
actual coefficient derivatives, yields the uniform inverse-frequency gain. -/
theorem longitudinal_gain_frequency (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    {r₀ n₀ A Ar Az : ℝ} (hκ : κ ≠ 0) (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) x = 0)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ R x)
    (hn₀ : 0 < n₀) (hn : n₀ ≤ ‖phaseNormal R Vr Vθ Vz Φ x‖)
    (hA : ‖a x 0‖ ≤ A) (hAr : ‖along Vr (fun y => a y 0) x‖ ≤ Ar)
    (hAz : ‖along Vz (fun y => a y 2) x‖ ≤ Az) :
    ‖longitudinalCoefficient (phaseNormal R Vr Vθ Vz Φ x) (a x)‖ ≤
      (Ar + A / r₀ + Az) / (|κ| * n₀) := by
  have hA₀ : 0 ≤ A := (norm_nonneg _).trans hA
  have hrabs : r₀ ≤ |R x| := hr.trans (le_abs_self _)
  have hrad : ‖a x 0‖ / |R x| ≤ A / r₀ :=
    (div_le_div_of_nonneg_right hA (abs_nonneg _)).trans
      (div_le_div_of_nonneg_left hA₀ hr₀ hrabs)
  have hnum : ‖along Vr (fun y => a y 0) x‖ + ‖a x 0‖ / |R x| +
      ‖along Vz (fun y => a y 2) x‖ ≤ Ar + A / r₀ + Az :=
    add_le_add (add_le_add hAr hrad) hAz
  have hnum₀ : 0 ≤ Ar + A / r₀ + Az :=
    (add_nonneg (add_nonneg (norm_nonneg _) (div_nonneg (norm_nonneg _) (abs_nonneg _)))
      (norm_nonneg _)).trans hnum
  calc
    ‖longitudinalCoefficient (phaseNormal R Vr Vθ Vz Φ x) (a x)‖ ≤
        (‖along Vr (fun y => a y 0) x‖ + ‖a x 0‖ / |R x| +
          ‖along Vz (fun y => a y 2) x‖) /
          (|κ| * ‖phaseNormal R Vr Vθ Vz Φ x‖) :=
      longitudinalCoefficient_bound R Vr Vθ Vz κ hκ hΦ ha haθ hdiv
    _ ≤ (Ar + A / r₀ + Az) / (|κ| * ‖phaseNormal R Vr Vθ Vz Φ x‖) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    _ ≤ (Ar + A / r₀ + Az) / (|κ| * n₀) :=
      div_le_div_of_nonneg_left hnum₀ (mul_pos (abs_pos.mpr hκ) hn₀)
        (mul_le_mul_of_nonneg_left hn (abs_nonneg _))

/-- The manuscript frequency is `κ = k*j`, with a nonzero integer harmonic. -/
theorem longitudinal_gain (R : E → ℝ) (Vr Vθ Vz : E → E)
    (k : ℝ) (j : ℤ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E}
    {r₀ n₀ A Ar Az : ℝ} (hk : k ≠ 0) (hj : j ≠ 0)
    (hΦ : DifferentiableAt ℝ Φ x)
    (ha : ∀ i, DifferentiableAt ℝ (fun y => a y i) x)
    (haθ : along Vθ (fun y => a y 1) x = 0)
    (hdiv : cylindricalDivergence R Vr Vθ Vz (vectorMode (k * (j : ℝ)) Φ a) x = 0)
    (hr₀ : 0 < r₀) (hr : r₀ ≤ R x)
    (hn₀ : 0 < n₀) (hn : n₀ ≤ ‖phaseNormal R Vr Vθ Vz Φ x‖)
    (hA : ‖a x 0‖ ≤ A) (hAr : ‖along Vr (fun y => a y 0) x‖ ≤ Ar)
    (hAz : ‖along Vz (fun y => a y 2) x‖ ≤ Az) :
    ‖longitudinalCoefficient (phaseNormal R Vr Vθ Vz Φ x) (a x)‖ ≤
      (Ar + A / r₀ + Az) / (|k| * |(j : ℝ)| * n₀) := by
  have hjr : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
  simpa only [abs_mul] using longitudinal_gain_frequency R Vr Vθ Vz (k * (j : ℝ))
    (mul_ne_zero hk hjr) hΦ ha haθ hdiv hr₀ hr hn₀ hn hA hAr hAz

/-- Operator norms of the actual full coefficient derivatives can be
used to supply the directional derivative bounds above. -/
theorem norm_along_le (V : E → E) (f : E → F) (x : E) :
    ‖along V f x‖ ≤ ‖fderiv ℝ f x‖ * ‖V x‖ :=
  (fderiv ℝ f x).le_opNorm (V x)

/-! ## Finite jets of the longitudinal contraction -/

theorem contDiffOn_strippedDivergence {U : Set E} {R : E → ℝ} {Vr Vz : E → E}
    {a : E → ComplexVector} (hU : IsOpen U)
    (hR : ContDiffOn ℝ ∞ R U) (hRne : ∀ x ∈ U, R x ≠ 0)
    (hr : ContDiffOn ℝ ∞ Vr U) (hz : ContDiffOn ℝ ∞ Vz U)
    (ha₀ : ContDiffOn ℝ ∞ (fun y => a y 0) U)
    (ha₂ : ContDiffOn ℝ ∞ (fun y => a y 2) U) :
    ContDiffOn ℝ ∞ (strippedDivergence R Vr Vz a) U :=
  ((contDiffOn_along hU hr ha₀).add ((hR.inv hRne).smul ha₀)).add
    (contDiffOn_along hU hz ha₂)

/-- At every derivative order, the contraction `n·a` has the same
inverse-frequency factor. Derivatives of the normal are included on the
left, and derivatives of the full coefficient divergence on the right. -/
theorem normalDot_jet_norm_eq {U : Set E} (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {x : E} (m : ℕ)
    (hκ : κ ≠ 0) (hU : IsOpen U) (hΦ : DifferentiableOn ℝ Φ U)
    (ha : ∀ i, DifferentiableOn ℝ (fun y => a y i) U)
    (haθ : ∀ y ∈ U, along Vθ (fun z => a z 1) y = 0)
    (hdiv : ∀ y ∈ U, cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) y = 0)
    (hS : ContDiffOn ℝ ∞ (strippedDivergence R Vr Vz a) U) (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ m (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) x‖ =
      ‖iteratedFDeriv ℝ m (strippedDivergence R Vr Vz a) x‖ / |κ| := by
  have hc : phaseFactor κ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    simpa only [norm_phaseFactor] using abs_ne_zero.mpr hκ
  have heq : EqOn (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y))
      (fun y => (-(phaseFactor κ)⁻¹) • strippedDivergence R Vr Vz a y) U := by
    intro y hy
    have he := longitudinal_identity R Vr Vθ Vz κ
      ((hΦ y hy).differentiableAt (hU.mem_nhds hy))
      (fun i => (ha i y hy).differentiableAt (hU.mem_nhds hy)) (haθ y hy) (hdiv y hy)
    calc
      _ = -strippedDivergence R Vr Vz a y / phaseFactor κ :=
        (eq_div_iff hc).mpr (by simpa only [mul_comm] using he)
      _ = _ := by simp only [smul_eq_mul, div_eq_mul_inv]; ring
  have he : (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) =ᶠ[𝓝 x]
      (fun y => (-(phaseFactor κ)⁻¹) • strippedDivergence R Vr Vz a y) :=
    eventually_of_mem (hU.mem_nhds hx) heq
  have he' : (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) =ᶠ[𝓝[univ] x]
      (fun y => (-(phaseFactor κ)⁻¹) • strippedDivergence R Vr Vz a y) := by
    simpa only [nhdsWithin_univ] using he
  have hj := he'.iteratedFDerivWithin_eq (𝕜 := ℝ) he.self_of_nhds m
  simp only [iteratedFDerivWithin_univ] at hj
  rw [hj, iteratedFDeriv_const_smul_apply'
    ((hS.contDiffAt (hU.mem_nhds hx)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl m))]
  simp only [norm_smul, norm_neg, norm_inv, norm_phaseFactor, div_eq_mul_inv]
  ring

/-- Uniform finite-jet version of the exact contraction estimate. -/
theorem normalDot_finiteJetBound {U : Set E} (R : E → ℝ) (Vr Vθ Vz : E → E)
    (κ : ℝ) {Φ : E → ℝ} {a : E → ComplexVector} {m : ℕ} {C : ℝ}
    (hκ : κ ≠ 0) (hU : IsOpen U) (hΦ : DifferentiableOn ℝ Φ U)
    (ha : ∀ i, DifferentiableOn ℝ (fun y => a y i) U)
    (haθ : ∀ y ∈ U, along Vθ (fun z => a z 1) y = 0)
    (hdiv : ∀ y ∈ U, cylindricalDivergence R Vr Vθ Vz (vectorMode κ Φ a) y = 0)
    (hS : ContDiffOn ℝ ∞ (strippedDivergence R Vr Vz a) U)
    (hJ : JetBounds.FiniteJetBound m (strippedDivergence R Vr Vz a) U C) :
    JetBounds.FiniteJetBound m
      (fun y => normalDot (phaseNormal R Vr Vθ Vz Φ y) (a y)) U (C / |κ|) := by
  intro n hn x hx
  rw [normalDot_jet_norm_eq R Vr Vθ Vz κ n hκ hU hΦ ha haθ hdiv hS hx]
  exact div_le_div_of_nonneg_right (hJ n hn x hx) (abs_nonneg κ)

/-- The coefficient divergence bound is derived from actual coefficient
jets through order `m+1`, and graph-direction and inverse-radius jets
through order `m`. -/
theorem strippedDivergence_finiteJetBound {U : Set E} {R : E → ℝ} {Vr Vz : E → E}
    {a : E → ComplexVector} {m : ℕ} {Ar Az Cr Cz CI : ℝ}
    (hU : IsOpen U) (hR : ContDiffOn ℝ ∞ R U) (hRne : ∀ x ∈ U, R x ≠ 0)
    (hr : ContDiffOn ℝ ∞ Vr U) (hz : ContDiffOn ℝ ∞ Vz U)
    (ha₀ : ContDiffOn ℝ ∞ (fun y => a y 0) U)
    (ha₂ : ContDiffOn ℝ ∞ (fun y => a y 2) U)
    (hAr : JetBounds.FiniteJetBound (m + 1) (fun y => a y 0) U Ar)
    (hAz : JetBounds.FiniteJetBound (m + 1) (fun y => a y 2) U Az)
    (hCr : JetBounds.FiniteJetBound m Vr U Cr)
    (hCz : JetBounds.FiniteJetBound m Vz U Cz)
    (hCI : JetBounds.FiniteJetBound m (fun y => (R y)⁻¹) U CI) :
    JetBounds.FiniteJetBound m (strippedDivergence R Vr Vz a) U
      ((2 : ℝ) ^ m * Ar * Cr +
        ‖(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ)‖ * (2 : ℝ) ^ m * CI * Ar +
        (2 : ℝ) ^ m * Az * Cz) := by
  have hm := ENat.natCast_le_of_coe_top_le_withTop le_rfl m
  have hm1 := ENat.natCast_le_of_coe_top_le_withTop le_rfl (m + 1)
  have hbr := JetBounds.FiniteJetBound.transport hU (hr.of_le hm) (ha₀.of_le hm1) hCr hAr
  have hbz := JetBounds.FiniteJetBound.transport hU (hz.of_le hm) (ha₂.of_le hm1) hCz hAz
  have hbi := JetBounds.FiniteJetBound.bilinear
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ) hU
    ((hR.inv hRne).of_le hm) (ha₀.of_le hm) hCI (hAr.of_le (Nat.le_succ m))
  have hdr := (contDiffOn_along hU hr ha₀).of_le hm
  have hdz := (contDiffOn_along hU hz ha₂).of_le hm
  have hdi := ((hR.inv hRne).smul ha₀).of_le hm
  exact JetBounds.FiniteJetBound.add hU (hdr.add hdi) hdz
    (JetBounds.FiniteJetBound.add hU hdr hdi hbr hbi) hbz

/-! ## Compatibility with the phase and graph already formalized -/

/-- This carrier is the previously formalized slot harmonic, including its
integer-harmonic and angular-period conventions. -/
theorem carrier_eq_slot_harmonic (k : ℝ) (j : ℤ) (ε p pz x₀ : ℝ)
    (F G : PhaseCalculus.Slow → ℝ) :
    carrier (k * (j : ℝ)) (PhaseCalculus.phase ε p pz x₀ F G) =
      PhaseCalculus.harmonic k j ε p pz x₀ F G := by
  funext q
  unfold carrier phaseFactor PhaseCalculus.harmonic
  apply congrArg Complex.exp
  simp only [Complex.ofReal_mul]
  ring

/-- The graph direction in the axial slot is `ε ∂Z`; after that rescaling
the normal here is exactly the normal used in the phase module. -/
theorem phaseNormal_eq_slot_normal (ε p pz x₀ : ℝ)
    (F G : PhaseCalculus.Slow → ℝ) (q : PhaseCalculus.Slot) :
    phaseNormal (fun y : PhaseCalculus.Slot => y.1.1)
      (fun _ => PhaseCalculus.eR) (fun _ => PhaseCalculus.eTheta)
      (fun _ => ε • PhaseCalculus.eZ) (PhaseCalculus.phase ε p pz x₀ F G) q =
      PhaseCalculus.phaseNormal ε p pz x₀ F G q := by
  ext i
  fin_cases i <;>
    simp [phaseNormal, PhaseCalculus.phaseNormal, along, map_smul, smul_eq_mul]

/-- Restricting a complex harmonic to the actual auxiliary graph gives the
radial product formula with the genuine radial graph vector field. -/
theorem graph_deriv_radial_mode (d : ℝ) (vr vt : GraphCalculus.Plane) (κ : ℝ)
    {Φ : GraphCalculus.Lift → ℝ} {a : GraphCalculus.Lift → ℂ} {r t : ℝ}
    (hr : r ≠ 0) (hΦ : DifferentiableAt ℝ Φ (GraphCalculus.graph d vr vt (r, t)))
    (ha : DifferentiableAt ℝ a (GraphCalculus.graph d vr vt (r, t))) :
    deriv (fun s => mode κ Φ a (GraphCalculus.graph d vr vt (s, t))) r =
      (along (GraphCalculus.radialVector d vr) a (GraphCalculus.graph d vr vt (r, t)) +
        phaseFactor κ * Complex.ofReal
          (along (GraphCalculus.radialVector d vr) Φ (GraphCalculus.graph d vr vt (r, t))) *
            a (GraphCalculus.graph d vr vt (r, t))) *
        carrier κ Φ (GraphCalculus.graph d vr vt (r, t)) := by
  have hm : DifferentiableAt ℝ (mode κ Φ a) (GraphCalculus.graph d vr vt (r, t)) :=
    ha.mul (differentiableAt_carrier κ hΦ)
  calc
    _ = along (GraphCalculus.radialVector d vr) (mode κ Φ a)
        (GraphCalculus.graph d vr vt (r, t)) :=
      (hm.hasFDerivAt.comp_hasDerivAt r
        (GraphCalculus.hasDerivAt_graph_radial d vr vt r t hr)).deriv
    _ = _ := along_mode _ κ hΦ ha

/-- The analogous actual graph pullback identity in its time direction. -/
theorem graph_deriv_time_mode (d : ℝ) (vr vt : GraphCalculus.Plane) (κ : ℝ)
    {Φ : GraphCalculus.Lift → ℝ} {a : GraphCalculus.Lift → ℂ} {r t : ℝ}
    (hΦ : DifferentiableAt ℝ Φ (GraphCalculus.graph d vr vt (r, t)))
    (ha : DifferentiableAt ℝ a (GraphCalculus.graph d vr vt (r, t))) :
    deriv (fun s => mode κ Φ a (GraphCalculus.graph d vr vt (r, s))) t =
      (along (fun _ => GraphCalculus.timeVector vt) a (GraphCalculus.graph d vr vt (r, t)) +
        phaseFactor κ * Complex.ofReal
          (along (fun _ => GraphCalculus.timeVector vt) Φ (GraphCalculus.graph d vr vt (r, t))) *
            a (GraphCalculus.graph d vr vt (r, t))) *
        carrier κ Φ (GraphCalculus.graph d vr vt (r, t)) := by
  have hm : DifferentiableAt ℝ (mode κ Φ a) (GraphCalculus.graph d vr vt (r, t)) :=
    ha.mul (differentiableAt_carrier κ hΦ)
  calc
    _ = along (fun _ => GraphCalculus.timeVector vt) (mode κ Φ a)
        (GraphCalculus.graph d vr vt (r, t)) :=
      (hm.hasFDerivAt.comp_hasDerivAt t
        (GraphCalculus.hasDerivAt_graph_time d vr vt r t)).deriv
    _ = _ := along_mode _ κ hΦ ha

end NavierStokes.HarmonicCalculus
