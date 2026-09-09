/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MovingFrameODE
public import LeanPool.NavierStokesAndEuler.NavierStokes.SmoothPathFamily
public import LeanPool.NavierStokesAndEuler.NavierStokes.WeightedODEJets
public import LeanPool.NavierStokesAndEuler.NavierStokes.PulseCovariance
public import LeanPool.NavierStokesAndEuler.NavierStokes.PhaseEstimates
public import LeanPool.NavierStokesAndEuler.NavierStokes.JointODE

@[expose] public section

/-!
# Constructed primary pulse solutions

The operator and forcing are defined from the actual moving tangent frame.
The solution is the finite-interval Volterra solution, with its differentiable
extension.  Reconstruction into ambient coordinates satisfies the projected
equation exactly.  Estimates are derived for this constructed solution.
-/

noncomputable section

namespace NavierStokes.PrimaryODE

open Set Filter
open scoped Topology ContDiff InnerProductSpace

abbrev State := MovingFrameODE.Plane
abbrev Space := MovingFrameODE.Space
abbrev Frame := MovingFrameODE.Frame

/-- Smooth input quantities before any solution is constructed.  `eigenvector`
is the scalar `h` in `x=p+q, y=h(p-q)`; its logarithmic derivative is
`eigenRate`.  `viscosity` is the fundamental scalar damping. -/
structure FrameData (Q : Type) where
  beta : Q × ℝ → ℝ
  betaDot : Q × ℝ → ℝ
  rho : Q × ℝ → ℝ
  rhoDot : Q × ℝ → ℝ
  rotation : Q × ℝ → ℝ
  F : Q × ℝ → ℝ
  shear : Q × ℝ → State
  frame : Q × ℝ → Frame
  eigenvalue : Q × ℝ → ℝ
  eigenvector : Q × ℝ → ℝ
  eigenRate : Q × ℝ → ℝ
  viscosity : Q × ℝ → ℝ

namespace FrameData

variable {Q : Type} (d : FrameData Q)

noncomputable def errorA (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff11 (d.rho z) (d.rhoDot z) ⟪d.frame z 0, d.shear z⟫_ℝ

noncomputable def errorB (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff12 (d.F z) (d.frame z 1 0) (d.rho z) (d.rotation z) -
    d.eigenvalue z / d.eigenvector z

noncomputable def errorC (z : Q × ℝ) : ℝ :=
  MovingFrameODE.coeff21 (d.F z) (d.frame z 1 0) ⟪d.frame z 1, d.shear z⟫_ℝ
    (d.rho z) (d.rotation z) - d.eigenvalue z * d.eigenvector z

noncomputable def error11 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal11 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error12 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal12 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error21 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal21 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def error22 (z : Q × ℝ) : ℝ :=
  MovingFrameODE.modal22 (d.errorA z) (d.errorB z) (d.errorC z)
    (d.eigenvector z) (d.eigenRate z)

noncomputable def damping (j : ℤ) (z : Q × ℝ) : ℝ := (j : ℝ) ^ 2 * d.viscosity z

noncomputable def coefficient (j : ℤ) (z : Q × ℝ) : State →L[ℝ] State :=
  GrowingMode.modalOperator (d.eigenvalue z) (d.damping j z)
    (d.error11 z) (d.error12 z) (d.error21 z) (d.error22 z)

noncomputable def forceX (f : Q × ℝ → Space) (z : Q × ℝ) : ℝ :=
  -(f z 0 - d.rho z * ⟪d.frame z 0, MovingFrameODE.tail (f z)⟫_ℝ) /
    (1 + d.rho z ^ 2)

noncomputable def forceY (f : Q × ℝ → Space) (z : Q × ℝ) : ℝ :=
  -⟪d.frame z 1, MovingFrameODE.tail (f z)⟫_ℝ

noncomputable def forcing (f : Q × ℝ → Space) (z : Q × ℝ) : State :=
  !₂[(d.forceX f z + d.forceY f z / d.eigenvector z) / 2,
    (d.forceX f z - d.forceY f z / d.eigenvector z) / 2]

noncomputable def ambient (z : Q × ℝ) (w : State) : Space :=
  MovingFrameODE.tangent (d.rho z) (d.frame z) (w 0 + w 1)
    (d.eigenvector z * (w 0 - w 1))

noncomputable def normal (z : Q × ℝ) : Space :=
  MovingFrameODE.normal (d.beta z) (d.rho z) (d.frame z)

noncomputable def normalMotion (z : Q × ℝ) : Space :=
  MovingFrameODE.normalMotion (d.beta z) (d.betaDot z) (d.rho z) (d.rhoDot z)
    (d.rotation z) (d.frame z)

@[simp] theorem forcing_zero (z : Q × ℝ) : d.forcing (fun _ => 0) z = 0 := by
  ext i
  have hz : MovingFrameODE.tail (0 : Space) = 0 := by ext i; fin_cases i <;> rfl
  fin_cases i <;> simp [forcing, forceX, forceY, hz]

@[simp] theorem forcing_zero_function : d.forcing (fun _ => 0) = (fun _ => 0) :=
  funext d.forcing_zero

@[simp] theorem damping_one (z : Q × ℝ) : d.damping 1 z = d.viscosity z := by
  simp [damping]

theorem ambient_tangent (z : Q × ℝ) (w : State) :
    ⟪d.normal z, d.ambient z w⟫_ℝ = 0 :=
  MovingFrameODE.normal_tangent _ _ _ _ _

/-- Actual derivatives of the supplied frame data, without assumptions about
any ODE solution. -/
structure Kinematics (p : Q) (I : Set ℝ) : Prop where
  beta_ne_zero : ∀ v ∈ I, d.beta (p, v) ≠ 0
  eigenvector_ne_zero : ∀ v ∈ I, d.eigenvector (p, v) ≠ 0
  beta_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.beta (p, t)) (d.betaDot (p, v)) v
  rho_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.rho (p, t)) (d.rhoDot (p, v)) v
  eigenvector_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.eigenvector (p, t))
      (d.eigenRate (p, v) * d.eigenvector (p, v)) v
  frameK_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.frame (p, t) 0)
      (d.rotation (p, v) • d.frame (p, v) 1) v
  frameN_deriv : ∀ v ∈ I,
    HasDerivAt (fun t => d.frame (p, t) 1)
      (-d.rotation (p, v) • d.frame (p, v) 0) v

end FrameData

section Construction

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}

/-- The differentiable extension of the actual Volterra solution. -/
noncomputable def extendedFamily (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) : ℝ → State :=
  ParametricODE.solutionExtension hab (SmoothPathFamily.pathFamily A p) (x₀ p)
    (SmoothPathFamily.pathFamily f p)

omit [NormedAddCommGroup Q] in
theorem extendedFamily_eq_path (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) (v : Icc a b) :
    extendedFamily hab A x₀ f p v = SmoothPathFamily.odeFamily hab A x₀ f p v :=
  ParametricODE.solutionExtension_coe _ _ _ _ _

omit [NormedAddCommGroup Q] in
theorem extendedFamily_initial (hab : a ≤ b)
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (p : Q) : extendedFamily hab A x₀ f p a = x₀ p := by
  exact (extendedFamily_eq_path hab A x₀ f p ⟨a, le_rfl, hab⟩).trans
    (SmoothPathFamily.odeFamily_initial _ _ _ _ _)

theorem extendedFamily_hasDerivAt (hab : a ≤ b) {U : Set Q}
    (A : Q × ℝ → State →L[ℝ] State) (x₀ : Q → State) (f : Q × ℝ → State)
    (hA : ContinuousOn A (U ×ˢ Icc a b)) (hf : ContinuousOn f (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (extendedFamily hab A x₀ f p)
      (A (p, v) (extendedFamily hab A x₀ f p v) + f (p, v)) v := by
  have hAc := SmoothPathFamily.slice_continuous hA hp
  have hfc := SmoothPathFamily.slice_continuous hf hp
  have hh := ParametricODE.solutionExtension_hasDerivAt hab
    (SmoothPathFamily.pathFamily A p) (x₀ p) (SmoothPathFamily.pathFamily f p) ⟨v, hv⟩
  unfold extendedFamily
  simpa only [SmoothPathFamily.pathFamily_apply A p hAc,
    SmoothPathFamily.pathFamily_apply f p hfc] using hh

noncomputable def solution (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) : ℝ → State :=
  extendedFamily hab (d.coefficient j) x₀ (d.forcing f) p

noncomputable def ambientSolution (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) (v : ℝ) : Space :=
  d.ambient (p, v) (solution hab d j x₀ f p v)

omit [NormedAddCommGroup Q] in
theorem solution_initial (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) :
    solution hab d j x₀ f p a = x₀ p :=
  extendedFamily_initial _ _ _ _ _

theorem solution_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (solution hab d j x₀ f p)
      (d.coefficient j (p, v) (solution hab d j x₀ f p v) + d.forcing f (p, v)) v :=
  extendedFamily_hasDerivAt _ _ _ _ hA hf hp hv

omit [NormedAddCommGroup Q] in
theorem ambientSolution_tangent (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) (p : Q) (v : ℝ) :
    ⟪d.normal (p, v), ambientSolution hab d j x₀ f p v⟫_ℝ = 0 :=
  d.ambient_tangent _ _

/-- Exact reconstruction into equation (27), including the projected physical
forcing and harmonic-dependent scalar viscosity. -/
theorem ambientSolution_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (j : ℤ)
    (x₀ : Q → State) (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (hk : d.Kinematics p (Icc a b)) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (ambientSolution hab d j x₀ f p)
      (TangentProjection.projectedRhs (d.normal (p, v)) (d.normalMotion (p, v))
        (ambientSolution hab d j x₀ f p v)
        (MovingFrameODE.baseAction (d.F (p, v)) (d.shear (p, v))
          (ambientSolution hab d j x₀ f p v))
        (f (p, v)) (d.damping j (p, v))) v := by
  let z := solution hab d j x₀ f p
  let z' := d.coefficient j (p, v) (z v) + d.forcing f (p, v)
  have hz : HasDerivAt z z' v := solution_hasDerivAt hab d j x₀ f hA hf hp hv
  have hplus := GrowingMode.hasDerivAt_coordinate hz 0
  have hminus := GrowingMode.hasDerivAt_coordinate hz 1
  have hx := hplus.fun_add hminus
  have hy := (hk.eigenvector_deriv v hv).fun_mul (hplus.fun_sub hminus)
  apply (MovingFrameODE.hasDerivAt_projected_iff (β' := d.betaDot (p, v))
    (hk.beta_ne_zero v hv) (hk.rho_deriv v hv) hx hy
    (hk.frameK_deriv v hv) (hk.frameN_deriv v hv)).mpr
  have hm := (MovingFrameODE.modal_equations_iff (hk.eigenvector_ne_zero v hv)
    (z v 0) (z v 1) (z' 0) (z' 1) (d.eigenvalue (p, v)) (d.damping j (p, v))
    (d.errorA (p, v)) (d.errorB (p, v)) (d.errorC (p, v)) (d.eigenRate (p, v))
    (d.forceX f (p, v)) (d.forceY f (p, v))).mpr
      ⟨by rfl, by rfl⟩
  constructor
  · convert! hm.1 using 1
    simp only [FrameData.errorA, FrameData.errorB, FrameData.forceX, MovingFrameODE.rhsX]
    ring
  · convert! hm.2 using 1
    simp only [FrameData.errorC, FrameData.forceY, MovingFrameODE.rhsY]
    ring

end Construction

section Smooth

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Smoothness of the explicit input fields.  Frame smoothness means smoothness
of each ambient basis vector, avoiding an arbitrary manifold structure on
the space of orthonormal bases. -/
structure FrameData.SmoothOn (d : FrameData Q) (Ω : Set (Q × ℝ)) : Prop where
  beta : ContDiffOn ℝ ∞ d.beta Ω
  betaDot : ContDiffOn ℝ ∞ d.betaDot Ω
  rho : ContDiffOn ℝ ∞ d.rho Ω
  rhoDot : ContDiffOn ℝ ∞ d.rhoDot Ω
  rotation : ContDiffOn ℝ ∞ d.rotation Ω
  F : ContDiffOn ℝ ∞ d.F Ω
  shear : ContDiffOn ℝ ∞ d.shear Ω
  frame : ∀ i, ContDiffOn ℝ ∞ (fun z => d.frame z i) Ω
  eigenvalue : ContDiffOn ℝ ∞ d.eigenvalue Ω
  eigenvector : ContDiffOn ℝ ∞ d.eigenvector Ω
  eigenRate : ContDiffOn ℝ ∞ d.eigenRate Ω
  viscosity : ContDiffOn ℝ ∞ d.viscosity Ω
  eigenvector_ne_zero : ∀ z ∈ Ω, d.eigenvector z ≠ 0

theorem FrameData.SmoothOn.errorA {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorA Ω := by
  exact (h.rho.mul (((h.frame 0).inner ℝ h.shear).sub h.rhoDot)).div
    (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity)

theorem FrameData.SmoothOn.errorB {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorB Ω := by
  have hn : ContDiffOn ℝ ∞ (fun z => d.frame z 1 0) Ω :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn (h.frame 1)
  exact (((contDiffOn_const.mul h.F).mul hn).sub (h.rho.mul h.rotation)).div
    (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity) |>.sub
      (h.eigenvalue.div h.eigenvector h.eigenvector_ne_zero)

theorem FrameData.SmoothOn.errorC {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) : ContDiffOn ℝ ∞ d.errorC Ω := by
  have hn : ContDiffOn ℝ ∞ (fun z => d.frame z 1 0) Ω :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn (h.frame 1)
  exact ((((contDiffOn_const.mul h.F).mul hn).add ((h.frame 1).inner ℝ h.shear)).neg.add
    (h.rho.mul h.rotation)).sub (h.eigenvalue.mul h.eigenvector)

theorem FrameData.SmoothOn.modal_errors {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) :
    ContDiffOn ℝ ∞ d.error11 Ω ∧ ContDiffOn ℝ ∞ d.error12 Ω ∧
      ContDiffOn ℝ ∞ d.error21 Ω ∧ ContDiffOn ℝ ∞ d.error22 Ω := by
  have hb := h.eigenvector.mul h.errorB
  have hc := h.errorC.div h.eigenvector h.eigenvector_ne_zero
  exact ⟨(((h.errorA.add hb).add hc).sub h.eigenRate).div_const 2,
    (((h.errorA.sub hb).add hc).add h.eigenRate).div_const 2,
    (((h.errorA.add hb).sub hc).add h.eigenRate).div_const 2,
    (((h.errorA.sub hb).sub hc).sub h.eigenRate).div_const 2⟩

private theorem modalOperator_expansion (lam damping e11 e12 e21 e22 : ℝ) :
    GrowingMode.modalOperator lam damping e11 e12 e21 e22 =
      (lam - damping + e11) • GrowingMode.modalOperator 0 0 1 0 0 0 +
      e12 • GrowingMode.modalOperator 0 0 0 1 0 0 +
      e21 • GrowingMode.modalOperator 0 0 0 0 1 0 +
      (-lam - damping + e22) • GrowingMode.modalOperator 0 0 0 0 0 1 := by
  ext z i
  fin_cases i <;> simp [GrowingMode.modalOperator]

theorem FrameData.SmoothOn.coefficient {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) (j : ℤ) : ContDiffOn ℝ ∞ (d.coefficient j) Ω := by
  rcases h.modal_errors with ⟨h11, h12, h21, h22⟩
  have hd : ContDiffOn ℝ ∞ (d.damping j) Ω := contDiffOn_const.mul h.viscosity
  have hh := ((((h.eigenvalue.sub hd).add h11).smul
    (contDiffOn_const (c := GrowingMode.modalOperator 0 0 1 0 0 0))).add
    (h12.smul (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 1 0 0))) |>.add
      (h21.smul (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 0 1 0)))).add
        (((h.eigenvalue.neg.sub hd).add h22).smul
          (contDiffOn_const (c := GrowingMode.modalOperator 0 0 0 0 0 1)))
  apply hh.congr
  intro z _
  exact modalOperator_expansion _ _ _ _ _ _

theorem FrameData.SmoothOn.forcing {d : FrameData Q} {Ω : Set (Q × ℝ)}
    (h : d.SmoothOn Ω) {f : Q × ℝ → Space} (hf : ContDiffOn ℝ ∞ f Ω) :
    ContDiffOn ℝ ∞ (d.forcing f) Ω := by
  have ht := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    MovingFrameODE.tailCLM).comp_contDiffOn hf
  have hr := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 0)).comp_contDiffOn hf
  have hx : ContDiffOn ℝ ∞ (d.forceX f) Ω :=
    (hr.sub (h.rho.mul ((h.frame 0).inner ℝ ht))).neg.div
      (contDiffOn_const.add (h.rho.pow 2)) (fun z _ => by positivity)
  have hy : ContDiffOn ℝ ∞ (d.forceY f) Ω := ((h.frame 1).inner ℝ ht).neg
  have hdiv := hy.div h.eigenvector h.eigenvector_ne_zero
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) MovingFrameODE.pairCLM).comp_contDiffOn
    (((hx.add hdiv).div_const 2).prodMk ((hx.sub hdiv).div_const 2))

/-- Jointly smooth physical/frame inputs give an actually constructed smooth
family of modal paths. -/
theorem solutionPath_contDiffOn {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (j : ℤ) (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (SmoothPathFamily.odeFamily hab (d.coefficient j) x₀ (d.forcing f)) U :=
  SmoothPathFamily.contDiffOn_odeFamily_of_joint hab U V hU hV hI
    (d.coefficient j) x₀ (d.forcing f) (hd.coefficient j) hx₀ (hd.forcing hf)

end Smooth

/-- Geometric perturbations of the actual frame produce the four modal error
bounds.  The two reference identities are the chosen eigenpair equations. -/
theorem FrameData.modal_errors_of_geometry {Q : Type} (d : FrameData Q) (z : Q × ℝ)
    (B₀ : Frame) (g₀ : State) {F₀ s M η H κ : ℝ}
    (hM : 1 ≤ M) (hη : 0 ≤ η) (hH : 0 ≤ H)
    (hρ : |d.rho z| ≤ M) (hs : |s| ≤ M) (hF₀ : |F₀| ≤ M) (hg₀ : ‖g₀‖ ≤ M)
    (horth : ⟪B₀ 0, g₀⟫_ℝ = 0)
    (hF : |d.F z - F₀| ≤ η) (hg : ‖d.shear z - g₀‖ ≤ η)
    (hK : ‖d.frame z 0 - B₀ 0‖ ≤ η) (hN : ‖d.frame z 1 - B₀ 1‖ ≤ η)
    (hρd : |d.rho z - s| ≤ η) (hρ' : |d.rhoDot z| ≤ η) (hrot : |d.rotation z| ≤ η)
    (hpair₁ : d.eigenvalue z / d.eigenvector z = 2 * F₀ * (B₀ 1 0) / (1 + s ^ 2))
    (hpair₂ : d.eigenvalue z * d.eigenvector z = -(2 * F₀ * (B₀ 1 0) + ⟪B₀ 1, g₀⟫_ℝ))
    (hh : |d.eigenvector z| ≤ H) (hhi : |1 / d.eigenvector z| ≤ H)
    (hrate : |d.eigenRate z| ≤ κ) :
    |d.error11 z| ≤ (1 + 2 * H) * ((16 * M ^ 2 * (1 + M)) * η) + κ ∧
    |d.error12 z| ≤ (1 + 2 * H) * ((16 * M ^ 2 * (1 + M)) * η) + κ ∧
    |d.error21 z| ≤ (1 + 2 * H) * ((16 * M ^ 2 * (1 + M)) * η) + κ ∧
    |d.error22 z| ≤ (1 + 2 * H) * ((16 * M ^ 2 * (1 + M)) * η) + κ := by
  obtain ⟨ha, hb, hc⟩ := MovingFrameODE.frame_coefficients_close
    hM hη hρ hs hF₀ hg₀ horth hF hg hK hN hρd hρ' hrot
  have hb' : |d.errorB z| ≤ (16 * M ^ 2 * (1 + M)) * η := by
    simpa only [FrameData.errorB, hpair₁] using hb
  have hc' : |d.errorC z| ≤ (16 * M ^ 2 * (1 + M)) * η := by
    simpa only [FrameData.errorC, hpair₂] using hc
  exact MovingFrameODE.modal_errors_le hH ha hb' hc' hh hhi hrate

/-- Scalar viscosity keeps the same sign at every nonzero integer harmonic.
The modal energy estimate is derived from entrywise coefficient errors. -/
theorem FrameData.energy_bound {Q : Type} (d : FrameData Q) (z : Q × ℝ)
    {j : ℤ} (hj : j ≠ 0) {referenceDamping C D S : ℝ}
    (hlam : 0 ≤ d.eigenvalue z) (hν : 0 ≤ d.viscosity z)
    (hνerr : referenceDamping - D / S ≤ d.viscosity z)
    (herr : |d.error11 z| ≤ C / S ∧ |d.error12 z| ≤ C / S ∧
      |d.error21 z| ≤ C / S ∧ |d.error22 z| ≤ C / S) (w : State) :
    ⟪w, d.coefficient j z w⟫_ℝ ≤
      (d.eigenvalue z - referenceDamping + (D + 4 * C) / S) * ‖w‖ ^ 2 := by
  have hd := ViscousPropagator.high_harmonic_damping hj hν hνerr
  have he := MovingFrameODE.modal_energy_le hlam (d.damping j z)
    herr.1 herr.2.1 herr.2.2.1 herr.2.2.2 w
  apply he.trans
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  change _ - (j : ℝ) ^ 2 * d.viscosity z + _ ≤ _
  rw [show (D + 4 * C) / S = D / S + 4 * (C / S) by ring]
  linarith

section Primary

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}

noncomputable def primarySeed (a : ℝ) (P : Q × ℝ → ℝ) (p : Q) : State := !₂[P (p, a), 0]

noncomputable def primary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ) (p : Q) : ℝ → State :=
  solution hab d 1 (primarySeed a P) (fun _ => 0) p

noncomputable def radialPrimary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    (p : Q) (v : ℝ) : ℝ := primary hab d P p v 0 + primary hab d P p v 1

noncomputable def transversePrimary (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    (p : Q) (v : ℝ) : ℝ :=
  d.eigenvector (p, v) * (primary hab d P p v 0 - primary hab d P p v 1)

omit [NormedAddCommGroup Q] in
theorem primary_initial (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ) (p : Q) :
    primary hab d P p a = !₂[P (p, a), 0] := solution_initial _ _ _ _ _ _

theorem primary_hasDerivAt (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    {U : Set Q} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {v : ℝ} (hv : v ∈ Icc a b) :
    HasDerivAt (primary hab d P p)
      (d.coefficient 1 (p, v) (primary hab d P p v)) v := by
  have hf : ContinuousOn (d.forcing (fun _ => 0)) (U ×ˢ Icc a b) := by
    simpa only [FrameData.forcing_zero_function] using
      (continuousOn_const : ContinuousOn (fun _ : Q × ℝ => (0 : State)) (U ×ˢ Icc a b))
  unfold primary
  simpa only [FrameData.forcing_zero, add_zero] using
    solution_hasDerivAt hab d 1 (primarySeed a P) (fun _ => 0) hA hf hp hv

/-- The actual constructed real primary has positive radial component,
two-sided reference-envelope comparison, and a small eigenvector ratio error.
Only coefficient estimates and the scalar reference equation are inputs. -/
theorem primary_bounds (hab : a ≤ b) (d : FrameData Q) (P : Q × ℝ → ℝ)
    {U : Set Q} (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) {S C D L lammin : ℝ}
    (hlammin : 0 < lammin) (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * GrowingMode.coneConstant lammin C ≤ S) (hslot : b - a ≤ L * S)
    (referenceDamping : ℝ → ℝ)
    (hlam : ∀ v ∈ Icc a b, lammin ≤ d.eigenvalue (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hν : ∀ v ∈ Icc a b, |d.viscosity (p, v) - referenceDamping v| ≤ D / S)
    (hPpos : ∀ v ∈ Icc a b, 0 < P (p, v))
    (hP : ∀ v ∈ Icc a b, HasDerivAt (fun t => P (p, t))
      ((d.eigenvalue (p, v) - referenceDamping v) * P (p, v)) v) :
    ∀ v ∈ Icc a b,
      0 < radialPrimary hab d P p v ∧
      (Real.exp (-(D + 2 * C) * L) / 2) * P (p, v) ≤ radialPrimary hab d P p v ∧
      radialPrimary hab d P p v ≤ (3 * Real.exp ((D + 2 * C) * L) / 2) * P (p, v) ∧
      |transversePrimary hab d P p v / radialPrimary hab d P p v - d.eigenvector (p, v)| ≤
        4 * |d.eigenvector (p, v)| * (GrowingMode.coneConstant lammin C / S) := by
  have hAslice : ContinuousOn (fun v => d.coefficient 1 (p, v)) (Icc a b) :=
    hA.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨hp, hv⟩)
  have hAi : ContinuousOn (fun v => GrowingMode.modalOperator (d.eigenvalue (p, v))
      (d.viscosity (p, v)) (d.error11 (p, v)) (d.error12 (p, v))
      (d.error21 (p, v)) (d.error22 (p, v))) (Icc a b) := by
    simpa only [FrameData.coefficient, FrameData.damping_one] using hAslice
  have hode (v : ℝ) (hv : v ∈ Icc a b) := primary_hasDerivAt hab d P hA hp hv
  simp only [FrameData.coefficient, FrameData.damping_one] at hode
  have hplus : 0 < primary hab d P p a 0 := by
    rw [primary_initial]
    exact hPpos a ⟨le_rfl, hab⟩
  have hminus : primary hab d P p a 1 = 0 := by rw [primary_initial]; rfl
  have hm := GrowingMode.scaled_growing_mode_bounds hab hlammin hC hD hS hlarge hslot
    (fun v => d.eigenvalue (p, v)) (fun v => d.viscosity (p, v)) referenceDamping
    (fun v => d.error11 (p, v)) (fun v => d.error12 (p, v))
    (fun v => d.error21 (p, v)) (fun v => d.error22 (p, v))
    (fun v => P (p, v)) hAi hode hlam herr hν hPpos hP hplus hminus
  have hratio : primary hab d P p a 0 / P (p, a) = 1 := by
    rw [primary_initial]
    exact div_self (hPpos a ⟨le_rfl, hab⟩).ne'
  simp only [hratio, mul_one] at hm
  obtain ⟨hr, hrhalf, _⟩ := GrowingMode.scaled_cone_conditions hlammin hC hS hlarge
  intro v hv
  obtain ⟨hzpos, hzcone, hzlo, hzhi⟩ := hm v hv
  obtain ⟨hxlo, hxhi, hxratio⟩ := GrowingMode.original_coordinate_bounds
    (h := d.eigenvector (p, v)) hzpos hr.le hrhalf hzcone
  refine ⟨?_, ?_, ?_, hxratio⟩
  · change 0 < primary hab d P p v 0 + primary hab d P p v 1
    linarith
  · change _ ≤ primary hab d P p v 0 + primary hab d P p v 1
    nlinarith
  · change primary hab d P p v 0 + primary hab d P p v 1 ≤ _
    nlinarith

end Primary

section Forward

variable {Q : Type} [NormedAddCommGroup Q]
variable {a b : ℝ}

theorem solution_forward_bound (hab : a ≤ b) (d : FrameData Q) {j : ℤ} (hj : j ≠ 0)
    (x₀ : Q → State) (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (referenceDamping rate P : ℝ → ℝ)
    {S C D : ℝ} (hS : 0 < S) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPpos : ∀ v, 0 < P v) (hP : ∀ v, HasDerivAt P (rate v * P v) v)
    (hreference : ∀ v ∈ Icc a b, rate v = d.eigenvalue (p, v) - referenceDamping v)
    (hlam : ∀ v ∈ Icc a b, 0 ≤ d.eigenvalue (p, v))
    (hν : ∀ v ∈ Icc a b, 0 ≤ d.viscosity (p, v))
    (hνerr : ∀ v ∈ Icc a b, referenceDamping v - D / S ≤ d.viscosity (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S) :
    ∀ v ∈ Icc a b, ‖solution hab d j x₀ f p v‖ ≤
      Real.exp (((D + 4 * C) / S) * (v - a)) * P v *
        (‖x₀ p‖ / P a + ∫ s in a..v, ‖d.forcing f (p, s)‖ / P s) := by
  have hode (v : ℝ) (hv : v ∈ Icc a b) := solution_hasDerivAt hab d j x₀ f hA hf hp hv
  have hu : ContinuousOn (solution hab d j x₀ f p) (Icc a b) :=
    fun v hv => (hode v hv).continuousAt.continuousWithinAt
  have hforce : ContinuousOn (fun v => d.forcing f (p, v)) (Icc a b) :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨hp, hv⟩)
  have he (v : ℝ) (hv : v ∈ Ico a b) (w : State) :
      ⟪w, d.coefficient j (p, v) w⟫_ℝ ≤ (rate v + (D + 4 * C) / S) * ‖w‖ ^ 2 := by
    have hv' := Ico_subset_Icc_self hv
    rw [hreference v hv']
    exact d.energy_bound (p, v) hj (hlam v hv') (hν v hv') (hνerr v hv') (herr v hv') w
  have hbnd := ViscousPropagator.norm_le_envelope_mul_integral_on
    (fun v => d.coefficient j (p, v)) rate P (div_nonneg (by positivity) hS.le)
    hPpos hP hu hforce (fun v hv => (hode v (Ico_subset_Icc_self hv)).hasDerivWithinAt) he
  simpa only [solution_initial] using hbnd

/-- The same forward propagator constant applies to every nonzero harmonic.
The start of the finite interval may be any earlier slot time. -/
theorem homogeneous_forward_bound (hab : a ≤ b) (d : FrameData Q) {j : ℤ} (hj : j ≠ 0)
    (x₀ : Q → State) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (referenceDamping rate P : ℝ → ℝ)
    {S C D L : ℝ} (hS : 0 < S) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hslot : b - a ≤ L * S)
    (hPpos : ∀ v, 0 < P v) (hP : ∀ v, HasDerivAt P (rate v * P v) v)
    (hreference : ∀ v ∈ Icc a b, rate v = d.eigenvalue (p, v) - referenceDamping v)
    (hlam : ∀ v ∈ Icc a b, 0 ≤ d.eigenvalue (p, v))
    (hν : ∀ v ∈ Icc a b, 0 ≤ d.viscosity (p, v))
    (hνerr : ∀ v ∈ Icc a b, referenceDamping v - D / S ≤ d.viscosity (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S) :
    ∀ v ∈ Icc a b, ‖solution hab d j x₀ (fun _ => 0) p v‖ ≤
      Real.exp ((D + 4 * C) * L) * (P v / P a) * ‖x₀ p‖ := by
  have hf : ContinuousOn (d.forcing (fun _ => 0)) (U ×ˢ Icc a b) := by
    rw [FrameData.forcing_zero_function]
    exact continuousOn_const
  have hbnd := solution_forward_bound hab d hj x₀ (fun _ => 0) hA hf hp referenceDamping rate P
    hS hC hD hPpos hP hreference hlam hν hνerr herr
  simp only [FrameData.forcing_zero, norm_zero, zero_div, intervalIntegral.integral_zero, add_zero]
    at hbnd
  intro v hv
  have hexp : Real.exp (((D + 4 * C) / S) * (v - a)) ≤ Real.exp ((D + 4 * C) * L) := by
    apply Real.exp_le_exp.mpr
    have hfactor : ((D + 4 * C) / S) * (L * S) = (D + 4 * C) * L := by
      field_simp
    rw [← hfactor]
    exact mul_le_mul_of_nonneg_left ((sub_le_sub_right hv.2 a).trans hslot)
      (div_nonneg (by positivity) hS.le)
  calc
    _ ≤ Real.exp (((D + 4 * C) / S) * (v - a)) * P v * (‖x₀ p‖ / P a) := hbnd v hv
    _ ≤ Real.exp ((D + 4 * C) * L) * P v * (‖x₀ p‖ / P a) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hexp (hPpos v).le)
        (div_nonneg (norm_nonneg _) (hPpos a).le)
    _ = _ := by ring

/-- Zero-initial source solves are constructed by the same operator, and retain
every prescribed small amplitude factor in the source bound. -/
theorem zero_initial_source_bound (hab : a ≤ b) (d : FrameData Q) {j : ℤ} (hj : j ≠ 0)
    (f : Q × ℝ → Space) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    (hf : ContinuousOn (d.forcing f) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (referenceDamping rate P : ℝ → ℝ)
    {S C D K : ℝ} (hS : 0 < S) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hPpos : ∀ v, 0 < P v) (hP : ∀ v, HasDerivAt P (rate v * P v) v)
    (hreference : ∀ v ∈ Icc a b, rate v = d.eigenvalue (p, v) - referenceDamping v)
    (hlam : ∀ v ∈ Icc a b, 0 ≤ d.eigenvalue (p, v))
    (hν : ∀ v ∈ Icc a b, 0 ≤ d.viscosity (p, v))
    (hνerr : ∀ v ∈ Icc a b, referenceDamping v - D / S ≤ d.viscosity (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hsource : ∀ v ∈ Icc a b, ‖d.forcing f (p, v)‖ ≤ K * P v) :
    ∀ v ∈ Icc a b, ‖solution hab d j (fun _ => 0) f p v‖ ≤
      Real.exp (((D + 4 * C) / S) * (v - a)) * P v * (K * (v - a)) := by
  have hode (v : ℝ) (hv : v ∈ Icc a b) := solution_hasDerivAt hab d j (fun _ => 0) f hA hf hp hv
  apply ViscousPropagator.zero_initial_source_bound (fun v => d.coefficient j (p, v)) rate P
    (div_nonneg (by positivity) hS.le) hPpos hP
    (fun v hv => (hode v hv).continuousAt.continuousWithinAt)
    (hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun v hv => ⟨hp, hv⟩))
    (fun v hv => (hode v (Ico_subset_Icc_self hv)).hasDerivWithinAt)
    _ (solution_initial hab d j (fun _ => 0) f p) hsource
  intro v hv w
  have hv' := Ico_subset_Icc_self hv
  rw [hreference v hv']
  exact d.energy_bound (p, v) hj (hlam v hv') (hν v hv') (hνerr v hv') (herr v hv') w

end Forward

section PhaseFrame

variable {Q : Type}

/-- Build the actual frame from a supplied phase covector.  All frame rates
are computed from its supplied derivative; viscosity is the physical scalar
multiple of the squared phase norm. -/
noncomputable def FrameData.ofNormal (n nDot : Q × ℝ → Space)
    (hne : ∀ z, MovingFrameODE.tail (n z) ≠ 0)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) : FrameData Q where
  beta z := MovingFrameODE.normalScale (n z)
  betaDot z := PhaseEstimates.scaleDerivative (n z) (nDot z)
  rho z := MovingFrameODE.radialSlope (n z)
  rhoDot z := PhaseEstimates.slopeDerivative (n z) (nDot z)
  rotation z := PhaseEstimates.angularVelocity (n z) (nDot z)
  F := F
  shear := g
  frame z := MovingFrameODE.normalFrame (n z) (hne z)
  eigenvalue := lam
  eigenvector := h
  eigenRate := hRate
  viscosity z := viscosityScale z * ‖n z‖ ^ 2

theorem FrameData.ofNormal_normal (n nDot : Q × ℝ → Space)
    (hne : ∀ z, MovingFrameODE.tail (n z) ≠ 0)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) (z : Q × ℝ) :
    (FrameData.ofNormal n nDot hne F g lam h hRate viscosityScale).normal z = n z :=
  MovingFrameODE.normal_reconstructed (hne z)

theorem FrameData.ofNormal_kinematics (n nDot : Q × ℝ → Space)
    (hne : ∀ z, MovingFrameODE.tail (n z) ≠ 0)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) (p : Q) (I : Set ℝ)
    (hn : ∀ v ∈ I, HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v)
    (hh : ∀ v ∈ I, h (p, v) ≠ 0)
    (hdh : ∀ v ∈ I, HasDerivAt (fun t => h (p, t)) (hRate (p, v) * h (p, v)) v) :
    (FrameData.ofNormal n nDot hne F g lam h hRate viscosityScale).Kinematics p I := by
  refine ⟨fun v _ => (MovingFrameODE.normalScale_pos (hne (p, v))).ne', hh,
    ?_, ?_, hdh, ?_, ?_⟩
  · intro v hv
    exact PhaseEstimates.hasDerivAt_normalScale (hn v hv) (hne (p, v))
  · intro v hv
    exact PhaseEstimates.hasDerivAt_radialSlope (hn v hv) (hne (p, v))
  · intro v hv
    simpa only [FrameData.ofNormal, MovingFrameODE.normalFrame_zero,
      MovingFrameODE.normalFrame_one] using
        (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne (p, v))).1
  · intro v hv
    simpa only [FrameData.ofNormal, MovingFrameODE.normalFrame_zero,
      MovingFrameODE.normalFrame_one] using
        (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne (p, v))).2

theorem FrameData.Kinematics.normal_hasDerivAt {d : FrameData Q} {p : Q} {I : Set ℝ}
    (hk : d.Kinematics p I) {v : ℝ} (hv : v ∈ I) :
    HasDerivAt (fun t => d.normal (p, t)) (d.normalMotion (p, v)) v :=
  MovingFrameODE.hasDerivAt_normal (hk.beta_deriv v hv) (hk.rho_deriv v hv) (hk.frameK_deriv v hv)

theorem FrameData.ofNormal_normalMotion (n nDot : Q × ℝ → Space)
    (hne : ∀ z, MovingFrameODE.tail (n z) ≠ 0)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) {p : Q} {v : ℝ}
    (hn : HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v) :
    (FrameData.ofNormal n nDot hne F g lam h hRate viscosityScale).normalMotion (p, v) = nDot (p,
      v) := by
  have hbeta := PhaseEstimates.hasDerivAt_normalScale hn (hne (p, v))
  have hrho := PhaseEstimates.hasDerivAt_radialSlope hn (hne (p, v))
  have hK : HasDerivAt (fun t => MovingFrameODE.normalFrame (n (p, t)) (hne (p, t)) 0)
      (PhaseEstimates.angularVelocity (n (p, v)) (nDot (p, v)) •
        MovingFrameODE.normalFrame (n (p, v)) (hne (p, v)) 1) v := by
    simpa only [MovingFrameODE.normalFrame_zero, MovingFrameODE.normalFrame_one] using
      (PhaseEstimates.hasDerivAt_actual_frame hn (hne (p, v))).1
  have hd := MovingFrameODE.hasDerivAt_normal hbeta hrho hK
  have heq : (fun t => MovingFrameODE.normal (MovingFrameODE.normalScale (n (p, t)))
      (MovingFrameODE.radialSlope (n (p, t))) (MovingFrameODE.normalFrame (n (p, t)) (hne (p, t))))
        =
      (fun t => n (p, t)) := by
    funext t
    exact MovingFrameODE.normal_reconstructed (hne (p, t))
  rw [heq] at hd
  exact hd.unique hn

end PhaseFrame

section ParameterJets

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Full ordinary Fréchet jets of the same constructed solution.  All numerical
jet assumptions concern explicitly defined coefficients, initial data and
forcing; the output jet bound is derived by the triangular variational ODE. -/
theorem norm_iteratedFDeriv_solution_le_polynomial {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) {j : ℤ} (hj : j ≠ 0)
    (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V))
    {p : Q} (hp : p ∈ U) (referenceDamping rate W : ℝ → ℝ)
    {S C D K w : ℝ} (hS : 1 ≤ S) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hK : 1 ≤ K) (hw : 0 ≤ w)
    (hW : ∀ v, 0 < W v) (hdW : ∀ v, HasDerivAt W (rate v * W v) v)
    (hreference : ∀ v ∈ Icc a b, rate v = d.eigenvalue (p, v) - referenceDamping v)
    (hlam : ∀ v ∈ Icc a b, 0 ≤ d.eigenvalue (p, v))
    (hν : ∀ v ∈ Icc a b, 0 ≤ d.viscosity (p, v))
    (hνerr : ∀ v ∈ Icc a b, referenceDamping v - D / S ≤ d.viscosity (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hExp : Real.exp (((D + 4 * C) / S) * (b - a)) ≤ K) (hslot : b - a ≤ K * S)
    (m N : ℕ)
    (hAj : ∀ k : ℕ, k ≤ N → ∀ v : Icc a b,
      ‖iteratedFDeriv ℝ k (fun q => d.coefficient j (q, v)) p‖ ≤ K * S ^ m)
    (hxj : ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k x₀ p‖ ≤ w * K * S ^ m * W a)
    (hfj : ∀ k : ℕ, k ≤ N → ∀ v : Icc a b,
      ‖iteratedFDeriv ℝ k (fun q => d.forcing f (q, v)) p‖ ≤ w * K * S ^ m * W v)
    (n : ℕ) (hn : n ≤ N) (v : Icc a b) :
    ‖iteratedFDeriv ℝ n (fun q => solution hab d j x₀ f q v) p‖ ≤
      w * ((2 : ℝ) ^ (N + 1) * K ^ 3) ^ (n + 1) * S ^ ((m + 1) * (n + 1)) * W v := by
  have heq : (fun q => solution hab d j x₀ f q v) =
      (fun q => SmoothPathFamily.odeFamily hab (d.coefficient j) x₀ (d.forcing f) q v) := by
    funext q
    exact extendedFamily_eq_path _ _ _ _ _ _
  rw [heq]
  apply WeightedODEJets.norm_iteratedFDeriv_odeFamily_le_polynomial hab U V hU hV hI
    (d.coefficient j) x₀ (d.forcing f) (hd.coefficient j) hx₀ (hd.forcing hf) hp
    rate W (div_nonneg (by positivity) (zero_le_one.trans hS)) hW hdW
    _ hExp hS hK hw hslot m N hAj hxj hfj n hn v
  intro t z
  rw [hreference t t.2]
  exact d.energy_bound (p, t) hj (hlam t t.2) (hν t t.2) (hνerr t t.2) (herr t t.2) z

end ParameterJets

noncomputable def referenceProfile (c₀ u ell v : ℝ) : ℝ :=
  c₀ * Real.sqrt (1 + PulseGrowth.slotMagnitude u ell v ^ 2)

noncomputable def referenceProfileRate (u ell v : ℝ) : ℝ :=
  PulseGrowth.slotMagnitude u ell v * (u / ell) /
    (1 + PulseGrowth.slotMagnitude u ell v ^ 2)

theorem hasDerivAt_referenceProfile (c₀ u ell v : ℝ) :
    HasDerivAt (referenceProfile c₀ u ell)
      (referenceProfileRate u ell v * referenceProfile c₀ u ell v) v := by
  have hs : HasDerivAt (PulseGrowth.slotMagnitude u ell) (u / ell) v := by
    unfold PulseGrowth.slotMagnitude
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id v).const_mul u).div_const ell).const_add (u / 2)
  have hr := ((hs.fun_pow 2).const_add 1).sqrt (by positivity)
  convert! hr.const_mul c₀ using 1
  unfold referenceProfileRate referenceProfile
  have hp := PulseGrowth.radius_pos (PulseGrowth.slotMagnitude u ell v)
  have hsq := Real.sq_sqrt (PulseGrowth.one_add_sq_pos (PulseGrowth.slotMagnitude u ell v)).le
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
  generalize u / ell = q
  field_simp [hp.ne', (PulseGrowth.one_add_sq_pos (PulseGrowth.slotMagnitude u ell v)).ne']
  nlinarith only [congrArg (fun z : ℝ => c₀ * PulseGrowth.slotMagnitude u ell v * q * z) hsq]

theorem referenceProfile_ne_zero {c₀ : ℝ} (hc₀ : c₀ ≠ 0) (u ell v : ℝ) :
    referenceProfile c₀ u ell v ≠ 0 :=
  mul_ne_zero hc₀ (PulseGrowth.radius_pos _).ne'

theorem referenceEigenvalue_lower {lam u ell v : ℝ} (hlam : 0 < lam) (hu : 0 ≤ u)
    (hell : 0 < ell) (hv : v ∈ Icc 0 ell) :
    lam / Real.sqrt (1 + (3 * u / 2) ^ 2) ≤ ViscousPropagator.referenceEigenvalue lam u ell v := by
  have hs := GaussianEnvelope.slotMagnitude_mem_interval hu hell hv
  have hs0 := PulseGrowth.slotMagnitude_nonneg hu hell hv.1
  apply div_le_div_of_nonneg_left hlam.le (PulseGrowth.radius_pos _)
  apply Real.sqrt_le_sqrt
  nlinarith [hs.2]

noncomputable def referenceEnvelope {Q : Type} (lam u : Q → ℝ) (ell : ℝ) (z : Q × ℝ) : ℝ :=
  GaussianEnvelope.envelope (GaussianEnvelope.referenceRate (lam z.1) (u z.1) ell)
    (ell / 2) z.2

section GaussianPrimary

variable {Q : Type} [NormedAddCommGroup Q]

/-- The actual primary is bounded above and below by the manuscript's Gaussian
envelopes.  The reference scalar equation and spectral gap are derived here
from the displayed reference rate; they are not assumptions about a solution. -/
theorem primary_gaussian_bounds {ell : ℝ} (hell : 0 < ell) (d : FrameData Q)
    (lam u c₀ : Q → ℝ) {U : Set Q}
    (hA : ContinuousOn (d.coefficient 1) (U ×ˢ Icc 0 ell))
    {p : Q} (hp : p ∈ U) (hlam : 0 < lam p) (hu : 0 < u p)
    {S C D L : ℝ} (hC : 0 ≤ C) (hD : 0 ≤ D) (hS : 0 < S)
    (hlarge : 2 * GrowingMode.coneConstant
      (lam p / Real.sqrt (1 + (3 * u p / 2) ^ 2)) C ≤ S)
    (hslot : ell ≤ L * S)
    (heigen : ∀ v ∈ Icc 0 ell,
      d.eigenvalue (p, v) = ViscousPropagator.referenceEigenvalue (lam p) (u p) ell v)
    (hprofile : ∀ v ∈ Icc 0 ell, d.eigenvector (p, v) = referenceProfile (c₀ p) (u p) ell v)
    (herr : ∀ v ∈ Icc 0 ell,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hν : ∀ v ∈ Icc 0 ell,
      |d.viscosity (p, v) - ViscousPropagator.referenceViscosity (lam p) (u p) ell v| ≤ D / S) :
    ∃ b B : ℝ, 0 < b ∧ 0 < B ∧ ∀ v ∈ Icc 0 ell,
      0 < radialPrimary hell.le d (referenceEnvelope lam u ell) p v ∧
      (Real.exp (-(D + 2 * C) * L) / 2) * Real.exp (-B * (v - ell / 2) ^ 2 / ell) ≤
        radialPrimary hell.le d (referenceEnvelope lam u ell) p v ∧
      radialPrimary hell.le d (referenceEnvelope lam u ell) p v ≤
        (3 * Real.exp ((D + 2 * C) * L) / 2) * Real.exp (-b * (v - ell / 2) ^ 2 / ell) ∧
      |transversePrimary hell.le d (referenceEnvelope lam u ell) p v /
        radialPrimary hell.le d (referenceEnvelope lam u ell) p v - referenceProfile (c₀ p) (u p)
          ell v| ≤
        4 * |referenceProfile (c₀ p) (u p) ell v| *
          (GrowingMode.coneConstant (lam p / Real.sqrt (1 + (3 * u p / 2) ^ 2)) C / S) := by
  have hgap : 0 < lam p / Real.sqrt (1 + (3 * u p / 2) ^ 2) :=
    div_pos hlam (PulseGrowth.radius_pos _)
  have hPpos (v : ℝ) (_ : v ∈ Icc 0 ell) : 0 < referenceEnvelope lam u ell (p, v) :=
    GaussianEnvelope.envelope_pos _ _ _
  have hdP (v : ℝ) (hv : v ∈ Icc 0 ell) :
      HasDerivAt (fun t => referenceEnvelope lam u ell (p, t))
        ((d.eigenvalue (p, v) - ViscousPropagator.referenceViscosity (lam p) (u p) ell v) *
          referenceEnvelope lam u ell (p, v)) v := by
    rw [heigen v hv]
    exact ViscousPropagator.hasDerivAt_envelope
      (ViscousPropagator.continuous_referenceRate (lam p) (u p) ell) (ell / 2) v
  have hbnd := primary_bounds hell.le d (referenceEnvelope lam u ell) hA hp
    hgap hC hD hS hlarge (by simpa only [sub_zero] using hslot)
    (ViscousPropagator.referenceViscosity (lam p) (u p) ell)
    (fun v hv => (heigen v hv).symm ▸ referenceEigenvalue_lower hlam hu.le hell hv)
    herr hν hPpos hdP
  obtain ⟨b, B, hb, hB, hg⟩ := GaussianEnvelope.reference_uniform_gaussian_bounds hlam hu
  refine ⟨b, B, hb, hB, ?_⟩
  intro v hv
  obtain ⟨hpos, hlo, hhi, hrat⟩ := hbnd v hv
  have hgauss := hg ell hell v hv
  refine ⟨hpos, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_left hgauss.1 (by positivity)).trans hlo
  · exact hhi.trans (mul_le_mul_of_nonneg_left hgauss.2 (by positivity))
  · simpa only [hprofile v hv] using hrat

end GaussianPrimary

section SmoothPrimary

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Smoothness of the actual initial envelope, proved using integration as a
bounded linear map on the fixed compact time interval. -/
theorem initialEnvelope_contDiffOn {a b : ℝ} (hab : a ≤ b)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (rate : Q × ℝ → ℝ) (hrate : ContDiffOn ℝ ∞ rate (U ×ˢ V)) (midpoint : Icc a b) :
    ContDiffOn ℝ ∞
      (fun p => GaussianEnvelope.envelope (fun t => rate (p, t)) midpoint a) U := by
  let T : C(Icc a b, ℝ) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM ℝ midpoint).comp (ParametricODE.integrator hab)
  have hpath := SmoothPathFamily.contDiffOn_pathFamily_of_joint U V hU hV hI rate hrate
  have hc := ((ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) T).comp_contDiffOn hpath).neg.exp
  apply hc.congr
  intro p hp
  have hslice := SmoothPathFamily.slice_continuous
    (hrate.continuousOn.mono (Set.prod_mono Subset.rfl hI)) hp
  have hint : (∫ s in a..(midpoint : ℝ),
      ParametricODE.extend hab (SmoothPathFamily.pathFamily rate p) s) =
      ∫ s in a..(midpoint : ℝ), rate (p, s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le midpoint.2.1] at hs
    have hs' : s ∈ Icc a b := ⟨hs.1, hs.2.trans midpoint.2.2⟩
    rw [ParametricODE.extend, projIcc_of_mem hab hs']
    exact SmoothPathFamily.pathFamily_apply rate p hslice ⟨s, hs'⟩
  change Real.exp (∫ s in (midpoint : ℝ)..a, rate (p, s)) =
    Real.exp (-(∫ s in a..(midpoint : ℝ),
      ParametricODE.extend hab (SmoothPathFamily.pathFamily rate p) s))
  rw [hint, intervalIntegral.integral_symm]

theorem referenceRate_contDiffOn {U : Set Q} (V : Set ℝ)
    (lam u : Q → ℝ) (ell : ℝ) (hlam : ContDiffOn ℝ ∞ lam U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (fun z : Q × ℝ => GaussianEnvelope.referenceRate (lam z.1) (u z.1) ell z.2)
      (U ×ˢ V) := by
  have hl : ContDiffOn ℝ ∞ (fun z : Q × ℝ => lam z.1) (U ×ˢ V) :=
    hlam.comp contDiffOn_fst (fun _ hz => hz.1)
  have hu' : ContDiffOn ℝ ∞ (fun z : Q × ℝ => u z.1) (U ×ˢ V) :=
    hu.comp contDiffOn_fst (fun _ hz => hz.1)
  have hs : ContDiffOn ℝ ∞ (fun z : Q × ℝ => PulseGrowth.slotMagnitude (u z.1) ell z.2)
      (U ×ˢ V) := (hu'.div_const 2).add ((hu'.mul contDiffOn_snd).div_const ell)
  have hs2 := (contDiffOn_const (c := (1 : ℝ))).add (hs.pow 2)
  have hu2 := (contDiffOn_const (c := (1 : ℝ))).add (hu'.pow 2)
  have hr := hs2.sqrt (fun z _ => (PulseGrowth.one_add_sq_pos _).ne')
  have hur := hu2.sqrt (fun z _ => (PulseGrowth.one_add_sq_pos _).ne')
  exact (hl.div hr (fun z _ => (PulseGrowth.radius_pos _).ne')).sub
    ((hl.mul hs2).div (hu2.mul hur) (fun z _ => (PulseGrowth.dampingDenominator_pos _).ne'))

/-- The manuscript normalization `z₊(0)=P(0), z₋(0)=0` is itself a smooth
parameter family, obtained from the explicit reference rate. -/
theorem primarySeed_reference_contDiffOn {ell : ℝ} (hell : 0 ≤ ell)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc 0 ell ⊆ V)
    (lam u : Q → ℝ) (hlam : ContDiffOn ℝ ∞ lam U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (primarySeed 0 (referenceEnvelope lam u ell)) U := by
  have hm : ell / 2 ∈ Icc 0 ell := by constructor <;> linarith
  have hE := initialEnvelope_contDiffOn hell U V hU hV hI
    (fun z : Q × ℝ => GaussianEnvelope.referenceRate (lam z.1) (u z.1) ell z.2)
    (referenceRate_contDiffOn V lam u ell hlam hu) ⟨ell / 2, hm⟩
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) MovingFrameODE.pairCLM).comp_contDiffOn
    (hE.prodMk contDiffOn_const)

theorem primary_reference_path_contDiffOn {ell : ℝ} (hell : 0 ≤ ell) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc 0 ell ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (lam u : Q → ℝ)
    (hlam : ContDiffOn ℝ ∞ lam U) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ ∞ (SmoothPathFamily.odeFamily hell (d.coefficient 1)
      (primarySeed 0 (referenceEnvelope lam u ell)) (d.forcing (fun _ => 0))) U :=
  solutionPath_contDiffOn hell d U V hU hV hI hd 1
    (primarySeed 0 (referenceEnvelope lam u ell)) (fun _ => 0)
    (primarySeed_reference_contDiffOn hell U V hU hV hI lam u hlam hu) contDiffOn_const

/-- Parameter smoothness of the constructed extension at every time in the
closed slot, including its endpoints. -/
theorem solution_contDiffOn {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (j : ℤ) (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) (v : Icc a b) :
    ContDiffOn ℝ ∞ (fun q => solution hab d j x₀ f q v) U := by
  have hpath := solutionPath_contDiffOn hab d U V hU hV hI hd j x₀ f hx₀ hf
  have heval := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (ContinuousMap.evalCLM ℝ v)).comp_contDiffOn hpath
  apply heval.congr
  intro q _
  exact extendedFamily_eq_path _ _ _ _ _ _

/-- Reconstructed ambient tangent vectors inherit parameter smoothness from
the same constructed modal path and the explicit smooth frame data. -/
theorem ambientSolution_contDiffOn {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (j : ℤ) (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) (v : Icc a b) :
    ContDiffOn ℝ ∞ (fun q => ambientSolution hab d j x₀ f q v) U := by
  have hz := solution_contDiffOn hab d U V hU hV hI hd j x₀ f hx₀ hf v
  have hz0 := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn hz
  have hz1 := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)).comp_contDiffOn hz
  have hs : MapsTo (fun q : Q => (q, (v : ℝ))) U (U ×ˢ V) := fun _ hq => ⟨hq, hI v.2⟩
  have hc : ContDiffOn ℝ ∞ (fun q : Q => (q, (v : ℝ))) U :=
    contDiffOn_id.prodMk contDiffOn_const
  have hr := hd.rho.comp hc hs
  have hh := hd.eigenvector.comp hc hs
  have hK := (hd.frame 0).comp hc hs
  have hN := (hd.frame 1).comp hc hs
  have hx := hz0.add hz1
  have hy := hh.mul (hz0.sub hz1)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) MovingFrameODE.packCLM).comp_contDiffOn
    (hx.prodMk (((hr.neg.mul hx).smul hK).add (hy.smul hN)))

end SmoothPrimary

section Joint

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

/-- Genuine joint parameter/time smoothness of the constructed solution on
the closed slot.  The joint theorem constructs a smooth representative by
time rescaling, rather than claiming the clamped extension smooth outside. -/
theorem solution_joint_contDiffOn {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (j : ℤ) (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun z : Q × ℝ => solution hab d j x₀ f z.1 z.2) (U ×ˢ Icc a b) :=
  JointODE.contDiffOn_solutionExtension_joint hab U V hU hV hI
    (d.coefficient j) x₀ (d.forcing f) (hd.coefficient j) hx₀ (hd.forcing hf)

theorem ambientSolution_joint_contDiffOn {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    (U : Set Q) (V : Set ℝ) (hU : IsOpen U) (hV : IsOpen V) (hI : Icc a b ⊆ V)
    (hd : d.SmoothOn (U ×ˢ V)) (j : ℤ) (x₀ : Q → State) (f : Q × ℝ → Space)
    (hx₀ : ContDiffOn ℝ ∞ x₀ U) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (fun z : Q × ℝ => ambientSolution hab d j x₀ f z.1 z.2) (U ×ˢ Icc a b) := by
  have hz := solution_joint_contDiffOn hab d U V hU hV hI hd j x₀ f hx₀ hf
  have hz0 := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0)).comp_contDiffOn hz
  have hz1 := (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
    (PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1)).comp_contDiffOn hz
  have hs : U ×ˢ Icc a b ⊆ U ×ˢ V := Set.prod_mono Subset.rfl hI
  have hr := hd.rho.mono hs
  have hh := hd.eigenvector.mono hs
  have hK := (hd.frame 0).mono hs
  have hN := (hd.frame 1).mono hs
  have hx := hz0.add hz1
  have hy := hh.mul (hz0.sub hz1)
  exact (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞) MovingFrameODE.packCLM).comp_contDiffOn
    (hx.prodMk (((hr.neg.mul hx).smul hK).add (hy.smul hN)))

end Joint

/-- The physical viscosity perturbation follows from closeness of the actual
phase normal.  This gives the damping input without assuming an ODE bound. -/
theorem viscosity_error_of_normal_comparison {n n₀ : Space} {κ η M : ℝ}
    (hκ : 0 ≤ κ) (hclose : ‖n - n₀‖ ≤ η) (hn₀ : ‖n₀‖ ≤ M) :
    |κ * ‖n‖ ^ 2 - κ * ‖n₀‖ ^ 2| ≤ κ * η * (2 * M + η) := by
  have hη : 0 ≤ η := (norm_nonneg _).trans hclose
  have hd : |‖n‖ - ‖n₀‖| ≤ η := (abs_norm_sub_norm_le n n₀).trans hclose
  have hs : ‖n‖ + ‖n₀‖ ≤ 2 * M + η := by linarith [(abs_le.mp hd).2]
  have he : κ * ‖n‖ ^ 2 - κ * ‖n₀‖ ^ 2 = κ * ((‖n‖ - ‖n₀‖) * (‖n‖ + ‖n₀‖)) := by ring
  rw [he, abs_mul, abs_of_nonneg hκ, abs_mul,
    abs_of_nonneg (add_nonneg (norm_nonneg n) (norm_nonneg n₀))]
  calc
    κ * (|‖n‖ - ‖n₀‖| * (‖n‖ + ‖n₀‖)) ≤ κ * (η * (2 * M + η)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hd hs (add_nonneg (norm_nonneg n) (norm_nonneg n₀)) hη) hκ
    _ = _ := by ring

/-- The source transformation has a uniform norm bound from elementary frame
and eigenvector bounds, independently of the harmonic index. -/
theorem FrameData.forcing_norm_le {Q : Type} (d : FrameData Q) (f : Q × ℝ → Space)
    (z : Q × ℝ) {R H : ℝ} (hR : 0 ≤ R) (hH : 0 ≤ H)
    (hrho : |d.rho z| ≤ R) (hh : |1 / d.eigenvector z| ≤ H) :
    ‖d.forcing f z‖ ≤ (1 + R + H) * ‖f z‖ := by
  have hf0 : |f z 0| ≤ ‖f z‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (f z) 0
  have hi (i : Fin 2) : |⟪d.frame z i, MovingFrameODE.tail (f z)⟫_ℝ| ≤ ‖f z‖ := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [(d.frame z).norm_eq_one i, one_mul]
    exact PhaseEstimates.tail_norm_le _
  have hx : |d.forceX f z| ≤ (1 + R) * ‖f z‖ := by
    unfold FrameData.forceX
    apply (MovingFrameODE.abs_div_le_of_one_le _ _ (by nlinarith [sq_nonneg (d.rho z)])).trans
    rw [abs_neg]
    calc
      |f z 0 - d.rho z * ⟪d.frame z 0, MovingFrameODE.tail (f z)⟫_ℝ| ≤
          |f z 0| + |d.rho z * ⟪d.frame z 0, MovingFrameODE.tail (f z)⟫_ℝ| := abs_sub _ _
      _ = |f z 0| + |d.rho z| * |⟪d.frame z 0, MovingFrameODE.tail (f z)⟫_ℝ| := by rw [abs_mul]
      _ ≤ ‖f z‖ + R * ‖f z‖ := add_le_add hf0 (mul_le_mul hrho (hi 0) (abs_nonneg _) hR)
      _ = _ := by ring
  have hy : |d.forceY f z| ≤ ‖f z‖ := by simpa only [FrameData.forceY, abs_neg] using hi 1
  have hdiv : |d.forceY f z / d.eigenvector z| ≤ H * ‖f z‖ := by
    calc
      |d.forceY f z / d.eigenvector z| = |1 / d.eigenvector z| * |d.forceY f z| := by
        rw [abs_div, abs_div, abs_one]
        ring
      _ ≤ _ := mul_le_mul hh hy (abs_nonneg _) hH
  apply (MovingFrameODE.plane_norm_le_coordinate_sum (d.forcing f z)).trans
  change |(d.forceX f z + d.forceY f z / d.eigenvector z) / 2| +
    |(d.forceX f z - d.forceY f z / d.eigenvector z) / 2| ≤ _
  rw [abs_div, abs_div]
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [abs_add_le (d.forceX f z) (d.forceY f z / d.eigenvector z),
    abs_sub (d.forceX f z) (d.forceY f z / d.eigenvector z)]

private theorem norm_pack_le (x : ℝ) (v : State) : ‖MovingFrameODE.pack x v‖ ≤ |x| + ‖v‖ := by
  have hs := MovingFrameODE.inner_pack x x v v
  simp only [real_inner_self_eq_norm_sq] at hs
  nlinarith [norm_nonneg (MovingFrameODE.pack x v), norm_nonneg v, abs_nonneg x,
    sq_abs x, mul_nonneg (abs_nonneg x) (norm_nonneg v)]

theorem FrameData.ambient_norm_le {Q : Type} (d : FrameData Q) (z : Q × ℝ) (w : State)
    {R H : ℝ} (hrho : |d.rho z| ≤ R) (hh : |d.eigenvector z| ≤ H) :
    ‖d.ambient z w‖ ≤ 2 * (1 + R + H) * ‖w‖ := by
  have hR : 0 ≤ R := (abs_nonneg _).trans hrho
  have hH : 0 ≤ H := (abs_nonneg _).trans hh
  have hw (i : Fin 2) : |w i| ≤ ‖w‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le w i
  have hx : |w 0 + w 1| ≤ 2 * ‖w‖ := (abs_add_le _ _).trans (by linarith [hw 0, hw 1])
  have hdiff : |w 0 - w 1| ≤ 2 * ‖w‖ := (abs_sub _ _).trans (by linarith [hw 0, hw 1])
  have htail : ‖(-d.rho z * (w 0 + w 1)) • d.frame z 0 +
      (d.eigenvector z * (w 0 - w 1)) • d.frame z 1‖ ≤
      |d.rho z| * |w 0 + w 1| + |d.eigenvector z| * |w 0 - w 1| := by
    apply (norm_add_le _ _).trans_eq
    simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_neg, (d.frame z).norm_eq_one, mul_one]
  change ‖MovingFrameODE.pack (w 0 + w 1)
    ((-d.rho z * (w 0 + w 1)) • d.frame z 0 +
      (d.eigenvector z * (w 0 - w 1)) • d.frame z 1)‖ ≤ _
  apply (norm_pack_le _ _).trans
  have hrx := mul_le_mul hrho hx (abs_nonneg _) hR
  have hhy := mul_le_mul hh hdiff (abs_nonneg _) hH
  nlinarith

/-- The inverse coordinate transformation is uniformly bounded too, so the
modal forward estimate is a genuine ambient tangent propagator estimate. -/
theorem FrameData.norm_le_ambient {Q : Type} (d : FrameData Q) (z : Q × ℝ) (w : State)
    {H : ℝ} (hne : d.eigenvector z ≠ 0) (hh : |1 / d.eigenvector z| ≤ H) :
    ‖w‖ ≤ (1 + H) * ‖d.ambient z w‖ := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hh
  have hx : |w 0 + w 1| ≤ ‖d.ambient z w‖ := by
    simpa only [FrameData.ambient, MovingFrameODE.tangent, MovingFrameODE.pack_zero,
      Real.norm_eq_abs]
      using PiLp.norm_apply_le (d.ambient z w) 0
  have hy : |d.eigenvector z * (w 0 - w 1)| ≤ ‖d.ambient z w‖ := by
    have he : ⟪d.frame z 1, MovingFrameODE.tail (d.ambient z w)⟫_ℝ =
        d.eigenvector z * (w 0 - w 1) := by
      simp only [FrameData.ambient, MovingFrameODE.tangent, MovingFrameODE.tail_pack,
        inner_add_right, inner_smul_right, MovingFrameODE.frame_inner10,
        MovingFrameODE.frame_inner11, mul_zero, mul_one, zero_add]
    rw [← he]
    apply (abs_real_inner_le_norm _ _).trans
    rw [(d.frame z).norm_eq_one 1, one_mul]
    exact PhaseEstimates.tail_norm_le _
  have hdiff : |w 0 - w 1| ≤ H * ‖d.ambient z w‖ := by
    calc
      |w 0 - w 1| = |1 / d.eigenvector z| * |d.eigenvector z * (w 0 - w 1)| := by
        rw [← abs_mul]
        congr 1
        field_simp
      _ ≤ _ := mul_le_mul hh hy (abs_nonneg _) hH
  have hp : 2 * |w 0| ≤ |w 0 + w 1| + |w 0 - w 1| := by
    have hi := abs_add_le (w 0 + w 1) (w 0 - w 1)
    have he : w 0 + w 1 + (w 0 - w 1) = 2 * w 0 := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
    exact hi
  have hq : 2 * |w 1| ≤ |w 0 + w 1| + |w 0 - w 1| := by
    have hi := abs_sub (w 0 + w 1) (w 0 - w 1)
    have he : w 0 + w 1 - (w 0 - w 1) = 2 * w 1 := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hi
    exact hi
  have hn := MovingFrameODE.plane_norm_le_coordinate_sum w
  nlinarith

section AmbientForward

variable {Q : Type} [NormedAddCommGroup Q]

/-- The forward estimate in actual ambient tangent norm, with constants
independent of the nonzero integer harmonic. -/
theorem ambient_homogeneous_forward_bound {a b : ℝ} (hab : a ≤ b) (d : FrameData Q)
    {j : ℤ} (hj : j ≠ 0) (x₀ : Q → State) {U : Set Q}
    (hA : ContinuousOn (d.coefficient j) (U ×ˢ Icc a b))
    {p : Q} (hp : p ∈ U) (referenceDamping rate P : ℝ → ℝ)
    {S C D L R H : ℝ} (hS : 0 < S) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hslot : b - a ≤ L * S)
    (hPpos : ∀ v, 0 < P v) (hP : ∀ v, HasDerivAt P (rate v * P v) v)
    (hreference : ∀ v ∈ Icc a b, rate v = d.eigenvalue (p, v) - referenceDamping v)
    (hlam : ∀ v ∈ Icc a b, 0 ≤ d.eigenvalue (p, v))
    (hν : ∀ v ∈ Icc a b, 0 ≤ d.viscosity (p, v))
    (hνerr : ∀ v ∈ Icc a b, referenceDamping v - D / S ≤ d.viscosity (p, v))
    (herr : ∀ v ∈ Icc a b,
      |d.error11 (p, v)| ≤ C / S ∧ |d.error12 (p, v)| ≤ C / S ∧
      |d.error21 (p, v)| ≤ C / S ∧ |d.error22 (p, v)| ≤ C / S)
    (hrho : ∀ v ∈ Icc a b, |d.rho (p, v)| ≤ R)
    (hh : ∀ v ∈ Icc a b, |d.eigenvector (p, v)| ≤ H)
    (hne : d.eigenvector (p, a) ≠ 0) (hhi : |1 / d.eigenvector (p, a)| ≤ H) :
    ∀ v ∈ Icc a b, ‖ambientSolution hab d j x₀ (fun _ => 0) p v‖ ≤
      (2 * (1 + R + H) * (1 + H) * Real.exp ((D + 4 * C) * L)) *
        (P v / P a) * ‖ambientSolution hab d j x₀ (fun _ => 0) p a‖ := by
  have hbnd := homogeneous_forward_bound hab d hj x₀ hA hp referenceDamping rate P
    hS hC hD hslot hPpos hP hreference hlam hν hνerr herr
  have hstart : ‖x₀ p‖ ≤ (1 + H) * ‖ambientSolution hab d j x₀ (fun _ => 0) p a‖ := by
    simpa only [ambientSolution, solution_initial] using
      d.norm_le_ambient (p, a) (x₀ p) hne hhi
  have hR : 0 ≤ R := (abs_nonneg _).trans (hrho a ⟨le_rfl, hab⟩)
  have hH : 0 ≤ H := (abs_nonneg _).trans (hh a ⟨le_rfl, hab⟩)
  have hfac : 0 ≤ 2 * (1 + R + H) := by positivity
  intro v hv
  calc
    _ ≤ (2 * (1 + R + H)) * ‖solution hab d j x₀ (fun _ => 0) p v‖ :=
      d.ambient_norm_le (p, v) _ (hrho v hv) (hh v hv)
    _ ≤ (2 * (1 + R + H)) *
        (Real.exp ((D + 4 * C) * L) * (P v / P a) * ‖x₀ p‖) :=
      mul_le_mul_of_nonneg_left (hbnd v hv) hfac
    _ ≤ (2 * (1 + R + H)) *
        (Real.exp ((D + 4 * C) * L) * (P v / P a) *
          ((1 + H) * ‖ambientSolution hab d j x₀ (fun _ => 0) p a‖)) := by
      apply mul_le_mul_of_nonneg_left _ hfac
      exact mul_le_mul_of_nonneg_left hstart
        (mul_nonneg (Real.exp_pos _).le (div_pos (hPpos v) (hPpos a)).le)
    _ = _ := by ring

end AmbientForward

section LocalPhaseFrame

variable {Q : Type}

/-- Total frame selection.  The fallback is outside the nonvanishing phase
chart and imposes no hypothesis on those unused parameter values. -/
noncomputable def localFrame (n : Space) : Frame := by
  classical
  exact if hn : MovingFrameODE.tail n ≠ 0 then MovingFrameODE.normalFrame n hn
    else EuclideanSpace.basisFun (Fin 2) ℝ

theorem localFrame_eq {n : Space} (hn : MovingFrameODE.tail n ≠ 0) :
    localFrame n = MovingFrameODE.normalFrame n hn := by
  simp [localFrame, hn]

/-- The actual phase-derived coefficients require nonvanishing only on the
chart where they are used. -/
noncomputable def FrameData.ofNormalLocal (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) : FrameData Q where
  beta z := MovingFrameODE.normalScale (n z)
  betaDot z := PhaseEstimates.scaleDerivative (n z) (nDot z)
  rho z := MovingFrameODE.radialSlope (n z)
  rhoDot z := PhaseEstimates.slopeDerivative (n z) (nDot z)
  rotation z := PhaseEstimates.angularVelocity (n z) (nDot z)
  F := F
  shear := g
  frame z := localFrame (n z)
  eigenvalue := lam
  eigenvector := h
  eigenRate := hRate
  viscosity z := viscosityScale z * ‖n z‖ ^ 2

theorem FrameData.ofNormalLocal_normal (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) {z : Q × ℝ}
    (hn : MovingFrameODE.tail (n z) ≠ 0) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).normal z = n z := by
  change MovingFrameODE.normal _ _ (localFrame (n z)) = n z
  rw [localFrame_eq hn]
  exact MovingFrameODE.normal_reconstructed hn

theorem FrameData.ofNormalLocal_kinematics (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) (p : Q) (I : Set ℝ)
    (hn : ∀ v ∈ I, HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v)
    (hne : ∀ v ∈ I, MovingFrameODE.tail (n (p, v)) ≠ 0)
    (hh : ∀ v ∈ I, h (p, v) ≠ 0)
    (hdh : ∀ v ∈ I, HasDerivAt (fun t => h (p, t)) (hRate (p, v) * h (p, v)) v) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).Kinematics p I := by
  have hframe (v : ℝ) (hv : v ∈ I) (i : Fin 2) :
      (fun t => localFrame (n (p, t)) i) =ᶠ[𝓝 v]
        (fun t => if i = 0 then MovingFrameODE.normalDirection (n (p, t))
          else MovingFrameODE.quarterTurn (MovingFrameODE.normalDirection (n (p, t)))) := by
    have ht := MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v (hn v hv)
    filter_upwards [ht.continuousAt.eventually_ne (hne v hv)] with t ht'
    rw [localFrame_eq ht']
    fin_cases i
    · simpa only [Fin.zero_eta, ↓reduceIte] using MovingFrameODE.normalFrame_zero (n (p, t)) ht'
    · simpa only [Fin.mk_one, one_ne_zero, ↓reduceIte] using MovingFrameODE.normalFrame_one (n (p,
      t)) ht'
  refine ⟨fun v hv => (MovingFrameODE.normalScale_pos (hne v hv)).ne', hh,
    ?_, ?_, hdh, ?_, ?_⟩
  · intro v hv
    exact PhaseEstimates.hasDerivAt_normalScale (hn v hv) (hne v hv)
  · intro v hv
    exact PhaseEstimates.hasDerivAt_radialSlope (hn v hv) (hne v hv)
  · intro v hv
    have he := hframe v hv 0
    simp only [ite_true] at he
    have hd := (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne v hv)).1
    have hk := hd.congr_of_eventuallyEq he
    simpa only [FrameData.ofNormalLocal, localFrame_eq (hne v hv), MovingFrameODE.normalFrame_one]
      using hk
  · intro v hv
    have he := hframe v hv 1
    simp only [one_ne_zero, ite_false] at he
    have hd := (PhaseEstimates.hasDerivAt_actual_frame (hn v hv) (hne v hv)).2
    have hk := hd.congr_of_eventuallyEq he
    simpa only [FrameData.ofNormalLocal, localFrame_eq (hne v hv), MovingFrameODE.normalFrame_zero]
      using hk

theorem FrameData.ofNormalLocal_normalMotion (n nDot : Q × ℝ → Space)
    (F : Q × ℝ → ℝ) (g : Q × ℝ → State)
    (lam h hRate viscosityScale : Q × ℝ → ℝ) {p : Q} {v : ℝ}
    (hn : HasDerivAt (fun t => n (p, t)) (nDot (p, v)) v)
    (hne : MovingFrameODE.tail (n (p, v)) ≠ 0) :
    (FrameData.ofNormalLocal n nDot F g lam h hRate viscosityScale).normalMotion (p, v) = nDot (p,
      v) := by
  have htail := MovingFrameODE.tailCLM.hasFDerivAt.comp_hasDerivAt v hn
  have hnear := htail.continuousAt.eventually_ne hne
  have hKeq : (fun t => localFrame (n (p, t)) 0) =ᶠ[𝓝 v]
      (fun t => MovingFrameODE.normalDirection (n (p, t))) := by
    filter_upwards [hnear] with t ht
    rw [localFrame_eq ht]
    exact MovingFrameODE.normalFrame_zero (n (p, t)) ht
  have hK : HasDerivAt (fun t => localFrame (n (p, t)) 0)
      (PhaseEstimates.angularVelocity (n (p, v)) (nDot (p, v)) • localFrame (n (p, v)) 1) v := by
    simpa only [localFrame_eq hne, MovingFrameODE.normalFrame_one] using
      (PhaseEstimates.hasDerivAt_actual_frame hn hne).1.congr_of_eventuallyEq hKeq
  have hd := MovingFrameODE.hasDerivAt_normal
    (PhaseEstimates.hasDerivAt_normalScale hn hne) (PhaseEstimates.hasDerivAt_radialSlope hn hne) hK
  have heq : (fun t => n (p, t)) =ᶠ[𝓝 v]
      (fun t => MovingFrameODE.normal (MovingFrameODE.normalScale (n (p, t)))
        (MovingFrameODE.radialSlope (n (p, t))) (localFrame (n (p, t)))) := by
    filter_upwards [hnear] with t ht
    rw [localFrame_eq ht]
    exact (MovingFrameODE.normal_reconstructed ht).symm
  exact (hd.congr_of_eventuallyEq heq).unique hn

end LocalPhaseFrame

end NavierStokes.PrimaryODE
