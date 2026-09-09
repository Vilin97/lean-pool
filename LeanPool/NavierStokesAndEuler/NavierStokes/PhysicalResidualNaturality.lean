/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.PhysicalParticularWave
public import LeanPool.NavierStokesAndEuler.NavierStokes.HarmonicSourceSupport

@[expose] public section

/-!
# Naturality of the actual lifted residual coefficients

The hypotheses in this file concern the full free auxiliary-variable lift.
Equality only on the physical graph is deliberately insufficient.  The source
is always the literal `HarmonicResidual.residualBlock`, including its real
projection and its Gaussian and alias subtractions.
-/

noncomputable section

namespace NavierStokes.PhysicalResidualNaturality

open Set Filter
open scoped Topology ComplexConjugate
open HarmonicCalculus HarmonicFields


variable {D E F : Type} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scalar multiplication by a nonzero real number, with its actual inverse. -/
noncomputable def scalarEquiv (F : Type) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (a : ℝ) (ha : a ≠ 0) : F ≃L[ℝ] F :=
  { LinearEquiv.smulOfNeZero ℝ F a ha with
    continuous_toFun := continuous_const.smul continuous_id
    continuous_invFun := continuous_const.smul continuous_id }

@[simp] theorem scalarEquiv_apply (a : ℝ) (ha : a ≠ 0) (x : F) :
    scalarEquiv F a ha x = a • x := rfl

/-- This version also handles non-differentiable functions and the zero scalar. -/
theorem fderiv_scalar (a : ℝ) (f : D → F) (x : D) :
    fderiv ℝ (fun y => a • f y) x = a • fderiv ℝ f x := by
  by_cases ha : a = 0
  · subst a
    simp
  · have he := (scalarEquiv F a ha).comp_fderiv (f := f) (x := x)
    exact he

theorem along_pull (e : D ≃L[ℝ] E) (a b : ℝ) (V : D → D) (W : E → E)
    (f : E → F) (x : D) (hV : e (V x) = b • W (e x)) :
    along V (fun y => a • f (e y)) x = (a * b) • along W f (e x) := by
  unfold along
  rw [fderiv_scalar]
  change a • ((fderiv ℝ (f ∘ e) x) (V x)) = _
  rw [e.comp_right_fderiv, ContinuousLinearMap.comp_apply]
  change a • (fderiv ℝ f (e x)) (e (V x)) = _
  rw [hV, map_smul, smul_smul]

/-- Equality of every coefficient on a full lifted open set, with one weight. -/
def CoefficientsOn (U : Set D) (e : D ≃L[ℝ] E) (a : ℝ)
    (c : Coefficients D) (d : Coefficients E) : Prop :=
  ∀ j x, x ∈ U → c j x = a • d j (e x)

namespace CoefficientsOn

theorem reweight {U : Set D} {e : D ≃L[ℝ] E} {a b : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d)
    (hab : a = b) : CoefficientsOn U e b c d := hab ▸ hc

theorem zero (U : Set D) (e : D ≃L[ℝ] E) (a : ℝ) :
    CoefficientsOn U e a 0 0 := by
  intro j x hx
  simp

theorem add {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c₁ c₂ : Coefficients D} {d₁ d₂ : Coefficients E}
    (h₁ : CoefficientsOn U e a c₁ d₁) (h₂ : CoefficientsOn U e a c₂ d₂) :
    CoefficientsOn U e a (c₁ + c₂) (d₁ + d₂) := by
  intro j x hx
  change c₁ j x + c₂ j x = a • (d₁ j (e x) + d₂ j (e x))
  rw [h₁ j x hx, h₂ j x hx, smul_add]

theorem sub {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c₁ c₂ : Coefficients D} {d₁ d₂ : Coefficients E}
    (h₁ : CoefficientsOn U e a c₁ d₁) (h₂ : CoefficientsOn U e a c₂ d₂) :
    CoefficientsOn U e a (c₁ - c₂) (d₁ - d₂) := by
  intro j x hx
  change c₁ j x - c₂ j x = a • (d₁ j (e x) - d₂ j (e x))
  rw [h₁ j x hx, h₂ j x hx, smul_sub]

theorem neg {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d) :
    CoefficientsOn U e a (-c) (-d) := by
  intro j x hx
  change -c j x = a • (-d j (e x))
  rw [hc j x hx, smul_neg]

theorem boundConstant {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {f : D → ℂ} {g : E → ℂ} (h : ∀ x ∈ U, f x = a • g (e x)) :
    CoefficientsOn U e a (constantCoefficient f) (constantCoefficient g) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j
    simpa only [constantCoefficient, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same] using h
      x hx
  · simp [constantCoefficient, hj]

theorem convolution_sum {A : Type} (c d : Coefficients A) (S : Finset ℤ)
    (hS : c.support ⊆ S) (j : ℤ) (x : A) :
    (c * d) j x = ∑ k ∈ S, c k x * d (j-k) x := by
  rw [convolution_apply]
  exact Finset.sum_subset hS (by
    intro k hk hkc
    simp [Finsupp.notMem_support_iff.mp hkc])

theorem mul {U : Set D} {e : D ≃L[ℝ] E} {a b : ℝ}
    {c₁ c₂ : Coefficients D} {d₁ d₂ : Coefficients E}
    (h₁ : CoefficientsOn U e a c₁ d₁) (h₂ : CoefficientsOn U e b c₂ d₂) :
    CoefficientsOn U e (a*b) (c₁*c₂) (d₁*d₂) := by
  intro j x hx
  let S := c₁.support ∪ d₁.support
  rw [convolution_sum c₁ c₂ S Finset.subset_union_left,
    convolution_sum d₁ d₂ S Finset.subset_union_right, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [h₁ k x hx, h₂ (j-k) x hx]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

theorem scale {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d)
    (b : ℝ) : CoefficientsOn U e (b*a) (b • c) d := by
  intro j x hx
  change b • c j x = (b*a) • d j (e x)
  rw [hc j x hx, smul_smul]

theorem angular {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d)
    (k : ℤ) : CoefficientsOn U e a (angularDifferentiate k c) (angularDifferentiate k d) := by
  intro j x hx
  change _ * c j x = a • (_ * d j (e x))
  rw [hc j x hx]
  simp only [Complex.real_smul]
  ring

theorem realCoefficients {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d) :
    CoefficientsOn U e a (HarmonicResidual.realCoefficients c) (HarmonicResidual.realCoefficients
      d) := by
  intro j x hx
  simp only [HarmonicResidual.realCoefficients_apply, hc j x hx, hc (-j) x hx,
    Complex.real_smul, map_mul, Complex.conj_ofReal]
  ring

theorem nonconstant {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {c : Coefficients D} {d : Coefficients E} (hc : CoefficientsOn U e a c d) :
    CoefficientsOn U e a (HarmonicResidual.nonconstant c) (HarmonicResidual.nonconstant d) := by
  intro j x hx
  by_cases hj : j = 0
  · subst j
    simp [HarmonicResidual.nonconstant]
  · simpa only [HarmonicResidual.nonconstant, AddMonoidAlgebra.coeff_erase, Finsupp.erase_ne hj]
    using hc j x hx

/-- Carrier compatibility is an equality before restriction to the graph. -/
theorem differentiate {U : Set D} (hU : IsOpen U) {e : D ≃L[ℝ] E}
    {a b k kr : ℝ} {c : Coefficients D} {d : Coefficients E}
    {V : D → D} {W : E → E} {Phi : D → ℝ} {Psi : E → ℝ}
    (hc : CoefficientsOn U e a c d)
    (hV : ∀ x ∈ U, e (V x) = b • W (e x))
    (hphase : EqOn (fun x => k * Phi x) (fun x => kr * Psi (e x)) U) :
    CoefficientsOn U e (a*b) (differentiate V k Phi c) (differentiate W kr Psi d) := by
  intro j x hx
  have hv := hV x hx
  have he : c j =ᶠ[𝓝 x] (fun y => a • d j (e y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hc j y hy
  have hp : (fun y => k * Phi y) =ᶠ[𝓝 x] (fun y => kr * Psi (e y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hphase hy
  have hd : along V (c j) x = (a*b) • along W (d j) (e x) := by
    unfold along
    rw [he.fderiv_eq]
    exact along_pull e a b V W (d j) x hv
  have hdp : k * along V Phi x = (kr*b) * along W Psi (e x) := by
    have heq := congrArg (fun L : D →L[ℝ] ℝ => L (V x)) hp.fderiv_eq
    change along V (fun y => k • Phi y) x = along V (fun y => kr • Psi (e y)) x at heq
    rw [along_pull e kr b V W Psi x hv] at heq
    change (fderiv ℝ (fun y => k • Phi y) x) (V x) = _ at heq
    rw [fderiv_scalar] at heq
    exact heq
  simp only [differentiate_apply, derivativeCoefficient, hd, hc j x hx,
    Complex.real_smul, phaseFactor, Complex.ofReal_mul]
  have hz := congrArg Complex.ofReal hdp
  simp only [Complex.ofReal_mul] at hz
  calc
    _ = (a : ℂ) * (b : ℂ) * along W (d j) (e x) +
        (a : ℂ) * ((j : ℝ) : ℂ) * Complex.I *
          ((k : ℂ) * ((along V Phi x : ℝ) : ℂ)) * d j (e x) := by ring
    _ = _ := by rw [hz]; ring

end CoefficientsOn

/-! ## The actual cylindrical operator, including its frame terms -/

/-- Primitive chart identities.  The time and viscosity identities include
the slow-time sign and the physical viscosity normalization. -/
structure FrameOn (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (g : HarmonicResidual.Frame D) (r : HarmonicResidual.Frame E) : Prop where
  radial : ∀ x ∈ U, e (g.radial x) = l • r.radial (e x)
  axial : ∀ x ∈ U, e (g.axial x) = l • r.axial (e x)
  time : ∀ x ∈ U, e (g.time x) = (c*l) • r.time (e x)
  radius : ∀ x ∈ U, r.radius (e x) = l * g.radius x
  viscosity : g.viscosity * l = c * r.viscosity

namespace FrameOn

variable {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
  {g : HarmonicResidual.Frame D} {r : HarmonicResidual.Frame E}

theorem inverseRadius (H : FrameOn U e c l g r) (hl : l ≠ 0) :
    CoefficientsOn U e l
      (constantCoefficient (fun x => ((g.radius x)⁻¹ : ℝ) : D → ℂ))
      (constantCoefficient (fun x => ((r.radius x)⁻¹ : ℝ) : E → ℂ)) := by
  apply CoefficientsOn.boundConstant
  intro x hx
  have hrad : (g.radius x)⁻¹ = l * (r.radius (e x))⁻¹ := by
    rw [H.radius x hx, mul_inv_rev]
    calc
      _ = (l * l⁻¹) * (g.radius x)⁻¹ := by rw [mul_inv_cancel₀ hl, one_mul]
      _ = _ := by ring
  simpa only [Complex.real_smul, ← Complex.ofReal_mul] using congrArg Complex.ofReal hrad

theorem inverseRadiusSq (H : FrameOn U e c l g r) (hl : l ≠ 0) :
    CoefficientsOn U e (l*l)
      (constantCoefficient (fun x => (((g.radius x)^2)⁻¹ : ℝ) : D → ℂ))
      (constantCoefficient (fun x => (((r.radius x)^2)⁻¹ : ℝ) : E → ℂ)) := by
  apply CoefficientsOn.boundConstant
  intro x hx
  have hrad : ((g.radius x)^2)⁻¹ = (l*l) * ((r.radius (e x))^2)⁻¹ := by
    rw [H.radius x hx, mul_pow, mul_inv_rev]
    calc
      _ = (l^2 * (l^2)⁻¹) * (g.radius x ^ 2)⁻¹ := by
        rw [mul_inv_cancel₀ (pow_ne_zero 2 hl), one_mul]
      _ = _ := by ring
  simpa only [Complex.real_smul, ← Complex.ofReal_mul] using congrArg Complex.ofReal hrad

theorem scalarLaplacian (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {f : Coefficients D} {q : Coefficients E} (hf : CoefficientsOn U e a f q)
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    CoefficientsOn U e (a*(l*l))
      (HarmonicResidual.scalarLaplacian g k Phi kp f)
      (HarmonicResidual.scalarLaplacian r kr Psi kp q) := by
  have hrr := (hf.differentiate hU H.radial hp).differentiate hU H.radial hp
  have hr := (H.inverseRadius hl).mul (hf.differentiate hU H.radial hp)
  have ht := (H.inverseRadiusSq hl).mul ((hf.angular kp).angular kp)
  have hzz := (hf.differentiate hU H.axial hp).differentiate hU H.axial hp
  have hrr' := hrr.reweight (b := a*(l*l)) (by ring)
  have hr' := hr.reweight (b := a*(l*l)) (by ring)
  have ht' := ht.reweight (b := a*(l*l)) (by ring)
  have hzz' := hzz.reweight (b := a*(l*l)) (by ring)
  exact ((hrr'.add hr').add ht').add hzz'

theorem rotate {a : ℝ} {f : HarmonicResidual.VectorCoefficients D}
    {q : HarmonicResidual.VectorCoefficients E}
    (hf : ∀ i, CoefficientsOn U e a (f i) (q i)) :
    ∀ i, CoefficientsOn U e a (HarmonicResidual.rotate f i) (HarmonicResidual.rotate q i) := by
  intro i
  fin_cases i
  · exact (hf 1).neg
  · exact hf 0
  · exact CoefficientsOn.zero U e a

theorem vectorLaplacian (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {f : HarmonicResidual.VectorCoefficients D} {q : HarmonicResidual.VectorCoefficients E}
    (hf : ∀ i, CoefficientsOn U e a (f i) (q i))
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    ∀ i, CoefficientsOn U e (a*(l*l))
      (HarmonicResidual.vectorLaplacian g k Phi kp f i)
      (HarmonicResidual.vectorLaplacian r kr Psi kp q i) := by
  intro i
  have htwo : CoefficientsOn U e 1
      (constantCoefficient (fun _ : D => (2 : ℂ)))
      (constantCoefficient (fun _ : E => (2 : ℂ))) :=
    CoefficientsOn.boundConstant (by intro x hx; simp)
  have ht := htwo.mul (rotate (fun i => (hf i).angular kp) i)
  have ht' := ht.reweight (b := a) (one_mul a)
  have hframe := (H.inverseRadiusSq hl).mul (ht'.add (rotate (rotate hf) i))
  have hframe' := hframe.reweight (b := a*(l*l)) (by ring)
  exact (H.scalarLaplacian hU hl kp (hf i) hp).add hframe'

theorem transport (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {a b k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {f v : HarmonicResidual.VectorCoefficients D} {q w : HarmonicResidual.VectorCoefficients E}
    (hf : ∀ i, CoefficientsOn U e a (f i) (q i))
    (hv : ∀ i, CoefficientsOn U e b (v i) (w i))
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    ∀ i, CoefficientsOn U e (a*b*l)
      (HarmonicResidual.transport g k Phi kp f v i)
      (HarmonicResidual.transport r kr Psi kp q w i) := by
  intro i
  have hr := (hf 0).mul ((hv i).differentiate hU H.radial hp)
  have ht := ((hf 1).mul (H.inverseRadius hl)).mul ((hv i).angular kp |>.add (rotate hv i))
  have hz := (hf 2).mul ((hv i).differentiate hU H.axial hp)
  have hr' := hr.reweight (b := a*b*l) (by ring)
  have ht' := ht.reweight (b := a*b*l) (by ring)
  have hz' := hz.reweight (b := a*b*l) (by ring)
  simpa only [HarmonicResidual.transport, Complex.ofReal_inv] using (hr'.add ht').add hz'

theorem gradient (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {f : Coefficients D} {q : Coefficients E} (hf : CoefficientsOn U e a f q)
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    ∀ i, CoefficientsOn U e (a*l)
      (HarmonicResidual.gradient g k Phi kp f i)
      (HarmonicResidual.gradient r kr Psi kp q i) := by
  intro i
  fin_cases i
  · exact hf.differentiate hU H.radial hp
  · have ht := (H.inverseRadius hl).mul (hf.angular kp)
    exact ht.reweight (mul_comm l a)
  · exact hf.differentiate hU H.axial hp

theorem linearResidual (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {B f : HarmonicResidual.VectorCoefficients D} {Br q : HarmonicResidual.VectorCoefficients E}
    {p : Coefficients D} {pr : Coefficients E}
    (hB : ∀ i, CoefficientsOn U e c (B i) (Br i))
    (hf : ∀ i, CoefficientsOn U e c (f i) (q i))
    (hp : CoefficientsOn U e (c*c) p pr)
    (hphase : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    ∀ i, CoefficientsOn U e (c*c*l)
      (HarmonicResidual.linearResidual g k Phi kp B f p i)
      (HarmonicResidual.linearResidual r kr Psi kp Br q pr i) := by
  intro i
  have htime := (hf i).differentiate hU H.time hphase
  have htime' := htime.reweight (b := c*c*l) (by ring)
  have hfirst := ((htime'.add (H.transport hU hl kp hB hf hphase i)).add
    (H.transport hU hl kp hf hB hphase i)).add (H.gradient hU hl kp hp hphase i)
  have hv : CoefficientsOn U e (c*c*l)
      (constantCoefficient (fun _ => (g.viscosity : ℂ)) *
        HarmonicResidual.vectorLaplacian g k Phi kp f i)
      (constantCoefficient (fun _ => (r.viscosity : ℂ)) *
        HarmonicResidual.vectorLaplacian r kr Psi kp q i) := by
    intro j x hx
    have he := H.vectorLaplacian hU hl kp hf hphase i j x hx
    simp only [constantCoefficient, AddMonoidAlgebra.coeff_single_zero_mul, Pi.mul_apply,
      he, Complex.real_smul, Complex.ofReal_mul]
    have hvis := congrArg Complex.ofReal H.viscosity
    simp only [Complex.ofReal_mul] at hvis
    calc
      _ = (c : ℂ) * (l : ℂ) * ((g.viscosity : ℂ) * (l : ℂ)) *
          HarmonicResidual.vectorLaplacian r kr Psi kp q i j (e x) := by ring
      _ = _ := by rw [hvis]; ring
  exact hfirst.sub hv

theorem nonlinearResidual (H : FrameOn U e c l g r) (hU : IsOpen U) (hl : l ≠ 0)
    {k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} (kp : ℤ)
    {B f : HarmonicResidual.VectorCoefficients D} {Br q : HarmonicResidual.VectorCoefficients E}
    {p : Coefficients D} {pr : Coefficients E}
    (hB : ∀ i, CoefficientsOn U e c (B i) (Br i))
    (hf : ∀ i, CoefficientsOn U e c (f i) (q i))
    (hp : CoefficientsOn U e (c*c) p pr)
    (hphase : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U) :
    ∀ i, CoefficientsOn U e (c*c*l)
      (HarmonicResidual.nonlinearResidual g k Phi kp B f p i)
      (HarmonicResidual.nonlinearResidual r kr Psi kp Br q pr i) := by
  intro i
  exact (H.linearResidual hU hl kp hB hf hp hphase i).add
    (H.transport hU hl kp hf hf hphase i)

end FrameOn

/-! ## Recovering the source from actual field compatibility -/

omit [NormedAddCommGroup D] [NormedSpace ℝ D] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Uniqueness at one full angular fiber.  Frequencies may differ, but the
integer angular carrier and the complete slow carrier agree. -/
theorem coefficient_of_field {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ}
    {kp : ℤ} (hkp : kp ≠ 0) (f : Coefficients D) (q : Coefficients E)
    (x : D) (y : E) (hphase : k*Phi x = kr*Psi y)
    (hfield : ∀ theta, field f k Phi kp (x,theta) =
      a • field q kr Psi kp (y,theta)) (j : ℤ) : f j x = a • q j y := by
  rw [← HarmonicResidual.extract_field f k Phi hkp j x,
    ← HarmonicResidual.extract_field q kr Psi hkp j y]
  unfold HarmonicResidual.extract
  have htest (theta : ℝ) :
      field (AddMonoidAlgebra.single (-j) (fun _ : D => (1 : ℂ))) k Phi kp (x,theta) =
      field (AddMonoidAlgebra.single (-j) (fun _ : E => (1 : ℂ))) kr Psi kp (y,theta) := by
    simp only [field, evaluate_single, hphase]
  simp_rw [hfield, htest, Complex.real_smul]
  simp only [angularMean]
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  ring

theorem CoefficientsOn.of_fields {U : Set D} {e : D ≃L[ℝ] E}
    {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} {kp : ℤ} (hkp : kp ≠ 0)
    {f : Coefficients D} {q : Coefficients E}
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U)
    (hf : ∀ x ∈ U, ∀ theta, field f k Phi kp (x,theta) =
      a • field q kr Psi kp (e x,theta)) : CoefficientsOn U e a f q := by
  intro j x hx
  exact coefficient_of_field hkp f q x (e x) (hp hx) (hf x hx) j

theorem CoefficientsOn.of_real_fields {U : Set D} {e : D ≃L[ℝ] E}
    {a k kr : ℝ} {Phi : D → ℝ} {Psi : E → ℝ} {kp : ℤ} (hkp : kp ≠ 0)
    {f : Coefficients D} {q : Coefficients E}
    (hp : EqOn (fun x => k*Phi x) (fun x => kr*Psi (e x)) U)
    (hf : ∀ x ∈ U, ∀ theta, (field f k Phi kp (x,theta)).re =
      a * (field q kr Psi kp (e x,theta)).re) :
    CoefficientsOn U e a (HarmonicResidual.realCoefficients f)
      (HarmonicResidual.realCoefficients q) := by
  apply CoefficientsOn.of_fields hkp hp
  intro x hx theta
  simp only [HarmonicResidual.field_realCoefficients, hf x hx theta,
    Complex.real_smul, Complex.ofReal_mul]

omit [NormedAddCommGroup D] [NormedSpace ℝ D] in
theorem realCoefficients_sub (a b : Coefficients D) :
    HarmonicResidual.realCoefficients (a-b) =
      HarmonicResidual.realCoefficients a - HarmonicResidual.realCoefficients b := by
  ext j x
  change HarmonicResidual.realCoefficients (a-b) j x =
    HarmonicResidual.realCoefficients a j x - HarmonicResidual.realCoefficients b j x
  simp only [HarmonicResidual.realCoefficients_apply]
  change (2 : ℂ)⁻¹ * (a j x - b j x + conj (a (-j) x - b (-j) x)) = _
  rw [map_sub]
  ring

/-- Compatibility of a label's primitive fields.  Gaussian and alias inputs
are compared as real fields, exactly as in the physical residual. -/
structure LabelOn (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (d : HarmonicResidual.LabelData D) (r : HarmonicResidual.LabelData E) : Prop where
  phase : EqOn (fun x => d.frequency*d.phase x)
    (fun x => r.frequency*r.phase (e x)) U
  angular : d.angularFrequency = r.angularFrequency
  velocity : ∀ i, CoefficientsOn U e c (d.velocity i) (r.velocity i)
  pressure : CoefficientsOn U e (c*c) d.pressure r.pressure
  gaussian : ∀ i, CoefficientsOn U e (c*c*l)
    (HarmonicResidual.realCoefficients (d.gaussian i))
    (HarmonicResidual.realCoefficients (r.gaussian i))
  aliasError : ∀ i, CoefficientsOn U e (c*c*l)
    (HarmonicResidual.realCoefficients (d.aliasError i))
    (HarmonicResidual.realCoefficients (r.aliasError i))

theorem LabelOn.residualCoefficients {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {d : HarmonicResidual.LabelData D} {r : HarmonicResidual.LabelData E}
    (H : LabelOn U e c l d r) (hU : IsOpen U) (hl : l ≠ 0)
    {g : HarmonicResidual.Frame D} {gr : HarmonicResidual.Frame E}
    (hg : FrameOn U e c l g gr)
    {B M : D → ComplexVector} {Br Mr : E → ComplexVector}
    (hB : ∀ x ∈ U, B x = c • Br (e x))
    (hM : ∀ x ∈ U, M x = c • Mr (e x)) :
    ∀ i, CoefficientsOn U e (c*c*l)
      (d.residualCoefficients g B M i) (r.residualCoefficients gr Br Mr i) := by
  have hbase : ∀ i, CoefficientsOn U e c
      (HarmonicResidual.constantVector (B+M) i)
      (HarmonicResidual.constantVector (Br+Mr) i) := by
    intro i
    apply CoefficientsOn.boundConstant
    intro x hx
    have he := congrArg (fun z : ComplexVector => z i) (congrArg₂ (·+·) (hB x hx) (hM x hx))
    simpa only [Pi.add_apply, Pi.smul_apply, smul_add] using he
  have hn := hg.nonlinearResidual hU hl d.angularFrequency hbase H.velocity H.pressure H.phase
  rw [H.angular] at hn
  intro i
  simp only [HarmonicResidual.LabelData.residualCoefficients, realCoefficients_sub]
  rw [H.angular]
  exact ((hn i).realCoefficients.sub (H.gaussian i)).sub (H.aliasError i)

theorem LabelOn.waveResidualCoefficients {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {d : HarmonicResidual.LabelData D} {r : HarmonicResidual.LabelData E}
    (H : LabelOn U e c l d r) (hU : IsOpen U) (hl : l ≠ 0)
    {g : HarmonicResidual.Frame D} {gr : HarmonicResidual.Frame E}
    (hg : FrameOn U e c l g gr)
    {B M : D → ComplexVector} {Br Mr : E → ComplexVector}
    (hB : ∀ x ∈ U, B x = c • Br (e x))
    (hM : ∀ x ∈ U, M x = c • Mr (e x)) :
    ∀ i, CoefficientsOn U e (c*c*l)
      (d.waveResidualCoefficients g B M i) (r.waveResidualCoefficients gr Br Mr i) :=
  fun i => (H.residualCoefficients hU hl hg hB hM i).nonconstant

/-- Only actual full-lift fields and their carrier are compared here.  In
particular, this does not assume compatibility of an already computed source. -/
structure BlockFieldsOn (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (b : CorrectionState.HarmonicBlock D) (br : CorrectionState.HarmonicBlock E)
    (G A : HarmonicResidual.BlockCoefficients D) (Gr Ar : HarmonicResidual.BlockCoefficients E)
    (n nr : ℕ) : Prop where
  phase : EqOn (fun x => b.frequency n*b.phase n x)
    (fun x => br.frequency nr*br.phase nr (e x)) U
  angular : b.angularFrequency n = br.angularFrequency nr
  angular_ne : b.angularFrequency n ≠ 0
  velocity : ∀ x ∈ U, ∀ theta i, b.oscillation n (x,theta) i =
    c * br.oscillation nr (e x,theta) i
  pressure : ∀ x ∈ U, ∀ theta, b.oscillatoryPressure n (x,theta) =
    (c*c) * br.oscillatoryPressure nr (e x,theta)
  gaussian : ∀ x ∈ U, ∀ theta i,
    (field (G n i) (b.frequency n) (b.phase n) (b.angularFrequency n) (x,theta)).re =
      (c*c*l) * (field (Gr nr i) (br.frequency nr) (br.phase nr)
        (br.angularFrequency nr) (e x,theta)).re
  aliasError : ∀ x ∈ U, ∀ theta i,
    (field (A n i) (b.frequency n) (b.phase n) (b.angularFrequency n) (x,theta)).re =
      (c*c*l) * (field (Ar nr i) (br.frequency nr) (br.phase nr)
        (br.angularFrequency nr) (e x,theta)).re

theorem BlockFieldsOn.labelOn {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {b : CorrectionState.HarmonicBlock D} {br : CorrectionState.HarmonicBlock E}
    {G A : HarmonicResidual.BlockCoefficients D} {Gr Ar : HarmonicResidual.BlockCoefficients E}
    {n nr : ℕ} (H : BlockFieldsOn U e c l b br G A Gr Ar n nr) :
    LabelOn U e c l (HarmonicResidual.ofBlock b G A n) (HarmonicResidual.ofBlock br Gr Ar nr) := by
  have hkp : br.angularFrequency nr ≠ 0 := H.angular ▸ H.angular_ne
  refine ⟨H.phase, H.angular, ?_, ?_, ?_, ?_⟩
  · intro i
    apply CoefficientsOn.of_real_fields hkp H.phase
    intro x hx theta
    have he := H.velocity x hx theta i
    simpa only [CorrectionState.HarmonicBlock.oscillation, H.angular] using he
  · apply CoefficientsOn.of_real_fields hkp H.phase
    intro x hx theta
    have he := H.pressure x hx theta
    simpa only [CorrectionState.HarmonicBlock.oscillatoryPressure, H.angular] using he
  · intro i
    apply CoefficientsOn.of_real_fields hkp H.phase
    intro x hx theta
    have he := H.gaussian x hx theta i
    simp only [H.angular] at he
    exact he
  · intro i
    apply CoefficientsOn.of_real_fields hkp H.phase
    intro x hx theta
    have he := H.aliasError x hx theta i
    simp only [H.angular] at he
    exact he

/-- Exact naturality of the literal source supplied to the Volterra solve. -/
theorem residualSource_naturality {U : Set D} (hU : IsOpen U) {e : D ≃L[ℝ] E}
    {c l : ℝ} (hl : l ≠ 0)
    {C : CorrectionState.Context D} {Cr : CorrectionState.Context E}
    {s : CorrectionState.State D} {sr : CorrectionState.State E}
    {b : CorrectionState.HarmonicBlock D} {br : CorrectionState.HarmonicBlock E}
    {G A : HarmonicResidual.BlockCoefficients D} {Gr Ar : HarmonicResidual.BlockCoefficients E}
    {n nr : ℕ}
    (hg : FrameOn U e c l (HarmonicResidual.contextFrame C n) (HarmonicResidual.contextFrame Cr nr))
    (hB : ∀ x ∈ U, HarmonicResidual.contextBase C n x = c • HarmonicResidual.contextBase Cr nr (e
      x))
    (hM : ∀ x ∈ U, HarmonicResidual.stateMean s n x = c • HarmonicResidual.stateMean sr nr (e x))
    (H : BlockFieldsOn U e c l b br G A Gr Ar n nr)
    (j : ℤ) {x : D} (hx : x ∈ U) :
    ParticularWaveAssembly.residualSource C s b G A j n x =
      (c*c*l) • ParticularWaveAssembly.residualSource Cr sr br Gr Ar j nr (e x) := by
  ext i
  exact H.labelOn.waveResidualCoefficients hU hl hg hB hM i j x hx

/-! ## The concrete common-cover chart -/

open PhysicalParticularWave CommonCoverSolve

abbrev Lift := PhysicalResidualBridge.Lift
abbrev Associated := PhysicalParticularWave.Parameter × TorusInverse.Plane

/-- The invertible real-lift map underlying the integer torus cover. -/
noncomputable def chartEquiv (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) : Lift ≃L[ℝ] Lift :=
  (scalarEquiv ℝ (ratioPower Q Qr (1/2)) (ratioPower_pos hQ hQr _).ne').prodCongr
    (((scalarEquiv ℝ (ratioPower Q Qr (CoordinateAlgebra.D h)) (ratioPower_pos hQ hQr
      _).ne').prodCongr
      (scalarEquiv ℝ (ratioPower Q Qr 1) (ratioPower_pos hQ hQr _).ne')).prodCongr (coverPower gap))

@[simp] theorem chartEquiv_apply (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) (x : Lift) : chartEquiv h hQ hQr gap x = chartChange h Q Qr gap x := rfl

/-- Actual graph directions on the free lift, before adjoining the angle. -/
noncomputable def commonFrame (h Q : ℝ) (i : ℕ) : HarmonicResidual.Frame Lift where
  radius := Prod.fst
  radial x := ((PhysicalResidualBridge.commonGraph Q h i).radial (x,0)).1
  axial x := ((PhysicalResidualBridge.commonGraph Q h i).axial (x,0)).1
  time x := ((PhysicalResidualBridge.commonGraph Q h i).temporal (x,0)).1
  viscosity := Q ^ h

theorem weight_time {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    velocityWeight h Q Qr * ratioPower Q Qr (1/2) = clockWeight h Q Qr :=
  ratioPower_mul hQ hQr _ _

theorem weight_pressure {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    velocityWeight h Q Qr * velocityWeight h Q Qr = pressureWeight h Q Qr := by
  unfold velocityWeight pressureWeight
  rw [ratioPower_mul hQ hQr]
  congr 1
  ring

theorem weight_source {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    velocityWeight h Q Qr * velocityWeight h Q Qr * ratioPower Q Qr (1/2) =
      sourceWeight h Q Qr := by
  rw [mul_assoc, weight_time hQ hQr, mul_comm, clock_mul_velocity hQ hQr]

theorem weight_viscosity {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (h : ℝ) :
    Q ^ h * ratioPower Q Qr (1/2) = velocityWeight h Q Qr * Qr ^ h := by
  change Q ^ h * (Q ^ (1/2 : ℝ) / Qr ^ (1/2 : ℝ)) =
    (Q ^ CoordinateAlgebra.A h / Qr ^ CoordinateAlgebra.A h) * Qr ^ h
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_eq_div_iff (Real.rpow_pos_of_pos hQr (1/2)).ne'
    (Real.rpow_pos_of_pos hQr (CoordinateAlgebra.A h)).ne').2
  rw [← Real.rpow_add hQ]
  have ha : h + (1/2 : ℝ) = CoordinateAlgebra.A h := by unfold CoordinateAlgebra.A; ring
  rw [ha]
  calc
    _ = Q ^ CoordinateAlgebra.A h * (Qr ^ h * Qr ^ (1/2 : ℝ)) := by
      rw [← Real.rpow_add hQr, ha]
    _ = _ := by ring

theorem commonFrame_chart (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (i gap : ℕ) :
    FrameOn {x : Lift | 0 < x.1} (chartEquiv h hQ hQr gap)
      (velocityWeight h Q Qr) (ratioPower Q Qr (1/2))
      (commonFrame h Q i) (commonFrame h Qr (i+gap)) := by
  constructor
  · intro x hx
    exact congrArg Prod.fst (cylinderChange_radial hQ hQr h i gap (x := (x,0)) hx)
  · intro x hx
    exact congrArg Prod.fst (cylinderChange_axial hQ hQr h i gap (x,0))
  · intro x hx
    rw [weight_time hQ hQr]
    exact congrArg Prod.fst (cylinderChange_temporal hQ hQr h i gap (x,0))
  · intro x hx
    rfl
  · exact weight_viscosity hQ hQr h

/-- Association and the `(T,Z)` order used by the correction state. -/
noncomputable def associatedToLift : Associated ≃ₗᵢ[ℝ] Lift :=
  (ParticularWaveBounds.liftAssoc TorusInverse.Plane).symm.trans PhysicalResidualTZ.swapSlow

@[simp] theorem associatedToLift_apply (x : Associated) :
    associatedToLift x = (x.1.1, ((x.1.2.2,x.1.2.1),x.2)) := rfl

noncomputable def associatedChart (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) : Associated ≃L[ℝ] Associated :=
  (associatedToLift.toContinuousLinearEquiv.trans (chartEquiv h hQ hQr gap)).trans
    associatedToLift.symm.toContinuousLinearEquiv

@[simp] theorem associatedChart_apply (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (gap : ℕ) (x : Associated) :
    associatedChart h hQ hQr gap x = (parameterChange h Q Qr x.1, coverPower gap x.2) := rfl

noncomputable def associatedFrame (h Q : ℝ) (i : ℕ) : HarmonicResidual.Frame Associated :=
  StateReindex.frame associatedToLift (commonFrame h Q i)

theorem associatedFrame_chart (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr)
    (i gap : ℕ) :
    FrameOn {x : Associated | 0 < x.1.1} (associatedChart h hQ hQr gap)
      (velocityWeight h Q Qr) (ratioPower Q Qr (1/2))
      (associatedFrame h Q i) (associatedFrame h Qr (i+gap)) := by
  have H := commonFrame_chart h hQ hQr i gap
  constructor
  · intro x hx
    apply associatedToLift.injective
    simpa only [associatedChart, associatedFrame, StateReindex.frame, StateReindex.vector,
      ParticularWaveBounds.reindexVector, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.map_smul] using H.radial (associatedToLift x) hx
  · intro x hx
    apply associatedToLift.injective
    simpa only [associatedChart, associatedFrame, StateReindex.frame, StateReindex.vector,
      ParticularWaveBounds.reindexVector, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.map_smul] using H.axial (associatedToLift x) hx
  · intro x hx
    apply associatedToLift.injective
    simpa only [associatedChart, associatedFrame, StateReindex.frame, StateReindex.vector,
      ParticularWaveBounds.reindexVector, ContinuousLinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.apply_symm_apply,
      LinearIsometryEquiv.map_smul] using H.time (associatedToLift x) hx
  · intro x hx
    rfl
  · exact H.viscosity

/-- The positive-radius free lift.  Every auxiliary variable remains free. -/
def positiveLift : Set Associated := {x | 0 < x.1.1}

theorem positiveLift_open : IsOpen positiveLift := isOpen_lt continuous_const continuous_fst.fst

/-- Concrete primitive coherence needed by a band solve.  These are field,
phase, and explicit operator identities, never an identity of residuals or
of solved waves. -/
structure BandCoherence (D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter)
    (h : ℝ) {Q Qr : ℝ} (hQ : 0 < Q) (hQr : 0 < Qr) (i gap n : ℕ) : Prop where
  targetFrame : HarmonicResidual.contextFrame D.context n = associatedFrame h Q i
  referenceFrame : HarmonicResidual.contextFrame D.context D.reference.band =
    associatedFrame h Qr (i+gap)
  base : ∀ x ∈ positiveLift, HarmonicResidual.contextBase D.context n x =
    velocityWeight h Q Qr • HarmonicResidual.contextBase D.context D.reference.band
      (associatedChart h hQ hQr gap x)
  mean : ∀ x ∈ positiveLift, HarmonicResidual.stateMean D.state n x =
    velocityWeight h Q Qr • HarmonicResidual.stateMean D.state D.reference.band
      (associatedChart h hQ hQr gap x)
  block : BlockFieldsOn positiveLift (associatedChart h hQ hQr gap)
    (velocityWeight h Q Qr) (ratioPower Q Qr (1/2))
    D.carrierBlock D.carrierBlock D.gaussianInput D.aliasInput D.gaussianInput D.aliasInput
    n D.reference.band

theorem BandCoherence.source_on
    {D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter}
    {h Q Qr : ℝ} {hQ : 0 < Q} {hQr : 0 < Qr} {i gap n : ℕ}
    (H : BandCoherence D h hQ hQr i gap n) (j : ℤ) {x : Associated} (hx : x ∈ positiveLift) :
    ParticularWaveAssembly.residualSource D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j n x = transportedResidualSource D h Q Qr gap j x := by
  have hf : FrameOn positiveLift (associatedChart h hQ hQr gap)
      (velocityWeight h Q Qr) (ratioPower Q Qr (1/2))
      (HarmonicResidual.contextFrame D.context n)
      (HarmonicResidual.contextFrame D.context D.reference.band) := by
    rw [H.targetFrame, H.referenceFrame]
    exact associatedFrame_chart h hQ hQr i gap
  have he := residualSource_naturality positiveLift_open (ratioPower_pos hQ hQr (1/2)).ne'
    hf H.base H.mean H.block j hx
  rw [weight_source hQ hQr] at he
  rw [transportedResidualSource_apply D h hQ hQr]
  exact he

/-- Primitive support assumptions, allowing arbitrary zero-mode aliases. -/
structure PositiveSupport (b : CorrectionState.HarmonicBlock Associated)
    (G A : HarmonicResidual.BlockCoefficients Associated) (n : ℕ) where
  supportSet : Set Associated
  closed : IsClosed supportSet
  positive : supportSet ⊆ positiveLift
  velocity : ∀ i, HarmonicSourceSupport.NonzeroSupported supportSet
    (HarmonicResidual.realCoefficients (b.velocity n i))
  pressure : HarmonicSourceSupport.NonzeroSupported supportSet
    (HarmonicResidual.realCoefficients (b.pressure n))
  gaussian : ∀ i, HarmonicSourceSupport.NonzeroSupported supportSet
    (HarmonicResidual.realCoefficients (G n i))
  aliasError : ∀ i, HarmonicSourceSupport.NonzeroSupported supportSet
    (HarmonicResidual.realCoefficients (A n i))

theorem PositiveSupport.source_zero
    {b : CorrectionState.HarmonicBlock Associated}
    {G A : HarmonicResidual.BlockCoefficients Associated} {n : ℕ}
    (H : PositiveSupport b G A n) (C : CorrectionState.Context Associated)
    (s : CorrectionState.State Associated) (j : ℤ) {x : Associated} (hx : x ∉ positiveLift) :
    ParticularWaveAssembly.residualSource C s b G A j n x = 0 := by
  have hs := HarmonicSourceSupport.residualSource_support_of_real C s b G A H.closed n
    H.velocity H.pressure H.gaussian H.aliasError j
  by_contra hn
  exact hx (H.positive (hs hn))

/-- Full free-variable equality, including the complement of the annular
cells, derived from primitive field coherence and primitive support. -/
theorem BandCoherence.source_eq
    {D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter}
    {h Q Qr : ℝ} {hQ : 0 < Q} {hQr : 0 < Qr} {i gap n : ℕ}
    (H : BandCoherence D h hQ hQr i gap n)
    (hn : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band) (j : ℤ) :
    ParticularWaveAssembly.residualSource D.context D.state D.carrierBlock
      D.gaussianInput D.aliasInput j n = transportedResidualSource D h Q Qr gap j := by
  funext x
  by_cases hx : x ∈ positiveLift
  · exact H.source_on j hx
  · rw [hn.source_zero D.context D.state j hx, transportedResidualSource_apply D h hQ hQr]
    have hyr : (parameterChange h Q Qr x.1, coverPower gap x.2) ∉ positiveLift := by
      intro hy
      apply hx
      exact (mul_pos_iff_of_pos_left (ratioPower_pos hQ hQr (1/2))).mp hy
    rw [referenceSource, hr.source_zero D.context D.state j hyr, smul_zero]

/-- The actual target-source Volterra solve is the coherently transported
one; no equality of outputs is supplied as an assumption. -/
theorem BandCoherence.residualBandAmplitude_eq
    {D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter}
    {h Q Qr : ℝ} {hQ : 0 < Q} {hQr : 0 < Qr} {i gap n : ℕ}
    (H : BandCoherence D h hQ hQr i gap n)
    (hn : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
    (K : ℝ) (j : ℤ) :
    residualBandAmplitude D h hQ hQr gap K j n = bandAmplitude D h hQ hQr gap K j :=
  PhysicalParticularWave.residualBandAmplitude_eq D h hQ hQr gap K j n (H.source_eq hn hr j)

theorem BandCoherence.residualBandPressure_eq
    {D : ParticularWaveAssembly.AssemblyData PhysicalParticularWave.Parameter}
    {h Q Qr : ℝ} {hQ : 0 < Q} {hQr : 0 < Qr} {i gap n : ℕ}
    (H : BandCoherence D h hQ hQr i gap n)
    (hn : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput n)
    (hr : PositiveSupport D.carrierBlock D.gaussianInput D.aliasInput D.reference.band)
    (K : ℝ) (j : ℤ) :
    residualBandPressure D h hQ hQr gap K j n = bandPressure D h hQ hQr gap K j :=
  PhysicalParticularWave.residualBandPressure_eq D h hQ hQr gap K j n (H.source_eq hn hr j)

/-! ## A lift-coherence invariant preserved by actual state addition -/

def ScalarOn (U : Set D) (e : D ≃L[ℝ] E) (a : ℝ) (f : D → ℝ) (g : E → ℝ) : Prop :=
  ∀ x ∈ U, f x = a * g (e x)

namespace ScalarOn

theorem reweight {U : Set D} {e : D ≃L[ℝ] E} {a b : ℝ} {f : D → ℝ} {g : E → ℝ}
    (hf : ScalarOn U e a f g) (hab : a = b) : ScalarOn U e b f g := hab ▸ hf

theorem add {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ} {f v : D → ℝ} {g w : E → ℝ}
    (hf : ScalarOn U e a f g) (hv : ScalarOn U e a v w) : ScalarOn U e a (f+v) (g+w) := by
  intro x hx
  change f x + v x = a * (g (e x) + w (e x))
  rw [hf x hx, hv x hx, mul_add]

theorem sub {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ} {f v : D → ℝ} {g w : E → ℝ}
    (hf : ScalarOn U e a f g) (hv : ScalarOn U e a v w) : ScalarOn U e a (f-v) (g-w) := by
  intro x hx
  change f x - v x = a * (g (e x) - w (e x))
  rw [hf x hx, hv x hx, mul_sub]

theorem mul {U : Set D} {e : D ≃L[ℝ] E} {a b : ℝ} {f v : D → ℝ} {g w : E → ℝ}
    (hf : ScalarOn U e a f g) (hv : ScalarOn U e b v w) : ScalarOn U e (a*b) (f*v) (g*w) := by
  intro x hx
  change f x * v x = (a*b) * (g (e x) * w (e x))
  rw [hf x hx, hv x hx]
  ring

theorem smul {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ} {f : D → ℝ} {g : E → ℝ}
    (hf : ScalarOn U e a f g) (b : ℝ) : ScalarOn U e a (b • f) (b • g) := by
  intro x hx
  change b * f x = a * (b * g (e x))
  rw [hf x hx]
  ring

theorem along {U : Set D} (hU : IsOpen U) {e : D ≃L[ℝ] E} {a b : ℝ}
    {f : D → ℝ} {g : E → ℝ} {V : D → D} {W : E → E}
    (hf : ScalarOn U e a f g) (hV : ∀ x ∈ U, e (V x) = b • W (e x)) :
    ScalarOn U e (a*b) (HarmonicCalculus.along V f) (HarmonicCalculus.along W g) := by
  intro x hx
  have he : f =ᶠ[𝓝 x] (fun y => a • g (e y)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hf y hy
  change (fderiv ℝ f x) (V x) = _
  rw [he.fderiv_eq]
  exact along_pull e a b V W g x (hV x hx)

end ScalarOn

structure TripleOn (U : Set D) (e : D ≃L[ℝ] E) (a : ℝ)
    (f : MeanIncrementBounds.Triple D) (g : MeanIncrementBounds.Triple E) (n nr : ℕ) : Prop where
  radial : ScalarOn U e a (f.radial n) (g.radial nr)
  angular : ScalarOn U e a (f.angular n) (g.angular nr)
  axial : ScalarOn U e a (f.axial n) (g.axial nr)

theorem TripleOn.updated {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {f v : MeanIncrementBounds.Triple D} {g w : MeanIncrementBounds.Triple E} {n nr : ℕ}
    (hf : TripleOn U e a f g n nr) (hv : TripleOn U e a v w n nr) :
    TripleOn U e a (MeanIncrementBounds.updated f v) (MeanIncrementBounds.updated g w) n nr :=
  ⟨hf.radial.add hv.radial, hf.angular.add hv.angular, hf.axial.add hv.axial⟩

/-- A full free-lift invariant on the actual state fields.  It is stronger
than graph-only physical representation and is closed under addition. -/
structure StateOn (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (s : CorrectionState.State D) (r : CorrectionState.State E) (n nr : ℕ) : Prop where
  mean : TripleOn U e c s.mean r.mean n nr
  pressure : ScalarOn U e (c*c) (s.pressure n) (r.pressure nr)
  oscillation : ∀ x ∈ U, ∀ theta i, s.oscillation n (x,theta) i =
    c * r.oscillation nr (e x,theta) i
  oscillatoryPressure : ∀ x ∈ U, ∀ theta, s.oscillatoryPressure n (x,theta) =
    (c*c) * r.oscillatoryPressure nr (e x,theta)
  baseError : ∀ x ∈ U, ∀ theta i, s.errors.base n (x,theta) i =
    (c*c*l) * r.errors.base nr (e x,theta) i
  gaussian : ∀ x ∈ U, ∀ theta i, s.errors.gaussian n (x,theta) i =
    (c*c*l) * r.errors.gaussian nr (e x,theta) i
  aliasError : ∀ x ∈ U, ∀ theta i, s.errors.aliasError n (x,theta) i =
    (c*c*l) * r.errors.aliasError nr (e x,theta) i

theorem StateOn.addIncrement {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {s v : CorrectionState.State D} {r w : CorrectionState.State E} {n nr : ℕ}
    (hs : StateOn U e c l s r n nr) (hv : StateOn U e c l v w n nr) :
    StateOn U e c l
      (s.addIncrement v.mean v.pressure v.oscillation v.oscillatoryPressure v.errors)
      (r.addIncrement w.mean w.pressure w.oscillation w.oscillatoryPressure w.errors) n nr := by
  refine ⟨hs.mean.updated hv.mean, hs.pressure.add hv.pressure, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx theta i
    change s.oscillation n (x,theta) i + v.oscillation n (x,theta) i = _
    rw [hs.oscillation x hx theta i, hv.oscillation x hx theta i]
    exact (mul_add _ _ _).symm
  · intro x hx theta
    change s.oscillatoryPressure n (x,theta) + v.oscillatoryPressure n (x,theta) = _
    rw [hs.oscillatoryPressure x hx theta, hv.oscillatoryPressure x hx theta]
    exact (mul_add _ _ _).symm
  · intro x hx theta i
    change s.errors.base n (x,theta) i + v.errors.base n (x,theta) i = _
    rw [hs.baseError x hx theta i, hv.baseError x hx theta i]
    exact (mul_add _ _ _).symm
  · intro x hx theta i
    change s.errors.gaussian n (x,theta) i + v.errors.gaussian n (x,theta) i = _
    rw [hs.gaussian x hx theta i, hv.gaussian x hx theta i]
    exact (mul_add _ _ _).symm
  · intro x hx theta i
    change s.errors.aliasError n (x,theta) i + v.errors.aliasError n (x,theta) i = _
    rw [hs.aliasError x hx theta i, hv.aliasError x hx theta i]
    exact (mul_add _ _ _).symm

theorem StateOn.covariance {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn U e c l s r n nr) (i j : Fin 3) :
    ScalarOn U e (c*c) (s.covariance i j n) (r.covariance i j nr) := by
  intro x hx
  simp only [CorrectionState.State.covariance, CorrectionState.bilinearCovariance,
    CorrectionState.angularAverage]
  have he : (fun theta => s.oscillation n (x,theta) i * s.oscillation n (x,theta) j) =
      fun theta => (c*c) * (r.oscillation nr (e x,theta) i * r.oscillation nr (e x,theta) j) := by
    funext theta
    rw [H.oscillation x hx theta i, H.oscillation x hx theta j]
    ring
  rw [he, intervalIntegral.integral_const_mul]
  ring

theorem dr_eq_along (C : CorrectionState.Context D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : C.operators.dr f n x =
      HarmonicCalculus.along (HarmonicResidual.contextFrame C n).radial (f n) x := by
  simp only [MeanIncrementBounds.Operators.dr, WeightedClasses.graphDerivative,
    HarmonicResidual.contextFrame, HarmonicCalculus.along, map_add, map_smul, smul_eq_mul]
  ring

theorem dz_eq_along (C : CorrectionState.Context D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : C.operators.dz f n x =
      HarmonicCalculus.along (HarmonicResidual.contextFrame C n).axial (f n) x := by
  simp only [MeanIncrementBounds.Operators.dz, HarmonicResidual.contextFrame,
    HarmonicCalculus.along, map_smul, smul_eq_mul]

theorem time_eq_along (C : CorrectionState.Context D) (f : MeanIncrementBounds.Field D)
    (n : ℕ) (x : D) : C.operators.time f n x =
      HarmonicCalculus.along (HarmonicResidual.contextFrame C n).time (f n) x := by
  simp only [MeanIncrementBounds.Operators.time, MeanIncrementBounds.Operators.slowTime,
    MeanIncrementBounds.Operators.fastTime, Pi.add_apply, HarmonicResidual.contextFrame,
    HarmonicCalculus.along, map_sub, map_smul, smul_eq_mul]
  ring

namespace FrameOn

variable {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
  {C : CorrectionState.Context D} {Cr : CorrectionState.Context E} {n nr : ℕ}
  (H : FrameOn U e c l (HarmonicResidual.contextFrame C n) (HarmonicResidual.contextFrame Cr nr))

include H

theorem scalarDr (hU : IsOpen U) {a : ℝ} {f : MeanIncrementBounds.Field D}
    {g : MeanIncrementBounds.Field E} (hf : ScalarOn U e a (f n) (g nr)) :
    ScalarOn U e (a*l) (C.operators.dr f n) (Cr.operators.dr g nr) := by
  intro x hx
  simpa only [dr_eq_along] using hf.along hU H.radial x hx

theorem scalarDz (hU : IsOpen U) {a : ℝ} {f : MeanIncrementBounds.Field D}
    {g : MeanIncrementBounds.Field E} (hf : ScalarOn U e a (f n) (g nr)) :
    ScalarOn U e (a*l) (C.operators.dz f n) (Cr.operators.dz g nr) := by
  intro x hx
  simpa only [dz_eq_along] using hf.along hU H.axial x hx

theorem scalarTime (hU : IsOpen U) {a : ℝ} {f : MeanIncrementBounds.Field D}
    {g : MeanIncrementBounds.Field E} (hf : ScalarOn U e a (f n) (g nr)) :
    ScalarOn U e (a*(c*l)) (C.operators.time f n) (Cr.operators.time g nr) := by
  intro x hx
  simpa only [time_eq_along] using hf.along hU H.time x hx

theorem scalarInvRadius (hl : l ≠ 0) :
    ScalarOn U e l (C.operators.invRadius n) (Cr.operators.invRadius nr) := by
  intro x hx
  have he := H.inverseRadius hl 0 x hx
  simp only [constantCoefficient, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Complex.real_smul,
    ← Complex.ofReal_mul, Complex.ofReal_inj] at he
  exact he

theorem scalarRadialDiv (hU : IsOpen U) (hl : l ≠ 0) {a : ℝ}
    {f : MeanIncrementBounds.Field D} {g : MeanIncrementBounds.Field E}
    (hf : ScalarOn U e a (f n) (g nr)) (b : ℝ) :
    ScalarOn U e (a*l) (C.operators.radialDiv b f n) (Cr.operators.radialDiv b g nr) := by
  have hprod := ((H.scalarInvRadius hl).mul hf).reweight (mul_comm l a)
  exact (H.scalarDr hU hf).add (hprod.smul b)

theorem scalarViscosity (hU : IsOpen U) (hl : l ≠ 0) {a : ℝ}
    {f : MeanIncrementBounds.Field D} {g : MeanIncrementBounds.Field E}
    (hf : ScalarOn U e a (f n) (g nr)) (b : ℝ) :
    ScalarOn U e (a*c*l) (C.operators.viscosity b f n) (Cr.operators.viscosity b g nr) := by
  have hrr := (H.scalarDr hU (H.scalarDr hU hf)).reweight (b := a*(l*l)) (by ring)
  have hr := ((H.scalarInvRadius hl).mul (H.scalarDr hU hf)).reweight (b := a*(l*l)) (by ring)
  have hzz := (H.scalarDz hU (H.scalarDz hU hf)).reweight (b := a*(l*l)) (by ring)
  have hi := ((H.scalarInvRadius hl).mul ((H.scalarInvRadius hl).mul hf)).reweight
    (b := a*(l*l)) (by ring)
  have hsum := ((hrr.add hr).add hzz).sub (hi.smul b)
  intro x hx
  simp only [MeanIncrementBounds.Operators.viscosity]
  have he := hsum x hx
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at he
  rw [he]
  have hvis : C.operators.epsilon n * l = c * Cr.operators.epsilon nr := H.viscosity
  calc
    _ = a*l*(C.operators.epsilon n*l) *
      (Cr.operators.dr (Cr.operators.dr g) nr (e x) +
        Cr.operators.invRadius nr (e x) * Cr.operators.dr g nr (e x) +
        Cr.operators.dz (Cr.operators.dz g) nr (e x) -
        b*(Cr.operators.invRadius nr (e x)*(Cr.operators.invRadius nr (e x)*g nr (e x)))) := by ring
    _ = _ := by rw [hvis]; ring

end FrameOn

namespace TripleOn

variable {U : Set D} {e : D ≃L[ℝ] E} {c : ℝ} {n nr : ℕ}
  {b m : MeanIncrementBounds.Triple D} {br mr : MeanIncrementBounds.Triple E}

theorem thetaRadial (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.thetaRadial b m n) (MeanIncrementBounds.thetaRadial br
      mr nr) :=
  ((hb.radial.mul hm.angular).add (hm.radial.mul hb.angular)).add (hm.radial.mul hm.angular)

theorem thetaAxial (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.thetaAxial b m n) (MeanIncrementBounds.thetaAxial br mr
      nr) :=
  ((hb.axial.mul hm.angular).add (hb.angular.mul hm.axial)).add (hm.axial.mul hm.angular)

theorem axialRadial (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.axialRadial b m n) (MeanIncrementBounds.axialRadial br
      mr nr) :=
  ((hb.radial.mul hm.axial).add (hm.radial.mul hb.axial)).add (hm.radial.mul hm.axial)

theorem axialAxial (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.axialAxial b m n) (MeanIncrementBounds.axialAxial br mr
      nr) :=
  ((hb.axial.mul hm.axial).smul 2).add (hm.axial.mul hm.axial)

theorem radialRadial (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.radialRadial b m n) (MeanIncrementBounds.radialRadial
      br mr nr) :=
  ((hb.radial.mul hm.radial).smul 2).add (hm.radial.mul hm.radial)

theorem radialAngular (hb : TripleOn U e c b br n nr) (hm : TripleOn U e c m mr n nr) :
    ScalarOn U e (c*c) (MeanIncrementBounds.radialAngular b m n) (MeanIncrementBounds.radialAngular
      br mr nr) :=
  ((hb.angular.mul hm.angular).smul 2).add (hm.angular.mul hm.angular)

theorem complexValue (H : TripleOn U e c b br n nr) (x : D) (hx : x ∈ U) :
    (![(b.radial n x : ℂ), (b.angular n x : ℂ), (b.axial n x : ℂ)] : ComplexVector) =
      c • ![(br.radial nr (e x) : ℂ), (br.angular nr (e x) : ℂ), (br.axial nr (e x) : ℂ)] := by
  ext i
  fin_cases i <;> simp [H.radial x hx, H.angular x hx, H.axial x hx, Complex.real_smul]

end TripleOn

/-- Context coherence includes the actual virtual stress fields, not just
the velocity carried by a state. -/
structure ContextOn (U : Set D) (e : D ≃L[ℝ] E) (c l : ℝ)
    (C : CorrectionState.Context D) (Cr : CorrectionState.Context E) (n nr : ℕ) : Prop where
  frame : FrameOn U e c l (HarmonicResidual.contextFrame C n) (HarmonicResidual.contextFrame Cr nr)
  base : TripleOn U e c C.base Cr.base n nr
  virtualTheta : ScalarOn U e (c*c) (C.virtualTheta n) (Cr.virtualTheta nr)
  virtualAxial : ScalarOn U e (c*c) (C.virtualAxial n) (Cr.virtualAxial nr)

namespace StateOn

variable {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
  {C : CorrectionState.Context D} {Cr : CorrectionState.Context E}
  {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
  (H : StateOn U e c l s r n nr) (G : ContextOn U e c l C Cr n nr)

include H G

/-- Naturality of the genuine angular mean residual, including the
recomputed covariance and virtual stress divergence. -/
theorem thetaResidual (hU : IsOpen U) (hl : l ≠ 0) :
    ScalarOn U e (c*c*l) (s.thetaResidual C n) (r.thetaResidual Cr nr) := by
  have ht := (G.frame.scalarTime hU H.mean.angular).reweight (b := c*c*l) (by ring)
  have hr := G.frame.scalarRadialDiv hU hl
    (f := MeanIncrementBounds.thetaRadial C.base s.mean + s.covariance 0 1)
    (g := MeanIncrementBounds.thetaRadial Cr.base r.mean + r.covariance 0 1)
    ((G.base.thetaRadial H.mean).add (H.covariance 0 1)) 2
  have hz := G.frame.scalarDz hU
    (f := MeanIncrementBounds.thetaAxial C.base s.mean + s.covariance 2 1)
    (g := MeanIncrementBounds.thetaAxial Cr.base r.mean + r.covariance 2 1)
    ((G.base.thetaAxial H.mean).add (H.covariance 2 1))
  have hv := G.frame.scalarViscosity hU hl H.mean.angular 1
  have hs := G.frame.scalarRadialDiv hU hl G.virtualTheta 2
  exact (((ht.add hr).add hz).sub hv).sub hs

/-- Naturality of the genuine axial mean residual, with pressure retained. -/
theorem axialResidual (hU : IsOpen U) (hl : l ≠ 0) :
    ScalarOn U e (c*c*l) (s.axialResidual C n) (r.axialResidual Cr nr) := by
  have ht := (G.frame.scalarTime hU H.mean.axial).reweight (b := c*c*l) (by ring)
  have hr := G.frame.scalarRadialDiv hU hl
    (f := MeanIncrementBounds.axialRadial C.base s.mean + s.covariance 0 2)
    (g := MeanIncrementBounds.axialRadial Cr.base r.mean + r.covariance 0 2)
    ((G.base.axialRadial H.mean).add (H.covariance 0 2)) 1
  have hz := G.frame.scalarDz hU
    (f := MeanIncrementBounds.axialAxial C.base s.mean + s.covariance 2 2 + s.pressure)
    (g := MeanIncrementBounds.axialAxial Cr.base r.mean + r.covariance 2 2 + r.pressure)
    (((G.base.axialAxial H.mean).add (H.covariance 2 2)).add H.pressure)
  have hv := G.frame.scalarViscosity hU hl H.mean.axial 0
  have hs := G.frame.scalarRadialDiv hU hl G.virtualAxial 1
  exact (((ht.add hr).add hz).sub hv).sub hs

theorem gr (hU : IsOpen U) (hl : l ≠ 0) :
    ScalarOn U e (c*c*l) (s.gr C n) (r.gr Cr nr) := by
  have ht := (G.frame.scalarTime hU H.mean.radial).reweight (b := c*c*l) (by ring)
  have hr := G.frame.scalarRadialDiv hU hl
    (f := MeanIncrementBounds.radialRadial C.base s.mean + s.covariance 0 0)
    (g := MeanIncrementBounds.radialRadial Cr.base r.mean + r.covariance 0 0)
    ((G.base.radialRadial H.mean).add (H.covariance 0 0)) 1
  have hz := G.frame.scalarDz hU
    (f := MeanIncrementBounds.axialRadial C.base s.mean + s.covariance 2 0)
    (g := MeanIncrementBounds.axialRadial Cr.base r.mean + r.covariance 2 0)
    ((G.base.axialRadial H.mean).add (H.covariance 2 0))
  have ha := ((G.frame.scalarInvRadius hl).mul
    ((G.base.radialAngular H.mean).add (H.covariance 1 1))).reweight (b := c*c*l) (by ring)
  have hv := G.frame.scalarViscosity hU hl H.mean.radial 1
  have he := ((((ht.add hr).add hz).sub ha).sub hv).smul (-1)
  simp only [neg_one_smul] at he
  exact he

theorem radialResidual (hU : IsOpen U) (hl : l ≠ 0) :
    ScalarOn U e (c*c*l) (s.radialResidual C n) (r.radialResidual Cr nr) :=
  (G.frame.scalarDr hU H.pressure).sub (H.gr G hU hl)

theorem reducedMeanResidual (hU : IsOpen U) (hl : l ≠ 0) (i : Fin 3) :
    ScalarOn U e (c*c*l) (fun x => s.reducedMeanResidual C n x i)
      (fun x => r.reducedMeanResidual Cr nr x i) := by
  fin_cases i
  · exact H.radialResidual G hU hl
  · exact H.thetaResidual G hU hl
  · exact H.axialResidual G hU hl

theorem source (hU : IsOpen U) (hl : l ≠ 0)
    {b : CorrectionState.HarmonicBlock D} {br : CorrectionState.HarmonicBlock E}
    {ga al : HarmonicResidual.BlockCoefficients D} {gar alr : HarmonicResidual.BlockCoefficients E}
    (hb : BlockFieldsOn U e c l b br ga al gar alr n nr) (j : ℤ) {x : D} (hx : x ∈ U) :
    ParticularWaveAssembly.residualSource C s b ga al j n x =
      (c*c*l) • ParticularWaveAssembly.residualSource Cr r br gar alr j nr (e x) :=
  residualSource_naturality hU hl G.frame G.base.complexValue H.mean.complexValue hb j hx

end StateOn

theorem angularAverage_on {U : Set D} {e : D ≃L[ℝ] E} {a : ℝ}
    {f : CorrectionState.OscillatoryScalar D} {g : CorrectionState.OscillatoryScalar E} {n nr : ℕ}
    (hf : ∀ x ∈ U, ∀ theta, f n (x,theta) = a * g nr (e x,theta)) :
    ScalarOn U e a (CorrectionState.angularAverage f n) (CorrectionState.angularAverage g nr) := by
  intro x hx
  unfold CorrectionState.angularAverage
  rw [show (fun theta => f n (x,theta)) = (fun theta => a*g nr (e x,theta)) from funext (hf x hx),
    intervalIntegral.integral_const_mul]
  ring

theorem StateOn.meanBaseError {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn U e c l s r n nr) (i : Fin 3) :
    ScalarOn U e (c*c*l) (fun x => s.meanBaseError n x i) (fun x => r.meanBaseError nr x i) :=
  angularAverage_on (fun x hx theta => H.baseError x hx theta i)

theorem StateOn.meanExcluded {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn U e c l s r n nr) (i : Fin 3) :
    ScalarOn U e (c*c*l) (fun x => s.meanExcluded n x i) (fun x => r.meanExcluded nr x i) := by
  apply angularAverage_on
  intro x hx theta
  simp only [CorrectionState.ExcludedErrors.total, Pi.add_apply,
    H.baseError x hx theta i, H.gaussian x hx theta i, H.aliasError x hx theta i]
  ring

theorem StateOn.meanResidual {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {C : CorrectionState.Context D} {Cr : CorrectionState.Context E}
    {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn U e c l s r n nr) (G : ContextOn U e c l C Cr n nr)
    (hU : IsOpen U) (hl : l ≠ 0) (i : Fin 3) :
    ScalarOn U e (c*c*l) (fun x => s.meanResidual C n x i) (fun x => r.meanResidual Cr nr x i) :=
  (H.reducedMeanResidual G hU hl i).add (H.meanBaseError i)

theorem StateOn.meanGoodResidual {U : Set D} {e : D ≃L[ℝ] E} {c l : ℝ}
    {C : CorrectionState.Context D} {Cr : CorrectionState.Context E}
    {s : CorrectionState.State D} {r : CorrectionState.State E} {n nr : ℕ}
    (H : StateOn U e c l s r n nr) (G : ContextOn U e c l C Cr n nr)
    (hU : IsOpen U) (hl : l ≠ 0) (i : Fin 3) :
    ScalarOn U e (c*c*l) (fun x => s.meanGoodResidual C n x i) (fun x => r.meanGoodResidual Cr nr x
      i) :=
  (H.meanResidual G hU hl i).sub (H.meanExcluded i)

/-! ## Literal reference views of one state -/

/-- The state is stored once on the reference lift.  Band values are
constructed by pullback, rather than chosen independently. -/
noncomputable def stateView (e : ℕ → D ≃L[ℝ] E) (c l : ℕ → ℝ)
    (r : CorrectionState.State E) (nr : ℕ) : CorrectionState.State D where
  mean :=
    { radial := fun n x => c n * r.mean.radial nr (e n x)
      angular := fun n x => c n * r.mean.angular nr (e n x)
      axial := fun n x => c n * r.mean.axial nr (e n x) }
  pressure n x := (c n*c n) * r.pressure nr (e n x)
  oscillation n x i := c n * r.oscillation nr (e n x.1,x.2) i
  oscillatoryPressure n x := (c n*c n) * r.oscillatoryPressure nr (e n x.1,x.2)
  errors :=
    { base := fun n x i => (c n*c n*l n) * r.errors.base nr (e n x.1,x.2) i
      gaussian := fun n x i => (c n*c n*l n) * r.errors.gaussian nr (e n x.1,x.2) i
      aliasError := fun n x i => (c n*c n*l n) * r.errors.aliasError nr (e n x.1,x.2) i }

theorem stateView_coherent (e : ℕ → D ≃L[ℝ] E) (c l : ℕ → ℝ)
    (r : CorrectionState.State E) (nr n : ℕ) (U : Set D) :
    StateOn U (e n) (c n) (l n) (stateView e c l r nr) r n nr := by
  constructor
  · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x hx; rfl
  · intro x hx theta i; rfl
  · intro x hx theta; rfl
  · intro x hx theta i; rfl
  · intro x hx theta i; rfl
  · intro x hx theta i; rfl

/-- Pullback commutes with the actual additive state update. -/
theorem stateView_addIncrement (e : ℕ → D ≃L[ℝ] E) (c l : ℕ → ℝ)
    (r w : CorrectionState.State E) (nr : ℕ) :
    stateView e c l
      (r.addIncrement w.mean w.pressure w.oscillation w.oscillatoryPressure w.errors) nr =
      (stateView e c l r nr).addIncrement (stateView e c l w nr).mean
        (stateView e c l w nr).pressure (stateView e c l w nr).oscillation
        (stateView e c l w nr).oscillatoryPressure (stateView e c l w nr).errors := by
  cases r
  cases w
  simp only [stateView, CorrectionState.State.addIncrement, MeanIncrementBounds.updated,
    CorrectionState.ExcludedErrors.add, Pi.add_apply, mul_add]
  rfl

end NavierStokes.PhysicalResidualNaturality
