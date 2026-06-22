/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs
import LeanPool.Clawristotle.FlatTorus3Lemmas
import LeanPool.Clawristotle.Section3

/-!
# Transport Constraints (Section 4)

Derives that steady states are local Maxwellians: from the transport equation
and D(f) = 0 at each spatial point, applies Corollary 1 to conclude f(x, .) is
Maxwellian for each x.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Section 5b: Transport Constraints (Section 4 of tex)
-- Reference: Lemmas 10-12, Corollary 2
-- ============================================================================

/-- Corollary 2 (Steady state is a local Maxwellian).
    Reference: cor:local_maxwellian

    At any steady state of the VML system with ν > 0, f(x,·) is a Maxwellian
    for each x ∈ T³.

    Proof: By Lemma 11, Dₓ(f) = 0 for all x. By Corollary 1, f(x,·) is Maxwellian. -/
theorem steady_state_is_local_maxwellian
    (X : Type*)
    (f : X → (Fin 3 → ℝ) → ℝ) (Ψ : ℝ → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hf_int : ∀ x, Integrable (f x))
    (hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0)
    -- Analytical interface: score form + PSD properties for each x
    (hScoreForm : ∀ x, entropyDissipation Ψ (f x) =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ (f x) v w)
    (hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ (f x) p.1 p.2))
    (hPSD_inner : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v))
    (hPSD_outer : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)) :
    ∀ x, IsMaxwellian (f x) := by
  intro x
  exact D_zero_implies_maxwellian Ψ (f x) hΨ (hf_pos x) (hf_smooth x) (hf_int x) (hD_zero x)
    (hScoreForm x) (hPSD_cont x) (hPSD_inner x) (hPSD_outer x)

private lemma hasFDerivAt_proj_mul_const (j : Fin 3) (c : ℝ) (v : Fin 3 → ℝ) :
    HasFDerivAt (fun w : Fin 3 → ℝ => w j * c)
      (c • (ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
  exact (ContinuousLinearMap.proj (ι := Fin 3) (φ := fun _ => ℝ) j :
    (Fin 3 → ℝ) →L[ℝ] ℝ).hasFDerivAt.mul_const c

/-- HasFDerivAt for each component of the Lorentz force E + v×B.
    Component 0: fderiv is B₂·proj₁ - B₁·proj₂
    Component 1: fderiv is B₀·proj₂ - B₂·proj₀
    Component 2: fderiv is B₁·proj₀ - B₀·proj₁ -/
private lemma lorentz_hasFDerivAt_components (E_val B_val : Fin 3 → ℝ) (v : Fin 3 → ℝ) :
    HasFDerivAt (fun w => E_val 0 + cross w B_val 0)
      ((B_val 2 • ContinuousLinearMap.proj 1 - B_val 1 • ContinuousLinearMap.proj 2 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v ∧
    HasFDerivAt (fun w => E_val 1 + cross w B_val 1)
      ((B_val 0 • ContinuousLinearMap.proj 2 - B_val 2 • ContinuousLinearMap.proj 0 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v ∧
    HasFDerivAt (fun w => E_val 2 + cross w B_val 2)
      ((B_val 1 • ContinuousLinearMap.proj 0 - B_val 0 • ContinuousLinearMap.proj 1 :
        (Fin 3 → ℝ) →L[ℝ] ℝ)) v := by
  refine ⟨?_, ?_, ?_⟩ <;> apply HasFDerivAt.const_add
  · change HasFDerivAt (fun w => cross w B_val 0) _ v
    unfold cross; simp only [Matrix.cons_val_zero]
    exact (hasFDerivAt_proj_mul_const 1 (B_val 2) v).sub
      (hasFDerivAt_proj_mul_const 2 (B_val 1) v)
  · change HasFDerivAt (fun w => cross w B_val 1) _ v
    unfold cross; simp only [Matrix.cons_val_one]
    exact (hasFDerivAt_proj_mul_const 2 (B_val 0) v).sub
      (hasFDerivAt_proj_mul_const 0 (B_val 2) v)
  · change HasFDerivAt (fun w => cross w B_val 2) _ v
    unfold cross; simp only [Matrix.cons_val_two]
    exact (hasFDerivAt_proj_mul_const 0 (B_val 1) v).sub
      (hasFDerivAt_proj_mul_const 1 (B_val 0) v)

/-- Velocity divergence of the Lorentz force vanishes: div_v(E + v×B) = 0.
    E is constant in v, and the cross product v×B has zero trace. -/
lemma lorentz_force_div_zero (E_val B_val : Fin 3 → ℝ) :
    ∀ v, vDiv (fun w => E_val + cross w B_val) v = 0 := by
  intro v
  unfold vDiv
  simp only [Fin.sum_univ_three]
  have hsimp : ∀ i : Fin 3, (fun w : Fin 3 → ℝ => (E_val + cross w B_val) i) =
      (fun w => E_val i + cross w B_val i) := fun i => by ext; simp [Pi.add_apply]
  simp_rw [hsimp]
  obtain ⟨h0, h1, h2⟩ := lorentz_hasFDerivAt_components E_val B_val v
  rw [h0.fderiv, h1.fderiv, h2.fderiv]
  simp [ContinuousLinearMap.proj_apply]

/-- Chain rule for the entropy potential: ∇(g·log g - g) = log(g) · ∇g.
    This is the Fréchet derivative version, used to relate IBP to entropy integrals. -/
private lemma fderiv_entropy_potential (g : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ)
    (hg_smooth : ContDiff ℝ 3 g) (hg_pos : 0 < g v) :
    fderiv ℝ (fun w => g w * Real.log (g w) - g w) v =
      Real.log (g v) • fderiv ℝ g v := by
  have hg_diff : DifferentiableAt ℝ g v :=
    hg_smooth.differentiable (by norm_num) |>.differentiableAt
  have hg_ne : g v ≠ 0 := ne_of_gt hg_pos
  have hlog_diff : DifferentiableAt ℝ (fun w => Real.log (g w)) v :=
    (Real.differentiableAt_log hg_ne).comp v hg_diff
  have hlog_fderiv : fderiv ℝ (fun w => Real.log (g w)) v = (g v)⁻¹ • fderiv ℝ g v := by
    have h := ((Real.hasDerivAt_log hg_ne).comp_hasFDerivAt v hg_diff.hasFDerivAt).fderiv
    convert h using 1
    rfl
  have h1 : fderiv ℝ (fun w => g w * Real.log (g w)) v =
      g v • fderiv ℝ (fun w => Real.log (g w)) v + Real.log (g v) • fderiv ℝ g v := by
    have h_eq : (fun w => g w * Real.log (g w)) = g * (fun w => Real.log (g w)) := by
      ext; simp [Pi.mul_apply]
    rw [h_eq]; exact (hg_diff.hasFDerivAt.mul hlog_diff.hasFDerivAt).fderiv
  rw [hlog_fderiv] at h1
  have h_sub : HasFDerivAt (fun w => g w * Real.log (g w) - g w)
      (fderiv ℝ (fun w => g w * Real.log (g w)) v - fderiv ℝ g v) v :=
    (hg_diff.mul hlog_diff).hasFDerivAt.sub hg_diff.hasFDerivAt
  rw [h_sub.fderiv, h1]; ext x
  simp
  field_simp; ring

/-- The diagonal partial derivative ∂(E + v×B)_i/∂v_i = 0 for each i.
    This is because cross product component i depends on v_j, v_k (j,k ≠ i) but not v_i. -/
private lemma lorentz_partial_diag_zero (E_val B_val : Fin 3 → ℝ) (i : Fin 3) (v : Fin 3 → ℝ) :
    fderiv ℝ (fun w => (E_val + cross w B_val) i) v (Pi.single i 1) = 0 := by
  have hsimp : ∀ j : Fin 3, (fun w : Fin 3 → ℝ => (E_val + cross w B_val) j) =
      (fun w => E_val j + cross w B_val j) := fun j => by ext; simp [Pi.add_apply]
  obtain ⟨h0, h1, h2⟩ := lorentz_hasFDerivAt_components E_val B_val v
  fin_cases i
  · change (fderiv ℝ (fun w => (E_val + cross w B_val) 0) v) (Pi.single 0 1) = 0
    rw [hsimp, h0.fderiv]; simp [ContinuousLinearMap.proj_apply, Pi.single]
  · change (fderiv ℝ (fun w => (E_val + cross w B_val) 1) v) (Pi.single 1 1) = 0
    rw [hsimp, h1.fderiv]; simp [ContinuousLinearMap.proj_apply, Pi.single]
  · change (fderiv ℝ (fun w => (E_val + cross w B_val) 2) v) (Pi.single 2 1) = 0
    rw [hsimp, h2.fderiv]; simp [ContinuousLinearMap.proj_apply, Pi.single]

/-- Force transport vanishes: ∫_v (E + v×B) · ∇_v f · log f dv = 0.
    Uses: div_v(E + v×B) = 0 + velocity-space IBP (velocity_ibp). -/
lemma force_transport_zero
    (g : (Fin 3 → ℝ) → ℝ) (E_val B_val : Fin 3 → ℝ)
    (hg_pos : ∀ v, 0 < g v)
    (hg_smooth : ContDiff ℝ 3 g)
    (_hg_int : Integrable g)
    (h_int_f_dg : ∀ i, Integrable (fun v =>
      (E_val + cross v B_val) i *
        fderiv ℝ (fun w => g w * Real.log (g w) - g w) v (Pi.single i 1)))
    (h_int_fg : ∀ i, Integrable (fun v =>
      (E_val + cross v B_val) i * (g v * Real.log (g v) - g v))) :
    ∫ v, dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v) = 0 := by
  -- If the integrand is not integrable, the integral is 0 by Lean's convention
  by_cases h_int : Integrable (fun v =>
      dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v))
  · -- Integrable case: rewrite using chain rule ∇(g·log g - g) = log(g)·∇g
    have h_rw : (fun v => dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) =
        (fun v => dotProduct (E_val + cross v B_val)
          (vGrad (fun w => g w * Real.log (g w) - g w) v)) := by
      ext v; simp only [dotProduct, vGrad]
      have h := fderiv_entropy_potential g v hg_smooth (hg_pos v)
      simp_rw [h, _root_.smul_apply, smul_eq_mul]
      simp [Fin.sum_univ_three]; ring
    conv_lhs => rw [show (∫ v, dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) =
        ∫ v, (fun v => dotProduct (E_val + cross v B_val) (vGrad g v) * Real.log (g v)) v
      from by simp]
    rw [h_rw]
    -- Apply velocity_ibp: ∫ (div G)·h = -∫ ⟨G, ∇h⟩. Since div G = 0, get 0 = -∫ ⟨G, ∇h⟩.
    have h_ibp := velocity_ibp (fun v => E_val + cross v B_val)
      (fun w => g w * Real.log (g w) - g w)
      (by -- differentiability of Lorentz force components (affine in v)
        intro i; simp only [cross, Pi.add_apply]
        fin_cases i <;>
          simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val,
            cons_val_zero, cons_val_one, differentiable_const_add_iff] <;>
          fun_prop)
      (by -- differentiability of entropy potential (g smooth, g > 0)
        exact ((hg_smooth.mul (hg_smooth.log (fun v => ne_of_gt (hg_pos v)))).sub
          hg_smooth).differentiable (by norm_num))
      (by -- ∂(F_i)/∂v_i = 0 for Lorentz force (cross product structure), so integrand = 0
        intro i
        have key : ∀ v, fderiv ℝ (fun w => (fun v => E_val + cross v B_val) w i) v
            (Pi.single i 1) = 0 := lorentz_partial_diag_zero E_val B_val i
        simp_rw [key, zero_mul]; exact integrable_zero _ _ _)
      h_int_f_dg
      h_int_fg
    simp_rw [lorentz_force_div_zero E_val B_val, zero_mul, integral_zero] at h_ibp
    linarith
  · exact integral_undef h_int

/-- Spatial transport of log f vanishes component-wise:
    ∫_X (∂f/∂xᵢ)(x,v) · log f(x,v) dx = 0.
    Uses hIBP_spatial + hGradChainLog + hGradIntZero. -/
private lemma spatial_transport_log_zero {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ x v, 0 < f x v)
    (v : Fin 3 → ℝ)
    (hDiff_fv : FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v))
    (hDiff_logfv : FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v)))
    (i : Fin 3) :
    (∫ x, FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)) = 0 := by
  have h_ibp := FlatTorus3.hIBP_spatial (fun x => f x v) (fun x => Real.log (f x v)) i
    (hDiff_fv.of_le (by decide)) (hDiff_logfv.of_le (by decide))
  have h_chain : ∀ x, FlatTorus3.gradX (fun y => Real.log (f y v)) x i =
      (1 / f x v) * FlatTorus3.gradX (fun y => f y v) x i :=
    fun x => FlatTorus3.hGradChainLog (fun y => f y v)
      (hDiff_fv.of_le (by decide)) (fun x => hf_pos x v) x i
  have h_lhs : (∫ x, f x v * FlatTorus3.gradX (fun y => Real.log (f y v)) x i) =
      ∫ x, FlatTorus3.gradX (fun y => f y v) x i := by
    congr 1
    ext x
    rw [h_chain]
    have := ne_of_gt (hf_pos x v)
    field_simp
  rw [h_lhs] at h_ibp
  have h_grad_int : (∫ x, FlatTorus3.gradX (fun y => f y v) x i) = 0 := by
    have := FlatTorus3.hGradIntZero (fun y => f y v) (hDiff_fv.of_le (by decide)) (Pi.single i 1)
    simp [dotProduct, Fin.sum_univ_three] at this
    fin_cases i <;> simp_all [Pi.single, Function.update]
  rw [h_grad_int] at h_ibp
  have h_comm : (∫ x, Real.log (f x v) * FlatTorus3.gradX (fun y => f y v) x i) = 0 := by
    linarith
  have : (fun x => FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v)) =
      (fun x => Real.log (f x v) * FlatTorus3.gradX (fun y => f y v) x i) := by ext x; ring
  rw [this]; exact h_comm

/-- Transport entropy vanishes at steady state on T³.
    Proof: Multiply Vlasov by log f, integrate over v and X.
    Spatial transport vanishes by hIBP_spatial (spatial_transport_log_zero),
    force transport vanishes by velocity-space IBP (force_transport_zero).
    Reference: Lemma 11 (lem:global_entropy_zero) in H-theorem-formal.tex. -/
lemma transport_entropy_from_vlasov
    {X : Type*} [FlatTorus3 X]
    (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ))
    (Ψ : ℝ → ℝ) (ν : ℝ)
    (hν : 0 < ν)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hf_int : ∀ x, Integrable (f x))
    -- Spatial differentiability of f(·,v) and log f(·,v)
    (hDiff_fv : ∀ v, FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v))
    (hDiff_logfv : ∀ v, FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v)))
    (hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v)
    -- Velocity-space integrability for transport decomposition
    (hSpatialTransport_int : ∀ x, Integrable (fun v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
    (hForceTransport_int : ∀ x, Integrable (fun v =>
      (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)))
    -- Per-component integrability for velocity-space IBP
    (hForceIBP_f_dg : ∀ x i, Integrable (fun v =>
      (E x + cross v (B x)) i *
        fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1)))
    (hForceIBP_fg : ∀ x i, Integrable (fun v =>
      (E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v)))
    -- Joint integrability for Fubini (spatial × velocity)
    (hSpatialTransport_joint : Integrable (Function.uncurry (fun x v =>
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
      (volume.prod volume))
    -- Per-component spatial integrability for the transport × log f terms
    (hSpatTransComp : ∀ v i, MeasureTheory.Integrable (fun x =>
      FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v))) :
    (∫ x, entropyDissipation Ψ (f x)) = 0 := by
  -- Strategy: ν * ∫D = 0, and ν > 0.
  suffices h_zero : ν * (∫ x, entropyDissipation Ψ (f x)) = 0 by
    rcases mul_eq_zero.mp h_zero with h | h
    · linarith
    · exact h
  -- ν * ∫D = ∫(ν * D) via integral_mul_left
  have h_comm : ν * (∫ x, entropyDissipation Ψ (f x)) =
      ∫ x, ν * entropyDissipation Ψ (f x) := by
    rw [← integral_const_mul]
  rw [h_comm]
  -- For each x: ν * D(f x) = ∫_v (v · ∇_x f) * log f (force transport = 0)
  have h_key : ∀ x, ν * entropyDissipation Ψ (f x) =
      ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) := by
    intro x
    unfold entropyDissipation
    rw [← integral_const_mul]
    have hrw : (fun v => ν * (LandauOperator Ψ (f x) v * Real.log (f x v))) =
        (fun v => v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v) +
          (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v)) := by
      ext v
      have hV := hVlasov x v
      have : ν * (LandauOperator Ψ (f x) v * Real.log (f x v)) =
          (ν * LandauOperator Ψ (f x) v) * Real.log (f x v) := by ring
      rw [this, ← hV]; ring
    rw [hrw, integral_add (hSpatialTransport_int x) (hForceTransport_int x)]
    rw [force_transport_zero (f x) (E x) (B x) (hf_pos x) (hf_smooth x) (hf_int x)
      (hForceIBP_f_dg x) (hForceIBP_fg x)]
    simp [add_zero]
  -- Rewrite ∫(ν * D) = ∫(∫_v transport * log f)
  have h_eq : (fun x => ν * entropyDissipation Ψ (f x)) =
      (fun x => ∫ v, v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) := by
    ext x; exact h_key x
  rw [h_eq]
  -- Fubini: swap ∫_X and ∫_v
  rw [FlatTorus3.hSpatialVelocityFubini _ hSpatialTransport_joint]
  -- For each v, spatial integral vanishes
  suffices h_v : ∀ v : Fin 3 → ℝ, (∫ x,
      v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)) = 0 by
    simp_rw [h_v]
    exact integral_zero (Fin 3 → ℝ) ℝ
  -- Expand dotProduct v (gradX (f · v)) * log f = ∑_i v_i * gradX(f·v)_i * log f
  -- Then use integral_add + integral_mul_left + spatial_transport_log_zero
  intro v
  simp only [dotProduct, Fin.sum_univ_three]
  -- (v₀*g₀ + v₁*g₁ + v₂*g₂) * logf = v₀*g₀*logf + v₁*g₁*logf + v₂*g₂*logf
  have hrw : (fun x => (v 0 * FlatTorus3.gradX (fun y => f y v) x 0 +
      v 1 * FlatTorus3.gradX (fun y => f y v) x 1 +
      v 2 * FlatTorus3.gradX (fun y => f y v) x 2) * Real.log (f x v)) =
      (fun x => v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) +
       (v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) +
        v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v)))) := by
    ext x; ring
  have hA : MeasureTheory.Integrable (fun x => v 0 *
      (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v))) :=
    (hSpatTransComp v 0).const_mul _
  have hB : MeasureTheory.Integrable (fun x => v 1 *
      (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v))) :=
    (hSpatTransComp v 1).const_mul _
  have hC : MeasureTheory.Integrable (fun x => v 2 *
      (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) :=
    (hSpatTransComp v 2).const_mul _
  erw [hrw]
  have h0 := spatial_transport_log_zero f hf_pos v (hDiff_fv v) (hDiff_logfv v) (0 : Fin 3)
  have h1 := spatial_transport_log_zero f hf_pos v (hDiff_fv v) (hDiff_logfv v) (1 : Fin 3)
  have h2 := spatial_transport_log_zero f hf_pos v (hDiff_fv v) (hDiff_logfv v) (2 : Fin 3)
  have hm0 : (∫ x : X, v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v))) =
      v 0 * ∫ x, FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v) :=
    integral_const_mul _ _
  have hm1 : (∫ x : X, v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v))) =
      v 1 * ∫ x, FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v) :=
    integral_const_mul _ _
  have hm2 : (∫ x : X, v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) =
      v 2 * ∫ x, FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v) :=
    integral_const_mul _ _
  have hA0 : ∫ x : X, v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) = 0 := by
    rw [hm0, h0, mul_zero]
  have hB0 : ∫ x : X, v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) = 0 := by
    rw [hm1, h1, mul_zero]
  have hC0 : ∫ x : X, v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v)) = 0 := by
    rw [hm2, h2, mul_zero]
  have hBC : (∫ x : X, v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) +
      v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) = 0 := by
    rw [MeasureTheory.integral_add hB hC, hB0, hC0, add_zero]
  have hABC : ∫ x : X, v 0 * (FlatTorus3.gradX (fun y => f y v) x 0 * Real.log (f x v)) +
      (v 1 * (FlatTorus3.gradX (fun y => f y v) x 1 * Real.log (f x v)) +
       v 2 * (FlatTorus3.gradX (fun y => f y v) x 2 * Real.log (f x v))) = 0 := by
    have h := MeasureTheory.integral_add hA (hB.add hC)
    simp only [Pi.add_apply] at h; linarith [hBC]
  linarith

end VML
