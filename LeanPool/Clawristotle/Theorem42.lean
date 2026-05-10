/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.VMLInputDerive

/-!
set_option linter.style.longLine false

# Abstract Theorem 4.2: Steady State Implies Maxwellian

States and proves the main abstract result: any smooth steady state of the
Vlasov-Maxwell-Landau system satisfying `VelocityDecayConditions` is a global
Maxwellian with E = 0 and B = const.

**Physical Context (Non-Relativistic Limit):**
Note that this formalization assumes a strictly non-relativistic framework where
velocities $v \in \mathbb{R}^3$ are unbounded. This admits superluminal particles,
but is the standard mathematical setting for the classical Landau equation.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Theorem 42: Clean statement with minimal physical hypotheses
--
-- Reference: H-theorem-formal.pdf, Section 10, Theorem 42.
-- This is the main result: any sufficiently smooth steady-state solution
-- of the VML system on a periodic domain must be a global Maxwellian
-- equilibrium with E = 0 and B = const.
-- ============================================================================

/-- Velocity-space decay / integrability conditions for the VML steady state theorem.

    These conditions hold for distribution functions with sufficient velocity-space
    decay (e.g., Schwartz class or sub-Gaussian tails). They ensure that:
    - The H-theorem chain (IBP + Fubini symmetrization) goes through
    - The transport entropy equation can be decomposed
    - The Landau flux is differentiable and integrable

    Bundled into a single structure for readability of the main theorem. -/
structure VelocityDecayConditions {X : Type*} [FlatTorus3 X]
    (Ψ : ℝ → ℝ) (f : X → (Fin 3 → ℝ) → ℝ) (E B : X → (Fin 3 → ℝ)) where
  -- PSD integrand integrability (for "nonneg integral = 0 → pointwise = 0")
  hPSD_inner_int : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v)
  hPSD_outer_int : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)
  -- Fubini integrability for the symmetrized weak form
  hFubini_double : ∀ x, Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    dotProduct (vGrad (Real.log ∘ f x) p.1)
      (mulVec (landauMatrix Ψ (p.1 - p.2))
        (f x p.2 • vGrad (f x) p.1 - f x p.1 • vGrad (f x) p.2)))
  hFubini_inner : ∀ x v, Integrable (fun w =>
    dotProduct (vGrad (Real.log ∘ f x) v)
      (mulVec (landauMatrix Ψ (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)))
  hFubini_outer : ∀ x, Integrable (fun v => ∫ w,
    dotProduct (vGrad (Real.log ∘ f x) v)
      (mulVec (landauMatrix Ψ (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)))
  -- Transport integrability (for entropy decomposition)
  hSpatialTransport_int : ∀ x, Integrable (fun v =>
    v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v))
  hForceTransport_int : ∀ x, Integrable (fun v =>
    (E x + cross v (B x)) ⬝ᵥ vGrad (f x) v * Real.log (f x v))
  -- Landau flux differentiability (differentiation under the integral sign)
  hLandauFluxDiff : ∀ x i, Differentiable ℝ (fun v =>
    (∫ w, mulVec (landauMatrix Ψ (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i)
  -- Per-component integrability for velocity-space IBP of Landau operator
  hLandauIBP_df_g : ∀ x i, Integrable (fun v =>
    fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f x w • vGrad (f x) v' - f x v' • vGrad (f x) w)) i) v (Pi.single i 1) *
    (Real.log ∘ f x) v)
  hLandauIBP_f_dg : ∀ x i, Integrable (fun v =>
    (∫ w, mulVec (landauMatrix Ψ (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i *
    fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1))
  hLandauIBP_fg : ∀ x i, Integrable (fun v =>
    (∫ w, mulVec (landauMatrix Ψ (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i * (Real.log ∘ f x) v)
  -- Integrability of the Landau flux (for pulling dot product through ∫)
  hLandauFluxInt : ∀ x v, Integrable (fun w =>
    mulVec (landauMatrix Ψ (v - w))
      (f x w • vGrad (f x) v - f x v • vGrad (f x) w))
  -- Per-component integrability for velocity-space IBP in entropy estimate
  hForceIBP_f_dg : ∀ x i, Integrable (fun v =>
    (E x + cross v (B x)) i *
      fderiv ℝ (fun w => f x w * Real.log (f x w) - f x w) v (Pi.single i 1))
  hForceIBP_fg : ∀ x i, Integrable (fun v =>
    (E x + cross v (B x)) i * (f x v * Real.log (f x v) - f x v))
  -- Joint integrability for Fubini (spatial × velocity transport)
  hSpatialTransport_joint : Integrable (Function.uncurry (fun x v =>
    v ⬝ᵥ FlatTorus3.gradX (fun y => f y v) x * Real.log (f x v)))
    (volume.prod volume)
  -- Per-component spatial integrability for transport × log f decomposition
  hSpatTransComp : ∀ v i, MeasureTheory.Integrable (fun x =>
    FlatTorus3.gradX (fun y => f y v) x i * Real.log (f x v))
  -- Uniform velocity domination: f(x,v) ≤ g(v) for some integrable g
  -- (needed for dominated convergence → continuity of ρ = ∫f dv)
  hf_velocity_dominated : ∃ g, Integrable g ∧ ∀ x v, f x v ≤ g v
  -- PSD integrand is jointly continuous (needed even when Ψ is singular, e.g. Coulomb)
  hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    PSDIntegrand Ψ (f x) p.1 p.2)
  -- Entropy dissipation is continuous on the spatial domain
  hD_cont : Continuous (fun x => entropyDissipation Ψ (f x))


/-- **Theorem 42** (Global steady state of the VML system).

    Consider the Vlasov-Maxwell-Landau system on a periodic spatial domain
    (modeled by a FlatTorus3) with collision frequency ν > 0, interaction
    potential Ψ > 0, and uniform neutralizing ion background density ρ_ion > 0.

    Let (f, E, B) be a sufficiently smooth steady-state solution with f > 0
    and f(x, ·) ∈ L¹(ℝ³) for each x. Then:

    (i)   f is a spatially uniform, zero-drift Maxwellian:
          f(v) = ρ_ion / (2πT)^(3/2) · exp(-|v|²/(2T))

    (ii)  The electric field vanishes: E = 0.

    (iii) The magnetic field is spatially constant.

    The velocity-space decay conditions (bundled in `VelocityDecayConditions`)
    require not only sufficient upper-bound velocity-space decay (e.g., Schwartz class),
    but importantly also a matching LOWER bound. The polynomial score bound (`hGradBound`)
    actively excludes functions with faster-than-exponential decay (like $e^{-e^{\|v\|}}$),
    even though they are Schwartz class. The conditions effectively restrict the
    domain to near-Maxwellian or stretched-exponential states.

    *Note on Physical Rigor:* This theorem addresses the classic non-relativistic formulation
    over $v \in \mathbb{R}^3$. As with all non-relativistic kinetic theory over an unbounded
    velocity space, this formally admits unphysical superluminal velocities ($|v| > c$).
    A strictly correct physical model would require replacing $v$ with momentum $p$.

    Reference: H-theorem-formal.pdf, Theorem 42. -/
theorem Theorem42
    -- === Spatial domain (abstract flat 3-torus) ===
    {X : Type*} [FlatTorus3 X]
    -- === Physical state at steady state ===
    (f : X → (Fin 3 → ℝ) → ℝ)
    (E B : X → (Fin 3 → ℝ))
    -- === Physical parameters ===
    (Ψ : ℝ → ℝ) (ν ρ_ion : ℝ)
    -- === Physical hypotheses ===
    (hν : 0 < ν)
    (hρ_ion : 0 < ρ_ion)
    (hΨ : ∀ r, 0 < Ψ r)
    (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth : ∀ x, ContDiff ℝ 3 (f x))
    (hf_int : ∀ x, Integrable (f x))
    -- === Steady-state Maxwell equations ===
    -- Ampère's law (∂ₜE = 0): ∇×B = J
    (hAmpere : ∀ x, FlatTorus3.curlX B x = fun i => ∫ v, v i * f x v)
    -- Gauss's law: ∇·E = ρ − ρ_ion
    (hGauss : ∀ x, FlatTorus3.divX E x = (∫ v, f x v) - ρ_ion)
    -- Solenoidal constraint: ∇·B = 0
    (hDivB : ∀ x, FlatTorus3.divX B x = 0)
    -- B is spatially differentiable (each component)
    (hDiff_B : ∀ i, FlatTorus3.IsSpatiallySmooth 2 (fun y => B y i))
    -- === Steady-state Vlasov equation ===
    -- v · ∇ₓf + (E + v×B) · ∇ᵥf = ν Q(f,f)
    (hVlasov : ∀ x v,
      dotProduct v (FlatTorus3.gradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator Ψ (f x) v)
    -- === Spatial differentiability ===
    -- f(·,v) is spatially differentiable for each fixed v.
    -- This is automatic for smooth distribution functions.
    -- log f(·,v) is derived from hDiff_fv + hf_pos + FlatTorus3.hDiff_log ⊤.
    (hDiff_fv : ∀ v, FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v))
    -- If f = exp(a + b·v + c|v|²), then a, b, c are spatially differentiable.
    -- Derived from hDiff_fv + hf_pos + FlatTorus3.hDiff_log ⊤
    -- (via maxwellian_params_isSpatiallyDiff).
    -- C² regularity (hDiff_B_C2, hDiff_maxwellian_C2) derived via FlatTorus3.hDiff_grad ⊤.
    -- === Velocity-space decay conditions ===
    (hDecay : VelocityDecayConditions Ψ f E B) :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Abbreviations for density and current (computed from f)
  set ρ : X → ℝ := fun x => ∫ v, f x v with hρ_def
  set J : X → (Fin 3 → ℝ) := fun x i => ∫ v, v i * f x v with hJ_def
  -- Step 0: Derive mathematical consequences of the Vlasov equation.
  have hρ_pos : ∀ x, 0 < ρ x := fun x =>
    density_positive_of_integral (f x) (hf_pos x) (hf_int x)
  -- Derive spatial differentiability of log f(·,v) from hDiff_fv + hf_pos + hDiff_log ⊤
  have hDiff_logfv : ∀ v, FlatTorus3.IsSpatiallySmooth 2 (fun x => Real.log (f x v)) := fun v =>
    FlatTorus3.hDiff_log 2 (fun x => f x v) ((hDiff_fv v).of_le (by decide)) (fun x => hf_pos x v)
  -- Derive that Maxwellian parameters a, b, c are spatially differentiable
  -- (from evaluating log f at v = 0, eⱼ, 2e₀ and using closure properties)
  have hDiff_maxwellian : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
      (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
      FlatTorus3.IsSpatiallySmooth 2 a ∧
      (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => b y j)) ∧
      FlatTorus3.IsSpatiallySmooth 2 c :=
    FlatTorus3.maxwellian_params_isSpatiallySmooth f hf_pos
      (fun v => (hDiff_fv v).of_le (by decide))
  -- Derive continuity of ρ = ∫ f(·,v) dv via dominated convergence
  have hρ_cont : Continuous ρ := by
    change Continuous (fun x => ∫ v, f x v)
    obtain ⟨g, hg_int, hg_bound⟩ := hDecay.hf_velocity_dominated
    exact continuous_of_dominated
      (fun x => (hf_smooth x).continuous.aestronglyMeasurable)
      (fun x => .of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_pos (hf_pos x v)]; exact hg_bound x v)
      hg_int
      (.of_forall fun v => FlatTorus3.hDiff_continuous 1 _ (hDiff_fv v))
  have hTransportEntropy : (∫ x, entropyDissipation Ψ (f x)) = 0 :=
    transport_entropy_from_vlasov f E B Ψ ν hν hf_pos hf_smooth hf_int hDiff_fv hDiff_logfv
      hVlasov hDecay.hSpatialTransport_int hDecay.hForceTransport_int
      hDecay.hForceIBP_f_dg hDecay.hForceIBP_fg hDecay.hSpatialTransport_joint
      hDecay.hSpatTransComp
  have hPolynomialId := polynomial_identity_from_vlasov f E B Ψ ν hf_pos hf_smooth hf_int hΨ hVlasov
  have hPB := poisson_boltzmann_from_vlasov f E B Ψ ν ρ ρ_ion hf_pos hf_smooth hf_int hΨ
    (fun x => rfl) hGauss hDiff_fv hVlasov
  -- Extremizers of ρ (extreme value theorem on compact T³)
  obtain ⟨x_max, hmax⟩ := continuous_attains_max ρ hρ_cont
  obtain ⟨x_min, hmin⟩ := continuous_attains_min ρ hρ_cont
  -- Step 1: Symmetrized weak form for each x (the core analytical input).
  have hIBP : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w))) :=
    fun x => landau_ibp Ψ (f x) (hf_pos x) (hf_smooth x) (hf_int x)
      (hDecay.hLandauFluxDiff x) (hDecay.hLandauIBP_df_g x) (hDecay.hLandauIBP_f_dg x)
      (hDecay.hLandauIBP_fg x) (hDecay.hLandauFluxInt x)
  have hFubiniSym : ∀ x, ∫ v, ∫ w, dotProduct
        (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix Ψ (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    intro x; exact fubini_symmetrization_logf Ψ (f x) (hf_smooth x)
      (hDecay.hFubini_double x) (hDecay.hFubini_inner x) (hDecay.hFubini_outer x)
  have hSWF_all : ∀ x, ∫ v, LandauOperator Ψ (f x) v * (Real.log ∘ f x) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f x) v - vGrad (Real.log ∘ f x) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
    intro x
    rw [hIBP x, hFubiniSym x]
    ring
  -- Step 2: Derive D(f) = 0 from the Vlasov equation.
  have hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0 := by
    have hD_nonpos : ∀ x, entropyDissipation Ψ (f x) ≤ 0 := by
      intro x
      exact H_theorem Ψ (f x) (fun r => le_of_lt (hΨ r)) (hf_pos x) (hf_smooth x) (hSWF_all x)
    have hD_int_zero : FlatTorus3.spatialIntegral (fun x => entropyDissipation Ψ (f x)) = 0 :=
      hTransportEntropy
    intro x
    have hD_neg : ∀ y, 0 ≤ -(entropyDissipation Ψ (f y)) := fun y => neg_nonneg.mpr (hD_nonpos y)
    have hD_neg_int : FlatTorus3.spatialIntegral (fun y => -(entropyDissipation Ψ (f y))) = 0 := by
      have h := FlatTorus3.hSpatialMul (fun y => entropyDissipation Ψ (f y)) (-1)
      simp only [mul_neg_one] at h
      linarith [hD_int_zero]
    linarith [FlatTorus3.hSpatialNonnegZero _ hDecay.hD_cont.neg hD_neg hD_neg_int x]
  -- Step 3: Apply the main theorem via VMLInput.
  have result := main_from_physics {
    x₀ := Classical.arbitrary X
    f := f
    E := E
    B := B
    ν := ν
    ρ_ion := ρ_ion
    Ψ := Ψ
    hν := hν
    hρ_ion := hρ_ion
    hΨ := hΨ
    hf_pos := hf_pos
    hf_smooth := hf_smooth
    hf_int := hf_int
    ρ := ρ
    hρ_eq := fun x => rfl
    hρ_pos := hρ_pos
    hρ_cont := hρ_cont
    J := J
    hAmpere := hAmpere
    hGauss := fun x => hGauss x
    hDivB := hDivB
    hDiff_fv := hDiff_fv
    hDiff_B := hDiff_B
    hD_zero := hD_zero
    hScoreForm := fun x => entropy_score_form Ψ (f x) (hf_pos x) (hf_smooth x) (hSWF_all x)
    hPSD_cont := hDecay.hPSD_cont
    hPSD_inner := hDecay.hPSD_inner_int
    hPSD_outer := hDecay.hPSD_outer_int
    hDiff_maxwellian := hDiff_maxwellian
    hPolynomialIdentity := fun a b c ha hb hc hform =>
      hPolynomialId a b c ha hb hc hform
    hJ_from_maxwellian := fun b_func c₀ hform => by
      intro x
      obtain ⟨a₀, ha₀⟩ := hform x
      show J x = ρ x • ((-1 / (2 * c₀)) • b_func x)
      simp only [J, ρ]
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      exact current_density_of_gaussian (f x) (hf_pos x) (hf_int x) a₀ (b_func x) c₀ ha₀ i
    x_max := x_max
    hmax := hmax
    x_min := x_min
    hmin := hmin
    hPB_eq := hPB
    hNormalization := fun a₀ c₀ hc₀ hf_form hdens => by
      intro x v
      have h_int : ∫ w : Fin 3 → ℝ, f x w = ρ_ion := by
        rw [← hdens x]
      exact gaussian_normalization_maxwellian ρ_ion a₀ c₀ hρ_ion hc₀
        (f x) (hf_form x) h_int v
  }
  obtain ⟨eq, hf_eq, hE, hB⟩ := result
  exact ⟨eq.T, eq.B₀, eq.hT, hf_eq, hE, hB⟩

end VML
