/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.CoulombSpatialTransport
import LeanPool.Clawristotle.CoulombFluxBound
import LeanPool.Clawristotle.CoulombPSD
import LeanPool.Clawristotle.CoulombFluxDiff
import LeanPool.Clawristotle.IteratedDerivHelpers
import LeanPool.Clawristotle.LogBoundHelpers

/-!
# Concrete Theorem 4.2 for Coulomb Collisions on T^3

Specializes the abstract `ConcreteTheorem42` to the Coulomb kernel Psi(r) = r^{-3},
the physically most important case in plasma physics. Verifies all 19 fields of
`VelocityDecayConditions` for Coulomb and states the main result: any smooth
steady state of the VML system with Coulomb collisions is a global Maxwellian
with E = 0 and B = const.
-/

open MeasureTheory Matrix Finset BigOperators Real

noncomputable section
namespace VML

/-- **Coulomb Theorem 42.** Characterization of smooth steady states of the
    Vlasov–Maxwell–Landau system with Coulomb collisions on T³ = (ℝ/ℤ)³.

    *Note on Physical Rigor:* This theorem addresses the classic non-relativistic formulation
    over $v \in \mathbb{R}^3$. As with all non-relativistic kinetic theory over an unbounded
    velocity space, this formally admits unphysical superluminal velocities ($|v| > c$).
    A strictly correct physical model would require replacing $v$ with momentum $p$.

    This is the physically most important case: Coulomb interactions between
    charged particles in a plasma. The collision kernel Ψ(r) = r⁻³ is singular
    at r = 0 but the formalization handles this via the PSD continuity condition
    in VelocityDecayConditions (the singularity cancels in the quadratic form).

    **Hypotheses** (12 total):
    - 2 physical parameters (ν > 0, ρ_ion > 0)
    - 1 strict positivity (f > 0)
    - 3 smoothness (f smooth in v and x, B smooth)
    - 2 decay (uniform C² velocity decay; polynomial score bound)
    - 4 equations (Vlasov, Ampère, Gauss, div B = 0)

    **Independence note:** The polynomial score bound (hGradBound) is
    NOT derivable from the Schwartz decay alone. The ratio |∂f|/f equals
    |∂f| * exp(C(1+‖v‖)^K) in the worst case, which grows super-polynomially
    for K ≥ 1. Counterexample: f(v) = exp(-|v|²)(2 + sin(exp(⟨v⟩))) is Schwartz
    with stretched-exponential lower bound, but |∂f|/f grows like exp(⟨v⟩).
    The polynomial score bound is a genuine additional assumption, satisfied by
    physically relevant distributions (Maxwellians, perturbations thereof).

    **Coulomb-specificity of hGradBound:** This hypothesis is needed solely to
    handle the Coulomb singularity Ψ(r) = r⁻³. The score difference
    ∇log f(v) − ∇log f(w) = O(|v−w|) cancels the 1/|v−w| blow-up of the
    Coulomb collision matrix, ensuring PSD integrability. For bounded kernels
    (e.g. Maxwell molecules with Ψ = const), the abstract `Theorem42` applies
    without any score bound hypothesis.

    **Restrictiveness of hGradBound:** The polynomial score bound
    forces a strict lower bound on the decay rate of $f$. It actively excludes
    many standard Schwartz class functions, such as those with faster-than-exponential
    decay (e.g., $f(v) = \exp(-\exp(\|v\|))$), because their logarithmic gradient
    grows too fast. Thus, while the theorem covers Maxwellians, it strictly
    prohibits solutions that vanish too rapidly at infinity.

    **Scope:** Single species, non-relativistic, 3D flat torus, Coulomb kernel
    (Ψ(r) = r⁻³). Assumes existence of a smooth positive steady-state solution. -/
theorem CoulombConcreteTheorem42
    -- === Physical state at steady state ===
    (f : Torus3 → (Fin 3 → ℝ) → ℝ)
    (E B : Torus3 → Fin 3 → ℝ)
    (ν ρ_ion : ℝ)
    -- === Physical parameters ===
    (hν : 0 < ν)                                -- (1)
    (hρ_ion : 0 < ρ_ion)                        -- (2)
    (hf_pos : ∀ x v, 0 < f x v)                -- (3)
    -- === Smoothness ===
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))                             -- (4)
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))   -- (5)
    (hB_smooth : ∀ i, ContDiff ℝ 2 (periodicLift (fun x => B x i)))     -- (6)
    -- === Uniform C² velocity decay ===
    (hSchwartz : UniformSchwartzDecay f)         -- (7)
    -- === Polynomial score bound (independent of hSchwartz) ===
    -- This is NOT derivable from hSchwartz alone: the ratio |∂f|/f can grow
    -- super-polynomially even for Schwartz f.
    -- Satisfied by Maxwellians and physically reasonable perturbations.
    (hGradBound : ∃ (Cg : ℝ) (Kg : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ) (i : Fin 3),
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v) -- (8)
    -- === Steady-state Vlasov equation with Coulomb kernel ===
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)  -- (9)
    -- === Steady-state Maxwell equations ===
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)       -- (10)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)              -- (11)
    (hDivB : ∀ x, torusDivX B x = 0)             -- (12)
    :
    -- === Conclusion ===
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧
    (∀ x, B x = B₀) := by
  -- Extract gradient bound components (used in multiple fields)
  obtain ⟨Cg, Kg, hCg⟩ := hGradBound
  -- Log growth bound (derived from hGradBound via MVT)
  have hLogBound := log_bound_from_grad f hf_pos hf_smooth_v hf_smooth_x Cg Kg hCg
  -- Schwartz decay specialized to each x (used in many fields below)
  have hSchwartz_x : ∀ x, ∀ (N : ℕ) {k : ℕ}, k ≤ 2 → ∃ C > 0, ∀ v,
      ‖iteratedFDeriv ℝ k (f x) v‖ * (1 + ‖v‖) ^ N ≤ C := fun x =>
    fun N {k} hk => (hSchwartz.hDecay N hk).imp fun C hC => ⟨hC.1, fun v => hC.2 x v⟩
  -- Flux × score integrability (used for hLandauIBP_f_dg and hFubini_outer)
  have hIBP_f_dg : ∀ x i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) i *
      fderiv ℝ (Real.log ∘ f x) v (Pi.single i 1)) := fun x i =>
    coulomb_ibp_f_dg_integrable (f x) (hf_pos x) (hf_smooth_v x)
      (hSchwartz_x x) (fun v j => hCg x v j) i
  -- Extract hFluxInt for reuse
  have hFluxInt : ∀ x v, Integrable (fun w =>
      mulVec (landauMatrix coulombKernel (v - w))
        (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := fun x v =>
    landau_flux_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
      (hSchwartz_x x) v
  have hDecay : VelocityDecayConditions coulombKernel f E B := {
    hPSD_inner_int := fun x v =>
      psd_inner_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j) v
    hPSD_outer_int := fun x =>
      psd_outer_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j)
    hFubini_double := fun x =>
      fubini_double_integrable_coulomb (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) (fun v j => hCg x v j)
    hFubini_inner := by
      intro x v
      simp only [dotProduct]
      exact integrable_finset_sum _ fun i _ =>
        ((integrable_pi_iff.mp (hFluxInt x v) i).const_mul _)
    hFubini_outer := by
      intro x
      -- Step 1: pull dotProduct through ∫_w (score(v) is constant in w)
      have h_eq : ∀ v, (∫ w, dotProduct (vGrad (Real.log ∘ f x) v)
          (mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w))) =
        dotProduct (vGrad (Real.log ∘ f x) v)
          (∫ w, mulVec (landauMatrix coulombKernel (v - w))
            (f x w • vGrad (f x) v - f x v • vGrad (f x) w)) := by
        intro v
        simp only [dotProduct]
        rw [integral_finset_sum _ (fun i _ => ((hFluxInt x v).eval i).const_mul _)]
        congr 1; ext i
        rw [eval_integral (fun i => (hFluxInt x v).eval i), integral_const_mul]
      simp_rw [h_eq]
      -- Step 2: dotProduct score flux = ∑ i, score_i * flux_i, each integrable by hIBP_f_dg
      simp only [dotProduct, Fin.sum_univ_three, vGrad]
      have h := fun i => (hIBP_f_dg x i).congr (Filter.Eventually.of_forall
        fun v => show _ = _ from mul_comm _ _)
      exact (h 0).add (h 1) |>.add (h 2)
    hSpatialTransport_int := fun x =>
      spatial_transport_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLogBound x
    hForceTransport_int := fun x =>
      force_transport_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x
    hLandauFluxDiff := by
      intro x i
      exact coulomb_flux_differentiable (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x) i
    hLandauIBP_df_g := by
      obtain ⟨C_log, K_log, hLB⟩ := hLogBound
      intro x i
      exact coulomb_ibp_df_g_integrable (f x) (hf_pos x) (hf_smooth_v x)
        (hSchwartz_x x)
        ⟨C_log, K_log, fun v => hLB x v⟩ i
    hLandauIBP_f_dg := hIBP_f_dg
    hLandauIBP_fg := fun x i =>
      flux_times_log_integrable_coulomb hf_pos hf_smooth_v hSchwartz hLogBound x i
    hLandauFluxInt := hFluxInt
    hForceIBP_f_dg := fun x i =>
      force_ibp_f_dg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hForceIBP_fg := fun x i =>
      force_ibp_fg_integrable_coulomb E B hf_pos hf_smooth_v hSchwartz hLogBound x i
    hSpatialTransport_joint :=
      spatial_transport_joint_integrable hf_pos hf_smooth_v hf_smooth_x hSchwartz hLogBound
    hSpatTransComp := by
      intro v i
      have hDiff_fv : FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v) :=
        (hf_smooth_x v).of_le (by decide)
      have hcont_grad := FlatTorus3.hDiff_continuous 0 _ (FlatTorus3.hDiff_grad 1 _ i hDiff_fv)
      have hcont_log := FlatTorus3.hDiff_continuous 1 _
        (FlatTorus3.hDiff_log 2 _ hDiff_fv (fun x => hf_pos x v))
      exact (hcont_grad.mul hcont_log).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    hf_velocity_dominated := by
      obtain ⟨C, hC_pos, hbound⟩ := hSchwartz.hDecay 4 (k := 0) (by norm_num)
      refine ⟨fun v => C / (1 + ‖v‖) ^ 4, inverse_poly_integrable C, fun x v => ?_⟩
      have hb := hbound x v
      simp only [norm_iteratedFDeriv_zero, norm_eq_abs] at hb
      have hv_pos : (0 : ℝ) < (1 + ‖v‖) ^ 4 := by positivity
      rw [abs_of_pos (hf_pos x v)] at hb
      rwa [le_div_iff₀ hv_pos]
    -- PSD continuity: the key Coulomb-specific condition.
    -- Despite Ψ(r) = r⁻³ being singular, the PSD integrand is continuous
    -- because the score difference Δ = O(|v-w|) cancels the singularity.
    hPSD_cont := fun x => psd_continuous_coulomb (f x) (hf_pos x) (hf_smooth_v x)
    hD_cont :=
      entropy_dissipation_continuous_coulomb f E B ν hν hf_pos hf_smooth_v hf_smooth_x
        hSchwartz hLogBound hVlasov
  }
  exact Theorem42 f E B coulombKernel ν ρ_ion
    hν hρ_ion coulombKernel_pos hf_pos
    (fun x => (hf_smooth_v x).of_le
      (by exact_mod_cast (by decide : 2 + 1 ≤ 3)))
    (hSchwartz.integrable hf_smooth_v)
    hAmpere hGauss hDivB
    (fun i => (hB_smooth i).of_le (by decide))
    hVlasov
    (fun v => (hf_smooth_x v).of_le (by decide))
    hDecay

/-- The steady state is parameterized by an injective temperature T_eq.
    Note: T_eq is uniquely determined *by the state f itself* via injectivity, but the overall
    theorem classifies a family of steady states parameterized by T > 0 and B₀ ∈ ℝ³. -/
theorem CoulombConcreteTheorem42_classify_T
    (f : Torus3 → (Fin 3 → ℝ) → ℝ) (E B : Torus3 → Fin 3 → ℝ) (ν ρ_ion : ℝ)
    (hν : 0 < ν) (hρ_ion : 0 < ρ_ion) (hf_pos : ∀ x v, 0 < f x v)
    (hf_smooth_v : ∀ x, ContDiff ℝ 3 (f x))
    (hf_smooth_x : ∀ v, ContDiff ℝ 2 (periodicLift (fun x => f x v)))
    (hB_smooth : ∀ i, ContDiff ℝ 2 (periodicLift (fun x => B x i)))
    (hSchwartz : UniformSchwartzDecay f)
    (hGradBound : ∃ (Cg : ℝ) (Kg : ℕ), ∀ (x : Torus3) (v : Fin 3 → ℝ) (i : Fin 3),
      |fderiv ℝ (f x) v (Pi.single i 1)| ≤ Cg * (1 + ‖v‖) ^ Kg * f x v)
    (hVlasov : ∀ x v,
      dotProduct v (torusGradX (fun y => f y v) x) +
      dotProduct (E x + cross v (B x)) (vGrad (f x) v) =
      ν * LandauOperator coulombKernel (f x) v)
    (hAmpere : ∀ x, torusCurlX B x = fun i => ∫ v, v i * f x v)
    (hGauss : ∀ x, torusDivX E x = (∫ v, f x v) - ρ_ion)
    (hDivB : ∀ x, torusDivX B x = 0) :
    ∃ (T_eq : ℝ) (B₀ : Fin 3 → ℝ), 0 < T_eq ∧
    (∀ x v, f x v = equilibriumMaxwellian ρ_ion T_eq v) ∧
    (∀ x, E x = 0) ∧ (∀ x, B x = B₀) ∧
    (∀ T', 0 < T' → (∀ v, equilibriumMaxwellian ρ_ion T' v = equilibriumMaxwellian ρ_ion T_eq v) →
      T' = T_eq) := by
  obtain ⟨T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const⟩ :=
    CoulombConcreteTheorem42 f E B ν ρ_ion hν hρ_ion hf_pos hf_smooth_v hf_smooth_x hB_smooth
      hSchwartz hGradBound hVlasov hAmpere hGauss hDivB
  exact ⟨T_eq, B₀, hT_pos, hf_eq, hE_zero, hB_const,
    fun T' hT' h_eq => equilibriumMaxwellian_T_injective ρ_ion T' T_eq hρ_ion hT' hT_pos h_eq⟩

end VML
