/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Defs

/-!
# VML Data Structures

Defines the core data structures for the VML steady state problem:
- `VMLSteadyState`: intermediate bundle of derived facts
- `VMLEquilibrium`: the equilibrium configuration
- `VMLInput`: minimal physical input for the steady state problem
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 6: VML Steady State Structure
-- ============================================================================

/-- Intermediate bundle of DERIVED facts about a VML steady state on T³ × ℝ³.

    This is NOT an input specification — all fields are proved from physical
    hypotheses in `VMLInput.toSteadyState` (VMLInputDerive.lean). It serves as
    an internal API between the derivation logic (Sections 3-7) and the final
    assembly (`main_steady_state`).

    Encodes:
    - The VML equations at steady state (Vlasov, Ampère, Gauss, div B = 0)
    - Analytical results from the H-theorem chain (Sections 3-4 of tex)
    - Polynomial matching results (Section 5 of tex)
    - Maximum principle conclusion (Section 7 of tex) -/
structure VMLSteadyState (X : Type*) [FlatTorus3 X] where
  /-- A distinguished base point of the spatial domain. -/
  x₀ : X
  /-- The velocity distribution function `f(x, v)`. -/
  f : X → (Fin 3 → ℝ) → ℝ
  /-- The electric field. -/
  E : X → (Fin 3 → ℝ)
  /-- The magnetic field. -/
  B : X → (Fin 3 → ℝ)
  /-- The collision frequency. -/
  ν : ℝ
  /-- The (constant) ion background charge density. -/
  ρ_ion : ℝ
  /-- The collision kernel weight `Ψ`. -/
  Ψ : ℝ → ℝ
  hν : 0 < ν
  hρ_ion : 0 < ρ_ion
  hΨ : ∀ r, 0 < Ψ r
  hf_pos : ∀ x v, 0 < f x v
  /-- The charge density `ρ(x) = ∫ f(x, v) dv`. -/
  ρ : X → ℝ
  hρ_pos : ∀ x, 0 < ρ x
  hρ_cont : Continuous ρ
  /-- The current density. -/
  J : X → (Fin 3 → ℝ)
  -- Maxwell equations at steady state
  hAmpere : ∀ x, FlatTorus3.curlX B x = J x
  hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion
  hDivB : ∀ x, FlatTorus3.divX B x = 0
  -- Spatial differentiability for B (needed for harmonic → constant)
  hDiff_B : ∀ i, FlatTorus3.IsSpatiallySmooth 2 (fun y => B y i)
  -- === H-theorem chain results (Sections 3-4 of tex) ===
  /-- The local log-density parameter `a(x)` in the Maxwellian form of `f`. -/
  a_loc : X → ℝ
  /-- The local drift parameter `b(x)` in the Maxwellian form of `f`. -/
  b_loc : X → (Fin 3 → ℝ)
  /-- The local inverse-temperature parameter `c(x)` in the Maxwellian form of `f`. -/
  c_loc : X → ℝ
  hc_neg : ∀ x, c_loc x < 0
  hMaxwellianForm : ∀ x v,
    f x v = Real.exp (a_loc x + dotProduct (b_loc x) v + c_loc x * normSq v)
  -- === Polynomial matching results (Section 5 of tex) ===
  /-- The constant value of `c_loc`. -/
  c₀ : ℝ
  hc₀_neg : c₀ < 0
  hc_const : ∀ x, c_loc x = c₀
  /-- The constant drift direction `b₀`. -/
  b₀ : Fin 3 → ℝ
  hb_const : ∀ x, b_loc x = (-2 * c₀) • b₀
  hForceBalance : ∀ x,
    FlatTorus3.gradX a_loc x = -(2 * c₀) • (E x + cross b₀ (B x))
  hJ_def : ∀ x, J x = (ρ x) • b₀
  -- === Maximum principle (Section 7 of tex) ===
  hDensityConst : ∀ x, ρ x = ρ_ion
  hGradA_zero : b₀ = 0 → (∀ x, ρ x = ρ_ion) → ∀ x, FlatTorus3.gradX a_loc x = 0
  -- === Normalization (Gaussian integral) ===
  hNormalization : b₀ = 0 → (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

-- ============================================================================
-- The equilibrium configuration of a VML steady state.
-- ============================================================================

/-- The equilibrium configuration of a VML steady state. -/
structure VMLEquilibrium where
  /-- The equilibrium temperature. -/
  T : ℝ
  /-- The equilibrium (constant) magnetic field. -/
  B₀ : Fin 3 → ℝ
  hT : 0 < T

-- ============================================================================
-- Minimal physical input for the VML steady state problem.
-- ============================================================================

/-- Minimal physical input for the VML steady state problem.

    Contains:
    - The physical state (f, E, B) on a spatial domain X with [FlatTorus3 X]
    - Physical parameters (ν, ρ_ion, Ψ)
    - Maxwell equations at steady state
    - Entropy dissipation vanishes (from H-theorem chain)
    - Analytical interface hypotheses (polynomial identity, Gaussian integrals)

    The spatial operators (grad, div, curl, ∫) and their properties come from
    the FlatTorus3 typeclass instance, NOT from this structure.

    The key distinction from VMLSteadyState: this structure does NOT include
    the Maxwellian parameters (a, b, c), temperature/drift constancy, or
    density constancy — those are DERIVED in toSteadyState. -/
structure VMLInput (X : Type*) [FlatTorus3 X] where
  /-- A distinguished base point of the spatial domain. -/
  x₀ : X
  -- Physical state
  /-- The velocity distribution function `f(x, v)`. -/
  f : X → (Fin 3 → ℝ) → ℝ
  /-- The electric field. -/
  E : X → (Fin 3 → ℝ)
  /-- The magnetic field. -/
  B : X → (Fin 3 → ℝ)
  /-- The collision frequency. -/
  ν : ℝ
  /-- The (constant) ion background charge density. -/
  ρ_ion : ℝ
  /-- The collision kernel weight `Ψ`. -/
  Ψ : ℝ → ℝ
  -- Positivity
  hν : 0 < ν
  hρ_ion : 0 < ρ_ion
  hΨ : ∀ r, 0 < Ψ r
  hf_pos : ∀ x v, 0 < f x v
  -- Smoothness
  hf_smooth : ∀ x, ContDiff ℝ 3 (f x)
  -- Integrability (f(x,·) ∈ L¹(ℝ³) for each x)
  hf_int : ∀ x, Integrable (f x)
  -- Derived densities
  /-- The charge density `ρ(x) = ∫ f(x, v) dv`. -/
  ρ : X → ℝ
  hρ_eq : ∀ x, ρ x = ∫ v, f x v
  hρ_pos : ∀ x, 0 < ρ x
  hρ_cont : Continuous ρ
  /-- The current density. -/
  J : X → (Fin 3 → ℝ)
  -- Maxwell equations at steady state
  hAmpere : ∀ x, FlatTorus3.curlX B x = J x
  hGauss : ∀ x, FlatTorus3.divX E x = ρ x - ρ_ion
  hDivB : ∀ x, FlatTorus3.divX B x = 0
  -- Spatial differentiability for f(·,v): each slice f(·,v) is spatially C¹
  hDiff_fv : ∀ v, FlatTorus3.IsSpatiallySmooth 2 (fun x => f x v)
  -- Spatial differentiability for B components
  hDiff_B : ∀ i, FlatTorus3.IsSpatiallySmooth 2 (fun y => B y i)
  -- === Derived from H-theorem chain ===
  hD_zero : ∀ x, entropyDissipation Ψ (f x) = 0
  hScoreForm : ∀ x, entropyDissipation Ψ (f x) =
    -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ (f x) v w
  hPSD_cont : ∀ x, Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
    PSDIntegrand Ψ (f x) p.1 p.2)
  hPSD_inner : ∀ x v, Integrable (PSDIntegrand Ψ (f x) v)
  hPSD_outer : ∀ x, Integrable (fun v => ∫ w, PSDIntegrand Ψ (f x) v w)
  -- === Analytical interface hypotheses ===
  -- Maxwellian parameters are spatially differentiable (follows from f being smooth)
  hDiff_maxwellian : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    FlatTorus3.IsSpatiallySmooth 2 a ∧
    (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => b y j)) ∧
    FlatTorus3.IsSpatiallySmooth 2 c
  -- Note: hDiff_B_C2 and hDiff_maxwellian_C2 are now DERIVED via FlatTorus3.hDiff_grad.
  hPolynomialIdentity : ∀ (a : X → ℝ) (b : X → Fin 3 → ℝ) (c : X → ℝ),
    FlatTorus3.IsSpatiallySmooth 2 a →
    (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => b y j)) →
    FlatTorus3.IsSpatiallySmooth 2 c →
    (∀ x v, f x v = Real.exp (a x + dotProduct (b x) v + c x * normSq v)) →
    ∀ x v,
      dotProduct v (FlatTorus3.gradX c x) * normSq v +
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => b y j) x i)) +
      dotProduct v (FlatTorus3.gradX a x) +
      dotProduct (E x) (b x) +
      dotProduct v ((2 * c x) • E x + cross (B x) (b x)) = 0
  -- Current from Maxwellian: J = ρ · drift
  hJ_from_maxwellian : ∀ (b : X → Fin 3 → ℝ) (c₀ : ℝ),
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + dotProduct (b x) v + c₀ * normSq v)) →
    ∀ x, J x = ρ x • ((-1 / (2 * c₀)) • b x)
  -- Maximum principle inputs (compactness of T³)
  /-- A point where `ρ` attains its maximum (exists by compactness of T³). -/
  x_max : X
  hmax : ∀ x, ρ x ≤ ρ x_max
  /-- A point where `ρ` attains its minimum (exists by compactness of T³). -/
  x_min : X
  hmin : ∀ x, ρ x_min ≤ ρ x
  -- Poisson-Boltzmann equation: T Δ(log ρ) = ρ - ρ_ion (isotropic case: b₀ = 0)
  hPB_eq : ∀ (c₀ : ℝ), c₀ < 0 →
    (∀ x, ∃ a₀, ∀ v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    ∀ x, (-1 / (2 * c₀)) * FlatTorus3.divX (FlatTorus3.gradX (Real.log ∘ ρ)) x =
      ρ x - ρ_ion
  -- Normalization: Gaussian integral yields equilibriumMaxwellian
  hNormalization : ∀ a₀ c₀,
    c₀ < 0 →
    (∀ x v, f x v = Real.exp (a₀ + c₀ * normSq v)) →
    (∀ x, ρ x = ρ_ion) →
    ∀ x v, f x v = equilibriumMaxwellian ρ_ion (-1 / (2 * c₀)) v

end VML
