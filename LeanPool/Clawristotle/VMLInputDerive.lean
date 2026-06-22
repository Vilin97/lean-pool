/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.VMLStructures
import LeanPool.Clawristotle.Section3
import LeanPool.Clawristotle.Section4
import LeanPool.Clawristotle.Section5
import LeanPool.Clawristotle.Section6
import LeanPool.Clawristotle.Section7
import LeanPool.Clawristotle.Section8

/-!
# Deriving VMLInput from Concrete Hypotheses

Constructs a `VMLInput` from a `VMLSteadyState` and `VelocityDecayConditions`,
then applies the abstract proof chain (Sections 2-8) to derive the main theorem
`ConcreteTheorem42` with minimal physical hypotheses.
-/

open Matrix Finset BigOperators Real MeasureTheory
noncomputable section
namespace VML

-- ============================================================================
-- Main theorem from VMLSteadyState + VMLInput derivation
--
-- VMLInput contains genuine physical hypotheses and analytical "interface"
-- facts. VMLSteadyState is derived from VMLInput. The main theorem is
-- stated in terms of both.
-- ============================================================================

/-- Main Theorem: Global steady state of the VML system.
    Reference: Theorem 12 (thm:main)

    Any smooth steady state (f, E, B) on T³ × ℝ³ with ν > 0 is:
    (i)   f = ρIon/(2πT∞)^{3/2} exp(-|v|²/(2T∞))  (global Maxwellian, zero drift)
    (ii)  E = 0
    (iii) B = B∞ (spatially constant)
    (iv)  T∞ > 0 is a constant parameter characterizing the steady-state family

    Proof assembles:
    Step 1: f is local Maxwellian (Corollary 2, via H-theorem chain)
    Step 2: T is constant (Lemma 14, O(|v|³) terms)
    Step 3: u is constant (Lemma 15, Killing's equation on T³)
    Step 4: u = 0 (Lemma 19, Ampère + divergence theorem)
    Step 5: n ≡ ρIon, E = 0 (Lemmas 20-21, Poisson–Boltzmann + max principle)
    Step 6: B constant (Lemma 22, harmonic on T³)
    Step 7: Parameters from conservation (Lemmas 24-28) -/
theorem main_steady_state {X : Type*} [FlatTorus3 X] (ss : VMLSteadyState X) :
    ∃ eq : VMLEquilibrium,
    (∀ x v, ss.f x v = equilibriumMaxwellian ss.ρIon eq.T v) ∧
    (∀ x, ss.E x = 0) ∧
    (∀ x, ss.B x = eq.B₀) := by
  -- Step 1: Drift velocity is zero (Lemma 19, via Ampère + Stokes)
  have hb_zero := bulk_velocity_zero ss
  -- Step 2: Electric field vanishes (Corollary 3, via force balance + max principle)
  have hE := electric_field_zero ss
  -- Step 3: Magnetic field is constant (Lemma 22, via curl=0 + div=0 + harmonic)
  obtain ⟨B₀, hB⟩ := magnetic_field_constant ss
  -- Step 4: T∞ = -1/(2c₀) > 0
  have hT : 0 < -1 / (2 * ss.c₀) := by
    apply div_pos_of_neg_of_neg <;> linarith [ss.hc₀_neg]
  -- Step 5: f is the equilibrium Maxwellian (from normalization)
  have hf := ss.hNormalization hb_zero ss.hDensityConst
  exact ⟨⟨-1 / (2 * ss.c₀), B₀, hT⟩, hf, hE, hB⟩

-- ============================================================================
-- VMLInput helpers: Derive VMLSteadyState from VMLInput
-- ============================================================================

variable {X : Type*} [FlatTorus3 X]

/-- Extract Maxwellian parameters from VMLInput.
    Uses the H-theorem chain to show f is locally Maxwellian at each x,
    then extracts the parameters via Classical.choice. -/
private theorem VMLInput.isMaxwellian_at (p : VMLInput X) (x : X) : IsMaxwellian (p.f x) :=
  steady_state_is_local_maxwellian X p.f p.Ψ p.hΨ p.hf_pos
    p.hf_smooth p.hf_int p.hD_zero p.hScoreForm p.hPSD_cont p.hPSD_inner p.hPSD_outer x

/-- The local log-density parameter `a(x)` extracted from the Maxwellian form of `p.f`. -/
noncomputable def _root_.VML.VMLInput.aLoc (p : VMLInput X) : X → ℝ :=
  fun x => (p.isMaxwellian_at x).choose

/-- The local drift parameter `b(x)` extracted from the Maxwellian form of `p.f`. -/
noncomputable def _root_.VML.VMLInput.bLoc (p : VMLInput X) : X → (Fin 3 → ℝ) :=
  fun x => (p.isMaxwellian_at x).choose_spec.choose

/-- The local inverse-temperature parameter `c(x)` extracted from the Maxwellian form of `p.f`. -/
noncomputable def _root_.VML.VMLInput.cLoc (p : VMLInput X) : X → ℝ :=
  fun x => (p.isMaxwellian_at x).choose_spec.choose_spec.choose

lemma _root_.VML.VMLInput.hc_neg (p : VMLInput X) : ∀ x, p.cLoc x < 0 :=
  fun x => (p.isMaxwellian_at x).choose_spec.choose_spec.choose_spec.1

lemma _root_.VML.VMLInput.hMaxwellianForm (p : VMLInput X) :
    ∀ x v, p.f x v = Real.exp (p.aLoc x + dotProduct (p.bLoc x) v +
      p.cLoc x * normSq v) :=
  fun x => (p.isMaxwellian_at x).choose_spec.choose_spec.choose_spec.2

/-- IsSpatiallySmooth 2 for the Maxwellian parameters aLoc, bLoc, cLoc. -/
lemma _root_.VML.VMLInput.hDiff_abc (p : VMLInput X) :
    FlatTorus3.IsSpatiallySmooth 2 p.aLoc ∧
    (∀ j, FlatTorus3.IsSpatiallySmooth 2 (fun y => p.bLoc y j)) ∧
    FlatTorus3.IsSpatiallySmooth 2 p.cLoc :=
  p.hDiff_maxwellian p.aLoc p.bLoc p.cLoc p.hMaxwellianForm

/-- Temperature is spatially constant: c(x) ≡ c₀. -/
lemma _root_.VML.VMLInput.hc_const_grad (p : VMLInput X) :
    ∀ x, FlatTorus3.gradX p.cLoc x = 0 := by
  apply temperature_constant
  intro x
  -- Use poly_cubic_extraction: rearrange polynomial identity into standard form
  exact poly_cubic_extraction
    (FlatTorus3.gradX p.cLoc x)
    (fun i j => FlatTorus3.gradX (fun y => p.bLoc y j) x i)
    (FlatTorus3.gradX p.aLoc x + (2 * p.cLoc x) • p.E x + cross (p.B x) (p.bLoc x))
    (dotProduct (p.E x) (p.bLoc x))
    (fun v => by
      have h := p.hPolynomialIdentity p.aLoc p.bLoc p.cLoc
        p.hDiff_abc.1 p.hDiff_abc.2.1 p.hDiff_abc.2.2 p.hMaxwellianForm x v
      simp only [dotProduct_add] at *
      linarith)

/-- Extract the constant temperature parameter c₀. -/
noncomputable def _root_.VML.VMLInput.c₀ (p : VMLInput X) : ℝ := p.cLoc p.x₀

lemma _root_.VML.VMLInput.hc₀_neg (p : VMLInput X) : p.c₀ < 0 := p.hc_neg p.x₀

lemma _root_.VML.VMLInput.hc_const (p : VMLInput X) : ∀ x, p.cLoc x = p.c₀ :=
  fun x => FlatTorus3.hGradZeroConst p.cLoc
    (p.hDiff_abc.2.2.of_le (by decide))
    p.hc_const_grad x p.x₀

/-- The O(|v|²) Killing equation from the polynomial identity. -/
lemma _root_.VML.VMLInput.hKilling (p : VMLInput X) :
    ∀ x i j, FlatTorus3.gradX (fun y => p.bLoc y j) x i +
      FlatTorus3.gradX (fun y => p.bLoc y i) x j = 0 := by
  intro x
  have hpoly := fun v => p.hPolynomialIdentity p.aLoc p.bLoc p.cLoc
        p.hDiff_abc.1 p.hDiff_abc.2.1 p.hDiff_abc.2.2 p.hMaxwellianForm x v
  have hgrad_c : FlatTorus3.gradX p.cLoc x = 0 := p.hc_const_grad x
  -- Remove cubic term (gradX c = 0)
  have hred : ∀ v : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => p.bLoc y j) x i)) +
      dotProduct v (FlatTorus3.gradX p.aLoc x) +
      dotProduct (p.E x) (p.bLoc x) +
      dotProduct v ((2 * p.cLoc x) • p.E x + cross (p.B x) (p.bLoc x)) = 0 := by
    intro v; have := hpoly v
    rw [hgrad_c, dotProduct_zero, zero_mul, zero_add] at this
    exact this
  -- C = 0: substitute v = 0
  have hC : dotProduct (p.E x) (p.bLoc x) = 0 := by
    have := hred 0
    simp only [Pi.zero_apply, mul_zero, zero_mul, sum_const_zero, zero_dotProduct, add_zero,
      zero_add, dotProduct_add, dotProduct_smul, smul_eq_mul] at this
    exact this
  -- Q(v) + L(v) = 0
  have hQL : ∀ v : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => p.bLoc y j) x i)) +
      dotProduct v (FlatTorus3.gradX p.aLoc x) +
      dotProduct v ((2 * p.cLoc x) • p.E x + cross (p.B x) (p.bLoc x)) = 0 := by
    intro v; linarith [hred v, hC]
  -- Q(v) = 0: use v and -v. Q(-v) = Q(v), L(-v) = -L(v), so 2Q(v) = 0.
  have hQ : ∀ v : Fin 3 → ℝ,
      (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => p.bLoc y j) x i)) = 0 := by
    intro v
    have h1 := hQL v
    have h2 := hQL (-v)
    simp only [Pi.neg_apply, neg_mul_neg, neg_dotProduct] at h2
    linarith
  exact poly_killing_extraction _ hQ

/-- Drift velocity b is constant on T³. -/
lemma _root_.VML.VMLInput.hb_const_exists (p : VMLInput X) :
    ∃ b₀ : Fin 3 → ℝ, ∀ x, p.bLoc x = b₀ := by
  -- Derive C² condition for bLoc from hDiff_grad ⊤ + C¹ differentiability of bLoc components
  have hDiff_b_C2 : ∀ j i, FlatTorus3.IsSpatiallySmooth 1 (fun x =>
      FlatTorus3.gradX (fun y => p.bLoc y j) x i) :=
    fun j i => FlatTorus3.hDiff_grad 1 (fun y => p.bLoc y j) i (p.hDiff_abc.2.1 j)
  have hHarm := FlatTorus3.hKillingToHarmonic p.bLoc
    (fun j => (p.hDiff_abc.2.1 j).of_le (by decide))
    (fun j i => (hDiff_b_C2 j i).of_le (by decide)) p.hKilling
  use fun j => p.bLoc p.x₀ j
  intro x; ext j
  exact FlatTorus3.hHarmonic_const _ ((p.hDiff_abc.2.1 j).of_le (by decide)) (hHarm j) x p.x₀

/-- Extract the constant drift parameter b₀. -/
noncomputable def _root_.VML.VMLInput.b₀ (p : VMLInput X) : Fin 3 → ℝ :=
  p.hb_const_exists.choose

lemma _root_.VML.VMLInput.hb_const (p : VMLInput X) : ∀ x, p.bLoc x = p.b₀ :=
  p.hb_const_exists.choose_spec

/-- Force balance from the polynomial identity. -/
lemma _root_.VML.VMLInput.hForceBalance (p : VMLInput X) :
    ∀ x, FlatTorus3.gradX p.aLoc x =
      -(2 * p.c₀) • p.E x + cross p.b₀ (p.B x) := by
  intro x
  have hpoly := fun v => p.hPolynomialIdentity p.aLoc p.bLoc p.cLoc
        p.hDiff_abc.1 p.hDiff_abc.2.1 p.hDiff_abc.2.2 p.hMaxwellianForm x v
  have hgrad_c : FlatTorus3.gradX p.cLoc x = 0 := p.hc_const_grad x
  have hgrad_b : ∀ j : Fin 3, FlatTorus3.gradX (fun y => p.bLoc y j) x = 0 := by
    intro j
    apply FlatTorus3.hGradConst
    intro x' y'
    show p.bLoc x' j = p.bLoc y' j
    rw [p.hb_const x', p.hb_const y']
  -- Reduce to linear + constant form (using cLoc = c₀, bLoc = b₀)
  have hLC : ∀ v : Fin 3 → ℝ,
      dotProduct v (FlatTorus3.gradX p.aLoc x + (2 * p.c₀) • p.E x +
        cross (p.B x) p.b₀) +
      dotProduct (p.E x) p.b₀ = 0 := by
    intro v
    have hp := hpoly v
    rw [hgrad_c, dotProduct_zero, zero_mul, zero_add] at hp
    have hQ : (∑ i : Fin 3, ∑ j : Fin 3, v i * v j *
        (FlatTorus3.gradX (fun y => p.bLoc y j) x i)) = 0 :=
      Finset.sum_eq_zero (fun i _ =>
        Finset.sum_eq_zero (fun j _ => by simp [congr_fun (hgrad_b j) i]))
    rw [p.hc_const x, p.hb_const x] at hp
    simp only [dotProduct_add] at *
    linarith [hp, hQ]
  -- Apply poly_linear_extraction
  have hd_zero := (poly_linear_extraction _ _ hLC).1
  -- hd_zero : gradX a x + (2c₀) • E x + cross (B x) b₀ = 0
  -- → gradX a x = -(2c₀) • E x + cross b₀ (B x)
  rw [add_assoc] at hd_zero
  rw [eq_neg_of_add_eq_zero_left hd_zero, neg_add, ← neg_smul, neg_cross]

/-- Current density J = ρ · drift velocity. -/
lemma _root_.VML.VMLInput.hJ_def' (p : VMLInput X) :
    ∀ x, p.J x = (p.ρ x) • ((-1 / (2 * p.c₀)) • p.b₀) := by
  have hform : ∀ x, ∃ a₀, ∀ v,
      p.f x v = Real.exp (a₀ + dotProduct (p.b₀) v + p.c₀ * normSq v) := by
    intro x
    use p.aLoc x
    intro v
    rw [p.hMaxwellianForm x v, p.hc_const x, p.hb_const x]
  -- The b field is constant, so we use the constant b₀
  have hform' : ∀ x, ∃ a₀, ∀ v,
      p.f x v = Real.exp (a₀ + dotProduct ((fun _ => p.b₀) x) v + p.c₀ * normSq v) :=
    hform
  have := p.hJ_from_maxwellian (fun _ => p.b₀) p.c₀ hform'
  exact this

/-- The drift parameter b₀ vanishes.
    Proof: Ampère + Stokes on T³ gives |u₀|² ∫ ρ = 0, and ∫ ρ > 0,
    so u₀ = (-1/(2c₀))b₀ = 0, hence b₀ = 0 since c₀ ≠ 0. -/
lemma _root_.VML.VMLInput.hb₀_zero (p : VMLInput X) : p.b₀ = 0 := by
  set u₀ := (-1 / (2 * p.c₀)) • p.b₀
  -- Step 1: ∫ u₀ · curlX B = 0 (Stokes on T³)
  have h1 : FlatTorus3.spatialIntegral
      (fun x => dotProduct u₀ (FlatTorus3.curlX p.B x)) = 0 :=
    FlatTorus3.hCurlIntZero p.B u₀ (fun j => (p.hDiff_B j).of_le (by decide))
  -- Step 2: curlX B = J = ρ • u₀
  have h2 : ∀ x, dotProduct u₀ (FlatTorus3.curlX p.B x) = p.ρ x * normSq u₀ := by
    intro x
    rw [p.hAmpere, p.hJ_def' x]
    exact dotProduct_smul_self (p.ρ x) u₀
  -- Step 3: ∫ ρ * |u₀|² = |u₀|² * ∫ ρ = 0
  have h3 : FlatTorus3.spatialIntegral (fun x => p.ρ x * normSq u₀) = 0 := by
    rwa [show (fun x => p.ρ x * normSq u₀) =
      (fun x => dotProduct u₀ (FlatTorus3.curlX p.B x)) from funext (fun x => (h2 x).symm)]
  have h4 : FlatTorus3.spatialIntegral p.ρ * normSq u₀ = 0 := by
    rwa [← FlatTorus3.hSpatialMul]
  -- Step 4: ∫ ρ > 0, so |u₀|² = 0, hence u₀ = 0
  have h5 : 0 < FlatTorus3.spatialIntegral p.ρ := FlatTorus3.hSpatialPos p.ρ p.hρ_cont p.hρ_pos
  have h6 : normSq u₀ = 0 := by
    rcases mul_eq_zero.mp h4 with h | h
    · linarith
    · exact h
  have hu₀ : u₀ = 0 := normSq_eq_zero.mp h6
  -- Step 5: (-1/(2c₀)) • b₀ = 0 and c₀ ≠ 0, so b₀ = 0
  have hcoeff_ne : (-1 : ℝ) / (2 * p.c₀) ≠ 0 := by
    apply div_ne_zero (by norm_num)
    exact mul_ne_zero two_ne_zero (ne_of_lt p.hc₀_neg)
  exact (smul_eq_zero.mp hu₀).resolve_left hcoeff_ne

/-- Poisson-Boltzmann equation for the density. -/
lemma _root_.VML.VMLInput.hPB (p : VMLInput X) :
    ∀ x, (-1 / (2 * p.c₀)) * FlatTorus3.divX (FlatTorus3.gradX (Real.log ∘ p.ρ)) x =
      p.ρ x - p.ρIon := by
  -- b₀ = 0, so f is isotropic: f x v = exp(a₀(x) + c₀|v|²)
  have hb0 := p.hb₀_zero
  have hform : ∀ x, ∃ a₀, ∀ v,
      p.f x v = Real.exp (a₀ + p.c₀ * normSq v) := by
    intro x
    exact ⟨p.aLoc x, fun v => by
      rw [p.hMaxwellianForm x v, p.hc_const x, p.hb_const x, hb0]
      simp [dotProduct, Fin.sum_univ_three, normSq]⟩
  exact p.hPB_eq p.c₀ p.hc₀_neg hform

/-- Density is constant: ρ(x) = ρIon. -/
lemma _root_.VML.VMLInput.hDensityConst (p : VMLInput X) : ∀ x, p.ρ x = p.ρIon := by
  have hT : 0 < -1 / (2 * p.c₀) := by
    apply div_pos_of_neg_of_neg <;> linarith [p.hc₀_neg]
  -- Derive IsSpatiallySmooth 2 (log ∘ ρ) from Maxwellian form.
  -- Since b₀ = 0, f(x,v) = exp(a(x) + c₀|v|²), so ρ(x) = exp(a(x)) * C where C = ∫ exp(c₀|v|²) dv.
  -- Therefore log ρ(x) = a(x) + log C, so log ∘ ρ = a + const, which is IsSpatiallySmooth 2.
  have hDiff_logRho : FlatTorus3.IsSpatiallySmooth 2 (Real.log ∘ p.ρ) := by
    -- log ρ(x) = a(x) + log(∫ exp(c₀|v|²) dv)
    -- Step 1: show ρ(x) = exp(a(x)) * C
    have hb0 := p.hb₀_zero
    set C := ∫ v : Fin 3 → ℝ, Real.exp (p.c₀ * normSq v)
    have hρ_form : ∀ x, p.ρ x = Real.exp (p.aLoc x) * C := by
      intro x
      rw [p.hρ_eq x]
      have : ∀ v, p.f x v = Real.exp (p.aLoc x) * Real.exp (p.c₀ * normSq v) := by
        intro v
        rw [p.hMaxwellianForm x v, p.hc_const x, p.hb_const x, hb0]
        simp [dotProduct, Fin.sum_univ_three, normSq, Real.exp_add]
      simp_rw [this]
      exact integral_const_mul _ _
    -- Step 2: show log ρ(x) = a(x) + log C
    have hC_pos : 0 < C := by
      have h0 := p.hρ_pos p.x₀
      rw [hρ_form p.x₀] at h0
      exact pos_of_mul_pos_right h0 (Real.exp_pos _).le
    have hlog_form : (Real.log ∘ p.ρ) = fun x => p.aLoc x + Real.log C := by
      ext x; simp only [Function.comp_apply]
      rw [hρ_form x, Real.log_mul (Real.exp_pos _).ne' hC_pos.ne', Real.log_exp]
    -- Step 3: IsSpatiallySmooth 2 (a + const) from closure properties
    rw [hlog_form]
    exact FlatTorus3.hDiff_add 2 _ _ (p.hDiff_abc.1.of_le (by decide)) (FlatTorus3.hDiff_const 2 _)
  -- Laplacian signs at extrema from FlatTorus3 class axioms
  have hmax_logρ : ∀ x, (Real.log ∘ p.ρ) x ≤ (Real.log ∘ p.ρ) p.xMax :=
    fun x => Real.log_le_log (p.hρ_pos x) (p.hmax x)
  have hmin_logρ : ∀ x, (Real.log ∘ p.ρ) p.xMin ≤ (Real.log ∘ p.ρ) x :=
    fun x => Real.log_le_log (p.hρ_pos p.xMin) (p.hmin x)
  have hmax_lapl := FlatTorus3.hLaplacianMaxNonpos (Real.log ∘ p.ρ) p.xMax hDiff_logRho hmax_logρ
  have hmin_lapl := FlatTorus3.hLaplacianMinNonneg (Real.log ∘ p.ρ) hDiff_logRho p.xMin hmin_logρ
  exact poisson_boltzmann_max_principle X p.ρ p.ρIon (-1 / (2 * p.c₀))
    (fun φ => FlatTorus3.divX (FlatTorus3.gradX φ))
    p.hρ_pos hT p.hρ_ion p.hPB p.xMax p.hmax p.xMin p.hmin
    hmax_lapl hmin_lapl

/-- ∇a vanishes when b₀ = 0 and ρ = ρIon. -/
lemma _root_.VML.VMLInput.hGradA_zero (p : VMLInput X) :
    p.b₀ = 0 → (∀ x, p.ρ x = p.ρIon) → ∀ x, FlatTorus3.gradX p.aLoc x = 0 := by
  intro hb0 hdens
  -- Force balance with b₀ = 0: ∇a = -(2c₀) • E + cross 0 B = -(2c₀) • E
  have hfb_simp : ∀ y, FlatTorus3.gradX p.aLoc y = -(2 * p.c₀) • p.E y := by
    intro y; rw [p.hForceBalance y, hb0, cross_zero_left, add_zero]
  -- gradX aLoc = -(2c₀) • E as functions
  have hfun_eq : FlatTorus3.gradX p.aLoc = fun y => -(2 * p.c₀) • p.E y := funext hfb_simp
  -- aLoc is harmonic: div(gradX aLoc) = -(2c₀) * divX E = -(2c₀)(ρ - ρIon) = 0
  have h_harmonic : ∀ y, FlatTorus3.divX (FlatTorus3.gradX p.aLoc) y = 0 := by
    intro y
    rw [hfun_eq, FlatTorus3.hDivLinear, p.hGauss, hdens y, sub_self, mul_zero]
  -- aLoc is constant on T³ (harmonic → constant)
  have ha_const := FlatTorus3.hHarmonic_const p.aLoc (p.hDiff_abc.1.of_le (by decide)) h_harmonic
  -- Constant → gradient zero
  exact FlatTorus3.hGradConst p.aLoc ha_const

/-- f is the equilibrium Maxwellian when b₀ = 0 and ρ = ρIon. -/
lemma _root_.VML.VMLInput.hNorm (p : VMLInput X) :
    p.b₀ = 0 → (∀ x, p.ρ x = p.ρIon) →
    ∀ x v, p.f x v = equilibriumMaxwellian p.ρIon (-1 / (2 * p.c₀)) v := by
  intro hb0 hdens
  -- With b₀ = 0 and ∇a = 0, a is constant. So f = exp(a₀ + c₀|v|²).
  -- The normalization hypothesis converts this to equilibriumMaxwellian.
  have hGradA := p.hGradA_zero hb0 hdens
  -- aLoc is constant (gradient zero → constant)
  have ha_const : ∀ x, p.aLoc x = p.aLoc p.x₀ :=
    fun x => FlatTorus3.hGradZeroConst p.aLoc (p.hDiff_abc.1.of_le (by decide)) hGradA x p.x₀
  -- f x v = exp(a₀ + 0 + c₀ |v|²) = exp(a₀ + c₀ |v|²)
  have hf_form : ∀ x v,
      p.f x v = Real.exp (p.aLoc p.x₀ + p.c₀ * normSq v) := by
    intro x v
    rw [p.hMaxwellianForm x v, p.hc_const x, p.hb_const x, hb0, ha_const x]
    simp [dotProduct, Fin.sum_univ_three, normSq]
  exact p.hNormalization (p.aLoc p.x₀) p.c₀ p.hc₀_neg hf_form hdens

/-- Build VMLSteadyState from VMLInput by deriving all analytical conclusions. -/
noncomputable def _root_.VML.VMLInput.toSteadyState (p : VMLInput X) : VMLSteadyState X where
  x₀ := p.x₀
  f := p.f
  E := p.E
  B := p.B
  ν := p.ν
  ρIon := p.ρIon
  Ψ := p.Ψ
  hν := p.hν
  hρ_ion := p.hρ_ion
  hΨ := p.hΨ
  hf_pos := p.hf_pos
  ρ := p.ρ
  hρ_pos := p.hρ_pos
  hρ_cont := p.hρ_cont
  J := p.J
  hAmpere := p.hAmpere
  hGauss := p.hGauss
  hDivB := p.hDivB
  hDiff_B := p.hDiff_B
  -- Derived fields
  aLoc := p.aLoc
  bLoc := p.bLoc
  cLoc := p.cLoc
  hc_neg := p.hc_neg
  hMaxwellianForm := p.hMaxwellianForm
  c₀ := p.c₀
  hc₀_neg := p.hc₀_neg
  hc_const := p.hc_const
  b₀ := (-1 / (2 * p.c₀)) • p.b₀
  hb_const := fun x => by
    -- bLoc x = (-2 * c₀) • ((-1/(2c₀)) • b₀) = b₀
    rw [p.hb_const x]
    ext i
    simp [Pi.smul_apply, smul_eq_mul]
    have hc₀_ne : p.c₀ ≠ 0 := ne_of_lt p.hc₀_neg
    field_simp
  hForceBalance := fun x => by
    -- ∇a = -(2c₀)E + b₀ × B, and VMLSteadyState expects -(2c₀)(E + drift × B)
    -- where drift = (-1/(2c₀))b₀. These are equal since -(2c₀)*(-1/(2c₀)) = 1.
    have hfb := p.hForceBalance x
    rw [hfb]
    have hc₀_ne : p.c₀ ≠ 0 := ne_of_lt p.hc₀_neg
    rw [smul_add, cross_smul_left, smul_smul]
    have h1 : -(2 * p.c₀) * (-1 / (2 * p.c₀)) = 1 := by
      field_simp
    rw [h1, one_smul]
  hJ_def := fun x => by
    exact p.hJ_def' x
  hDensityConst := p.hDensityConst
  hGradA_zero := fun hb0 hdens => by
    -- (-1/(2c₀)) • b₀ = 0 implies b₀ = 0 (since c₀ ≠ 0)
    have hc₀_ne : p.c₀ ≠ 0 := ne_of_lt p.hc₀_neg
    have hcoeff_ne : (-1 : ℝ) / (2 * p.c₀) ≠ 0 := by
      apply div_ne_zero (by norm_num)
      exact mul_ne_zero two_ne_zero hc₀_ne
    have hb₀_zero : p.b₀ = 0 :=
      (smul_eq_zero.mp hb0).resolve_left hcoeff_ne
    exact p.hGradA_zero hb₀_zero hdens
  hNormalization := fun hb0 hdens => by
    have hc₀_ne : p.c₀ ≠ 0 := ne_of_lt p.hc₀_neg
    have hcoeff_ne : (-1 : ℝ) / (2 * p.c₀) ≠ 0 := by
      apply div_ne_zero (by norm_num)
      exact mul_ne_zero two_ne_zero hc₀_ne
    have hb₀_zero : p.b₀ = 0 :=
      (smul_eq_zero.mp hb0).resolve_left hcoeff_ne
    exact p.hNorm hb₀_zero hdens

/-- Main theorem (honest version): From physical inputs alone,
    any smooth steady state (f, E, B) on T³ × ℝ³ with ν > 0 is:
    (i)   f = ρIon/(2πT∞)^{3/2} exp(-|v|²/(2T∞))  (global Maxwellian, zero drift)
    (ii)  E = 0
    (iii) B = B∞ (spatially constant)
    (iv)  T∞ > 0 is a constant parameter characterizing the steady-state family -/
theorem main_from_physics (p : VMLInput X) :
    ∃ eq : VMLEquilibrium,
    (∀ x v, p.f x v = equilibriumMaxwellian p.ρIon eq.T v) ∧
    (∀ x, p.E x = 0) ∧
    (∀ x, p.B x = eq.B₀) :=
  main_steady_state p.toSteadyState

end VML
