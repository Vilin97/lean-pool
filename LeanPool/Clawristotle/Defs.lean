/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Core Definitions for the Vlasov-Maxwell-Landau System

Defines the Landau collision operator, velocity decay conditions, the `VMLSteadyState`
structure, and the `FlatTorus3` typeclass. Also provides `@[simp]` unfolding lemmas and
small auxiliary lemmas about the definitions. Derived FlatTorus3 lemmas are in
`FlatTorus3Lemmas.lean`.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 1: Vector and Matrix Basics for ℝ³
-- ============================================================================

/-- Squared Euclidean norm: ‖z‖² = z · z = ∑ᵢ zᵢ² -/
def normSq (z : Fin 3 → ℝ) : ℝ := dotProduct z z

@[simp]
lemma normSq_zero : normSq (0 : Fin 3 → ℝ) = 0 := by
  simp [normSq, dotProduct]

lemma normSq_nonneg (z : Fin 3 → ℝ) : 0 ≤ normSq z := by
  unfold normSq dotProduct
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (a := z i)

lemma normSq_eq_zero {z : Fin 3 → ℝ} : normSq z = 0 ↔ z = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; simp [normSq, dotProduct]⟩
  unfold normSq dotProduct at h
  ext i
  exact mul_self_eq_zero.mp
    ((Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_self_nonneg (a := z i)).mp h i
      (Finset.mem_univ i))

lemma normSq_pos {z : Fin 3 → ℝ} (hz : z ≠ 0) : 0 < normSq z :=
  lt_of_le_of_ne (normSq_nonneg z) (fun h => hz (normSq_eq_zero.mp h.symm))

lemma normSq_neg (z : Fin 3 → ℝ) : normSq (-z) = normSq z := by
  simp [normSq, dotProduct, Pi.neg_apply]

/-- Euclidean norm: |z| = √(z · z) -/
def eucNorm (z : Fin 3 → ℝ) : ℝ := Real.sqrt (normSq z)

lemma eucNorm_nonneg (z : Fin 3 → ℝ) : 0 ≤ eucNorm z := Real.sqrt_nonneg _

lemma eucNorm_neg (z : Fin 3 → ℝ) : eucNorm (-z) = eucNorm z := by
  simp [eucNorm, normSq_neg]

lemma eucNorm_sq (z : Fin 3 → ℝ) : eucNorm z ^ 2 = normSq z := by
  simp [eucNorm, sq_sqrt (normSq_nonneg z)]

-- ============================================================================
-- Section 2: The Landau Collision Matrix
-- ============================================================================

/-- The inner part of the Landau matrix: B(z) = |z|² I₃ - z zᵀ.
    This is the matrix that appears inside the scalar factor Ψ(|z|). -/
def innerLandauMatrix (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  normSq z • (1 : Matrix (Fin 3) (Fin 3) ℝ) - vecMulVec z z

/-- The Landau collision matrix: A(z) = Ψ(|z|) · (|z|² I₃ - z zᵀ).
    Reference: Definition 2 (def:landau_matrix) -/
def landauMatrix (Ψ : ℝ → ℝ) (z : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Ψ (eucNorm z) • innerLandauMatrix z

lemma innerLandauMatrix_apply (z : Fin 3 → ℝ) (i j : Fin 3) :
    innerLandauMatrix z i j = (if i = j then normSq z else 0) - z i * z j := by
  simp [innerLandauMatrix, one_apply, vecMulVec_apply,
    smul_eq_mul]

-- ============================================================================
-- Section 3: Maxwellian Distributions
-- ============================================================================

/-- A Maxwellian distribution: log-quadratic with c₀ < 0 (ensuring integrability).
    Specifically: ∃ a₀ b c₀, c₀ < 0 ∧ f(v) = exp(a₀ + b · v + c₀ |v|²) -/
def IsMaxwellian (f : (Fin 3 → ℝ) → ℝ) : Prop :=
  ∃ (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ),
    c₀ < 0 ∧ ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)

/-- The Maxwellian parameters (a₀, b, c₀) are injective: if exp(a₀ + b·v + c₀|v|²) =
    exp(a₀' + b'·v + c₀'|v|²) for all v, then a₀ = a₀', b = b', c₀ = c₀'. -/
lemma IsMaxwellian_params_injective
    (a₀ a₀' : ℝ) (b b' : Fin 3 → ℝ) (c₀ c₀' : ℝ)
    (h : ∀ v : Fin 3 → ℝ, a₀ + dotProduct b v + c₀ * normSq v =
      a₀' + dotProduct b' v + c₀' * normSq v) :
    a₀ = a₀' ∧ b = b' ∧ c₀ = c₀' := by
  -- Evaluate at v = 0 to get a₀ = a₀'
  have h0 : a₀ = a₀' := by
    have := h 0; simp [dotProduct, normSq] at this; linarith
  -- Evaluate at eᵢ and 2eᵢ to get c₀ = c₀' and bᵢ = bᵢ'
  have hc : c₀ = c₀' := by
    have h1 := h (Pi.single 0 1)
    have h2 := h (Pi.single 0 2)
    simp [dotProduct, normSq, Pi.single_apply] at h1 h2
    linarith
  have hb : b = b' := by
    ext i
    have hi := h (Pi.single i 1)
    simp [dotProduct, normSq, Pi.single_apply] at hi
    fin_cases i <;> linarith
  exact ⟨h0, hb, hc⟩

/-- A Maxwellian distribution is strictly positive everywhere. -/
lemma _root_.VML.IsMaxwellian.pos (hM : IsMaxwellian f) : ∀ v, 0 < f v := by
  obtain ⟨a₀, b, c₀, _, hf⟩ := hM
  intro v; rw [hf]; exact Real.exp_pos _

/-- A Maxwellian distribution is smooth (C^∞). -/
lemma _root_.VML.IsMaxwellian.contDiff (hM : IsMaxwellian f) : ContDiff ℝ ⊤ f := by
  obtain ⟨a₀, b, c₀, _, hf⟩ := hM
  have : f = fun v => Real.exp (a₀ + dotProduct b v + c₀ * normSq v) := funext hf
  rw [this]
  apply Real.contDiff_exp.comp
  have hDot : ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => dotProduct b v) :=
    ContDiff.sum fun i _ => contDiff_const.mul (contDiff_apply ℝ ℝ i)
  have hNorm : ContDiff ℝ ⊤ (fun v : Fin 3 → ℝ => normSq v) := by
    unfold normSq dotProduct
    exact ContDiff.sum fun i _ => (contDiff_apply ℝ ℝ i).mul (contDiff_apply ℝ ℝ i)
  exact (contDiff_const.add hDot).add (contDiff_const.mul hNorm)

/-- The equilibrium Maxwellian (zero drift, density = ρIon):
    f∞(v) = ρIon/(2πT∞)^(3/2) · exp(-|v|²/(2T∞)) -/
def equilibriumMaxwellian (ρIon T : ℝ) (v : Fin 3 → ℝ) : ℝ :=
  ρIon / (2 * π * T) ^ ((3 : ℝ) / 2) *
    Real.exp (-(normSq v) / (2 * T))

/-- The equilibrium Maxwellian is a Maxwellian (i.e., satisfies `IsMaxwellian`).
    Rewrites ρ/(2πT)^{3/2} · exp(-|v|²/(2T)) = exp(log(ρ/(2πT)^{3/2}) + 0·v + (-1/(2T))|v|²). -/
lemma equilibriumMaxwellian_isMaxwellian (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) :
    IsMaxwellian (equilibriumMaxwellian ρ T) := by
  refine ⟨Real.log (ρ / (2 * π * T) ^ ((3 : ℝ) / 2)), 0, -1 / (2 * T),
    by exact div_neg_of_neg_of_pos (by norm_num) (by positivity), fun v => ?_⟩
  unfold equilibriumMaxwellian
  rw [zero_dotProduct, normSq, add_zero]
  have hpos : 0 < ρ / (2 * π * T) ^ ((3 : ℝ) / 2) :=
    div_pos hρ (Real.rpow_pos_of_pos (by positivity) _)
  conv_lhs => rw [show ρ / (2 * π * T) ^ ((3 : ℝ) / 2) =
    Real.exp (Real.log (ρ / (2 * π * T) ^ ((3 : ℝ) / 2))) from (Real.exp_log hpos).symm]
  rw [← Real.exp_add]
  congr 1; ring

/-- The equilibrium temperature T is an injective parameter: if two Maxwellians with
    the same density agree as functions, their temperatures must be equal. -/
lemma equilibriumMaxwellian_T_injective (ρ T₁ T₂ : ℝ) (hρ : 0 < ρ) (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h : ∀ v, equilibriumMaxwellian ρ T₁ v = equilibriumMaxwellian ρ T₂ v) : T₁ = T₂ := by
  -- Evaluate at v = 0: ρ/(2πT₁)^{3/2} * 1 = ρ/(2πT₂)^{3/2} * 1
  have h0 := h 0
  simp only [equilibriumMaxwellian, normSq_zero, neg_zero, zero_div, Real.exp_zero, mul_one] at h0
  -- Cancel ρ: (2πT₁)^{3/2} = (2πT₂)^{3/2}
  have hπT₁ : (0 : ℝ) < 2 * π * T₁ := by positivity
  have hπT₂ : (0 : ℝ) < 2 * π * T₂ := by positivity
  have h_eq : (2 * π * T₁) ^ ((3 : ℝ) / 2) = (2 * π * T₂) ^ ((3 : ℝ) / 2) := by
    field_simp at h0; linarith
  -- rpow injectivity: 2πT₁ = 2πT₂, hence T₁ = T₂
  have h_base := Real.rpow_left_injOn (by norm_num : (3 : ℝ) / 2 ≠ 0)
    (Set.mem_Ici.mpr (le_of_lt hπT₁)) (Set.mem_Ici.mpr (le_of_lt hπT₂)) h_eq
  nlinarith [Real.pi_pos]

/-- The equilibrium Maxwellian is strictly positive for ρ > 0, T > 0. -/
lemma equilibriumMaxwellian_pos (ρ T : ℝ) (hρ : 0 < ρ) (hT : 0 < T) (v : Fin 3 → ℝ) :
    0 < equilibriumMaxwellian ρ T v := by
  unfold equilibriumMaxwellian
  apply mul_pos
  · apply div_pos hρ
    exact Real.rpow_pos_of_pos (by positivity) _
  · exact Real.exp_pos _

-- ============================================================================
-- Section 3b: Velocity Calculus
-- ============================================================================

/-- Velocity gradient: ∇ᵥf(v), the vector of partial derivatives of f at v.
    Uses Fréchet derivative from Mathlib. -/
def vGrad (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => fderiv ℝ f v (Pi.single i 1)

/-- Velocity divergence: ∇ᵥ · F(v) = ∑ᵢ ∂Fᵢ/∂vᵢ -/
def vDiv (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (v : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1)

/-- Cross product in ℝ³: a × b -/
def cross (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

/-- Velocity-space integration by parts on ℝ³.
    ∫ (∇ᵥ · F)(v) · g(v) dv = -∫ F(v) · (∇ᵥg)(v) dv.

    Uses Mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`
    (n-dimensional IBP for Fréchet derivatives) applied per component.

    The three per-component integrability hypotheses (derivative·g, f·derivative,
    and f·g) are the natural conditions for Bochner-integral IBP. -/
lemma velocity_ibp
    (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (g : (Fin 3 → ℝ) → ℝ)
    (hF_diff : ∀ i, Differentiable ℝ (fun v => F v i))
    (hg_diff : Differentiable ℝ g)
    (h_int_df_g : ∀ i, Integrable (fun v => fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v))
    (h_int_f_dg : ∀ i, Integrable (fun v => F v i * fderiv ℝ g v (Pi.single i 1)))
    (h_int_fg : ∀ i, Integrable (fun v => F v i * g v)) :
    ∫ v, vDiv F v * g v = -(∫ v, dotProduct (F v) (vGrad g v)) := by
  -- Strategy: expand into per-component integrals, apply Mathlib IBP per component.
  -- Step 1: Per-component IBP from Mathlib
  -- Per-component IBP from Mathlib: ∫ Fᵢ * ∂g/∂vᵢ = -∫ ∂Fᵢ/∂vᵢ * g
  have hi : ∀ i : Fin 3,
      ∫ v, F v i * fderiv ℝ g v (Pi.single i 1) =
      -(∫ v, fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v) :=
    fun i => integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (h_int_df_g i) (h_int_f_dg i) (h_int_fg i)
      (fun x _ => (hF_diff i) x) (fun x _ => hg_diff x)
  -- Both sides equal Finset.sum over per-component integrals
  have lhs_eq : (fun v => vDiv F v * g v) = fun v =>
      ∑ i : Fin 3, fderiv ℝ (fun w => F w i) v (Pi.single i 1) * g v :=
    funext fun v => by simp only [vDiv, Fin.sum_univ_three]; ring
  have rhs_eq : (fun v => dotProduct (F v) (vGrad g v)) = fun v =>
      ∑ i : Fin 3, F v i * fderiv ℝ g v (Pi.single i 1) :=
    funext fun v => by simp only [dotProduct, vGrad, Fin.sum_univ_three]
  rw [lhs_eq, rhs_eq,
      integral_finsetSum _ (fun i _ => h_int_df_g i),
      integral_finsetSum _ (fun i _ => h_int_f_dg i)]
  simp only [Fin.sum_univ_three, hi]; ring

-- ============================================================================
-- Section 4: Landau Collision Operator
-- ============================================================================

/-- The Landau collision operator Q(f,f)(v).
    Reference: Definition 3 (def:landau_operator)

    Q(f,f)(v) = ∇ᵥ · ∫_{ℝ³} A(v-w) [f(w)∇ᵥf(v) - f(v)∇_wf(w)] dw -/
def LandauOperator (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v : Fin 3 → ℝ) : ℝ :=
  vDiv (fun v' =>
    ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) v

/-- The entropy dissipation functional: D(f) = ∫ Q(f,f)(v) log f(v) dv.
    Reference: Definition in Lemma 5 (lem:entropy_dissipation) -/
def entropyDissipation (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∫ v, LandauOperator Ψ f v * Real.log (f v)

/-- IBP for the Landau collision operator: ∫ Q(g,g)(v) · log g(v) dv equals
    the symmetrized weak form. Combines velocity-space IBP (∫ div F · g = -∫ F · ∇g)
    with dotProduct_integral_comm (pulling the w-integral through the dot product).

    The integrability hypotheses on the Landau flux are the natural conditions for
    Bochner-integral IBP. They require the flux F(v) = ∫_w A(v-w)[...] dw and
    its derivatives to be integrable against log g — this holds for distributions
    with sufficient velocity-space decay (e.g., sub-Gaussian tails). -/
lemma landau_ibp (Ψ : ℝ → ℝ) (g : (Fin 3 → ℝ) → ℝ)
    (hg_pos : ∀ v, 0 < g v) (hg_smooth : ContDiff ℝ 3 g) (_hg_int : Integrable g)
    -- Differentiability of Landau flux components (requires differentiation under ∫)
    (hFlux_diff : ∀ i, Differentiable ℝ (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i))
    -- Per-component integrability for IBP
    (h_int_df_g : ∀ i, Integrable (fun v =>
      fderiv ℝ (fun v' => (∫ w, mulVec (landauMatrix Ψ (v' - w))
        (g w • vGrad g v' - g v' • vGrad g w)) i) v (Pi.single i 1) *
      (Real.log ∘ g) v))
    (h_int_f_dg : ∀ i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i *
      fderiv ℝ (Real.log ∘ g) v (Pi.single i 1)))
    (h_int_fg : ∀ i, Integrable (fun v =>
      (∫ w, mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w)) i * (Real.log ∘ g) v))
    -- Integrability of the Landau flux (for pulling dot product through ∫)
    (hFlux_int : ∀ v, Integrable (fun w =>
      mulVec (landauMatrix Ψ (v - w))
        (g w • vGrad g v - g v • vGrad g w))) :
    ∫ v, LandauOperator Ψ g v * (Real.log ∘ g) v =
    -(∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ g) v)
        (mulVec (landauMatrix Ψ (v - w))
          (g w • vGrad g v - g v • vGrad g w))) := by
  -- Step 1: Unfold LandauOperator = vDiv(Flux)
  unfold LandauOperator
  -- Step 2: Apply velocity IBP: ∫ vDiv(Flux) · log g = -∫ Flux · ∇(log g)
  have h_ibp := velocity_ibp
    (fun v => ∫ w, mulVec (landauMatrix Ψ (v - w))
      (g w • vGrad g v - g v • vGrad g w))
    (Real.log ∘ g)
    hFlux_diff
    (hg_smooth.differentiable (by norm_num) |>.log (fun v => ne_of_gt (hg_pos v)))
    h_int_df_g h_int_f_dg h_int_fg
  rw [h_ibp]
  -- Step 3: Pull w-integral through dot product: ⟨c, ∫ F dw⟩ = ∫ ⟨c, F⟩ dw
  congr 2
  funext v
  rw [dotProduct_comm]
  -- ⟨∇log g(v), ∫ w, A·flux dw⟩ = ∫ w, ⟨∇log g(v), A·flux(w)⟩ via CLM
  set c := vGrad (Real.log ∘ g) v
  set F := fun w => mulVec (landauMatrix Ψ (v - w))
      (g w • vGrad g v - g v • vGrad g w)
  -- Express dotProduct c as a continuous linear map
  let L : (Fin 3 → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin 3, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i) (c i)
  have hL : ∀ x, L x = dotProduct c x := fun x => by simp [L, dotProduct, Fin.sum_univ_three]
                                                     ring
  rw [show dotProduct c (∫ w, F w) = L (∫ w, F w) from (hL _).symm,
    show (∫ w, dotProduct c (F w)) = ∫ w, L (F w) from by
      congr 1; ext w; exact (hL _).symm]
  exact (L.integral_comp_comm (hFlux_int v)).symm

/-- The PSD integrand: g(v,w) = f(v)·f(w)·⟨Δ(v,w), A(v-w) Δ(v,w)⟩
    where Δ(v,w) = ∇log f(v) - ∇log f(w).
    This appears in the entropy dissipation formula (Lemma 5). -/
def PSDIntegrand (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ) (v w : Fin 3 → ℝ) : ℝ :=
  f v * f w *
    dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
      (mulVec (landauMatrix Ψ (v - w))
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w))

-- ============================================================================
-- Small helper lemmas about definitions
-- ============================================================================

/-- Cross product antisymmetry: -cross a b = cross b a. -/
lemma neg_cross (a b : Fin 3 → ℝ) : -cross a b = cross b a := by
  ext i; fin_cases i <;> simp [cross, Pi.neg_apply] <;> ring

lemma cross_smul_left (c : ℝ) (a b : Fin 3 → ℝ) :
    cross (c • a) b = c • cross a b := by
  ext i; fin_cases i <;> simp [cross, Pi.smul_apply, smul_eq_mul, mul_sub] <;> ring


/-- Helper: cross product with zero first argument -/
lemma cross_zero_left (b : Fin 3 → ℝ) : cross (0 : Fin 3 → ℝ) b = 0 := by
  ext i; fin_cases i <;> simp [cross]

/-- Helper: (vecMulVec z z) *ᵥ w = (z · w) • z -/
lemma vecMulVec_self_mulVec (z w : Fin 3 → ℝ) :
    mulVec (vecMulVec z z) w = dotProduct z w • z := by
  ext i
  simp only [mulVec, vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, mul_comm]

-- ============================================================================
-- FlatTorus3: Abstract characterization of a flat compact 3-torus
-- ============================================================================

/-- Abstract characterization of a flat 3-torus with differential operators.

    The spatial domain X is a compact nonempty space equipped with a MeasureSpace
    instance (providing a canonical measure for integration via Mathlib's `∫`) and
    abstract differential operators (grad, div, curl).

    These axioms are satisfied by any flat compact Riemannian 3-manifold without
    boundary (e.g. T³ = ℝ³/ℤ³) equipped with its standard differential operators
    and Riemannian volume form. See `TorusInstance.lean` for a concrete instance
    on `Fin 3 → AddCircle 1`.

    **Axiom design note:**
    The linear operator axioms (hGradAdd, hGradScalarMul, hDivLinear) are stated
    universally (for all functions X → ℝ) because linearity of `fderiv` genuinely
    holds for all functions: `fderiv(c * f) = c * fderiv(f)` is true even for
    non-differentiable f (both sides are 0 by definition).

    The chain rule axiom (hGradChainExp) requires IsSpatiallySmooth ⊤ φ: without it,
    on the concrete torus both sides collapse to 0 via fderiv's junk value, making
    the axiom vacuously true rather than expressing a genuine chain rule.

    hSpatialVelocityFubini requires joint integrability of uncurried F; the concrete
    instance (TorusInstance) provides it via Mathlib's `integral_integral_swap`.
    hSpatialAdd requires integrability of both summands (honest: Mathlib's `integral_add`).
    hGradIntegrable provides integrability of gradient components for spatially differentiable
    functions (on torus: C¹ → continuous → integrable on compact).

    Integration uses Mathlib's `∫ x, f x` (Bochner integral over `volume`).

    Property fields (23):
    - Operator properties (5): hDivLinear, hGradConst, hGradAdd, hGradScalarMul, hGradChainExp
    - Closed manifold integration (2): hCurlIntZero, hIBP_spatial
    - Analysis on compact manifold (4): hHarmonic_const, hLaplacianMaxNonpos,
      hSpatialPos, hSpatialNonnegZero
    - Flat geometry (2): hKillingToHarmonic, hCurlZeroDivZeroHarmonic
    - Abstract measure (3): hSpatialVelocityFubini, hSpatialAdd, hGradIntegrable
    - Differentiability predicate + closure (7): IsSpatiallySmooth ⊤, hDiff_const ⊤, hDiff_add ⊤,
      hDiff_smul ⊤, hDiff_log ⊤, hDiff_continuous ⊤, hDiff_grad ⊤

    Derived lemmas (in `FlatTorus3Lemmas.lean`):
    - hGradChainLog, hGradIntZero, hLaplacianMinNonneg, hSpatialMul, etc. -/
class FlatTorus3 (X : Type*) extends MeasureSpace X, TopologicalSpace X where
  instCompact : CompactSpace X
  instNonempty : Nonempty X
  instFirstCountable : FirstCountableTopology X
  /-- The spatial gradient operator on the torus. -/
  gradX : (X → ℝ) → X → (Fin 3 → ℝ)
  /-- The spatial divergence operator on the torus. -/
  divX : (X → (Fin 3 → ℝ)) → X → ℝ
  /-- The spatial curl operator on the torus. -/
  curlX : (X → (Fin 3 → ℝ)) → X → (Fin 3 → ℝ)
  -- Linearity of the divergence operator
  hDivLinear : ∀ (α : ℝ) (G : X → (Fin 3 → ℝ)),
    ∀ x, divX (fun y => α • G y) x = α * divX G x
  -- Gradient of a spatially constant function vanishes
  hGradConst : ∀ (φ : X → ℝ), (∀ x y, φ x = φ y) → ∀ x, gradX φ x = 0
  -- Strictly positive continuous function has strictly positive integral
  hSpatialPos : ∀ g : X → ℝ, Continuous g → (∀ x, 0 < g x) → 0 < ∫ x, g x
  -- Nonneg continuous function with zero integral is identically zero
  hSpatialNonnegZero : ∀ g : X → ℝ, Continuous g →
    (∀ x, 0 ≤ g x) → ∫ x, g x = 0 → ∀ x, g x = 0
  -- Spatial differentiability predicate (abstract; on the concrete torus,
  -- this is ContDiff ℝ n (periodicLift f), i.e. the periodic lift is Cⁿ)
  /-- Spatial `Cⁿ`-smoothness predicate (on the concrete torus, `ContDiff ℝ n (periodicLift f)`). -/
  IsSpatiallySmooth : ℕ∞ → (X → ℝ) → Prop
  hDiff_of_le : ∀ {n m} f, m ≤ n → IsSpatiallySmooth n f → IsSpatiallySmooth m f
  hDiff_const : ∀ n c, IsSpatiallySmooth n (fun _ : X => c)
  hDiff_add : ∀ n f g, IsSpatiallySmooth n f → IsSpatiallySmooth n g →
    IsSpatiallySmooth n (fun x => f x + g x)
  hDiff_smul : ∀ n c f, IsSpatiallySmooth n f → IsSpatiallySmooth n (fun x => c * f x)
  -- Closure under log (for positive functions)
  hDiff_log : ∀ n f, IsSpatiallySmooth n f → (∀ x, 0 < f x) → IsSpatiallySmooth n (Real.log ∘ f)
  -- Spatially differentiable functions are continuous.
  hDiff_continuous : ∀ n f, IsSpatiallySmooth (n + 1) f → Continuous f
  -- Gradient closure: if f is Cⁿ⁺¹, its gradient is Cⁿ.
  hDiff_grad : ∀ (n : ℕ∞) (f : X → ℝ) (i : Fin 3), IsSpatiallySmooth (n + 1) f →
    IsSpatiallySmooth n (fun x => gradX f x i)
  -- Curl integral vanishes (Stokes theorem for 2-forms)
  hCurlIntZero : ∀ (F : X → Fin 3 → ℝ) (u : Fin 3 → ℝ),
    (∀ j, IsSpatiallySmooth 1 (fun x => F x j)) →
    ∫ x, dotProduct u (curlX F x) = 0
  -- Harmonic functions on compact manifold are constant (Hodge theory)
  hHarmonic_const : ∀ φ : X → ℝ, IsSpatiallySmooth 2 φ →
    (∀ x, divX (gradX φ) x = 0) → ∀ x y, φ x = φ y
  -- Second derivative test: Laplacian ≤ 0 at a maximum
  hLaplacianMaxNonpos : ∀ (φ : X → ℝ) (x₀ : X), IsSpatiallySmooth 2 φ →
    (∀ x, φ x ≤ φ x₀) → divX (gradX φ) x₀ ≤ 0
  -- Linearity of gradient: gradX(f + g) = gradX(f) + gradX(g) for differentiable f, g
  hGradAdd : ∀ (f g : X → ℝ), IsSpatiallySmooth 1 f → IsSpatiallySmooth 1 g →
    ∀ x, gradX (fun y => f y + g y) x = gradX f x + gradX g x
  -- Scalar multiplication: gradX(c · f) = c · gradX(f) for constant c
  hGradScalarMul : ∀ (c : ℝ) (f : X → ℝ),
    ∀ x, gradX (fun y => c * f y) x = c • gradX f x
  -- Chain rule for exp: gradX(exp ∘ φ) = exp(φ) · gradX(φ)
  hGradChainExp : ∀ (φ : X → ℝ), IsSpatiallySmooth 1 φ →
    ∀ x i, gradX (fun y => Real.exp (φ y)) x i = Real.exp (φ x) * gradX φ x i
  -- Killing fields have harmonic components (flatness of the metric).
  hKillingToHarmonic : ∀ (b : X → Fin 3 → ℝ),
    (∀ j, IsSpatiallySmooth 1 (fun y => b y j)) →
    (∀ j i, IsSpatiallySmooth 1 (fun x => gradX (fun y => b y j) x i)) →
    (∀ x i j, gradX (fun y => b y j) x i + gradX (fun y => b y i) x j = 0) →
    ∀ j : Fin 3, ∀ x, divX (gradX (fun y => b y j)) x = 0
  -- Irrotational + solenoidal vector field has harmonic components.
  hCurlZeroDivZeroHarmonic : ∀ F : X → (Fin 3 → ℝ),
    (∀ i, IsSpatiallySmooth 1 (fun y => F y i)) →
    (∀ i j, IsSpatiallySmooth 1 (fun x => gradX (fun y => F y i) x j)) →
    (∀ x, curlX F x = 0) → (∀ x, divX F x = 0) →
    ∀ i, ∀ x, divX (gradX (fun y => F y i)) x = 0
  -- Integration by parts on the torus: ∫ φ · (∇ψ)ᵢ = -∫ ψ · (∇φ)ᵢ
  hIBP_spatial : ∀ (φ ψ : X → ℝ) (i : Fin 3),
    IsSpatiallySmooth 1 φ → IsSpatiallySmooth 1 ψ →
    (∫ x, φ x * gradX ψ x i) = -(∫ x, ψ x * gradX φ x i)
  -- Fubini: swap spatial integral (over compact X) with velocity integral (over ℝ³)
  hSpatialVelocityFubini : ∀ (F : X → (Fin 3 → ℝ) → ℝ),
    MeasureTheory.Integrable (Function.uncurry F)
      (volume.prod (MeasureSpace.volume (α := Fin 3 → ℝ))) →
    (∫ x, ∫ v, F x v) = ∫ v, ∫ x, F x v
  -- Additivity of spatial integral (requires integrability of both summands)
  hSpatialAdd : ∀ (g₁ g₂ : X → ℝ), MeasureTheory.Integrable g₁ → MeasureTheory.Integrable g₂ →
    (∫ x, (g₁ x + g₂ x)) = (∫ x, g₁ x) + ∫ x, g₂ x
  -- Gradient components of spatially differentiable functions are integrable
  hGradIntegrable : ∀ (g : X → ℝ), IsSpatiallySmooth 1 g →
    ∀ i, MeasureTheory.Integrable (fun x => gradX g x i)

namespace FlatTorus3

variable {X : Type*} [FlatTorus3 X]

-- Register CompactSpace and Nonempty as instances so they're automatically
-- available whenever [FlatTorus3 X] is in scope.
instance (priority := 100) instCompactSpace : CompactSpace X := FlatTorus3.instCompact
instance (priority := 100) instNonemptySpace : Nonempty X := FlatTorus3.instNonempty
instance (priority := 100) instFirstCountableTopology : FirstCountableTopology X :=
  FlatTorus3.instFirstCountable

/-- Compatibility wrapper: spatial integral as Mathlib's Bochner integral.
    Defined as `abbrev` so it unfolds transparently in rewrites. -/
noncomputable abbrev spatialIntegral (g : X → ℝ) : ℝ := ∫ x, g x

end FlatTorus3

end VML
