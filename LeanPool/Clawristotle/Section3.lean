/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/
import LeanPool.Clawristotle.Section3Helpers
import LeanPool.Clawristotle.Section3Helpers2

/-!
# Nullspace of the Landau Operator (Section 3)

H-theorem for the Landau operator (D(f) <= 0), characterization of D(f) = 0
as f being a Maxwellian, and Corollary 1: if entropy dissipation vanishes then
f is a local Maxwellian at each spatial point.
-/

open Matrix Finset BigOperators Real MeasureTheory

noncomputable section

namespace VML

-- ============================================================================
-- Section 5: H-Theorem and Nullspace of the Landau Operator
-- Reference: Section 3 of the tex (Lemmas 4-9, Theorems 3-5, Corollary 1)
-- ============================================================================

/-- Theorem 3 (H-theorem for the Landau operator).
    Reference: thm:H_theorem

    D(f) = ∫ Q(f,f)(v) log f(v) dv ≤ 0.

    Proof: By Lemma 5, D(f) is the negative of a double integral of
    the quadratic form Yᵀ A(z) Y weighted by f(v)f(w) > 0.
    By Lemma 2 (PSD), the integrand is non-negative, so D(f) ≤ 0. -/
theorem H_theorem (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 ≤ Ψ r) (hf_pos : ∀ v, 0 < f v)
    (hf_smooth : ContDiff ℝ 3 f)
    (hSWF : ∫ v, LandauOperator Ψ f v * (Real.log ∘ f) v =
      -(1 / 2) * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))) :
    entropyDissipation Ψ f ≤ 0 := by
  rw [entropy_score_form Ψ f hf_pos hf_smooth hSWF]
  unfold PSDIntegrand
  linarith [psd_weighted_integral_nonneg Ψ f hΨ hf_pos]

/-- Lemma 8 (Integration: log f is a polynomial of degree ≤ 2).
    Reference: lem:log_f_quadratic

    If ∇log f(v) = b + 2c₀ v, then log f(v) = a₀ + b · v + c₀|v|².

    Proof: Direct integration of each component ∂ᵢ log f = bᵢ + 2c₀ vᵢ. -/
theorem log_f_quadratic (f : (Fin 3 → ℝ) → ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ)
    (hf_pos : ∀ v, 0 < f v) (hf_smooth : ContDiff ℝ 3 f)
    (hgrad : ∀ v, vGrad (Real.log ∘ f) v = b + (2 * c₀) • v) :
    ∃ a₀ : ℝ, ∀ v, Real.log (f v) = a₀ + dotProduct b v + c₀ * normSq v :=
  ⟨(Real.log ∘ f) 0, affine_gradient_antiderivative (Real.log ∘ f) b c₀
    -- Smoothness of log ∘ f follows from f smooth and f > 0 (standard)
    (hf_smooth.log (fun v => ne_of_gt (hf_pos v))) hgrad⟩

/-- Theorem 4 (Nullspace of the Landau operator — necessity).
    Reference: thm:nullspace_necessity

    If Q(f,f) = 0 and f ∈ L¹(ℝ³), then f is a Maxwellian.

    Proof chains: Q=0 → D=0 (Lemma 5) → parallelism (Lemma 6) →
    ∇log f affine (Lemma 7) → log f quadratic (Lemma 8) → f Maxwellian. -/
theorem nullspace_necessity (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (hΨ : ∀ r, 0 < Ψ r) (hf_pos : ∀ v, 0 < f v)
    (_hf_smooth : ContDiff ℝ 3 f) (hf_int : Integrable f)
    (hQ : ∀ v, LandauOperator Ψ f v = 0)
    (hScoreForm : entropyDissipation Ψ f =
      -(1 / 2) * ∫ v, ∫ w, PSDIntegrand Ψ f v w)
    (hPSD_cont : Continuous (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      PSDIntegrand Ψ f p.1 p.2))
    (hPSD_inner : ∀ v, Integrable (PSDIntegrand Ψ f v))
    (hPSD_outer : Integrable (fun v => ∫ w, PSDIntegrand Ψ f v w)) :
    IsMaxwellian f := by
  -- Q=0 → D=0 (D = ∫ Q · log f = ∫ 0 = 0)
  have hD : entropyDissipation Ψ f = 0 := by
    simp [entropyDissipation, show (fun v => LandauOperator Ψ f v * Real.log (f v)) =
      (fun _ => 0) from funext (fun v => by rw [hQ, zero_mul])]
  exact D_zero_implies_maxwellian Ψ f hΨ hf_pos _hf_smooth hf_int hD
    hScoreForm hPSD_cont hPSD_inner hPSD_outer

/-- Theorem 5 (Nullspace of the Landau operator — sufficiency).
    Reference: thm:nullspace_sufficiency

    If log f(v) = a₀ + b · v + c₀|v|², then Q(f,f) = 0.

    Proof: ∇log f(v) - ∇log f(w) = 2c₀(v - w), so the integrand in Q
    contains A(v-w)(v-w) = 0 by Lemma 3 (projection annihilation). -/
theorem nullspace_sufficiency (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (a₀ : ℝ) (b : Fin 3 → ℝ) (c₀ : ℝ) (_hc₀ : c₀ < 0)
    (hf : ∀ v, f v = Real.exp (a₀ + dotProduct b v + c₀ * normSq v)) :
    ∀ v, LandauOperator Ψ f v = 0 := by
  intro v
  unfold LandauOperator
  -- The Landau flux vanishes for a Maxwellian (Gap 8)
  have hFluxZero := maxwellian_landau_flux_zero Ψ f a₀ b c₀ hf
  -- The flux function is identically zero, so its divergence is zero
  rw [show (fun v' => ∫ w, mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 from
    funext fun v' => by simp [show (fun w => mulVec (landauMatrix Ψ (v' - w))
      (f w • vGrad f v' - f v' • vGrad f w)) = fun _ => 0 from
        funext fun w => hFluxZero v' w]]
  unfold vDiv
  simp

/-- Density is positive when f > 0 and integrable.
    Proof: ∫ f > 0 for continuous positive integrable f on ℝ³ (positive measure).
    Reference: Used in VMLInput construction. -/
lemma density_positive_of_integral
    (f : (Fin 3 → ℝ) → ℝ) (hf_pos : ∀ v, 0 < f v) (hf_int : Integrable f) :
    0 < ∫ v, f v := by
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun v => le_of_lt (hf_pos v)) hf_int,
    show Function.support f = Set.univ from Set.eq_univ_of_forall (fun v => ne_of_gt (hf_pos v)),
    MeasureTheory.Measure.measure_univ_pos]
  exact NeZero.ne volume

-- ============================================================================
-- Fubini symmetrization for the Landau weak form (proved by Aristotle)
-- Reference: Used in Theorem 42 to derive the symmetrized weak form.
-- Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
-- ============================================================================

/-- landauMatrix is symmetric under swapping arguments of subtraction. -/
lemma landauMatrix_sub_comm (Ψ : ℝ → ℝ) (v w : Fin 3 → ℝ) :
    landauMatrix Ψ (w - v) = landauMatrix Ψ (v - w) := by
  rw [show w - v = -(v - w) from by abel, landauMatrix_even]

/-- Fubini symmetrization for the Landau weak form specialized to φ = log ∘ f.
    ∫∫ ⟨∇log f(v) - ∇log f(w), A(v-w) · flux⟩ = 2 · ∫∫ ⟨∇log f(v), A(v-w) · flux⟩
    Proved by Aristotle (project 85302568). -/
theorem fubini_symmetrization_logf (Ψ : ℝ → ℝ) (f : (Fin 3 → ℝ) → ℝ)
    (_hf_smooth : ContDiff ℝ 3 f)
    (h_int_double : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
      dotProduct (vGrad (Real.log ∘ f) p.1)
        (mulVec (landauMatrix Ψ (p.1 - p.2))
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))))
    (_ : ∀ v, Integrable (fun w =>
      dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w))))
    (_ : Integrable (fun v => ∫ w,
      dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)))) :
    ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) =
      2 * ∫ v, ∫ w, dotProduct (vGrad (Real.log ∘ f) v)
        (mulVec (landauMatrix Ψ (v - w))
          (f w • vGrad f v - f v • vGrad f w)) := by
  have h_integrable_swap :
      Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
        vGrad (Real.log ∘ f) p.2 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ
          (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) MeasureSpace.volume := by
    have h_integrable :
        Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ
            (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2)) MeasureSpace.volume ∧
        Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          f p.2 • (vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ vGrad f p.1) -
          f p.1 • (vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ
            vGrad f p.2)) MeasureSpace.volume := by
      convert h_int_double using 1
      simp [mul_sub, sub_mul, mul_assoc, mul_comm,
        Finset.mul_sum _ _ _, Matrix.mulVec, dotProduct]
    have h_mp : MeasurePreserving
        (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (p.2, p.1))
        MeasureSpace.volume MeasureSpace.volume :=
      ⟨measurable_swap, Measure.prod_swap ..⟩
    have h_swap_int :
        Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          vGrad (Real.log ∘ f) p.2 ⬝ᵥ landauMatrix Ψ (p.2 - p.1) *ᵥ
            (f p.1 • vGrad f p.2 - f p.2 • vGrad f p.1)) MeasureSpace.volume := by
      have : Integrable (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) =>
          vGrad (Real.log ∘ f) p.1 ⬝ᵥ landauMatrix Ψ (p.1 - p.2) *ᵥ
            (f p.2 • vGrad f p.1 - f p.1 • vGrad f p.2))
          (Measure.map (fun p : (Fin 3 → ℝ) × (Fin 3 → ℝ) => (p.2, p.1))
            MeasureSpace.volume) := by
        rw [h_mp.map_eq]; exact h_integrable.1
      convert this.comp_measurable measurable_swap using 1
      rfl
    convert h_swap_int.neg using 1
    ext p
    simp only [Pi.neg_apply]
    rw [landauMatrix_sub_comm]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have h_split :
      ∫ v, ∫ w,
        (vGrad (Real.log ∘ f) v - vGrad (Real.log ∘ f) w) ⬝ᵥ
          landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w) =
      (∫ v, ∫ w,
        vGrad (Real.log ∘ f) v ⬝ᵥ
          landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w)) -
      (∫ v, ∫ w,
        vGrad (Real.log ∘ f) w ⬝ᵥ
          landauMatrix Ψ (v - w) *ᵥ (f w • vGrad f v - f v • vGrad f w)) := by
    convert MeasureTheory.integral_sub h_int_double h_integrable_swap using 1
    · erw [MeasureTheory.integral_prod]
      · simp []
      · exact Integrable.sub h_int_double h_integrable_swap
    · erw [MeasureTheory.integral_prod, MeasureTheory.integral_prod]
      · exact h_integrable_swap
      · exact h_int_double
  -- After the split: I₁ - I₂ = 2 * I₁, i.e., I₂ = -I₁
  rw [h_split]
  -- Show that the second integral equals minus the first (by Fubini + symmetry)
  suffices hsuff : (∫ v, ∫ w, vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w)) =
    -(∫ v, ∫ w, vGrad (Real.log ∘ f) v ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w)) by linarith
  -- Step 1: Swap integration order via Fubini
  rw [MeasureTheory.integral_integral_swap h_integrable_swap]
  -- Step 2: The integrand with swapped v↔w = negative of original
  -- (by A(-z)=A(z) + flux antisymmetry)
  have h_symm : ∀ w v : Fin 3 → ℝ, vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (v - w) *ᵥ
      (f w • vGrad f v - f v • vGrad f w) = -(vGrad (Real.log ∘ f) w ⬝ᵥ landauMatrix Ψ (w - v) *ᵥ
      (f v • vGrad f w - f w • vGrad f v)) := by
    intro w v
    rw [landauMatrix_sub_comm]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  simp_rw [h_symm, MeasureTheory.integral_neg]

end VML
