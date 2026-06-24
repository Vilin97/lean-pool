/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # Definitions.lean
  Core definitions for the Fock-space phase retrieval problem.
  Scaffolding notes: Definitions/basic_definitions.md

  Public API:
  - `rho`
  - `polyEval`
  - `polyEvalCircle`
  - `fockNormSq`
  - `rhoFockNormSq`
  - `circleNormSq`
  - `polar_coord_fock`
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! # Definitions -/


open MeasureTheory Complex Real Finset
open scoped ENNReal NNReal

noncomputable section

namespace FockSPR

/-! ## Convention: align with Mathlib

We adopt Mathlib's conventions throughout:
- **Circle**: `AddCircle (2*π)` with normalized Haar measure (probability measure).
  Fourier monomials `fourier n` are orthonormal w.r.t. this measure.
- **Polar coordinates**: Mathlib's `polarCoord` with angular range `(-π, π)`.
- **Complex plane**: `ℂ ≃ ℝ²`. Lebesgue measure on `ℂ` is `volume`. -/

/-- The two-pi period, as a convenient abbreviation. -/
def T : ℝ := 2 * Real.pi

lemma T_pos : 0 < T := mul_pos two_pos Real.pi_pos

instance : Fact (0 < T) := ⟨T_pos⟩

/-! ## Def 1.1: The function `rho` -/

/-- `rho(w) = | ‖1 + w‖ - 1 |` where `‖·‖` is the complex modulus. -/
def rho (w : ℂ) : ℝ := |‖(1 : ℂ) + w‖ - 1|

/-! ## Def 1.2: Polynomial evaluation -/

/-- For `a : Fin D → ℂ` representing coefficients `a₁, …, a_D`, the polynomial
`U(z) = ∑_{n=1}^D aₙ zⁿ` with `U(0) = 0`. -/
def polyEval {D : ℕ} (a : Fin D → ℂ) (z : ℂ) : ℂ :=
  ∑ k : Fin D, a k * z ^ (k.val + 1)

/-! ## Def 1.3: Polynomial evaluation on a circle (via AddCircle) -/

/-- Restriction of the polynomial to `|z| = r`, viewed as a function on `AddCircle T`.
`polyEvalCircle a r t = ∑_k a(k) * r^{k+1} * fourier(k+1)(t)`. -/
def polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) : AddCircle T → ℂ :=
  fun t => ∑ k : Fin D, a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t

/-! ## Def 1.4: Fock norm squared (finite) -/

/-- `‖U‖_F² = ∑_{n=1}^D |aₙ|² n!` — the Fock-space norm squared as a finite sum. -/
def fockNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  ∑ k : Fin D, ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ)

/-! ## Def 1.5: Rho-Fock norm squared (finite) -/

/-- The RHS of the main inequality:
`(1/π) ∫_ℂ ρ(U(z))² exp(−|z|²) dm(z)`. -/
def rhoFockNormSq {D : ℕ} (a : Fin D → ℂ) : ℝ :=
  (1 / Real.pi) * ∫ z : ℂ, (rho (polyEval a z)) ^ 2 * Real.exp (-‖z‖ ^ 2)

/-! ## Def 1.6: Circle L² norm squared -/

/-- `‖f‖²_{L²(S¹)} = ∫ |f(t)|² d(haar)` w.r.t. normalized Haar measure on `AddCircle T`. -/
def circleNormSq (f : AddCircle T → ℂ) : ℝ :=
  ∫ t, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle

/-! ## Helper lemmas -/

/-- `rho(w) ≤ ‖w‖`: the function ρ is bounded by the norm. -/
private lemma rho_le_norm (w : ℂ) : rho w ≤ ‖w‖ := by
  simp only [rho]
  calc |‖(1 : ℂ) + w‖ - 1| = |‖(1 : ℂ) + w‖ - ‖(1 : ℂ)‖| := by simp
    _ ≤ ‖(1 : ℂ) + w - 1‖ := abs_norm_sub_norm_le _ _
    _ = ‖w‖ := by ring_nf

/-- `cos θ + sin θ * I = exp(I * θ)` as complex numbers. -/
private lemma cos_add_sin_mul_I (θ : ℝ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) = Complex.exp (Complex.I * ↑θ) := by
  rw [mul_comm Complex.I, Complex.exp_mul_I]
  simp [Complex.ofReal_cos, Complex.ofReal_sin]

/-- The power `(cos θ + sin θ * I)^n = exp(I * n * θ)`. -/
private lemma cos_add_sin_mul_I_pow (θ : ℝ) (n : ℕ) :
    (↑(Real.cos θ) + ↑(Real.sin θ) * Complex.I : ℂ) ^ n =
    Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [cos_add_sin_mul_I]
  rw [show Complex.I * ↑(n : ℤ) * ↑θ = ↑n * (Complex.I * ↑θ) from by push_cast; ring]
  rw [Complex.exp_nat_mul]

/-- `polarCoord.symm(r,θ)^n = r^n * exp(i n θ)` -/
private lemma polarCoord_symm_pow (r θ : ℝ) (n : ℕ) :
    (Complex.polarCoord.symm (r, θ) : ℂ) ^ n =
    (↑r) ^ n * Complex.exp (Complex.I * ↑(n : ℤ) * ↑θ) := by
  rw [Complex.polarCoord_symm_apply, mul_pow, cos_add_sin_mul_I_pow]

/-- The key link: `fourier n (QuotientAddGroup.mk θ) = exp(I * n * θ)` for `T = 2π`. -/
private lemma fourier_mk_eq_exp (n : ℤ) (θ : ℝ) :
    (fourier n (QuotientAddGroup.mk θ : AddCircle T) : ℂ) =
    Complex.exp (Complex.I * ↑n * ↑θ) := by
  rw [fourier_coe_apply]
  congr 1
  simp only [T]
  push_cast
  field_simp

/-- `polyEval a (Complex.polarCoord.symm (r, θ))` equals `polyEvalCircle a r` applied to the
    image of `θ` in `AddCircle T`. -/
private lemma polyEval_polarCoord_eq {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (θ : ℝ) :
    polyEval a (Complex.polarCoord.symm (r, θ)) =
    polyEvalCircle a r (QuotientAddGroup.mk θ) := by
  simp only [polyEval, polyEvalCircle]
  congr 1
  ext k
  rw [polarCoord_symm_pow, fourier_mk_eq_exp]
  ring

/-- Integral over AddCircle with volume = T • haar. -/
private lemma integral_addCircle_volume_eq_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ t : AddCircle T, f t = T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure]
  simp [ENNReal.toReal_ofReal T_pos.le]

/-- Integral of periodic function over `Ioo(-π, π)` equals integral over `AddCircle T`. -/
private lemma integral_Ioo_eq_addCircle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
    ∫ t : AddCircle T, f t := by
  rw [← integral_Ioc_eq_integral_Ioo]
  have h : -Real.pi + T = Real.pi := by simp [T]; ring
  rw [show Set.Ioc (-Real.pi) Real.pi = Set.Ioc (-Real.pi) (-Real.pi + T) from by rw [h]]
  exact AddCircle.integral_preimage T (-Real.pi) f

/-- Combining the two: ∫ over Ioo = T • ∫ d(haar). -/
private lemma integral_Ioo_eq_T_smul_haar
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : AddCircle T → E) :
    ∫ θ in Set.Ioo (-Real.pi) Real.pi, f (QuotientAddGroup.mk θ) =
    T • ∫ t : AddCircle T, f t ∂AddCircle.haarAddCircle := by
  rw [integral_Ioo_eq_addCircle, integral_addCircle_volume_eq_smul_haar]

/-! ## Helper: Norm bound and integrability for polar-coordinate integrands -/

/-- Bound on ‖polyEvalCircle a r t‖: at most (∑ ‖a_k‖ * |r|^{k+1}). -/
private lemma norm_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
  unfold polyEvalCircle
  calc ‖∑ k : Fin D, a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖
      ≤ ∑ k : Fin D, ‖a k * (r : ℂ) ^ (k.val + 1) * fourier ((k.val + 1 : ℕ) : ℤ) t‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1) := by
        apply Finset.sum_le_sum; intro k _
        rw [norm_mul, norm_mul, norm_pow, Complex.norm_real]
        calc ‖a k‖ * ‖r‖ ^ (k.val + 1) * ‖fourier ((k.val + 1 : ℕ) : ℤ) t‖
            ≤ ‖a k‖ * ‖r‖ ^ (k.val + 1) * ‖(fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ))‖ :=
              mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) (by positivity)
          _ = ‖a k‖ * ‖r‖ ^ (k.val + 1) := by rw [fourier_norm]; ring
          _ = ‖a k‖ * |r| ^ (k.val + 1) := by rw [Real.norm_eq_abs]

/-- ‖polyEvalCircle a r t‖² ≤ D * ∑ ‖a_k‖² * r^{2(k+1)}, a convenient bound.
    Actually, we prove the simpler bound: ≤ (∑ ‖a_k‖ * |r|^{k+1})² . -/
private lemma norm_sq_polyEvalCircle_le {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (t : AddCircle T) :
    ‖polyEvalCircle a r t‖ ^ 2 ≤ (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 :=
  sq_le_sq' (by linarith [norm_nonneg (polyEvalCircle a r t),
    Finset.sum_nonneg (fun k (_ : k ∈ Finset.univ) =>
      mul_nonneg (norm_nonneg (a k)) (pow_nonneg (abs_nonneg r) (k.val + 1)))])
    (norm_polyEvalCircle_le a r t)

/-- The composition `θ ↦ QuotientAddGroup.mk θ` is continuous as a map `ℝ → AddCircle T`. -/
private lemma continuous_mk_addCircle :
    Continuous (fun θ : ℝ => (QuotientAddGroup.mk θ : AddCircle T)) :=
  continuous_quotient_mk'

/-- Continuity of the polyEvalCircle composition with QuotientAddGroup.mk, as a function
    on ℝ × ℝ. -/
private lemma continuous_polyEvalCircle_comp {D : ℕ} (a : Fin D → ℂ) :
    Continuous (fun p : ℝ × ℝ => polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) := by
  unfold polyEvalCircle
  apply continuous_finsetSum
  intro k _
  exact Continuous.mul (Continuous.mul continuous_const
    ((continuous_ofReal.comp continuous_fst).pow _))
    ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
      (continuous_mk_addCircle.comp continuous_snd))

-- to_mathlib: Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
/-- `r^n * exp(-r²)` is integrable on `ℝ` for any `n : ℕ`. -/
private lemma integrable_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => r ^ n * Real.exp (-r ^ 2)) volume := by
  have hs : (-1 : ℝ) < (n : ℝ) := by exact_mod_cast (show -1 < (n : ℤ) by omega)
  have h := integrable_rpow_mul_exp_neg_mul_sq one_pos hs
  refine h.congr ?_
  filter_upwards with r
  rw [rpow_natCast]; ring_nf

/-- `|r|^n * exp(-r²)` is integrable on `ℝ` for any `n : ℕ`. -/
private lemma integrable_abs_pow_mul_exp_neg_sq (n : ℕ) :
    Integrable (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) volume := by
  have : (fun r : ℝ => |r| ^ n * Real.exp (-r ^ 2)) = fun r => ‖r ^ n * Real.exp (-r ^ 2)‖ := by
    ext r; rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  rw [this]; exact (integrable_pow_mul_exp_neg_sq n).norm

/-- IntegrableOn for the polar-coordinate integrand with ‖polyEvalCircle‖². -/
private lemma integrableOn_polar_norm {D : ℕ} (a : Fin D → ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  -- The integrand is continuous, non-negative on Ioi 0, and bounded by a polynomial × Gaussian.
  -- Using integrable_prod_iff: the inner integral over θ is continuous (bounded interval),
  -- and the outer integral over r is bounded by C * r^{2D+1} * exp(-r²), which is integrable.
  have hcont : Continuous (fun p : ℝ × ℝ =>
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2))) :=
    Continuous.mul continuous_fst (Continuous.mul
      ((continuous_norm.comp (continuous_polyEvalCircle_comp a)).pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))
  -- Use integrable_prod_iff on the restricted measure
  rw [IntegrableOn, ← Measure.prod_restrict (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi)]
  rw [integrable_prod_iff hcont.aestronglyMeasurable]
  constructor
  · -- For a.e. r in Ioi 0, θ ↦ integrand(r,θ) is integrable on Ioo(-π,π)
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    apply Filter.Eventually.of_forall
    intro r _
    -- Continuous function on bounded interval → integrable
    -- The inner function θ ↦ r * ‖polyEvalCircle a r (mk θ)‖² * exp(-r²) is continuous in θ
    have hcont_theta : Continuous (fun θ : ℝ =>
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) := by
      apply Continuous.mul continuous_const
      apply Continuous.mul
      · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
          Continuous.mul (Continuous.mul continuous_const continuous_const)
            ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
              continuous_mk_addCircle)))).pow 2
      · exact continuous_const
    exact (hcont_theta.continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Set.Ioo_subset_Icc_self
  · -- r ↦ ∫_θ ‖f(r,θ)‖ dθ is integrable on Ioi 0.
    -- Use Integrable.mono' with bound 4*T*C² * (|r|^3 + |r|^{2D+1}) * exp(-r²).
    set C := ∑ k : Fin D, ‖a k‖
    set bound := fun r : ℝ => T * (4 * C ^ 2) *
      (|r| ^ 3 * Real.exp (-r ^ 2) + |r| ^ (2 * D + 1) * Real.exp (-r ^ 2))
    apply Integrable.mono'
      (g := bound)
    · -- bound is integrable on vol.restrict (Ioi 0)
      exact (((integrable_abs_pow_mul_exp_neg_sq 3).add
        (integrable_abs_pow_mul_exp_neg_sq (2 * D + 1))).const_mul _).restrict
    · -- AEStronglyMeasurable: the parametric integral r ↦ ∫ ‖f(r,·)‖ is continuous.
      -- Use continuous_parametric_integral_of_continuous with uncurried version.
      -- f(r, θ) = ‖r * (‖polyEvalCircle a r (mk θ)‖² * exp(-r²))‖ is continuous.
      -- The uncurried version Function.uncurry g = fun (r,θ) => f(r,θ) is hcont.norm.
      -- So r ↦ ∫ θ in Icc(-π,π), f(r,θ) dθ is continuous.
      -- Since Ioo ⊂ Icc has the same measure (no atoms), the Ioo integral is also continuous.
      have hcont_int : Continuous (fun r : ℝ => ∫ θ in Set.Icc (-Real.pi) Real.pi,
          ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
            Real.exp (-r ^ 2))‖) :=
        continuous_parametric_integral_of_continuous hcont.norm isCompact_Icc
      -- The Ioo and Icc integrals agree (Ioo and Icc differ by a null set).
      have hIoo_eq_Icc : ∀ r, ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
            Real.exp (-r ^ 2))‖ =
          ∫ θ in Set.Icc (-Real.pi) Real.pi,
          ‖r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 *
            Real.exp (-r ^ 2))‖ := by intro r; exact (integral_Icc_eq_integral_Ioo).symm
      simp_rw [hIoo_eq_Icc]
      exact hcont_int.aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · -- Pointwise norm bound
      apply (ae_restrict_iff' measurableSet_Ioi).mpr
      apply Filter.Eventually.of_forall
      intro r hr
      simp only [Set.mem_Ioi] at hr
      -- Bound ‖∫ ‖f‖ dθ‖ ≤ bound(r) via pointwise estimates and integral bounding.
      -- The inner integral is nonneg, so ‖∫ ‖f‖‖ = ∫ ‖f‖.
      -- Then ‖f(r,θ)‖ ≤ |r| * (∑ ‖a_k‖ * |r|^{k+1})² * exp(-r²) by norm_sq_polyEvalCircle_le.
      -- Integrating over θ ∈ Ioo(-π,π) of measure T gives ≤ T * |r| * (∑..)² * exp(-r²).
      -- By the polynomial bound (∑..)² ≤ 4C² * (|r|² + |r|^{2D}), this ≤ bound(r).
      -- Step 1: ‖∫ ‖f‖‖ = ∫ ‖f‖ since ‖f‖ ≥ 0
      rw [Real.norm_of_nonneg (setIntegral_nonneg measurableSet_Ioo
        (fun _ _ => norm_nonneg _))]
      -- Step 2: Simplify ‖f(r,y)‖ to r * (‖polyEvalCircle‖² * exp(-r²))
      have hnorm_eq : ∀ y : ℝ,
          ‖(r, y).1 * (‖polyEvalCircle a (r, y).1 (↑(r, y).2)‖ ^ 2 *
            rexp (-(r, y).1 ^ 2))‖ =
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) := by
        intro y; simp only []
        rw [Real.norm_of_nonneg (mul_nonneg hr.le (mul_nonneg (sq_nonneg _) (exp_pos _).le))]
      simp_rw [hnorm_eq]
      -- Step 3: Bound pointwise: the integrand ≤ a constant independent of y
      have hr_abs : |r| = r := abs_of_pos hr
      set S := (∑ k : Fin D, ‖a k‖ * |r| ^ (k.val + 1)) ^ 2 with hS_def
      have hbd : ∀ y : ℝ,
          r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2)) ≤
          r * (S * rexp (-r ^ 2)) :=
        fun y => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (norm_sq_polyEvalCircle_le a r _) (exp_pos _).le) hr.le
      -- Step 4: ∫ ≤ T * (r * S * exp(-r²)) via integral bound with constant
      calc ∫ y in Set.Ioo (-Real.pi) Real.pi,
            r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))
          ≤ ∫ _ in Set.Ioo (-Real.pi) Real.pi, r * (S * rexp (-r ^ 2)) := by
            apply setIntegral_mono_on
            · -- integrability of left side
              have hcont_y : Continuous (fun y : ℝ =>
                  r * (‖polyEvalCircle a r (QuotientAddGroup.mk y)‖ ^ 2 * rexp (-r ^ 2))) := by
                apply Continuous.mul continuous_const
                apply Continuous.mul
                · exact (continuous_norm.comp (continuous_finsetSum _ (fun k _ =>
                    Continuous.mul (Continuous.mul continuous_const continuous_const)
                      ((fourier ((k.val + 1 : ℕ) : ℤ) : C(AddCircle T, ℂ)).continuous.comp
                        continuous_mk_addCircle)))).pow 2
                · exact continuous_const
              exact hcont_y.continuousOn.integrableOn_compact isCompact_Icc
                |>.mono_set Set.Ioo_subset_Icc_self
            · exact (continuousOn_const.integrableOn_compact isCompact_Icc).mono_set
                Set.Ioo_subset_Icc_self
            · exact measurableSet_Ioo
            · exact fun y _ => hbd y
        _ = T * (r * (S * rexp (-r ^ 2))) := by
            rw [setIntegral_const]
            simp only [smul_eq_mul]
            rw [Measure.real, Real.volume_Ioo,
              show Real.pi - (-Real.pi) = T by simp [T]; ring,
              ENNReal.toReal_ofReal T_pos.le]
        _ ≤ bound r := by
            simp only [bound, hr_abs]
            -- Goal: T * (r * (S * exp(-r²))) ≤ T * (4*C²) * (r³*exp(-r²) + r^{2D+1}*exp(-r²))
            -- Suffices to show: r * S ≤ 4*C² * (r³ + r^{2D+1})
            -- Factor exp(-r²) and T out
            have hexp := (exp_pos (-r ^ 2)).le
            have hT := T_pos.le
            -- Rewrite to T * (r * S * exp(-r²)) and T * (4*C² * (r³ + r^{2D+1}) * exp(-r²))
            suffices h : r * S ≤ 4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) by
              have hexp_pos := exp_pos (-r ^ 2)
              have h1 : r * (S * rexp (-r ^ 2)) = (r * S) * rexp (-r ^ 2) := by ring
              have h2 : 4 * C ^ 2 * (r ^ 3 * rexp (-r ^ 2) + r ^ (2 * D + 1) * rexp (-r ^ 2)) =
                  4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) * rexp (-r ^ 2) := by ring
              calc T * (r * (S * rexp (-r ^ 2)))
                  = T * ((r * S) * rexp (-r ^ 2)) := by ring
                _ ≤ T * (4 * C ^ 2 * (r ^ 3 + r ^ (2 * D + 1)) * rexp (-r ^ 2)) := by
                    apply mul_le_mul_of_nonneg_left _ hT
                    exact mul_le_mul_of_nonneg_right h hexp_pos.le
                _ = T * (4 * C ^ 2) *
                    (r ^ 3 * rexp (-r ^ 2) +
                      r ^ (2 * D + 1) * rexp (-r ^ 2)) := by ring
            -- S = (∑ k, ‖a k‖ * r^{k+1})² since |r| = r
            rw [hS_def, hr_abs]
            -- Factor r from each term: ∑ ‖a k‖ * r^{k+1} = r * ∑ ‖a k‖ * r^k
            have hsum_factor : ∑ k : Fin D, ‖a k‖ * r ^ (k.val + 1) =
                r * ∑ k : Fin D, ‖a k‖ * r ^ k.val := by
              rw [Finset.mul_sum]; congr 1; ext k
              rw [pow_succ]; ring
            rw [hsum_factor]
            -- (r * X)² = r² * X², so r * (r * X)² = r³ * X²
            ring_nf
            -- Goal: r³ * (∑ x, r^x.val * ‖a x‖)² ≤ 4*C²*r^{2D+1} + 4*C²*r³
            have hC_nn : 0 ≤ C := Finset.sum_nonneg (fun k _ => norm_nonneg (a k))
            by_cases hD : D = 0
            · subst hD; simp; nlinarith [sq_nonneg C, pow_nonneg hr.le 3]
            · -- D ≥ 1
              have hD_pos : 0 < D := Nat.pos_of_ne_zero hD
              -- Each r^k ≤ 1 + r^(D-1) for k ∈ {0,...,D-1}
              have hr_nn := hr.le
              have hpow_le : ∀ k : Fin D, r ^ k.val ≤ 1 + r ^ (D - 1) := by
                intro k
                by_cases hr1 : r ≤ 1
                · have : r ^ k.val ≤ 1 := pow_le_one₀ (n := k.val) hr_nn hr1
                  linarith [pow_nonneg hr_nn (D - 1)]
                · push Not at hr1
                  have : r ^ k.val ≤ r ^ (D - 1) :=
                    pow_le_pow_right₀ hr1.le (by omega : k.val ≤ D - 1)
                  linarith
              -- ∑ r^k * ‖a k‖ ≤ (1 + r^(D-1)) * C
              have hsum_le : ∑ x : Fin D, r ^ x.val * ‖a x‖ ≤
                  (1 + r ^ (D - 1)) * C := by
                calc ∑ x, r ^ x.val * ‖a x‖
                    ≤ ∑ x : Fin D, (1 + r ^ (D - 1)) * ‖a x‖ :=
                      Finset.sum_le_sum (fun k _ =>
                        mul_le_mul_of_nonneg_right (hpow_le k) (norm_nonneg _))
                  _ = _ := by rw [← Finset.mul_sum]
              -- Square both sides
              have hsum_nn : 0 ≤ ∑ x : Fin D, r ^ x.val * ‖a x‖ :=
                Finset.sum_nonneg (fun k _ =>
                  mul_nonneg (pow_nonneg hr_nn k.val) (norm_nonneg _))
              have hfact_nn : 0 ≤ (1 + r ^ (D - 1)) * C :=
                mul_nonneg (by linarith [pow_nonneg hr_nn (D - 1)]) hC_nn
              have hsq : (∑ x : Fin D, r ^ x.val * ‖a x‖) ^ 2 ≤
                  ((1 + r ^ (D - 1)) * C) ^ 2 :=
                sq_le_sq' (by linarith) hsum_le
              -- ((1+a)*b)² = (1+a)²*b²
              -- (1+a)² = 1 + 2a + a² ≤ 2 + 2a² = 2(1+a²)
              -- So ((1+a)*b)² ≤ 2(1+a²)*b²
              -- With a = r^(D-1): (1+r^(D-1))²*C² ≤ 2*(1+(r^(D-1))²)*C² = 2*(1+r^(2*(D-1)))*C²
              have hrd := pow_nonneg hr_nn (D - 1)
              have hsq2 : ((1 + r ^ (D - 1)) * C) ^ 2 ≤
                  2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2 := by nlinarith [sq_nonneg (1 - r ^ (D - 1))]
              -- r^3 * 2 * (1 + (r^(D-1))²) * C² ≤ 4 * (r^3 + r^3*(r^(D-1))²) * C²
              -- r^3 * (r^(D-1))² = r^(2D+1)
              have hpow_eq : r ^ 3 * (r ^ (D - 1)) ^ 2 = r * r ^ (D * 2) := by
                have hexp_eq : 3 + (D - 1) * 2 = 1 + D * 2 := by omega
                rw [← pow_mul, ← pow_add, hexp_eq, pow_add, pow_one]
              calc r ^ 3 * (∑ x, r ^ x.val * ‖a x‖) ^ 2
                  ≤ r ^ 3 * (2 * (1 + (r ^ (D - 1)) ^ 2) * C ^ 2) := by
                    exact mul_le_mul_of_nonneg_left
                      (le_trans hsq hsq2) (pow_nonneg hr_nn 3)
                _ = 2 * C ^ 2 * (r ^ 3 + r ^ 3 * (r ^ (D - 1)) ^ 2) := by ring
                _ = 2 * C ^ 2 * (r ^ 3 + r * r ^ (D * 2)) := by rw [hpow_eq]
                _ ≤ r * r ^ (D * 2) * C ^ 2 * 4 + r ^ 3 * C ^ 2 * 4 := by
                    nlinarith [pow_nonneg hr_nn 3,
                      mul_nonneg hr_nn (pow_nonneg hr_nn (D * 2)),
                      sq_nonneg C]

/-- IntegrableOn for the polar-coordinate integrand with ρ(polyEvalCircle)². -/
private lemma integrableOn_polar_rho {D : ℕ} (a : Fin D → ℂ) :
    IntegrableOn
      (fun p : ℝ × ℝ => p.1 * (rho (polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) ^ 2 *
        Real.exp (-p.1 ^ 2)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
      (volume.prod volume) := by
  -- ρ(w)² ≤ ‖w‖² since ρ(w) ≤ ‖w‖, so this follows from integrableOn_polar_norm.
  -- Use Integrable.mono' on the restricted measure (IntegrableOn = Integrable (restrict)).
  rw [IntegrableOn]
  apply Integrable.mono' (integrableOn_polar_norm a)
  · -- AEStronglyMeasurable on the restricted measure
    exact (Continuous.mul continuous_fst (Continuous.mul
      ((Continuous.abs (Continuous.sub (continuous_norm.comp
        (Continuous.add continuous_const (continuous_polyEvalCircle_comp a)))
        continuous_const)).pow 2)
      (Real.continuous_exp.comp (Continuous.neg (continuous_fst.pow 2))))).aestronglyMeasurable
  · -- Pointwise bound: ‖f(r,θ)‖ ≤ g(r,θ) ae w.r.t. restricted measure
    rw [Filter.Eventually, MeasureTheory.ae_restrict_eq
      (measurableSet_Ioi.prod measurableSet_Ioo)]
    apply Filter.mem_inf_of_right
    apply Filter.mem_principal.mpr
    intro ⟨r, θ⟩ ⟨hr, _⟩
    simp only [Set.mem_Ioi, Set.mem_setOf_eq] at hr ⊢
    simp only [Real.norm_eq_abs, abs_mul]
    rw [abs_of_pos hr]
    apply mul_le_mul_of_nonneg_left _ hr.le
    rw [abs_of_nonneg (sq_nonneg _), abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have hle := rho_le_norm (polyEvalCircle a r (QuotientAddGroup.mk θ))
    have hnn := norm_nonneg (polyEvalCircle a r (QuotientAddGroup.mk θ))
    have hrho_nn : 0 ≤ rho (polyEvalCircle a r (QuotientAddGroup.mk θ)) := abs_nonneg _
    exact sq_le_sq' (by linarith) hle

/-! ## Lemma 1.7: Polar-coordinate decomposition of the Fock norm -/

theorem polar_coord_fock {D : ℕ} (a : Fin D → ℂ) :
    rhoFockNormSq a = 2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, (rho (polyEvalCircle a r t)) ^ 2 ∂AddCircle.haarAddCircle) := by
  simp only [rhoFockNormSq]
  -- Step 1: Use polar coordinates to rewrite ∫_ℂ f(z) as ∫_{target} r * f(pc.symm(r,θ))
  rw [show (∫ z : ℂ, (rho (polyEval a z)) ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • ((rho (polyEval a (Complex.polarCoord.symm p))) ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)))
    from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  -- Step 2: Rewrite the integrand using helper lemmas
  -- For (r, θ) ∈ Ioi 0 ×ˢ Ioo(-π, π):
  --   ‖pc.symm(r,θ)‖ = |r| = r (since r > 0)
  --   polyEval a (pc.symm(r,θ)) = polyEvalCircle a r (mk θ)
  --   p.1 • x = r * x (for real x)
  -- So the integrand is r * (rho(polyEvalCircle a r (mk θ)))^2 * exp(-r²)
  -- Rewrite the integrand pointwise
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • ((rho (polyEval a (Complex.polarCoord.symm p))) ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * ((rho (polyEvalCircle a p.1 (QuotientAddGroup.mk p.2))) ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, polyEval_polarCoord_eq, Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [integrand_rw]
  -- Now the goal is:
  -- 1/π * ∫ p in Ioi 0 ×ˢ Ioo(-π) π, p.1 * (G(mk p.2) * exp(-p.1²))
  --   = 2 * ∫ r in Ioi 0, r * exp(-r²) * ∫ t, G(r,t) d(haar)
  -- Step 3: Apply Fubini to split the product integral
  -- First, establish integrability. The integrand is the image under polar coordinates
  -- of (ρ(U(z)))² * exp(-‖z‖²), which is a finite sum of continuous functions with
  -- Gaussian decay, hence integrable.
  have hint : IntegrableOn
    (fun p : ℝ × ℝ => p.1 * (rho (polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) ^ 2 *
      Real.exp (-p.1 ^ 2)))
    (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
    (volume.prod volume) := integrableOn_polar_rho a
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod (fun p : ℝ × ℝ =>
    p.1 * (rho (polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)) ^ 2 *
      Real.exp (-p.1 ^ 2))) hint]
  -- Simplify the projections from Fubini
  simp only []
  -- Now goal is:
  -- 1/π * ∫ r in Ioi 0, ∫ θ in Ioo(-π) π, r * (G(r, mk θ) * exp(-r²))
  -- = 2 * ∫ r in Ioi 0, r * exp(-r²) * ∫ t, G(r,t) d(haar)
  -- Show the inner θ-integral for each r equals r*exp(-r²)*(T*∫ d haar)
  -- Then (1/π) * ∫ r, r*exp(-r²)*(T*∫ d haar) = (T/π) * ∫ r, ... = 2 * ∫ r, ...
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (rho (polyEvalCircle a r (QuotientAddGroup.mk θ)) ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, rho (polyEvalCircle a r t) ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    -- Rewrite the integrand: r * (G * exp(-r²)) = (r * exp(-r²)) * G
    have h1 : ∀ θ : ℝ,
        r * (rho (polyEvalCircle a r (QuotientAddGroup.mk θ)) ^ 2 * Real.exp (-r ^ 2)) =
        (r * Real.exp (-r ^ 2)) * rho (polyEvalCircle a r (QuotientAddGroup.mk θ)) ^ 2 := by
      intro θ; ring
    simp_rw [h1]
    -- Factor out the constant r * exp(-r²)
    rw [MeasureTheory.integral_const_mul]
    -- Convert the θ-integral to T * Haar integral
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      rho (polyEvalCircle a r t) ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          rho (polyEvalCircle a r (QuotientAddGroup.mk θ)) ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => rho (polyEvalCircle a r t) ^ 2) (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]
    ring
  simp_rw [inner_eq]
  -- Now: 1/π * ∫ r in Ioi 0, T * (r * exp(-r²) * ∫ t, G d(haar))
  -- = 2 * ∫ r in Ioi 0, r * exp(-r²) * ∫ t, G d(haar)
  -- Factor T out of the integral
  rw [MeasureTheory.integral_const_mul]
  -- 1/π * (T * ∫ ...) = 2 * ∫ ...
  -- Since 1/π * T = 2
  have hT_eq : (1 / Real.pi) * T = 2 := by
    simp only [T]
    field_simp
  rw [← mul_assoc, hT_eq]

/-! ## Lemma 1.8: Fock norm equals Gaussian integral -/

/-- The squared norm of `polyEvalCircle a r` under Haar measure equals `∑ ‖a_k‖² r^{2(k+1)}`,
    by orthonormality of the Fourier monomials. -/
private lemma circleNormSq_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) :
    ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle =
    ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
  -- polyEvalCircle a r t = ∑_k (a_k * r^{k+1}) * fourier(k+1)(t)
  -- By orthonormality of Fourier monomials: ∫ ‖∑ c_k e_k‖² = ∑ ‖c_k‖²
  -- Following the pattern from parseval_finite in LocalCircleEstimate.lean.
  -- Step 1: Build the continuous map and its L² representative
  let E' := (Finset.univ : Finset (Fin D)).map
    ⟨fun k => ((k.val + 1 : ℕ) : ℤ), fun k₁ k₂ h => by
      simp only at h; exact Fin.ext (by omega)⟩
  let b : ℤ → ℂ := fun n => ∑ k ∈ (Finset.univ : Finset (Fin D)).filter
    (fun k => ((k.val + 1 : ℕ) : ℤ) = n), a k * (r : ℂ) ^ (k.val + 1)
  -- The filter sum has at most one element, so b n = a_k * r^{k+1} when n = k+1
  have hb_eq : ∀ k : Fin D, b ((k.val + 1 : ℕ) : ℤ) = a k * (r : ℂ) ^ (k.val + 1) := by
    intro k
    simp only [b]
    rw [Finset.sum_filter]
    have : ∀ j : Fin D, (((j.val + 1 : ℕ) : ℤ) = ((k.val + 1 : ℕ) : ℤ)) ↔ j = k := by
      intro j; constructor
      · intro h; ext; omega
      · intro h; rw [h]
    simp_rw [this]
    simp [Finset.sum_ite_eq']
  let c : ℤ → ℂ := fun n =>
    if h : ∃ k : Fin D, ((k.val + 1 : ℕ) : ℤ) = n
    then a h.choose * (r : ℂ) ^ (h.choose.val + 1)
    else 0
  -- Define the continuous map
  let Pcont : C(AddCircle T, ℂ) := ∑ k : Fin D,
    (a k * (r : ℂ) ^ (k.val + 1)) • fourier ((k.val + 1 : ℕ) : ℤ)
  have hPcont_eq : ∀ t : AddCircle T, (Pcont : AddCircle T → ℂ) t =
      polyEvalCircle a r t := by
    intro t
    simp only [Pcont, polyEvalCircle, ContinuousMap.coe_sum, Finset.sum_apply,
      ContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Step 2: Build the Lp version
  let PLp := (ContinuousMap.toLp (α := AddCircle T) 2 AddCircle.haarAddCircle ℂ) Pcont
  have hPLp : PLp = ∑ k : Fin D,
      (a k * (r : ℂ) ^ (k.val + 1)) • fourierLp 2 ((k.val + 1 : ℕ) : ℤ) := by
    simp only [PLp, Pcont, fourierLp, map_sum, map_smul]
  -- Step 3: Rewrite as a sum over E' for orthonormal_fourier.inner_sum
  have hPLp' : PLp = ∑ n ∈ E', b n • fourierLp 2 n := by
    rw [hPLp]
    simp only [E', b]
    rw [Finset.sum_map]
    congr 1; ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [Finset.sum_filter]
    have : ∀ j : Fin D, (((j.val + 1 : ℕ) : ℤ) = ((k.val + 1 : ℕ) : ℤ)) ↔ j = k := by
      intro j; constructor
      · intro h; ext; omega
      · intro h; rw [h]
    simp_rw [this]
    simp [Finset.sum_ite_eq']
  -- Step 4: Compute inner product via orthonormality
  have hinner_orth : @inner ℂ _ _ PLp PLp =
      Complex.ofReal (∑ k : Fin D, ‖a k * (r : ℂ) ^ (k.val + 1)‖ ^ 2) := by
    rw [hPLp', orthonormal_fourier.inner_sum b b E']
    rw [show E' = (Finset.univ : Finset (Fin D)).map
      ⟨fun k => ((k.val + 1 : ℕ) : ℤ), fun k₁ k₂ h => by
        simp only at h; exact Fin.ext (by omega)⟩ from rfl]
    rw [Finset.sum_map, Complex.ofReal_sum]
    congr 1; ext k
    simp only [Function.Embedding.coeFn_mk]
    rw [hb_eq k, mul_comm (starRingEnd ℂ _), mul_conj]
    congr 1; exact (Complex.sq_norm _).symm
  -- Step 5: Simplify ‖a_k * r^{k+1}‖² = ‖a_k‖² * r^{2(k+1)}
  have hnorm_eq : ∀ k : Fin D,
      ‖a k * (r : ℂ) ^ (k.val + 1)‖ ^ 2 = ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
    intro k
    rw [norm_mul, norm_pow, Complex.norm_real, mul_pow]
    congr 1
    rw [← pow_mul, show (k.val + 1) * 2 = 2 * (k.val + 1) from by ring,
        pow_mul, Real.norm_eq_abs, sq_abs]
  simp_rw [hnorm_eq] at hinner_orth
  -- Step 6: Connect inner product to integral via L2.inner_def
  have hinner_L2 := L2.inner_def (𝕜 := ℂ) PLp PLp
  have hcombine := hinner_L2.symm.trans hinner_orth
  -- Step 7: The coercion from ContinuousMap to Lp agrees a.e.
  have hae := ContinuousMap.coeFn_toLp (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (p := 2) Pcont
  -- Step 8: Compute the final result via calc
  calc ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle
      = ∫ t : AddCircle T, ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2 ∂AddCircle.haarAddCircle := by
          symm; apply integral_congr_ae
          filter_upwards [hae] with t ht
          show ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2 = ‖polyEvalCircle a r t‖ ^ 2
          rw [show (↑↑PLp : AddCircle T → ℂ) t = Pcont t from ht, hPcont_eq t]
    _ = (∫ t : AddCircle T, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
            ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle).re := by
          have hint := L2.integrable_inner (𝕜 := ℂ) PLp PLp
          symm
          calc (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle).re
              = Complex.reCLM (∫ t, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle) := rfl
            _ = ∫ t, Complex.reCLM (@inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
                ((↑↑PLp : AddCircle T → ℂ) t)) ∂AddCircle.haarAddCircle :=
                (ContinuousLinearMap.integral_comp_comm _ hint).symm
            _ = ∫ t, ‖(↑↑PLp : AddCircle T → ℂ) t‖ ^ 2 ∂AddCircle.haarAddCircle := by
                congr 1; ext t
                exact @inner_self_eq_norm_sq ℂ ℂ _ _ _ ((↑↑PLp : AddCircle T → ℂ) t)
    _ = ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) := by
          rw [show (∫ t : AddCircle T, @inner ℂ ℂ _ ((↑↑PLp : AddCircle T → ℂ) t)
              ((↑↑PLp : AddCircle T → ℂ) t) ∂AddCircle.haarAddCircle) =
              Complex.ofReal (∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1))
              from hcombine, Complex.ofReal_re]

/-- The radial Gaussian integral: `2 ∫_{r>0} r^{2n+1} exp(-r²) dr = n!`.
    This follows from the substitution `t = r²` giving `∫_0^∞ t^n exp(-t) dt = Γ(n+1) = n!`. -/
private lemma radial_gaussian_integral (n : ℕ) :
    2 * ∫ r in Set.Ioi (0 : ℝ), r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
    (n.factorial : ℝ) := by
  -- Use integral_rpow_mul_exp_neg_rpow with p = 2, q = 2*n + 1
  have hp : (0 : ℝ) < 2 := two_pos
  have hq : (-1 : ℝ) < (2 * (n : ℝ) + 1) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  -- First convert ℕ powers to ℝ powers so we can apply integral_rpow_mul_exp_neg_rpow
  have pow_eq : ∀ (r : ℝ), r ∈ Set.Ioi (0 : ℝ) →
      r ^ (2 * n + 1) * Real.exp (-r ^ 2) =
      r ^ (2 * (n : ℝ) + 1) * Real.exp (-r ^ (2 : ℝ)) := by
    intro r _
    congr 1
    · rw [← rpow_natCast r (2 * n + 1)]
      congr 1
      push_cast
      ring
    · congr 1; congr 1
      rw [← rpow_natCast r 2]
      norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi pow_eq, integral_rpow_mul_exp_neg_rpow hp hq]
  -- Now we have: 2 * (1/2 * Γ((2n+2)/2)) = n!
  -- (2n+2)/2 = n+1, and Γ(n+1) = n!
  have h1 : (2 * (n : ℝ) + 1 + 1) / 2 = ↑n + 1 := by ring
  rw [h1, Real.Gamma_nat_eq_factorial]
  ring

-- Helper: ‖polyEval a z‖ = ‖polyEvalCircle a r (mk θ)‖ when z = polarCoord.symm(r, θ)
private lemma norm_polyEval_eq_norm_polyEvalCircle {D : ℕ} (a : Fin D → ℂ) (r : ℝ) (θ : ℝ) :
    ‖polyEval a (Complex.polarCoord.symm (r, θ))‖ =
    ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ := by rw [polyEval_polarCoord_eq]

-- The polar form of the Gaussian integral for ‖U‖²
private lemma fockNorm_polar {D : ℕ} (a : Fin D → ℂ) :
    (1 / Real.pi) * ∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
    2 * ∫ r in Set.Ioi (0 : ℝ), r * Real.exp (-r ^ 2) *
      (∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
  -- Same structure as polar_coord_fock: polar coordinates + Fubini + Haar conversion
  -- Step 1: polar coordinates
  rw [show (∫ z : ℂ, ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2)) =
    (∫ p in polarCoord.target, p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
      Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)))
    from (Complex.integral_comp_polarCoord_symm _).symm]
  rw [polarCoord_target]
  -- Step 2: Rewrite integrand
  have integrand_rw : ∀ p : ℝ × ℝ,
      p.1 • (‖polyEval a (Complex.polarCoord.symm p)‖ ^ 2 *
        Real.exp (-‖Complex.polarCoord.symm p‖ ^ 2)) =
      p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
        Real.exp (-p.1 ^ 2)) := by
    intro ⟨r, θ⟩
    simp only [smul_eq_mul, norm_polyEval_eq_norm_polyEvalCircle,
      Complex.norm_polarCoord_symm, sq_abs]
  simp_rw [integrand_rw]
  -- Step 3: Fubini
  have hint : IntegrableOn
    (fun p : ℝ × ℝ => p.1 * (‖polyEvalCircle a p.1 (QuotientAddGroup.mk p.2)‖ ^ 2 *
      Real.exp (-p.1 ^ 2)))
    (Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi)
    (volume.prod volume) := integrableOn_polar_norm a
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
  rw [setIntegral_prod _ hint]
  simp only []
  -- Step 4: Inner integral conversion
  have inner_eq : ∀ r : ℝ,
      (∫ θ in Set.Ioo (-Real.pi) Real.pi,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2))) =
      T * (r * Real.exp (-r ^ 2) *
        ∫ t : AddCircle T, ‖polyEvalCircle a r t‖ ^ 2 ∂AddCircle.haarAddCircle) := by
    intro r
    have h1 : ∀ θ : ℝ,
        r * (‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 * Real.exp (-r ^ 2)) =
        (r * Real.exp (-r ^ 2)) * ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2 := by
      intro θ; ring
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    have := integral_Ioo_eq_T_smul_haar (fun t : AddCircle T =>
      ‖polyEvalCircle a r t‖ ^ 2)
    simp only [smul_eq_mul] at this
    rw [show (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          ‖polyEvalCircle a r (QuotientAddGroup.mk θ)‖ ^ 2) =
        (∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (fun t : AddCircle T => ‖polyEvalCircle a r t‖ ^ 2) (QuotientAddGroup.mk θ))
        from by rfl]
    rw [this]; ring
  simp_rw [inner_eq]
  rw [MeasureTheory.integral_const_mul]
  have hT_eq : (1 / Real.pi) * T = 2 := by simp only [T]; field_simp
  rw [← mul_assoc, hT_eq]

theorem fockNorm_eq_gaussian_integral {D : ℕ} (a : Fin D → ℂ) :
    (1 / Real.pi) * ∫ z : ℂ,
      ‖polyEval a z‖ ^ 2 * Real.exp (-‖z‖ ^ 2) =
    fockNormSq a := by
  -- Step 1: Convert to polar coordinates
  rw [fockNorm_polar a]
  -- Step 2: Apply Parseval (circleNormSq_polyEvalCircle) to the angular integral
  simp_rw [circleNormSq_polyEvalCircle a]
  -- Step 3: Exchange sum and integral, and evaluate radial integrals
  simp only [fockNormSq]
  -- Rewrite the integrand: r * exp(-r²) * ∑_k ‖a_k‖² * (r²)^{k.val+1}
  -- = ∑_k ‖a_k‖² * r^{2*(k.val+1)+1} * exp(-r²)
  have integrand_eq : ∀ r : ℝ,
      r * Real.exp (-r ^ 2) * ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ 2) ^ (k.val + 1) =
      ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
    intro r
    rw [Finset.mul_sum]
    congr 1
    ext k
    have : (r ^ 2) ^ (k.val + 1) = r ^ (2 * (k.val + 1)) := by rw [← pow_mul]
    rw [this]
    ring
  simp_rw [integrand_eq]
  -- Exchange sum and integral (finite sum)
  -- The set integral ∫_s = ∫ ∂(volume.restrict s)
  -- We need IntegrableOn for each summand
  -- Integrability of each summand
  have hint_summand : ∀ k : Fin D,
      IntegrableOn (fun r => ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)))
        (Set.Ioi 0) volume := by
    intro k
    -- The integrand is ‖a k‖² * (r^{2(k+1)+1} * exp(-r²))
    -- Use integrable_pow_mul_exp_neg_sq
    exact (integrable_pow_mul_exp_neg_sq (2 * (k.val + 1) + 1)).integrableOn |>.const_mul _
  -- Exchange sum and integral
  have sum_integral_eq :
      ∫ r in Set.Ioi (0 : ℝ),
        ∑ k : Fin D, ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) =
      ∑ k : Fin D, ∫ r in Set.Ioi (0 : ℝ),
        ‖a k‖ ^ 2 * (r ^ (2 * (k.val + 1) + 1) * Real.exp (-r ^ 2)) := by
    rw [integral_finsetSum Finset.univ (fun k _ => (hint_summand k).integrable)]
  rw [sum_integral_eq]
  -- Factor constant ‖a_k‖² out of each integral
  simp_rw [MeasureTheory.integral_const_mul]
  -- Now: 2 * ∑_k ‖a_k‖² * ∫_{r>0} r^{2(k+1)+1} * exp(-r²)
  -- Use radial_gaussian_integral: 2 * ∫ = (k+1)!
  rw [Finset.mul_sum]
  congr 1
  ext k
  rw [← mul_assoc, mul_comm 2, mul_assoc, radial_gaussian_integral (k.val + 1)]

end FockSPR
