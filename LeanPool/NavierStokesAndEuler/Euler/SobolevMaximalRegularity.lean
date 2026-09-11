/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedTopBlocks
public import LeanPool.NavierStokesAndEuler.Euler.TimeLp
import LeanPool.NavierStokesAndEuler.Euler.TimeLpMap
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.RegularizedMildEquation
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlockCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.SobolevLaplacian
public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Order.Lattice
import LeanPool.NavierStokesAndEuler.Euler.Foundations.LiftedWeakDerivative

/-! Genuine all-finite-order maximal regularity for actual viscous cylinder mild solutions. -/

section

/-! Actual maximal regularity at arbitrary finite Sobolev order via finitely many top derivative
equations. -/

section

/-! A genuine L²-time H² estimate for regularized heat solutions, with only L² forcing. -/

section

/-! Genuine gradient energy and maximal-regularity estimates for smooth Sobolev heat solutions. -/

@[expose] public section

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerPressureSpatialRegularity
  EulerCylinderSobolev EulerCylinderSobolevSpace EulerSobolevLaplacian EulerSobolevHeatGenerator
  EulerLiftedWeakDerivative
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual sum of the four first-derivative L² energies. -/
def gradientEnergy (u : SobolevSpace period 1) : ℝ :=
  ∑ i : Fin 4, ‖value period (derivativeOperator period 0 i u)‖ ^ 2

/-- Gradient energy is nonnegative. -/
theorem gradientEnergy_nonneg (u : SobolevSpace period 1) : 0 ≤ gradientEnergy period u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Gradient energy is a continuous function of the actual H¹ field. -/
theorem gradientEnergy_continuous : Continuous (gradientEnergy period) := by
  apply continuous_finsetSum
  intro i _
  exact (((valueOperator period 0).continuous.comp (derivativeOperator period 0
      i).continuous).norm).pow 2

/-- Genuine strong-derivative integration by parts identifies the full gradient pairing with the
Laplacian. -/
theorem gradient_pairing (u : SobolevSpace period 2) (v : SobolevSpace period 1) :
    (∑ i : Fin 4, ⟪value period (derivativeOperator period 1 i u),
      value period (derivativeOperator period 0 i v)⟫_ℝ) =
      -⟪laplacianEvaluation period 2 (by norm_num) u, value period v⟫_ℝ := by
  have hi (i : Fin 4) : ⟪value period (derivativeOperator period 1 i u),
      value period (derivativeOperator period 0 i v)⟫_ℝ =
      -⟪value period (derivativeOperator period 0 i (derivativeOperator period 1 i u)), value
          period v⟫_ℝ := by
    have h := translation_derivative_pairing period (standardDirection i)
      (value period (derivativeOperator period 1 i u))
      (value period (derivativeOperator period 0 i (derivativeOperator period 1 i u)))
      (value period v) (value period (derivativeOperator period 0 i v))
      (derivativeOperator_hasDerivAt period i (derivativeOperator period 1 i u))
      (derivativeOperator_hasDerivAt period i v)
    linarith
  rw [← laplacianOperator_value period u, laplacianOperator_apply]
  change _ = -⟪(valueOperator period 0) (∑ i : Fin 4, _), value period v⟫_ℝ
  rw [map_sum, sum_inner]
  simp only [hi, Finset.sum_neg_distrib]
  rfl

/-- Actual L² time derivatives of the first spatial derivatives determine the gradient-energy
derivative. -/
theorem gradient_energy_hasDerivAt (u : ℝ → SobolevSpace period 2) (v : SobolevSpace period 1) (t :
    ℝ)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 1 i (u s)))
      (value period (derivativeOperator period 0 i v)) t) :
    HasDerivAt (fun s => gradientEnergy period (truncateOperator period 1 (u s)))
      (-2 * ⟪laplacianEvaluation period 2 (by norm_num) (u t), value period v⟫_ℝ) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i (_ : i ∈ (Finset.univ : Finset (Fin 4)))
      => (hd i).norm_sq)
  have he : (∑ i : Fin 4, 2 * ⟪value period (derivativeOperator period 1 i (u t)),
      value period (derivativeOperator period 0 i v)⟫_ℝ) =
      -2 * ⟪laplacianEvaluation period 2 (by norm_num) (u t), value period v⟫_ℝ := by
    rw [← Finset.mul_sum, gradient_pairing]
    ring
  rw [he] at h
  exact h

omit [Fact (0 < period)] in
/-- The scalar Young bound with the exact viscosity scaling used by maximal regularity. -/
theorem viscosity_young (ν x y : ℝ) (hν : 0 < ν) : 2*x*y ≤ ν*x^2 + ν⁻¹*y^2 := by
  have h := div_nonneg (sq_nonneg (ν*x-y)) hν.le
  have he : (ν*x-y)^2 / ν = ν*x^2 - 2*x*y + ν⁻¹*y^2 := by
    field_simp
    ring
  rw [he] at h
  linarith

/-- The true heat gradient energy absorbs the source without differentiating the source in its
bound. -/
theorem heat_gradient_energy_hasDerivAt (u : ℝ → SobolevSpace period 3)
    (f : SobolevSpace period 1) (ν t : ℝ)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 2 i (u s)))
      (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u t) + f))) t) :
    HasDerivAt (fun s => gradientEnergy period (restrictOperator period (by
        norm_num : 1 ≤ 3) (u s)))
      (-2 * ⟪laplacianEvaluation period 3 (by norm_num) (u t),
        ν • laplacianEvaluation period 3 (by norm_num) (u t) + value period f⟫_ℝ) t := by
  have h := gradient_energy_hasDerivAt period (fun s => truncateOperator period 2 (u s))
    (ν • laplacianOperator period 1 (u t) + f) t hd
  have he : laplacianEvaluation period 2 (by norm_num) (truncateOperator period 2 (u t)) =
      laplacianEvaluation period 3 (by norm_num) (u t) := by
    rw [laplacianEvaluation_apply, laplacianEvaluation_apply]
    rfl
  change HasDerivAt _ (-2 * ⟪laplacianEvaluation period 2 _ (truncateOperator period 2 (u t)),
    ν • value period (laplacianOperator period 1 (u t)) + value period f⟫_ℝ) t at h
  rw [he, laplacianOperator_value] at h
  exact h

/-- The actual derivative of gradient energy controls the full L² Laplacian with no source
derivative loss. -/
theorem heat_gradient_energy_bound (u : ℝ → SobolevSpace period 3)
    (f : SobolevSpace period 1) (ν t : ℝ) (hν : 0 < ν)
    (hd : ∀ i : Fin 4, HasDerivAt (fun s => value period (derivativeOperator period 2 i (u s)))
      (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u t) + f))) t) :
    deriv (fun s => gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u s))) t ≤
      -ν * ‖laplacianEvaluation period 3 (by norm_num) (u t)‖^2 + ν⁻¹ * ‖value period f‖^2 := by
  rw [(heat_gradient_energy_hasDerivAt period u f ν t hd).deriv, inner_add_right, inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hb := norm_inner_le_norm (𝕜 := ℝ) (laplacianEvaluation period 3 (by
      norm_num) (u t)) (value period f)
  rw [Real.norm_eq_abs] at hb
  have hc := neg_le_abs ⟪laplacianEvaluation period 3 (by norm_num) (u t), value period f⟫_ℝ
  have hy := viscosity_young ν ‖laplacianEvaluation period 3 (by
      norm_num) (u t)‖ ‖value period f‖ hν
  nlinarith

end EulerHeatGradientEnergy

end
end

end

section

/-! A genuine H² bound by H¹ and the cylinder Laplacian, used in strong maximal-regularity limits.
-/

section

/-! Exact L² Hessian coercivity from actual commuting strong derivatives. -/

@[expose] public section

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator

variable (period : ℝ) [Fact (0 < period)]

/-- The actual sum of all sixteen second-coordinate L² energies. -/
def hessianEnergy (u : SobolevSpace period 2) : ℝ :=
  ∑ j : Fin 4, ∑ i : Fin 4, ‖value period (derivativeOperator period 0 i
    (derivativeOperator period 1 j u))‖^2

/-- One row of the genuine Hessian energy is the corresponding gradient-Laplacian pairing. -/
theorem hessian_row_identity (u : SobolevSpace period 3) (j : Fin 4) :
    (∑ i : Fin 4, ‖value period (derivativeOperator period 1 i (derivativeOperator period 2 j
        u))‖^2) =
      -⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ := by
  have h := gradient_pairing period (derivativeOperator period 2 j u)
    (truncateOperator period 1 (derivativeOperator period 2 j u))
  have he : laplacianEvaluation period 2 (by norm_num) (derivativeOperator period 2 j u) =
      value period (derivativeOperator period 0 j (laplacianOperator period 1 u)) := by
    rw [← laplacianOperator_value, laplacian_derivative]
  rw [he, value_truncateOperator] at h
  have h' := h.trans (congrArg Neg.neg (real_inner_comm (F := LiftL2 period)
      (value period (derivativeOperator period 2 j u))
      (value period (derivativeOperator period 0 j (laplacianOperator period 1 u)))))
  convert h' using 1
  apply Finset.sum_congr rfl
  intro i _
  exact (real_inner_self_eq_norm_sq (value period (derivativeOperator period 1 i
    (derivativeOperator period 2 j u)))).symm

/-- The sum of the genuine gradient-Laplacian pairings is minus the Laplacian norm squared. -/
theorem laplacian_gradient_pairing (u : SobolevSpace period 3) :
    (∑ j : Fin 4, ⟪value period (derivativeOperator period 2 j u),
      value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ) =
      -‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  have hp := gradient_pairing period (truncateOperator period 2 u) (laplacianOperator period 1 u)
  have he : laplacianEvaluation period 2 (by norm_num) (truncateOperator period 2 u) =
      laplacianEvaluation period 3 (by norm_num) u := by
    rw [laplacianEvaluation_apply, laplacianEvaluation_apply]
    rfl
  rw [he, laplacianOperator_value, real_inner_self_eq_norm_sq] at hp
  exact hp

/-- All genuine second-coordinate derivatives are controlled exactly by the Laplacian. -/
theorem hessianEnergy_eq_laplacian (u : SobolevSpace period 3) :
    hessianEnergy period (truncateOperator period 2 u) =
      ‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  calc
    _ = ∑ j : Fin 4, -⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ :=
      Finset.sum_congr rfl (fun j _ => hessian_row_identity period u j)
    _ = -(∑ j : Fin 4, ⟪value period (derivativeOperator period 2 j u),
        value period (derivativeOperator period 0 j (laplacianOperator period 1 u))⟫_ℝ) :=
      Finset.sum_neg_distrib _
    _ = _ := by rw [laplacian_gradient_pairing, neg_neg]

end EulerHeatGradientEnergy

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevEllipticBound

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeatGenerator
    EulerHeatGradientEnergy

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual second derivative word is bounded by the full genuine Hessian energy. -/
theorem second_word_sq_le_hessian (u : SobolevSpace period 2) (w : Fin 2 → Fin 4) :
    ‖word period u (le_refl 2) w‖^2 ≤ hessianEnergy period u := by
  have hw : Fin.snoc (Fin.snoc (Fin.elim0 : Fin 0 → Fin 4) (w 0)) (w 1) = w := by
    funext i
    fin_cases i <;> rfl
  have he : word period u (le_refl 2) w =
      value period (derivativeOperator period 0 (w 0) (derivativeOperator period 1 (w 1) u)) := by
    change u.val ⟨⟨2, _⟩, w⟩ = u.val ⟨⟨2, _⟩, Fin.snoc (Fin.snoc Fin.elim0 (w 0)) (w 1)⟩
    rw [hw]
  rw [he]
  exact (Finset.single_le_sum (fun i _ => sq_nonneg
    ‖value period (derivativeOperator period 0 i (derivativeOperator period 1 (w 1) u))‖)
    (Finset.mem_univ (w 0))).trans
    (Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun i _ => sq_nonneg
      ‖value period (derivativeOperator period 0 i (derivativeOperator period 1 j u))‖))
      (Finset.mem_univ (w 1)))

/-- The complete H² norm is controlled by its H¹ restriction and the actual Hessian energy. -/
theorem H2_norm_sq_le (u : SobolevSpace period 2) :
    ‖u‖^2 ≤ ‖truncateOperator period 1 u‖^2 + hessianEnergy period u := by
  have hh : 0 ≤ hessianEnergy period u := Finset.sum_nonneg (fun j _ =>
    Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hB : 0 ≤ ‖truncateOperator period 1 u‖^2 + hessianEnergy period u :=
    add_nonneg (sq_nonneg _) hh
  apply (Real.le_sqrt (norm_nonneg u) hB).mp
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  apply Real.le_sqrt_of_sq_le
  by_cases hlow : n ≤ 1
  · have hnorm : ‖u.val ⟨⟨n, hn⟩, w⟩‖ ≤ ‖truncateOperator period 1 u‖ :=
      word_norm_le period (truncateOperator period 1 u) ⟨⟨n, Nat.lt_succ_of_le hlow⟩, w⟩
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (le_add_of_nonneg_right hh)
  · have hn2 : n = 2 := by omega
    subst n
    exact (second_word_sq_le_hessian period u w).trans (le_add_of_nonneg_left (sq_nonneg _))

/-- The actual finite Sobolev elliptic estimate has no Fourier or inverse-operator assumption. -/
theorem H2_norm_sq_le_laplacian (u : SobolevSpace period 3) :
    ‖truncateOperator period 2 u‖^2 ≤ ‖restrictOperator period (by norm_num : 1 ≤ 3) u‖^2 +
      ‖laplacianEvaluation period 3 (by norm_num) u‖^2 := by
  have h := H2_norm_sq_le period (truncateOperator period 2 u)
  rw [hessianEnergy_eq_laplacian] at h
  exact h

end EulerSobolevEllipticBound

end
end

end

section

/-! Integrated genuine heat gradient energy, with the source measured only in L². -/

@[expose] public section

noncomputable section

namespace EulerHeatGradientEnergy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSobolevLaplacian EulerSobolevHeatGenerator
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual integrated heat energy gains the full Laplacian in L² time without a source
derivative in the bound. -/
theorem heat_laplacian_integral_bound (u : ℝ → SobolevSpace period 3)
    (f : ℝ → SobolevSpace period 1) (ν s t : ℝ) (hν : 0 < ν) (hst : s ≤ t)
    (hu : ContinuousOn u (Icc s t)) (hf : ContinuousOn f (Icc s t))
    (hd : ∀ r ∈ Ioo s t, ∀ i : Fin 4,
      HasDerivAt (fun a => value period (derivativeOperator period 2 i (u a)))
        (value period (derivativeOperator period 0 i (ν • laplacianOperator period 1 (u r) + f r)))
            r) :
    ν * (∫ r in s..t, ‖laplacianEvaluation period 3 (by norm_num) (u r)‖^2) ≤
      gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u s)) +
        ν⁻¹ * (∫ r in s..t, ‖value period (f r)‖^2) := by
  let G := fun r => gradientEnergy period (restrictOperator period (by norm_num : 1 ≤ 3) (u r))
  let L := fun r => ‖laplacianEvaluation period 3 (by norm_num) (u r)‖^2
  let F := fun r => ‖value period (f r)‖^2
  have hG : ContinuousOn G (Icc s t) :=
    (gradientEnergy_continuous period).comp_continuousOn
      ((restrictOperator period (by norm_num : 1 ≤ 3)).continuous.comp_continuousOn hu)
  have hL : ContinuousOn L (Icc s t) :=
    (((laplacianEvaluation period 3 (by norm_num)).continuous.comp_continuousOn hu).norm).pow 2
  have hF : ContinuousOn F (Icc s t) :=
    (((valueOperator period 1).continuous.comp_continuousOn hf).norm).pow 2
  have hLi : IntervalIntegrable L volume s t := hL.intervalIntegrable_of_Icc hst
  have hFi : IntervalIntegrable F volume s t := hF.intervalIntegrable_of_Icc hst
  have hφ : IntegrableOn (fun r => -ν * L r + ν⁻¹ * F r) (Icc s t) :=
    ((hL.const_mul (-ν)).add (hF.const_mul ν⁻¹)).integrableOn_Icc
  have hdiff : ∀ r ∈ Ioo s t, HasDerivAt G (deriv G r) r := by
    intro r hr
    exact (heat_gradient_energy_hasDerivAt period u (f r) ν r (hd r hr)).differentiableAt.hasDerivAt
  have hb : ∀ r ∈ Ioo s t, deriv G r ≤ -ν * L r + ν⁻¹ * F r := by
    intro r hr
    exact heat_gradient_energy_bound period u (f r) ν r hν (hd r hr)
  have hi := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le hst hG
    (fun r hr => (hdiff r hr).hasDerivWithinAt) hφ hb
  rw [intervalIntegral.integral_add (hLi.const_mul (-ν)) (hFi.const_mul ν⁻¹),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hi
  have hnonneg := gradientEnergy_nonneg period (restrictOperator period (by norm_num : 1 ≤ 3) (u t))
  change G t - G s ≤ -ν * (∫ r in s..t, L r) + ν⁻¹ * (∫ r in s..t, F r) at hi
  change 0 ≤ G t at hnonneg
  change ν * (∫ r in s..t, L r) ≤ G s + ν⁻¹ * (∫ r in s..t, F r)
  linarith

end EulerHeatGradientEnergy

end
end

end

@[expose] public section

noncomputable section

namespace EulerHeatMaximalEstimate

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerSobolevHeatGenerator EulerHeatGradientEnergy EulerSobolevEllipticBound EulerTimeLp
  EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual gradient energy is bounded by four times the complete H¹ norm squared. -/
theorem gradientEnergy_bound (u : SobolevSpace period 1) : gradientEnergy period u ≤ 4*‖u‖^2 := by
  unfold gradientEnergy
  calc
    _ ≤ ∑ _i : Fin 4, ‖u‖^2 := Finset.sum_le_sum fun i _ => by
      have h := (value_norm_le period (derivativeOperator period 0 i u)).trans
          (derivativeOperator_bound period i u)
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp

omit [Fact (0 < period)] in
/-- Integrating a continuous scalar upper bound by a constant plus another continuous function. -/
theorem integral_le_constant_add (f g : ℝ → ℝ) (c T : ℝ) (hT : 0 ≤ T)
    (hf : Continuous f) (hg : Continuous g) (hfg : ∀ t ∈ Icc 0 T, f t ≤ c + g t) :
    (∫ t in (0 : ℝ)..T, f t) ≤ T*c + ∫ t in (0 : ℝ)..T, g t := by
  have h := intervalIntegral.integral_mono_on hT (hf.intervalIntegrable (μ := volume) 0 T)
    (((continuous_const (y := c)).add hg).intervalIntegrable (μ := volume) 0 T) hfg
  change (∫ t in (0 : ℝ)..T, f t) ≤ ∫ t in (0 : ℝ)..T, c + g t at h
  rw [intervalIntegral.integral_add (intervalIntegrable_const) (hg.intervalIntegrable (μ := volume)
      0 T),
    intervalIntegral.integral_const] at h
  simpa only [sub_zero, smul_eq_mul] using h

/-- The actual pointwise elliptic estimate with the lower Sobolev path norm as a uniform bound. -/
theorem path_H2_point_bound (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) (t :
    ℝ) :
    ‖truncateOperator period 2 (extendPath T hT u t)‖^2 ≤
      ‖(restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        ‖laplacianEvaluation period 3 (by norm_num) (extendPath T hT u t)‖^2 := by
  let low := (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have h := H2_norm_sq_le_laplacian period (extendPath T hT u t)
  have hl := extendPath_norm_le T hT low t
  change ‖restrictOperator period (by norm_num : 1 ≤ 3) (extendPath T hT u t)‖ ≤ ‖low‖ at hl
  change _ ≤ ‖low‖^2 + _
  exact h.trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hl 2) le_rfl)

/-- The actual H² time norm is bounded by the H¹ path norm and the genuine Laplacian time integral.
-/
theorem time_H2_elliptic_bound (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    ‖pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 ≤
      T * ‖(restrictOperator period (by
          norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        ∫ t in (0 : ℝ)..T, ‖laplacianEvaluation period 3 (by
            norm_num) (extendPath T hT u t)‖^2 := by
  let high := (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  have hhigh : Continuous (fun t => ‖extendPath T hT high t‖^2) :=
    ((extendPath_continuous T hT high).norm).pow 2
  have hLap : Continuous (fun t => ‖laplacianEvaluation period 3 (by
      norm_num) (extendPath T hT u t)‖^2) :=
    (((laplacianEvaluation period 3 (by
        norm_num)).continuous.comp (extendPath_continuous T hT u)).norm).pow 2
  rw [pathLp_norm_sq]
  exact integral_le_constant_add _ _ _ T hT hhigh hLap (fun t _ => path_H2_point_bound period T hT
      u t)

/-- The true heat PDE bounds the full L²-time H² norm by H¹ data and undifferentiated L² forcing. -/
theorem heat_time_H2_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ t ∈ Ioo 0 T, ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t))) t) :
    ‖pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 ≤
      (T + 4*ν⁻¹) * ‖(restrictOperator period (by
          norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u‖^2 +
        (ν⁻¹)^2 * ‖pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)‖^2
            := by
  let low := (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u
  let source := (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f
  let L := ∫ t in (0 : ℝ)..T, ‖laplacianEvaluation period 3 (by norm_num) (extendPath T hT u t)‖^2
  have he := heat_laplacian_integral_bound period (extendPath T hT u) (extendPath T hT f) ν 0 T hν
      hT
    (extendPath_continuous T hT u).continuousOn (extendPath_continuous T hT f).continuousOn hd
  have hb := gradientEnergy_bound period (restrictOperator period (by
      norm_num : 1 ≤ 3) (extendPath T hT u 0))
  have hl := extendPath_norm_le T hT low 0
  change ‖restrictOperator period (by norm_num : 1 ≤ 3) (extendPath T hT u 0)‖ ≤ ‖low‖ at hl
  have hinit : gradientEnergy period (restrictOperator period (by
      norm_num : 1 ≤ 3) (extendPath T hT u 0)) ≤ 4*‖low‖^2 := by
    exact hb.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hl 2) (by norm_num))
  have hs : (∫ t in (0 : ℝ)..T, ‖value period (extendPath T hT f t)‖^2) = ‖pathLp T hT source‖^2 :=
    (pathLp_norm_sq T hT source).symm
  rw [hs] at he
  have hL : L ≤ 4*ν⁻¹*‖low‖^2 + (ν⁻¹)^2*‖pathLp T hT source‖^2 := by
    calc
      L = ν⁻¹*(ν*L) := by rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul]
      _ ≤ ν⁻¹*(4*‖low‖^2 + ν⁻¹*‖pathLp T hT source‖^2) :=
        mul_le_mul_of_nonneg_left (he.trans (add_le_add hinit le_rfl)) (inv_nonneg.mpr hν.le)
      _ = _ := by ring
  have hb2 := time_H2_elliptic_bound period T hT u
  change _ ≤ T*‖low‖^2 + L at hb2
  change _ ≤ (T+4*ν⁻¹)*‖low‖^2 + (ν⁻¹)^2*‖pathLp T hT source‖^2
  calc
    _ ≤ T*‖low‖^2 + (4*ν⁻¹*‖low‖^2 + (ν⁻¹)^2*‖pathLp T hT source‖^2) :=
      hb2.trans (add_le_add le_rfl hL)
    _ = _ := by ring

end EulerHeatMaximalEstimate

end
end

end

section

/-! Strong Cauchy convergence from a quadratic norm estimate in complete-space arguments. -/

@[expose] public section

namespace EulerQuadraticCauchy

open scoped Topology

/-- Replacing three vectors by equal vectors preserves a quadratic norm estimate. -/
theorem transport_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (a b : ℝ) (x x' : X) (y y' : Y) (z z' : Z)
    (hx : x = x') (hy : y = y') (hz : z = z')
    (h : ‖x‖ ^ 2 ≤ a * ‖y‖ ^ 2 + b * ‖z‖ ^ 2) : ‖x'‖^2 ≤ a*‖y'‖^2+b*‖z'‖^2 := by
  subst x'; subst y'; subst z'; exact h

/-- A quadratic norm estimate passes to actual strong limits in three normed spaces. -/
theorem limit_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : ℕ → Y) (V : ℕ → Z) (u : X) (f : Y) (v : Z) (a b : ℝ)
    (hu : Filter.Tendsto U Filter.atTop (𝓝 u))
    (hf : Filter.Tendsto F Filter.atTop (𝓝 f))
    (hv : Filter.Tendsto V Filter.atTop (𝓝 v))
    (hb : ∀ n, ‖V n‖ ^ 2 ≤ a * ‖U n‖ ^ 2 + b * ‖F n‖ ^ 2) : ‖v‖^2 ≤ a*‖u‖^2+b*‖f‖^2 := by
  exact le_of_tendsto_of_tendsto' (hv.norm.pow 2)
    (((hu.norm.pow 2).const_mul a).add ((hf.norm.pow 2).const_mul b)) hb

/-- A sequence whose squared differences are bounded by two Cauchy-sequence differences is Cauchy.
-/
theorem cauchy_of_quadratic_bound {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : ℕ → Y) (V : ℕ → Z) (a b : ℝ)
    (hu : CauchySeq U) (hf : CauchySeq F)
    (hb : ∀ n m, ‖V n - V m‖ ^ 2 ≤ a * ‖U n - U m‖ ^ 2 + b * ‖F n - F m‖ ^ 2) : CauchySeq V := by
  have hU : Filter.Tendsto (fun p : ℕ×ℕ => ‖U p.1-U p.2‖) Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hu
  have hF : Filter.Tendsto (fun p : ℕ×ℕ => ‖F p.1-F p.2‖) Filter.atTop (𝓝 0) := by
    simpa only [dist_eq_norm] using cauchySeq_iff_tendsto_dist_atTop_0.mp hf
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simp only [dist_eq_norm]
  apply squeeze_zero (fun p : ℕ×ℕ => norm_nonneg (V p.1-V p.2)) (fun p : ℕ×ℕ =>
      Real.le_sqrt_of_sq_le (hb p.1 p.2))
  have hlim := ((hU.pow 2).const_mul a).add ((hF.pow 2).const_mul b)
  simpa only [zero_pow (by
      norm_num : (2 : ℕ) ≠ 0), mul_zero, add_zero, Real.sqrt_zero] using hlim.sqrt

end EulerQuadraticCauchy

end

end

section

/-! Strong L²-time H² Cauchy convergence from genuine heat energy, avoiding weak compactness. -/

@[expose] public section

noncomputable section

namespace EulerHeatMaximalCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevLaplacian
  EulerHeatMaximalEstimate EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A bounded linear observation preserves the difference form of the forced heat right hand side.
-/
theorem linear_heat_rhs_sub {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (L : Y →L[ℝ] Z) (A : X →L[ℝ] Y) (ν : ℝ) (u v : X) (f g : Y) :
    L (ν • A (u-v)+(f-g)) = L (ν • A u+f)-L (ν • A v+g) := by
  rw [map_sub A, smul_sub, sub_add_sub_comm, map_sub L]

/-- The difference of two actual differentiated heat equations is the same linear equation with
difference source. -/
theorem first_derivative_difference (T : ℝ) (hT : 0 ≤ T) (ν : ℝ)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) (t : ℝ) (i : Fin 4)
    (hu : HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t))) t)
    (hv : HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT v s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT v t) + extendPath T hT g t))) t) :
    HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s)))
      (value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t))) t :=
            by
  have h := hu.fun_sub hv
  have he : (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s))) =
      fun s => value period (derivativeOperator period 2 i (extendPath T hT u s)) -
        value period (derivativeOperator period 2 i (extendPath T hT v s)) := by
    funext s
    exact map_sub ((valueOperator period 2).comp (derivativeOperator period 2 i))
      (u (projIcc 0 T hT s)) (v (projIcc 0 T hT s))
  have hr : value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t)) =
      value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT u t) + extendPath T hT f t)) -
      value period (derivativeOperator period 0 i
        (ν • laplacianOperator period 1 (extendPath T hT v t) + extendPath T hT g t)) := by
    exact linear_heat_rhs_sub ((valueOperator period 0).comp (derivativeOperator period 0 i))
      (laplacianOperator period 1) ν (u (projIcc 0 T hT t)) (v (projIcc 0 T hT t))
      (f (projIcc 0 T hT t)) (g (projIcc 0 T hT t))
  exact (h.congr_deriv hr.symm).congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun he))

/-- Restrict a regularized path to its actual H¹ topology. -/
def lowerPath (T : ℝ) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    C(Icc (0 : ℝ) T, SobolevSpace period 1) :=
  (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u

/-- Embed the actual H² restriction of a regularized path into L² time. -/
def higherTime (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    TimeLp T (SobolevSpace period 2) :=
  pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)

/-- Embed the actual undifferentiated forcing into L² time. -/
def sourceTime (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    TimeLp T (LiftL2 period) :=
  pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)

/-- The lower path restriction preserves differences. -/
theorem lowerPath_sub (T : ℝ) (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    lowerPath period T (u-v) = lowerPath period T u-lowerPath period T v :=
  map_sub ((restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v

/-- The actual higher time embedding preserves differences. -/
theorem higherTime_sub (T : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3)) :
    higherTime period T hT (u-v) = higherTime period T hT u-higherTime period T hT v := by
  let A := (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  exact (congrArg (pathLp T hT) (map_sub A u v)).trans (pathLp_sub T hT (A u) (A v))

/-- The actual source time embedding preserves differences. -/
theorem sourceTime_sub (T : ℝ) (hT : 0 ≤ T) (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1)) :
    sourceTime period T hT (f-g) = sourceTime period T hT f-sourceTime period T hT g := by
  let A := (valueOperator period 1).compLeftContinuous ℝ (Icc (0 : ℝ) T)
  exact (congrArg (pathLp T hT) (map_sub A f g)).trans (pathLp_sub T hT (A f) (A g))

/-- The true linear heat equation controls actual H² time differences by lower path and source
differences. -/
theorem heat_H2_difference_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u v : C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f g : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ t ∈ Ioo 0 T, ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u-v) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u-v) t) + extendPath T hT (f-g) t))) t)
              :
    ‖higherTime period T hT u-higherTime period T hT v‖^2 ≤
      (T+4*ν⁻¹)*‖lowerPath period T u-lowerPath period T v‖^2 +
      (ν⁻¹)^2*‖sourceTime period T hT f-sourceTime period T hT g‖^2 := by
  exact EulerQuadraticCauchy.transport_quadratic_bound (T+4*ν⁻¹) ((ν⁻¹)^2)
    (higherTime period T hT (u-v)) (higherTime period T hT u-higherTime period T hT v)
    (lowerPath period T (u-v)) (lowerPath period T u-lowerPath period T v)
    (sourceTime period T hT (f-g)) (sourceTime period T hT f-sourceTime period T hT g)
    (higherTime_sub period T hT u v) (lowerPath_sub period T u v) (sourceTime_sub period T hT f g)
    (heat_time_H2_bound period T hT ν hν (u-v) (f-g) hd)

/-- Actual regularized heat solutions which converge in H¹ and have Cauchy L² sources converge
strongly in L² time with two full derivatives. -/
theorem heat_H2_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u n) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u n) t) + extendPath T hT (f n) t))) t)
    (hu : CauchySeq (fun n => (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n)))
    (hf : CauchySeq (fun n => pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (f n)))) :
    CauchySeq (fun n => pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n))) := by
  change CauchySeq (fun n => higherTime period T hT (u n))
  change CauchySeq (fun n => lowerPath period T (u n)) at hu
  change CauchySeq (fun n => sourceTime period T hT (f n)) at hf
  apply EulerQuadraticCauchy.cauchy_of_quadratic_bound
    (fun n => lowerPath period T (u n)) (fun n => sourceTime period T hT (f n))
    (fun n => higherTime period T hT (u n)) (T+4*ν⁻¹) ((ν⁻¹)^2) hu hf
  intro n m
  apply heat_H2_difference_bound period T hT ν hν (u n) (u m) (f n) (f m)
  intro t ht i
  exact first_derivative_difference period T hT ν (u n) (u m) (f n) (f m) t i
    (hd n t ht i) (hd m t ht i)

/-- Completeness constructs a genuine Bochner L²-time H² limit of the regularized heat solutions. -/
theorem exists_heat_H2_limit (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 3))
    (f : ℕ → C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT (u n) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (u n) t) + extendPath T hT (f n) t))) t)
    (hu : CauchySeq (fun n => (restrictOperator period (by norm_num : 1 ≤ 3)).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (u n)))
    (hf : CauchySeq (fun n => pathLp T hT ((valueOperator period 1).compLeftContinuous ℝ
      (Icc (0 : ℝ) T) (f n)))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      Filter.Tendsto (fun n => pathLp T hT ((truncateOperator period 2).compLeftContinuous ℝ
        (Icc (0 : ℝ) T) (u n))) Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete (heat_H2_cauchy period T hT ν hν u f hd hu hf)

end EulerHeatMaximalCauchy

end
end

end

section

/-! Actual higher Sobolev norms controlled by lower norms and finitely many top derivative blocks.
-/

@[expose] public section

noncomputable section

namespace EulerSobolevTopBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks

variable (period : ℝ) [Fact (0 < period)]

/-- A full top derivative is literally a second derivative of one of the genuine top word blocks. -/
theorem top_word_block (q : ℕ) (u : SobolevSpace period (2 + q)) (w : Fin (2 + q) → Fin 4) :
    word period u (le_refl (2+q)) w =
      word period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u) (le_refl 2)
        (fun i => w (Fin.castAdd q i)) := by
  rw [wordBlock_word, Fin.append_castAdd_natAdd]

/-- The genuine complete H^(q+2) norm is controlled by H^(q+1) and all order-q H² derivative blocks.
-/
theorem top_blocks_norm_sq (q : ℕ) (u : SobolevSpace period (2 + q)) :
    ‖u‖^2 ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := by
  have hsum : 0 ≤ ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hB : 0 ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := add_nonneg (sq_nonneg _) hsum
  apply (Real.le_sqrt (norm_nonneg u) hB).mp
  change ‖u.val‖ ≤ _
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  rintro ⟨⟨n, hn⟩, w⟩
  apply Real.le_sqrt_of_sq_le
  by_cases hlow : n ≤ 1+q
  · have hnorm : ‖u.val ⟨⟨n, hn⟩, w⟩‖ ≤ ‖restrictOperator period (by omega : 1+q ≤ 2+q) u‖ :=
      word_norm_le period (restrictOperator period (by omega : 1+q ≤ 2+q) u)
        ⟨⟨n, Nat.lt_succ_of_le hlow⟩, w⟩
    exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans
      (le_add_of_nonneg_right hsum)
  · have hn2 : n = 2+q := by omega
    subst n
    have hw := top_word_block period q u w
    change ‖word period u (le_refl (2+q)) w‖^2 ≤ _
    rw [hw]
    have hnorm := word_norm_le period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u)
      (⟨⟨2, by omega⟩, fun i => w (Fin.castAdd q i)⟩ : SobolevWord 2)
    change ‖word period (wordBlock period 2 q (fun i => w (Fin.natAdd 2 i)) u)
      (le_refl 2) (fun i => w (Fin.castAdd q i))‖ ≤ _ at hnorm
    have hs := Finset.single_le_sum (fun v _ => sq_nonneg ‖wordBlock period 2 q v u‖)
      (Finset.mem_univ (fun i => w (Fin.natAdd 2 i)))
    exact ((pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hs).trans
      (le_add_of_nonneg_left (sq_nonneg _))

end EulerSobolevTopBlocks

end
end

end

section

/-! Strong time-space completion controlled by genuine finite spatial derivative blocks. -/

@[expose] public section

noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
  EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks EulerSobolevTopBlocks
open scoped Topology

/-- Integration preserves a finite quadratic norm comparison between bounded spatial observations.
-/
theorem pathLp_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u‖^2 ≤ ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 := by
  have hu := extendPath_continuous T hT u
  have hA : Continuous (fun t => ‖A (extendPath T hT u t)‖^2) := (A.continuous.comp hu).norm.pow 2
  have hB : ∀ i, Continuous (fun t => ‖B i (extendPath T hT u t)‖^2) :=
    fun i => ((B i).continuous.comp hu).norm.pow 2
  have hsum : Continuous (fun t => ∑ i, ‖B i (extendPath T hT u t)‖^2) := continuous_finsetSum _
      (fun i _ => hB i)
  have h := intervalIntegral.integral_mono_on hT ((hu.norm.pow 2).intervalIntegrable (μ := volume)
      0 T)
    ((hA.add hsum).intervalIntegrable (μ := volume) 0 T) (fun t _ => hb (extendPath T hT u t))
  change (∫ t in (0 : ℝ)..T, ‖extendPath T hT u t‖^2) ≤
    ∫ t in (0 : ℝ)..T, ‖A (extendPath T hT u t)‖^2 + ∑ i, ‖B i (extendPath T hT u t)‖^2 at h
  rw [intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 T)
    (hsum.intervalIntegrable (μ := volume) 0 T),
    intervalIntegral.integral_finsetSum (fun i _ => (hB i).intervalIntegrable (μ := volume) 0 T)]
        at h
  simp only [pathLp_norm_sq]
  exact h

/-- All actual order-q H² blocks and the lower H^(q+1) norm control the full H^(q+2) time norm. -/
theorem top_blocks_time_norm (period : ℝ) [Fact (0 < period)] (q : ℕ)
    (T : ℝ) (hT : 0 ≤ T) (u : C(Icc (0 : ℝ) T, SobolevSpace period (2 + q))) :
    ‖pathLp T hT u‖^2 ≤
      ‖pathLp T hT ((restrictOperator period (by
          omega : 1+q ≤ 2+q)).compLeftContinuous ℝ (Icc (0 : ℝ) T) u)‖^2 +
      ∑ w : Fin q → Fin 4, ‖pathLp T hT ((wordBlock period 2 q w).compLeftContinuous ℝ (Icc (0 : ℝ)
          T) u)‖^2 :=
  pathLp_quadratic_bound _ _ (top_blocks_norm_sq period q) T hT u

end EulerTopBlockTimeNorm

end
end

end

section

/-! Actual strong L²-time completion from finitely many closed derivative blocks. -/

section

/-! Strong Cauchy convergence controlled by finitely many genuine norm observations. -/

@[expose] public section

namespace EulerQuadraticCauchy

open scoped Topology

/-- A finite family of Cauchy observations controlling squared differences forces a sequence to be
Cauchy. -/
theorem cauchy_of_finite_quadratic_bound {X Y Z I : Type*} [Fintype I]
    [NormedAddCommGroup X] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    (U : ℕ → X) (F : I → ℕ → Y) (V : ℕ → Z)
    (hu : CauchySeq U) (hf : ∀ i, CauchySeq (F i))
    (hb : ∀ n m, ‖V n - V m‖ ^ 2 ≤ ‖U n - U m‖ ^ 2 + ∑ i, ‖F i n - F i m‖ ^ 2) : CauchySeq V := by
  have hU : Filter.Tendsto (fun p : ℕ×ℕ => ‖U p.1-U p.2‖^2) Filter.atTop (𝓝 0) := by
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp hu).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hF : ∀ i, Filter.Tendsto (fun p : ℕ×ℕ => ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    intro i
    have h := (cauchySeq_iff_tendsto_dist_atTop_0.mp (hf i)).pow 2
    simpa only [dist_eq_norm, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using h
  have hsum : Filter.Tendsto (fun p : ℕ×ℕ => ∑ i, ‖F i p.1-F i p.2‖^2) Filter.atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun i _ => hF i)
  apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
  simp only [dist_eq_norm]
  apply squeeze_zero (fun p : ℕ×ℕ => norm_nonneg (V p.1-V p.2))
    (fun p : ℕ×ℕ => Real.le_sqrt_of_sq_le (hb p.1 p.2))
  simpa only [add_zero, Real.sqrt_zero] using (hU.add hsum).sqrt

end EulerQuadraticCauchy

end

end

@[expose] public section

noncomputable section

namespace EulerTopBlockTimeNorm

open MeasureTheory Set EulerTimeLp EulerVolterraConvolution
open scoped Topology

variable {X Y Z I : Type*} [Fintype I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Bounded spatial observation and actual time embedding preserve subtraction together. -/
theorem mapped_pathLp_sub (T : ℝ) (hT : 0 ≤ T) (A : X →L[ℝ] Y)
    (u v : C(Icc (0 : ℝ) T, X)) :
    pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u-v)) =
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
      pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v) :=
  (congrArg (pathLp T hT) (map_sub (A.compLeftContinuous ℝ (Icc (0 : ℝ) T)) u v)).trans
    (pathLp_sub T hT _ _)

/-- The integrated genuine spatial block bound also controls time-space differences. -/
theorem pathLp_quadratic_difference (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u v : C(Icc (0 : ℝ) T, X)) :
    ‖pathLp T hT u-pathLp T hT v‖^2 ≤
      ‖pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 +
      ∑ i, ‖pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) u) -
        pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) v)‖^2 := by
  have h := pathLp_quadratic_bound A B hb T hT (u-v)
  simp only [pathLp_sub, mapped_pathLp_sub] at h
  exact h

/-- Genuine finite block convergence and lower-order convergence construct strong convergence in the
full Bochner Sobolev space. -/
theorem cauchy_pathLp_of_blocks (A : X →L[ℝ] Y) (B : I → X →L[ℝ] Z)
    (hb : ∀ x, ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 + ∑ i, ‖B i x‖ ^ 2)
    (T : ℝ) (hT : 0 ≤ T) (u : ℕ → C(Icc (0 : ℝ) T, X))
    (hu : CauchySeq (fun n => pathLp T hT (A.compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))))
    (hf : ∀ i, CauchySeq (fun n => pathLp T hT ((B i).compLeftContinuous ℝ (Icc (0 : ℝ) T) (u n))))
        :
    CauchySeq (fun n => pathLp T hT (u n)) := by
  exact EulerQuadraticCauchy.cauchy_of_finite_quadratic_bound _ _ _ hu hf
    (fun n m => pathLp_quadratic_difference A B hb T hT (u n) (u m))

end EulerTopBlockTimeNorm

end
end

end

section

/-! Genuine maximal spatial regularity of the actual viscous mild solution, proved by strong Cauchy
limits. -/

@[expose] public section

noncomputable section

namespace EulerHeatMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerSobolevLaplacian EulerTimeLp EulerVolterraConvolution EulerRegularizedMildEquation
  EulerHeatMaximalCauchy EulerHeatMaximalEstimate
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual regularized mild solutions are strongly Cauchy in Bochner L² time with two
derivatives. -/
theorem regularized_mild_cauchy (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) := by
  apply heat_H2_cauchy period T hT ν hν (fun n => regularizedState period T n u)
    (fun n => regularizedForcing period T n f)
    (regularizedState_first_time_derivative period T hT ν hν u₀ f u hsol)
  · exact (regularizedState_low_tendsto period T u).cauchySeq
  · exact (pathLp_tendsto T hT _ _ (regularizedForcing_value_tendsto period T f)).cauchySeq

/-- The strong higher-order limit has exactly the original lower-order field almost everywhere in
time. -/
theorem regularized_limit_restriction (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1)) (U : TimeLp T (SobolevSpace period 2))
    (hU : Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u))
        Filter.atTop (𝓝 U)) :
    ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) := by
  have hlow := regularizedState_low_tendsto period T u
  have hrestrict : Filter.Tendsto (fun n => (truncateOperator period 1).compLeftContinuous ℝ (Icc
      (0 : ℝ) T)
      ((truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState period T
          n u))) Filter.atTop (𝓝 u) := by
    convert hlow using 1
    funext n
    apply ContinuousMap.ext
    intro t
    apply value_injective period
    rfl
  exact limit_restriction_ae T hT (truncateOperator period 1)
    (fun n => (truncateOperator period 2).compLeftContinuous ℝ (Icc (0 : ℝ) T) (regularizedState
        period T n u)) u U hU hrestrict

/-- The genuine heat estimate passes to the strong higher-order time limit without weak compactness.
-/
theorem regularized_limit_bound (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period 0)) (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hd : ∀ n t, t ∈ Ioo 0 T → ∀ i : Fin 4,
      HasDerivAt (fun s => value period (derivativeOperator period 2 i (extendPath T hT
          (regularizedState period T n u) s)))
        (value period (derivativeOperator period 0 i
          (ν • laplacianOperator period 1 (extendPath T hT (regularizedState period T n u) t) +
            extendPath T hT (regularizedForcing period T n f) t))) t)
    (U : TimeLp T (SobolevSpace period 2))
    (hU : Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u))
        Filter.atTop (𝓝 U)) :
    ‖U‖^2 ≤ (T+4*ν⁻¹)*‖u‖^2 + (ν⁻¹)^2 *
      ‖pathLp T hT ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)‖^2 := by
  have hlow := regularizedState_low_tendsto period T u
  have hsource := pathLp_tendsto T hT _
    ((valueOperator period 0).compLeftContinuous ℝ (Icc (0 : ℝ) T) f)
    (regularizedForcing_value_tendsto period T f)
  exact EulerQuadraticCauchy.limit_quadratic_bound
    (fun n => lowerPath period T (regularizedState period T n u))
    (fun n => sourceTime period T hT (regularizedForcing period T n f))
    (fun n => higherTime period T hT (regularizedState period T n u)) u _ U (T+4*ν⁻¹) ((ν⁻¹)^2)
    hlow hsource hU (fun n => heat_time_H2_bound period T hT ν hν
      (regularizedState period T n u) (regularizedForcing period T n f) (hd n))

/-- Completeness of actual H² Bochner space constructs its strong Cauchy limit. -/
theorem exists_H2_time_limit (T : ℝ) (u : ℕ → TimeLp T (SobolevSpace period 2)) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period 2), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

/-- Strong completion constructs the higher-order limit of the concrete mild-solution
approximations. -/
theorem exists_regularized_mild_limit (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop
          (𝓝 U) := by
  have hc : CauchySeq (fun n => higherTime period T hT (regularizedState period T n u)) :=
    regularized_mild_cauchy period T hT ν hν u₀ f u hsol
  exact exists_H2_time_limit period T (fun n => higherTime period T hT (regularizedState period T n
      u)) hc

/-- The actual viscous mild solution with H¹ values and continuous L² source has two full spatial
derivatives in L² time.
The higher-regularity element is constructed in the complete Bochner space and identified with the
original field almost everywhere. -/
theorem viscous_mild_maximal_regularity (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period 2),
      ((fun t => truncateOperator period 1 (U t)) =ᵐ[timeMeasure T] extendPath T hT u) ∧
      Filter.Tendsto (fun n => higherTime period T hT (regularizedState period T n u)) Filter.atTop
          (𝓝 U) := by
  refine (exists_regularized_mild_limit period T hT ν hν u₀ f u hsol).imp ?_
  intro U hU
  exact ⟨regularized_limit_restriction period T hT u U hU, hU⟩

/-- Actual H² spatial representatives exist for almost every time of the genuine H¹ viscous mild
solution. -/
theorem viscous_mild_ae_H2 (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (u₀ : SobolevSpace period 1) (f : C(Icc (0 : ℝ) T, SobolevSpace period 0))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period 1))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period 1 (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period 0 ν hν r (extendPath T hT f (t.val-r))) :
    ∀ᵐ t ∂timeMeasure T, ∃ v : SobolevSpace period 2, value period v = value period (extendPath T
        hT u t) := by
  obtain ⟨U, hU, _⟩ := viscous_mild_maximal_regularity period T hT ν hν u₀ f u hsol
  filter_upwards [hU] with t ht
  exact ⟨U t, congrArg (value period) ht⟩

end EulerHeatMaximalRegularity

end
end

end

@[expose] public section

noncomputable section

namespace EulerMaximalTopCauchy

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerTimeLp EulerVolterraConvolution EulerMildWordEquation EulerMildTopWord
  EulerRegularizedMildEquation EulerRegularizedTopBlocks EulerHeatMaximalRegularity
  EulerTopBlockTimeNorm EulerSobolevTopBlocks EulerSobolevWordBlocks EulerHeatMaximalCauchy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The top block norm estimate in the original q+1 indexing used by actual mild solutions. -/
theorem top_blocks_norm_sq_original (q : ℕ) (u : SobolevSpace period (2 + q)) :
    ‖u‖^2 ≤ ‖restrictOperator period (by omega : q+1 ≤ 2+q) u‖^2 +
      ∑ w : Fin q → Fin 4, ‖wordBlock period 2 q w u‖^2 := by
  have h := top_blocks_norm_sq period q u
  have hr := restrictOperator_bound period (by omega : 1+q ≤ q+1)
    (restrictOperator period (by omega : q+1 ≤ 2+q) u)
  rw [restrictOperator_comp] at hr
  exact h.trans (add_le_add (pow_le_pow_left₀ (norm_nonneg _) hr 2) le_rfl)

/-- Every actual top-word regularization is strongly Cauchy in time with its two full extra spatial
derivatives. -/
theorem maximalApproximation_word_cauchy {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r)))
    (w : Fin q → Fin 4) :
    CauchySeq (fun n => pathLp T hT ((wordBlock period 2 q w).compLeftContinuous ℝ (Icc (0 : ℝ) T)
      (maximalApproximation period q T n u))) := by
  have h := regularized_mild_cauchy period T hT ν hν
    (boundedWordBlock period 1 q (by omega) w u₀)
    (mapPath period T (boundedWordBlock period 0 q (by omega) w) f)
    (mapPath period T (boundedWordBlock period 1 q (by omega) w) u)
    (top_word_mild period ν hν T hT u₀ f u hsol w)
  simpa only [maximalApproximation_word, higherTime] using h

/-- The genuine full H^(q+2) heat regularizations form a strong Bochner Cauchy sequence, with no
assumed derivative bound. -/
theorem maximalApproximation_cauchy {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    CauchySeq (fun n => pathLp T hT (maximalApproximation period q T n u)) := by
  apply cauchy_pathLp_of_blocks (restrictOperator period (by omega : q+1 ≤ 2+q))
    (fun w : Fin q → Fin 4 => wordBlock period 2 q w) (top_blocks_norm_sq_original period q)
    T hT (fun n => maximalApproximation period q T n u)
  · exact (pathLp_tendsto T hT _ u (maximalApproximation_low_tendsto period q T u)).cauchySeq
  · exact maximalApproximation_word_cauchy period ν hν T hT u₀ f u hsol

end EulerMaximalTopCauchy

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevMaximalRegularity

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevHeat
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks EulerMaximalTopCauchy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The complete actual Bochner Sobolev space realizes every strong Cauchy sequence. -/
theorem exists_sobolev_time_limit (q : ℕ) (T : ℝ)
    (u : ℕ → TimeLp T (SobolevSpace period (2 + q))) (hu : CauchySeq u) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)), Filter.Tendsto u Filter.atTop (𝓝 U) :=
  cauchySeq_tendsto_of_complete hu

/-- Completion supplies the genuine higher-order limit of the actual viscous approximations. -/
theorem exists_maximal_mild_limit {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)),
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop (𝓝
          U) := by
  have hc : CauchySeq (fun n => pathLp T hT (maximalApproximation period q T n u)) :=
    maximalApproximation_cauchy period ν hν T hT u₀ f u hsol
  exact exists_sobolev_time_limit period q T (fun n => pathLp T hT (maximalApproximation period q T
      n u)) hc

/-- The actual higher-order limit restricts to the original viscous solution almost everywhere. -/
theorem maximal_limit_restriction {q : ℕ} (T : ℝ) (hT : 0 ≤ T)
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop
        (𝓝 U)) :
    ((fun t => restrictOperator period (by
        omega : q+1 ≤ 2+q) (U t)) =ᵐ[timeMeasure T] extendPath T hT u) :=
  limit_restriction_ae T hT (restrictOperator period (by omega : q+1 ≤ 2+q))
    (fun n => maximalApproximation period q T n u) u U hU (maximalApproximation_low_tendsto period
        q T u)

/-- Actual viscous mild solutions with continuous Hq forcing and H^(q+1) values possess full H^(q+2)
regularity in Bochner L² time.
The stronger field is constructed from genuine heat approximations and identified with the original
field almost everywhere. -/
theorem viscous_mild_maximal_regularity {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∃ U : TimeLp T (SobolevSpace period (2+q)),
      ((fun t => restrictOperator period (by
          omega : q+1 ≤ 2+q) (U t)) =ᵐ[timeMeasure T] extendPath T hT u) ∧
      Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n u)) Filter.atTop (𝓝
          U) := by
  refine (exists_maximal_mild_limit period ν hν T hT u₀ f u hsol).imp ?_
  intro U hU
  exact ⟨maximal_limit_restriction period T hT u U hU, hU⟩

/-- The genuine full higher-order spatial derivatives exist at almost every time of the actual
viscous solution. -/
theorem viscous_mild_ae_higher {q : ℕ} (ν : ℝ) (hν : 0 < ν) (T : ℝ) (hT : 0 ≤ T)
    (u₀ : SobolevSpace period (q + 1)) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      u t = heatOperator period (q+1) (2*ν*t.val).toNNReal u₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r (extendPath T hT f (t.val-r))) :
    ∀ᵐ t ∂timeMeasure T, ∃ v : SobolevSpace period (2+q),
      restrictOperator period (by omega : q+1 ≤ 2+q) v = extendPath T hT u t := by
  obtain ⟨U, hU, _⟩ := viscous_mild_maximal_regularity period ν hν T hT u₀ f u hsol
  filter_upwards [hU] with t ht
  exact ⟨U t, ht⟩

end EulerSobolevMaximalRegularity
