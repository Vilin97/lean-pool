/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouTransform
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Poitou Kernel Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex

namespace NumberField.Odlyzko

theorem abs_sinh_le_cosh (x : ℝ) :
    |Real.sinh x| ≤ Real.cosh x := by
  have hid := Real.cosh_sq_sub_sinh_sq x
  have hsq : Real.sinh x ^ 2 ≤ Real.cosh x ^ 2 := by
    nlinarith
  have habssq : |Real.sinh x| ^ 2 ≤ Real.cosh x ^ 2 := by simp_all
  exact ((sq_le_sq₀ (abs_nonneg _) (Real.cosh_pos x).le)).mp habssq

/-- A poitou kernel derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouKernelDerivative
    (f f' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f' x / Real.cosh (x / 2) -
    f x * Real.sinh (x / 2) / (2 * Real.cosh (x / 2) ^ 2)

theorem hasDerivAt_poitouKernel
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x) (x : ℝ) :
    HasDerivAt (poitouKernel f)
      (poitouKernelDerivative f f' x) x := by
  unfold poitouKernel poitouKernelDerivative
  have hden :
      HasDerivAt (fun z : ℝ ↦ Real.cosh (z / 2))
        (Real.sinh (x / 2) / 2) x := by
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have h := (hf x).div hden (Real.cosh_pos (x / 2)).ne'
  exact h.congr_deriv (by
    grind)

theorem abs_poitouKernelDerivative_le
    (f f' : ℝ → ℝ) (x : ℝ) :
    |poitouKernelDerivative f f' x| ≤ |f' x| + |f x| / 2 := by
  unfold poitouKernelDerivative
  have hc : 1 ≤ Real.cosh (x / 2) := Real.one_le_cosh _
  have hcpos : 0 < Real.cosh (x / 2) := Real.cosh_pos _
  calc
    |f' x / Real.cosh (x / 2) -
        f x * Real.sinh (x / 2) /
          (2 * Real.cosh (x / 2) ^ 2)| ≤
      |f' x / Real.cosh (x / 2)| +
        |f x * Real.sinh (x / 2) /
          (2 * Real.cosh (x / 2) ^ 2)| :=
      abs_sub _ _
    _ ≤ |f' x| + |f x| / 2 := by
      rw [abs_div, abs_div, abs_mul,
        abs_of_pos hcpos, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, abs_of_pos hcpos]
      apply add_le_add
      · exact (div_le_iff₀ hcpos).2
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hc (abs_nonneg (f' x)))
      · have hratio :
            |Real.sinh (x / 2)| / Real.cosh (x / 2) ^ 2 ≤ 1 := by
          apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
          simpa only [one_mul] using (show
              |Real.sinh (x / 2)| ≤ Real.cosh (x / 2) ^ 2 by
            calc
            |Real.sinh (x / 2)| ≤ Real.cosh (x / 2) :=
              abs_sinh_le_cosh _
            _ ≤ Real.cosh (x / 2) ^ 2 := by
              nlinarith)
        calc
          |f x| * |Real.sinh (x / 2)| /
                (2 * Real.cosh (x / 2) ^ 2) =
              |f x| / 2 *
                (|Real.sinh (x / 2)| / Real.cosh (x / 2) ^ 2) := by
            ring
          _ ≤ |f x| / 2 * 1 :=
            mul_le_mul_of_nonneg_left hratio (by positivity)
          _ = |f x| / 2 := mul_one _

/-- A poitou vertical profile derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouVerticalProfileDerivative
    (f f' : ℝ → ℝ) (σ x : ℝ) : ℂ :=
  (poitouKernelDerivative f f' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    (poitouKernel f x : ℂ) *
      ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x))

theorem hasDerivAt_poitouVerticalProfile
    {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (σ x : ℝ) :
    HasDerivAt
      (fun z : ℝ ↦
        (poitouKernel f z : ℂ) *
          Complex.exp ((σ - 1 / 2) * z))
      (poitouVerticalProfileDerivative f f' σ x) x := by
  have hk := (hasDerivAt_poitouKernel hf x).ofReal_comp
  have he :
      HasDerivAt (fun z : ℝ ↦
        Complex.exp ((σ - 1 / 2) * z))
        ((σ - 1 / 2) * Complex.exp ((σ - 1 / 2) * x)) x := by
    have hlin :=
      ((hasDerivAt_id x).const_mul (σ - 1 / 2)).ofReal_comp
    convert hlin.cexp using 1 <;>
      simp only [id_eq] <;> push_cast <;> ring
  exact hk.mul he

end NumberField.Odlyzko
