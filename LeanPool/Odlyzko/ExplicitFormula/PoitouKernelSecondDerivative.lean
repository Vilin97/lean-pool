/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.PoitouKernelDerivative

/-!
# Poitou Kernel Second Derivative

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter
open scoped Topology

namespace NumberField.Odlyzko

/-- A poitou kernel second derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouKernelSecondDerivative
    (f f' f'' : ℝ → ℝ) (x : ℝ) : ℝ :=
  f'' x / Real.cosh (x / 2) -
    f' x * Real.sinh (x / 2) / Real.cosh (x / 2) ^ 2 -
    f x / (4 * Real.cosh (x / 2)) +
    f x * Real.sinh (x / 2) ^ 2 /
      (2 * Real.cosh (x / 2) ^ 3)

theorem hasDerivAt_poitouKernelDerivative
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (x : ℝ) :
    HasDerivAt (poitouKernelDerivative f f')
      (poitouKernelSecondDerivative f f' f'' x) x := by
  let c : ℝ → ℝ := fun z ↦ Real.cosh (z / 2)
  let sh : ℝ → ℝ := fun z ↦ Real.sinh (z / 2)
  have hc : HasDerivAt c (sh x / 2) x := by
    dsimp [c, sh]
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).cosh
  have hsh : HasDerivAt sh (c x / 2) x := by
    dsimp [c, sh]
    simpa only [div_eq_mul_inv, id_eq, one_mul] using
      ((hasDerivAt_id x).div_const 2).sinh
  have hcne : c x ≠ 0 := by
    dsimp [c]
    exact (Real.cosh_pos _).ne'
  have hfirst := (hf' x).div hc hcne
  have hsecond :=
    (((hf x).mul hsh).div
      ((hc.mul hc).const_mul 2)
      (by
        simp_all))
  have h := hfirst.sub hsecond
  have he :
      HasDerivAt (poitouKernelDerivative f f')
        (poitouKernelSecondDerivative f f' f'' x) x := by
    have hevent :
        poitouKernelDerivative f f' =ᶠ[𝓝 x]
          (f' / c - (f * sh) / (fun z ↦ 2 * (c * c) z)) :=
      Filter.Eventually.of_forall fun z ↦ by
        unfold poitouKernelDerivative
        dsimp [c, sh]
        ring
    have hfun := h.congr_of_eventuallyEq hevent
    refine hfun.congr_deriv ?_
    unfold poitouKernelSecondDerivative
    dsimp [c, sh]
    field_simp [(Real.cosh_pos (x / 2)).ne']
    ring
  grind

theorem abs_poitouKernelSecondDerivative_le
    (f f' f'' : ℝ → ℝ) (x : ℝ) :
    |poitouKernelSecondDerivative f f' f'' x| ≤
      |f'' x| + |f' x| + 3 * |f x| / 4 := by
  let c := Real.cosh (x / 2)
  let sh := Real.sinh (x / 2)
  have hc : 1 ≤ c := Real.one_le_cosh _
  have hcpos : 0 < c := Real.cosh_pos _
  have hsh : |sh| ≤ c := abs_sinh_le_cosh _
  unfold poitouKernelSecondDerivative
  change
    |f'' x / c - f' x * sh / c ^ 2 -
        f x / (4 * c) + f x * sh ^ 2 / (2 * c ^ 3)| ≤ _
  calc
    |f'' x / c - f' x * sh / c ^ 2 -
        f x / (4 * c) + f x * sh ^ 2 / (2 * c ^ 3)| ≤
      |f'' x / c| + |f' x * sh / c ^ 2| +
        |f x / (4 * c)| + |f x * sh ^ 2 / (2 * c ^ 3)| := by
      have h₁ := abs_add_le
        (f'' x / c - f' x * sh / c ^ 2 - f x / (4 * c))
        (f x * sh ^ 2 / (2 * c ^ 3))
      have h₂ := abs_sub
        (f'' x / c - f' x * sh / c ^ 2) (f x / (4 * c))
      have h₃ := abs_sub (f'' x / c) (f' x * sh / c ^ 2)
      linarith
    _ ≤ |f'' x| + |f' x| + |f x| / 4 + |f x| / 2 := by
      apply add_le_add
      · apply add_le_add
        · apply add_le_add
          · rw [abs_div, abs_of_pos hcpos]
            exact (div_le_iff₀ hcpos).2
              (by simpa using mul_le_mul_of_nonneg_left hc (abs_nonneg (f'' x)))
          · rw [abs_div, abs_mul,
              abs_of_pos (pow_pos hcpos 2)]
            apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
            calc
              |f' x| * |sh| ≤ |f' x| * c :=
                mul_le_mul_of_nonneg_left hsh (abs_nonneg _)
              _ ≤ |f' x| * c ^ 2 := by
                gcongr
                nlinarith
              _ = |f' x| * c ^ 2 := rfl
        · rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
            abs_of_pos hcpos]
          apply (div_le_iff₀ (mul_pos (by norm_num) hcpos)).2
          nlinarith [abs_nonneg (f x)]
      · rw [abs_div, abs_mul, abs_mul, abs_pow, abs_pow,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_of_pos hcpos]
        apply (div_le_iff₀ (mul_pos (by norm_num) (pow_pos hcpos 3))).2
        have hsq : |sh| ^ 2 ≤ c ^ 2 := by gcongr
        have hc3 : c ^ 2 ≤ c ^ 3 := by
          nlinarith [sq_nonneg c]
        nlinarith [abs_nonneg (f x)]
    _ = _ := by ring

/-- A poitou vertical profile second derivative used in the Odlyzko-bound argument. -/
noncomputable def poitouVerticalProfileSecondDerivative
    (f f' f'' : ℝ → ℝ) (σ x : ℝ) : ℂ :=
  (poitouKernelSecondDerivative f f' f'' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    2 * (σ - 1 / 2) *
      (poitouKernelDerivative f f' x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x) +
    (σ - 1 / 2) ^ 2 * (poitouKernel f x : ℂ) *
      Complex.exp ((σ - 1 / 2) * x)

theorem hasDerivAt_poitouVerticalProfileDerivative
    {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (σ x : ℝ) :
    HasDerivAt (poitouVerticalProfileDerivative f f' σ)
      (poitouVerticalProfileSecondDerivative f f' f'' σ x) x := by
  let a : ℝ := σ - 1 / 2
  have hk :=
    (hasDerivAt_poitouKernel hf x).ofReal_comp
  have hk' :=
    (hasDerivAt_poitouKernelDerivative hf hf' x).ofReal_comp
  have he :
      HasDerivAt (fun z : ℝ ↦ Complex.exp (a * z))
        (a * Complex.exp (a * x)) x := by
    convert (((hasDerivAt_id x).const_mul a).ofReal_comp.cexp) using 1 <;>
      simp only [id_eq] <;> push_cast <;> ring
  unfold poitouVerticalProfileDerivative
    poitouVerticalProfileSecondDerivative
  dsimp [a] at he ⊢
  have hleft := hk'.mul he
  have hright := hk.mul
    (he.const_mul (((σ - 1 / 2 : ℝ) : ℂ)))
  have h := hleft.add hright
  have h' : HasDerivAt
      (poitouVerticalProfileDerivative f f' σ)
      (poitouVerticalProfileSecondDerivative f f' f'' σ x) x := by
    have hevent :
        poitouVerticalProfileDerivative f f' σ =ᶠ[𝓝 x]
          (((fun z : ℝ ↦ (poitouKernelDerivative f f' z : ℂ)) *
              fun z : ℝ ↦ Complex.exp
                (((σ - 1 / 2 : ℝ) : ℂ) * (z : ℂ))) +
            (fun z : ℝ ↦ (poitouKernel f z : ℂ)) *
              fun z : ℝ ↦ ((σ - 1 / 2 : ℝ) : ℂ) *
                Complex.exp (((σ - 1 / 2 : ℝ) : ℂ) * (z : ℂ))) :=
      Filter.Eventually.of_forall fun z ↦ by
        unfold poitouVerticalProfileDerivative
        simp
    have hfun := h.congr_of_eventuallyEq hevent
    refine hfun.congr_deriv ?_
    unfold poitouVerticalProfileSecondDerivative
    push_cast
    ring
  exact h'

end NumberField.Odlyzko
