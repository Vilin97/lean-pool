/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SymFun.HookVanishing

/-!
# Rationality of the Newton generating series

The Newton generating series of a sequence obeying a nontrivial
linear recurrence is a rational function.
`RationalityFromRecurrence.lean` produces a coprime polynomial pair
from the recurrence; here both constant terms are normalised to 1,
which is the form the trace zeta function is read in, and the
recurrence itself is supplied by hook vanishing.
-/

@[expose] public section

namespace RS

open scoped Polynomial PowerSeries

/-! ### Normalising both constant terms to 1 -/

-- Raised budget: the rational form is assembled from the
-- recurrence, so the whole truncated product enters the term.
/-- The Newton generating series of a sequence satisfying a nontrivial
linear recurrence is a rational function: there exist coprime
polynomials `P, Q` with constant terms 1, `deg P ≤ b`, `deg Q ≤ a`,
such that `H · ↑Q = ↑P` in `ℂ⟦X⟧`. -/
theorem newtonH_series_rational {t : ℕ → ℂ} {a b : ℕ}
    (c : Fin (a + 1) → ℂ) (hc : c ≠ 0)
    (hrec : ∀ ρ : ℤ, (b : ℤ) - a ≤ ρ →
      ∑ k : Fin (a + 1), c k * newtonHZ t (ρ + 1 + (k : ℤ)) = 0) :
    ∃ P Q : Polynomial ℂ,
      P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧
      P.natDegree ≤ b ∧ Q.natDegree ≤ a ∧
      IsCoprime P Q ∧
      newtonHSeries t * (↑Q : ℂ⟦X⟧) = ↑P := by
  -- Get raw truncated pair
  obtain ⟨Q, P, hQ_ne, hP_ne, hQH, hQ_deg, hP_deg⟩ :=
    truncated_product_from_recurrence c hc hrec
  -- Get coprime pair with nonzero constant coefficients
  obtain ⟨Q₀, P₀, hQ0_ne, hP0_ne, hcop, hQ0H, hQ0c, hP0c,
    hQ0_deg_le, hP0_deg_le⟩ := coprime_pair_from_product Q P hQ_ne hP_ne hQH
  -- Constant coefficients are equal (since H has constant coeff 1)
  have hcoeff_eq : Q₀.coeff 0 = P₀.coeff 0 := by
    have := congr_arg PowerSeries.constantCoeff hQ0H
    simp only [map_mul, Polynomial.constantCoeff_coe] at this
    rwa [newtonH_series_constantCoeff, mul_one] at this
  -- Normalise to constant term 1
  set u := Q₀.coeff 0 with hu_def
  have hu_ne : u ≠ 0 := hQ0c
  set P' := Polynomial.C u⁻¹ * P₀ with hP'_def
  set Q' := Polynomial.C u⁻¹ * Q₀ with hQ'_def
  refine ⟨P', Q', ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- P'.coeff 0 = 1
  · rw [hP'_def, Polynomial.coeff_C_mul, ← hcoeff_eq, inv_mul_cancel₀ hu_ne]
  -- Q'.coeff 0 = 1
  · rw [hQ'_def, Polynomial.coeff_C_mul, inv_mul_cancel₀ hu_ne]
  -- P'.natDegree ≤ b
  · calc P'.natDegree ≤ P₀.natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ P.natDegree := hP0_deg_le
      _ ≤ b := hP_deg
  -- Q'.natDegree ≤ a
  · calc Q'.natDegree ≤ Q₀.natDegree := Polynomial.natDegree_C_mul_le _ _
      _ ≤ Q.natDegree := hQ0_deg_le
      _ ≤ a := hQ_deg
  -- IsCoprime P' Q'
  · have hCu : IsUnit (Polynomial.C u⁻¹ : ℂ[X]) := by
      rw [Polynomial.isUnit_C]
      exact isUnit_iff_ne_zero.mpr (inv_ne_zero hu_ne)
    exact (isCoprime_mul_units_left hCu hCu P₀ Q₀).mpr hcop
  -- H * ↑Q' = ↑P'
  · have : (↑Q' : ℂ⟦X⟧) * newtonHSeries t = ↑P' := by
      simp only [hQ'_def, hP'_def, Polynomial.coe_mul, Polynomial.coe_C]
      rw [mul_assoc, hQ0H]
    rw [mul_comm] at this
    exact this

/-- If the Schur specialization vanishes outside the `(a, b)` hook,
the Newton generating series is a rational function `P / Q` with
coprime numerator/denominator of constant term 1. -/
theorem newtonH_series_rational_of_hook_vanishing {t : ℕ → ℂ} {a b : ℕ}
    (hvan : ∀ μ : YoungDiagram, ¬ IsInHook a b μ → diagramSchur μ t = 0) :
    ∃ P Q : Polynomial ℂ, P.coeff 0 = 1 ∧ Q.coeff 0 = 1 ∧
      P.natDegree ≤ b ∧ Q.natDegree ≤ a ∧ IsCoprime P Q ∧
      newtonHSeries t * (↑Q : ℂ⟦X⟧) = (↑P : ℂ⟦X⟧) := by
  -- Bridge hook vanishing to the list-form used by the recurrence extractor
  have hlist : ∀ w : List ℕ, w.SortedGE → (∀ x ∈ w, 0 < x) →
      w.length = a + 1 → b + 1 ≤ w.getD a 0 → schurDet t w = 0 := by
    intro w hw hpos hlen hlast
    set μ := YoungDiagram.ofRowLens w hw with hμ_def
    have hrows : μ.rowLens = w :=
      YoungDiagram.rowLens_ofRowLens_eq_self hpos
    have hout : ¬ IsInHook a b μ := by
      rw [not_isInHook_iff, hμ_def, rowLen_ofRowLens_getD]
      omega
    have := hvan μ hout
    rwa [diagramSchur, hrows] at this
  -- Extract the recurrence
  obtain ⟨c, hc, hrec⟩ := exists_recurrence_of_schurDet_vanishing hlist
  -- Apply the rationality theorem
  exact newtonH_series_rational c hc hrec

end RS
