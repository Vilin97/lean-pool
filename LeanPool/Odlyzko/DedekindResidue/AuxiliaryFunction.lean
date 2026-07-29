/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib

/-!
# The auxiliary test function of Belabas–Friedman

Real, `sorry`-free definitions of the auxiliary functions from Belabas–Friedman,
*Computing the residue of the Dedekind zeta function* (arXiv:1305.0035):

* `gAux s` — the function `g_s(t) = exp(-h|t|)/|t|`, `h = s - 1/2` (eq. 6);
* `auxF s X` — the test function `F_{s,X}` (eqs. 11–12).

The Fourier transform of `auxF` (Lemma 2, eq. 8) is stated and proved later.
-/

namespace DedekindResidue

@[expose] public section

open scoped Real

/-- `g_s(t) = exp(-h|t|)/|t|` with `h = s - 1/2` — Belabas–Friedman eq. (6).
(Junk value `0` at `t = 0`.) -/
noncomputable def gAux (s : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-(s - 1 / 2) * Complex.ofReal |t|) / Complex.ofReal |t|

/-- The auxiliary test function `F_{s,X}` — Belabas–Friedman eqs. (11)–(12):
`F(t) = 1` for `|t| ≤ log X`, and `F(t) = (log X / |t|)·exp(-h(|t| - log X))`
(with `h = s - 1/2`, `T = log X`) for `|t| > log X`. -/
noncomputable def auxF (s : ℂ) (X t : ℝ) : ℂ :=
  if |t| ≤ Real.log X then 1
  else Complex.ofReal (Real.log X / |t|) *
    Complex.exp (-(s - 1 / 2) * Complex.ofReal (|t| - Real.log X))

/-- `F_{s,X}` is even: `F(-t) = F(t)` — eqs. (11)–(12) depend on `t` only through `|t|`. -/
@[simp] theorem auxF_neg (s : ℂ) (X t : ℝ) : auxF s X (-t) = auxF s X t := by
  unfold auxF; rw [abs_neg]

/-- On the plateau `|t| ≤ log X`, `F_{s,X}(t) = 1` — eq. (11). -/
theorem auxF_of_le (s : ℂ) (X : ℝ) {t : ℝ} (h : |t| ≤ Real.log X) : auxF s X t = 1 := by
  unfold auxF; exact if_pos h

/-- `F_{s,X}(0) = 1` whenever `X ≥ 1` (so `log X ≥ 0`, putting `0` on the plateau). -/
theorem auxF_zero (s : ℂ) {X : ℝ} (hX : 1 ≤ X) : auxF s X 0 = 1 :=
  auxF_of_le s X (by rw [abs_zero]; exact Real.log_nonneg hX)

/-- `F_{s,X}` is measurable (in fact continuous, but measurability is all the Lemma-2
Fourier integral needs). The break locus `|t| = log X` is a measurable set. -/
theorem measurable_auxF (s : ℂ) (X : ℝ) : Measurable (auxF s X) := by
  unfold auxF
  refine Measurable.ite ?_ measurable_const ?_
  · exact measurableSet_le (by fun_prop) measurable_const
  · fun_prop

end

end DedekindResidue
