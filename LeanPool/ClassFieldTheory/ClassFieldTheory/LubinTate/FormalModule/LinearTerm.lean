/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Substitution
/-!
# Prescribed linear terms for multivariable power series

A multivariable power series has a prescribed linear term when its difference
from the corresponding linear form has total order at least two.
-/

@[expose] public section

noncomputable section

namespace LubinTate
namespace SameUniformizer

variable {R : Type*} [CommRing R]
variable {σ : Type*} [Fintype σ]

/-- The multivariable linear form `sum_i L_i X_i`. -/
noncomputable def linearForm (L : σ → R) : MvPowerSeries σ R :=
  ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i

/-- States the theorem `constantCoeff_linearForm`. -/
@[simp]
theorem constantCoeff_linearForm (L : σ → R) :
    MvPowerSeries.constantCoeff (linearForm L) = 0 := by
  simp [linearForm]

/-- A series has prescribed linear term `L` when its difference from
`sum_i L_i X_i` has total order at least two. -/
def HasLinearTerm (H : MvPowerSeries σ R) (L : σ → R) : Prop :=
  (2 : ℕ∞) ≤ (H - linearForm L).order

namespace HasLinearTerm

variable {H : MvPowerSeries σ R} {L : σ → R}

/-- A series with a prescribed linear term has zero constant
coefficient. -/
theorem constantCoeff_eq_zero (h : HasLinearTerm H L) :
    MvPowerSeries.constantCoeff H = 0 := by
  have horder : (1 : ℕ∞) ≤ (H - linearForm L).order :=
    (by norm_num : (1 : ℕ∞) ≤ 2).trans h
  have hconstant :=
    MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp horder
  simpa using hconstant

/-- Consequently the series can genuinely be substituted into a
one-variable power series. -/
theorem hasSubst (h : HasLinearTerm H L) :
    PowerSeries.HasSubst H :=
  PowerSeries.HasSubst.of_constantCoeff_zero h.constantCoeff_eq_zero

end HasLinearTerm

end SameUniformizer
end LubinTate

end
