/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Assembly

/-! Energy estimate and logarithmic asymptotic (§5.3 of the proof notes).

The result is stated in exponential form, `|Q_n(C_r)| ≤ exp((−6 + ε) n²)`: a logarithmic form
would, with
Lean's convention `Real.log 0 = 0`, silently assert that `Q_n(C_r) ≠ 0`, which the energy
method does not give.
`energy_bound_of_inputs_log` gives the logarithmic form wherever the value is nonzero.

Module map (Zeta32/Analytic/Energy/): Pointwise, Stirling, LogNorm, Scaling — (5′), (6′);
PoissonKernel, Component,
Poisson, CIntegrals, Regularity, Potential — (8′), (11′), (15′) and the identification with
`rhoA`, `Wt`, `ellA`,
`massA` of FstarDefs; ZeroMass, CircleTools, Discrete — (12), (13′); Assembly — (14′) and the
constant. -/

public section

open Filter Polynomial

namespace Zeta32.Analytic

theorem energy_bound_of_inputs : ∀ r : ℚ, (∀ n, HeineBound r n) → FstarInput →
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      |Polynomial.aeval (Cr r) (Qtilde r n)| ≤ Real.exp ((-6 + ε) * (n:ℝ)^2) :=
  fun r hH hF ε hε => EnergyI.energy_bound_exp r hH hF ε hε

theorem energy_bound_of_inputs_log : ∀ r : ℚ, (∀ n, HeineBound r n) → FstarInput →
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Polynomial.aeval (Cr r) (Qtilde r n) ≠ 0 →
      Real.log |Polynomial.aeval (Cr r) (Qtilde r n)| ≤ (-6 + ε) * (n:ℝ)^2 := by
  intro r hH hF ε hε
  filter_upwards [energy_bound_of_inputs r hH hF ε hε] with n hn hne
  rw [← Real.log_exp ((-6 + ε) * (n:ℝ)^2)]
  exact Real.log_le_log (abs_pos.mpr hne) hn

end Zeta32.Analytic

end
