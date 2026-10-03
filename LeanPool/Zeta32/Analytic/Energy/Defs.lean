/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.FstarDefs

/-! Definitions for the energy estimate of the proof notes, §5.3 (layout (4,5,3), c = 3).

* `potD ρ a x = ∫_{-a}^{a} log|x - t| ρ(t) dt` and `ID ρ a = ∫ potD ρ a · ρ` (logarithmic
potential and energy of a
  density on `[-a, a]`), `potA a = potD (rhoA a) a`, `IA a = ID (rhoA a) a` for the closed form
  `rhoA` of FstarDefs;
* the c-components of the proof notes (8′): `rhoC a c t = c√(a²-t²)/(2π u_c (t²+c²))`, `u_c =
√(c²+a²)`, the weight
  `gtil = (1/3, 5/3, 4/3)` on `(0,1), [1,5), [5,∞)`, and the constants `kC a c`, `wC c x` with
  `2 L_c = kC + wC` on the support. -/

public section

open Real MeasureTheory

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- Logarithmic potential of a density `ρ` supported on `[-a, a]`. -/
@[expose]
def potD (ρ : ℝ → ℝ) (a x : ℝ) : ℝ := ∫ t in (-a)..a, Real.log |x - t| * ρ t

/-- Logarithmic energy of a density `ρ` supported on `[-a, a]`. -/
@[expose]
def ID (ρ : ℝ → ℝ) (a : ℝ) : ℝ := ∫ x in (-a)..a, potD ρ a x * ρ x

/-- Potential of the comparison density `rhoA a`. -/
@[expose]
def potA (a x : ℝ) : ℝ := potD (rhoA a) a x

/-- Energy of the comparison density `rhoA a`. -/
@[expose]
def IA (a : ℝ) : ℝ := ID (rhoA a) a

/-- The weight `g` of the proof notes (8′) for layout (4,5,3). -/
@[expose]
def gtil (c : ℝ) : ℝ := if c < 1 then 1/3 else if c < 5 then 5/3 else 4/3

/-- `u_c = √(c² + a²)`. -/
@[expose]
def uC (a c : ℝ) : ℝ := √(c^2 + a^2)

/-- The component density `ρ_c` of GLOBAL-INTEGRAL-v1 (9). -/
@[expose]
def rhoC (a c t : ℝ) : ℝ := c * √(a^2 - t^2) / (2 * π * uC a c * (t^2 + c^2))

/-- Potential of the component `ρ_c`. -/
@[expose]
def potC (a c x : ℝ) : ℝ := ∫ t in (-a)..a, Real.log |x - t| * rhoC a c t

/-- Value of `2 L_c − wC c` on the support. -/
@[expose]
def kC (a c : ℝ) : ℝ := Real.log (a * c / (uC a c + c)) - c / uC a c * Real.log (a / 2)

/-- `w_c(x) = ½ log(1 + x²/c²)`, so that `W = ∫ g w_c dc`. -/
@[expose]
def wC (c x : ℝ) : ℝ := Real.log (1 + x^2 / c^2) / 2

end
end Zeta32.Analytic.EnergyI

end
