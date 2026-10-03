/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Shared definitions for the analytic constant F* of layout (4,5,3) (the proof notes, 5.3 (8′),
the proof notes, 5.4). Mathlib only. `FstarPoints` implies `FstarInput`, which the
energy bound uses. -/

public section

namespace Zeta32
noncomputable section

/-- `W(x) = (2/3)(πx − 2(x·atan(1/x) + log(1+x²)/2) + (x·atan(5/x) + 5·log(1+x²/25)/2)/2)`. -/
@[expose]
def Wt (x : ℝ) : ℝ :=
  (2/3) * (Real.pi * x - 2 * (x * Real.arctan (1/x) + Real.log (1 + x^2) / 2)
    + (x * Real.arctan (5/x) + 5 * Real.log (1 + x^2/25) / 2) / 2)

/-- `G(c,x) = log((√(c²+a²) + √(a²−x²)) / (√(c²+a²) − √(a²−x²)))`. -/
@[expose]
def Gfun (a c x : ℝ) : ℝ :=
  Real.log ((Real.sqrt (c^2 + a^2) + Real.sqrt (a^2 - x^2)) / (Real.sqrt (c^2 + a^2) - Real.sqrt
    (a^2 - x^2)))

/-- `ρ_a(x)`, g = (1/3, 5/3, 4/3) on (0,1), [1,5), [5,∞). -/
@[expose]
def rhoA (a x : ℝ) : ℝ :=
  ((1/3) * (Gfun a 0 x - Gfun a 1 x) + (5/3) * (Gfun a 1 x - Gfun a 5 x) + (4/3) * Gfun a 5 x) /
    (4 * Real.pi)

/-- Total mass of `ρ_a`. -/
@[expose]
def massA (a : ℝ) : ℝ :=
  ((1/3) * (1 - (Real.sqrt (1 + a^2) - a)) + (5/3) * (4 - (Real.sqrt (25 + a^2) - Real.sqrt (1 +
    a^2)))
    + (4/3) * (Real.sqrt (25 + a^2) - 5)) / 2

/-- `J(c) = −c·log(2c/(c+√(c²+a²))) − (√(c²+a²) − c)`; `J(0) = −a` for `a > 0`. -/
@[expose]
def Jfun (a c : ℝ) : ℝ :=
  -c * Real.log (2*c / (c + Real.sqrt (c^2 + a^2))) - (Real.sqrt (c^2 + a^2) - c)

/-- `ℓ(a)`, the closed form (16) of GLOBAL-INTEGRAL-v1 for this layout. -/
@[expose]
def ellA (a : ℝ) : ℝ :=
  2 * Real.log (a/2) + (1/3) * (Jfun a 0 - Jfun a 1) + (5/3) * (Jfun a 1 - Jfun a 5) + (4/3) *
    Jfun a 5

/-- The analytic constant is at most −6 at the root of the mass equation. -/
@[expose]
def FstarInput : Prop :=
  ∀ a : ℝ, 0 < a → massA a = 1 →
    9 * (3/2 - Real.log 3) + (9/2) * (ellA a - 2 * ∫ x in (0:ℝ)..a, Wt x * rhoA a x) ≤ -6

/-- Rational lower endpoint for the equilibrium-support parameter. -/
@[expose]
def aMinus : ℝ := 93331/50000
/-- Rational upper endpoint for the equilibrium-support parameter. -/
@[expose]
def aPlus : ℝ := 186663/100000
/-- `x_k = a₋·k/16`. -/
@[expose]
def xk (k : ℕ) : ℝ := aMinus * k / 16
/-- Certified rational lower bounds for the potential weight at the fifteen test points. -/
@[expose]
def Wlow : Fin 15 → ℚ := ![(17/250 : ℚ), (153/1000 : ℚ), (127/500 : ℚ), (369/1000 : ℚ),
  (499/1000 : ℚ), (641/1000 : ℚ), (397/500 : ℚ), (239/250 : ℚ), (141/125 : ℚ), (1307/1000 : ℚ),
  (1493/1000 : ℚ), (421/250 : ℚ), (1881/1000 : ℚ), (2083/1000 : ℚ), (286/125 : ℚ)]
/-- Certified rational lower bounds for the auxiliary ratio at the fifteen test points. -/
@[expose]
def Rlow : Fin 15 → ℚ := ![(223/500 : ℚ), (203/500 : ℚ), (377/1000 : ℚ), (44/125 : ℚ), (329/1000
  : ℚ), (153/500 : ℚ), (283/1000 : ℚ), (13/50 : ℚ), (119/500 : ℚ), (43/200 : ℚ), (191/1000 : ℚ),
  (167/1000 : ℚ), (71/500 : ℚ), (113/1000 : ℚ), (39/500 : ℚ)]

/-- Finitely many rational checks. Index `k : Fin 15` stands for the point `x_(k+1)`. -/
@[expose]
def FstarPoints : Prop :=
  massA aMinus < 1 ∧ 1 < massA aPlus ∧
  (∀ a ∈ Set.Icc aMinus aPlus, ellA a ≤ -159/100) ∧
  (549/500 : ℝ) < Real.log 3 ∧
  ∀ k : Fin 15, ((Wlow k : ℚ) : ℝ) ≤ Wt (xk (k.val + 1)) ∧ ((Rlow k : ℚ) : ℝ) ≤ rhoA aMinus (xk
    (k.val + 1))

end
end Zeta32
