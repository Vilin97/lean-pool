/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Envelope.HookConfinement
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.SquareGrowthSharp
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.Package

/-!
# Sharp hook confinement

Hook confinement with the displayed constant of the accompanying
paper, and with the threshold quantified as the appendix states it:
relative to the assembled Schur package, *every* side `s > 2e√A`
confines, not merely some side.

`HookConfinement.lean` proves the existential form over an arbitrary
package. The constant here comes from the block dimensions of the
assembled package, through `square_growth_sharp`.
-/

namespace RS

universe u

/-- The assembled package's dimension field is the native block
dimension of the chosen simple submodule. -/
theorem schurPackage_dim (μ : YoungDiagram) :
    (schurPackage.{u}).dim μ = nDim (jtSimple μ) := rfl

namespace PermTower

variable {E : ℕ → Type u}

/-- **Sharp square death**: in a tower of growth `A`, the square of
any side `s > 2e√A` is dead relative to the assembled package.  Its
block dimension exceeds `√A ^ (s²)` by `square_growth_sharp`, so the
square of that dimension exceeds `A ^ (s²)`, which is what
`not_alive_square` asks for. -/
theorem not_alive_square_sharp [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    [∀ n, Module.Finite ℂ (E n)]
    (T : PermTower E A) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A < s) :
    ¬ T.Alive schurPackage.{u} (squareDiagram s) := by
  refine T.not_alive_square schurPackage.{u} ?_
  have hgrow := square_growth_sharp (Real.sqrt A) (Real.sqrt_nonneg A) s hs
    (jtSimple (squareDiagram s)) (jtSimple_char (squareDiagram s))
  have hAeq : (Real.sqrt A ^ (s ^ 2)) ^ 2 = A ^ (s ^ 2) := by
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt T.growth_nonneg]
  rw [schurPackage_dim, ← hAeq]
  exact pow_lt_pow_left₀ hgrow (pow_nonneg (Real.sqrt_nonneg A) _) two_ne_zero

/-- **Sharp hook confinement**: in a tower of growth `A`, every alive
shape lies in the `(s − 1, s − 1)` hook, for *every* side
`s > 2e√A`. -/
theorem hook_confinement_sharp [∀ n, Ring (E n)] [∀ n, Algebra ℂ (E n)] {A : ℝ}
    [∀ n, Module.Finite ℂ (E n)]
    (T : PermTower E A) {s : ℕ}
    (hs : 2 * Real.exp 1 * Real.sqrt A < s) :
    ∀ μ : YoungDiagram, T.Alive schurPackage.{u} μ →
      IsInHook (s - 1) (s - 1) μ := by
  intro μ halive
  by_contra hout
  rw [not_isInHook_iff] at hout
  have hsq : squareDiagram s ≤ μ := squareDiagram_le_of_rowLen (by omega)
  exact T.not_alive_of_le _ hsq (T.not_alive_square_sharp hs) halive

end PermTower

end RS
