/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Energy
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The closed form (A.5) of the external field `V`

`∫₀^c log(t + u²) du = c log(t + c²) - 2c + 2√t arctan(c/√t)` for `t > 0`, hence
`V(t) = log(1+t) - 6α log(t+α²) - 2 + 12α + 2√t (π + arctan(1/√t) - 6 arctan(α/√t))`.
-/

public section

open Filter Topology Set MeasureTheory

namespace Zeta5Irrational

/-- Antiderivative of `u ↦ log (t + u²)`. -/
noncomputable def GVpot (t u : ℝ) : ℝ :=
  u * Real.log (t + u ^ 2) - 2 * u + 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t)

lemma hasDerivAt_GV {t : ℝ} (ht : 0 < t) (u : ℝ) :
    HasDerivAt (GVpot t) (Real.log (t + u ^ 2)) u := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hs2 : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have h1 :
    HasDerivAt (fun u : ℝ => u * Real.log (t + u ^ 2))
      (1 * Real.log (t + u ^ 2) + u * ((2 * u) / (t + u ^ 2))) u := by
    have hlog : HasDerivAt (fun u : ℝ => Real.log (t + u ^ 2)) ((2 * u) / (t + u ^ 2)) u := by
      have := ((hasDerivAt_pow 2 u).const_add t).log (by positivity)
      simpa using this
    exact (hasDerivAt_id u).mul hlog
  have h2 : HasDerivAt (fun u : ℝ => 2 * u) 2 u := by simpa using (hasDerivAt_id u).const_mul 2
  have h3 :
    HasDerivAt (fun u : ℝ => 2 * Real.sqrt t * Real.arctan (u / Real.sqrt t))
      (2 * Real.sqrt t * ((1 / (1 + (u / Real.sqrt t) ^ 2)) * (1 / Real.sqrt t))) u := by
    have := ((hasDerivAt_id u).div_const (Real.sqrt t)).arctan
    simpa using this.const_mul (2 * Real.sqrt t)
  have h := (h1.sub h2).add h3
  refine h.congr_deriv ?_
  have hne : t + u ^ 2 ≠ 0 := by positivity
  field_simp
  rw [hs2]
  ring

/-- `∫₀^c log(t + u²) du = c log(t + c²) - 2c + 2√t arctan(c/√t)` for `t > 0`. -/
lemma integral_log_add_sq {t : ℝ} (ht : 0 < t) (c : ℝ) :
    ∫ u in (0 : ℝ)..c, Real.log (t + u ^ 2) =
      c * Real.log (t + c ^ 2) - 2 * c + 2 * Real.sqrt t * Real.arctan (c / Real.sqrt t) := by
  have :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := c) (f := GVpot t) (f' :=
      fun u => Real.log (t + u ^ 2)) (fun u _ => hasDerivAt_GV ht u)
      ((Continuous.log (by fun_prop) (fun u => by positivity)).intervalIntegrable _ _)
  rw [this]
  simp [GVpot]

/-- **(A.5)**: the closed form of `V`. -/
theorem Vfield_eq {t : ℝ} (ht : 0 < t) :
    Vfield t =
      Real.log (1 + t) - 6 * (3 / 40) * Real.log (t + (3 / 40) ^ 2) - 2 + 12 * (3 / 40) +
        2 * Real.sqrt t *
          (Real.pi + Real.arctan (1 / Real.sqrt t) - 6 * Real.arctan ((3 / 40) / Real.sqrt t)) := by
  unfold Vfield
  rw [integral_log_add_sq ht, integral_log_add_sq ht]
  ring_nf

end Zeta5Irrational
