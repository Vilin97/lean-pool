/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.Tools.ComputableReal.ComputableReal
import Mathlib.Probability.Distributions.Gamma

open Real

#exit
--Casts and basic arithmetic, logic
example :
    (10 / 9 : ℝ) < (15 / 2 ⊔ 3) ∧
    |1 / 10 - (1 : ℝ)| < 1 ∧
    (if _ : 1 < 2 then 5 / 2 else 6 : ℝ) < 7 ∧
    (if [1,10].length = 2 then 5 else 10 / 7 : ℝ) / 7 < 1 ∧
    3.5 < (4 : ℝ)
    := by
  native_decide

--Checking the sign of a number
example : (2 - 5 / 2 : ℝ).sign + 1 = 0 := by
  native_decide

--Math with pi
example :
    2 < √(π + 1)
    ∧ 5 * π / √(2 + π) < 7
    ∧ (31415926 / 10000000 : ℚ) < π
    ∧ π < 31415927 / 10000000
    := by
  native_decide

--We can prove equalities if values "truncate" -- like Real.sqrt does for negative values.
example : √(1 - π) = 0 := by
  native_decide

--Evaluating the first bit of the harmonic series
example : |∑ x ∈ Finset.range 500, 1 / (x : ℝ) - 6.7908234| < 0.0000001 := by
  native_decide

--Some special functions
example :
    1 / (tanh (1/2) - (1/2)) < -26 ∧
    |4.7 - cosh (sinh (cosh 1))| < 0.02
    := by
  native_decide

--e^pi - pi: https://xkcd.com/217/
example : |exp π - π - 19.9990999| < 0.0000001 := by
  native_decide

--Below are some approximate identities from https://xkcd.com/1047/
example : |√3 - 2 * exp 1 / π| < 0.002 := by
  native_decide

example : |√5 - (2 / exp 1 + 3 / 2)| < 0.001 := by
  native_decide

--We don't get to cheat! If we try to turn up the "precision" so that it becomes
-- false, the tactic fails and informs us:
/--
error: tactic 'native_decide' evaluated that the proposition
  |√5 - (2 / rexp 1 + 3 / 2)| < 1e-4
is false
-/
#guard_msgs in
example : |√5 - (2 / exp 1 + 3 / 2)| < 0.0001 := by
  native_decide

open goldenRatio in
example :
    let proton_electron_mass_ratio := 1836.152673426;
    |proton_electron_mass_ratio - (exp 8 - 10) / φ| < 0.0004 := by
  native_decide

example : |√2 - (3/5 + π / (7 - π))| < 0.00001 := by
  native_decide

/-
If we try to use a function that isn't supported, then the error will sometimes tell us the
 relevant function, that it's noncomputable.
-/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it
depends on 'ProbabilityTheory.gammaCDFReal', and it does not have executable code
-/
#guard_msgs in
example : 0 < ProbabilityTheory.gammaCDFReal 1 1 2 := by
  native_decide

/-
Often, though, it will refer to some *other* noncomputable term. For instance, if you have
division of reals anywhere, it might complain that 'Real.instDivInvMonoid' is noncomputable,
even though `ProbabilityTheory.gammaCDFReal` is the actual culprit.

This happens because it first tries to make a `Decidable` instance using `ComputableReal`,
it fails (because there's no implementation for `ProbabilityTheory.gammaCDFReal`), and then
it falls back to `Real.decidableLT` (which is really just `Classical.propDecidable`). And
then it tries to compile the whole definition, and fails on the first noncomputable term
it hits.
-/
/--
error: failed to compile definition, consider marking it as 'noncomputable' because it depends on
'Real.instDivInvMonoid', and it does not have executable code
-/
#guard_msgs in
example : 0 < ProbabilityTheory.gammaCDFReal 1 (1 / 2) 2 := by
  native_decide

/- Operations over complex numbers: -/
example : (1 + Complex.I) * (1 - Complex.I : ℂ) = 2 := by
  native_decide

example : ‖Complex.I‖ ≠ (1 / 2) := by
  native_decide
