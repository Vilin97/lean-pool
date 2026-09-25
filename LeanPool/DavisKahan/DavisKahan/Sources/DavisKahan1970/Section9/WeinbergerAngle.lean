/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.WeinbergerComparison

/-!
# Davis--Kahan 1970, Section 9: the Weinberger angle half

Equation (9.8) combines two logically different ingredients:

* the Lehmann/arrowhead construction of lower eigenvalue bounds, formalized in
  `WeinbergerComparison.lean`; and
* an eigenvector-angle estimate of Weinberger type.

The second ingredient is not a consequence of an independent scalar lower
bound for the corresponding eigenvalue.  For the first Ritz vector the usual
one-sided energy split gives the familiar ratio.  For later Ritz vectors in a
cluster, the Weinberger argument retains coupled variational information from
other Ritz vectors.

This file records that boundary in executable form.  It provides the scalar
energy-splitting lemma that is sufficient for the familiar sine-square ratio,
and a rational three-dimensional counterexample showing that a scalar lower
bound for the second eigenvalue alone does not imply the same ratio for the
second Ritz vector.

The counterexample is deliberately stated as a theorem: Weinberger's coupled
hypotheses may not be replaced by the weaker scalar statement simply because
the latter has the desired type shape.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- The algebraic core of the valid Weinberger sine-square estimate.

Think of `s²` as the squared norm of the component of a unit Ritz vector above
an exterior threshold.  If the complementary component carries energy at least
`alphaCheck * (1 - s²)` and the exterior component carries energy at least
`gamma * s²`, then its Rayleigh value `alphaHat` forces the standard ratio.

For the first Ritz vector, a lower bound for the bottom eigenvalue supplies the
first energy inequality automatically.  For later vectors in a cluster that
energy inequality is extra coupled information; a scalar lower bound for the
corresponding eigenvalue does not supply it. -/
theorem weinberger_sine_sq_le_of_coupled_energy
    {s alphaCheck alphaHat gamma lowEnergy highEnergy : ℝ}
    (hgap : alphaCheck < gamma)
    (hsplit : alphaHat = lowEnergy + highEnergy)
    (hlow : alphaCheck * (1 - s ^ 2) ≤ lowEnergy)
    (hhigh : gamma * s ^ 2 ≤ highEnergy) :
    s ^ 2 ≤ (alphaHat - alphaCheck) / (gamma - alphaCheck) := by
  have hden : 0 < gamma - alphaCheck := by linarith
  apply (le_div_iff₀ hden).2
  nlinarith

/-- A machine-checked counterexample to the false inference

`scalar lower bound for lambda_2  =>  Weinberger's second-vector angle ratio`.

The conjuncts encode an exact three-dimensional Ritz problem for
`diag(0, 10, 100)`:

* `w₁ = (18/35, -6/7, 1/35)` and `w₂ = (3/7, 2/7, 6/7)` are unit and orthogonal;
* they are also orthogonal for the quadratic form of `diag(0,10,100)`, hence
  diagonalize its compression to their two-dimensional trial space;
* their Ritz values are `52/7` and `520/7`;
* `10` is the exact second eigenvalue and `99` is a valid lower threshold below
  the third eigenvalue `100`;
* nevertheless the squared component of `w₂` above the first two coordinate
  directions is `36/49`, strictly larger than
  `(520/7 - 10) / (99 - 10) = 450/623`.

Thus the second-vector angle estimate needs Weinberger's coupled variational
information; the scalar lower-eigenvalue fact by itself is insufficient. -/
theorem secondScalarLowerBound_angleBound_counterexample :
    (((18 : ℝ) / 35) ^ 2 + ((-6 : ℝ) / 7) ^ 2 + ((1 : ℝ) / 35) ^ 2 = 1) ∧
    (((3 : ℝ) / 7) ^ 2 + ((2 : ℝ) / 7) ^ 2 + ((6 : ℝ) / 7) ^ 2 = 1) ∧
    ((18 : ℝ) / 35 * ((3 : ℝ) / 7)
      + ((-6 : ℝ) / 7) * ((2 : ℝ) / 7)
      + ((1 : ℝ) / 35) * ((6 : ℝ) / 7) = 0) ∧
    ((10 : ℝ) * ((-6 : ℝ) / 7) * ((2 : ℝ) / 7)
      + 100 * ((1 : ℝ) / 35) * ((6 : ℝ) / 7) = 0) ∧
    ((10 : ℝ) * ((-6 : ℝ) / 7) ^ 2
      + 100 * ((1 : ℝ) / 35) ^ 2 = 52 / 7) ∧
    ((10 : ℝ) * ((2 : ℝ) / 7) ^ 2
      + 100 * ((6 : ℝ) / 7) ^ 2 = 520 / 7) ∧
    ((52 : ℝ) / 7 < 520 / 7) ∧
    ((520 : ℝ) / 7 < 99) ∧
    ((10 : ℝ) ≤ 10) ∧
    ((99 : ℝ) ≤ 100) ∧
    ¬ (((6 : ℝ) / 7) ^ 2 ≤
      (((520 : ℝ) / 7) - 10) / (99 - 10)) := by
  norm_num

end Section9
end DavisKahan1970
end TauCeti
