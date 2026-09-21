/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.NumericalBounds
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.SchurComplement
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SphericalPythagoras

/-!
# Davis--Kahan 1970, Section 9: individual eigenvectors inside a cluster

This module isolates the scalar geometry used after the Schur-complement
reduction.  The exact coefficient `sqrt 7 / 10` is the Euclidean combination
of half of the `tan(2 psi)` coefficient and the complementary-coordinate
`tangent` coefficient.

The Pythagorean combination `omega ^ 2 ≤ psi ^ 2 + eta ^ 2` is **not** assumed
here.  It is derived, through `TauCeti.sq_le_sq_add_sq_of_cos_eq_cos_mul_cos`,
from the exact spherical right-triangle identity `cos omega = cos psi * cos eta`
that holds because the in-plane vector `e_k` is orthogonal to the out-of-plane
component of the eigenvector `f_k`.  Likewise the two angle bounds are derived
from the corresponding tangent bounds rather than assumed: on the branch
`0 ≤ psi < pi / 4` selected by the Schur-complement rotation one has
`psi ≤ tan (2 psi) / 2`, and on `0 ≤ eta < pi / 2` one has `eta ≤ tan eta`.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

/-- Coefficient multiplying the Schur-complement `tan(2 psi)` bound after the
factor one half. -/
noncomputable def halfTanTwoPsiCoefficient : ℝ := Real.sqrt 3 / 30

/-- Coefficient multiplying the complementary-coordinate tangent bound. -/
noncomputable def tanEtaCoefficient : ℝ := Real.sqrt 15 / 15

/-- The squared combined coefficient of the individual-angle decomposition. -/
lemma combined_individual_coefficient_sq :
    halfTanTwoPsiCoefficient ^ 2 + tanEtaCoefficient ^ 2 = (7 : ℝ) / 100 := by
  have h3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h15 : Real.sqrt (15 : ℝ) ^ 2 = 15 := Real.sq_sqrt (by norm_num)
  unfold halfTanTwoPsiCoefficient tanEtaCoefficient
  nlinarith

/-- The combined coefficient itself, the nonnegative square root of the previous. -/
lemma combined_individual_coefficient :
    Real.sqrt (halfTanTwoPsiCoefficient ^ 2 + tanEtaCoefficient ^ 2) =
      Real.sqrt 7 / 10 := by
  -- rewrite the radicand as an explicit square and cancel, rather than asking
  -- `nlinarith` to match two square roots
  rw [combined_individual_coefficient_sq,
    show (7 : ℝ) / 100 = (Real.sqrt 7 / 10) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7)]; norm_num,
    Real.sqrt_sq (by positivity)]

/-- Abstract form of the final combination: if the squared target angle is
bounded by the squared in-plane and out-of-plane contributions, then a common
positive denominator yields the `sqrt 7 / 10` envelope. -/
theorem individual_angle_le_exact_envelope
    {omega psi eta ε denominator : ℝ}
    (_homega0 : 0 ≤ omega)
    (hpsi0 : 0 ≤ psi) (heta0 : 0 ≤ eta)
    (hden : 0 < denominator)
    (homega : omega ^ 2 ≤ psi ^ 2 + eta ^ 2)
    (hpsi : psi ≤ halfTanTwoPsiCoefficient * ε / denominator)
    (heta : eta ≤ tanEtaCoefficient * ε / denominator)
    (hε : 0 ≤ ε) :
    omega ≤ (Real.sqrt 7 / 10) * ε / denominator := by
  have hp0 : 0 ≤ halfTanTwoPsiCoefficient := by
    unfold halfTanTwoPsiCoefficient
    positivity
  have he0 : 0 ≤ tanEtaCoefficient := by
    unfold tanEtaCoefficient
    positivity
  have hpsq : psi ^ 2 ≤
      (halfTanTwoPsiCoefficient * ε / denominator) ^ 2 := by
    nlinarith
  have hetasq : eta ^ 2 ≤
      (tanEtaCoefficient * ε / denominator) ^ 2 := by
    nlinarith
  have hcoeff := combined_individual_coefficient_sq
  have htargetsq : omega ^ 2 ≤
      ((Real.sqrt 7 / 10) * ε / denominator) ^ 2 := by
    calc
      omega ^ 2 ≤ psi ^ 2 + eta ^ 2 := homega
      _ ≤ (halfTanTwoPsiCoefficient * ε / denominator) ^ 2 +
          (tanEtaCoefficient * ε / denominator) ^ 2 := add_le_add hpsq hetasq
      _ = ((Real.sqrt 7 / 10) * ε / denominator) ^ 2 := by
        have h7 : Real.sqrt (7 : ℝ) ^ 2 = 7 := Real.sq_sqrt (by norm_num)
        field_simp [ne_of_gt hden]
        nlinarith
  have hright0 : 0 ≤ (Real.sqrt 7 / 10) * ε / denominator := by positivity
  nlinarith

/-! ## The two angles are controlled by their tangents

Both estimates that Section 9 produces are tangent estimates: the
Schur-complement rotation is delivered as `tan (2 psi)`, and the
complementary-coordinate bound as `tan eta`.  On the branches the eigenvalue
ordering selects, each angle is below the corresponding tangent expression, so
no angle bound has to be assumed. -/

/-- On the branch `0 ≤ psi < pi / 4` the angle is at most half the tangent of
its double.  This is the branch the Schur-complement rotation lives on: the
correction is purely off-diagonal, so the rotation angle never reaches
`pi / 4`. -/
theorem angle_le_half_tan_two_angle {psi : ℝ} (h0 : 0 ≤ psi)
    (h4 : psi < Real.pi / 4) :
    psi ≤ Real.tan (2 * psi) / 2 := by
  have h : 2 * psi ≤ Real.tan (2 * psi) :=
    Real.le_tan (by linarith) (by linarith)
  linarith

/-- On `[0, pi / 2)` an angle is at most its own tangent. -/
theorem angle_le_tan {eta : ℝ} (h0 : 0 ≤ eta) (h2 : eta < Real.pi / 2) :
    eta ≤ Real.tan eta := Real.le_tan h0 h2

/-! ### The in-plane angle read off from two orthonormal coordinates

The Schur-complement rotation is presented by the pair of coordinates of a unit
vector against an orthonormal pair: if the vector has coordinates `p` and `q`
then the angle it makes with the first basis vector has cosine
`p / sqrt (p ^ 2 + q ^ 2)`.  The two facts the reduction needs are that the
angle stays below `pi / 4` exactly when `q < p`, and that half the tangent of
its double is the elementary expression `p q / (p ^ 2 - q ^ 2)`. -/

/-- The angle whose cosine is `p / sqrt (p ^ 2 + q ^ 2)` is below `pi / 4`
precisely because the first coordinate dominates. -/
theorem arccos_ratio_lt_pi_div_four {p q : ℝ} (hq : 0 ≤ q) (hqp : q < p) :
    Real.arccos (p / Real.sqrt (p ^ 2 + q ^ 2)) < Real.pi / 4 := by
  have hp : 0 < p := lt_of_le_of_lt hq hqp
  have hs : 0 < Real.sqrt (p ^ 2 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (p ^ 2 + q ^ 2) ^ 2 = p ^ 2 + q ^ 2 :=
    Real.sq_sqrt (by positivity)
  have hkey : Real.sqrt 2 / 2 < p / Real.sqrt (p ^ 2 + q ^ 2) := by
    rw [div_lt_div_iff₀ (by norm_num) hs]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith [Real.sqrt_nonneg 2, hs.le, hsq,
      sq_nonneg (Real.sqrt 2 * Real.sqrt (p ^ 2 + q ^ 2) - 2 * p)]
  have hle : p / Real.sqrt (p ^ 2 + q ^ 2) ≤ 1 := by
    rw [div_le_one hs]
    nlinarith [hsq, Real.sqrt_nonneg (p ^ 2 + q ^ 2)]
  have h4 : Real.arccos (Real.sqrt 2 / 2) = Real.pi / 4 := by
    rw [← Real.cos_pi_div_four, Real.arccos_cos (by positivity) (by linarith [Real.pi_pos])]
  rw [← h4]
  exact Real.arccos_lt_arccos (by nlinarith [Real.sqrt_nonneg 2]) hkey hle

/-- Half the tangent of the doubled angle, in the two coordinates.  This is the
exact `tan (2 psi) / 2` the Schur-complement reduction has to bound. -/
theorem half_tan_two_arccos_ratio {p q : ℝ} (hq : 0 ≤ q) (hqp : q < p) :
    Real.tan (2 * Real.arccos (p / Real.sqrt (p ^ 2 + q ^ 2))) / 2
      = p * q / (p ^ 2 - q ^ 2) := by
  have hp : 0 < p := lt_of_le_of_lt hq hqp
  have hs : 0 < Real.sqrt (p ^ 2 + q ^ 2) := Real.sqrt_pos.2 (by positivity)
  have hsq : Real.sqrt (p ^ 2 + q ^ 2) ^ 2 = p ^ 2 + q ^ 2 :=
    Real.sq_sqrt (by positivity)
  have htan : Real.tan (Real.arccos (p / Real.sqrt (p ^ 2 + q ^ 2))) = q / p := by
    rw [Real.tan_arccos]
    have h1 : 1 - (p / Real.sqrt (p ^ 2 + q ^ 2)) ^ 2
        = (q / Real.sqrt (p ^ 2 + q ^ 2)) ^ 2 := by
      field_simp
      nlinarith [hsq]
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp
  rw [Real.tan_two_mul, htan]
  have hne : p ^ 2 - q ^ 2 ≠ 0 := by nlinarith
  field_simp

/-- **The individual-eigenvector envelope, from the spherical identity and the
two tangent estimates.**

Nothing about the target angle `omega` is assumed beyond its range and the
*exact* spherical right-triangle identity `cos omega = cos psi * cos eta`; the
Pythagorean combination is derived.  The two quantitative inputs are the
tangent estimates the Schur-complement reduction and the complementary
coordinate actually produce. -/
theorem individual_angle_le_exact_envelope_of_tangents
    {omega psi eta ε denominator : ℝ}
    (homega0 : 0 ≤ omega) (homegapi : omega ≤ Real.pi)
    (hpsi0 : 0 ≤ psi) (hpsi4 : psi < Real.pi / 4)
    (heta0 : 0 ≤ eta) (heta2 : eta < Real.pi / 2)
    (hcos : Real.cos omega = Real.cos psi * Real.cos eta)
    (hden : 0 < denominator)
    (htanpsi : Real.tan (2 * psi) / 2 ≤
      halfTanTwoPsiCoefficient * ε / denominator)
    (htaneta : Real.tan eta ≤ tanEtaCoefficient * ε / denominator)
    (hε : 0 ≤ ε) :
    omega ≤ (Real.sqrt 7 / 10) * ε / denominator := by
  have hpi := Real.pi_pos
  have hpsi : psi ≤ halfTanTwoPsiCoefficient * ε / denominator :=
    (angle_le_half_tan_two_angle hpsi0 hpsi4).trans htanpsi
  have heta : eta ≤ tanEtaCoefficient * ε / denominator :=
    (angle_le_tan heta0 heta2).trans htaneta
  have hsq : omega ^ 2 ≤ psi ^ 2 + eta ^ 2 :=
    sq_le_sq_add_sq_of_cos_eq_cos_mul_cos homega0 homegapi hpsi0
      (by linarith) heta0 heta2.le hcos
  exact individual_angle_le_exact_envelope homega0 hpsi0 heta0 hden hsq hpsi heta hε

/-- **The same envelope, with the spherical identity itself discharged.**

Here `e` is the Ritz vector, `f` the exact eigenvector, `K` the trial subspace
and `g` the direction inside `K` that `f` points to.  The angle `omega` between
`e` and `f`, the out-of-plane angle `eta` between `f` and `K`, and the in-plane
angle `psi` between `e` and `g` are the `arccos` of the corresponding line
cosines, and the identity relating them is proved, not assumed. -/
theorem individual_angle_le_exact_envelope_of_subspace
    {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] {e f g : E}
    (he : e ∈ K) (hen : ‖e‖ = 1) (hfn : ‖f‖ = 1)
    (hPf : K.starProjection f ≠ 0)
    (hg : g = ((‖K.starProjection f‖ : ℝ) : 𝕜)⁻¹ • K.starProjection f)
    {ε denominator : ℝ} (hden : 0 < denominator) (hε : 0 ≤ ε)
    (hpsi4 : Real.arccos ‖inner 𝕜 e g‖ < Real.pi / 4)
    (htanpsi : Real.tan (2 * Real.arccos ‖inner 𝕜 e g‖) / 2 ≤
      halfTanTwoPsiCoefficient * ε / denominator)
    (htaneta : Real.tan (Real.arccos ‖K.starProjection f‖) ≤
      tanEtaCoefficient * ε / denominator) :
    Real.arccos ‖inner 𝕜 e f‖ ≤ (Real.sqrt 7 / 10) * ε / denominator := by
  subst hg
  have heta2 : Real.arccos ‖K.starProjection f‖ < Real.pi / 2 := by
    refine lt_of_le_of_ne (Real.arccos_le_pi_div_two.2 (norm_nonneg _)) ?_
    intro hcontra
    exact hPf (norm_eq_zero.1 (Real.arccos_eq_pi_div_two.1 hcontra))
  exact individual_angle_le_exact_envelope_of_tangents (Real.arccos_nonneg _)
    (Real.arccos_le_pi _) (Real.arccos_nonneg _) hpsi4 (Real.arccos_nonneg _)
    heta2 ((TauCeti.Submodule.cos_lineAngle_eq_mul K he hen hfn hPf).trans
      (mul_comm _ _)) hden htanpsi htaneta hε

end Section9
end DavisKahan1970
end TauCeti
