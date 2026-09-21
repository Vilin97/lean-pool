/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.Operator.PartialSylvesterBoundedInverse

/-!
# Davis--Kahan 1970, Theorem 5.1, on a Banach space

Theorem 5.1 is the Sylvester estimate the paper states without a Hilbert
structure: `A X - X B = R` with `A` bounded below on one side and `B` above on
the other, in any norm on cross-space operators that contractions cannot
increase.

`CompatibleCrossOperatorNorm` is that norm class, transcribed from the paper's
own compatibility axiom, and the five theorems below are the printed statement
and its four printed variants: the exact form, the interchanged form the paper
obtains from the symmetry of `A` and `B`, its exact companion, and the
unbounded-`A` form the paper's remark asserts its proof already covers.
-/

open scoped InnerProductSpace
open Set

namespace TauCeti
namespace DavisKahan1970

universe u v

section BanachSylvester

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type u} {Y : Type v}
  [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A norm on cross-space bounded operators compatible with contractions on
both sides, as required in Davis--Kahan Theorem 5.1. -/
structure CompatibleCrossOperatorNorm where
  /-- The compatible real-valued norm on operators between the two Hilbert spaces. -/
  toFun : (X →L[𝕜] Y) → ℝ
  nonneg : ∀ T, 0 ≤ toFun T
  eq_zero : ∀ T, toFun T = 0 → T = 0
  smul : ∀ c : 𝕜, ∀ T, toFun (c • T) = ‖c‖ * toFun T
  triangle : ∀ S T, toFun (S + T) ≤ toFun S + toFun T
  compatible : ∀ (L : Y →L[𝕜] Y) (T : X →L[𝕜] Y)
    (R : X →L[𝕜] X), ‖L‖ ≤ 1 → ‖R‖ ≤ 1 →
      toFun (L ∘L T ∘L R) ≤ toFun T

/-- The residual surface subspace is orthogonally complemented. -/
instance : CoeFun (CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (fun _ => (X →L[𝕜] Y) → ℝ) :=
  ⟨CompatibleCrossOperatorNorm.toFun⟩

/-- An explicit bounded left inverse of `A` with a reciprocal norm bound.  On a
general Banach space a lower bound on `A` does not furnish a bounded projection
onto the (possibly non-complemented) range, so the reusable datum is the left
inverse itself; on a Hilbert space the spectral-separation lower bound supplies
it through the closed-range orthogonal projection. -/
structure BoundedLeftInverseData (A : Y →L[𝕜] Y) (c : ℝ) where
  /-- The bounded left inverse with the specified operator-norm bound. -/
  leftInverse : Y →L[𝕜] Y
  comp_eq_id : leftInverse ∘L A = ContinuousLinearMap.id 𝕜 Y
  norm_le : ‖leftInverse‖ ≤ c

/-- An explicit bounded right inverse with a reciprocal norm bound, used by the
source's symmetric form of Theorem 5.1. -/
structure BoundedRightInverseData (B : X →L[𝕜] X) (c : ℝ) where
  /-- The bounded right inverse with the specified operator-norm bound. -/
  rightInverse : X →L[𝕜] X
  comp_eq_id : B ∘L rightInverse = ContinuousLinearMap.id 𝕜 X
  norm_le : ‖rightInverse‖ ≤ c

namespace CompatibleCrossOperatorNorm

/-- The compatible norm vanishes at the zero operator. -/
theorem map_zero (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y)) :
    N (0 : X →L[𝕜] Y) = 0 := by
  have h := N.smul 0 (0 : X →L[𝕜] Y)
  simpa using h

/-- Full two-sided ideal estimate obtained by normalizing the multipliers. -/
theorem comp_le_mul (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (L : Y →L[𝕜] Y) (T : X →L[𝕜] Y) (R : X →L[𝕜] X) :
    N (L ∘L T ∘L R) ≤ ‖L‖ * N T * ‖R‖ := by
  by_cases hL : L = 0
  · subst L; simp [map_zero N]
  by_cases hR : R = 0
  · subst R; simp [map_zero N]
  let Ln : Y →L[𝕜] Y := (‖L‖ : 𝕜)⁻¹ • L
  let Rn : X →L[𝕜] X := (‖R‖ : 𝕜)⁻¹ • R
  have hLnorm : ‖L‖ ≠ 0 := norm_ne_zero_iff.mpr hL
  have hRnorm : ‖R‖ ≠ 0 := norm_ne_zero_iff.mpr hR
  have hLscalar : (‖L‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hLnorm
  have hRscalar : (‖R‖ : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hRnorm
  have hLn : ‖Ln‖ ≤ 1 := by
    change ‖(‖L‖ : 𝕜)⁻¹ • L‖ ≤ 1
    rw [norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg L), inv_mul_cancel₀ hLnorm]
  have hRn : ‖Rn‖ ≤ 1 := by
    change ‖(‖R‖ : 𝕜)⁻¹ • R‖ ≤ 1
    rw [norm_smul, norm_inv, RCLike.norm_ofReal,
      abs_of_nonneg (norm_nonneg R), inv_mul_cancel₀ hRnorm]
  have hcompat := N.compatible Ln T Rn hLn hRn
  have hfactor :
      L ∘L T ∘L R = ((‖L‖ * ‖R‖ : ℝ) : 𝕜) • (Ln ∘L T ∘L Rn) := by
    ext x
    simp only [Ln, Rn, ContinuousLinearMap.comp_apply, smul_apply,
      map_smul, smul_smul, RCLike.ofReal_mul]
    rw [show ((‖L‖ : 𝕜) * (‖R‖ : 𝕜)) * ((‖R‖ : 𝕜)⁻¹ * (‖L‖ : 𝕜)⁻¹) = 1 from by
      field_simp, one_smul]
  rw [hfactor, N.smul]
  calc
    ‖((‖L‖ * ‖R‖ : ℝ) : 𝕜)‖ * N (Ln ∘L T ∘L Rn)
        ≤ (‖L‖ * ‖R‖) * N T := by
          simpa using mul_le_mul_of_nonneg_left hcompat
            (mul_nonneg (norm_nonneg L) (norm_nonneg R))
    _ = ‖L‖ * N T * ‖R‖ := by ring

/-- One-sided left estimate. -/
theorem comp_left_le_mul (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (L : Y →L[𝕜] Y) (T : X →L[𝕜] Y) :
    N (L ∘L T) ≤ ‖L‖ * N T := by
  have h := comp_le_mul N L T (ContinuousLinearMap.id 𝕜 X)
  rw [ContinuousLinearMap.comp_id] at h
  calc
    N (L ∘L T) ≤ ‖L‖ * N T * ‖ContinuousLinearMap.id 𝕜 X‖ := h
    _ ≤ ‖L‖ * N T * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (mul_nonneg (norm_nonneg L) (N.nonneg T))
    _ = ‖L‖ * N T := by ring

/-- A compatible cross-operator norm is invariant under negation. -/
theorem map_neg (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (T : X →L[𝕜] Y) : N (-T) = N T := by
  have h := N.smul (-1) T
  simpa using h

/-- One-sided right ideal estimate. -/
theorem comp_right_le_mul (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (T : X →L[𝕜] Y) (R : X →L[𝕜] X) :
    N (T ∘L R) ≤ N T * ‖R‖ := by
  have h := comp_le_mul N (ContinuousLinearMap.id 𝕜 Y) T R
  have hid : ‖ContinuousLinearMap.id 𝕜 Y‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc
    N (T ∘L R) = N ((ContinuousLinearMap.id 𝕜 Y) ∘L T ∘L R) := by
      rw [ContinuousLinearMap.id_comp]
    _ ≤ ‖ContinuousLinearMap.id 𝕜 Y‖ * N T * ‖R‖ := h
    _ ≤ 1 * N T * ‖R‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hid (N.nonneg T)) (norm_nonneg R)
    _ = N T * ‖R‖ := by ring

end CompatibleCrossOperatorNorm

/-- Reusable Banach-space Sylvester lower bound from a bounded left inverse.

Davis--Kahan Theorem 5.1 assumes a genuine bounded inverse `A⁻¹` with
`‖A⁻¹‖ ≤ (gamma + delta)⁻¹`.  The proof uses only the left-inverse half of that
datum, so this reusable theorem is intentionally stronger than the printed
statement.  The source-facing theorem `theorem5_1_banach_sylvester_exact` below
restores the literal two-sided inverse hypothesis for statement-level auditing. -/
theorem theorem5_1_banach_sylvester
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hleft : BoundedLeftInverseData A (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  let L := hleft.leftInverse
  have hgd : 0 < gamma + delta := add_pos_of_nonneg_of_pos hgamma hdelta
  have hLT : T = L ∘L C + L ∘L T ∘L B := by
    have hcancel : L ∘L A = ContinuousLinearMap.id 𝕜 Y := hleft.comp_eq_id
    apply ContinuousLinearMap.ext
    intro x
    have heqpoint := congrArg (fun S : X →L[𝕜] Y => S x) hEq
    simp only [sub_apply, ContinuousLinearMap.comp_apply] at heqpoint
    change T x = L (C x) + L (T (B x))
    have hLA : L (A (T x)) = T x := by
      have hp := congrArg (fun S : Y →L[𝕜] Y => S (T x)) hcancel
      simpa using hp
    rw [← heqpoint, map_sub, hLA]
    abel
  have htri : N T ≤ N (L ∘L C) + N (L ∘L T ∘L B) := by
    calc
      N T = N (L ∘L C + L ∘L T ∘L B) := congrArg N.toFun hLT
      _ ≤ N (L ∘L C) + N (L ∘L T ∘L B) := N.triangle _ _
  have hLC : N (L ∘L C) ≤ (gamma + delta)⁻¹ * N C :=
    (CompatibleCrossOperatorNorm.comp_left_le_mul N L C).trans
      (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg C))
  have hLTB : N (L ∘L T ∘L B) ≤ (gamma + delta)⁻¹ * N T * gamma :=
    (CompatibleCrossOperatorNorm.comp_le_mul N L T B).trans
      (mul_le_mul
        (mul_le_mul_of_nonneg_right hleft.norm_le (N.nonneg T))
        hB (norm_nonneg B)
        (mul_nonneg (inv_nonneg.mpr hgd.le) (N.nonneg T)))
  have hsum : N T ≤ (gamma + delta)⁻¹ * N C +
      (gamma + delta)⁻¹ * N T * gamma :=
    htri.trans (add_le_add hLC hLTB)
  have hscaled := mul_le_mul_of_nonneg_left hsum hgd.le
  have hnormalize :
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
        N C + N T * gamma := by
    calc
      (gamma + delta) *
          ((gamma + delta)⁻¹ * N C + (gamma + delta)⁻¹ * N T * gamma) =
          ((gamma + delta) * (gamma + delta)⁻¹) * N C +
            ((gamma + delta) * (gamma + delta)⁻¹) * N T * gamma := by ring
      _ = N C + N T * gamma := by
        rw [mul_inv_cancel₀ hgd.ne']; ring
  rw [hnormalize] at hscaled
  nlinarith


/-- **Davis--Kahan 1970, Theorem 5.1 with the printed inverse hypothesis.**

The paper states `‖A⁻¹‖ ≤ (gamma + delta)⁻¹`.  This source-facing wrapper
carries that literally as a bounded operator `Ainv` which is both a left and a
right inverse of `A`.  The proof below only needs the left-inverse equation,
which is why the reusable theorem `theorem5_1_banach_sylvester` is formulated
with the weaker `BoundedLeftInverseData` hypothesis. -/
theorem theorem5_1_banach_sylvester_exact
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A Ainv : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 Y)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 Y)
    (hAinv_norm : ‖Ainv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  exact theorem5_1_banach_sylvester N A B T C hgamma hdelta hB
    ⟨Ainv, hAinv_left, hAinv_norm⟩ hEq


/-- **Davis--Kahan 1970, Theorem 5.1 with the roles of `A` and `B`
interchanged.**

This is the printed symmetry remark following Theorem 5.1.  The left block is
bounded by `gamma`, the right block has a bounded right inverse of norm at most
`(gamma + delta)⁻¹`, and the same compatible-norm conclusion follows. -/
theorem theorem5_1_banach_sylvester_interchanged
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hA : ‖A‖ ≤ gamma)
    (hright : BoundedRightInverseData B (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C :=
  TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_rightInverse
    N.triangle N.map_neg
    (fun L S => N.comp_left_le_mul L S)
    (fun S R => N.comp_right_le_mul S R)
    N.nonneg hright.comp_eq_id hgamma hdelta hright.norm_le hA hEq


/-- **The printed `A`/`B` interchange remark with a literal inverse of `B`.**

This is the symmetric source wrapper: `A` is bounded by `gamma`, while `Binv`
is a genuine bounded two-sided inverse of `B` with norm at most
`(gamma + delta)⁻¹`. -/
theorem theorem5_1_banach_sylvester_interchanged_exact
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A : Y →L[𝕜] Y) (B Binv : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hA : ‖A‖ ≤ gamma)
    (_hBinv_left : Binv ∘L B = ContinuousLinearMap.id 𝕜 X)
    (hBinv_right : B ∘L Binv = ContinuousLinearMap.id 𝕜 X)
    (hBinv_norm : ‖Binv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C := by
  exact theorem5_1_banach_sylvester_interchanged N A B T C hgamma hdelta hA
    ⟨Binv, hBinv_right, hBinv_norm⟩ hEq

/-- **Davis--Kahan 1970, Theorem 5.1 with an unbounded left block.**

The partial operator `A` is closed and densely defined as stated in the paper,
and has an everywhere-defined bounded left inverse.  The bounded maps `T` and
`C` satisfy the Sylvester equation on that domain.  No right inverse or
surjectivity hypothesis is imposed: the proof uses only cancellation after
applying `A` to `T x`.  The conclusion is the same compatible-norm bound as in
the bounded theorem. -/
theorem theorem5_1_banach_sylvester_unboundedA
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A : Y →ₗ.[𝕜] Y) (_hAdense : Dense (A.domain : Set Y))
    (_hAclosed : A.IsClosed)
    (hAinv : TauCeti.LinearPMap.BoundedEverywhereLeftInverseData A)
    (B : X →L[𝕜] X) (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hAinvNorm : ‖hAinv.inv‖ ≤ (gamma + delta)⁻¹)
    (hB : ‖B‖ ≤ gamma)
    (hEq : TauCeti.LinearPMap.BoundedRightSylvesterEquation A B T C) :
    delta * N T ≤ N C :=
  TauCeti.LinearPMap.opNorm_le_of_boundedRight_sylvester_of_everywhereLeftInverse
    N.triangle
    (fun L S => N.comp_left_le_mul L S)
    (fun S R => N.comp_right_le_mul S R)
    N.nonneg hAinv hgamma hdelta hAinvNorm hB hEq

/-! ## Theorem 5.1 at the printed Banach scope

Davis and Kahan open Theorem 5.1 with "Let `X`, `Y` be **Banach** spaces".  The theorems
above never use completeness -- the estimate is a rearrangement of the Sylvester identity,
not a fixed-point argument -- so they hold over normed spaces, which is strictly stronger
mathematics and is worth keeping as such.

It is not the same *statement* as the printed one, though, and this row's canonical evidence
should be the printed one.  The two wrappers below add `[CompleteSpace X]` and
`[CompleteSpace Y]`, carry the printed hypotheses in their printed form -- `α ≥ 0` and not
`α > 0`, an actual two-sided inverse with `‖A⁻¹‖ ≤ (α + δ)⁻¹`, and a norm on cross-space maps
compatible with the two bound norms -- and invoke the general theorems internally.  Nothing is
reproved and nothing above is weakened. -/

section BanachScope

/-- **Davis--Kahan 1970, Theorem 5.1, at the printed Banach scope.**

`δ N(X) ≤ N(C)` for `AX - XB = C`, with `X` and `Y` Banach, `‖B‖ ≤ α`,
`‖A⁻¹‖ ≤ (α + δ)⁻¹`, `α ≥ 0` and `δ > 0`, and `N` any norm on `X → Y` maps compatible with
the two bound norms.

`theorem5_1_banach_sylvester_exact` is the same statement without completeness; it is the
stronger theorem, and this one is the printed one. -/
theorem theorem5_1_banach_sylvester_banachScope
    [CompleteSpace X] [CompleteSpace Y]
    (N : CompatibleCrossOperatorNorm (𝕜 := 𝕜) (X := X) (Y := Y))
    (A Ainv : Y →L[𝕜] Y) (B : X →L[𝕜] X)
    (T C : X →L[𝕜] Y) {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hB : ‖B‖ ≤ gamma)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 Y)
    (hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 Y)
    (hAinv_norm : ‖Ainv‖ ≤ (gamma + delta)⁻¹)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C :=
  theorem5_1_banach_sylvester_exact N A Ainv B T C hgamma hdelta hB
    hAinv_left hAinv_right hAinv_norm hEq

/-- **Theorem 5.1's estimate under the four properties its proof actually consumes**, over an
arbitrary scalar field.

`N` here is not required to be a norm.  The hypotheses are subadditivity, the two one-sided
bounds by the operator norm, and nonnegativity -- exactly what the rearrangement of the
Sylvester identity uses, and nothing more.  A `CompatibleCrossOperatorNorm` supplies all four
and is genuinely a norm besides: it also has absolute homogeneity, `N T = 0 → T = 0`, and
two-sided contraction compatibility rather than the ideal bounds.  So this theorem is a
**generalization** of `theorem5_1_banach_sylvester_banachScope`, not the same statement with a
bundle unfolded, and the source's "any norm compatible with those bound norms" is the bundled
one.

An earlier version of this docstring called the four properties "the compatible norm spelled
out" and "the same content" as the bundle.  Both were wrong, and the 2026-09-05 hostile
follow-up review caught them; the row's registration had already been corrected to
`generalization` by then, so only the prose was stale.  Cite
`theorem5_1_banach_sylvester_banachScope` for Theorem 5.1; cite this when the object in hand is
a bare ideal gauge rather than a norm. -/
theorem theorem5_1_banach_sylvester_banachScope_ofProperties
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {N : (F →L[𝕜] E) → ℝ}
    (hadd : ∀ f g : F →L[𝕜] E, N (f + g) ≤ N f + N g)
    (hidealL : ∀ (L : E →L[𝕜] E) (f : F →L[𝕜] E), N (L ∘L f) ≤ ‖L‖ * N f)
    (hidealR : ∀ (f : F →L[𝕜] E) (R : F →L[𝕜] F), N (f ∘L R) ≤ N f * ‖R‖)
    (hNnonneg : ∀ f : F →L[𝕜] E, 0 ≤ N f)
    {A Ainv : E →L[𝕜] E} {B : F →L[𝕜] F} {T C : F →L[𝕜] E} {gamma delta : ℝ}
    (hgamma : 0 ≤ gamma) (hdelta : 0 < delta)
    (hAinv_left : Ainv ∘L A = ContinuousLinearMap.id 𝕜 E)
    (_hAinv_right : A ∘L Ainv = ContinuousLinearMap.id 𝕜 E)
    (hAinv_norm : ‖Ainv‖ ≤ (gamma + delta)⁻¹) (hB : ‖B‖ ≤ gamma)
    (hEq : A ∘L T - T ∘L B = C) :
    delta * N T ≤ N C :=
  TauCeti.ContinuousLinearMap.opNorm_le_of_sylvester_of_leftInverse
    hadd hidealL hidealR hNnonneg hAinv_left hgamma hdelta hAinv_norm hB hEq

end BanachScope

end BanachSylvester
end DavisKahan1970
end TauCeti
