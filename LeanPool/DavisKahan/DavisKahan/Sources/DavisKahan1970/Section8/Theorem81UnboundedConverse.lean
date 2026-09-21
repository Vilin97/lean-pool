/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedBranch
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralProjectionNaturality

/-!
# Theorem 8.1's printed characterization, both directions, at unbounded scope

Davis and Kahan state Theorem 8.1 as an *if and only if*: `Θ ≤ π/4` holds exactly
when the chosen reducing blocks of `A + H` are placed as `Λ₀ ≤ α`, `Λ₁ ≥ α + δ`.

`theorem8_1_maximalAngle_le_of_spectrumIn_unbounded` proves the direction from
the placement.  This module proves the converse, and with it the printed
equivalence, at unbounded ambient scope.

The converse is *uniqueness of the branch*: a reducing subspace `M` of `A + H`
inside the closed quarter turn from `P` must be the canonical branch
`Q = E_{A+H}(-∞, α]`, whose placement is already known.  Two ingredients:

* the **pointwise** strict bound
  `norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded_printed` --
  `‖P_P y − P_Q y‖ < ‖y‖/√2` for every `y ≠ 0`.  The bounded proof uses the
  *uniform* `IsQuarterAcute P Q`, whose constant `δ / (1 + ‖C‖)` degenerates as
  `‖A‖ → ∞`; the uniqueness argument tests one vector at a time and never needed
  it.  This is what makes the converse available unbounded.
* the commutation `P_M P_Q = P_Q P_M`, from
  `specProjection_apply_of_unitary_intertwines`: `M` reduces `A + H`, so its
  *reflection* is a unitary commuting with `A + H`, and a unitary commuting with a
  self-adjoint partial map commutes with its spectral projections.

With those, `M ∩ Qᗮ = 0` and `Q ∩ Mᗮ = 0`, and commuting projections turn the two
trivial crossed intersections into `M = Q`.

## Provenance

Davis--Kahan 1970, Theorem 8.1, the `only if` half of the printed
characterization, at the paper's ambient unbounded scope.  The bounded sibling is
`theorem8_1_eq_canonicalBranch_of_maximalAngle_le`.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahanExt (maximalAngle)

noncomputable section

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### A reducing projection commutes with every spectral projection -/

/-- **The projection onto a reducing subspace commutes with every spectral
projection of the operator.**

The reflection `2 P_Q − 1` is a unitary preserving the domain and commuting with
`B` there, so `specProjection_apply_of_unitary_intertwines` applies; dividing the
reflection identity by two is the whole rest of the proof. -/
theorem starProjection_specProjection_comm_of_reduces
    {B : H →ₗ.[ℂ] H} (hB : IsSelfAdjoint B) {Q : Submodule ℂ H}
    [Q.HasOrthogonalProjection]
    (hQ : TauCeti.LinearPMap.ReducesSubspace B Q)
    (S : Set ℝ) (hS : MeasurableSet S) (x : H) :
    Q.starProjection (TauCeti.LinearPMap.specProjection hB S hS x)
      = TauCeti.LinearPMap.specProjection hB S hS (Q.starProjection x) := by
  obtain ⟨hmaps, hcomm⟩ := TauCeti.DavisKahan.reflection_commutes_of_reducesSubspace hQ
  have hmaps' : ∀ z : B.domain, Q.reflection (z : H) ∈ B.domain := by
    intro z
    have h := hmaps z
    rwa [Submodule.reflectionOperator_apply_eq_reflection] at h
  have hint : ∀ z : B.domain, B ⟨Q.reflection (z : H), hmaps' z⟩ = Q.reflection (B z) := by
    intro z
    have heq : (⟨Q.reflection (z : H), hmaps' z⟩ : B.domain)
        = ⟨Q.reflectionOperator (z : H), hmaps z⟩ :=
      Subtype.ext (Submodule.reflectionOperator_apply_eq_reflection Q (z : H)).symm
    rw [heq, hcomm z]
    exact Submodule.reflectionOperator_apply_eq_reflection Q _
  have hnat := TauCeti.LinearPMap.specProjection_apply_of_unitary_intertwines hB
    Q.reflection hmaps' hint S hS x
  have hnat' : Q.reflectionOperator (TauCeti.LinearPMap.specProjection hB S hS x)
      = TauCeti.LinearPMap.specProjection hB S hS (Q.reflectionOperator x) := by
    rw [Submodule.reflectionOperator_apply_eq_reflection,
      Submodule.reflectionOperator_apply_eq_reflection]
    exact hnat
  rw [Submodule.reflectionOperator_apply, Submodule.reflectionOperator_apply, map_sub,
    map_smul] at hnat'
  exact smul_right_injective H (two_ne_zero) (sub_left_inj.mp hnat')

/-! ### Two pieces of projection geometry -/

omit [CompleteSpace H] in
/-- **The pointwise strict bound, read on the orthogonal complement.**

A vector of `Qᗮ` on which the projector difference is strictly inside the `√2/2`
threshold is strictly outside the cone of `P`. -/
theorem norm_starProjection_lt_of_mem_orthogonal_of_sq_lt
    {P Q : Submodule ℂ H} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    {y : H}
    (hlt : ‖P.starProjection y - Q.starProjection y‖ ^ 2 < (1 / 2 : ℝ) * ‖y‖ ^ 2)
    (hy : y ∈ Qᗮ) :
    ‖P.starProjection y‖ < Real.sqrt 2 / 2 * ‖y‖ := by
  have hQy : Q.starProjection y = 0 :=
    (Submodule.starProjection_apply_eq_zero_iff Q).mpr hy
  rw [hQy, sub_zero] at hlt
  have hb : (0 : ℝ) ≤ Real.sqrt 2 / 2 * ‖y‖ := by positivity
  refine lt_of_pow_lt_pow_left₀ 2 hb ?_
  have hsq : (Real.sqrt 2 / 2 * ‖y‖) ^ 2 = (1 / 2 : ℝ) * ‖y‖ ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hsq]
  exact hlt

omit [CompleteSpace H] in
/-- The projector difference does not see orthogonal complementation. -/
theorem norm_starProjection_orthogonal_sub_eq (U V : Submodule ℂ H)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] (y : H) :
    ‖Uᗮ.starProjection y - Vᗮ.starProjection y‖
      = ‖U.starProjection y - V.starProjection y‖ := by
  rw [Submodule.starProjection_orthogonal_apply, Submodule.starProjection_orthogonal_apply,
    show y - U.starProjection y - (y - V.starProjection y)
      = V.starProjection y - U.starProjection y by abel, norm_sub_rev]

omit [CompleteSpace H] in
/-- **Commuting projections with trivial crossed intersections coincide.**

If `P_M` and `P_Q` commute and neither subspace meets the other's complement, then
`M = Q`.  The commutation is what makes `P_{Qᗮ} u` stay inside `M`. -/
theorem eq_of_starProjection_comm_of_crossed_trivial
    {M Q : Submodule ℂ H} [M.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hcomm : ∀ x : H, M.starProjection (Q.starProjection x)
      = Q.starProjection (M.starProjection x))
    (hMQ : ∀ u : H, u ∈ M → u ∈ Qᗮ → u = 0)
    (hQM : ∀ u : H, u ∈ Q → u ∈ Mᗮ → u = 0) :
    M = Q := by
  refine le_antisymm ?_ ?_
  · intro u hu
    have hMu : M.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr hu
    have key : M.starProjection (Qᗮ.starProjection u) = Qᗮ.starProjection u := by
      rw [Submodule.starProjection_orthogonal_apply, map_sub, hcomm, hMu]
    have hzero : Qᗮ.starProjection u = 0 :=
      hMQ _ (Submodule.starProjection_eq_self_iff.mp key) (Qᗮ.starProjection_apply_mem u)
    rw [Submodule.starProjection_orthogonal_apply] at hzero
    have hu' : u = Q.starProjection u := (sub_eq_zero.mp hzero)
    rw [hu']
    exact Q.starProjection_apply_mem u
  · intro u hu
    have hQu : Q.starProjection u = u := Submodule.starProjection_eq_self_iff.mpr hu
    have key : Q.starProjection (Mᗮ.starProjection u) = Mᗮ.starProjection u := by
      rw [Submodule.starProjection_orthogonal_apply, map_sub, ← hcomm, hQu]
    have hzero : Mᗮ.starProjection u = 0 :=
      hQM _ (Submodule.starProjection_eq_self_iff.mp key) (Mᗮ.starProjection_apply_mem u)
    rw [Submodule.starProjection_orthogonal_apply] at hzero
    have hu' : u = M.starProjection u := (sub_eq_zero.mp hzero)
    rw [hu']
    exact M.starProjection_apply_mem u

/-! ### Uniqueness of the branch, and the printed equivalence -/

variable {A : H →ₗ.[ℂ] H} {Hop : H →L[ℂ] H} {P : Submodule ℂ H}
  [P.HasOrthogonalProjection] {alpha delta : ℝ}

/-- **Theorem 8.1's uniqueness of the branch, at unbounded scope.**

A reducing subspace of `A + H` inside the closed quarter turn from `P` is the
canonical spectral branch. -/
theorem theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : H) ∈ P →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ alpha * ‖(x : H)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : H) ∈ Pᗮ →
      (alpha + delta) * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (hM : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) M)
    (hMangle : maximalAngle P M ≤ Real.pi / 4) :
    M = canonicalLowBranchUnbounded (isSelfAdjoint_perturbed hA hH) alpha := by
  have hHsa : IsSelfAdjoint Hop :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH
  have hPP : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    isSelfAdjoint_perturbed hA hH
  have hQred := canonicalLowBranchUnbounded_reduces hB alpha
  have hform := theorem8_1_canonicalBranchUnbounded_form (A := A) (Hop := Hop) (P := Pᗮ)
    (alpha := alpha) (delta := delta) hA hH hredPperp hPhigh
    (by rw [hPP]; exact hPlow)
    (by rw [hPP]; exact hHPperp) (by rw [hPP]; exact hHP) hdelta
  have hstrict := DavisKahan.norm_starProjection_sub_sq_lt_of_orderedFormGap_unbounded_printed
    A Hop P (canonicalLowBranchUnbounded hB alpha) hA hHsa hredPperp hQred.orthogonal
    hPlow hPhigh hform.1 hform.2 hHP hHPperp hdelta
  have hgapM : P.projectionGap M ≤ Real.sqrt 2 / 2 :=
    (maximalAngle_le_pi_div_four_iff P M).1 hMangle
  have hgapMperp : Pᗮ.projectionGap Mᗮ ≤ Real.sqrt 2 / 2 := by
    rw [TauCeti.DavisKahan.subspaceGap_orthogonal P M]
    exact hgapM
  have hQsp : (canonicalLowBranchUnbounded hB alpha).starProjection
      = TauCeti.LinearPMap.specProjection hB (Set.Iic alpha) measurableSet_Iic :=
    (TauCeti.LinearPMap.specProjection_eq_starProjection_specRange hB
      (Set.Iic alpha) measurableSet_Iic).symm
  refine eq_of_starProjection_comm_of_crossed_trivial ?_ ?_ ?_
  · intro x
    rw [hQsp]
    exact starProjection_specProjection_comm_of_reduces hB hM _ _ x
  · intro u huM huQperp
    by_contra hne
    have h1 := sqrt_two_div_two_mul_norm_le_norm_starProjection hgapM huM
    have h2 := norm_starProjection_lt_of_mem_orthogonal_of_sq_lt (hstrict u hne) huQperp
    linarith
  · intro u huQ huMperp
    by_contra hne
    have h1 := sqrt_two_div_two_mul_norm_le_norm_starProjection hgapMperp huMperp
    have hlt : ‖Pᗮ.starProjection u
        - (canonicalLowBranchUnbounded hB alpha)ᗮ.starProjection u‖ ^ 2
        < (1 / 2 : ℝ) * ‖u‖ ^ 2 := by
      rw [norm_starProjection_orthogonal_sub_eq]
      exact hstrict u hne
    have h2 := norm_starProjection_lt_of_mem_orthogonal_of_sq_lt hlt
      (by rw [Submodule.orthogonal_orthogonal]; exact huQ)
    linarith

/-- **Davis--Kahan 1970, Theorem 8.1's printed characterization, at unbounded
scope.**

`Θ(P, M) ≤ π/4` exactly when the chosen reducing blocks of `A + H` are placed as
the paper prescribes: `Λ₀ ≤ α` on `M` and `Λ₁ ≥ α + δ` on `Mᗮ`.  Both are read as
ordered form bounds on the domain, which is the reading the unbounded quarter-angle
theorem and the spectral branch both use. -/
theorem theorem8_1_maximalAngle_le_iff_orderedFormGap_unbounded
    (hA : IsSelfAdjoint A) (hH : Hop.IsSymmetric)
    (hredPperp : TauCeti.LinearPMap.ReducesSubspace A Pᗮ)
    (hPlow : ∀ x : A.domain, (x : H) ∈ P →
      RCLike.re ⟪A x, (x : H)⟫_ℂ ≤ alpha * ‖(x : H)‖ ^ 2)
    (hPhigh : ∀ x : A.domain, (x : H) ∈ Pᗮ →
      (alpha + delta) * ‖(x : H)‖ ^ 2 ≤ RCLike.re ⟪A x, (x : H)⟫_ℂ)
    (hHP : ∀ x ∈ P, Hop x ∈ Pᗮ) (hHPperp : ∀ x ∈ Pᗮ, Hop x ∈ P)
    (hdelta : 0 < delta)
    (M : Submodule ℂ H) [M.HasOrthogonalProjection]
    (hM : TauCeti.LinearPMap.ReducesSubspace (TauCeti.LinearPMap.addBounded A Hop) M) :
    maximalAngle P M ≤ Real.pi / 4 ↔
      ((∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : H) ∈ M →
          RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ ≤
            alpha * ‖(x : H)‖ ^ 2) ∧
        ∀ x : (TauCeti.LinearPMap.addBounded A Hop).domain, (x : H) ∈ Mᗮ →
          (alpha + delta) * ‖(x : H)‖ ^ 2 ≤
            RCLike.re ⟪TauCeti.LinearPMap.addBounded A Hop x, (x : H)⟫_ℂ) := by
  have hHsa : IsSelfAdjoint Hop :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hH
  have hPP : (Pᗮ)ᗮ = P := Submodule.orthogonal_orthogonal P
  have hB : IsSelfAdjoint (TauCeti.LinearPMap.addBounded A Hop) :=
    isSelfAdjoint_perturbed hA hH
  constructor
  · intro hangle
    have hMQ := theorem8_1_eq_canonicalBranchUnbounded_of_maximalAngle_le
      hA hH hredPperp hPlow hPhigh hHP hHPperp hdelta M hM hangle
    have hform := theorem8_1_canonicalBranchUnbounded_form (A := A) (Hop := Hop) (P := Pᗮ)
      (alpha := alpha) (delta := delta) hA hH hredPperp hPhigh
      (by rw [hPP]; exact hPlow)
      (by rw [hPP]; exact hHPperp) (by rw [hPP]; exact hHP) hdelta
    refine ⟨fun x hx => hform.1 x ?_, fun x hx => hform.2 x ?_⟩
    · rwa [← hMQ]
    · rwa [← hMQ]
  · rintro ⟨hMlow, hMhigh⟩
    exact DavisKahan.maximalAngle_le_pi_div_four_of_orderedFormGap_unbounded_printed
      A Hop P M hA hHsa hredPperp hM.orthogonal hPlow hPhigh hMlow hMhigh hHP hHPperp hdelta

end

end Section8
end DavisKahan1970
end TauCeti
