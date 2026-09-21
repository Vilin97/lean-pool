/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaApproximatePair
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.SpectralSelection
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.SubspaceSingularTransport

/-! # Tan Two Theta Branch Free Infinite -/

open TauCeti.DavisKahan.ExactSinTheta

open TauCeti.DavisKahan.Sylvester

/-!
# The branch-free `tan 2Θ` theorem with an *arbitrary* trial subspace

`DavisKahan/DoubleAngle/TanTwoThetaKyFanFiniteCarrier.lean` proves the
branch-free Section 7 estimate on an arbitrary ambient Hilbert space but with
`[FiniteDimensional 𝕜 U]`, because it compresses to the carrier `U ⊔ T''U` in
order to reach the intrinsic singular-system layer.  This module removes that
restriction.

## Method

The finite-dimensional layer needs an *exact* matched singular pair of the
graph coordinate for each index, and on an arbitrary Hilbert space `T` need not
have singular vectors at all.  The replacement is the repository's
`ApproximateLeadingSingularFamily`, which exists for **every** bounded operator
with no compactness assumption, together with the approximate-pair form of
equation (7.6) in `DavisKahan/DoubleAngle/TanTwoThetaApproximatePair.lean`.
This is the same limiting architecture that
`DavisKahan.Sources.DavisKahan1970.SharpKyFan.sharp_transformed_prefix` uses to
remove finite-dimensionality from the *selected-branch* theorem; only the
per-pair estimate is different, and in particular nothing here divides by
`I - X* X` or asks for a contraction.

The family is taken for the graph coordinate *as a map between the two blocks*,
`blockGraphCoordinate T U : U →L Uᗮ`, so that the right vectors lie in `U` and
the left vectors in `Uᗮ` **by typing** rather than approximately.  Its
approximation numbers are those of the ambient `T`, by the existing
`sameApproximationSingularValues_ambientSubspaceBlock`.

## The pole at `π/4`

No uniform separation from the pole is assumed.  The per-pair estimate derives
it from the gap (see `penalty_le_of_paired_approximate`), and the resulting
penalty is `O(ε)`; the `ε → 0` passage here is what removes it.  The tail
indices of the family, where the approximation number is at most `ε`, are far
from the pole for trivial reasons and contribute `O(ε)` as well.

## Scalar scope

The existence of approximate leading singular families is proved through the
complex projection-valued measure, so this module is stated over `ℂ`.  The real
case is obtained by complexification in
`DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfiniteReal.lean`; the
`RCLike`-generic core in `TanTwoThetaApproximatePair.lean` is shared.
-/

namespace TauCeti
namespace DavisKahan.TanTwoTheta


open scoped InnerProductSpace
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan (exists_approximateLeadingSingularFamily)

noncomputable section

universe u

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A subspace admitting an orthogonal projection inside a complete ambient
space is itself complete.  `local instance` does not propagate through imports,
so it is reinstalled here; the whole argument happens in the coordinate spaces
of `U` and `Uᗮ`. -/
local instance instCompleteSpaceCoeBranchFreeInfinite
    {G : Type u} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (U : Submodule ℂ G) [U.HasOrthogonalProjection] : CompleteSpace U :=
  (Submodule.isComplete_coe_of_hasOrthogonalProjection U).completeSpace_coe

section BlockCoordinate

variable {T : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]

/-- The graph coordinate read as an operator between the two blocks,
`U →L Uᗮ`.  Approximate singular families for this operator automatically have
their right vectors in `U` and their left vectors in `Uᗮ`, which is what the
approximate-pair form of equation (7.6) consumes. -/
def blockGraphCoordinate (T : E →L[ℂ] E) (U : Submodule ℂ E)
    [U.HasOrthogonalProjection] : U →L[ℂ] Uᗮ :=
  Uᗮ.orthogonalProjectionOnto ∘L T ∘L U.subtypeL

omit [CompleteSpace E] in
/-- On `U` the block coordinate is just `T`. -/
theorem coe_blockGraphCoordinate (hTmem : ∀ x, T x ∈ Uᗮ) (x : U) :
    ((blockGraphCoordinate T U x : Uᗮ) : E) = T (x : E) := by
  show Uᗮ.starProjection (T (x : E)) = T (x : E)
  exact Submodule.starProjection_eq_self_iff.mpr (hTmem _)

omit [CompleteSpace E] in
/-- `T` is supported on `U`: it factors through the orthogonal projection. -/
theorem apply_eq_apply_starProjection (hTzero : ∀ x ∈ Uᗮ, T x = 0) (x : E) :
    T x = T (U.starProjection x) := by
  have hmem : x - U.starProjection x ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    rw [inner_sub_right, ← U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw, sub_self]
  have hz := hTzero _ hmem
  have hadd : T x = T (U.starProjection x) + T (x - U.starProjection x) := by
    rw [← map_add]
    congr 1
    abel
  rw [hadd, hz, add_zero]

/-- The ambient graph coordinate is the block coordinate framed by the
inclusion and the projection. -/
theorem eq_subtypeL_comp_blockGraphCoordinate
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0) :
    T = Uᗮ.subtypeL ∘L blockGraphCoordinate T U ∘L
      ContinuousLinearMap.adjoint U.subtypeL := by
  rw [Submodule.adjoint_subtypeL]
  ext x
  show T x = ((blockGraphCoordinate T U (U.orthogonalProjectionOnto x) : Uᗮ) : E)
  rw [coe_blockGraphCoordinate hTmem]
  exact apply_eq_apply_starProjection hTzero x

/-- The block coordinate has exactly the approximation numbers of the ambient
graph coordinate. -/
theorem approximationNumber_blockGraphCoordinate
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0) (n : ℕ) :
    (blockGraphCoordinate T U).approximationNumber n = T.approximationNumber n := by
  have h := sameApproximationSingularValues_ambientSubspaceBlock U Uᗮ
    (blockGraphCoordinate T U)
  rw [← eq_subtypeL_comp_blockGraphCoordinate hTmem hTzero] at h
  exact (h n).symm

/-- The adjoint of the ambient graph coordinate agrees with the adjoint of the
block coordinate on `Uᗮ`. -/
theorem coe_adjoint_blockGraphCoordinate
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0) (y : Uᗮ) :
    ((ContinuousLinearMap.adjoint (blockGraphCoordinate T U) y : U) : E) =
      ContinuousLinearMap.adjoint T (y : E) := by
  have hfac := eq_subtypeL_comp_blockGraphCoordinate hTmem hTzero
  have hadj : ContinuousLinearMap.adjoint T =
      U.subtypeL ∘L ContinuousLinearMap.adjoint (blockGraphCoordinate T U) ∘L
        Uᗮ.orthogonalProjectionOnto := by
    have hc := congrArg ContinuousLinearMap.adjoint hfac
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, Submodule.adjoint_subtypeL,
      ContinuousLinearMap.comp_assoc] at hc
    exact hc
  rw [hadj]
  show _ = ((ContinuousLinearMap.adjoint (blockGraphCoordinate T U)
    (Uᗮ.orthogonalProjectionOnto (y : E)) : U) : E)
  congr 2
  exact (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self y).symm

omit [CompleteSpace E] in
/-- Coercion of an orthonormal family in a subspace is orthonormal in the
ambient space. -/
theorem orthonormal_coe_subtype {U : Submodule ℂ E} {m : ℕ} {f : Fin m → U}
    (hf : Orthonormal ℂ f) : Orthonormal ℂ (fun j => ((f j : U) : E)) := by
  rw [orthonormal_iff_ite] at hf ⊢
  intro i j
  simpa [Submodule.coe_inner] using hf i j

end BlockCoordinate

section Main

variable {A H T : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]
  {a b : ℝ}

/-- The total `ε`-coefficient of the finite-`ε` estimate: the per-pair penalty
plus the trivial contribution of the tail indices, where the approximation
number is at most `ε` and so the pole is far away. -/
def branchFreeTotalErrorCoefficient (A H T : E →L[ℂ] E) (d : ℝ) : ℝ :=
  branchFreeTangentErrorCoefficient A H T d + d * (8 / 3)

omit [CompleteSpace E] in
/-- The total error coefficient is nonnegative. -/
theorem branchFreeTotalErrorCoefficient_nonneg (A H T : E →L[ℂ] E) {d : ℝ}
    (hd : 0 ≤ d) : 0 ≤ branchFreeTotalErrorCoefficient A H T d := by
  unfold branchFreeTotalErrorCoefficient
  have := branchFreeTangentErrorCoefficient_nonneg A H T d
  positivity

/-- **The branch-free Section 7 estimate with an explicit `ε` error, over an
arbitrary finite index set, with no dimension hypothesis.**

`S` is arbitrary rather than an initial segment because `t ↦ 2t/|1 - t²|` is
not monotone across the quarter turn, so a `tan 2Θ` representative carries the
branch-free tangents as a multiset. -/
theorem sum_absDoubleAngleTangent_le_add_error
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (S : Finset ℕ) {ε : ℝ} (hε0 : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (hsmall : approximatePairErrorCoefficient A H T * ε ≤ (b - a) / 4) :
    (b - a) * ∑ n ∈ S, absDoubleAngleTangent (approximationSingularValue n T) ≤
      2 * kyFanApproximationGauge S.card H +
        S.card * (branchFreeTotalErrorCoefficient A H T (b - a) * ε) := by
  classical
  have hd : 0 < b - a := by linarith
  have hε1 : ε ≤ 1 := by linarith
  set X : U →L[ℂ] Uᗮ := blockGraphCoordinate T U with hXdef
  have hXnum : ∀ n, X.approximationNumber n = approximationSingularValue n T :=
    fun n => approximationNumber_blockGraphCoordinate hTmem hTzero n
  -- a family long enough to cover every index of `S`
  set k : ℕ := S.sup id + 1 with hkdef
  have hSk : ∀ n ∈ S, n < k := by
    intro n hn
    exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
  obtain ⟨F⟩ := exists_approximateLeadingSingularFamily X k hε0
  -- split `S` at the family's cutoff
  set S₁ : Finset ℕ := S.filter (fun n => n < F.count) with hS₁def
  set S₂ : Finset ℕ := S.filter (fun n => ¬ n < F.count) with hS₂def
  have hSsplit : (S₁.card : ℝ) + S₂.card = S.card := by
    have := Finset.card_filter_add_card_filter_not (s := S)
      (p := fun n => n < F.count)
    push_cast [← this, hS₁def, hS₂def]
    ring
  have hsumsplit : ∑ n ∈ S, absDoubleAngleTangent (approximationSingularValue n T) =
      (∑ n ∈ S₁, absDoubleAngleTangent (approximationSingularValue n T)) +
        ∑ n ∈ S₂, absDoubleAngleTangent (approximationSingularValue n T) := by
    rw [hS₁def, hS₂def, Finset.sum_filter_add_sum_filter_not]
  -- (i) the selected indices, through the approximate-pair estimate
  set m : ℕ := S₁.card with hmdef
  have hmem₁ : ∀ n ∈ S₁, n < F.count := by
    intro n hn
    rw [hS₁def, Finset.mem_filter] at hn
    exact hn.2
  set e := S₁.orderIsoOfFin (rfl : S₁.card = m) with hedef
  set idx : Fin m → Fin F.count :=
    fun j => ⟨(e j : ℕ), hmem₁ _ (e j).2⟩ with hidxdef
  have hidxinj : Function.Injective idx := by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact congrArg Fin.val hij
  set uu : Fin m → E := fun j => ((F.right (idx j) : U) : E) with huudef
  set vv : Fin m → E := fun j => ((F.left (idx j) : Uᗮ) : E) with hvvdef
  set tt : Fin m → ℝ :=
    fun j => approximationSingularValue ((e j : ℕ)) T with httdef
  have hu : Orthonormal ℂ uu :=
    orthonormal_coe_subtype (F.right_orthonormal.comp idx hidxinj)
  have hv : Orthonormal ℂ vv :=
    orthonormal_coe_subtype (F.left_orthonormal.comp idx hidxinj)
  have hXidx : ∀ j : Fin m, X.approximationNumber (idx j : ℕ) = tt j := by
    intro j
    rw [httdef]
    exact hXnum _
  have hTuu : ∀ j, ‖T (uu j) - ((tt j : ℝ) : ℂ) • vv j‖ ≤ ε := by
    intro j
    have hres := F.apply_residual (idx j)
    rw [hXidx j] at hres
    have hcoe : T (uu j) - ((tt j : ℝ) : ℂ) • vv j =
        ((X (F.right (idx j)) - ((tt j : ℝ) : ℂ) • F.left (idx j) : Uᗮ) : E) := by
      rw [huudef, hvvdef, ← coe_blockGraphCoordinate (T := T) (U := U) hTmem]
      simp [hXdef]
    rw [hcoe]
    exact hres
  have hTvv : ∀ j, ‖ContinuousLinearMap.adjoint T (vv j) -
      ((tt j : ℝ) : ℂ) • uu j‖ ≤ ε := by
    intro j
    have hres := F.adjoint_residual (idx j)
    rw [hXidx j] at hres
    have hcoe : ContinuousLinearMap.adjoint T (vv j) - ((tt j : ℝ) : ℂ) • uu j =
        ((ContinuousLinearMap.adjoint X (F.left (idx j)) -
          ((tt j : ℝ) : ℂ) • F.right (idx j) : U) : E) := by
      rw [huudef, hvvdef,
        ← coe_adjoint_blockGraphCoordinate (T := T) (U := U) hTmem hTzero]
      simp [hXdef]
    rw [hcoe]
    exact hres
  have hpart₁ := sum_absDoubleAngleTangent_le_of_approximatePairs
    hA hH hAU hHU hHUperp hTmem hUb hUa hinv hab hu hv
    (fun j => (F.right (idx j)).2) (fun j => (F.left (idx j)).2)
    (fun j => approximationSingularValue_nonneg _ _) hε1 hTuu hTvv hsmall
  have hreindex : ∑ j : Fin m, absDoubleAngleTangent (tt j) =
      ∑ n ∈ S₁, absDoubleAngleTangent (approximationSingularValue n T) := by
    rw [← Finset.sum_coe_sort S₁
      (fun n : ℕ => absDoubleAngleTangent (approximationSingularValue n T))]
    exact Equiv.sum_comp e.toEquiv
      (fun x : {x // x ∈ S₁} =>
        absDoubleAngleTangent (approximationSingularValue (x : ℕ) T))
  rw [hreindex] at hpart₁
  have hkyfanmono : kyFanApproximationGauge m H ≤
      kyFanApproximationGauge S.card H := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · have hcard : m ≤ S.card := by
        rw [hmdef, hS₁def]
        exact Finset.card_filter_le _ _
      exact fun n hn => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hn) hcard)
    · exact fun n _ _ => approximationSingularValue_nonneg _ _
  -- (ii) the tail indices: the approximation number is at most `ε`, so the
  -- pole is far away for trivial reasons
  have htail : ∀ n ∈ S₂,
      absDoubleAngleTangent (approximationSingularValue n T) ≤ 8 / 3 * ε := by
    intro n hn
    rw [hS₂def, Finset.mem_filter] at hn
    have hcount : F.count ≤ n := Nat.le_of_not_lt hn.2
    have hsmalln : approximationSingularValue n T ≤ ε := by
      rw [← hXnum n]
      exact F.tail_small n hcount (hSk n hn.1)
    have hn0 : 0 ≤ approximationSingularValue n T := approximationSingularValue_nonneg _ _
    have hden : (3 : ℝ) / 4 ≤ 1 - approximationSingularValue n T ^ 2 := by nlinarith
    have hdenabs : (3 : ℝ) / 4 ≤ |1 - approximationSingularValue n T ^ 2| :=
      hden.trans (le_abs_self _)
    rw [absDoubleAngleTangent, div_le_iff₀ (by linarith : (0:ℝ) < |1 - approximationSingularValue n T ^ 2|)]
    nlinarith
  have hpart₂ : ∑ n ∈ S₂,
      absDoubleAngleTangent (approximationSingularValue n T) ≤
        S₂.card * (8 / 3 * ε) := by
    calc ∑ n ∈ S₂, absDoubleAngleTangent (approximationSingularValue n T)
        ≤ ∑ _n ∈ S₂, (8 / 3 * ε) := Finset.sum_le_sum htail
      _ = S₂.card * (8 / 3 * ε) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- combine
  have hC0 : 0 ≤ branchFreeTangentErrorCoefficient A H T (b - a) :=
    branchFreeTangentErrorCoefficient_nonneg A H T (b - a)
  have hm : (m : ℝ) ≤ S.card := by
    have h1 : (0 : ℝ) ≤ S₂.card := Nat.cast_nonneg _
    linarith [hSsplit]
  have hS₂le : (S₂.card : ℝ) ≤ S.card := by
    have h1 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith [hSsplit]
  rw [hsumsplit, mul_add]
  unfold branchFreeTotalErrorCoefficient
  have hstep₂ : (b - a) * ∑ n ∈ S₂,
      absDoubleAngleTangent (approximationSingularValue n T) ≤
        S.card * ((b - a) * (8 / 3) * ε) := by
    have h := mul_le_mul_of_nonneg_left hpart₂ hd.le
    refine h.trans ?_
    have : (b - a) * (S₂.card * (8 / 3 * ε)) =
        (S₂.card : ℝ) * ((b - a) * (8 / 3) * ε) := by ring
    rw [this]
    refine mul_le_mul_of_nonneg_right hS₂le ?_
    positivity
  have hstep₁ : (b - a) * ∑ n ∈ S₁,
      absDoubleAngleTangent (approximationSingularValue n T) ≤
        2 * kyFanApproximationGauge S.card H +
          S.card * (branchFreeTangentErrorCoefficient A H T (b - a) * ε) := by
    refine hpart₁.trans ?_
    have h1 : 2 * kyFanApproximationGauge m H ≤
        2 * kyFanApproximationGauge S.card H := by linarith
    have h2 : (m : ℝ) *
        (branchFreeTangentErrorCoefficient A H T (b - a) * ε) ≤
          S.card * (branchFreeTangentErrorCoefficient A H T (b - a) * ε) := by
      refine mul_le_mul_of_nonneg_right hm ?_
      positivity
    linarith
  have hexpand : (S.card : ℝ) *
      ((branchFreeTangentErrorCoefficient A H T (b - a) + (b - a) * (8 / 3)) * ε) =
      S.card * (branchFreeTangentErrorCoefficient A H T (b - a) * ε) +
        S.card * ((b - a) * (8 / 3) * ε) := by ring
  rw [hexpand]
  linarith

/-- **The branch-free Ky Fan root of the Section 2 `tan 2Θ` theorem on an
arbitrary Hilbert space, with an arbitrary trial subspace.**

This is `sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace`
with `[FiniteDimensional 𝕜 U]` removed.  The `ε → 0` passage is what removes
the pole penalty; no uniform separation from `π/4` is assumed at any point. -/
theorem sum_absDoubleAngleTangent_le_of_invariantSubspace
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (S : Finset ℕ) :
    (b - a) * ∑ n ∈ S, absDoubleAngleTangent (approximationSingularValue n T) ≤
      2 * kyFanApproximationGauge S.card H := by
  have hd : 0 < b - a := by linarith
  set E₀ : ℝ := approximatePairErrorCoefficient A H T with hE₀
  set Ctot : ℝ := branchFreeTotalErrorCoefficient A H T (b - a) with hCtot
  have hE₀0 : 0 ≤ E₀ := approximatePairErrorCoefficient_nonneg A H T
  have hCtot0 : 0 ≤ Ctot := branchFreeTotalErrorCoefficient_nonneg A H T hd.le
  refine le_of_forall_pos_le_add ?_
  intro η hη
  -- pick `ε` small enough for both the smallness hypothesis and the target `η`
  set D : ℝ := (S.card : ℝ) * Ctot + 1 with hD
  have hD0 : 0 < D := by
    have : (0 : ℝ) ≤ (S.card : ℝ) * Ctot := by positivity
    rw [hD]; linarith
  set ε : ℝ := min (1 / 2) (min (η / D) ((b - a) / (4 * (E₀ + 1)))) with hεdef
  have hE₀1 : 0 < E₀ + 1 := by linarith
  have hε0 : 0 < ε := by
    rw [hεdef]
    refine lt_min (by norm_num) (lt_min (div_pos hη hD0) ?_)
    positivity
  have hεhalf : ε ≤ 1 / 2 := min_le_left _ _
  have hεD : ε ≤ η / D := le_trans (min_le_right _ _) (min_le_left _ _)
  have hεgap : ε ≤ (b - a) / (4 * (E₀ + 1)) :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hsmall : E₀ * ε ≤ (b - a) / 4 := by
    have h1 : E₀ * ε ≤ E₀ * ((b - a) / (4 * (E₀ + 1))) :=
      mul_le_mul_of_nonneg_left hεgap hE₀0
    refine h1.trans ?_
    have hkey : E₀ * ((b - a) / (4 * (E₀ + 1))) = (b - a) / 4 * (E₀ / (E₀ + 1)) := by
      field_simp
    rw [hkey]
    have hfrac : E₀ / (E₀ + 1) ≤ 1 := by
      rw [div_le_one hE₀1]; linarith
    nlinarith [hfrac, hd]
  have hmain := sum_absDoubleAngleTangent_le_add_error hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hab S hε0 hεhalf hsmall
  refine hmain.trans ?_
  have herr : (S.card : ℝ) * (Ctot * ε) ≤ η := by
    have h1 : (S.card : ℝ) * (Ctot * ε) = ((S.card : ℝ) * Ctot) * ε := by ring
    rw [h1]
    have h2 : ((S.card : ℝ) * Ctot) * ε ≤ ((S.card : ℝ) * Ctot) * (η / D) := by
      refine mul_le_mul_of_nonneg_left hεD ?_
      positivity
    refine h2.trans ?_
    rw [mul_div_assoc', div_le_iff₀ hD0]
    have : (0 : ℝ) ≤ η := hη.le
    nlinarith [hCtot0, Nat.cast_nonneg (α := ℝ) S.card]
  linarith

/-- **Representative packaging of the branch-free Ky Fan root, arbitrary trial
subspace.**  Any operator whose approximation numbers are a *rearrangement* of
the branch-free double-angle tangents of the graph-coordinate approximation
numbers obeys every prefix bound.

This is `kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace` with
`[FiniteDimensional 𝕜 U]` removed.  The rearrangement `π` is what makes the
statement honest: approximation numbers are antitone while `t ↦ 2t/|1 - t²|` is
not monotone across the quarter turn, and a unitarily invariant norm sees only
the multiset of singular values. -/
theorem kyFan_absTanTwoTheta_le_of_invariantSubspace
    {E₂ F₂ : Type u}
    [NormedAddCommGroup E₂] [InnerProductSpace ℂ E₂] [CompleteSpace E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace ℂ F₂] [CompleteSpace F₂]
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (tanTwoTheta : E₂ →L[ℂ] F₂) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      absDoubleAngleTangent (approximationSingularValue n T))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k tanTwoTheta ≤
      2 * kyFanApproximationGauge k H := by
  classical
  set S : Finset ℕ := (Finset.range k).image π.symm with hSdef
  have hScard : S.card = k := by
    rw [hSdef, Finset.card_image_of_injective _ π.symm.injective,
      Finset.card_range]
  have hgauge : kyFanApproximationGauge k tanTwoTheta =
      ∑ n ∈ S, absDoubleAngleTangent (approximationSingularValue n T) := by
    rw [hSdef, Finset.sum_image (fun x _ y _ h => π.symm.injective h)]
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← htan (π.symm j), Equiv.apply_symm_apply]
    rfl
  have h := sum_absDoubleAngleTangent_le_of_invariantSubspace hA hH hAU hHU
    hHUperp hTmem hTzero hUb hUa hinv hab S
  rw [hScard] at h
  rw [hgauge]
  exact h

/-- **Davis--Kahan 1970, the unrestricted `tan 2Θ` theorem, every Fan-dominant
unitary-invariant ideal, arbitrary Hilbert space and arbitrary trial
subspace.**

If the fully off-diagonal perturbation `H` belongs to the ideal, then so does
every branch-free `tan 2Θ` representative, and
`(b - a) · N(tan 2Θ) ≤ 2 · N(H)`.

**No branch is selected and none is assumed** -- there is no hypothesis
`approximationSingularValue 0 T < 1` -- and **no dimension hypothesis is made**:
neither the ambient space nor the trial subspace is assumed
finite-dimensional. -/
theorem absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_invariantSubspace
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[ℂ] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  have hδ : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k,
      (b - a) / 2 * kyFanApproximationGauge k tanTwoTheta ≤
        kyFanApproximationGauge k H := by
    intro k
    have h := kyFan_absTanTwoTheta_le_of_invariantSubspace hA hH hAU hHU
      hHUperp hTmem hTzero hUb hUa hinv hab tanTwoTheta π htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

end Main

end

end DavisKahan.TanTwoTheta
end TauCeti
