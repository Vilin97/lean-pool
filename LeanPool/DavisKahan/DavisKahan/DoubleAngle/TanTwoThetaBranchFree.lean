/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFan

/-!
# The unrestricted, branch-free `tan 2Θ` theorem

Davis and Kahan's Section 2 `tan 2Θ` theorem places **no** restriction on
which side of the quarter turn the principal angles lie.  Section 8 says so
explicitly: "The double-angle conclusions also allow angles close to `π/2`.
... The explanation is that the double-angle theorems imposed no special
choice of the reducing subspace `QH` of `A + H`."  The quarter-acute
conclusion `Θ < π/4` is Theorem 8.1's, earned from the *extra* hypothesis
that the two subspaces are the spectral subspaces of `A` and `A + H` for the
same interval.

`DavisKahan/DoubleAngle/TanTwoThetaKyFan.lean` proves the theorem under the
selected-branch hypothesis `T.singularValues 0 < 1`.  This module removes the
mathematical need for it.

## The printed argument, and where the branch enters

The paired-singular-vector computation of equation (7.6) is exact and
branch-free; it is `paired_singularVector_gap_inequality`:

`(b - a) · tⱼ ≤ (1 - tⱼ²) · Re ⟪vⱼ, H uⱼ⟫`,   `tⱼ = tan θⱼ`.

Only the *last* step of the selected-branch proof divides by `1 - tⱼ²`, and
that is where the branch is silently chosen.  Davis and Kahan instead make
two moves, both of which this module carries out.

1. **`cos 2θⱼ ≠ 0` follows from the gap.**  If `tⱼ = 1` the inequality reads
   `(b - a) ≤ 0`, contradicting the spectral gap `a < b`.  So no principal
   angle is exactly `π/4` and `|1 - tⱼ²| > 0`; this is
   `singularValue_ne_one`.

2. **The sign is chosen according to `cos 2θⱼ`.**  Dividing by `|1 - tⱼ²|`
   rather than by `1 - tⱼ²` and bounding `(1 - tⱼ²)·c ≤ |1 - tⱼ²|·|c|` gives

   `(b - a) · |tan 2θⱼ| ≤ 2 |Re ⟪vⱼ, H uⱼ⟫|`,

   with `|tan 2θ| = 2 tan θ / |1 - tan² θ|`, valid on both sides of `π/4`.

The Ky Fan passage then needs the *magnitude* form of the variational bound,
`TauCeti.sum_abs_le_kyFanSum_of_orthonormal`,
which rephases each left singular vector by the sign of `cos 2θⱼ`.  That
rephasing is the formal content of the paper's "choose the sign according to
`cos 2θⱼ`".

## Why the conclusion is stated up to a rearrangement

`t ↦ 2t/|1 - t²|` increases on `[0, 1)` and decreases on `(1, ∞)`, so along
the antitone singular-value list of the graph coordinate the branch-free
double-angle tangents are **not** antitone.  A `tan 2Θ` representative
therefore carries those numbers *as a multiset*, not in index order.  This is
not a weakening: a unitarily invariant norm sees only the multiset of singular
values, and the paper's `tan 2Θ` is the functional calculus of the angle
operator, whose singular values are exactly the sorted `|tan 2θⱼ|`.

Accordingly the branch-free Ky Fan root here is proved for an **arbitrary**
finite index set (`sum_absDoubleAngleTangent_le`), which is strictly stronger
than a prefix statement and is what a rearranged representative needs.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open TauCeti.DavisKahan.TanTwoTheta
open Module _root_.TauCeti.LinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

section Scalar

variable {A H T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  {a b : ℝ}

/-- **`cos 2θⱼ ≠ 0` from the spectral gap.**  Davis and Kahan's first move
after equation (7.6): a principal angle of exactly `π/4` would force the gap
to close, so the double-angle cosine never vanishes and `tan 2Θ` is
everywhere finite -- even though no branch has been selected. -/
theorem singularValue_ne_one
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    {i : Fin (finrank 𝕜 E)} (hi : T.singularValues (i : ℕ) ≠ 0) :
    T.singularValues (i : ℕ) ≠ 1 := by
  intro hone
  have hkey := paired_singularVector_gap_inequality hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hi
  rw [hone] at hkey
  simp only [one_pow, sub_self, zero_mul, mul_one] at hkey
  linarith

/-- **The branch-free paired-singular-vector inequality.**

For each singular pair of the graph coordinate with nonzero singular value,
the *magnitude* of the double-angle tangent is controlled by the magnitude of
the matched coefficient of the perturbation, with the sharp constant two, and
with no hypothesis on which side of the quarter turn the angle lies. -/
theorem absDoubleAngleTangent_scalar
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    {i : Fin (finrank 𝕜 E)} (hi : T.singularValues (i : ℕ) ≠ 0) :
    (b - a) * absDoubleAngleTangent (T.singularValues (i : ℕ)) ≤
      2 * |RCLike.re ⟪leftSingularVector T i, H (rightSingularBasis T i)⟫_𝕜| := by
  set t : ℝ := T.singularValues (i : ℕ) with hts
  set c : ℝ :=
    RCLike.re ⟪leftSingularVector T i, H (rightSingularBasis T i)⟫_𝕜 with hcs
  have ht0 : 0 < t := lt_of_le_of_ne (T.singularValues_nonneg _) (Ne.symm hi)
  have hkey := paired_singularVector_gap_inequality hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hi
  rw [← hts, ← hcs] at hkey
  -- the gap forbids the quarter-turn pole
  have hne : t ≠ 1 :=
    singularValue_ne_one hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab hi
  have habs : (0 : ℝ) < |1 - t ^ 2| := by
    refine abs_pos.mpr ?_
    intro hzero
    exact hne (by nlinarith)
  -- the sign of the matched coefficient follows the sign of `cos 2θ`
  have hsign : (1 - t ^ 2) * c ≤ |1 - t ^ 2| * |c| := by
    calc (1 - t ^ 2) * c ≤ |(1 - t ^ 2) * c| := le_abs_self _
      _ = |1 - t ^ 2| * |c| := abs_mul _ _
  rw [absDoubleAngleTangent, show (b - a) * (2 * t / |1 - t ^ 2|) =
    ((b - a) * (2 * t)) / |1 - t ^ 2| from by ring, div_le_iff₀ habs]
  nlinarith

end Scalar

section KyFan

open UnitarilyInvariantSeminorm

variable {A H T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  {a b : ℝ}

/-- Summed branch-free form over any set of participating indices with
nonzero singular values.  The sign choice of the printed proof is carried by
the magnitude form of the Ky Fan variational bound. -/
private theorem sum_absDoubleAngleTangent_le_of_ne_zero
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (S : Finset (Fin (finrank 𝕜 E)))
    (hSne : ∀ x ∈ S, T.singularValues (x : ℕ) ≠ 0) :
    (b - a) * ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ)) ≤
      2 * kyFanSum S.card H := by
  classical
  have hmn : S.card ≤ finrank 𝕜 E := by
    calc S.card ≤ Finset.univ.card := Finset.card_le_univ S
      _ = finrank 𝕜 E := by rw [Finset.card_univ, Fintype.card_fin]
  let e := S.orderIsoOfFin rfl
  have hSprop : ∀ j : Fin S.card,
      T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ) ≠ 0 :=
    fun j => hSne _ (e j).2
  have hecoe_inj : Function.Injective
      (fun j : Fin S.card => (e j : Fin (finrank 𝕜 E))) :=
    fun x y h => e.injective (Subtype.ext h)
  have huu : Orthonormal 𝕜
      (fun j : Fin S.card => rightSingularBasis T (e j : Fin (finrank 𝕜 E))) :=
    (rightSingularBasis T).orthonormal.comp _ hecoe_inj
  have hww : Orthonormal 𝕜
      (fun j : Fin S.card => leftSingularVector T (e j : Fin (finrank 𝕜 E))) :=
    (orthonormal_leftSingularVector_subtype T).comp
      (fun j : Fin S.card => (⟨(e j : Fin (finrank 𝕜 E)), hSprop j⟩ :
        {j : Fin (finrank 𝕜 E) // T.singularValues j ≠ 0}))
      (fun x y h => hecoe_inj (congrArg
        (fun z : {j : Fin (finrank 𝕜 E) // T.singularValues j ≠ 0} =>
          (z : Fin (finrank 𝕜 E))) h))
  have hscalar : ∀ j : Fin S.card,
      (b - a) / 2 * absDoubleAngleTangent
          (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) ≤
        |RCLike.re ⟪leftSingularVector T (e j : Fin (finrank 𝕜 E)),
          H (rightSingularBasis T (e j : Fin (finrank 𝕜 E)))⟫_𝕜| := by
    intro j
    have h := absDoubleAngleTangent_scalar hA hH hAU hHU hHUperp hTmem hTzero
      hUb hUa hinv hab (hSprop j)
    linarith
  have hwitness := sum_abs_le_kyFanSum_of_orthonormal
    (A := H) hmn hww huu hscalar
  have hsum : ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ)) =
      ∑ j : Fin S.card, absDoubleAngleTangent
        (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) := by
    rw [← Finset.sum_coe_sort S
      (fun x : Fin (finrank 𝕜 E) => absDoubleAngleTangent
        (T.singularValues (x : ℕ)))]
    exact (Equiv.sum_comp e.toEquiv
      (fun x : {x // x ∈ S} => absDoubleAngleTangent
        (T.singularValues ((x : Fin (finrank 𝕜 E)) : ℕ)))).symm
  calc (b - a) * ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ))
      = 2 * ∑ j : Fin S.card, (b - a) / 2 * absDoubleAngleTangent
          (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) := by
        rw [hsum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 2 * kyFanSum S.card H := by linarith

/-- **The branch-free Ky Fan root of the `tan 2Θ` theorem**
(Davis--Kahan 1970, Section 7, equation (7.6) and the following
paired-singular-vector argument, with the printed sign choice rather than a
selected branch).

Stated for an *arbitrary* finite index set rather than a prefix, because the
branch-free double-angle tangents are not monotone along the singular-value
list: a `tan 2Θ` representative carries them as a multiset.  Every prefix
statement is the special case of an initial segment, and the general form is
what a rearranged representative consumes. -/
theorem sum_absDoubleAngleTangent_le
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (S : Finset (Fin (finrank 𝕜 E))) :
    (b - a) * ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ)) ≤
      2 * kyFanSum S.card H := by
  classical
  set S' : Finset (Fin (finrank 𝕜 E)) :=
    S.filter (fun j => T.singularValues (j : ℕ) ≠ 0) with hS'
  have hsub : S' ⊆ S := Finset.filter_subset _ _
  have hSne : ∀ x ∈ S', T.singularValues (x : ℕ) ≠ 0 := by
    intro x hx
    rw [hS', Finset.mem_filter] at hx
    exact hx.2
  have hLHS : ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ)) =
      ∑ x ∈ S', absDoubleAngleTangent (T.singularValues (x : ℕ)) := by
    rw [hS']
    refine (Finset.sum_filter_of_ne ?_).symm
    intro x _ hx hzero
    rw [hzero, absDoubleAngleTangent_zero] at hx
    exact hx rfl
  have hmono : kyFanSum S'.card H ≤ kyFanSum S.card H := by
    unfold kyFanSum
    rw [Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) S'.card,
      Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) S.card]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) (Finset.card_le_card hsub)))
      fun i _ _ => H.singularValues_nonneg i
  have hcore := sum_absDoubleAngleTangent_le_of_ne_zero hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hab S' hSne
  rw [hLHS]
  linarith

/-- **Davis--Kahan 1970, the unrestricted `tan 2Θ` theorem, every rectangular
unitarily invariant norm** (finite-dimensional graph-coordinate form).

`(b - a) · N (tan 2Θ) ≤ 2 · N (H)` where `tan 2Θ` is *any* operator whose
singular values are the branch-free double-angle tangents
`2 tⱼ / |1 - tⱼ²|` of the principal angles between `U` and the perturbed
invariant graph subspace, in any order.

**No branch is selected and none is assumed.**  There is no hypothesis
`T.singularValues 0 < 1`; the perturbed subspace may make angles arbitrarily
close to `π/2` with `U`, exactly as the paper permits. -/
theorem absTanTwoTheta0_offDiagonal_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (tanTwoTheta : E →ₗ[𝕜] E) (σ : Equiv.Perm (Fin (finrank 𝕜 E)))
    (htan : ∀ j : Fin (finrank 𝕜 E),
      tanTwoTheta.singularValues (σ j : ℕ) =
        absDoubleAngleTangent (T.singularValues (j : ℕ))) :
    (b - a) * N tanTwoTheta ≤ 2 * N H := by
  classical
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hkey : ∀ k, k ≤ finrank 𝕜 E →
      (b - a) * kyFanSum k tanTwoTheta ≤
        2 * kyFanSum k H := by
    intro k hk
    set P : Finset (Fin (finrank 𝕜 E)) :=
      Finset.univ.filter (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < k) with hP
    set S : Finset (Fin (finrank 𝕜 E)) := P.image σ.symm with hS
    have hScard : S.card ≤ k := by
      rw [hS, Finset.card_image_of_injective _ σ.symm.injective]
      have hmaps : ∀ x ∈ P, (x : ℕ) ∈ Finset.range k := by
        intro x hx
        rw [hP, Finset.mem_filter] at hx
        exact Finset.mem_range.mpr hx.2
      calc P.card ≤ (Finset.range k).card :=
          Finset.card_le_card_of_injOn (fun x => (x : ℕ)) hmaps
            fun x _ y _ h => Fin.val_injective h
        _ = k := Finset.card_range k
    have hmono : kyFanSum S.card H ≤ kyFanSum k H := by
      unfold kyFanSum
      rw [Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) S.card,
        Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) k]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) hScard))
        fun i _ _ => H.singularValues_nonneg i
    have hLHS : kyFanSum k tanTwoTheta =
        ∑ x ∈ S, absDoubleAngleTangent (T.singularValues (x : ℕ)) := by
      have h1 : kyFanSum k tanTwoTheta =
          ∑ x ∈ P, tanTwoTheta.singularValues (x : ℕ) := by
        unfold kyFanSum
        rw [hP]
        exact (sum_filter_lt_eq_sum_fin (n := finrank 𝕜 E) hk
          (fun j => tanTwoTheta.singularValues j)).symm
      rw [h1, hS, Finset.sum_image (fun x _ y _ h => σ.symm.injective h)]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← htan (σ.symm x), Equiv.apply_symm_apply]
    have hcore := sum_absDoubleAngleTangent_le hA hH hAU hHU hHUperp hTmem
      hTzero hUb hUa hinv hab S
    rw [hLHS]
    linarith
  have hprefix : ∀ k,
      kyFanSum k (((b - a : ℝ) : 𝕜) • tanTwoTheta) ≤
        kyFanSum k (((2 : ℝ) : 𝕜) • H) := by
    intro k
    rw [kyFanSum_real_smul k tanTwoTheta hba,
      kyFanSum_real_smul k H (by norm_num : (0 : ℝ) ≤ 2)]
    by_cases hk : k ≤ finrank 𝕜 E
    · exact hkey k hk
    · have hk' : finrank 𝕜 E ≤ k := Nat.le_of_not_ge hk
      rw [TauCeti.kyFanSum_eq_of_finrank_le hk' tanTwoTheta,
        TauCeti.kyFanSum_eq_of_finrank_le hk' H]
      exact hkey (finrank 𝕜 E) le_rfl
  have hN := N.apply_le_of_kyFanSum_le hprefix
  rw [N.smul_eq, N.smul_eq] at hN
  have hnorm1 : ‖(((b - a : ℝ)) : 𝕜)‖ = b - a := by
    rw [RCLike.norm_ofReal]
    exact abs_of_nonneg hba
  have hnorm2 : ‖(((2 : ℝ)) : 𝕜)‖ = 2 := by
    rw [RCLike.norm_ofReal]
    norm_num
  rw [hnorm1, hnorm2] at hN
  exact hN

end KyFan

end DavisKahan.FiniteDimensional
end TauCeti
