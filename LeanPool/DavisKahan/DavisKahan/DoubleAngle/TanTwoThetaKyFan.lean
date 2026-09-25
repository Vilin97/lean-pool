/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.ScalarDoubleAngleTangent
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm

/-!
# The `tan 2Θ` theorem for every unitarily invariant norm

This module certifies the arbitrary-unitarily-invariant-norm scope of the
Davis--Kahan `tan 2Θ` theorem (Section 7, equation (7.6) and the following
paired-singular-vector argument) in the finite-dimensional graph-coordinate
formulation.

## Setting

`A` is symmetric with an invariant subspace `U`; its quadratic form is at
least `b` on `U` and at most `a` on `Uᗮ`.  The symmetric perturbation `H` is
fully off-diagonal: it maps `U` into `Uᗮ` and `Uᗮ` into `U`.  The perturbed
invariant subspace is presented as the graph of the coordinate operator `T`
(supported on `U`, valued in `Uᗮ`): the hypothesis `hinv` states that
`A + H` maps every graph vector `x + T x` to another graph vector.  The
singular values of `T` are the tangents `tan θⱼ` of the principal angles
between `U` and the graph; quarter-acuteness is the hypothesis
`T.singularValues 0 < 1`.

## The paired-singular-vector argument

For a singular pair `T u = t • v`, `T† v = t • u` with `t ≠ 0`, the vector
`u + T u` lies on the graph, and sandwiching the invariance relation between
`v` and `u` yields the exact scalar identity

`⟪v, H u⟫ + t ⟪v, A v⟫ = t ⟪u, A u⟫ + t² ⟪u, H v⟫`.

Off-diagonality kills every other block, the form bounds give
`(b - a) t ≤ (1 - t²) re ⟪v, H u⟫`, and hence

`(b - a) · tan 2θ = (b - a) · 2t/(1 - t²) ≤ 2 re ⟪v, H u⟫`.

Summing over the leading singular pairs and applying the Ky Fan variational
bound `∑ re ⟪vⱼ, H uⱼ⟫ ≤ ∑ σⱼ(H)` gives every Ky Fan prefix inequality, and
Fan dominance upgrades this to every rectangular unitarily invariant norm:

`(b - a) · N (tan 2Θ₀) ≤ 2 · N (H)`,

where `tan 2Θ₀` is any operator whose singular values are the double-angle
tangents `2 σⱼ(T)/(1 - σⱼ(T)²)`, exactly the paper's representative freedom.

Numerical remark: the pointwise inequality
`(b - a) · tan 2θⱼ ≤ 2 σⱼ(H)` is FALSE in general (a rank-deficient
off-diagonal perturbation can tilt more principal angles than its rank), so
the Ky Fan summation is essential, not a convenience.

This module lives in the double-angle production directory; it is
finite-dimensional because it consumes the intrinsic singular-system layer.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan.FiniteDimensional

open TauCeti.DavisKahan.TanTwoTheta
open Module _root_.TauCeti.LinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

omit [FiniteDimensional 𝕜 E] in
/-- A symmetric operator with an invariant subspace leaves the orthogonal
complement invariant. -/
theorem apply_mem_orthogonal_of_isSymmetric
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U : Submodule 𝕜 E}
    (hAU : ∀ x ∈ U, A x ∈ U) {v : E} (hv : v ∈ Uᗮ) : A v ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  rw [← hA z v]
  exact (Submodule.mem_orthogonal U v).mp hv (A z) (hAU z hz)

/-- The adjoint of an operator vanishing on `Uᗮ` takes values in `U`. -/
theorem adjoint_apply_mem_of_orthogonal_zero
    {T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hTzero : ∀ x ∈ Uᗮ, T x = 0) (y : E) : T.adjoint y ∈ U := by
  rw [← Submodule.orthogonal_orthogonal U, Submodule.mem_orthogonal]
  intro w hw
  rw [LinearMap.adjoint_inner_right, hTzero w hw, inner_zero_left]

/-- A right singular vector of the graph coordinate with nonzero singular
value lies in `U`. -/
theorem rightSingularBasis_mem_of_singularValue_ne_zero
    {T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    (hTzero : ∀ x ∈ Uᗮ, T x = 0) {i : Fin (finrank 𝕜 E)}
    (hi : T.singularValues (i : ℕ) ≠ 0) : rightSingularBasis T i ∈ U := by
  have hσ2 : (((T.singularValues (i : ℕ) : ℝ) ^ 2 : ℝ) : 𝕜) ≠ 0 :=
    RCLike.ofReal_ne_zero.mpr (pow_ne_zero _ hi)
  have hrepr : rightSingularBasis T i =
      (((T.singularValues (i : ℕ) : ℝ) ^ 2 : ℝ) : 𝕜)⁻¹ •
        T.adjoint (T (rightSingularBasis T i)) := by
    rw [show T.adjoint (T (rightSingularBasis T i)) =
        (T.adjoint.comp T) (rightSingularBasis T i) from rfl,
      adjointCompSelf_apply_rightSingularBasis, smul_smul,
      inv_mul_cancel₀ hσ2, one_smul]
  rw [hrepr]
  exact Submodule.smul_mem _ _ (adjoint_apply_mem_of_orthogonal_zero hTzero _)

/-- Left singular vectors of the graph coordinate lie in `Uᗮ`. -/
theorem leftSingularVector_mem_orthogonal
    {T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E}
    (hTmem : ∀ x, T x ∈ Uᗮ) (i : Fin (finrank 𝕜 E)) :
    leftSingularVector T i ∈ Uᗮ :=
  Submodule.smul_mem _ _ (hTmem _)

section Scalar

variable {A H T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  {a b : ℝ}

/-- **The paired-singular-vector inequality of equation (7.6), branch-free.**

This is the exact scalar consequence Davis and Kahan extract from sandwiching
the invariance relation between a matched singular pair of the graph
coordinate.  Written in this cleared form -- multiplied through by
`1 - tan² θⱼ` rather than divided by it -- it carries **no** hypothesis on
which side of the quarter turn the angle lies, because `1 - t²` is only ever
multiplied, never inverted.

The printed proof's two subsequent moves, namely that `cos 2θⱼ ≠ 0` follows
from the gap and that the sign of the matched coefficient is dictated by the
sign of `cos 2θⱼ`, are both read off from this single inequality; see
`DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean`. -/
theorem paired_singularVector_gap_inequality
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    {i : Fin (finrank 𝕜 E)} (hi : T.singularValues (i : ℕ) ≠ 0) :
    (b - a) * T.singularValues (i : ℕ) ≤
      (1 - T.singularValues (i : ℕ) ^ 2) *
        RCLike.re ⟪leftSingularVector T i, H (rightSingularBasis T i)⟫_𝕜 := by
  set t : ℝ := T.singularValues (i : ℕ) with hts
  set u : E := rightSingularBasis T i with hus
  set v : E := leftSingularVector T i with hvs
  have ht0 : 0 < t := lt_of_le_of_ne (T.singularValues_nonneg _) (Ne.symm hi)
  have humem : u ∈ U := rightSingularBasis_mem_of_singularValue_ne_zero hTzero hi
  have hvmem : v ∈ Uᗮ := leftSingularVector_mem_orthogonal hTmem i
  have hunorm : ‖u‖ = 1 := (rightSingularBasis T).orthonormal.norm_eq_one i
  have hvnorm : ‖v‖ = 1 :=
    (orthonormal_leftSingularVector_subtype T).norm_eq_one ⟨i, hi⟩
  have hTu : T u = ((t : ℝ) : 𝕜) • v :=
    apply_rightSingularBasis_eq_smul_leftSingularVector T i
  have hTav : T.adjoint v = ((t : ℝ) : 𝕜) • u :=
    adjoint_apply_leftSingularVector T hi
  have hzw : ∀ z ∈ U, ∀ w ∈ Uᗮ, ⟪z, w⟫_𝕜 = 0 := fun z hz w hw =>
    (Submodule.mem_orthogonal U w).mp hw z hz
  have hwz : ∀ w ∈ Uᗮ, ∀ z ∈ U, ⟪w, z⟫_𝕜 = 0 := fun w hw z hz =>
    (Submodule.mem_orthogonal' U w).mp hw z hz
  obtain ⟨y, hyU, hy⟩ := hinv u humem
  -- sandwich the invariance relation between `v` and `u`
  have hmain : ⟪v, (A + H) (u + T u)⟫_𝕜 =
      ((t : ℝ) : 𝕜) * ⟪u, (A + H) (u + T u)⟫_𝕜 := by
    simp only [hy, inner_add_right, inner_add_right, hwz v hvmem y hyU, zero_add,
      hzw u humem (T y) (hTmem y), add_zero, ← LinearMap.adjoint_inner_left,
      hTav, inner_smul_left, RCLike.conj_ofReal]
  -- expand both sides through off-diagonality
  have hAv : A v ∈ Uᗮ := apply_mem_orthogonal_of_isSymmetric hA hAU hvmem
  have hexpL : ⟪v, (A + H) (u + T u)⟫_𝕜 =
      ⟪v, H u⟫_𝕜 + ((t : ℝ) : 𝕜) * ⟪v, A v⟫_𝕜 := by
    simp only [hTu, LinearMap.add_apply, map_add, map_add, map_smul, map_smul,
      inner_add_right, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, hwz v hvmem (A u) (hAU u humem),
      hwz v hvmem (H v) (hHUperp v hvmem)]
    ring
  have hexpR : ⟪u, (A + H) (u + T u)⟫_𝕜 =
      ⟪u, A u⟫_𝕜 + ((t : ℝ) : 𝕜) * ⟪u, H v⟫_𝕜 := by
    simp only [hTu, LinearMap.add_apply, map_add, map_add, map_smul, map_smul,
      inner_add_right, inner_add_right, inner_add_right, inner_smul_right,
      inner_smul_right, hzw u humem (A v) hAv,
      hzw u humem (H u) (hHU u humem)]
    ring
  rw [hexpL, hexpR] at hmain
  -- take real parts
  have hre := congrArg RCLike.re hmain
  simp only [map_add, RCLike.re_ofReal_mul] at hre
  -- the two mixed coefficients agree in real part
  have hHc : RCLike.re ⟪u, H v⟫_𝕜 = RCLike.re ⟪v, H u⟫_𝕜 := by
    rw [← hH u v]
    exact inner_re_symm (𝕜 := 𝕜) (H u) v
  -- form bounds at the two unit vectors
  have hAuu : b ≤ RCLike.re ⟪u, A u⟫_𝕜 := by
    have h := hUb u humem
    rw [hunorm] at h
    rw [← hA u u]
    simpa using h
  have hAvv : RCLike.re ⟪v, A v⟫_𝕜 ≤ a := by
    have h := hUa v hvmem
    rw [hvnorm] at h
    rw [← hA v v]
    simpa using h
  rw [hHc] at hre
  set c : ℝ := RCLike.re ⟪v, H u⟫_𝕜 with hcs
  nlinarith [mul_le_mul_of_nonneg_left hAvv ht0.le,
    mul_le_mul_of_nonneg_left hAuu ht0.le]

/-- **The paired-singular-vector scalar inequality of equation (7.6).**
For each singular pair of the graph coordinate with nonzero singular value,
the double-angle tangent is controlled by the matched diagonal coefficient of
the perturbation.

This is the *selected-branch* reading: the hypothesis `hT1` places every angle
strictly inside the acute quarter, so `1 - t²` is positive and the cleared
inequality `paired_singularVector_gap_inequality` may be divided through.  The
unrestricted printed theorem is in
`DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean`. -/
theorem doubleAngleTangent_scalar
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    {i : Fin (finrank 𝕜 E)} (hi : T.singularValues (i : ℕ) ≠ 0) :
    (b - a) * doubleAngleTangent (T.singularValues (i : ℕ)) ≤
      2 * RCLike.re ⟪leftSingularVector T i, H (rightSingularBasis T i)⟫_𝕜 := by
  set t : ℝ := T.singularValues (i : ℕ) with hts
  have ht0 : 0 < t := lt_of_le_of_ne (T.singularValues_nonneg _) (Ne.symm hi)
  have ht1 : t < 1 :=
    lt_of_le_of_lt (T.singularValues_antitone (Nat.zero_le (i : ℕ))) hT1
  have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have hkey := paired_singularVector_gap_inequality hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hi
  rw [← hts] at hkey
  unfold doubleAngleTangent
  rw [show (b - a) * (2 * t / (1 - t ^ 2)) =
    ((b - a) * (2 * t)) / (1 - t ^ 2) from by ring, div_le_iff₀ h1t]
  nlinarith

end Scalar

section KyFan

open UnitarilyInvariantSeminorm

variable {A H T : E →ₗ[𝕜] E} {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  {a b : ℝ}

/-- Summed form of the scalar inequality over any set of participating
indices with nonzero singular values. -/
private theorem sum_doubleAngleTangent_le_of_ne_zero
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    (S : Finset (Fin (finrank 𝕜 E)))
    (hSne : ∀ x ∈ S, T.singularValues (x : ℕ) ≠ 0) :
    (b - a) * ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) ≤
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
      (b - a) / 2 * doubleAngleTangent
          (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) ≤
        RCLike.re ⟪leftSingularVector T (e j : Fin (finrank 𝕜 E)),
          H (rightSingularBasis T (e j : Fin (finrank 𝕜 E)))⟫_𝕜 := by
    intro j
    have h := doubleAngleTangent_scalar hA hH hAU hHU hHUperp hTmem hTzero
      hUb hUa hinv hT1 (hSprop j)
    linarith
  have hwitness := sum_le_kyFanSum_of_orthonormal
    (A := H) hmn hww huu hscalar
  have hsum : ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) =
      ∑ j : Fin S.card, doubleAngleTangent
        (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) := by
    rw [← Finset.sum_coe_sort S
      (fun x : Fin (finrank 𝕜 E) => doubleAngleTangent
        (T.singularValues (x : ℕ)))]
    exact (Equiv.sum_comp e.toEquiv
      (fun x : {x // x ∈ S} => doubleAngleTangent
        (T.singularValues ((x : Fin (finrank 𝕜 E)) : ℕ)))).symm
  calc (b - a) * ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ))
      = 2 * ∑ j : Fin S.card, (b - a) / 2 * doubleAngleTangent
          (T.singularValues ((e j : Fin (finrank 𝕜 E)) : ℕ)) := by
        rw [hsum, Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ 2 * kyFanSum S.card H := by linarith

private theorem kyFan_tanTwoTheta0_offDiagonal_le_of_le_finrank
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    (tanTwoTheta0 : E →ₗ[𝕜] E)
    (htan : ∀ j : ℕ, tanTwoTheta0.singularValues j =
      doubleAngleTangent (T.singularValues j))
    {k : ℕ} (hk : k ≤ finrank 𝕜 E) :
    (b - a) * kyFanSum k tanTwoTheta0 ≤
      2 * kyFanSum k H := by
  classical
  set S : Finset (Fin (finrank 𝕜 E)) := Finset.univ.filter
    (fun j : Fin (finrank 𝕜 E) =>
      (j : ℕ) < k ∧ T.singularValues (j : ℕ) ≠ 0) with hS
  have hSne : ∀ x ∈ S, T.singularValues (x : ℕ) ≠ 0 := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact hx.2.2
  have hcard_le : S.card ≤ k := by
    have hmaps : ∀ x ∈ S, (x : ℕ) ∈ Finset.range k := by
      intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact Finset.mem_range.mpr hx.2.1
    calc S.card ≤ (Finset.range k).card :=
        Finset.card_le_card_of_injOn (fun x => (x : ℕ)) hmaps
          fun x _ y _ h => Fin.val_injective h
      _ = k := Finset.card_range k
  have hLHS : kyFanSum k tanTwoTheta0 =
      ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) := by
    have h1 : kyFanSum k tanTwoTheta0 =
        ∑ i : Fin k, doubleAngleTangent (T.singularValues (i : ℕ)) := by
      unfold kyFanSum
      exact Finset.sum_congr rfl fun i _ => htan (i : ℕ)
    have h2 := sum_filter_lt_eq_sum_fin (n := finrank 𝕜 E) hk
      (fun j => doubleAngleTangent (T.singularValues j))
    have h3 : ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) =
        ∑ x ∈ Finset.univ.filter
            (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < k),
          doubleAngleTangent (T.singularValues (x : ℕ)) := by
      rw [hS, ← Finset.filter_filter]
      refine Finset.sum_filter_of_ne ?_
      intro x _ hx hzero
      rw [hzero, doubleAngleTangent_zero] at hx
      exact hx rfl
    rw [h1, ← h2, h3]
  have hmono : kyFanSum S.card H ≤ kyFanSum k H := by
    unfold kyFanSum
    rw [Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) S.card,
      Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) k]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hcard_le))
      fun i _ _ => H.singularValues_nonneg i
  have hcore := sum_doubleAngleTangent_le_of_ne_zero hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hT1 S hSne
  rw [hLHS]
  linarith

/-- Representative-free form of the Ky Fan root: the prefix sums of the
double-angle tangents of the graph-coordinate singular values are controlled
by the singular-value prefixes of the off-diagonal perturbation.  This is the
form consumed by the infinite-dimensional compression argument. -/
theorem kyFan_doubleAngleTangent_offDiagonal_le
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    (k : ℕ) :
    (b - a) * ∑ j ∈ Finset.range k,
        doubleAngleTangent (T.singularValues j) ≤
      2 * kyFanSum k H := by
  classical
  -- reduce to `k ≤ finrank` since both sides freeze past the dimension
  suffices hcase : ∀ m : ℕ, m ≤ finrank 𝕜 E →
      (b - a) * ∑ j ∈ Finset.range m,
          doubleAngleTangent (T.singularValues j) ≤
        2 * kyFanSum m H by
    by_cases hk : k ≤ finrank 𝕜 E
    · exact hcase k hk
    · have hk' : finrank 𝕜 E ≤ k := Nat.le_of_not_ge hk
      have hsum : ∑ j ∈ Finset.range k,
          doubleAngleTangent (T.singularValues j) =
            ∑ j ∈ Finset.range (finrank 𝕜 E),
              doubleAngleTangent (T.singularValues j) := by
        refine (Finset.sum_subset
          (fun x hx => Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_range.mp hx) hk')) ?_).symm
        intro j _ hj
        have hjge : finrank 𝕜 E ≤ j := by
          by_contra hlt
          exact hj (Finset.mem_range.mpr (Nat.lt_of_not_ge hlt))
        rw [T.singularValues_of_finrank_le hjge, doubleAngleTangent_zero]
      rw [hsum, TauCeti.kyFanSum_eq_of_finrank_le hk' H]
      exact hcase (finrank 𝕜 E) le_rfl
  intro m hm
  set S : Finset (Fin (finrank 𝕜 E)) := Finset.univ.filter
    (fun j : Fin (finrank 𝕜 E) =>
      (j : ℕ) < m ∧ T.singularValues (j : ℕ) ≠ 0) with hS
  have hSne : ∀ x ∈ S, T.singularValues (x : ℕ) ≠ 0 := by
    intro x hx
    rw [hS, Finset.mem_filter] at hx
    exact hx.2.2
  have hcard_le : S.card ≤ m := by
    have hmaps : ∀ x ∈ S, (x : ℕ) ∈ Finset.range m := by
      intro x hx
      rw [hS, Finset.mem_filter] at hx
      exact Finset.mem_range.mpr hx.2.1
    calc S.card ≤ (Finset.range m).card :=
        Finset.card_le_card_of_injOn (fun x => (x : ℕ)) hmaps
          fun x _ y _ h => Fin.val_injective h
      _ = m := Finset.card_range m
  have hLHS : ∑ j ∈ Finset.range m,
      doubleAngleTangent (T.singularValues j) =
        ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) := by
    have h1 : ∑ j ∈ Finset.range m,
        doubleAngleTangent (T.singularValues j) =
          ∑ i : Fin m, doubleAngleTangent (T.singularValues (i : ℕ)) :=
      (Fin.sum_univ_eq_sum_range
        (fun j => doubleAngleTangent (T.singularValues j)) m).symm
    have h2 := sum_filter_lt_eq_sum_fin (n := finrank 𝕜 E) hm
      (fun j => doubleAngleTangent (T.singularValues j))
    have h3 : ∑ x ∈ S, doubleAngleTangent (T.singularValues (x : ℕ)) =
        ∑ x ∈ Finset.univ.filter
            (fun j : Fin (finrank 𝕜 E) => (j : ℕ) < m),
          doubleAngleTangent (T.singularValues (x : ℕ)) := by
      rw [hS, ← Finset.filter_filter]
      refine Finset.sum_filter_of_ne ?_
      intro x _ hx hzero
      rw [hzero, doubleAngleTangent_zero] at hx
      exact hx rfl
    rw [h1, ← h2, h3]
  have hmono : kyFanSum S.card H ≤ kyFanSum m H := by
    unfold kyFanSum
    rw [Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) S.card,
      Fin.sum_univ_eq_sum_range (fun i => H.singularValues i) m]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hcard_le))
      fun i _ _ => H.singularValues_nonneg i
  have hcore := sum_doubleAngleTangent_le_of_ne_zero hA hH hAU hHU hHUperp
    hTmem hTzero hUb hUa hinv hT1 S hSne
  rw [hLHS]
  linarith

/-- **The Ky Fan root of the `tan 2Θ` theorem** (Davis--Kahan 1970,
Section 7, equation (7.6) and the following paired-singular-vector
argument): every prefix sum of double-angle tangents is controlled by the
corresponding singular-value prefix of the off-diagonal perturbation, with
the sharp constant two. -/
theorem kyFan_tanTwoTheta0_offDiagonal_le
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    (tanTwoTheta0 : E →ₗ[𝕜] E)
    (htan : ∀ j : ℕ, tanTwoTheta0.singularValues j =
      doubleAngleTangent (T.singularValues j))
    (k : ℕ) :
    (b - a) * kyFanSum k tanTwoTheta0 ≤
      2 * kyFanSum k H := by
  by_cases hk : k ≤ finrank 𝕜 E
  · exact kyFan_tanTwoTheta0_offDiagonal_le_of_le_finrank hA hH hAU hHU
      hHUperp hTmem hTzero hUb hUa hinv hT1 tanTwoTheta0 htan hk
  · have hk' : finrank 𝕜 E ≤ k := Nat.le_of_not_ge hk
    rw [TauCeti.kyFanSum_eq_of_finrank_le hk' tanTwoTheta0,
      TauCeti.kyFanSum_eq_of_finrank_le hk' H]
    exact kyFan_tanTwoTheta0_offDiagonal_le_of_le_finrank hA hH hAU hHU
      hHUperp hTmem hTzero hUb hUa hinv hT1 tanTwoTheta0 htan le_rfl

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, every rectangular unitarily
invariant norm** (finite-dimensional graph-coordinate form).

`(b - a) · N (tan 2Θ₀) ≤ 2 · N (H)` for any operator `tan 2Θ₀` whose
singular values are the double-angle tangents of the principal angles
between `U` and the perturbed invariant graph subspace. -/
theorem tanTwoTheta0_offDiagonal_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hA : A.IsSymmetric) (hH : H.IsSymmetric)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a ≤ b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : T.singularValues 0 < 1)
    (tanTwoTheta0 : E →ₗ[𝕜] E)
    (htan : ∀ j : ℕ, tanTwoTheta0.singularValues j =
      doubleAngleTangent (T.singularValues j)) :
    (b - a) * N tanTwoTheta0 ≤ 2 * N H := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  have hprefix : ∀ k,
      kyFanSum k (((b - a : ℝ) : 𝕜) • tanTwoTheta0) ≤
        kyFanSum k (((2 : ℝ) : 𝕜) • H) := by
    intro k
    rw [kyFanSum_real_smul k tanTwoTheta0 hba,
      kyFanSum_real_smul k H (by norm_num : (0 : ℝ) ≤ 2)]
    exact kyFan_tanTwoTheta0_offDiagonal_le hA hH hAU hHU hHUperp hTmem
      hTzero hUb hUa hinv hT1 tanTwoTheta0 htan k
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
