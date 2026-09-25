/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.TwoProjections
-- supplies the two crossed intersections `halmosSourceDefect`/`halmosTargetDefect`, the
-- projection calculus they are described by, and `complementaryProjection_mul_projection`.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Halmos.GenericRotationPredicates
-- supplies `IsDirectRotation`, the five-field predicate whose characterisation this
-- module proves.  It lives in `TauCeti.DavisKahan`.
public import LeanPool.DavisKahan.DavisKahan.Geometry.Polar.DirectRotation

/-! # Principal Square Root -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester
-- supplies `spectraReflectionProduct`, `spectraCanonicalIntertwiner`, the operator absolute
-- value `ContinuousLinearMap.modulus` and the polar identities relating them.  That module
-- and everything beneath it are `Geometry`/`BoundedOperator` leaves and never import
-- the source layer, so this module is acyclic.

/-!
# Principal unitary square roots of the reflection product

Davis--Kahan 1970, Proposition 3.3, characterises the direct rotation between two subspaces
`U` and `V` as the *principal* unitary square root of the reflection product
`J_V J_U = spectraReflectionProduct U V`: the square root whose spectrum avoids the open left
half-plane, singled out among the square roots by the requirement that it carry the source
crossed intersection `U ⊓ Vᗮ` onto the target crossed intersection `Uᗮ ⊓ V`.

This module owns that characterisation and the block calculus it runs on.  It was extracted
from the Section 3 frontier module; the mathematics is unchanged.  The extraction is what
lets `DavisKahan/Sources/DavisKahan1970/Section3PrincipalSquareRoot.lean` -- the source-facing
home of Proposition 3.3 -- stop importing the former `DavisKahan.Section3`.

## Scope

Everything here is at the paper's arbitrary-pair scope: complex scalars, a complete space, and
**no acuteness hypothesis**.  Acuteness enters only downstream, where the principal branch is
identified with the canonical direct rotation.

## Main results

* `IsPrincipalUnitarySquareRoot`: unitary, squares to the given operator, spectrum in the
  closed right half-plane.
* `proposition3_3_principalSquareRoot_forward`: every direct rotation is such a square root,
  and carries one crossed intersection onto the other.
* `proposition3_3_principalSquareRoot_converse`: every such square root with the crossed
  mapping property is a direct rotation.
* `proposition3_3_principalSquareRoot_iff`: the two halves as a characterisation.
* `crossedDefect_image_of_unitary_sq`: the crossed mapping condition is free for any unitary
  square root that intertwines the projections.

The `BlockCalculus` section is the `U`-block bookkeeping shared with Proposition 3.1, which
stays in the frontier module and consumes it from here.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan



universe u

section BlockCalculus

/-! The block calculus, and the square identity it feeds, use no property of the
scalars beyond `RCLike`: they are projection algebra and the `star` operation.
They are stated at that generality so that the real Davis--Kahan endpoints can
use them directly rather than through complexification.  The rest of the module
is genuinely complex — it runs on the spectrum and the continuous functional
calculus. -/

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable (U V : Submodule 𝕜 H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-! ### The `U`-block calculus of a unitary intertwiner

These four identities are what both Proposition 3.1 and Proposition 3.3 run on, and they need
no acuteness.  They were originally inlined in Proposition 3.1's proof; Proposition 3.3's
forward direction needs the same seventy-five lines, so they live here once. -/

variable (T : H →L[𝕜] H)

omit [CompleteSpace H] in
/-- **Block decomposition of an operator relative to `U ⊕ Uᗮ`.** -/
theorem eq_sum_blocks (A : H →L[𝕜] H) :
    A = U.starProjection * A * U.starProjection + U.starProjection * A * (Uᗮ).starProjection
      + (Uᗮ).starProjection * A * U.starProjection
      + (Uᗮ).starProjection * A * (Uᗮ).starProjection := by
  have hone : U.starProjection + (Uᗮ).starProjection = 1 := by
    rw [show (Uᗮ).starProjection = 1 - U.starProjection from
      Submodule.starProjection_orthogonal' U]
    abel
  calc A = (U.starProjection + (Uᗮ).starProjection) * A
        * (U.starProjection + (Uᗮ).starProjection) := by rw [hone, one_mul, mul_one]
    _ = _ := by noncomm_ring

/-- **The `U`-blocks of `star T`**, for an operator whose diagonal compressions are self-adjoint
and whose crossed blocks are skew: the diagonal blocks are fixed and the off-diagonal ones are
sign-flipped. -/
theorem star_blocks_eq
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    (hcrossed : (Uᗮ).starProjection * T * U.starProjection =
      -star (U.starProjection * T * (Uᗮ).starProjection)) :
    U.starProjection * star T * U.starProjection = U.starProjection * T * U.starProjection ∧
      (Uᗮ).starProjection * star T * (Uᗮ).starProjection
        = (Uᗮ).starProjection * T * (Uᗮ).starProjection ∧
      U.starProjection * star T * (Uᗮ).starProjection
        = -(U.starProjection * T * (Uᗮ).starProjection) ∧
      (Uᗮ).starProjection * star T * U.starProjection
        = -((Uᗮ).starProjection * T * U.starProjection) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := hsource_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcomplement_sa.star_eq
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := congrArg star hcrossed
    rw [star_neg, star_star, star_mul, star_mul,
      (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    exact h
  · have h := hcrossed
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc] at h
    rw [h, neg_neg]

/-- **A direct rotation squares to the reflection product**, with no acuteness hypothesis and
at every `RCLike` field.

The reflection through `U` conjugates `star T` back to `T` -- the diagonal blocks survive and the
off-diagonal ones are negated twice -- and the intertwining turns that into `T * T = J_V J_U`. -/
theorem sq_eq_reflectionProduct
    (hunitary : T ∈ unitary (H →L[𝕜] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    (hcrossed : (Uᗮ).starProjection * T * U.starProjection =
      -star (U.starProjection * T * (Uᗮ).starProjection)) :
    T * T = V.reflectionOperator * U.reflectionOperator := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  have hRsub : U.reflectionOperator = U.starProjection - (Uᗮ).starProjection := by
    rw [reflectionOperator_eq_projection_add_projection_sub_one U,
      show (Uᗮ).starProjection = 1 - U.starProjection from
        Submodule.starProjection_orthogonal' U]
    abel
  have hkey : U.reflectionOperator * star T * U.reflectionOperator = T := by
    rw [hRsub]
    have expand : (U.starProjection - (Uᗮ).starProjection) * star T
        * (U.starProjection - (Uᗮ).starProjection)
        = U.starProjection * star T * U.starProjection
          - U.starProjection * star T * (Uᗮ).starProjection
          - (Uᗮ).starProjection * star T * U.starProjection
          + (Uᗮ).starProjection * star T * (Uᗮ).starProjection := by
      noncomm_ring
    rw [expand, e11, e12, e21, e22]
    conv_rhs => rw [eq_sum_blocks U T]
    abel
  have hTR : T * U.reflectionOperator = V.reflectionOperator * T := by
    rw [reflectionOperator_eq_projection_add_projection_sub_one U,
      reflectionOperator_eq_projection_add_projection_sub_one V,
      mul_sub, mul_add, mul_one, sub_mul, add_mul, one_mul, hintertwines]
  have hRV : V.reflectionOperator = T * U.reflectionOperator * star T := by
    have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
    calc V.reflectionOperator
        = V.reflectionOperator * (T * star T) := by rw [hTsT, mul_one]
      _ = V.reflectionOperator * T * star T := by rw [mul_assoc]
      _ = T * U.reflectionOperator * star T := by rw [← hTR]
  have hexp : V.reflectionOperator * U.reflectionOperator
      = T * (U.reflectionOperator * star T * U.reflectionOperator) := by
    rw [hRV]; noncomm_ring
  rw [hexp, hkey]

/-- **The Hermitian part of a direct rotation is twice its diagonal.**

The crossed blocks of `T` and of `star T` are negatives of one another, so they cancel in the
sum and only the diagonal survives, doubled. -/
theorem add_star_eq_two_diagonal
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    (hcrossed : (Uᗮ).starProjection * T * U.starProjection =
      -star (U.starProjection * T * (Uᗮ).starProjection)) :
    T + star T =
      U.starProjection * T * U.starProjection + U.starProjection * T * U.starProjection
        + ((Uᗮ).starProjection * T * (Uᗮ).starProjection
          + (Uᗮ).starProjection * T * (Uᗮ).starProjection) := by
  obtain ⟨e11, e22, e12, e21⟩ := star_blocks_eq U T hsource_sa hcomplement_sa hcrossed
  calc T + star T
      = (U.starProjection * T * U.starProjection + U.starProjection * T * (Uᗮ).starProjection
            + (Uᗮ).starProjection * T * U.starProjection
            + (Uᗮ).starProjection * T * (Uᗮ).starProjection)
          + (U.starProjection * star T * U.starProjection
            + U.starProjection * star T * (Uᗮ).starProjection
            + (Uᗮ).starProjection * star T * U.starProjection
            + (Uᗮ).starProjection * star T * (Uᗮ).starProjection) := by
        rw [← eq_sum_blocks U T, ← eq_sum_blocks U (star T)]
    _ = _ := by rw [e11, e12, e21, e22]; abel

end BlockCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
variable (U V : Submodule ℂ H) [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]
variable (T : H →L[ℂ] H)

/-- **A direct rotation squares to the reflection product**, at the complex
scalars and phrased with `spectraReflectionProduct`.  This is
`sq_eq_reflectionProduct`; `spectraReflectionProduct U V` *is* `J_V J_U`. -/
theorem sq_eq_spectraReflectionProduct
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection))
    (hcrossed : (Uᗮ).starProjection * T * U.starProjection =
      -star (U.starProjection * T * (Uᗮ).starProjection)) :
    T * T = spectraReflectionProduct U V :=
  sq_eq_reflectionProduct U V T hunitary hintertwines hsource_sa hcomplement_sa hcrossed

/-- A unitary principal square root of the reflection product. -/
structure IsPrincipalUnitarySquareRoot
    (A T : H →L[ℂ] H) : Prop where
  unitary_mem : T ∈ unitary (H →L[ℂ] H)
  square_eq : T * T = A
  spectrum_right_half_plane :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re

open scoped ComplexOrder in
private theorem principalSquareRoot_nonneg_sum (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hroot.unitary_mem
  have e2 : cfc (fun z : ℂ => star z) T = star T := by
    rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
  have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
    rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
      continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
  rw [e3]
  apply cfc_nonneg
  intro z hz
  have hre : 0 ≤ z.re := hroot.spectrum_right_half_plane z hz
  rw [Complex.le_def]
  refine ⟨?_, ?_⟩
  · simp only [Complex.zero_re, Complex.add_re, Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.zero_im, Complex.add_im, Complex.star_def, Complex.conj_im]
    ring

open scoped ComplexOrder in
private theorem principalSquareRoot_sum_eq_modulus (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T) :
    let A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
    T + star T = A + A := by
  let A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V)
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hroot.unitary_mem
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hroot.unitary_mem
  have hTpos := principalSquareRoot_nonneg_sum U V T hroot
  have hsqeq : (T + star T) * (T + star T) = (A + A) * (A + A) := by
    have expand : (T + star T) * (T + star T)
        = T * T + T * star T + star T * T + star T * star T := by noncomm_ring
    have hstarTT : star T * star T = star (spectraReflectionProduct U V) := by
      rw [← star_mul, hroot.square_eq]
    have expandR : (A + A) * (A + A) = A * A + A * A + A * A + A * A := by noncomm_ring
    have hAA : A * A = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
      ContinuousLinearMap.modulus_mul_self_eq_star_mul_self _
    rw [expand, hroot.square_eq, hTsT, hsTT, hstarTT, expandR, hAA]
    have hG : spectraReflectionProduct U V + 1 =
        spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [add_comm]
      exact (spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V).symm
    have hstarG : star (spectraReflectionProduct U V) + 1 =
        star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V) := by
      have h := congrArg star hG
      rwa [star_add, star_add, star_one] at h
    have hSS : spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)
        = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
          + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V :=
      spectraCanonicalIntertwiner_add_star U V
    calc spectraReflectionProduct U V + 1 + 1 + star (spectraReflectionProduct U V)
        = (spectraReflectionProduct U V + 1) + (star (spectraReflectionProduct U V) + 1) := by
          abel
      _ = (spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V)
            + (star (spectraCanonicalIntertwiner U V) + star (spectraCanonicalIntertwiner U V)) := by
          rw [hG, hstarG]
      _ = (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V))
            + (spectraCanonicalIntertwiner U V + star (spectraCanonicalIntertwiner U V)) := by
          abel
      _ = (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V)
          + (star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V) := by
          rw [hSS]
      _ = star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V
            + star (spectraCanonicalIntertwiner U V) * spectraCanonicalIntertwiner U V := by
          abel
  have h2A_nonneg : (0 : H →L[ℂ] H) ≤ A + A :=
    add_nonneg (ContinuousLinearMap.modulus_nonneg _) (ContinuousLinearMap.modulus_nonneg _)
  calc T + star T
      = CFC.sqrt ((T + star T) * (T + star T)) := (CFC.sqrt_unique rfl hTpos).symm
    _ = CFC.sqrt ((A + A) * (A + A)) := by rw [hsqeq]
    _ = A + A := CFC.sqrt_unique rfl h2A_nonneg

private theorem re_inner_nonneg_of_nonneg_sum (T : H →L[ℂ] H)
    (hTpos : (0 : H →L[ℂ] H) ≤ T + star T) :
    ∀ y : H, 0 ≤ RCLike.re ⟪T y, y⟫_ℂ := by
  intro y
  have hp := (ContinuousLinearMap.nonneg_iff_isPositive (f := (T + star T))).mp hTpos
  have hy := hp.re_inner_nonneg_left y
  rw [add_apply, inner_add_left, map_add] at hy
  have hstar : RCLike.re ⟪star T y, y⟫_ℂ = RCLike.re ⟪T y, y⟫_ℂ := by
    rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]
    exact inner_re_symm (𝕜 := ℂ) y (T y)
  rw [hstar] at hy
  linarith

open scoped ComplexOrder in
/-- Davis--Kahan 1970, Proposition 3.3, converse direction.  The crossed
intersection mapping condition selects the correct square root on the
minus-one spectral subspace. -/
theorem proposition3_3_principalSquareRoot_converse
    (T : H →L[ℂ] H)
    (hroot : IsPrincipalUnitarySquareRoot
      (spectraReflectionProduct U V) T)
    (hcross : T '' (halmosSourceDefect U V : Set H) =
      (halmosTargetDefect U V : Set H)) :
    IsDirectRotation U V T := by
  set A := ContinuousLinearMap.modulus (spectraCanonicalIntertwiner U V) with hAdef
  have hunit := hroot.unitary_mem
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunit
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunit
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunit
  -- (1) accretive: 0 ≤ T + star T
  have hTpos : (0 : H →L[ℂ] H) ≤ T + star T :=
    principalSquareRoot_nonneg_sum U V T hroot
  -- accretive quadratic form
  have haccr : ∀ y : H, 0 ≤ RCLike.re ⟪T y, y⟫_ℂ :=
    re_inner_nonneg_of_nonneg_sum T hTpos
  -- (2) T + star T = A + A
  have hkey : T + star T = A + A := principalSquareRoot_sum_eq_modulus U V T hroot
  -- (3) T * A = S
  have hTA : T * A = spectraCanonicalIntertwiner U V := by
    have h1 : T * (T + star T) = spectraCanonicalIntertwiner U V + spectraCanonicalIntertwiner U V := by
      rw [mul_add, hroot.square_eq, hTsT,
        spectraCanonicalIntertwiner_add_self_eq_one_add_reflectionProduct U V]
      abel
    rw [hkey, mul_add] at h1
    -- h1 : T * A + T * A = S + S
    have hh : (2 : ℂ) • (T * A) = (2 : ℂ) • spectraCanonicalIntertwiner U V := by
      rw [two_smul, two_smul]; exact h1
    exact smul_right_injective (H →L[ℂ] H) (two_ne_zero) hh
  -- crossed_blocks and compressions and intertwines
  have hAP : A * U.starProjection = U.starProjection * A :=
    (spectraCanonicalAbsoluteValue_commute_projection U V).eq
  -- hXA
  have hXA : (T * U.starProjection - V.starProjection * T) * A = 0 := by
    have step : T * U.starProjection * A = V.starProjection * T * A := by
      calc T * U.starProjection * A
          = T * (U.starProjection * A) := by rw [mul_assoc]
        _ = T * (A * U.starProjection) := by rw [← hAP]
        _ = (T * A) * U.starProjection := by rw [mul_assoc]
        _ = spectraCanonicalIntertwiner U V * U.starProjection := by rw [hTA]
        _ = V.starProjection * spectraCanonicalIntertwiner U V :=
            spectraCanonicalIntertwiner_mul_projection U V
        _ = V.starProjection * (T * A) := by rw [hTA]
        _ = V.starProjection * T * A := by rw [mul_assoc]
    rw [sub_mul, step, sub_self]
  -- G = -1 on source defect
  have hGneg : ∀ z, z ∈ halmosSourceDefect U V → spectraReflectionProduct U V z = -z := by
    intro z hz
    obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
    have hRU : U.reflectionOperator z = z := by
      rw [Submodule.reflectionOperator_apply, hPz]; module
    rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
    module
  -- X vanishes on ker A
  have hXker : ∀ x : H, A x = 0 → (T * U.starProjection - V.starProjection * T) x = 0 := by
    intro x hx
    have hSx : spectraCanonicalIntertwiner U V x = 0 := by
      have hn : ‖spectraCanonicalIntertwiner U V x‖ = 0 := by
        rw [← ContinuousLinearMap.norm_modulus_apply (spectraCanonicalIntertwiner U V) x, ← hAdef,
          hx, norm_zero]
      exact norm_eq_zero.mp hn
    have hSexpand : spectraCanonicalIntertwiner U V x =
        V.starProjection (U.starProjection x) + (Vᗮ).starProjection ((Uᗮ).starProjection x) := by
      change (V.starProjection * U.starProjection + (Vᗮ).starProjection * (Uᗮ).starProjection) x = _
      simp only [add_apply, mul_apply_eq_comp]
    rw [hSexpand] at hSx
    have hmemV : V.starProjection (U.starProjection x) ∈ V := V.starProjection_apply_mem _
    have hmemVc : (Vᗮ).starProjection ((Uᗮ).starProjection x) ∈ Vᗮ :=
      Vᗮ.starProjection_apply_mem _
    have hab_inner : ⟪V.starProjection (U.starProjection x),
        (Vᗮ).starProjection ((Uᗮ).starProjection x)⟫_ℂ = 0 :=
      Submodule.inner_right_of_mem_orthogonal hmemV hmemVc
    have hQPx : V.starProjection (U.starProjection x) = 0 := by
      have hself : ⟪V.starProjection (U.starProjection x), V.starProjection (U.starProjection
        x)⟫_ℂ = 0 := by
        calc ⟪V.starProjection (U.starProjection x), V.starProjection (U.starProjection x)⟫_ℂ
            = ⟪V.starProjection (U.starProjection x),
                V.starProjection (U.starProjection x)
                  + (Vᗮ).starProjection ((Uᗮ).starProjection x)⟫_ℂ
              - ⟪V.starProjection (U.starProjection x),
                (Vᗮ).starProjection ((Uᗮ).starProjection x)⟫_ℂ := by
              rw [inner_add_right]; ring
          _ = 0 := by rw [hSx, hab_inner, inner_zero_right]; ring
      exact inner_self_eq_zero.mp hself
    have hPxsource : U.starProjection x ∈ halmosSourceDefect U V := by
      refine Submodule.mem_inf.mpr ⟨U.starProjection_apply_mem x, ?_⟩
      exact (Submodule.starProjection_apply_eq_zero_iff V).mp hQPx
    have hQcPcx : (Vᗮ).starProjection ((Uᗮ).starProjection x) = 0 := by
      have := hSx
      rw [hQPx, zero_add] at this
      exact this
    have hPcxtarget : (Uᗮ).starProjection x ∈ halmosTargetDefect U V := by
      refine Submodule.mem_inf.mpr ⟨Uᗮ.starProjection_apply_mem x, ?_⟩
      have := (Submodule.starProjection_apply_eq_zero_iff Vᗮ).mp hQcPcx
      simpa using this
    -- x = Px + Pᗮx
    have hxsplit : U.starProjection x + (Uᗮ).starProjection x = x :=
      U.starProjection_add_starProjection_orthogonal x
    -- T (Px) ∈ target defect ⊆ V
    have hTPx_mem : T (U.starProjection x) ∈ halmosTargetDefect U V := by
      have : T (U.starProjection x) ∈ (halmosTargetDefect U V : Set H) := by
        rw [← hcross]
        exact Set.mem_image_of_mem T hPxsource
      exact this
    have hQTPx : V.starProjection (T (U.starProjection x)) = T (U.starProjection x) :=
      V.starProjection_eq_self_iff.mpr (mem_halmosTargetDefect.mp hTPx_mem).2
    -- T (Pᗮx) ∈ source defect ⊆ Vᗮ
    have hTPcx_mem : T ((Uᗮ).starProjection x) ∈ halmosSourceDefect U V := by
      have hmem : (Uᗮ).starProjection x ∈ (halmosTargetDefect U V : Set H) := hPcxtarget
      rw [← hcross] at hmem
      obtain ⟨z, hzsource, hzeq⟩ := hmem
      have hTz : T (T z) = spectraReflectionProduct U V z := by
        have := congrArg (fun f : H →L[ℂ] H => f z) hroot.square_eq
        simpa [mul_apply_eq_comp] using this
      have : T ((Uᗮ).starProjection x) = -z := by
        rw [← hzeq, hTz, hGneg z hzsource]
      rw [this]
      exact Submodule.neg_mem _ hzsource
    have hQTPcx : V.starProjection (T ((Uᗮ).starProjection x)) = 0 := by
      apply (Submodule.starProjection_apply_eq_zero_iff V).mpr
      exact (mem_halmosSourceDefect.mp hTPcx_mem).2
    -- assemble
    have hTx : T x = T (U.starProjection x) + T ((Uᗮ).starProjection x) := by
      rw [← map_add, hxsplit]
    change (T * U.starProjection - V.starProjection * T) x = 0
    rw [sub_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      hTx, map_add, hQTPx, hQTPcx, add_zero, sub_self]
  -- final intertwining: X = 0
  have hXeq : T * U.starProjection = V.starProjection * T := by
    have : CompleteSpace A.ker := A.isClosed_ker.completeSpace_coe
    have : A.ker.HasOrthogonalProjection := inferInstance
    have hrangeLe : A.range ≤ (T * U.starProjection - V.starProjection * T).ker := by
      rintro y ⟨z, rfl⟩
      rw [LinearMap.mem_ker]
      have := congrArg (fun f : H →L[ℂ] H => f z) hXA
      simpa [mul_apply_eq_comp] using this
    have hself : ContinuousLinearMap.adjoint A = A := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact (ContinuousLinearMap.modulus_isSelfAdjoint _).star_eq
    have horthEq : A.kerᗮ = A.range.topologicalClosure := by
      have h1 : A.rangeᗮ = A.ker := by rw [A.orthogonal_range, hself]
      calc A.kerᗮ = A.rangeᗮᗮ := by rw [h1]
        _ = A.range.topologicalClosure := Submodule.orthogonal_orthogonal_eq_closure _
    have hOrthLe : A.kerᗮ ≤ (T * U.starProjection - V.starProjection * T).ker := by
      rw [horthEq]
      exact Submodule.topologicalClosure_minimal _ hrangeLe
        (T * U.starProjection - V.starProjection * T).isClosed_ker
    have hsub : ∀ x : H, (T * U.starProjection - V.starProjection * T) x = 0 := by
      intro x
      have hsplit := A.ker.starProjection_add_starProjection_orthogonal x
      rw [← hsplit, map_add]
      have h1 : (T * U.starProjection - V.starProjection * T) (A.ker.starProjection x) = 0 := by
        apply hXker
        exact LinearMap.mem_ker.mp (A.ker.starProjection_apply_mem x)
      have h2 : (T * U.starProjection - V.starProjection * T) (A.kerᗮ.starProjection x) = 0 :=
        LinearMap.mem_ker.mp (hOrthLe (A.kerᗮ.starProjection_apply_mem x))
      rw [h1, h2, add_zero]
    have hzero : T * U.starProjection - V.starProjection * T = 0 := ContinuousLinearMap.ext hsub
    exact sub_eq_zero.mp hzero
  -- crossed_blocks
  refine
    { unitary_mem := hunit
      intertwines := hXeq
      source_compression_nonnegative := ?_
      complement_compression_nonnegative := ?_
      crossed_blocks := ?_ }
  · intro x
    have h := haccr (U.starProjection x)
    have hPTP : (U.starProjection * T * U.starProjection) x = U.starProjection (T
      (U.starProjection x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪U.starProjection x, T (U.starProjection x)⟫_ℂ
        = ⟪x, U.starProjection (T (U.starProjection x))⟫_ℂ :=
      U.starProjection_isSymmetric x (T (U.starProjection x))
    have heq : RCLike.re ⟪x, (U.starProjection * T * U.starProjection) x⟫_ℂ
        = RCLike.re ⟪T (U.starProjection x), U.starProjection x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · intro x
    have h := haccr ((Uᗮ).starProjection x)
    have hPTP : ((Uᗮ).starProjection * T * (Uᗮ).starProjection) x
        = (Uᗮ).starProjection (T ((Uᗮ).starProjection x)) := by
      simp only [mul_apply_eq_comp]
    have hsymm : ⟪(Uᗮ).starProjection x, T ((Uᗮ).starProjection x)⟫_ℂ
        = ⟪x, (Uᗮ).starProjection (T ((Uᗮ).starProjection x))⟫_ℂ :=
      Uᗮ.starProjection_isSymmetric x (T ((Uᗮ).starProjection x))
    have heq : RCLike.re ⟪x, ((Uᗮ).starProjection * T * (Uᗮ).starProjection) x⟫_ℂ
        = RCLike.re ⟪T ((Uᗮ).starProjection x), (Uᗮ).starProjection x⟫_ℂ := by
      rw [hPTP, ← hsymm]
      exact inner_re_symm (𝕜 := ℂ) _ _
    rw [heq]; exact h
  · have hcomm : Commute (T + star T) (U.starProjection) := by
      rw [hkey]
      exact (spectraCanonicalAbsoluteValue_commute_projection U V).add_left
        (spectraCanonicalAbsoluteValue_commute_projection U V)
    have hblock : (Uᗮ).starProjection * (T + star T) * U.starProjection = 0 := by
      calc (Uᗮ).starProjection * (T + star T) * U.starProjection
          = (Uᗮ).starProjection * ((T + star T) * U.starProjection) := by rw [mul_assoc]
        _ = (Uᗮ).starProjection * (U.starProjection * (T + star T)) := by rw [hcomm.eq]
        _ = ((Uᗮ).starProjection * U.starProjection) * (T + star T) := by rw [mul_assoc]
        _ = 0 := by rw [complementaryProjection_mul_projection U, zero_mul]
    have hstar : star (U.starProjection * T * (Uᗮ).starProjection)
        = (Uᗮ).starProjection * star T * U.starProjection := by
      rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
        (isSelfAdjoint_starProjection Uᗮ).star_eq, ← mul_assoc]
    rw [hstar]
    have hsum : (Uᗮ).starProjection * T * U.starProjection
        + (Uᗮ).starProjection * star T * U.starProjection = 0 := by
      have h := hblock
      rw [mul_add, add_mul] at h
      exact h
    exact eq_neg_of_add_eq_zero_left hsum

/-! ### Proposition 3.3, forward direction

The converse above holds for an arbitrary pair, acute or not.  What was missing was the forward
half in the same generality: the printed proposition says *every* direct rotation is a principal
square root of the reflection product, and the compiled forward statements
(`complex_directRotation_sq`, `complex_directRotation_hermitianPart`) speak only about the
canonical acute one.

The block calculus below supplies it.  Three things have to be produced, and only the first two
cost anything:

* `T * T = J_V J_U`.  This is the argument already inside
  `proposition3_1_positivity_characterization`, extracted so that it is available without
  acuteness.
* spectrum in the closed right half-plane.  The Hermitian part of a direct rotation is *twice its
  diagonal*, the crossed blocks cancelling by `crossed_blocks`, so it is positive; for a normal
  operator that transfers to the spectrum through `cfc_nonneg_iff`.
* the crossed-intersection mapping condition.  This one is **free**: the converse takes it as a
  hypothesis, but in the forward direction it is a consequence.  Both crossed intersections sit
  inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
  operator because `T * T` *is* it, and the intertwining moves `U` to `V` -- which pins the image
  down to the other crossed intersection.

The self-adjointness hypotheses on the diagonal compressions are the same two that
Proposition 3.1 needs, and for the same reason: `IsDirectRotation` records the compressions
only through their numerical range, which does not by itself force `star T`'s diagonal blocks to
agree with `T`'s. -/

section PrincipalSquareRoot

variable (T : H →L[ℂ] H)

/-- **The Hermitian part of a direct rotation is a positive operator.** -/
theorem nonneg_add_star_of_isDirectRotation (hT : IsDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection)) :
    (0 : H →L[ℂ] H) ≤ T + star T := by
  have hP : (0 : H →L[ℂ] H) ≤ U.starProjection * T * U.starProjection := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hsource_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.source_compression_nonnegative x
  have hPc : (0 : H →L[ℂ] H)
      ≤ (Uᗮ).starProjection * T * (Uᗮ).starProjection := by
    refine (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mpr ?_
    refine ContinuousLinearMap.isPositive_def'.mpr ⟨hcomplement_sa, fun x => ?_⟩
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm (𝕜 := ℂ)]
    exact hT.complement_compression_nonnegative x
  rw [add_star_eq_two_diagonal U T hsource_sa hcomplement_sa hT.crossed_blocks]
  exact add_nonneg (add_nonneg hP hP) (add_nonneg hPc hPc)

omit [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] in
open scoped ComplexOrder in
/-- **A unitary whose Hermitian part is positive has spectrum in the closed right half-plane.**

This is what the word "principal" means for a square root of a unitary: among the square roots,
the one whose spectral arc avoids the open left half-plane.  For a normal element the transfer
from operator positivity to the spectrum is `cfc_nonneg_iff`. -/
theorem spectrum_re_nonneg_of_nonneg_add_star
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hpos : (0 : H →L[ℂ] H) ≤ T + star T) :
    ∀ z ∈ spectrum ℂ T, 0 ≤ z.re := by
  have hTnorm : IsStarNormal T := isStarNormal_of_mem_unitary hunitary
  have e2 : cfc (fun z : ℂ => star z) T = star T := by
    rw [cfc_star (R := ℂ) (fun z : ℂ => z) T, cfc_id' ℂ T]
  have e3 : T + star T = cfc (fun z : ℂ => z + star z) T := by
    rw [cfc_add (R := ℂ) T (fun z : ℂ => z) (fun z : ℂ => star z)
      continuous_id.continuousOn continuous_star.continuousOn, cfc_id' ℂ T, e2]
  rw [e3] at hpos
  have hz := (cfc_nonneg_iff (R := ℂ) (fun z : ℂ => z + star z) T
    (by fun_prop) hTnorm).mp hpos
  intro z hzmem
  have h := hz z hzmem
  rw [Complex.le_def] at h
  have hre : (0 : ℝ) ≤ (z + star z).re := h.1
  simp only [Complex.add_re, Complex.star_def, Complex.conj_re] at hre
  linarith

/-! The two crossed intersections are exactly the part of the `-1` eigenspace of the reflection
product that lies in `U`, respectively in `V`.  That is the whole content of the crossed-mapping
condition in the forward direction. -/

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the source crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_source {z : H}
    (hz : z ∈ halmosSourceDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosSourceDefect hz
  have hRU : U.reflectionOperator z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- The reflection product acts as `-1` on the target crossed intersection. -/
theorem reflectionProduct_apply_eq_neg_of_mem_target {z : H}
    (hz : z ∈ halmosTargetDefect U V) : spectraReflectionProduct U V z = -z := by
  obtain ⟨hPz, hQz⟩ := projections_apply_of_mem_halmosTargetDefect hz
  have hRU : U.reflectionOperator z = -z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, map_neg, Submodule.reflectionOperator_apply, hQz]
  module

omit [CompleteSpace H] in
/-- Inside `U`, the `-1` eigenspace of the reflection product is the source crossed
intersection. -/
theorem mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzU : z ∈ U)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosSourceDefect U V := by
  have hPz : U.starProjection z = z := U.starProjection_eq_self_iff.mpr hzU
  have hRU : U.reflectionOperator z = z := by
    rw [Submodule.reflectionOperator_apply, hPz]; module
  rw [mul_apply_eq_comp, hRU, Submodule.reflectionOperator_apply] at hz
  have h0 : (2 : ℂ) • V.starProjection z = 0 := by
    have h := congrArg (fun w : H => w + z) hz
    simpa using h
  have hQz : V.starProjection z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨hzU, (Submodule.starProjection_apply_eq_zero_iff V).mp hQz⟩

omit [CompleteSpace H] in
/-- Inside `V`, the `-1` eigenspace of the reflection product is the target crossed
intersection. -/
theorem mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg {z : H} (hzV : z ∈ V)
    (hz : spectraReflectionProduct U V z = -z) : z ∈ halmosTargetDefect U V := by
  have hQz : V.starProjection z = z := V.starProjection_eq_self_iff.mpr hzV
  have hJV : V.reflectionOperator z = z := by
    rw [Submodule.reflectionOperator_apply, hQz]; module
  have hinv := Submodule.reflectionOperator_involutive (𝕜 := ℂ) V
  have h1 : V.reflectionOperator (U.reflectionOperator z) = -z := by
    rw [← mul_apply_eq_comp]; exact hz
  have h2 : V.reflectionOperator (V.reflectionOperator (U.reflectionOperator z))
      = U.reflectionOperator z := by
    have h := congrArg (fun f : H →L[ℂ] H => f (U.reflectionOperator z)) hinv
    simpa using h
  have hJU : U.reflectionOperator z = -z := by
    rw [h1, map_neg, hJV] at h2
    exact h2.symm
  rw [Submodule.reflectionOperator_apply] at hJU
  have h0 : (2 : ℂ) • U.starProjection z = 0 := by
    have h := congrArg (fun w : H => w + z) hJU
    simpa using h
  have hPz : U.starProjection z = 0 := (smul_eq_zero.mp h0).resolve_left two_ne_zero
  exact Submodule.mem_inf.mpr ⟨(Submodule.starProjection_apply_eq_zero_iff U).mp hPz, hzV⟩

/-- **The crossed-intersection mapping condition is free.**

For *any* unitary that squares to the reflection product and intertwines the two
projections, the source crossed intersection is carried onto the target one.  Neither
positivity of the diagonal blocks nor acuteness enters: both crossed intersections sit
inside the `-1` eigenspace of the reflection product, `T` and `star T` commute with that
operator because `T * T` *is* it, and the intertwining moves `U` to `V`, which pins the
image down to the other crossed intersection.

Proposition 3.3's forward direction and printed Proposition 3.4 both consume this. -/
theorem crossedDefect_image_of_unitary_sq
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hsq : T * T = spectraReflectionProduct U V)
    (hintertwines : T * U.starProjection = V.starProjection * T) :
    T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hTsT : T * star T = 1 := Unitary.mul_star_self_of_mem hunitary
  have hsTT : star T * T = 1 := Unitary.star_mul_self_of_mem hunitary
  -- `T` and `star T` both commute with the reflection product, because it *is* `T * T`.
  have hRT : ∀ x : H,
      spectraReflectionProduct U V (T x) = T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * T = T * spectraReflectionProduct U V := by
      rw [← hsq]; noncomm_ring
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  have hRsT : ∀ x : H,
      spectraReflectionProduct U V (star T x) = star T (spectraReflectionProduct U V x) := by
    intro x
    have h1 : spectraReflectionProduct U V * star T = star T * spectraReflectionProduct U V := by
      rw [← hsq]
      calc T * T * star T = T * (T * star T) := by noncomm_ring
        _ = T := by rw [hTsT, mul_one]
        _ = star T * T * T := by rw [hsTT, one_mul]
    have h := congrArg (fun f : H →L[ℂ] H => f x) h1
    simpa [mul_apply_eq_comp] using h
  -- The intertwining moves `U` to `V`, and its adjoint moves `V` back to `U`.
  have hTU : ∀ x ∈ U, T x ∈ V := by
    intro x hx
    have h := congrArg (fun f : H →L[ℂ] H => f x) hintertwines
    simp only [mul_apply_eq_comp] at h
    rw [U.starProjection_eq_self_iff.mpr hx] at h
    exact V.starProjection_eq_self_iff.mp h.symm
  have hstarInt : U.starProjection * star T = star T * V.starProjection := by
    have h := congrArg star hintertwines
    rw [star_mul, star_mul, (isSelfAdjoint_starProjection U).star_eq,
      (isSelfAdjoint_starProjection V).star_eq] at h
    exact h
  have hsTV : ∀ y ∈ V, star T y ∈ U := by
    intro y hy
    have h := congrArg (fun f : H →L[ℂ] H => f y) hstarInt
    simp only [mul_apply_eq_comp] at h
    rw [V.starProjection_eq_self_iff.mpr hy] at h
    exact U.starProjection_eq_self_iff.mp h
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    refine mem_halmosTargetDefect_of_reflectionProduct_apply_eq_neg U V
      (hTU x (mem_halmosSourceDefect.mp hx).1) ?_
    rw [hRT x, reflectionProduct_apply_eq_neg_of_mem_source U V hx, map_neg]
  · intro y hy
    refine ⟨star T y, ?_, ?_⟩
    · refine mem_halmosSourceDefect_of_reflectionProduct_apply_eq_neg U V
        (hsTV y (mem_halmosTargetDefect.mp hy).2) ?_
      rw [hRsT y, reflectionProduct_apply_eq_neg_of_mem_target U V hy, map_neg]
    · have h := congrArg (fun f : H →L[ℂ] H => f y) hTsT
      simpa [mul_apply_eq_comp] using h

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, with no acuteness hypothesis.**

Every direct rotation is a principal unitary square root of the reflection product, *and* it
carries the source crossed intersection onto the target one.  The second conclusion is the
mapping condition that the converse takes as a hypothesis; here it comes out rather than
going in (`crossedDefect_image_of_unitary_sq`). -/
theorem proposition3_3_principalSquareRoot_forward
    (hT : IsDirectRotation U V T)
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection)) :
    IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsq := sq_eq_spectraReflectionProduct U V T hT.unitary_mem hT.intertwines
    hsource_sa hcomplement_sa hT.crossed_blocks
  have hpos := nonneg_add_star_of_isDirectRotation U V T hT hsource_sa hcomplement_sa
  have hspec := spectrum_re_nonneg_of_nonneg_add_star T hT.unitary_mem hpos
  exact ⟨⟨hT.unitary_mem, hsq, hspec⟩,
    crossedDefect_image_of_unitary_sq U V T hT.unitary_mem hsq hT.intertwines⟩

/-- **Davis--Kahan 1970, Proposition 3.3, forward direction, from the printed hypotheses.**

The source says the direct rotation has **positive diagonal blocks**; this repository's
`IsDirectRotation` records them only through their numerical range, which is strictly
weaker and is why `proposition3_3_principalSquareRoot_forward` has to ask for self-adjointness
separately.  Stated with operator positivity, as printed, no side hypothesis is needed at all:
a positive operator is self-adjoint and its numerical range is nonnegative, so both weaker
conditions come for free. -/
theorem proposition3_3_principalSquareRoot_forward_of_nonneg_blocks
    (hunitary : T ∈ unitary (H →L[ℂ] H))
    (hintertwines : T * U.starProjection = V.starProjection * T)
    (hcrossed : (Uᗮ).starProjection * T * U.starProjection =
      -star (U.starProjection * T * (Uᗮ).starProjection))
    (hsource_pos : (0 : H →L[ℂ] H) ≤ U.starProjection * T * U.starProjection)
    (hcomplement_pos :
      (0 : H →L[ℂ] H) ≤ (Uᗮ).starProjection * T * (Uᗮ).starProjection) :
    IsDirectRotation U V T ∧
      IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
      T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H) := by
  have hsp := (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hsource_pos
  have hcp := (ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp hcomplement_pos
  have hT : IsDirectRotation U V T :=
    { unitary_mem := hunitary
      intertwines := hintertwines
      source_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hsp.re_inner_nonneg_left x
      complement_compression_nonnegative := fun x => by
        rw [inner_re_symm (𝕜 := ℂ)]
        exact hcp.re_inner_nonneg_left x
      crossed_blocks := hcrossed }
  exact ⟨hT, proposition3_3_principalSquareRoot_forward U V T hT hsp.isSelfAdjoint
    hcp.isSelfAdjoint⟩

open scoped ComplexOrder in
/-- **Davis--Kahan 1970, Proposition 3.3, as a characterisation**, for an arbitrary pair of
subspaces.

A unitary whose diagonal `U`-compressions are self-adjoint is a direct rotation exactly when it
is a principal square root of the reflection product carrying one crossed intersection onto the
other.

The two hypotheses are needed only for the forward implication; the converse,
`proposition3_3_principalSquareRoot_converse`, holds for *every* principal square root with the
mapping property, and should be used directly when they are not available. -/
theorem proposition3_3_principalSquareRoot_iff
    (hsource_sa : IsSelfAdjoint (U.starProjection * T * U.starProjection))
    (hcomplement_sa :
      IsSelfAdjoint ((Uᗮ).starProjection * T * (Uᗮ).starProjection)) :
    IsDirectRotation U V T ↔
      (IsPrincipalUnitarySquareRoot (spectraReflectionProduct U V) T ∧
        T '' (halmosSourceDefect U V : Set H) = (halmosTargetDefect U V : Set H)) :=
  ⟨fun hT => proposition3_3_principalSquareRoot_forward U V T hT hsource_sa hcomplement_sa,
    fun h => proposition3_3_principalSquareRoot_converse U V T h.1 h.2⟩

end PrincipalSquareRoot

end DavisKahan
end TauCeti
