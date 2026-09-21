/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81UnboundedBranch

/-!
# Theorem 8.1 part (i) at unbounded scope

Part (i) is the compression inequality `A₁ − α ≤ C₁(Λ₁ − α)C₁`, read as a form
inequality: the shifted energy of a vector is at most the shifted energy of its
component in the complement of the branch.  Unlike parts (ii) and (iii), which
Davis and Kahan print *in finite dimensions*, part (i) carries no dimension
qualifier and so inherits the paper's ambient unbounded scope.

The proof is short once the branch's ordered form bounds exist.  A reducing
subspace splits the energy, `re⟪B x, x⟫ = re⟪B u, u⟫ + re⟪B v, v⟫` with
`u = P_Q x` and `v = P_{Qᗮ} x`; the branch bound makes the `u` term's shifted
part nonpositive, and what is left is the claim.  Nothing about `P` is used: the
inequality holds for every domain vector, and the paper's `Pᗮ` is only where it
is read.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan

noncomputable section

universe v

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The energy splits along a reducing subspace.** -/
theorem re_inner_split_of_reduces {B : H →ₗ.[ℂ] H} {Q : Submodule ℂ H}
    [Q.HasOrthogonalProjection] (hred : TauCeti.LinearPMap.ReducesSubspace B Q)
    (x : B.domain) :
    (⟪B x, (x : H)⟫_ℂ).re
      = (⟪B ⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩,
          Q.starProjection (x : H)⟫_ℂ).re
        + (⟪B ⟨Qᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩,
            Qᗮ.starProjection (x : H)⟫_ℂ).re := by
  have hxeq : x = (⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩ : B.domain)
      + ⟨Qᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩ :=
    Subtype.ext (by
      change (x : H) = Q.starProjection (x : H) + Qᗮ.starProjection (x : H)
      rw [Submodule.starProjection_orthogonal_apply]
      abel)
  have hcross1 : (⟪B (⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩ : B.domain),
      Qᗮ.starProjection (x : H)⟫_ℂ) = 0 :=
    (Submodule.mem_orthogonal Q _).mp (Qᗮ.starProjection_apply_mem _) _
      (hred.invariant _ (Q.starProjection_apply_mem _))
  have hcross2 : (⟪B (⟨Qᗮ.starProjection (x : H),
      hred.orthogonalProjection_mem_domain x⟩ : B.domain),
      Q.starProjection (x : H)⟫_ℂ) = 0 := by
    refine (Submodule.mem_orthogonal Qᗮ _).mp ?_ _
      (hred.orthogonal_invariant _ (Qᗮ.starProjection_apply_mem _))
    rw [Submodule.orthogonal_orthogonal]
    exact Q.starProjection_apply_mem _
  have hexpand : (⟪B x, (x : H)⟫_ℂ)
      = ⟪B (⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩ : B.domain),
          Q.starProjection (x : H)⟫_ℂ
        + ⟪B (⟨Qᗮ.starProjection (x : H),
            hred.orthogonalProjection_mem_domain x⟩ : B.domain),
          Qᗮ.starProjection (x : H)⟫_ℂ := by
    have hstep : (⟪B x, (x : H)⟫_ℂ)
        = ⟪B ((⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩ : B.domain)
              + ⟨Qᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩),
            (((⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩ : B.domain)
              + ⟨Qᗮ.starProjection (x : H),
                  hred.orthogonalProjection_mem_domain x⟩ : B.domain) : H)⟫_ℂ := by
      exact congrArg (fun z : B.domain => (⟪B z, (z : H)⟫_ℂ)) hxeq
    rw [hstep, _root_.LinearPMap.map_add]
    change ⟪_ + _, (Q.starProjection (x : H) + Qᗮ.starProjection (x : H))⟫_ℂ = _
    rw [inner_add_left, inner_add_right, inner_add_right, hcross1, hcross2]
    ring
  rw [hexpand, Complex.add_re]

omit [CompleteSpace H] in
/-- **Davis--Kahan 1970, Theorem 8.1 part (i), upper block, at unbounded scope.**

`A₁ − α ≤ C₁(Λ₁ − α)C₁` as a form inequality: the `α`-shifted energy of a vector
is at most the `α`-shifted energy of its component in the branch's complement.
The paper reads it on `Pᗮ`; it holds on the whole domain. -/
theorem theorem8_1_upperCompressionRepulsion_unbounded
    {B : H →ₗ.[ℂ] H} {Q : Submodule ℂ H} [Q.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B Q) {alpha : ℝ}
    (hQlow : ∀ y : B.domain, (y : H) ∈ Q →
      (⟪B y, (y : H)⟫_ℂ).re ≤ alpha * ‖(y : H)‖ ^ 2)
    (x : B.domain) :
    (⟪B x, (x : H)⟫_ℂ).re - alpha * ‖(x : H)‖ ^ 2 ≤
      (⟪B ⟨Qᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩,
        Qᗮ.starProjection (x : H)⟫_ℂ).re
        - alpha * ‖Qᗮ.starProjection (x : H)‖ ^ 2 := by
  have hsplit := re_inner_split_of_reduces hred x
  have hnorm : ‖(x : H)‖ ^ 2
      = ‖Q.starProjection (x : H)‖ ^ 2 + ‖Qᗮ.starProjection (x : H)‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x : H) Q
  have hlow := hQlow ⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩
    (Q.starProjection_apply_mem _)
  rw [hsplit, hnorm]
  nlinarith [hlow]

omit [CompleteSpace H] in
/-- **Theorem 8.1 part (i), lower block, at unbounded scope.**

The dual reading, against the complement's lower form bound. -/
theorem theorem8_1_lowerCompressionRepulsion_unbounded
    {B : H →ₗ.[ℂ] H} {Q : Submodule ℂ H} [Q.HasOrthogonalProjection]
    (hred : TauCeti.LinearPMap.ReducesSubspace B Q) {c : ℝ}
    (hQhigh : ∀ y : B.domain, (y : H) ∈ Qᗮ →
      c * ‖(y : H)‖ ^ 2 ≤ (⟪B y, (y : H)⟫_ℂ).re)
    (x : B.domain) :
    c * ‖(x : H)‖ ^ 2 - (⟪B x, (x : H)⟫_ℂ).re ≤
      c * ‖Q.starProjection (x : H)‖ ^ 2
        - (⟪B ⟨Q.starProjection (x : H), hred.projection_mem_domain x⟩,
            Q.starProjection (x : H)⟫_ℂ).re := by
  have hsplit := re_inner_split_of_reduces hred x
  have hnorm : ‖(x : H)‖ ^ 2
      = ‖Q.starProjection (x : H)‖ ^ 2 + ‖Qᗮ.starProjection (x : H)‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection (x : H) Q
  have hhigh := hQhigh
    ⟨Qᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩
    (Qᗮ.starProjection_apply_mem _)
  rw [hsplit, hnorm]
  nlinarith [hhigh]

end

end Section8
end DavisKahan1970
end TauCeti
