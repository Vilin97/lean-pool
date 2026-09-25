/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.ReflectionBlocks
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.Closed

/-!
# The reflection block system for an unbounded operator

Let `A` be a partial linear map reduced by `U`, let `B` be a bounded operator
that is *odd* for the splitting `U ⊕ Uᗮ` (it exchanges the two summands), and
let `Z` be a bounded operator that commutes with `A + B` on `D(A)` and preserves
`D(A)`.  Writing

* `C := U.diagonalPart Z`   (the even block of `Z`),
* `S := U.offDiagonalPart Z` (the odd block of `Z`),

this module proves the two facts the unbounded double-angle theory rests on.

## Domain control

`C` and `S` preserve `D(A)`.  In blocks, with `Z = [[D₀, G⋆], [G, -D₁]]`, this
is exactly

`D₀ D(A₀) ⊆ D(A₀)`, `G D(A₀) ⊆ D(A₁)`, `G⋆ D(A₁) ⊆ D(A₀)`, `D₁ D(A₁) ⊆ D(A₁)`,

the compatibility that is awkward to obtain when the four blocks are handled
separately.  It follows from `Z D(A) ⊆ D(A)` together with the reducing
projections preserving `D(A)`; nothing about the spectrum of `A` is used.

## The Sylvester equation

On the whole of `D(A)`,

`A (S x) - S (A x) = C (B x) - B (C x)`.

This is the domain-correct, branch-free form of Davis--Kahan equation (7.6).
Blockwise, on `D(A₀)`, it reads

`A₁ G - G A₀ = -D₁ B - B D₀`,

an honest operator identity: every term is defined, by the domain inclusions
above.  No global `|A|`, no indefinite closed form, and no sign selection: the
sign of `cos 2θ` is inside `C x`, and only `C` appears.

## Main results

* `TauCeti.mem_domain_diagonalPart`, `TauCeti.mem_domain_offDiagonalPart`.
* `TauCeti.sylvester_offDiagonalPart_of_mem` and
  `TauCeti.sylvester_offDiagonalPart_of_mem_orthogonal`: the two block forms.
* `TauCeti.sylvester_offDiagonalPart`: the ambient identity on all of `D(A)`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: equation (7.6) and the Appendix
  to Section 6, where the unbounded extension is stated to be analogous but is
  not written out.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace

variable {𝕜 H : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable {A : H →ₗ.[𝕜] H} {U : Submodule 𝕜 H} [U.HasOrthogonalProjection]
variable {B Z : H →L[𝕜] H}

/-- **`B` exchanges the two summands.**  This is the Davis--Kahan hypothesis
`H₀ = H₁ = 0`: the perturbation is fully off-diagonal. -/
def IsOddFor (U : Submodule 𝕜 H) (B : H →L[𝕜] H) : Prop :=
  (∀ x ∈ U, B x ∈ Uᗮ) ∧ ∀ x ∈ Uᗮ, B x ∈ U

section Domain

/-- **The even block preserves the domain.** -/
theorem mem_domain_diagonalPart (hred : LinearPMap.ReducesSubspace A U)
    (hZ : LinearPMap.MapsDomainTo A A Z) (x : A.domain) :
    U.diagonalPart Z (x : H) ∈ A.domain := by
  rw [Submodule.diagonalPart_apply]
  refine A.domain.add_mem ?_ ?_
  · exact hred.projection_mem_domain
      ⟨Z (U.starProjection (x : H)), hZ ⟨_, hred.projection_mem_domain x⟩⟩
  · exact hred.orthogonalProjection_mem_domain
      ⟨Z (Uᗮ.starProjection (x : H)), hZ ⟨_, hred.orthogonalProjection_mem_domain x⟩⟩

/-- **The odd block preserves the domain.** -/
theorem mem_domain_offDiagonalPart (hred : LinearPMap.ReducesSubspace A U)
    (hZ : LinearPMap.MapsDomainTo A A Z) (x : A.domain) :
    U.offDiagonalPart Z (x : H) ∈ A.domain := by
  rw [Submodule.offDiagonalPart_apply]
  exact A.domain.sub_mem (hZ x) (mem_domain_diagonalPart hred hZ x)

end Domain

section Sylvester

variable (hred : LinearPMap.ReducesSubspace A U) (hB : IsOddFor U B)
  (hZdom : LinearPMap.MapsDomainTo A A Z)
  (hZcomm : ∀ x : A.domain,
    A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))

include hred hB hZdom hZcomm

/-- **Equation (7.6) for an unbounded operator, on `D(A₀)`.**

For `x` in the domain and in `U`,

`A (S x) - S (A x) = C (B x) - B (C x)`,

which in blocks is `A₁ G x - G A₀ x = -D₁ B x - B D₀ x`.  Every term is defined:
`S x ∈ D(A) ∩ Uᗮ` and `C x ∈ D(A) ∩ U` by `mem_domain_offDiagonalPart` and
`mem_domain_diagonalPart`. -/
theorem sylvester_offDiagonalPart_of_mem (x : A.domain) (hx : (x : H) ∈ U) :
    A ⟨U.offDiagonalPart Z (x : H), mem_domain_offDiagonalPart hred hZdom x⟩ +
        B (U.diagonalPart Z (x : H)) =
      U.offDiagonalPart Z (A x) + U.diagonalPart Z (B (x : H)) := by
  classical
  set C : H →L[𝕜] H := U.diagonalPart Z with hCdef
  set S : H →L[𝕜] H := U.offDiagonalPart Z with hSdef
  have hCmem : C (x : H) ∈ A.domain := mem_domain_diagonalPart hred hZdom x
  have hSmem : S (x : H) ∈ A.domain := mem_domain_offDiagonalPart hred hZdom x
  have hCU : C (x : H) ∈ U := diagonalPart_mem_of_mem U Z hx
  have hSU : S (x : H) ∈ Uᗮ := offDiagonalPart_mem_orthogonal_of_mem U Z hx
  -- split `Z x` into its two blocks, inside the domain
  have hsplit : (⟨Z (x : H), hZdom x⟩ : A.domain) =
      ⟨C (x : H), hCmem⟩ + ⟨S (x : H), hSmem⟩ := by
    apply Subtype.ext
    have := congrArg (fun T : H →L[𝕜] H => T (x : H))
      (diagonalPart_add_offDiagonalPart U Z)
    simpa only [add_apply, Submodule.coe_add, hCdef, hSdef] using this.symm
  have hAsplit : A ⟨Z (x : H), hZdom x⟩ =
      A ⟨C (x : H), hCmem⟩ + A ⟨S (x : H), hSmem⟩ := by
    rw [hsplit, A.map_add]
  have hBsplit : B (Z (x : H)) = B (C (x : H)) + B (S (x : H)) := by
    have := congrArg (fun T : H →L[𝕜] H => T (x : H))
      (diagonalPart_add_offDiagonalPart U Z)
    rw [← this]
    simp only [add_apply, hCdef, hSdef, map_add]
  -- the four memberships that decide which projection survives
  have hACU : A ⟨C (x : H), hCmem⟩ ∈ U := hred.invariant _ hCU
  have hASU : A ⟨S (x : H), hSmem⟩ ∈ Uᗮ := hred.orthogonal_invariant _ hSU
  have hBCU : B (C (x : H)) ∈ Uᗮ := hB.1 _ hCU
  have hBSU : B (S (x : H)) ∈ U := hB.2 _ hSU
  have hAxU : (A x) ∈ U := hred.invariant _ hx
  have hBxU : B (x : H) ∈ Uᗮ := hB.1 _ hx
  -- project the commutation identity onto `Uᗮ`
  have hcomm := hZcomm x
  have hproj := congrArg Uᗮ.starProjection hcomm
  rw [map_add, map_add, hAsplit, hBsplit, map_add, map_add,
    starProjection_orthogonal_eq_zero_of_mem hACU,
    Submodule.starProjection_eq_self_iff.mpr hASU,
    starProjection_orthogonal_eq_zero_of_mem hBSU,
    Submodule.starProjection_eq_self_iff.mpr hBCU,
    ← offDiagonalPart_apply_of_mem U Z hAxU,
    ← diagonalPart_apply_of_mem_orthogonal U Z hBxU] at hproj
  simpa only [zero_add, add_zero, hCdef, hSdef] using hproj

/-- **Equation (7.6) for an unbounded operator, on `D(A₁)`.**  The mirror of
`sylvester_offDiagonalPart_of_mem`, with the same conclusion. -/
theorem sylvester_offDiagonalPart_of_mem_orthogonal (x : A.domain)
    (hx : (x : H) ∈ Uᗮ) :
    A ⟨U.offDiagonalPart Z (x : H), mem_domain_offDiagonalPart hred hZdom x⟩ +
        B (U.diagonalPart Z (x : H)) =
      U.offDiagonalPart Z (A x) + U.diagonalPart Z (B (x : H)) := by
  classical
  set C : H →L[𝕜] H := U.diagonalPart Z with hCdef
  set S : H →L[𝕜] H := U.offDiagonalPart Z with hSdef
  have hCmem : C (x : H) ∈ A.domain := mem_domain_diagonalPart hred hZdom x
  have hSmem : S (x : H) ∈ A.domain := mem_domain_offDiagonalPart hred hZdom x
  have hCU : C (x : H) ∈ Uᗮ := diagonalPart_mem_orthogonal_of_mem_orthogonal U Z hx
  have hSU : S (x : H) ∈ U := offDiagonalPart_mem_of_mem_orthogonal U Z hx
  have hsplit : (⟨Z (x : H), hZdom x⟩ : A.domain) =
      ⟨C (x : H), hCmem⟩ + ⟨S (x : H), hSmem⟩ := by
    apply Subtype.ext
    have := congrArg (fun T : H →L[𝕜] H => T (x : H))
      (diagonalPart_add_offDiagonalPart U Z)
    simpa only [add_apply, Submodule.coe_add, hCdef, hSdef] using this.symm
  have hAsplit : A ⟨Z (x : H), hZdom x⟩ =
      A ⟨C (x : H), hCmem⟩ + A ⟨S (x : H), hSmem⟩ := by
    rw [hsplit, A.map_add]
  have hBsplit : B (Z (x : H)) = B (C (x : H)) + B (S (x : H)) := by
    have := congrArg (fun T : H →L[𝕜] H => T (x : H))
      (diagonalPart_add_offDiagonalPart U Z)
    rw [← this]
    simp only [add_apply, hCdef, hSdef, map_add]
  have hACU : A ⟨C (x : H), hCmem⟩ ∈ Uᗮ := hred.orthogonal_invariant _ hCU
  have hASU : A ⟨S (x : H), hSmem⟩ ∈ U := hred.invariant _ hSU
  have hBCU : B (C (x : H)) ∈ U := hB.2 _ hCU
  have hBSU : B (S (x : H)) ∈ Uᗮ := hB.1 _ hSU
  have hAxU : (A x) ∈ Uᗮ := hred.orthogonal_invariant _ hx
  have hBxU : B (x : H) ∈ U := hB.2 _ hx
  have hcomm := hZcomm x
  have hproj := congrArg U.starProjection hcomm
  rw [map_add, map_add, hAsplit, hBsplit, map_add, map_add,
    (U.starProjection_apply_eq_zero_iff).mpr hACU,
    Submodule.starProjection_eq_self_iff.mpr hASU,
    (U.starProjection_apply_eq_zero_iff).mpr hBSU,
    Submodule.starProjection_eq_self_iff.mpr hBCU,
    ← offDiagonalPart_apply_of_mem_orthogonal U Z hAxU,
    ← diagonalPart_apply_of_mem U Z hBxU] at hproj
  simpa only [zero_add, add_zero, hCdef, hSdef] using hproj

/-- **Equation (7.6) for an unbounded operator, on all of `D(A)`.**

`A (S x) - S (A x) = C (B x) - B (C x)`, with every term defined by the domain
inclusions.  Branch-free: no sign of `cos 2θ` is selected anywhere, because the
sign is absorbed into `C x`. -/
theorem sylvester_offDiagonalPart (x : A.domain) :
    A ⟨U.offDiagonalPart Z (x : H), mem_domain_offDiagonalPart hred hZdom x⟩ +
        B (U.diagonalPart Z (x : H)) =
      U.offDiagonalPart Z (A x) + U.diagonalPart Z (B (x : H)) := by
  classical
  set x₀ : A.domain := ⟨U.starProjection (x : H), hred.projection_mem_domain x⟩
    with hx₀
  set x₁ : A.domain :=
    ⟨Uᗮ.starProjection (x : H), hred.orthogonalProjection_mem_domain x⟩ with hx₁
  have hsum : x = x₀ + x₁ :=
    Subtype.ext (U.starProjection_add_starProjection_orthogonal (x : H)).symm
  have hcoe : (x : H) = (x₀ : H) + (x₁ : H) := congrArg Subtype.val hsum
  have h₀ := sylvester_offDiagonalPart_of_mem hred hB hZdom hZcomm x₀
    (U.starProjection_apply_mem (x : H))
  have h₁ := sylvester_offDiagonalPart_of_mem_orthogonal hred hB hZdom hZcomm x₁
    (Uᗮ.starProjection_apply_mem (x : H))
  have hAS : A ⟨U.offDiagonalPart Z (x : H),
        mem_domain_offDiagonalPart hred hZdom x⟩ =
      A ⟨U.offDiagonalPart Z (x₀ : H),
          mem_domain_offDiagonalPart hred hZdom x₀⟩ +
        A ⟨U.offDiagonalPart Z (x₁ : H),
          mem_domain_offDiagonalPart hred hZdom x₁⟩ := by
    rw [← A.map_add]
    exact congrArg (fun y : A.domain => A y)
      (Subtype.ext (show U.offDiagonalPart Z (x : H) =
        U.offDiagonalPart Z (x₀ : H) + U.offDiagonalPart Z (x₁ : H) by
          rw [hcoe, map_add]))
  have hAx : A x = A x₀ + A x₁ := by
    rw [← A.map_add]
    exact congrArg (fun y : A.domain => A y) hsum
  have hCx : U.diagonalPart Z (x : H) =
      U.diagonalPart Z (x₀ : H) + U.diagonalPart Z (x₁ : H) := by
    rw [hcoe, map_add]
  have hBx : B (x : H) = B (x₀ : H) + B (x₁ : H) := by rw [hcoe, map_add]
  rw [hAS, hCx, hAx, hBx]
  simp only [map_add]
  linear_combination (norm := module) h₀ + h₁

end Sylvester

end TauCeti
