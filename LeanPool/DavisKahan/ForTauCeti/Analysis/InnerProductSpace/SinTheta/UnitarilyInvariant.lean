/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Staged for Tau Ceti, roadmap topic T17.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SinThetaUINorm.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

The part-III Davis–Kahan sin-Θ theorem in **every unitarily invariant norm**:
`N (Q̂ ∘ P) ≤ N (S − T) / g`, where `P, Q̂` project onto the separated invariant
subspaces.  This is the Davis–Kahan (1970) statement at full generality; the
Frobenius (`sum_norm_sub_starProjection_span_sq_le_hilbertSchmidt`) and
operator-norm (`norm_starProjection_comp_starProjection_le`) theorems are the
Hilbert–Schmidt and spectral instances.

The norm-free construction of `A, B, X, Y` is shared verbatim with the
operator-norm theorem (`exists_isSymmetric_comp_sub_comp_eq`); only the final
estimate differs — here it is the abstract Sylvester bound
`TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq`, fed the operator seminorm
induced by `N`, whose operator-ideal property is `UnitarilyInvariantSeminorm`'s
`apply_comp_le`.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.OperatorNorm

/-! # The unitarily-invariant-norm Davis–Kahan sin-Θ theorem

For symmetric `T, S` on a finite-dimensional inner product space, a
`T`-invariant subspace `U` whose form sits above `c + g`, and an `S`-invariant
subspace `V` whose form sits below `c`, every unitarily invariant norm `N`
bounds the cross-projection:
`N (V.starProjection ∘ U.starProjection) ≤ N (S − T) / g`.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.apply_starProjection_comp_starProjection_le`:
  the part-III `sin Θ` bound, every unitarily invariant norm.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46.
* R. Bhatia, *Matrix Analysis*, Chapter VII (the Davis–Kahan theorems).

## Provenance

*Moved, not restated.*  This file was
`DavisKahan/FiniteDimensional/SinTheta/UnitarilyInvariant.lean`
before the whole remaining sin-Θ closure moved into
the staging layer.  Statements, proofs, signatures and namespaces are unchanged;
the declarations already lived in `TauCeti.*`, so the move was a path change and
an import repoint.

Y3(b2) and Y3(b3) are what made it possible: before them this file's import
closure crossed `ForMathlib`, which the `ForTauCeti` layer rule forbids.

-/

public section

namespace TauCeti
open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

namespace UnitarilyInvariantSeminorm

/-- **The part-III Davis–Kahan sin-Θ theorem, every unitarily invariant norm.**
Let `T, S` be symmetric, `U` a `T`-invariant subspace with quadratic form
`≥ (c + g) ‖·‖²`, and `V` an `S`-invariant subspace with form `≤ c ‖·‖²`.  Then
for every unitarily invariant norm `N` and every `g > 0`,
`N (V.starProjection ∘ U.starProjection) ≤ N (S − T) / g`.  The left side is
`N (sin Θ)`, so this is the part-III `‖sin Θ‖ ≤ ‖S − T‖ / g` in every unitarily
invariant norm; Frobenius and operator norm are the instances. -/
theorem apply_starProjection_comp_starProjection_le (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    N ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / g := by
  obtain ⟨A, B, hAsym, hBsym, hAc, hBc, hsylv⟩ :=
    exists_isSymmetric_comp_sub_comp_eq hT hS hUinv hVinv hU hV
  set P := U.starProjection with hP
  set Q := V.starProjection with hQ
  set X : E →L[𝕜] E := P ∘L Q with hX
  set Y : E →L[𝕜] E :=
    P ∘L (LinearMap.toContinuousLinearMap T - LinearMap.toContinuousLinearMap S) ∘L Q with hY
  -- The operator seminorm on `E →L[𝕜] E` induced by `N`.
  set N' : (E →L[𝕜] E) → ℝ := fun f => N (f : E →ₗ[𝕜] E) with hN'
  have hadd : ∀ f h : E →L[𝕜] E, N' (f + h) ≤ N' f + N' h := fun f h => by
    simp only [hN', ContinuousLinearMap.toLinearMap_add]; exact N.add_le _ _
  have hsmul : ∀ (a : 𝕜) (f : E →L[𝕜] E), N' (a • f) = ‖a‖ * N' f := fun a f => by
    simp only [hN', ContinuousLinearMap.toLinearMap_smul]; exact N.smul_eq _ _
  have hidealL : ∀ C f : E →L[𝕜] E, N' (C ∘L f) ≤ ‖C‖ * N' f := fun C f => by
    simp only [hN']
    exact N.apply_comp_le (norm_nonneg C) fun y => C.le_opNorm y
  have hidealR : ∀ f C : E →L[𝕜] E, N' (f ∘L C) ≤ N' f * ‖C‖ := fun f C => by
    simp only [hN']
    exact N.apply_comp_le' (norm_nonneg C) fun y => C.le_opNorm y
  -- The abstract Sylvester bound gives `N' X ≤ N' Y / g`.
  have hbound : N' X ≤ N' Y / g :=
    TauCeti.ContinuousLinearMap.le_div_of_comp_sub_comp_eq hadd hsmul hidealL hidealR
      hAsym hBsym hg hAc hBc hsylv
  -- `N' Y ≤ N (S − T)` by the ideal property (both projections are contractions).
  have hYcoe : (Y : E →ₗ[𝕜] E) = (P : E →ₗ[𝕜] E) ∘ₗ ((T - S) ∘ₗ (Q : E →ₗ[𝕜] E)) := by
    ext x
    simp [hY, map_sub]
  have hYbound : N' Y ≤ N (S - T) := by
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change N (Y : E →ₗ[𝕜] E) ≤ N (S - T)
    rw [hYcoe]
    calc N ((P : E →ₗ[𝕜] E) ∘ₗ ((T - S) ∘ₗ (Q : E →ₗ[𝕜] E)))
        ≤ 1 * N ((T - S) ∘ₗ (Q : E →ₗ[𝕜] E)) :=
          N.apply_comp_le zero_le_one fun y => by
            rw [one_mul]; exact U.norm_starProjection_apply_le y
      _ = N ((T - S) ∘ₗ (Q : E →ₗ[𝕜] E)) := one_mul _
      _ ≤ N (T - S) * 1 :=
          N.apply_comp_le' zero_le_one fun y => by
            rw [one_mul]; exact V.norm_starProjection_apply_le y
      _ = N (T - S) := mul_one _
      _ = N (S - T) := by rw [show (T - S : E →ₗ[𝕜] E) = -(S - T) by abel, N.apply_neg]
  -- `N (Q ∘ P) = N' X` by star-invariance of `N`.
  have hstar : N ((Q ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E) = N' X := by
    have hPsym : (P : E →ₗ[𝕜] E).IsSymmetric := U.starProjection_isSymmetric
    have hQsym : (Q : E →ₗ[𝕜] E).IsSymmetric := V.starProjection_isSymmetric
    have hadj : ((Q ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E).adjoint = (X : E →ₗ[𝕜] E) := by
      have hcoe : ((Q ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E) = (Q : E →ₗ[𝕜] E) ∘ₗ (P : E →ₗ[𝕜] E) := by
        ext x; simp
      rw [hcoe, LinearMap.adjoint_comp, hPsym.adjoint_eq, hQsym.adjoint_eq]
      ext x; simp [hX]
    rw [← N.apply_adjoint ((Q ∘L P : E →L[𝕜] E) : E →ₗ[𝕜] E), hadj]
  calc N ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = N' X := hstar
    _ ≤ N' Y / g := hbound
    _ ≤ N (S - T) / g := by gcongr

/-- **The Frobenius part-III Davis–Kahan sin-Θ theorem.**  The every-UI-norm
sin-Θ bound instantiated at the Frobenius norm:
`‖V.sP ∘ U.sP‖_F ≤ ‖S − T‖_F / g`.  Unfold either side with
`frobenius_apply` to read it as a column-norm sum `√(∑ ‖·‖²)`. -/
theorem frobenius_starProjection_comp_starProjection_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {c g : ℝ} (hg : 0 < g)
    (hU : ∀ x ∈ U, (c + g) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hV : ∀ x ∈ V, RCLike.re ⟪S x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2) :
    frobenius (𝕜 := 𝕜) (E := E) (F := E) ((V.starProjection ∘L U.starProjection : E →L[𝕜] E) :
      E →ₗ[𝕜] E)
      ≤ frobenius (𝕜 := 𝕜) (E := E) (F := E) (S - T) / g :=
  (frobenius (𝕜 := 𝕜) (E := E) (F := E)).apply_starProjection_comp_starProjection_le hT hS
    hUinv hVinv hg hU hV

end UnitarilyInvariantSeminorm

end TauCeti
