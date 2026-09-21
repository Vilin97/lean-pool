/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DoubleAngle.SpectralCutoff

/-!
# The unbounded, residual-form, branch-free `tan 2Θ` theorem, at the operator norm

Davis and Kahan prove the `tan 2Θ` theorem of Section 7 for bounded Hermitian
operators, and say in the Appendix to Section 6 that the extension to unbounded
self-adjoint operators is analogous to the single-angle passage.  They never
write it out.  This module states and proves the **operator-norm case** of that
extension, in residual form.

## The statement

`A` is self-adjoint and possibly unbounded, `𝔛₀ = 1_{(-∞, c]}(A)` is one of its
spectral subspaces and `𝔛₁ = 𝔛₀ᗮ` the complementary one, the quadratic form of
`A` is at most `a` on `𝔛₀` and at least `b` on `𝔛₁`, and `δ = b - a > 0`.  The
perturbation `B` is bounded and **fully off-diagonal** — this is the source's
`H₀ = H₁ = 0`, so `B` is the residual `R`.  `Z` is the reducing reflection
`2Q - 1` of `A + B`.  Writing `cos 2Θ₀` and `sin 2Θ₀` for the even and odd
blocks of `Z` relative to `𝔛₀ ⊕ 𝔛₁`, then for every `x ∈ 𝔛₀`

`δ ‖sin 2Θ₀ x‖ ≤ 2 ‖B‖ ‖cos 2Θ₀ x‖`   and   `κ ‖x‖ ≤ ‖cos 2Θ₀ x‖`,

with `κ = δ / √(δ² + 4‖B‖²) > 0`.  Dividing, `δ |tan 2θ| ≤ 2 ‖B‖`.

## What distinguishes this from the `tan 2Θ` results already here

* **The constant is the sharp `2`, and the right-hand side is the residual.**
  This is `δ · N(tan 2Θ₀) ≤ 2 · N(R)`, not the perturbation form `2 · N(E)`.
  The existing unbounded family
  (`DavisKahan/TanTwoTheta/UnboundedIdeal.lean`,
  `tanTwoTheta_addBounded_gauge_of_spectrum_gap`) is the perturbation form,
  carries a spurious `1/(1 - 2g²)` factor, and its own docstring disclaims that
  the object it bounds is the genuine `tan 2Θ`.

* **Branch-freeness is structural, not selected.**  The sign of `cos 2θ` has
  vanished into the block `cos 2Θ₀ x`, and only its magnitude survives; there is
  no acute/obtuse selection anywhere, and no hypothesis placing the angles on
  one side of `π/4`.  The sharp branch-free bounded theorem
  (`absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_invariantSubspace`) has that
  property and requires `A` bounded; this one has it with `A` unbounded.

* **The pole is excluded, not assumed.**  `|cos 2Θ₀| ≥ κ > 0` is a theorem with
  an explicit constant, proved before the tangent is formed, so the tangent's
  denominator never vanishes.  This is the same discipline the repository
  already uses for `tan Θ`.

## Scope, stated honestly

This is the **operator-norm** case, equivalently the Ky Fan prefix at `ν = 1`.
The arbitrary-unitarily-invariant-norm endpoint
`δ · N(tan 2Θ₀) ≤ 2 · N(B)` for every Fan-dominant ideal is **not** proved here;
see the `DK-6-appendix` census row for what blocks it.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a perturbation.
  III*, SIAM J. Numer. Anal. 7 (1970), 1--46: Section 7 for the `tan 2Θ`
  theorem and the reflection `Z = 2Q - 1`, equation (7.6) for the block system,
  and the Appendix to Section 6 for the unbounded passage.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- **Davis--Kahan Section 7, the `tan 2Θ` theorem for an unbounded self-adjoint
operator, in residual form, at the operator norm.**

Both halves of the estimate at once: the tangent inequality with the sharp
constant `2` against the residual `B`, and the explicit lower bound on the
tangent's denominator that makes it meaningful.

Hypotheses, in the source's terms.  `hA` : `A` is self-adjoint.  The trial
subspace is the spectral subspace `𝔛₀ = 1_{(-∞, c]}(A)`.  `hB` : the
perturbation is fully off-diagonal, `H₀ = H₁ = 0`.  `hZsa`, `hZ2` : `Z` is the
self-adjoint involution `2Q - 1`.  `hZdom`, `hZcomm` : `Z` preserves `D(A)` and
commutes with `A + B` there — that is, `Q` reduces the perturbed operator.
`hUa`, `hUb`, `hab` : the spectral separation `A ≤ a` on `𝔛₀`, `A ≥ b` on `𝔛₁`,
`a < b`. -/
theorem tanTwoTheta_unbounded_residual_opNorm_complex
    {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b c : ℝ} (hA : IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain,
      (x : H) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      (⟪A x, (x : H)⟫_ℂ).re ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : H) ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)
    (hab : a < b) {x : H}
    (hx : x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) :
    (b - a) *
        ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
          measurableSet_Iic).offDiagonalPart Z x‖ ≤
      2 * ‖B‖ *
        ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
          measurableSet_Iic).diagonalPart Z x‖ ∧
    TauCeti.diagonalBlockBound (b - a) ‖B‖ * ‖x‖ ≤
      ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
        measurableSet_Iic).diagonalPart Z x‖ :=
  ⟨TauCeti.gap_mul_norm_offDiagonalPart_apply_le_specRange hA hB hZsa hZ2 hZdom
      hZcomm hUa hUb hab hx,
   TauCeti.diagonalBlockBound_mul_le_norm_diagonalPart_apply_specRange hA hB
      hZsa hZ2 hZdom hZcomm hUa hUb hab hx⟩

/-- The tangent form: on the trial subspace the denominator is nonzero, so the
estimate can be divided through.  `‖sin 2Θ₀ x‖ / ‖cos 2Θ₀ x‖ ≤ 2 ‖B‖ / δ`. -/
theorem tanTwoTheta_unbounded_residual_div_complex
    {A : H →ₗ.[ℂ] H} {B Z : H →L[ℂ] H} {a b c : ℝ} (hA : IsSelfAdjoint A)
    (hB : TauCeti.IsOddFor
      (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic) B)
    (hZsa : IsSelfAdjoint Z) (hZ2 : Z * Z = 1)
    (hZdom : TauCeti.LinearPMap.MapsDomainTo A A Z)
    (hZcomm : ∀ x : A.domain,
      A ⟨Z (x : H), hZdom x⟩ + B (Z (x : H)) = Z (A x) + Z (B (x : H)))
    (hUa : ∀ x : A.domain,
      (x : H) ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic →
      (⟪A x, (x : H)⟫_ℂ).re ≤ a * ‖(x : H)‖ ^ 2)
    (hUb : ∀ x : A.domain,
      (x : H) ∈ (TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)ᗮ →
      b * ‖(x : H)‖ ^ 2 ≤ (⟪A x, (x : H)⟫_ℂ).re)
    (hab : a < b) {x : H}
    (hx : x ∈ TauCeti.LinearPMap.specRange hA (Set.Iic c) measurableSet_Iic)
    (hx0 : x ≠ 0) :
    ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
        measurableSet_Iic).offDiagonalPart Z x‖ /
      ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
        measurableSet_Iic).diagonalPart Z x‖ ≤ 2 * ‖B‖ / (b - a) := by
  obtain ⟨htan, hpole⟩ := tanTwoTheta_unbounded_residual_opNorm_complex hA hB hZsa hZ2
    hZdom hZcomm hUa hUb hab hx
  have hδ : 0 < b - a := by linarith
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hκ : 0 < TauCeti.diagonalBlockBound (b - a) ‖B‖ := by
    rw [TauCeti.diagonalBlockBound_eq]
    have : (0 : ℝ) < √((b - a) ^ 2 + 4 * ‖B‖ ^ 2) :=
      Real.sqrt_pos.mpr (by positivity)
    positivity
  have hden : 0 < ‖(TauCeti.LinearPMap.specRange hA (Set.Iic c)
      measurableSet_Iic).diagonalPart Z x‖ :=
    lt_of_lt_of_le (by positivity) hpole
  rw [div_le_div_iff₀ hden hδ]
  linarith [htan]

end

end DavisKahan1970
end TauCeti
