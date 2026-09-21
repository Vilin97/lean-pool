/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5

Staged for Tau Ceti: a new file alongside the spectral-subspace API.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-! # The two-level spectral model

`TauCeti.twoLevelOperator a b U` is the symmetric operator acting as `b` on `U`
and as `a` on `Uᗮ` — equivalently `a + (b - a) P_U`.  It is the canonical
spectral-perturbation example: a subspace, a gap, and nothing else.  Every
"take `Σ` with two eigenvalues and move the eigenspace" construction in the
Davis--Kahan literature is one of these, and stating the model this way keeps
the sharpness arguments basis-free.

The payoff is `twoLevelOperator_sub`: two models over the same pair of levels
differ by exactly `(b - a)` times the projector difference, so a perturbation
norm *is* an angle, with no coordinates in sight.

## Main results

* `TauCeti.eigenspace_twoLevelOperator`: the top eigenspace is `U` itself.
* `TauCeti.le_of_hasEigenvalue_twoLevelOperator`: the spectrum lies below `b`.
* `TauCeti.pointInternalGap_twoLevelOperator`: `U` is separated from `Uᗮ` by `b - a`.
* `TauCeti.twoLevelOperator_sub`: the perturbation is a scaled projector
  difference.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The symmetric operator acting as `b` on `U` and as `a` on `Uᗮ`. -/
noncomputable def twoLevelOperator (a b : ℝ) (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : E →ₗ[𝕜] E :=
  (a : 𝕜) • LinearMap.id + ((b : 𝕜) - (a : 𝕜)) • projection U

variable {a b : ℝ} {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
  [V.HasOrthogonalProjection]

/-- Pointwise formula: the two-level operator is `a` off `U` and `b` on `U`,
written as a scalar plus a multiple of the projection. -/
theorem twoLevelOperator_apply (x : E) :
    twoLevelOperator a b U x =
      (a : 𝕜) • x + ((b : 𝕜) - (a : 𝕜)) • projection U x := by
  simp [twoLevelOperator]

/-- The quadratic form of an orthogonal projector is the squared norm of the
projection. -/
theorem inner_projection_self (W : Submodule 𝕜 E) [W.HasOrthogonalProjection]
    (x : E) :
    ⟪projection W x, x⟫_𝕜 = ((‖projection W x‖ : ℝ) : 𝕜) ^ 2 := by
  have hmem : projection W x ∈ W := W.starProjection_apply_mem x
  have hperp : x - projection W x ∈ Wᗮ := W.sub_starProjection_mem_orthogonal x
  have hsplit : projection W x + (x - projection W x) = x := by abel
  calc ⟪projection W x, x⟫_𝕜
      = ⟪projection W x, projection W x + (x - projection W x)⟫_𝕜 := by rw [hsplit]
    _ = ⟪projection W x, projection W x⟫_𝕜
          + ⟪projection W x, x - projection W x⟫_𝕜 := inner_add_right _ _ _
    _ = ((‖projection W x‖ : ℝ) : 𝕜) ^ 2 := by
        rw [Submodule.inner_right_of_mem_orthogonal hmem hperp, add_zero,
          inner_self_eq_norm_sq_to_K]

/-- A two-level operator is symmetric: its two levels are real and the
projection is symmetric. -/
theorem isSymmetric_twoLevelOperator : (twoLevelOperator a b U).IsSymmetric := by
  intro x y
  simp only [twoLevelOperator_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, map_sub, RCLike.conj_ofReal]
  rw [projection_isSymmetric U x y]

/-- **The top eigenspace of the model is the subspace it was built from.** -/
theorem eigenspace_twoLevelOperator (hab : a ≠ b) :
    eigenspace (twoLevelOperator a b U) ((b : ℝ) : 𝕜) = U := by
  have hne : ((b : 𝕜) - (a : 𝕜)) ≠ 0 := by
    refine sub_ne_zero_of_ne ?_
    simpa using hab.symm
  ext x
  rw [Module.End.mem_eigenspace_iff, twoLevelOperator_apply]
  constructor
  · intro hx
    -- `(b - a) • P_U x = (b - a) • x`, and `b - a ≠ 0`.
    have h : ((b : 𝕜) - (a : 𝕜)) • projection U x = ((b : 𝕜) - (a : 𝕜)) • x := by
      linear_combination (norm := module) hx
    have hx' : projection U x = x := smul_right_injective E hne h
    exact hx' ▸ U.starProjection_apply_mem x
  · intro hx
    have hproj : projection U x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [hproj]
    module

/-- **The spectrum of the model lies below `b`.** -/
theorem le_of_hasEigenvalue_twoLevelOperator (hab : a ≤ b) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue (twoLevelOperator a b U) (lam : 𝕜)) :
    lam ≤ b := by
  obtain ⟨x, hxmem₀, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hlam
  have hxmem : x ∈ eigenspace (twoLevelOperator a b U) (lam : 𝕜) := hxmem₀
  have hx : twoLevelOperator a b U x = (lam : 𝕜) • x :=
    Module.End.mem_eigenspace_iff.mp hxmem
  -- Take the quadratic form of both sides.
  have h := congrArg (fun y => RCLike.re (⟪y, x⟫_𝕜)) hx
  simp only [twoLevelOperator_apply, inner_add_left, inner_smul_left, map_sub,
    RCLike.conj_ofReal, map_add, inner_projection_self,
    inner_self_eq_norm_sq_to_K] at h
  have hq : a * ‖x‖ ^ 2 + (b - a) * ‖projection U x‖ ^ 2 = lam * ‖x‖ ^ 2 := by
    simpa using h
  have hple : ‖projection U x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have hle := U.norm_starProjection_apply_le x
    have h0 : (0 : ℝ) ≤ ‖projection U x‖ := norm_nonneg _
    change ‖projection U x‖ ≤ ‖x‖ at hle
    nlinarith
  have hxpos : (0 : ℝ) < ‖x‖ ^ 2 := by
    have hne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    positivity
  nlinarith [hq, hple, hxpos]

/-- Cancelling a scalar against a nonzero vector. -/
private theorem eq_of_smul_eq_smul_right {α β : 𝕜} {x : E} (hx : x ≠ 0)
    (h : α • x = β • x) : α = β := by
  by_contra hne
  have hz : (α - β) • x = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp hz with h' | h'
  · exact hne (sub_eq_zero.mp h')
  · exact hx h'

/-- The restricted spectrum on the top block is `{b}` and on its complement is
`{a}`, so the two blocks are separated by `b - a`.

No `a < b` hypothesis: the separation is stated as the signed difference, which
is the gap when `a < b` and a weaker true statement otherwise. -/
theorem pointInternalGap_twoLevelOperator :
    PointInternalGap (twoLevelOperator a b U) U (b - a) := by
  have hU : IsInvariant (twoLevelOperator a b U) U := by
    intro x hx
    rw [twoLevelOperator_apply,
      show projection U x = x from Submodule.starProjection_eq_self_iff.mpr hx]
    exact U.add_mem (U.smul_mem _ hx) (U.smul_mem _ hx)
  refine ⟨hU, ?_⟩
  intro lam μ hlam hμ
  -- On `U` the operator is multiplication by `b`.
  have hb : lam = b := by
    obtain ⟨x, hxU, hx0, hxeq⟩ := mem_restrictedPointSpectrum_iff.mp hlam
    have hproj : projection U x = x := Submodule.starProjection_eq_self_iff.mpr hxU
    rw [twoLevelOperator_apply, hproj] at hxeq
    have hsm : ((b : ℝ) : 𝕜) • x = ((lam : ℝ) : 𝕜) • x := by
      rw [← hxeq]; module
    exact_mod_cast (eq_of_smul_eq_smul_right hx0 hsm).symm
  -- On `Uᗮ` it is multiplication by `a`.
  have ha : μ = a := by
    obtain ⟨x, hxU, hx0, hxeq⟩ := mem_restrictedPointSpectrum_iff.mp hμ
    have hproj : projection U x = 0 := by
      change U.starProjection x = 0
      rw [Submodule.starProjection_apply_eq_zero_iff]
      exact hxU
    rw [twoLevelOperator_apply, hproj, smul_zero, add_zero] at hxeq
    exact_mod_cast (eq_of_smul_eq_smul_right hx0 hxeq).symm
  rw [hb, ha]
  exact le_abs_self _

/-- Mathlib's sorted eigenvalue list of the model is bounded by the top level. -/
theorem eigenvalues_twoLevelOperator_le [FiniteDimensional 𝕜 E] {n : ℕ}
    (hab : a ≤ b) (hn : finrank 𝕜 E = n) (i : Fin n) :
    (isSymmetric_twoLevelOperator (a := a) (b := b) (U := U)).eigenvalues hn i ≤ b :=
  le_of_hasEigenvalue_twoLevelOperator hab
    (isSymmetric_twoLevelOperator.hasEigenvalue_eigenvalues hn i)

/-- **Two models over the same levels differ by a scaled projector
difference.**  This is what turns a perturbation norm into an angle. -/
theorem twoLevelOperator_sub :
    twoLevelOperator a b U - twoLevelOperator a b V =
      ((b : 𝕜) - (a : 𝕜)) • (projection U - projection V) := by
  ext x
  simp only [LinearMap.sub_apply, twoLevelOperator_apply, LinearMap.smul_apply,
    smul_sub]
  abel

end TauCeti
