/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

/-
Staged for Mathlib: additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`SinTwoThetaUINorm.lean`).

Formalized by Claude Fable 5 (claude-fable-5[1m]), plan step G1 of
the July 2026 completion campaign (Git history).

The subspace Davis–Kahan sin 2Θ theorem, in every unitarily invariant norm:
`N (Q ∘ P̂ ∘ P) ≤ N (S − T) / (b − a)`, where `P, Q = 1 − P` split along a
`T`-invariant subspace across whose splitting the quadratic form of `T` jumps
from `≤ a` to `≥ b`, and `P̂` projects onto any `S`-invariant subspace.  The
operator `2 (Q ∘ P̂ ∘ P)` has singular values `sin 2θᵢ` (the θᵢ the principal
angles between the two subspaces), so this is `‖sin 2Θ‖ ≤ 2 ‖S − T‖ / (b − a)`
— the gap hypothesis lives on ONE operator only, and no smallness of the
perturbation is assumed.

Proved by the mirror reduction (Davis–Kahan III, §8): reflect `T` through the
perturbed subspace, `T' := J T J` with `J = 2 P̂ − 1`, and apply the sin Θ
theorem (`SinThetaUINorm.lean`) to the pair `(T, T')` — the reflected subspace
`J (Uᗮ)` is `T'`-invariant with the transported form bound, so the pair is
separated by `T`'s own gap; the resulting cross-projection is `J`-conjugate to
`Q ∘ J ∘ P = 2 (Q ∘ P̂ ∘ P)`, and `N (T' − T) ≤ 2 N (S − T)` because `J`
commutes with `S`.
To be re-authored per Mathlib's AI-contribution policy at PR time.
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.SinTheta.UnitarilyInvariant
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AngleGeometry
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Gap
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace

/-! # The subspace Davis–Kahan sin 2Θ theorem, every unitarily invariant norm

## Statement cross-check (statement-first gate, plan step G1)

The classical subspace sin 2Θ theorem (Davis–Kahan 1970, part III, §8; see
also Bhatia, *Matrix Analysis*, VII.3 notes) reads: if the spectrum of the
symmetric `T` splits across a gap `(a, b)` along an invariant subspace `U`,
and `P̂` is a spectral projection of the perturbed operator `S = T + H`, then
`‖sin 2Θ‖ ≤ 2 ‖H‖ / (b − a)` in every unitarily invariant norm, where `Θ` is
the operator angle between `U` and `ran P̂`.  Distinctive features, mirrored
exactly here:

* the gap hypothesis constrains **one operator only** (`T`; two-sided:
  form `≥ b` on `U`, `≤ a` on `Uᗮ`) — unlike sin Θ, which needs a cross-gap
  between the two operators' spectral blocks;
* **no smallness** of `H` and **no location constraint** on the perturbed
  subspace are required (our `V` is merely `S`-invariant — spectral selection
  is not even mentioned, which is strictly more general than the classical
  statement; the degenerate sanity check `S = T` forces the conclusion `0 ≤ 0`
  because a `T`-invariant `V` then splits along `U ⊕ Uᗮ`);
* the constant is `2`, carried here by the identity
  `Q ∘ J ∘ P = 2 (Q ∘ P̂ ∘ P)` with `J = 2 P̂ − 1` the reflection.

Encoding of `sin 2Θ`: the conclusion bounds `N (Q ∘ P̂ ∘ P)` by
`N (S − T) / (b − a)`.  In a joint CS basis the operator `2 (Q ∘ P̂ ∘ P)` has
singular values `2 sin θᵢ cos θᵢ = sin 2θᵢ`, so `2 (Q ∘ P̂ ∘ P)` *is* the
`sin 2Θ` operator; certifying that dictionary in Lean (the analogue of the E2
identification for `sin Θ`) is the deferred principal-angle brick recorded in
the plan — the *norm bound* proved here is the analytic content of the
theorem.  The sharper mirror-defect form
`2 N (Q ∘ P̂ ∘ P) ≤ N (J T J − T) / (b − a)` (with `J T J − T` twice the
`J`-odd part of `H` when `J S = S J`) is stated separately: it needs no `S`
at all, only the reflection.

## Main results

* `TauCeti.UnitarilyInvariantSeminorm.sin_two_theta_reflection_le`: the
  mirror-defect bound `2 N (Q ∘ W.starProjection ∘ P) ≤ N (J T J − T) / (b−a)`
  for an arbitrary subspace `W` with reflection `J`.
* `TauCeti.UnitarilyInvariantSeminorm.sin_two_theta_starProjection_le`: the
  sin 2Θ theorem `N (Q ∘ P̂ ∘ P) ≤ N (S − T) / (b − a)`.

## References

* C. Davis and W. M. Kahan, *The rotation of eigenvectors by a
  perturbation. III*, SIAM J. Numer. Anal. 7 (1970), 1–46 (§8).
* R. Bhatia, *Matrix Analysis*, Chapter VII.
* C. Davis, *The rotation of eigenvectors by a perturbation*, J. Math. Anal.
  Appl. 6 (1963), 159–173 (the per-vector case, formalized in
  `RotationSharp.lean`).
-/

namespace TauCeti
open scoped InnerProductSpace
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] [CompleteSpace E] {T S : E →ₗ[𝕜] E}

namespace UnitarilyInvariantSeminorm

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
private theorem coe_apply (f : E ≃ₗᵢ[𝕜] E) (v : E) : f.toLinearMap v = f v := rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
private theorem coe_equiv_apply (f : E ≃ₗᵢ[𝕜] E) (v : E) :
    (f.toLinearEquiv : E →ₗ[𝕜] E) v = f v := rfl

omit [FiniteDimensional 𝕜 E] [CompleteSpace E] in
/-- The scalar `((2 : ℝ) : 𝕜)`-multiple agrees with the `ℕ`-double appearing in
`Submodule.reflection_apply`.  Auxiliary. -/
private theorem ofReal_two_smul (y : E) : ((2 : ℝ) : 𝕜) • y = 2 • y := by
  rw [show ((2 : ℝ) : 𝕜) = ((2 : ℕ) : 𝕜) by norm_cast, Nat.cast_smul_eq_nsmul]

/-- **The mirror-defect sin 2Θ bound.**  Let `T` be symmetric with an invariant
subspace `U` across whose splitting the quadratic form of `T` jumps from `≤ a`
(on `Uᗮ`) to `≥ b` (on `U`), and let `W` be *any* subspace, with reflection
`J = 2 W.starProjection − 1`.  Then for every unitarily invariant norm,

`2 N (Uᗮ.starProjection ∘ W.starProjection ∘ U.starProjection) ≤ N (J T J − T) / (b − a)`.

The right side is the *mirror defect* of `T` — how far `T` is from commuting
with the reflection through `W`; no second operator is involved. -/
theorem sin_two_theta_reflection_le (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) {U W : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [W.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    2 * N ((Uᗮ.starProjection ∘L W.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap - T)
        / (b - a) := by
  have hg : (0 : ℝ) < b - a := by linarith
  -- The reflected operator `T' = J T J` and the reflected subspace `J (Uᗮ)`.
  set T' : E →ₗ[𝕜] E :=
    W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap with hT'def
  have hT'sym : T'.IsSymmetric := by
    have h := isSymmetric_conj_unitary hT (W.reflection (𝕜 := 𝕜))
    rwa [Submodule.reflection_symm] at h
  have hUperp_inv : ∀ x ∈ Uᗮ, T x ∈ Uᗮ := fun x hx =>
    map_mem_orthogonal_of_forall_map_mem hT hUinv hx
  set V' : Submodule 𝕜 E :=
    Uᗮ.map ((W.reflection (𝕜 := 𝕜)).toLinearEquiv : E →ₗ[𝕜] E) with hV'def
  -- `V'` is `T'`-invariant.
  have hV'inv : ∀ x ∈ V', T' x ∈ V' := by
    rintro x ⟨w, hw, rfl⟩
    refine Submodule.mem_map.mpr ⟨T w, hUperp_inv w hw, ?_⟩
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      hT'def, LinearMap.comp_apply, Submodule.reflection_reflection]
  -- The form of `T'` on `V'` sits below `a`.
  have hV'form : ∀ x ∈ V', RCLike.re ⟪T' x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2 := by
    rintro x ⟨w, hw, rfl⟩
    simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
    have happly : T' (W.reflection w) = W.reflection (T w) := by
      simp only [hT'def, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearIsometryEquiv.coe_toLinearEquiv, Submodule.reflection_reflection]
    rw [happly, (W.reflection (𝕜 := 𝕜)).inner_map_map,
      (W.reflection (𝕜 := 𝕜)).norm_map]
    exact hUa w hw
  -- The form of `T` on `U` sits above `a + (b − a) = b`.
  have hUform : ∀ x ∈ U, (a + (b - a)) * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜 := by
    intro x hx
    have hb' : a + (b - a) = b := by ring
    rw [hb']
    exact hUb x hx
  -- The sin Θ theorem for the pair `(T, T')` across `T`'s own gap.
  have hmain := N.apply_starProjection_comp_starProjection_le hT hT'sym
    hUinv hV'inv hg hUform hV'form
  -- Identify the cross-projection: `P_{V'} ∘ P_U = J ∘ (P_{Uᗮ} ∘ J ∘ P_U)`.
  have hVsP : ∀ x, V'.starProjection x
      = W.reflection (Uᗮ.starProjection (W.reflection x)) := by
    intro x
    change (Uᗮ.map ((W.reflection (𝕜 := 𝕜)).toLinearEquiv : E →ₗ[𝕜] E)).starProjection x
      = W.reflection (Uᗮ.starProjection (W.reflection x))
    rw [Submodule.starProjection_map_apply, Submodule.reflection_symm]
  have hconj : ((V'.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = W.reflection.toLinearMap
          ∘ₗ ((Uᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ W.reflection.toLinearMap
          ∘ₗ ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    ext x
    simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      LinearMap.comp_apply, coe_apply]
    exact hVsP _
  -- Kill the outer reflection and halve the inner one: `Q ∘ J ∘ P = 2 Q P̂ P`.
  have hkey : ((Uᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ W.reflection.toLinearMap
        ∘ₗ ((U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = ((2 : ℝ) : 𝕜) • ((Uᗮ.starProjection ∘L W.starProjection
          ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) := by
    ext x
    have hz : Uᗮ.starProjection (U.starProjection x) = 0 := by
      refine Submodule.eq_starProjection_of_mem_orthogonal
        (Submodule.zero_mem Uᗮ) ?_
      simp only [sub_zero]
      exact U.le_orthogonal_orthogonal (U.starProjection_apply_mem x)
    simp only [LinearMap.comp_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, coe_apply,
      Submodule.reflection_apply, map_sub, map_nsmul, hz, sub_zero,
      ofReal_two_smul]
  calc 2 * N ((Uᗮ.starProjection ∘L W.starProjection ∘L U.starProjection
          : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = N (((2 : ℝ) : 𝕜) • ((Uᗮ.starProjection ∘L W.starProjection
          ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)) := by
        rw [N.smul_eq, RCLike.norm_ofReal]
        norm_num
    _ = N (((V'.starProjection ∘L U.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E))
        := by rw [hconj, N.invariant_left, hkey]
    _ ≤ N (T' - T) / (b - a) := hmain

/-- **The subspace Davis–Kahan sin 2Θ theorem, every unitarily invariant
norm.**  Let `T, S` be symmetric, `U` a `T`-invariant subspace with the
two-sided form separation `re ⟪T x, x⟫ ≥ b ‖x‖²` on `U` and `≤ a ‖x‖²` on
`Uᗮ` (`a < b` — the gap constrains `T` alone), and `V` any `S`-invariant
subspace.  Then

`N (Uᗮ.starProjection ∘ V.starProjection ∘ U.starProjection) ≤ N (S − T) / (b − a)`.

The operator `2 (Q ∘ P̂ ∘ P)` on the left has singular values `sin 2θᵢ`, so
this is `‖sin 2Θ‖ ≤ 2 ‖S − T‖ / (b − a)` — no smallness of the perturbation,
and no spectral-location constraint on `V`. -/
theorem sin_two_theta_starProjection_le (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    N ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) := by
  have hg : (0 : ℝ) < b - a := by linarith
  -- The mirror-defect bound with the perturbed subspace as the mirror.
  have h1 := N.sin_two_theta_reflection_le (W := V) hT hUinv hab hUb hUa
  -- The reflection through the `S`-invariant `V` commutes with `S`.
  have hcomm : ∀ x, V.reflection (S x) = S (V.reflection x) := by
    intro x
    have hc := starProjection_comp_toContinuousLinearMap_comm hS hVinv x
    rw [Submodule.reflection_apply, Submodule.reflection_apply, map_sub,
      map_nsmul, hc]
  have hJSJ : V.reflection.toLinearMap ∘ₗ S ∘ₗ V.reflection.toLinearMap = S := by
    ext x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toLinearEquiv]
    rw [← hcomm, Submodule.reflection_reflection]
  -- The mirror defect of `T` is twice the perturbation:
  -- `J T J − T = J (T − S) J + (S − T)`.
  have hident : V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T
      = V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
        + (S - T) := by
    have hexp : V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
        = V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap
          - V.reflection.toLinearMap ∘ₗ S ∘ₗ V.reflection.toLinearMap := by
      ext x
      simp [map_sub]
    rw [hexp, hJSJ]
    abel
  have hbound : N (V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T)
      ≤ 2 * N (S - T) := by
    rw [hident]
    calc N (V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap
          + (S - T))
        ≤ N (V.reflection.toLinearMap ∘ₗ (T - S) ∘ₗ V.reflection.toLinearMap)
          + N (S - T) := N.add_le _ _
      _ = N (T - S) + N (S - T) := by
          rw [N.invariant V.reflection V.reflection (T - S)]
      _ = 2 * N (S - T) := by
          rw [show T - S = -(S - T) by abel, N.apply_neg]
          ring
  have h2 : N (V.reflection.toLinearMap ∘ₗ T ∘ₗ V.reflection.toLinearMap - T)
        / (b - a)
      ≤ 2 * N (S - T) / (b - a) := by gcongr
  have h3 := h1.trans h2
  have h4 : 2 * N (S - T) / (b - a) = 2 * (N (S - T) / (b - a)) := by ring
  linarith

/-- **The Frobenius subspace sin 2Θ theorem.**  The every-UI-norm sin 2Θ bound
instantiated at the Frobenius norm:
`‖Uᗮ.sP ∘ V.sP ∘ U.sP‖_F ≤ ‖S − T‖_F / (b − a)`.  With
`sin_two_theta_starProjection_le`'s dictionary the left side is `‖½ sin 2Θ‖_F`;
unfold either side with `frobenius_apply` for the column-norm-sum reading. -/
theorem frobenius_sin_two_theta_starProjection_le
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hUinv : ∀ x ∈ U, T x ∈ U) (hVinv : ∀ x ∈ V, S x ∈ V)
    {a b : ℝ} (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪T x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪T x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2) :
    frobenius (𝕜 := 𝕜) (E := E) (F := E) ((Uᗮ.starProjection ∘L V.starProjection ∘L U.starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ frobenius (𝕜 := 𝕜) (E := E) (F := E) (S - T) / (b - a) :=
  (frobenius (𝕜 := 𝕜) (E := E) (F := E)).sin_two_theta_starProjection_le hT hS hUinv hVinv hab
    hUb hUa

/-! ### Spectral (eigenvalue-hypothesis) forms

The subspace headline `sin_two_theta_starProjection_le` and its mirror-defect
companion, specialized to spectral subspaces: `U` is the span of the
`T`-eigenvectors selected by `s`, whose eigenvalues sit above `b` while the
complementary ones sit below `a`; `V` is the analogous `S`-eigenblock selected
by `s'`.  This is the every-UI-norm sin 2Θ theorem in the eigenvalue-hypothesis
form the literature states, mirroring
`SinThetaOpNorm.norm_starProjection_comp_starProjection_le_of_eigenvalues`
(plan step OP1). -/

section Spectral

variable {n : ℕ}

/-- **Subspace sin 2Θ, every unitarily invariant norm, spectral form.**  With
`U` the `T`-eigenblock selected by `s` (selected eigenvalues `≥ b`, complementary
`≤ a`) and `V` the `S`-eigenblock selected by `s'`,
`N (Uᗮ.sP ∘ V.sP ∘ U.sP) ≤ N (S − T) / (b − a)` for every unitarily invariant
norm `N`.  The left side is `N (½ sin 2Θ)` (see the module docstring). -/
theorem sin_two_theta_starProjection_le_of_eigenvalues (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = n)
    {s s' : Finset (Fin n)} {a b : ℝ} (hab : a < b)
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a) :
    N ((((hT.eigenvectorBasis hn).spanIndices ↑s)ᗮ.starProjection ∘L
        ((hS.eigenvectorBasis hn).spanIndices ↑s').starProjection ∘L
        ((hT.eigenvectorBasis hn).spanIndices ↑s).starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (S - T) / (b - a) :=
  N.sin_two_theta_starProjection_le hT hS
    (fun _ hx => LinearMap.IsSymmetric.map_mem_spanIndices hT hn _ hx)
    (fun _ hx => LinearMap.IsSymmetric.map_mem_spanIndices hS hn _ hx) hab
    (fun _ hx => LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices hT hn (fun i hi
      => hb i hi) hx)
    (fun w hw => by
      rw [OrthonormalBasis.orthogonal_spanIndices] at hw
      exact LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices hT hn (fun i hi =>
        ha i hi) hw)

/-- **Mirror-defect sin 2Θ, spectral form.**  As
`sin_two_theta_starProjection_le_of_eigenvalues` but with an arbitrary subspace
`W` in the middle and the sharper mirror-defect right side (no second operator):
`2 N (Uᗮ.sP ∘ W.sP ∘ U.sP) ≤ N (J T J − T) / (b − a)`, `J = W.reflection`. -/
theorem sin_two_theta_reflection_le_of_eigenvalues (N : UnitarilyInvariantSeminorm 𝕜 E E)
    (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (W : Submodule 𝕜 E)
    [W.HasOrthogonalProjection] {s : Finset (Fin n)} {a b : ℝ} (hab : a < b)
    (hb : ∀ i ∈ s, b ≤ hT.eigenvalues hn i)
    (ha : ∀ i ∉ s, hT.eigenvalues hn i ≤ a) :
    2 * N ((((hT.eigenvectorBasis hn).spanIndices ↑s)ᗮ.starProjection ∘L
        W.starProjection ∘L
        ((hT.eigenvectorBasis hn).spanIndices ↑s).starProjection
        : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ≤ N (W.reflection.toLinearMap ∘ₗ T ∘ₗ W.reflection.toLinearMap - T) / (b - a) :=
  N.sin_two_theta_reflection_le hT
    (fun _ hx => LinearMap.IsSymmetric.map_mem_spanIndices hT hn _ hx) hab
    (fun _ hx => LinearMap.IsSymmetric.le_re_inner_apply_self_of_mem_spanIndices hT hn (fun i hi
      => hb i hi) hx)
    (fun w hw => by
      rw [OrthonormalBasis.orthogonal_spanIndices] at hw
      exact LinearMap.IsSymmetric.re_inner_apply_self_le_of_mem_spanIndices hT hn (fun i hi =>
        ha i hi) hw)

end Spectral

/-! ### The sin 2Θ singular-value dictionary (plan step OP3.B)

Certifies that the G1 left side `Q P̂ P` is `½ sin 2Θ`: its singular values are
`cos θᵢ sin θᵢ`, so for every unitarily invariant norm
`N (Q P̂ P) = N (diagOp (cos θᵢ sin θᵢ))`.  The proof is Opus's operator reroute
(plan v9): `M⋆M = C − C²` with `C = gram (P̂ P)` self-adjoint, whose eigenvalues
are `σ(P̂ P)² = cos²θᵢ` by the cos Θ dictionary
`singularValues_starProjection_comp_starProjection` (OP3.A); matching against
`diagOp` on `C`'s eigenbasis and reading off through `singularValues_eq_of_gram_eq`
and `apply_eq_gauge`. -/

section Dictionary

variable {d : ℕ}

omit [CompleteSpace E] in
/-- **The sin 2Θ dictionary.**  For orthonormal families `u, v` spanning `U, V`,
`P = P_U`, `P̂ = P_V`, `Q = P_{Uᗮ}`, and every unitarily invariant norm `N`,
`N (Q ∘ P̂ ∘ P) = N (diagOp bC (fun i ↦ cᵢ √(1 − cᵢ²)))` where
`cᵢ = cosPrincipalAngles hv hu i` and `bC` is the eigenbasis of `gram (P̂ P)`.
Since `2 cᵢ √(1 − cᵢ²) = sin 2θᵢ`, the left side is `N (½ sin 2Θ)` — the
every-UI-norm analogue of the E2 op-norm identification
`norm_orthogonal_starProjection_comp_starProjection`. -/
theorem apply_orthogonal_starProjection_comp_starProjection_comp
    (N : UnitarilyInvariantSeminorm 𝕜 E E) {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    N ((((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range v)).starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E)
        : E →ₗ[𝕜] E))
      = N (diagOp ((((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E)
            : E →ₗ[𝕜] E).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
          (fun i => cosPrincipalAngles hv hu i
            * Real.sqrt (1 - cosPrincipalAngles hv hu i ^ 2))) := by
  classical
  set P : E →ₗ[𝕜] E := ((Submodule.span 𝕜 (Set.range u)).starProjection : E →ₗ[𝕜] E) with hPdef
  set Ph : E →ₗ[𝕜] E := ((Submodule.span 𝕜 (Set.range v)).starProjection : E →ₗ[𝕜] E) with hPhdef
  set Q : E →ₗ[𝕜] E := ((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →ₗ[𝕜] E) with hQdef
  set PhP : E →ₗ[𝕜] E := (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
    (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) with hPhPdef
  set M : E →ₗ[𝕜] E := (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
    (Submodule.span 𝕜 (Set.range v)).starProjection ∘L
    (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) with hMdef
  set c : ℕ → ℝ := fun k => cosPrincipalAngles hv hu k with hcdef
  set C : E →ₗ[𝕜] E := P ∘ₗ Ph ∘ₗ P with hCdef
  -- Pointwise projection facts.
  have hPP : ∀ z, P (P z) = P z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr ((Submodule.span 𝕜 (Set.range
      u)).starProjection_apply_mem z)
  have hPhPh : ∀ z, Ph (Ph z) = Ph z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr ((Submodule.span 𝕜 (Set.range
      v)).starProjection_apply_mem z)
  have hQz : ∀ z, Q z = z - P z := fun z => by
    simp only [hQdef, hPdef, ContinuousLinearMap.coe_coe]
    rw [Submodule.starProjection_orthogonal]
    simp
  have hQQ : ∀ z, Q (Q z) = Q z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr
      ((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection_apply_mem z)
  have hPadj : LinearMap.adjoint P = P :=
    (Submodule.span 𝕜 (Set.range u)).starProjection_isSymmetric.adjoint_eq
  have hPhadj : LinearMap.adjoint Ph = Ph :=
    (Submodule.span 𝕜 (Set.range v)).starProjection_isSymmetric.adjoint_eq
  have hQadj : LinearMap.adjoint Q = Q :=
    (Submodule.span 𝕜 (Set.range u))ᗮ.starProjection_isSymmetric.adjoint_eq
  -- `M`, `PhP` as compositions.
  have hMcoe : M = Q ∘ₗ Ph ∘ₗ P := by
    refine LinearMap.ext fun x => ?_
    simp only [hMdef, hQdef, hPhdef, hPdef, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.comp_apply]
  have hPhPcoe : PhP = Ph ∘ₗ P := by
    refine LinearMap.ext fun x => ?_
    simp only [hPhPdef, hPhdef, hPdef, ContinuousLinearMap.coe_comp,
      ContinuousLinearMap.coe_coe, Function.comp_apply, LinearMap.comp_apply]
  -- `M⋆ = P ∘ Ph ∘ Q`, hence `M⋆M = C − C∘C`.
  have hMadj : LinearMap.adjoint M = P ∘ₗ Ph ∘ₗ Q := by
    simp only [hMcoe, LinearMap.adjoint_comp, hPadj, hPhadj, hQadj,
      LinearMap.comp_assoc]
  have hMM : LinearMap.adjoint M ∘ₗ M = C - C ∘ₗ C := by
    rw [hMadj, hMcoe]
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, hCdef]
    rw [hQQ, hQz (Ph (P x))]
    simp only [map_sub, hPhPh, hPP]
  -- `C = gram (P̂ P)`.
  have hCgram : C = LinearMap.adjoint PhP ∘ₗ PhP := by
    rw [hPhPcoe, LinearMap.adjoint_comp, hPadj, hPhadj]
    refine LinearMap.ext fun x => ?_
    simp only [hCdef, LinearMap.comp_apply, hPhPh]
  -- Eigenbasis of `gram (P̂ P)` and its eigenvalues `= c²`.
  set bC := PhP.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl with hbCdef
  have hσ : PhP.singularValues = cosPrincipalAngles hv hu := by
    rw [hPhPdef]; exact singularValues_starProjection_comp_starProjection hu hv
  have hCeig : ∀ i, C (bC i) = ((c i ^ 2 : ℝ) : 𝕜) • bC i := fun i => by
    rw [hCgram, PhP.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i]
    congr 2
    have := PhP.sq_singularValues_fin rfl i
    rw [hσ] at this
    rw [← this, hcdef]
  -- Bounds on `c`.
  have hc0 : ∀ k : ℕ, 0 ≤ c k := fun k => cosPrincipalAngles_nonneg hv hu k
  have hc1 : ∀ k : ℕ, c k ≤ 1 := fun k => by
    simp only [hcdef]
    rcases lt_or_ge k d with hk | hk
    · rw [cosPrincipalAngles_eq]
      exact singularValues_le_one_of_contraction (overlapOp_contraction hv hu)
        finrank_euclideanSpace_fin ⟨k, hk⟩
    · rw [cosPrincipalAngles_eq,
        (overlapOp hv hu).singularValues_of_finrank_le (by
          rw [finrank_euclideanSpace_fin]; exact hk)]
      exact zero_le_one
  -- Gram of `M` equals gram of the diagonal operator.
  set w : Fin (finrank 𝕜 E) → ℝ := fun i => c i * Real.sqrt (1 - c i ^ 2) with hwdef
  have hgram : LinearMap.adjoint M ∘ₗ M = LinearMap.adjoint (diagOp bC w) ∘ₗ diagOp bC w := by
    rw [hMM, adjoint_diagOp, diagOp_comp]
    refine bC.toBasis.ext fun i => ?_
    simp only [OrthonormalBasis.coe_toBasis]
    have hle : (0 : ℝ) ≤ 1 - c i ^ 2 := by nlinarith [hc0 i, hc1 i]
    have hwi : w i * w i = c i ^ 2 - c i ^ 2 * c i ^ 2 := by
      simp only [hwdef]
      rw [show c i * Real.sqrt (1 - c i ^ 2) * (c i * Real.sqrt (1 - c i ^ 2))
          = c i ^ 2 * Real.sqrt (1 - c i ^ 2) ^ 2 by ring, Real.sq_sqrt hle]
      ring
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hCeig, map_smul, smul_smul]
    rw [diagOp_apply_basis, Pi.mul_apply, hwi, ← sub_smul]
    congr 1
    push_cast
    ring
  -- Read off via the gauge.
  rw [N.apply_eq_gauge rfl bC M, N.apply_eq_gauge rfl bC (diagOp bC w),
    singularValues_eq_of_gram_eq hgram]

end Dictionary

end UnitarilyInvariantSeminorm

end TauCeti
namespace TauCeti
namespace DavisKahan.FiniteDimensional

open scoped InnerProductSpace BigOperators

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-! ## Canonical angle-operator wrappers -/

/-- Conjugation by the reflection through `V`. -/
noncomputable def reflectionConjugate (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  V.reflection.toLinearMap ∘ₗ A ∘ₗ V.reflection.toLinearMap

/-- The mirror defect `J A J - A` associated with the reflection through `V`. -/
noncomputable def reflectionDefect (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (A : E →ₗ[𝕜] E) : E →ₗ[𝕜] E :=
  reflectionConjugate V A - A

/-- The finite `sin 2 Theta` perturbation theorem in canonical
angle-operator form, for every unitarily invariant norm. -/
theorem sinTwoTheta_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hcross :
      N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
        N (B - A) / (b - a) := by
    simpa [projection, complementaryProjection] using
      N.sin_two_theta_starProjection_le hA hB hU hV hab hgap.1 hgap.2
  have hg : 0 < b - a := sub_pos.mpr hab
  rw [le_div_iff₀ hg] at hcross
  have hscale :
      N (sinTwoAngleOperator U V) =
        2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, N.smul_eq]
    norm_num
  rw [hscale]
  calc
    (b - a) * (2 * N
        (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)) =
        2 * ((b - a) * N
          (complementaryProjection U ∘ₗ projection V ∘ₗ projection U)) := by ring
    _ ≤ 2 * N (B - A) := by
      gcongr
      simpa [mul_comm] using hcross

/-- The one-sided cross-block normalization of the `sin 2 Theta` theorem. -/
theorem sinTwoTheta_cross_perturbation_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) *
        N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
      N (B - A) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have h := N.sin_two_theta_starProjection_le
    hA hB hU hV hab hgap.1 hgap.2
  rw [le_div_iff₀ (sub_pos.mpr hab)] at h
  simpa [projection, complementaryProjection, mul_comm] using h

/-- The mirror-defect form of the `sin 2 Theta` theorem.  It requires no
second operator. -/
theorem sinTwoTheta_reflectionDefect_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) {U V : Submodule 𝕜 E}
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (hU : IsInvariant A U) {a b : ℝ} (hab : a < b)
    (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ N (reflectionDefect V A) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hmirror :
      2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) ≤
        N (reflectionDefect V A) / (b - a) := by
    simpa [projection, complementaryProjection, reflectionDefect,
      reflectionConjugate] using
      N.sin_two_theta_reflection_le hA hU hab hgap.1 hgap.2
  rw [le_div_iff₀ (sub_pos.mpr hab)] at hmirror
  have hscale :
      N (sinTwoAngleOperator U V) =
        2 * N (complementaryProjection U ∘ₗ projection V ∘ₗ projection U) := by
    rw [sinTwoAngleOperator_eq_two_smul_cross, N.smul_eq]
    norm_num
  rw [hscale]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hmirror

/-- The reflection defect is at most twice the perturbation when `V` reduces
the second symmetric operator. -/
theorem reflectionDefect_le_two_mul_perturbation
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hB : B.IsSymmetric)
    {V : Submodule 𝕜 E} [V.HasOrthogonalProjection]
    (hV : IsInvariant B V) :
    N (reflectionDefect V A) ≤ 2 * N (B - A) := by
  let J : E →ₗ[𝕜] E := V.reflection.toLinearMap
  have hcomm : J ∘ₗ B = B ∘ₗ J := by
    ext x
    change V.reflection (B x) = B (V.reflection x)
    simp only [Submodule.reflection_apply, map_sub, map_nsmul]
    have hproj :
        V.starProjection (B x) = B (V.starProjection x) := by
      change projection V (B x) = B (projection V x)
      exact projection_apply_comm_of_isInvariant hB hV x
    rw [hproj]
  have hJinvol : J ∘ₗ J = LinearMap.id := by
    ext x
    change V.reflection (V.reflection x) = x
    exact V.reflection_reflection x
  have hconjB : J ∘ₗ B ∘ₗ J = B := by
    ext x
    have hc := LinearMap.congr_fun hcomm (J x)
    change J (B (J x)) = B (J (J x)) at hc
    have hj := LinearMap.congr_fun hJinvol x
    change J (J x) = x at hj
    change J (B (J x)) = B x
    calc
      J (B (J x)) = B (J (J x)) := hc
      _ = B x := congrArg B hj
  have hdef : reflectionDefect V A =
      J ∘ₗ (A - B) ∘ₗ J - (A - B) := by
    ext x
    simp only [reflectionDefect, reflectionConjugate, J, LinearMap.comp_apply,
      LinearMap.sub_apply, map_sub]
    have hb := LinearMap.congr_fun hconjB x
    change J (B (J x)) = B x at hb
    rw [hb]
    abel
  have hconjNorm : N (J ∘ₗ (A - B) ∘ₗ J) = N (A - B) := by
    simpa [J] using N.invariant V.reflection V.reflection (A - B)
  calc
    N (reflectionDefect V A) =
        N (J ∘ₗ (A - B) ∘ₗ J - (A - B)) := by rw [hdef]
    _ ≤ N (J ∘ₗ (A - B) ∘ₗ J) + N (-(A - B)) := by
      rw [sub_eq_add_neg]
      exact N.add_le _ _
    _ = N (A - B) + N (A - B) := by
      rw [hconjNorm, N.apply_neg]
    _ = 2 * N (B - A) := by
      have hsub : A - B = -(B - A) := by abel
      rw [hsub, N.apply_neg]
      ring

/-- The canonical spectral-subspace `sin 2 Theta` theorem. -/
theorem sinTwoTheta_pointSpectralSubspace_le
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {Ω : Set ℝ} {a b : ℝ} (hab : a < b)
    (hgap : TwoBlockFormGap A (pointSpectralSubspace A Ω) a b) :
    (b - a) * N (sinTwoAngleOperator (pointSpectralSubspace A Ω)
        (pointSpectralSubspace B Ω)) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB
    (isInvariant_pointSpectralSubspace A Ω) (isInvariant_pointSpectralSubspace B Ω) hab hgap

/-- The canonical angle-operator theorem already handles unequal finite ranks;
unmatched directions are represented by the singular-value padding convention. -/
theorem sinTwoTheta_perturbation_le_unequalFinrank
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * N (sinTwoAngleOperator U V) ≤ 2 * N (B - A) := by
  exact sinTwoTheta_perturbation_le N hA hB hU hV hab hgap

/-- Operator-norm specialization of `sinTwoTheta_perturbation_le`. -/
theorem opNorm_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * ‖(sinTwoAngleOperator U V).toContinuousLinearMap‖ ≤
      2 * ‖(B - A).toContinuousLinearMap‖ := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantSeminorm.opNorm (𝕜 := 𝕜) (E := E) (F := E))
    hA hB hU hV hab hgap

/-- Frobenius specialization of `sinTwoTheta_perturbation_le`. -/
theorem frobenius_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) :
    (b - a) * UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E)
      (sinTwoAngleOperator U V) ≤
      2 * UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F := E) (B - A) := by
  exact sinTwoTheta_perturbation_le (UnitarilyInvariantSeminorm.frobenius (𝕜 := 𝕜) (E := E) (F
    := E))
    hA hB hU hV hab hgap

/-- Ky Fan specialization of `sinTwoTheta_perturbation_le`. -/
theorem kyFan_sinTwoTheta_le
    {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {U V : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] (hU : IsInvariant A U) (hV : IsInvariant B V)
    {a b : ℝ} (hab : a < b) (hgap : TwoBlockFormGap A U a b) (k : ℕ) :
    (b - a) * kyFanSum k (sinTwoAngleOperator U V) ≤ 2 * kyFanSum k (B - A) := by
  let NK : UnitarilyInvariantSeminorm 𝕜 E E :=
    (UnitarilyInvariantSeminorm.kyFan
      (𝕜 := 𝕜) (E := E) (F := E) k)
  have h := sinTwoTheta_perturbation_le NK hA hB hU hV hab hgap
  simpa only [NK, UnitarilyInvariantSeminorm.kyFan_apply] using h

end DavisKahan.FiniteDimensional
end TauCeti
