/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaBranchFree
public import LeanPool.DavisKahan.DavisKahan.DoubleAngle.KyFanOrthonormal
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric

/-! # Tan Two Theta Ky Fan Finite Carrier -/

@[expose] public section

open TauCeti.DavisKahan.ExactSinTheta

/-!
# The `tan 2Θ` theorem at every unitary-invariant ideal, finite carrier

The Davis--Kahan 1970 Section 7 tangent-double-angle estimate on an
arbitrary `RCLike` Hilbert space, for a finite-dimensional invariant-graph
configuration: `U` is a finite-dimensional subspace, `A` is block diagonal
for `U ⊕ Uᗮ` in the quadratic-form sense, `H` is fully off-diagonal, and
the graph coordinate `T` of the perturbed invariant subspace is supported
on `U` with values in `Uᗮ`.

**Scope, stated plainly:** the *ambient* space may be infinite-dimensional,
but the *active configuration* may not — `[FiniteDimensional 𝕜 U]` is a
standing hypothesis, and the proof is a compression to the finite carrier
`M := U ⊔ T '' U` followed by transport back. This is an ambient-space
lifting of the finite-dimensional theorem, not the unrestricted
infinite-dimensional one, which is why the declarations carry
`_of_finiteDimensional_invariantSubspace` rather than the `_infinite` they
were originally given.

Within that scope the result is the source's norm statement: for every `k`,
the `k`-th Ky Fan
approximation-number prefix of any `tan 2Θ₀` representative is controlled
by that of `H` with constant two over the form gap, and consequently every
Fan-dominant unitary-invariant ideal family transports membership of `H`
to membership of `tan 2Θ₀` with the same gauge estimate.

## Method

Everything happens inside the finite-dimensional carrier
`M := U ⊔ T '' U`: the graph relation, the off-diagonal structure, and the
form bounds all compress exactly to `M`, because the invariance hypothesis
forces `(A + H)` to map the graph of `T` into `M`.  The compiled
finite-dimensional Ky Fan theorem
(`kyFan_doubleAngleTangent_offDiagonal_le`) applies to the compressions,
and the two Ky Fan prefixes transport back to the ambient operators along
`approximationSingularValue_comp_le` for the contractive inclusion and
projection, exactly for `T` and one-sidedly for `H`.
-/

namespace TauCeti
namespace DavisKahan.TanTwoTheta

open TauCeti.DavisKahan.FiniteDimensional

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

section Helpers

omit [CompleteSpace E] in
/-- The difference of nested orthogonal projections lands in the orthogonal
complement of the smaller subspace. -/
private theorem starProjection_sub_mem_orthogonal
    {U M : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hUM : U ≤ M) (x : E) :
    M.starProjection x - U.starProjection x ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [inner_sub_right]
  have h1 : ⟪w, M.starProjection x⟫_𝕜 = ⟪w, x⟫_𝕜 := by
    rw [← M.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (hUM hw)]
  have h2 : ⟪w, U.starProjection x⟫_𝕜 = ⟪w, x⟫_𝕜 := by
    rw [← U.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr hw]
  rw [h1, h2, sub_self]

omit [CompleteSpace E] in
/-- The orthogonal projection kills the orthogonal complement. -/
private theorem starProjection_eq_zero_of_mem_orthogonal
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    {x : E} (hx : x ∈ Uᗮ) :
    U.starProjection x = 0 := by
  have h := DFunLike.congr_fun (U.starProjection_orthogonal') x
  rw [sub_apply, one_apply_eq_self,
    Submodule.starProjection_eq_self_iff.mpr hx] at h
  exact sub_eq_self.mp h.symm

omit [CompleteSpace E] in
/-- The projection onto an intermediate subspace preserves the orthogonal
complement of a smaller subspace. -/
private theorem starProjection_mem_orthogonal_of_le
    {U M : Submodule 𝕜 E} [U.HasOrthogonalProjection]
    [M.HasOrthogonalProjection] (hUM : U ≤ M)
    {x : E} (hx : x ∈ Uᗮ) :
    M.starProjection x ∈ Uᗮ := by
  have h := starProjection_sub_mem_orthogonal (𝕜 := 𝕜) hUM x
  rwa [starProjection_eq_zero_of_mem_orthogonal hx, sub_zero] at h

omit [CompleteSpace E] in
/-- The residual of an orthogonal projection is orthogonal to the target. -/
private theorem sub_starProjection_mem_orthogonal'
    {U : Submodule 𝕜 E} [U.HasOrthogonalProjection] (x : E) :
    x - U.starProjection x ∈ Uᗮ := by
  rw [Submodule.mem_orthogonal]
  intro w hw
  rw [← inner_conj_symm, U.starProjection_inner_eq_zero x w hw, map_zero]

/-- Composition with contractions does not increase approximation singular
values. -/
private theorem approximationSingularValue_comp_contractions_le
    {E₁ F G G' : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']
    (n : ℕ) (L : F →L[𝕜] G) (K : E₁ →L[𝕜] F) (R : G' →L[𝕜] E₁)
    (hL : ‖L‖ ≤ 1) (hR : ‖R‖ ≤ 1) :
    approximationSingularValue n (L ∘L K ∘L R) ≤
      approximationSingularValue n K := by
  refine (approximationSingularValue_comp_le n L K R).trans ?_
  have h0 := approximationSingularValue_nonneg n K
  calc ‖L‖ * approximationSingularValue n K * ‖R‖
      ≤ 1 * approximationSingularValue n K * 1 := by
        refine mul_le_mul (mul_le_mul hL le_rfl h0 zero_le_one) hR
          (norm_nonneg _) ?_
        positivity
    _ = approximationSingularValue n K := by ring

end Helpers

section Main

variable {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
  {a b : ℝ}

private theorem compression_isSymmetric
    (M : Submodule 𝕜 E) [M.HasOrthogonalProjection]
    (B : E →L[𝕜] E) (hB : IsSelfAdjoint B) :
    (M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL : ↥M →L[𝕜] ↥M).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪((M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL) x : ↥M),
      y⟫_𝕜 = ⟪x, ((M.orthogonalProjectionOnto ∘L B ∘L M.subtypeL) y :
      ↥M)⟫_𝕜
  rw [Submodule.coe_inner, Submodule.coe_inner]
  change ⟪M.starProjection (B (x : E)), (y : E)⟫_𝕜 =
    ⟪(x : E), M.starProjection (B (y : E))⟫_𝕜
  calc ⟪M.starProjection (B (x : E)), (y : E)⟫_𝕜
      = ⟪B (x : E), M.starProjection (y : E)⟫_𝕜 :=
        M.inner_starProjection_left_eq_right _ _
    _ = ⟪B (x : E), (y : E)⟫_𝕜 := by
        rw [Submodule.starProjection_eq_self_iff.mpr y.2]
    _ = ⟪(x : E), B (y : E)⟫_𝕜 := hB.isSymmetric (x : E) (y : E)
    _ = ⟪M.starProjection (x : E), B (y : E)⟫_𝕜 := by
        rw [Submodule.starProjection_eq_self_iff.mpr x.2]
    _ = ⟪(x : E), M.starProjection (B (y : E))⟫_𝕜 :=
        M.inner_starProjection_left_eq_right _ _

private theorem tangent_singularValues_reindex
    (V : Type*) [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]
    (R : V →L[𝕜] V) (v : ℕ → ℝ) (hv : ∀ n, R.toLinearMap.singularValues n = v n)
    (S : Finset ℕ) :
    ∃ S' : Finset (Fin (finrank 𝕜 V)), S'.card ≤ S.card ∧
      ∑ n ∈ S, absDoubleAngleTangent (v n) =
        ∑ x ∈ S', absDoubleAngleTangent (R.toLinearMap.singularValues (x : ℕ)) := by
  classical
  set S' : Finset (Fin (finrank 𝕜 V)) :=
    Finset.univ.filter (fun j : Fin (finrank 𝕜 V) => (j : ℕ) ∈ S) with hS'def
  have hS'inj : ∀ x ∈ S', ∀ y ∈ S', (x : ℕ) = (y : ℕ) → x = y :=
    fun x _ y _ h => Fin.val_injective h
  have himg : S'.image (fun x : Fin (finrank 𝕜 V) => (x : ℕ)) =
      S.filter (fun n => n < finrank 𝕜 V) := by
    ext n
    simp only [hS'def, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
    · rintro ⟨hnS, hlt⟩
      exact ⟨⟨n, hlt⟩, hnS, rfl⟩
  have hS'card : S'.card ≤ S.card := by
    calc S'.card = (S'.image (fun x : Fin (finrank 𝕜 V) => (x : ℕ))).card :=
        (Finset.card_image_of_injOn hS'inj).symm
      _ = (S.filter (fun n => n < finrank 𝕜 V)).card := by rw [himg]
      _ ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have hLHS : ∑ n ∈ S, absDoubleAngleTangent (v n) =
      ∑ x ∈ S',
        absDoubleAngleTangent (R.toLinearMap.singularValues (x : ℕ)) := by
    have hsplit : ∑ n ∈ S,
          absDoubleAngleTangent (v n) =
        ∑ n ∈ S.filter (fun n => n < finrank 𝕜 V),
          absDoubleAngleTangent (v n) := by
      refine (Finset.sum_filter_of_ne ?_).symm
      intro n _ hne
      by_contra hlt
      exact hne (by
        rw [← hv n,
          R.toLinearMap.singularValues_of_finrank_le (Nat.le_of_not_lt hlt),
          absDoubleAngleTangent_zero])
    rw [hsplit, ← himg, Finset.sum_image hS'inj]
    exact Finset.sum_congr rfl fun x _ => by rw [hv (x : ℕ)]
  exact ⟨S', hS'card, hLHS⟩

/-- **The branch-free Ky Fan root of the `tan 2Θ` theorem on an arbitrary
Hilbert space** (finite-dimensional invariant configuration).

For *any* finite set of indices, the total branch-free double-angle tangent
of the graph-coordinate approximation numbers is controlled by the
corresponding approximation-number prefix of the off-diagonal perturbation,
with the sharp constant two.  **No branch is selected or assumed**: the
perturbed invariant subspace may make angles arbitrarily close to `π/2` with
the trial subspace, exactly as Davis and Kahan's Section 2 statement permits.

The index set is arbitrary rather than an initial segment because
`t ↦ 2t/|1 - t²|` is not monotone across the quarter turn, so a `tan 2Θ`
representative carries those numbers as a multiset; see
`DavisKahan/DoubleAngle/TanTwoThetaBranchFree.lean`.

The selected-branch prefix form
`kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantSubspace`
is derived from this one below, so the compression to the finite carrier is
carried out exactly once. -/
theorem sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (S : Finset ℕ) :
    (b - a) * ∑ n ∈ S,
        absDoubleAngleTangent (approximationSingularValue n T) ≤
      2 * kyFanApproximationGauge S.card H := by
  classical
  -- the finite-dimensional carrier of the whole configuration
  set W : Submodule 𝕜 E := U.map (T : E →ₗ[𝕜] E) with hWdef
  set M : Submodule 𝕜 E := U ⊔ W with hMdef
  have : FiniteDimensional 𝕜 W := Module.Finite.map U (T : E →ₗ[𝕜] E)
  have : FiniteDimensional 𝕜 M := inferInstance
  have : CompleteSpace M := FiniteDimensional.complete 𝕜 ↥M
  have hUM : U ≤ M := le_sup_left
  have hMperpU : Mᗮ ≤ Uᗮ := Submodule.orthogonal_le hUM
  have hTsplit : ∀ x : E, T x = T (U.starProjection x) := by
    intro x
    have hz := hTzero _ (sub_starProjection_mem_orthogonal' (𝕜 := 𝕜) x)
    have hadd : T x = T (U.starProjection x) +
        T (x - U.starProjection x) := by
      rw [← map_add]
      congr 1
      abel
    rw [hadd, hz, add_zero]
  have hTM : ∀ x : E, T x ∈ M := by
    intro x
    rw [hTsplit x]
    exact Submodule.mem_sup_right
      (Submodule.mem_map_of_mem (U.starProjection_apply_mem x))
  -- the compressions
  set A' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L A ∘L M.subtypeL with hA'def
  set H' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L H ∘L M.subtypeL with hH'def
  set T' : ↥M →L[𝕜] ↥M :=
    M.orthogonalProjectionOnto ∘L T ∘L M.subtypeL with hT'def
  have hcoeT : ∀ x : ↥M, ((T' x : ↥M) : E) = T (x : E) := by
    intro x
    change M.starProjection (T (x : E)) = T (x : E)
    exact Submodule.starProjection_eq_self_iff.mpr (hTM (x : E))
  -- the trial subspace inside the carrier
  set U' : Submodule 𝕜 ↥M := U.comap M.subtype with hU'def
  have : CompleteSpace U' := FiniteDimensional.complete 𝕜 ↥U'
  have hU'mem : ∀ x : ↥M, x ∈ U' ↔ (x : E) ∈ U := fun x => Iff.rfl
  have hU'perp : ∀ x : ↥M, x ∈ U'ᗮ ↔ (x : E) ∈ Uᗮ := by
    intro x
    constructor
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro w hw
      have hwM : w ∈ M := hUM hw
      have h := (Submodule.mem_orthogonal U' x).mp hx ⟨w, hwM⟩
        ((hU'mem ⟨w, hwM⟩).mpr hw)
      rwa [Submodule.coe_inner] at h
    · intro hx
      rw [Submodule.mem_orthogonal]
      intro w hw
      rw [Submodule.coe_inner]
      exact (Submodule.mem_orthogonal U (x : E)).mp hx (w : E)
        ((hU'mem w).mp hw)
  -- symmetry of the compressions
  -- transfer the block hypotheses to the carrier
  have hAU' : ∀ x ∈ U', A'.toLinearMap x ∈ U' := by
    intro x hx
    have hAx : A (x : E) ∈ U := hAU _ ((hU'mem x).mp hx)
    refine (hU'mem _).mpr ?_
    change M.starProjection (A (x : E)) ∈ U
    rw [Submodule.starProjection_eq_self_iff.mpr (hUM hAx)]
    exact hAx
  have hHU' : ∀ x ∈ U', H'.toLinearMap x ∈ U'ᗮ := by
    intro x hx
    have hHx : H (x : E) ∈ Uᗮ := hHU _ ((hU'mem x).mp hx)
    refine (hU'perp _).mpr ?_
    change M.starProjection (H (x : E)) ∈ Uᗮ
    exact starProjection_mem_orthogonal_of_le hUM hHx
  have hHUperp' : ∀ x ∈ U'ᗮ, H'.toLinearMap x ∈ U' := by
    intro x hx
    have hHx : H (x : E) ∈ U := hHUperp _ ((hU'perp x).mp hx)
    refine (hU'mem _).mpr ?_
    change M.starProjection (H (x : E)) ∈ U
    rw [Submodule.starProjection_eq_self_iff.mpr (hUM hHx)]
    exact hHx
  have hTmem' : ∀ x : ↥M, T'.toLinearMap x ∈ U'ᗮ := by
    intro x
    refine (hU'perp _).mpr ?_
    change ((T' x : ↥M) : E) ∈ Uᗮ
    rw [hcoeT]
    exact hTmem (x : E)
  have hTzero' : ∀ x ∈ U'ᗮ, T'.toLinearMap x = 0 := by
    intro x hx
    apply Subtype.ext
    change ((T' x : ↥M) : E) = ((0 : ↥M) : E)
    rw [hcoeT]
    exact hTzero _ ((hU'perp x).mp hx)
  -- transfer the quadratic-form bounds
  have hpair : ∀ (B : E →L[𝕜] E) (x : ↥M),
      ⟪(M.orthogonalProjectionOnto ∘L B ∘L
          M.subtypeL : ↥M →L[𝕜] ↥M).toLinearMap x, x⟫_𝕜 =
        ⟪B (x : E), (x : E)⟫_𝕜 := by
    intro B x
    rw [Submodule.coe_inner]
    change ⟪M.starProjection (B (x : E)), (x : E)⟫_𝕜 = _
    rw [M.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr x.2]
  have hUb' : ∀ x ∈ U', b * ‖x‖ ^ 2 ≤
      RCLike.re ⟪A'.toLinearMap x, x⟫_𝕜 := by
    intro x hx
    have h := hUb (x : E) ((hU'mem x).mp hx)
    rw [hpair A x]
    exact h
  have hUa' : ∀ x ∈ U'ᗮ, RCLike.re ⟪A'.toLinearMap x, x⟫_𝕜 ≤
      a * ‖x‖ ^ 2 := by
    intro x hx
    have h := hUa (x : E) ((hU'perp x).mp hx)
    rw [hpair A x]
    exact h
  -- transfer the graph invariance
  have hinv' : ∀ x ∈ U', ∃ y ∈ U',
      (A'.toLinearMap + H'.toLinearMap) (x + T'.toLinearMap x) =
        y + T'.toLinearMap y := by
    intro x hx
    obtain ⟨y, hyU, hy⟩ := hinv (x : E) ((hU'mem x).mp hx)
    refine ⟨⟨y, hUM hyU⟩, hyU, ?_⟩
    apply Subtype.ext
    change M.starProjection (A ((x : E) + M.starProjection (T (x : E)))) +
        M.starProjection (H ((x : E) + M.starProjection (T (x : E)))) =
      y + M.starProjection (T y)
    rw [Submodule.starProjection_eq_self_iff.mpr (hTM (x : E)),
      Submodule.starProjection_eq_self_iff.mpr (hTM y)]
    have hyM : y + T y ∈ M := M.add_mem (hUM hyU) (hTM y)
    calc M.starProjection (A ((x : E) + T (x : E))) +
          M.starProjection (H ((x : E) + T (x : E)))
        = M.starProjection ((A + H) ((x : E) + T (x : E))) := by
          rw [add_apply]
          exact (map_add M.starProjection _ _).symm
      _ = M.starProjection (y + T y) := by rw [hy]
      _ = y + T y := Submodule.starProjection_eq_self_iff.mpr hyM
  -- exact transport of the graph-coordinate singular values
  have hTfact : T = M.subtypeL ∘L T' ∘L M.orthogonalProjectionOnto := by
    ext x
    change T x = ((T' (M.orthogonalProjectionOnto x) : ↥M) : E)
    rw [hcoeT]
    change T x = T (M.starProjection x)
    have hperp : x - M.starProjection x ∈ Uᗮ :=
      hMperpU (sub_starProjection_mem_orthogonal' (𝕜 := 𝕜) x)
    have hz := hTzero _ hperp
    have hadd : T x = T (M.starProjection x) +
        T (x - M.starProjection x) := by
      rw [← map_add]
      congr 1
      abel
    rw [hadd, hz, add_zero]
  have hTa : ∀ n, approximationSingularValue n T' =
      approximationSingularValue n T := by
    intro n
    refine le_antisymm ?_ ?_
    · rw [hT'def]
      exact approximationSingularValue_comp_contractions_le n
        M.orthogonalProjectionOnto T M.subtypeL
        M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
    · conv_lhs => rw [hTfact]
      exact approximationSingularValue_comp_contractions_le n
        M.subtypeL T' M.orthogonalProjectionOnto
        M.norm_subtypeL_le M.orthogonalProjectionOnto_norm_le
  have hT'id : T'.toLinearMap.toContinuousLinearMap = T' := by
    ext x; rfl
  have hTsv : ∀ n, T'.toLinearMap.singularValues n =
      approximationSingularValue n T := by
    intro n
    have h := approximationSingularValue_eq_singularValues T'.toLinearMap n
    rw [hT'id] at h
    rw [← h, hTa n]
  -- the participating indices inside the finite carrier
  obtain ⟨S', hS'card, hLHS⟩ := tangent_singularValues_reindex ↥M T'
    (fun n => approximationSingularValue n T) hTsv S
  -- one-sided transport of the perturbation prefix
  have hH'id : H'.toLinearMap.toContinuousLinearMap = H' := by
    ext x; rfl
  have hHbridge : ∀ j : ℕ,
      TauCeti.kyFanSum j
        H'.toLinearMap = kyFanApproximationGauge j H' := by
    intro j
    rw [kyFanSum_eq_kyFanApproximationGauge j H'.toLinearMap,
      hH'id]
  have hHgauge : ∀ j : ℕ, kyFanApproximationGauge j H' ≤
      kyFanApproximationGauge j H := by
    intro j
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    refine Finset.sum_le_sum fun n _ => ?_
    rw [hH'def]
    exact approximationSingularValue_comp_contractions_le n
      M.orthogonalProjectionOnto H M.subtypeL
      M.orthogonalProjectionOnto_norm_le M.norm_subtypeL_le
  have hHmono : kyFanApproximationGauge S'.card H ≤
      kyFanApproximationGauge S.card H := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hS'card))
      fun n _ _ => approximationSingularValue_nonneg n H
  -- apply the branch-free finite theorem on the carrier
  have hfin := sum_absDoubleAngleTangent_le
    (compression_isSymmetric M A hA) (compression_isSymmetric M H hH) hAU' hHU' hHUperp' hTmem' hTzero'
    hUb' hUa' hinv' hab S'
  rw [hLHS]
  calc (b - a) * ∑ x ∈ S',
        absDoubleAngleTangent (T'.toLinearMap.singularValues (x : ℕ))
      ≤ 2 * TauCeti.kyFanSum S'.card
          H'.toLinearMap := hfin
    _ = 2 * kyFanApproximationGauge S'.card H' := by rw [hHbridge S'.card]
    _ ≤ 2 * kyFanApproximationGauge S'.card H := by linarith [hHgauge S'.card]
    _ ≤ 2 * kyFanApproximationGauge S.card H := by linarith

/-- **The Ky Fan root of the `tan 2Θ` theorem on an arbitrary Hilbert
space** (finite-dimensional invariant configuration).  Every prefix sum of
the double-angle tangents of the graph-coordinate approximation numbers is
controlled by the corresponding approximation-number prefix of the
off-diagonal perturbation, with the sharp constant two.

This is the selected-branch reading, recovered from the branch-free theorem
above: under `hT1` every principal angle is strictly acute, so the two
double-angle tangents agree termwise. -/
theorem kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantSubspace
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (k : ℕ) :
    (b - a) * ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T) ≤
      2 * kyFanApproximationGauge k H := by
  classical
  have hlt : ∀ n, approximationSingularValue n T < 1 := fun n =>
    lt_of_le_of_lt (approximationSingularValue_antitone T (Nat.zero_le n)) hT1
  have hnn : ∀ n, 0 ≤ approximationSingularValue n T := fun n =>
    approximationSingularValue_nonneg n T
  have hsame : ∀ n, doubleAngleTangent (approximationSingularValue n T) =
      absDoubleAngleTangent (approximationSingularValue n T) := fun n =>
    (absDoubleAngleTangent_eq_doubleAngleTangent (hlt n) (hnn n)).symm
  have hsum : ∑ n ∈ Finset.range k,
      doubleAngleTangent (approximationSingularValue n T) =
        ∑ n ∈ Finset.range k,
          absDoubleAngleTangent (approximationSingularValue n T) :=
    Finset.sum_congr rfl fun n _ => hsame n
  rcases lt_or_ge a b with hab | hab
  · have h := sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace
      hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab (Finset.range k)
    rw [Finset.card_range] at h
    rw [hsum]
    exact h
  · -- with no gap the left side is nonpositive and the estimate is trivial
    have hnonneg : 0 ≤ ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T) :=
      Finset.sum_nonneg fun n _ => doubleAngleTangent_nonneg (hnn n) (hlt n)
    have hRHS : 0 ≤ kyFanApproximationGauge k H := by
      unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
      exact Finset.sum_nonneg fun n _ => approximationSingularValue_nonneg n H
    nlinarith

/-- Representative packaging of the infinite-dimensional Ky Fan root: any
operator between Hilbert spaces whose approximation numbers are the
double-angle tangents of the graph-coordinate approximation numbers obeys
the prefix bounds. -/
theorem kyFan_tanTwoTheta0_offDiagonal_le_of_finiteDimensional_invariantSubspace
    {E₂ F₂ : Type*}
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (tanTwoTheta0 : E₂ →L[𝕜] F₂)
    (htan : ∀ n, approximationSingularValue n tanTwoTheta0 =
      doubleAngleTangent (approximationSingularValue n T))
    (k : ℕ) :
    (b - a) * kyFanApproximationGauge k tanTwoTheta0 ≤
      2 * kyFanApproximationGauge k H := by
  have hgauge : kyFanApproximationGauge k tanTwoTheta0 =
      ∑ n ∈ Finset.range k,
        doubleAngleTangent (approximationSingularValue n T) := by
    unfold kyFanApproximationGauge ContinuousLinearMap.kyFanGauge
    exact Finset.sum_congr rfl fun n _ => htan n
  rw [hgauge]
  exact kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantSubspace hA hH hAU hHU
    hHUperp hTmem hTzero hUb hUa hinv hT1 k

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, every Fan-dominant
unitary-invariant ideal, arbitrary Hilbert space** (finite-dimensional
invariant configuration).  If the off-diagonal perturbation `H` belongs to
the ideal, then so does every `tan 2Θ₀` representative, and
`(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`. -/
theorem tanTwoTheta0_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hT1 : approximationSingularValue 0 T < 1)
    (tanTwoTheta0 : E →L[𝕜] E)
    (htan : ∀ n, approximationSingularValue n tanTwoTheta0 =
      doubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta0 ∧
      (b - a) * N.gauge tanTwoTheta0 ≤
        2 * N.gauge H := by
  have hδ : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k,
      (b - a) / 2 * kyFanApproximationGauge k tanTwoTheta0 ≤
        kyFanApproximationGauge k H := by
    intro k
    have h := kyFan_tanTwoTheta0_offDiagonal_le_of_finiteDimensional_invariantSubspace hA hH hAU hHU
      hHUperp hTmem hTzero hUb hUa hinv hT1 tanTwoTheta0 htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

/-- Representative packaging of the branch-free Ky Fan root: any operator
between Hilbert spaces whose approximation numbers are a **rearrangement**
of the branch-free double-angle tangents of the graph-coordinate
approximation numbers obeys every prefix bound.

The rearrangement `π` is what makes this the honest statement: the
approximation numbers of an operator are antitone, while `t ↦ 2t/|1 - t²|`
is not monotone across the quarter turn.  A unitarily invariant norm sees
only the multiset of singular values, so nothing is lost. -/
theorem kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace
    {E₂ F₂ : Type*}
    [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (hab : a < b)
    (tanTwoTheta : E₂ →L[𝕜] F₂) (π : ℕ ≃ ℕ)
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
  have h := sum_absDoubleAngleTangent_le_of_finiteDimensional_invariantSubspace
    hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab S
  rw [hScard] at h
  rw [hgauge]
  exact h

/-- **Davis--Kahan 1970, the unrestricted `tan 2Θ` theorem, every
Fan-dominant unitary-invariant ideal, arbitrary Hilbert space**
(finite-dimensional invariant configuration).

If the fully off-diagonal perturbation `H` belongs to the ideal, then so does
every branch-free `tan 2Θ` representative, and
`(b - a) · N(tan 2Θ) ≤ 2 · N(H)`.

**No branch is selected and none is assumed.**  In particular there is no
hypothesis `approximationSingularValue 0 T < 1`; the perturbed invariant
subspace may make angles arbitrarily close to `π/2` with the trial
subspace. -/
theorem absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace
    (N : KyFanDominantIdealFamily (𝕜 := 𝕜))
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[𝕜] E) (π : ℕ ≃ ℕ)
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
    have h := kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace
      hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab tanTwoTheta π htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

end Main

end DavisKahan.TanTwoTheta
end TauCeti
