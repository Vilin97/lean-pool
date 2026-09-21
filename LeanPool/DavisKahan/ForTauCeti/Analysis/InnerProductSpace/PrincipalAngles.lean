/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T06.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/Analysis/InnerProductSpace/` (new file
`PrincipalAngles.lean`).

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]).

The canonical principal-angle API: the cosines of the principal angles between
two subspaces (given by orthonormal families) are the singular values of the
flat overlap operator `overlapOp` (from `AlignedBasis.lean`).  This packages the
`cos Θ`/`sin Θ` vectors, their basic order/range properties, the symmetry in the
two families (which needs `singularValues_adjoint`, W0.1(d)), and the bridge
`‖sin Θ‖²_F = d − overlap` to the flat overlap sum.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.AlignedBasis
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Projection.Geometry
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.KyFan


/-! # Principal angles between subspaces

For orthonormal families `u : Fin d → E` and `v : Fin d → E` spanning two
`d`-dimensional subspaces `U = span u`, `V = span v`, the **cosines of the
principal angles** are the singular values of the flat overlap operator
`overlapOp hu hv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)`
(matrix `⟪uᵢ, vⱼ⟫`).  The singular values lie in `[0, 1]` (the operator is a
contraction), are sorted decreasingly, and are symmetric in `u, v` (`M⋆` is the
overlap operator of the swapped pair, and `σ(M⋆) = σ(M)`).

The complementary quantity `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)` measures
the total misalignment of the two subspaces; here it equals `d − overlap` where
`overlap = ∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` is the flat overlap sum used throughout the
Davis–Kahan development.

## Main definitions

* `TauCeti.cosPrincipalAngles`: the sorted cosines `σ(overlapOp hu hv)`.
* `TauCeti.sinThetaSq`: the squared Frobenius sine `∑ᵢ (1 − cos²θᵢ)`.

## Main results

* `TauCeti.cosPrincipalAngles_nonneg` / `_le_one` / `_antitone`: range and
  order.
* `TauCeti.overlapOp_adjoint`: `(overlapOp hu hv)⋆ = overlapOp hv hu`.
* `TauCeti.cosPrincipalAngles_comm`: symmetry `cos Θ(u, v) = cos Θ(v, u)`.
* `TauCeti.sinThetaSq_eq_sub_overlap`: `‖sin Θ‖²_F = d − overlap`.
* `TauCeti.sum_sq_norm_aligned_le_sinThetaSq`: the Yu–Wang–Samworth
  aligned-basis bound restated as `∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {d : ℕ}

/-- **The cosines of the principal angles** between the subspaces spanned by two
orthonormal families `u, v : Fin d → E`: the (sorted, `ℕ →₀ ℝ`-indexed) singular
values of the overlap operator `overlapOp hu hv`. -/
@[expose]
noncomputable def cosPrincipalAngles {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℕ →₀ ℝ :=
  (overlapOp hu hv).singularValues

/-- Principal-angle cosines are nonnegative, being singular values. -/
theorem cosPrincipalAngles_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : ℕ) : 0 ≤ cosPrincipalAngles hu hv i :=
  (overlapOp hu hv).singularValues_nonneg i

/-- The principal-angle cosines are at most `1`: the overlap operator is a
contraction. -/
theorem cosPrincipalAngles_le_one {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : Fin d) : cosPrincipalAngles hu hv (i : ℕ) ≤ 1 :=
  singularValues_le_one_of_contraction (overlapOp_contraction hu hv)
    finrank_euclideanSpace_fin i

/-- The principal angles are listed in increasing order, so their cosines decrease. -/
theorem cosPrincipalAngles_antitone {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : Antitone (cosPrincipalAngles hu hv) :=
  (overlapOp hu hv).singularValues_antitone

/-- **The overlap operator of the swapped pair is the adjoint.**
`(overlapOp hu hv)⋆ = overlapOp hv hu`, immediate from `(P⋆ ∘ Q)⋆ = Q⋆ ∘ P`. -/
theorem overlapOp_adjoint {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (overlapOp hu hv).adjoint = overlapOp hv hu := by
  rw [overlapOp, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint, overlapOp]

/-- **Symmetry of the principal angles.**  `cos Θ(u, v) = cos Θ(v, u)`: the two
overlap operators are adjoint (`overlapOp_adjoint`) and adjoints share singular
values (`singularValues_adjoint`, plan step W0.1(d)). -/
theorem cosPrincipalAngles_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : cosPrincipalAngles hu hv = cosPrincipalAngles hv hu := by
  rw [cosPrincipalAngles, cosPrincipalAngles, ← overlapOp_adjoint hu hv,
    LinearMap.singularValues_adjoint]

/-- **The squared Frobenius sine** `‖sin Θ‖²_F = ∑ᵢ sin²θᵢ = ∑ᵢ (1 − cos²θᵢ)`
between the subspaces spanned by two orthonormal families of the same size. -/
@[expose]
noncomputable def sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) : ℝ :=
  ∑ k : Fin d, (1 - cosPrincipalAngles hu hv (k : ℕ) ^ 2)

/-- **`‖sin Θ‖²_F = d − overlap`.**  The squared Frobenius sine equals `d` minus
the flat overlap sum `∑ⱼ ∑ᵢ ‖⟪uᵢ, vⱼ⟫‖²` (which is `∑ cos²θᵢ`). -/
theorem sinThetaSq_eq_sub_overlap {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = (d : ℝ) - ∑ k, ∑ i, ‖⟪u i, v k⟫_𝕜‖ ^ 2 := by
  unfold sinThetaSq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  congr 1
  unfold cosPrincipalAngles
  exact sum_sq_singularValues_overlapOp hu hv

/-- **`‖sin Θ‖²_F = d − ∑ cos²θₖ`.**  The cosine form of `sinThetaSq_eq_sub_overlap`: the same
identity with the overlap sum left as the principal cosines rather than expanded into inner
products.

This is the shape the Davis--Kahan and Yu--Wang--Samworth arguments use, where the cosines are
carried symbolically and only the *sum* matters; `sinThetaSq_eq_sub_overlap` is the shape wanted
when the overlap has to be estimated entrywise.  Both are one step from the definition, and having
each spelled out saves every consumer the `Finset.sum_sub_distrib` dance. -/
theorem sinThetaSq_eq_card_sub_sum_sq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = (d : ℝ) - ∑ k : Fin d, cosPrincipalAngles hu hv (k : ℕ) ^ 2 := by
  unfold sinThetaSq
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]

/-- The squared sine of the principal angles is nonnegative: each summand `1 - cos²θₖ` is, because
the cosines lie in `[0, 1]`. -/
theorem sinThetaSq_nonneg {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    0 ≤ sinThetaSq hu hv :=
  Finset.sum_nonneg fun k _ => by
    have h1 := cosPrincipalAngles_le_one hu hv k
    have h0 := cosPrincipalAngles_nonneg hu hv (k : ℕ)
    nlinarith

/-- Symmetry of the squared Frobenius sine, `‖sin Θ(u, v)‖²_F = ‖sin Θ(v, u)‖²_F`. -/
theorem sinThetaSq_comm {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    sinThetaSq hu hv = sinThetaSq hv hu := by
  unfold sinThetaSq
  rw [cosPrincipalAngles_comm hu hv]

/-- **Aligned-basis bound in principal-angle form.**  The Yu–Wang–Samworth
Procrustes-rotated basis `wⱼ = (familyIsometry hv)(O⁻¹ eⱼ)` obeys
`∑ⱼ ‖wⱼ − uⱼ‖² ≤ 2 ‖sin Θ‖²_F`. -/
theorem sum_sq_norm_aligned_le_sinThetaSq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) :
    ∑ j, ‖familyIsometry hv ((choosePolarUnitary (overlapOp hu hv)).symm
          (EuclideanSpace.single j 1)) - u j‖ ^ 2
      ≤ 2 * sinThetaSq hu hv := by
  rw [sinThetaSq_eq_sub_overlap]
  exact sum_sq_norm_aligned_le hu hv

/-! ### Eigenblock families and the encoding-coherence bridges

The `sinThetaSq` of two eigenblock families equals the cross-block overlap sum
used throughout `DavisKahan.lean`, and (for equal blocks) half the squared
Frobenius distance of the two spectral projections.  All the `sin Θ` encodings in
this development are therefore provably the same quantity. -/

section Block

variable {n : ℕ}

/-- The orthonormal family enumerating the `s`-selected vectors of an
orthonormal basis. -/
noncomputable def blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Fin d → E := fun i => b (s.orderIsoOfFin hd i)

omit [FiniteDimensional 𝕜 E] in
/-- Selecting a subset of an orthonormal basis leaves an orthonormal family. -/
theorem orthonormal_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Orthonormal 𝕜 (blockFamily b s hd) :=
  b.orthonormal.comp _ (Subtype.coe_injective.comp (s.orderIsoOfFin hd).injective)

omit [FiniteDimensional 𝕜 E] in
/-- The selected family enumerates exactly the basis vectors indexed by `s`; this is what lets a
block be described either by its index set or by its span. -/
theorem range_blockFamily (b : OrthonormalBasis (Fin n) 𝕜 E) (s : Finset (Fin n))
    (hd : s.card = d) : Set.range (blockFamily b s hd) = b '' ↑s := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, (s.orderIsoOfFin hd i).2, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨(s.orderIsoOfFin hd).symm ⟨j, hj⟩, ?_⟩
    simp [blockFamily]

private theorem sum_blockFamily {s : Finset (Fin n)} (hd : s.card = d) (g : Fin n → ℝ) :
    ∑ i : Fin d, g ((s.orderIsoOfFin hd i : Fin n)) = ∑ i ∈ s, g i := by
  rw [← Finset.sum_coe_sort s g]
  exact Fintype.sum_equiv (s.orderIsoOfFin hd).toEquiv _ _ fun i => rfl

/-- **`sinThetaSq` of two eigenblocks is the cross-block overlap sum** — the
bridge from the principal-angle encoding to the `DavisKahan.lean` encoding. -/
theorem sinThetaSq_blockFamily_eq_sum_cross (bT bS : OrthonormalBasis (Fin n) 𝕜 E)
    {s s' : Finset (Fin n)} (hsd : s.card = d) (hs'd : s'.card = d) :
    sinThetaSq (orthonormal_blockFamily bT s hsd) (orthonormal_blockFamily bS s' hs'd)
      = ∑ j ∈ s', ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
  rw [sinThetaSq_eq_sub_overlap]
  have hrow : ∀ j : Fin n, ∑ i : Fin d, ‖⟪blockFamily bT s hsd i, bS j⟫_𝕜‖ ^ 2
      = ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := fun j =>
    sum_blockFamily hsd fun i => ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  have houter : ∑ k : Fin d, ∑ i : Fin d,
        ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2
      = ∑ j ∈ s', ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 := by
    rw [show (fun k : Fin d => ∑ i : Fin d,
          ‖⟪blockFamily bT s hsd i, blockFamily bS s' hs'd k⟫_𝕜‖ ^ 2)
        = fun k : Fin d => ∑ i ∈ s,
          ‖⟪bT i, bS ((s'.orderIsoOfFin hs'd k : Fin n))⟫_𝕜‖ ^ 2 from
      funext fun k => hrow _]
    exact sum_blockFamily hs'd fun j => ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
  rw [houter]
  have hpars : ∀ j : Fin n, ∑ i ∈ s, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2
      + ∑ i ∈ sᶜ, ‖⟪bT i, bS j⟫_𝕜‖ ^ 2 = 1 := fun j => by
    rw [Finset.sum_add_sum_compl, bT.sum_sq_norm_inner_right (bS j),
      bS.orthonormal.norm_eq_one j, one_pow]
  have hcard : (d : ℝ) = ∑ _j ∈ s', (1 : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_one, hs'd]
  rw [hcard, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by linarith [hpars j]

/-- **`sinThetaSq` is half the squared Frobenius projector distance**: for two
eigenblocks selected by the same `s`,
`∑ₖ ‖(P̂ − P)(bT k)‖² = 2 sinThetaSq`. -/
theorem sum_norm_sub_starProjection_sq_eq_two_mul_sinThetaSq
    (bT bS : OrthonormalBasis (Fin n) 𝕜 E) {s : Finset (Fin n)} (hsd : s.card = d) :
    ∑ k, ‖((Submodule.span 𝕜 (bS '' ↑s)).starProjection
        - (Submodule.span 𝕜 (bT '' ↑s)).starProjection) (bT k)‖ ^ 2
      = 2 * sinThetaSq (orthonormal_blockFamily bT s hsd)
          (orthonormal_blockFamily bS s hsd) := by
  rw [sum_norm_sub_starProjection_span_sq_eq bT bS s,
    sinThetaSq_comm, sinThetaSq_blockFamily_eq_sum_cross bS bT hsd hsd]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← norm_inner_symm]

end Block

/-! ### The operator-norm identification `‖Q̂ ∘L P‖ = sin θ_max`

The operator norm of "project onto `U`, then onto `Wᗮ`" is exactly the sine of
the largest principal angle between `U` and `W`.  This certifies that the
operator-norm Davis–Kahan theorem (`SinThetaOpNorm.lean`) bounds a principal
angle. -/

/-- The cosines of the principal angles *are* the singular values of the
overlap operator, definitionally.  This is the bridge that lets angle statements
be proved by singular-value arguments. -/
@[simp] theorem cosPrincipalAngles_eq {u v : Fin d → E} (hu : Orthonormal 𝕜 u)
    (hv : Orthonormal 𝕜 v) (i : ℕ) :
    cosPrincipalAngles hu hv i = (overlapOp hu hv).singularValues i := (rfl)

omit [FiniteDimensional 𝕜 E] in
/-- The coordinate isometry maps into the span of the family. -/
theorem familyIsometry_mem_span {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (y : EuclideanSpace 𝕜 (Fin d)) :
    familyIsometry hu y ∈ Submodule.span 𝕜 (Set.range u) := by
  rw [familyIsometry_apply]
  exact Submodule.sum_smul_mem _ _ fun i _ => Submodule.subset_span (Set.mem_range_self i)

/-- **Coisometry padding: precomposing with the adjoint of a `familyIsometry`
preserves singular values.**  For an orthonormal family `u : Fin d → E` and an
endomorphism `X` of `EuclideanSpace 𝕜 (Fin d)`, the composite
`X ∘ₗ ι_u⋆ : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)` has the same singular values as
`X`, as finsupps — the `finrank 𝕜 E − d` extra slots on the left are the zero
padding.  `ι_u⋆ ∘ ι_u = 1` gives the gram identity
`gram (X ∘ₗ ι_u⋆) = ι_u ∘ₗ gram X ∘ₗ ι_u⋆`, whose eigendata is that of `gram X`
pushed through `ι_u` and extended by `0` on `(span (range u))ᗮ`; gram
eigenvalues are nonnegative and sorted, so the padded vector is still sorted
and the sorted-eigenvalue uniqueness (`LinearMap.IsSymmetric.eigenvalues_eq_of_eigenbasis`) closes.
This transports singular-value data between the coordinate model and the
ambient space (plan step OP3.0). -/
theorem singularValues_comp_adjoint_familyIsometry
    {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (X : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)) :
    (X ∘ₗ LinearMap.adjoint (familyIsometry hu).toLinearMap).singularValues
      = X.singularValues := by
  exact singularValues_comp_adjoint_linearIsometry (familyIsometry hu) X

/-- Coordinates of the overlap operator: `(overlapOp hu hv y) i = ⟪uᵢ, ι_v y⟫`. -/
theorem overlapOp_coord {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v)
    (y : EuclideanSpace 𝕜 (Fin d)) (i : Fin d) :
    overlapOp hu hv y i = ⟪u i, familyIsometry hv y⟫_𝕜 := by
  have h1 : overlapOp hu hv y i
      = ⟪EuclideanSpace.single i (1 : 𝕜), overlapOp hu hv y⟫_𝕜 := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [h1, overlapOp_apply, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
    familyIsometry_single]

private theorem norm_sq_euclidean (z : EuclideanSpace 𝕜 (Fin d)) :
    ‖z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- Parseval for the projection onto the span of an orthonormal family
(`Set.range` phrasing of `Orthonormal.norm_sq_starProjection_span_image`). -/
private theorem norm_sq_starProjection_span_range {w : Fin d → E} (hw : Orthonormal 𝕜 w)
    (x : E) :
    ‖(Submodule.span 𝕜 (Set.range w)).starProjection x‖ ^ 2 = ∑ i, ‖⟪w i, x⟫_𝕜‖ ^ 2 := by
  rw [← Set.image_univ, ← Finset.coe_univ]
  exact Orthonormal.norm_sq_starProjection_span_image hw Finset.univ x

/-- **The key Pythagoras computation**: for `x = ι_u y ∈ U = span u`,
`‖P_{Wᗮ} x‖² = ‖y‖² − ‖(overlapOp hw hu) y‖²`. -/
private theorem norm_sq_orthogonal_starProjection_familyIsometry
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w)
    (y : EuclideanSpace 𝕜 (Fin d)) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y)‖ ^ 2
      = ‖y‖ ^ 2 - ‖overlapOp hw hu y‖ ^ 2 := by
  have hpyth := Submodule.norm_sq_eq_add_norm_sq_starProjection (familyIsometry hu y)
    (Submodule.span 𝕜 (Set.range w))
  have hWproj : ‖(Submodule.span 𝕜 (Set.range w)).starProjection (familyIsometry hu y)‖ ^ 2
      = ‖overlapOp hw hu y‖ ^ 2 := by
    rw [norm_sq_starProjection_span_range hw, norm_sq_euclidean]
    exact Finset.sum_congr rfl fun i _ => by rw [overlapOp_coord]
  have hiso : ‖familyIsometry hu y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [(familyIsometry hu).norm_map]
  linarith

/-- **Operator-norm principal-angle identification.**  For orthonormal families
`u, w : Fin d → E` spanning `U` and `W`, the operator norm of
`P_{Wᗮ} ∘L P_U` equals the sine of the largest principal angle between `U` and
`W`:

`‖P_{Wᗮ} ∘L P_U‖ = √(1 − cos²θ_max)`,

`cos θ_max` being the smallest principal-angle cosine
`cosPrincipalAngles hw hu (d − 1)`.  This certifies that the operator-norm
Davis–Kahan theorem (`norm_starProjection_comp_starProjection_le`) bounds
`sin θ_max`. -/
theorem norm_orthogonal_starProjection_comp_starProjection
    {u w : Fin d → E} (hu : Orthonormal 𝕜 u) (hw : Orthonormal 𝕜 w) (hd : 0 < d) :
    ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection‖
      = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) := by
  have hσ0 : 0 ≤ cosPrincipalAngles hw hu (d - 1) := cosPrincipalAngles_nonneg hw hu _
  have hσ1 : cosPrincipalAngles hw hu (d - 1) ≤ 1 := by
    have := cosPrincipalAngles_le_one hw hu (⟨d - 1, by omega⟩ : Fin d)
    simpa using this
  have h1σ : 0 ≤ 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by nlinarith
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_) ?_
  · -- upper bound: pull the projected vector back to coordinates via the
    -- adjoint of the coordinate isometry.
    set y : EuclideanSpace 𝕜 (Fin d) :=
      (familyIsometry hu).toLinearMap.adjoint
        ((Submodule.span 𝕜 (Set.range u)).starProjection z) with hy
    have hcoord : ∀ i, y i
        = ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 := fun i => by
      have h1 : y i = ⟪EuclideanSpace.single i (1 : 𝕜), y⟫_𝕜 := by
        rw [EuclideanSpace.inner_single_left, map_one, one_mul]
      rw [h1, hy, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap,
        familyIsometry_single]
    have hxy : familyIsometry hu y
        = (Submodule.span 𝕜 (Set.range u)).starProjection z := by
      have hsum : familyIsometry hu y
          = ∑ i, ⟪u i, (Submodule.span 𝕜 (Set.range u)).starProjection z⟫_𝕜 • u i := by
        rw [familyIsometry_apply]
        exact Finset.sum_congr rfl fun i _ => by rw [hcoord]
      rw [hsum, ← Orthonormal.starProjection_span_image_apply hu Finset.univ]
      apply Submodule.starProjection_eq_self_iff.mpr
      rw [Finset.coe_univ, Set.image_univ]
      exact Submodule.starProjection_apply_mem _ z
    have hyz : ‖y‖ ≤ ‖z‖ := by
      have h1 : ‖y‖ = ‖(Submodule.span 𝕜 (Set.range u)).starProjection z‖ := by
        rw [← hxy, (familyIsometry hu).norm_map]
      rw [h1]
      exact Submodule.norm_starProjection_apply_le _ z
    have hmin : cosPrincipalAngles hw hu (d - 1) * ‖y‖ ≤ ‖overlapOp hw hu y‖ := by
      rw [cosPrincipalAngles_eq]
      exact singularValues_last_mul_norm_le (overlapOp hw hu) finrank_euclideanSpace_fin hd y
    have h2 : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
          ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ ^ 2
        ≤ (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2 := by
      rw [← hxy, norm_sq_orthogonal_starProjection_familyIsometry hu hw y]
      have p1 : cosPrincipalAngles hw hu (d - 1) ^ 2 * ‖y‖ ^ 2
          ≤ ‖overlapOp hw hu y‖ ^ 2 := by
        have h := mul_self_le_mul_self (mul_nonneg hσ0 (norm_nonneg y)) hmin
        nlinarith [h]
      have hyz2 : ‖y‖ ^ 2 ≤ ‖z‖ ^ 2 := by
        have h := mul_self_le_mul_self (norm_nonneg y) hyz
        nlinarith [h]
      linarith [mul_le_mul_of_nonneg_left hyz2 h1σ, p1]
    calc ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection) z‖
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection
            ((Submodule.span 𝕜 (Set.range u)).starProjection z)‖ := rfl
      _ ≤ Real.sqrt ((1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ ^ 2) := by
          rw [← Real.sqrt_sq (norm_nonneg _)]
          exact Real.sqrt_le_sqrt h2
      _ = Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2) * ‖z‖ := by
          rw [Real.sqrt_mul h1σ, Real.sqrt_sq (norm_nonneg z)]
  · -- lower bound: the minimizing singular vector attains the angle.
    obtain ⟨y₀, hy₀n, hy₀⟩ := exists_norm_apply_eq_singularValues_last (overlapOp hw hu)
      finrank_euclideanSpace_fin hd
    have hx₀U : familyIsometry hu y₀ ∈ Submodule.span 𝕜 (Set.range u) :=
      familyIsometry_mem_span hu y₀
    have hx₀n : ‖familyIsometry hu y₀‖ = 1 := by
      rw [(familyIsometry hu).norm_map]; exact hy₀n
    have hPx₀ : (Submodule.span 𝕜 (Set.range u)).starProjection (familyIsometry hu y₀)
        = familyIsometry hu y₀ := Submodule.starProjection_eq_self_iff.mpr hx₀U
    have hval : ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y₀)‖ ^ 2
        = 1 - cosPrincipalAngles hw hu (d - 1) ^ 2 := by
      rw [norm_sq_orthogonal_starProjection_familyIsometry hu hw y₀, hy₀n, hy₀,
        cosPrincipalAngles_eq, one_pow]
    calc Real.sqrt (1 - cosPrincipalAngles hw hu (d - 1) ^ 2)
        = ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection (familyIsometry hu y₀)‖ := by
          rw [← hval, Real.sqrt_sq (norm_nonneg _)]
      _ = ‖((Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection) (familyIsometry hu y₀)‖ := by
          rw [ContinuousLinearMap.comp_apply, hPx₀]
      _ ≤ ‖(Submodule.span 𝕜 (Set.range w))ᗮ.starProjection ∘L
            (Submodule.span 𝕜 (Set.range u)).starProjection‖ * ‖familyIsometry hu y₀‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = _ := by rw [hx₀n, mul_one]

/-! ### The cos Θ singular-value dictionary (plan step OP3.A)

The singular values of `P_V ∘ P_U` are exactly the principal-angle cosines.
This upgrades the operator-norm/largest-angle identification
`norm_orthogonal_starProjection_comp_starProjection` to *all* singular values,
hence to every unitarily invariant norm.  The proof factors
`P_V ∘ P_U = ι_v ∘ overlapOp ∘ ι_u⋆` through the coordinate isometries, strips
the left isometry via `singularValues_eq_of_gram_eq`, and strips the right
`ι_u⋆` via the coisometry padding lemma `singularValues_comp_adjoint_familyIsometry`. -/

/-- The `i`-th coordinate of `ι_u⋆ x` is `⟪uᵢ, x⟫`. -/
theorem familyIsometry_adjoint_coord {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (x : E) (i : Fin d) :
    (familyIsometry hu).toLinearMap.adjoint x i = ⟪u i, x⟫_𝕜 := by
  have h1 : (familyIsometry hu).toLinearMap.adjoint x i
      = ⟪(EuclideanSpace.single i (1 : 𝕜)), (familyIsometry hu).toLinearMap.adjoint x⟫_𝕜 := by
    rw [EuclideanSpace.inner_single_left, map_one, one_mul]
  rw [h1, LinearMap.adjoint_inner_right, LinearIsometry.coe_toLinearMap, familyIsometry_single]

/-- `P_{span u} = ι_u ∘ ι_u⋆`: the orthogonal projection onto `span u`
expressed through the coordinate isometry. -/
theorem starProjection_span_range_eq_comp {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (x : E) :
    (Submodule.span 𝕜 (Set.range u)).starProjection x
      = familyIsometry hu ((familyIsometry hu).toLinearMap.adjoint x) := by
  rw [familyIsometry_apply]
  have hsp := Orthonormal.starProjection_span_image_apply hu Finset.univ x
  rw [Finset.coe_univ, Set.image_univ] at hsp
  rw [hsp]
  exact Finset.sum_congr rfl fun i _ => by rw [familyIsometry_adjoint_coord]

/-- **The cos Θ dictionary.**  The singular values of `P_V ∘ P_U` are the
cosines of the principal angles between `span u` and `span v`:
`σ(P_V ∘ P_U) = cosPrincipalAngles hv hu`. -/
theorem singularValues_starProjection_comp_starProjection {u v : Fin d → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E)
        : E →ₗ[𝕜] E).singularValues
      = cosPrincipalAngles hv hu := by
  set M : E →ₗ[𝕜] E := (((Submodule.span 𝕜 (Set.range v)).starProjection ∘L
    (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) with hMdef
  set Y : E →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    overlapOp hv hu ∘ₗ (familyIsometry hu).toLinearMap.adjoint with hYdef
  -- `ι_v⋆ ∘ ι_v = 1`.
  have hiso : (familyIsometry hv).toLinearMap.adjoint ∘ₗ (familyIsometry hv).toLinearMap
      = LinearMap.id := by
    refine LinearMap.ext fun y => ?_
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    exact ext_inner_right 𝕜 fun z => by
      rw [LinearMap.adjoint_inner_left]; exact (familyIsometry hv).inner_map_map y z
  -- `M = ι_v ∘ Y`.
  have hM : M = (familyIsometry hv).toLinearMap ∘ₗ Y := by
    refine LinearMap.ext fun x => ?_
    simp only [hMdef, hYdef, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_coe,
      Function.comp_apply, LinearMap.comp_apply, LinearIsometry.coe_toLinearMap]
    rw [starProjection_span_range_eq_comp hv, starProjection_span_range_eq_comp hu,
      overlapOp_apply]
  -- Strip the left isometry: `gram M = gram Y`.
  have hgram : M.adjoint ∘ₗ M = Y.adjoint ∘ₗ Y := by
    rw [hM, LinearMap.adjoint_comp]
    rw [show (LinearMap.adjoint Y ∘ₗ LinearMap.adjoint (familyIsometry hv).toLinearMap)
          ∘ₗ ((familyIsometry hv).toLinearMap ∘ₗ Y)
        = LinearMap.adjoint Y ∘ₗ ((familyIsometry hv).toLinearMap.adjoint
          ∘ₗ (familyIsometry hv).toLinearMap) ∘ₗ Y from by
      simp only [LinearMap.comp_assoc], hiso, LinearMap.id_comp]
  -- Strip the right isometry (OP3.0) and read off the definition.
  rw [singularValues_eq_of_gram_eq hgram, hYdef,
    singularValues_comp_adjoint_familyIsometry hu (overlapOp hv hu)]
  rfl

/-! ### Symmetry of the directed sine spectrum in equal dimensions

The cosine symmetry above is immediate from adjoints.  The corresponding sine
symmetry is subtler: the two coordinate sine maps have Gram operators
`I - M⋆M` and `I - MM⋆`, where `M` is the overlap operator.  The polar unitary
of `M` conjugates those complementary Gram operators, so the coordinate maps
have identical singular values.  Coisometry padding then transports the result
to the ambient cross projections.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PrincipalAngles`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `34319dc`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

/-- **The Gram operator of the coordinate sine map is `1 - M⋆M`,** where `M = overlapOp hv hu`.

Stated once for the same reason `comp_starProjection_span_range_factor` is: the theorem below
needs it at `(u, v)` and again at `(v, u)`, and the two instances were written out in full --
forty lines each, identical under the swap. -/
private theorem adjoint_comp_starProjection_orthogonal_comp_familyIsometry
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    LinearMap.adjoint
        ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (familyIsometry hu).toLinearMap)
        ∘ₗ ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
          ∘ₗ (familyIsometry hu).toLinearMap) =
      LinearMap.id - LinearMap.adjoint (overlapOp hv hu) ∘ₗ overlapOp hv hu := by
  apply LinearMap.ext
  intro x
  refine ext_inner_right 𝕜 fun y => ?_
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
  rw [LinearMap.adjoint_inner_left, inner_sub_left, LinearMap.adjoint_inner_left]
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change
    ⟪(Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (familyIsometry hu x),
        (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (familyIsometry hu y)⟫_𝕜 =
      ⟪x, y⟫_𝕜 - ⟪overlapOp hv hu x, overlapOp hv hu y⟫_𝕜
  rw [← (Submodule.span 𝕜 (Set.range v))ᗮ.inner_starProjection_left_eq_right,
    (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection_eq_self_iff.mpr
      ((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection_apply_mem _)]
  have hperp :
      (Submodule.span 𝕜 (Set.range v))ᗮ.starProjection (familyIsometry hu x) =
        familyIsometry hu x -
          (Submodule.span 𝕜 (Set.range v)).starProjection (familyIsometry hu x) := by
    have h := congrArg
      (fun T : E →L[𝕜] E => T (familyIsometry hu x))
      (Submodule.starProjection_orthogonal' (Submodule.span 𝕜 (Set.range v)))
    simpa only [sub_apply, one_apply_eq_self] using h
  rw [hperp, inner_sub_left, (familyIsometry hu).inner_map_map,
    starProjection_span_range_eq_comp hv]
  congr 1
  calc
    ⟪familyIsometry hv
        ((familyIsometry hv).toLinearMap.adjoint (familyIsometry hu x)),
        familyIsometry hu y⟫_𝕜 =
        ⟪(familyIsometry hv).toLinearMap.adjoint (familyIsometry hu x),
          (familyIsometry hv).toLinearMap.adjoint (familyIsometry hu y)⟫_𝕜 :=
      (LinearMap.adjoint_inner_right (familyIsometry hv).toLinearMap
        ((familyIsometry hv).toLinearMap.adjoint (familyIsometry hu x))
        (familyIsometry hu y)).symm
    _ = ⟪overlapOp hv hu x, overlapOp hv hu y⟫_𝕜 := by
      rfl

/-- The coordinate sine maps associated with two equal-length orthonormal
families have the same singular values in the two directions. -/
theorem singularValues_orthogonal_familyIsometry_comm
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ((((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ (familyIsometry hu).toLinearMap).singularValues =
      ((((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
        ∘ₗ (familyIsometry hv).toLinearMap).singularValues := by
  let Iu := (familyIsometry hu).toLinearMap
  let Iv := (familyIsometry hv).toLinearMap
  let PuPerp : E →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
  let PvPerp : E →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
  let Suv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E := PvPerp ∘ₗ Iu
  let Svu : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E := PuPerp ∘ₗ Iv
  let M : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) := overlapOp hv hu
  have hgramUV : LinearMap.adjoint Suv ∘ₗ Suv =
      LinearMap.id - LinearMap.adjoint M ∘ₗ M :=
    adjoint_comp_starProjection_orthogonal_comp_familyIsometry hu hv
  have hgramVU : LinearMap.adjoint Svu ∘ₗ Svu =
      LinearMap.id - LinearMap.adjoint (overlapOp hu hv) ∘ₗ overlapOp hu hv :=
    adjoint_comp_starProjection_orthogonal_comp_familyIsometry hv hu
  have hMadj : LinearMap.adjoint M = overlapOp hu hv := by
    simpa only [M] using overlapOp_adjoint hv hu
  have hgramVU' : LinearMap.adjoint Svu ∘ₗ Svu =
      LinearMap.id - M ∘ₗ LinearMap.adjoint M := by
    rw [hgramVU, ← hMadj, LinearMap.adjoint_adjoint]
  let O := choosePolarUnitary M
  have hconj : M ∘ₗ LinearMap.adjoint M =
      O.toLinearMap ∘ₗ (LinearMap.adjoint M ∘ₗ M) ∘ₗ O.symm.toLinearMap := by
    simpa only [O] using comp_adjoint_eq_conj_adjoint_comp M
  have hrotGram : LinearMap.adjoint Suv ∘ₗ Suv =
      LinearMap.adjoint (Svu ∘ₗ O.toLinearMap) ∘ₗ (Svu ∘ₗ O.toLinearMap) := by
    rw [hgramUV, LinearMap.adjoint_comp, O.adjoint_toLinearMap_eq_symm]
    rw [show (O.symm.toLinearMap ∘ₗ LinearMap.adjoint Svu) ∘ₗ
          (Svu ∘ₗ O.toLinearMap) =
        O.symm.toLinearMap ∘ₗ (LinearMap.adjoint Svu ∘ₗ Svu) ∘ₗ
          O.toLinearMap from by simp only [LinearMap.comp_assoc]]
    rw [hgramVU', hconj]
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub,
      LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
      LinearIsometryEquiv.symm_apply_apply]
  calc
    Suv.singularValues = (Svu ∘ₗ O.toLinearMap).singularValues :=
      singularValues_eq_of_gram_eq hrotGram
    _ = Svu.singularValues := singularValues_comp_unitary Svu O

/-- **Factor a projection composite through the coordinate isometry.**  `starProjection`
onto `span (range u)` is `ι_u ∘ ι_u⋆`, so any operator postcomposed with it factors as
"restrict to coordinates, act, and pad back" -- the shape
`singularValues_comp_adjoint_linearIsometry` consumes.

Stated once because the two halves of the symmetry below used it with `u` and `v` and were
otherwise identical; each was twelve lines of `change` and one rewrite. -/
private theorem comp_starProjection_span_range_factor {u : Fin d → E} (hu : Orthonormal 𝕜 u)
    (T : E →L[𝕜] E) :
    ((T ∘L (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      = (((T : E →L[𝕜] E) : E →ₗ[𝕜] E) ∘ₗ (familyIsometry hu).toLinearMap)
          ∘ₗ LinearMap.adjoint (familyIsometry hu).toLinearMap := by
  ext x
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change T ((Submodule.span 𝕜 (Set.range u)).starProjection x)
    = T (familyIsometry hu (LinearMap.adjoint (familyIsometry hu).toLinearMap x))
  rw [starProjection_span_range_eq_comp hu]

/-- The two ambient directed sine cross projections associated with equal-length
orthonormal families have identical singular-value sequences. -/
theorem singularValues_orthogonal_starProjection_comp_starProjection_comm
    {u v : Fin d → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) :
          E →ₗ[𝕜] E).singularValues =
      (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
        (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) :
          E →ₗ[𝕜] E).singularValues := by
  let Suv : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ∘ₗ (familyIsometry hu).toLinearMap
  let Svu : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] E :=
    (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E)
      ∘ₗ (familyIsometry hv).toLinearMap
  have hfactorUV :
      (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        Suv ∘ₗ LinearMap.adjoint (familyIsometry hu).toLinearMap :=
    comp_starProjection_span_range_factor hu _
  have hfactorVU :
      (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E) =
        Svu ∘ₗ LinearMap.adjoint (familyIsometry hv).toLinearMap :=
    comp_starProjection_span_range_factor hv _
  calc
    (((Submodule.span 𝕜 (Set.range v))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range u)).starProjection : E →L[𝕜] E) : E →ₗ[𝕜] E).singularValues =
        Suv.singularValues := by
      rw [hfactorUV,
        singularValues_comp_adjoint_linearIsometry (familyIsometry hu) Suv]
    _ = Svu.singularValues := by
      simpa only [Suv, Svu] using singularValues_orthogonal_familyIsometry_comm hu hv
    _ = (((Submodule.span 𝕜 (Set.range u))ᗮ.starProjection ∘L
          (Submodule.span 𝕜 (Set.range v)).starProjection : E →L[𝕜] E) :
            E →ₗ[𝕜] E).singularValues := by
      rw [hfactorVU,
        singularValues_comp_adjoint_linearIsometry (familyIsometry hv) Svu]

end TauCeti
