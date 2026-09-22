/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System


/-!
# Moore--Penrose inverse in finite-dimensional inner-product spaces

The pseudoinverse of a rectangular map is reconstructed from its intrinsic
right singular basis.  On a right singular vector `vᵢ`, the Gram operator
`A†A` acts by `σᵢ²`; the pseudoinverse therefore uses the coefficient
`(σᵢ²)⁻¹` in front of the rank-one map `y ↦ ⟪A vᵢ, y⟫ vᵢ`.

Zero singular values contribute zero through total field inversion.

## The Penrose identities

The construction above is *a* generalized inverse for obvious reasons; that it
is *the* Moore--Penrose inverse is the content of the four Penrose identities,
and all four are proved here:

1. `comp_moorePenroseInverse_comp` — `A A⁺ A = A`;
2. `moorePenroseInverse_comp_comp` — `A⁺ A A⁺ = A⁺`;
3. `isSymmetric_comp_moorePenroseInverse` — `A A⁺` is self-adjoint;
4. `isSymmetric_moorePenroseInverse_comp` — `A⁺ A` is self-adjoint.

Identities (2) and (4) are read off a single fact,
`moorePenroseInverse_comp_apply_rightSingularBasis`: the initial projection
`A⁺A` is diagonal in the right singular basis with entries `0` and `1`, so it is
the orthogonal projection onto the directions of nonzero singular value.
Identity (3) needs no orthogonality at all — `A A⁺` is visibly a
real-coefficient combination of rank-one projections onto the images of those
directions.

`eq_moorePenroseInverse_of_isMoorePenroseInverse` completes the characterization:
anything satisfying `IsMoorePenroseInverse A` equals `A⁺`.  So the name is earned — this is
*the* Moore--Penrose inverse, not merely a generalized inverse that happens to
be constructed from the singular system.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.MoorePenroseInverse`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `caa0966`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 Thinking; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- **Penrose's four conditions**, as a `Prop`-valued structure with named accessors rather
than four anonymous hypotheses.

The four conditions *are* Penrose's definition of a pseudoinverse, so packaging them is what
lets the uniqueness theorem below read as *the Moore--Penrose inverse is unique*, and gives
the relation somewhere to carry its own theory. -/
structure IsMoorePenroseInverse (A : E →ₗ[𝕜] F) (B : F →ₗ[𝕜] E) : Prop where
  /-- `B` is a generalized inverse of `A`. -/
  comp_comp_self : A ∘ₗ B ∘ₗ A = A
  /-- `A` is a generalized inverse of `B`. -/
  comp_comp_self' : B ∘ₗ A ∘ₗ B = B
  /-- The idempotent `A B` onto the range of `A` is self-adjoint. -/
  isSymmetric_comp : (A ∘ₗ B).IsSymmetric
  /-- The idempotent `B A` onto the range of `B` is self-adjoint. -/
  isSymmetric_comp' : (B ∘ₗ A).IsSymmetric

/-- The finite-dimensional Moore--Penrose inverse, reconstructed from the
right singular basis and the Gram eigenvalues. -/
noncomputable def moorePenroseInverse (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] E :=
  ∑ i : Fin (finrank 𝕜 E),
    (((((A.singularValues i) ^ 2 : ℝ) : 𝕜))⁻¹) •
      (InnerProductSpace.rankOne 𝕜
        (TauCeti.rightSingularBasis A i)
        (A (TauCeti.rightSingularBasis A i))).toLinearMap

/-- Gram orthogonality of the images of the right singular basis. -/
theorem inner_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i j : Fin (finrank 𝕜 E)) :
    inner 𝕜 (A (TauCeti.rightSingularBasis A i))
        (A (TauCeti.rightSingularBasis A j)) =
      (((A.singularValues j) ^ 2 : ℝ) : 𝕜) *
        inner 𝕜 (TauCeti.rightSingularBasis A i)
          (TauCeti.rightSingularBasis A j) := by
  rw [← LinearMap.adjoint_inner_right,
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    show A.adjoint (A (TauCeti.rightSingularBasis A j)) =
      (A.adjoint.comp A) (TauCeti.rightSingularBasis A j) from rfl,
    TauCeti.adjointCompSelf_apply_rightSingularBasis,
    inner_smul_right]

/-- The pseudoinverse followed by the original map fixes each right singular
vector with nonzero singular value. -/
theorem moorePenroseInverse_apply_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) {k : Fin (finrank 𝕜 E)}
    (hk : A.singularValues k ≠ 0) :
    moorePenroseInverse A (A (TauCeti.rightSingularBasis A k)) =
      TauCeti.rightSingularBasis A k := by
  classical
  unfold moorePenroseInverse
  rw [LinearMap.sum_apply]
  refine (Finset.sum_eq_single k ?_ ?_).trans ?_
  · intro i _ hik
    rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (TauCeti.rightSingularBasis A i)
        (TauCeti.rightSingularBasis A k) = 0 := by
      simp [orthonormal_iff_ite.mp
        (TauCeti.rightSingularBasis A).orthonormal i k, ite_eq_right hik]
    rw [hinner, mul_zero, zero_smul, smul_zero]
  · intro hkmem
    exact absurd (Finset.mem_univ k) hkmem
  · rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
      InnerProductSpace.rankOne_apply,
      inner_apply_rightSingularBasis]
    have hinner : inner 𝕜 (TauCeti.rightSingularBasis A k)
        (TauCeti.rightSingularBasis A k) = 1 := by
      simp
    rw [hinner, mul_one, smul_smul]
    have hσ : ((((A.singularValues k) ^ 2 : ℝ) : 𝕜)) ≠ 0 := by
      exact RCLike.ofReal_ne_zero.mpr (pow_ne_zero 2 hk)
    rw [inv_mul_cancel₀ hσ, one_smul]

/-- The first Penrose identity `A A⁺ A = A`. -/
theorem comp_moorePenroseInverse_comp (A : E →ₗ[𝕜] F) :
    A ∘ₗ moorePenroseInverse A ∘ₗ A = A := by
  apply (TauCeti.rightSingularBasis A).toBasis.ext
  intro i
  by_cases hi : A.singularValues i = 0
  · -- on a zero singular direction both sides vanish; the composite has to be
    -- unfolded before the vanishing rewrite reaches the inner occurrence
    rw [OrthonormalBasis.coe_toBasis]
    simp [TauCeti.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi]
  · rw [OrthonormalBasis.coe_toBasis]
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A (moorePenroseInverse A (A (TauCeti.rightSingularBasis A i))) =
      A (TauCeti.rightSingularBasis A i)
    rw [moorePenroseInverse_apply_apply_rightSingularBasis A hi]

/-- The initial projection `A⁺A` is diagonal in the right singular basis, with
entry `1` on the directions of nonzero singular value and `0` on the rest.  Every
Penrose identity below is read off this one fact. -/
theorem moorePenroseInverse_comp_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    (moorePenroseInverse A ∘ₗ A) (TauCeti.rightSingularBasis A i) =
      if A.singularValues i = 0 then 0 else TauCeti.rightSingularBasis A i := by
  by_cases hi : A.singularValues i = 0
  · rw [ite_eq_left hi, LinearMap.comp_apply,
      TauCeti.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi,
      map_zero]
  · rw [ite_eq_right hi, LinearMap.comp_apply,
      moorePenroseInverse_apply_apply_rightSingularBasis A hi]

/-- **The fourth Penrose identity: `A⁺A` is self-adjoint.**

`A⁺A` is diagonal in the right singular basis with entries `0` and `1`
(`moorePenroseInverse_comp_apply_rightSingularBasis`), so it is the orthogonal
projection onto the span of the directions with nonzero singular value. -/
theorem isSymmetric_moorePenroseInverse_comp (A : E →ₗ[𝕜] F) :
    (moorePenroseInverse A ∘ₗ A).IsSymmetric := by
  classical
  set v := TauCeti.rightSingularBasis A with hv
  set P := moorePenroseInverse A ∘ₗ A with hP
  -- On the basis, `⟪P (v j), v i⟫ = ⟪v j, P (v i)⟫`: both sides are `1` when
  -- `i = j` and `σᵢ ≠ 0`, and `0` otherwise.
  have horth : ∀ j i, ⟪v j, v i⟫_𝕜 = if j = i then 1 else 0 :=
    fun j i => orthonormal_iff_ite.mp v.orthonormal j i
  have hbasis : ∀ i j, ⟪P (v j), v i⟫_𝕜 = ⟪v j, P (v i)⟫_𝕜 := by
    intro i j
    rw [hP, moorePenroseInverse_comp_apply_rightSingularBasis,
      moorePenroseInverse_comp_apply_rightSingularBasis]
    by_cases hi : A.singularValues i = 0
    · by_cases hj : A.singularValues j = 0
      · rw [ite_eq_left hi, ite_eq_left hj, inner_zero_left, inner_zero_right]
      · have hne : j ≠ i := fun h => hj (h ▸ hi)
        rw [ite_eq_left hi, ite_eq_right hj, inner_zero_right, horth, ite_eq_right hne]
    · by_cases hj : A.singularValues j = 0
      · have hne : j ≠ i := fun h => hi (h ▸ hj)
        rw [ite_eq_right hi, ite_eq_left hj, inner_zero_left, horth, ite_eq_right hne]
      · rw [ite_eq_right hi, ite_eq_right hj]
  intro x y
  rw [← v.sum_repr x, ← v.sum_repr y]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hbasis]

/-- The pseudoinverse, evaluated.  Directions of zero singular value drop out
because the field inverse of `0` is `0`. -/
@[simp]
theorem moorePenroseInverse_apply (A : E →ₗ[𝕜] F) (y : F) :
    moorePenroseInverse A y =
      ∑ i : Fin (finrank 𝕜 E), (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹ •
        (⟪A (TauCeti.rightSingularBasis A i), y⟫_𝕜 •
          TauCeti.rightSingularBasis A i) := by
  simp [moorePenroseInverse, LinearMap.sum_apply,
    InnerProductSpace.rankOne_apply]

/-- **The second Penrose identity: `A⁺ A A⁺ = A⁺`.**

`A⁺` lands in the span of the right singular directions with nonzero singular
value, and `A⁺A` is the identity there. -/
theorem moorePenroseInverse_comp_comp (A : E →ₗ[𝕜] F) :
    moorePenroseInverse A ∘ₗ A ∘ₗ moorePenroseInverse A =
      moorePenroseInverse A := by
  classical
  ext y
  -- states the goal with the definition unfolded, in the shape the next step needs;
  -- there is no `_apply` lemma to rewrite with here.
  change (moorePenroseInverse A ∘ₗ A) (moorePenroseInverse A y) =
    moorePenroseInverse A y
  rw [moorePenroseInverse_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_smul, moorePenroseInverse_comp_apply_rightSingularBasis]
  by_cases hi : A.singularValues i = 0
  · rw [ite_eq_left hi]
    simp [hi]
  · rw [ite_eq_right hi]

/-- **The third Penrose identity: `A A⁺` is self-adjoint.**

Unlike its companion this needs no orthogonality: `A A⁺` is visibly
`∑ᵢ (σᵢ²)⁻¹ • rankOne (A vᵢ) (A vᵢ)`, a real-coefficient combination of
rank-one projections onto the images of the right singular vectors. -/
theorem isSymmetric_comp_moorePenroseInverse (A : E →ₗ[𝕜] F) :
    (A ∘ₗ moorePenroseInverse A).IsSymmetric := by
  have happ : ∀ w : F, (A ∘ₗ moorePenroseInverse A) w =
      ∑ i : Fin (finrank 𝕜 E), (((A.singularValues i ^ 2 : ℝ) : 𝕜))⁻¹ •
        (⟪A (TauCeti.rightSingularBasis A i), w⟫_𝕜 •
          A (TauCeti.rightSingularBasis A i)) := by
    intro w
    rw [LinearMap.comp_apply, moorePenroseInverse_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul]
  intro y z
  rw [happ y, happ z]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    map_inv₀, RCLike.conj_ofReal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_conj_symm]
  ring

/-- **Uniqueness: the four Penrose identities determine the inverse.**

Any `B` satisfying all four *is* `A⁺`, so together with the identities above the
name is earned rather than asserted: `moorePenroseInverse` is the Moore--Penrose
inverse, not merely some generalized inverse.

The proof is the classical one.  Both `B` and `A⁺` are shown equal to the same
composite `B ∘ₗ A ∘ₗ A⁺`, each by pushing an adjoint through the factorization
of `A` supplied by the *other* map's first identity. -/
theorem eq_moorePenroseInverse_of_isMoorePenroseInverse {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E}
    (h : IsMoorePenroseInverse A B) : B = moorePenroseInverse A := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  set G := moorePenroseInverse A with hGdef
  have hG1 : A ∘ₗ G ∘ₗ A = A := comp_moorePenroseInverse_comp A
  have hG2 : G ∘ₗ A ∘ₗ G = G := moorePenroseInverse_comp_comp A
  have hG3 : (A ∘ₗ G).IsSymmetric := isSymmetric_comp_moorePenroseInverse A
  have hG4 : (G ∘ₗ A).IsSymmetric := isSymmetric_moorePenroseInverse_comp A
  -- `A⋆ = A⋆ (A A⁺)`, from `A = (A A⁺) A` and self-adjointness of `A A⁺`.
  have hAr : LinearMap.adjoint A = LinearMap.adjoint A ∘ₗ (A ∘ₗ G) := by
    conv_lhs => rw [← hG1, ← LinearMap.comp_assoc]
    rw [LinearMap.adjoint_comp, hG3.adjoint_eq]
  -- `A⋆ = (B A) A⋆`, from `A = A (B A)` and self-adjointness of `B A`.
  have hAl : LinearMap.adjoint A = (B ∘ₗ A) ∘ₗ LinearMap.adjoint A := by
    conv_lhs => rw [← h1]
    rw [LinearMap.adjoint_comp, h4.adjoint_eq]
  have hB : B = B ∘ₗ A ∘ₗ G := by
    calc B = B ∘ₗ A ∘ₗ B := h2.symm
      _ = B ∘ₗ LinearMap.adjoint (A ∘ₗ B) := by rw [h3.adjoint_eq]
      _ = B ∘ₗ LinearMap.adjoint B ∘ₗ LinearMap.adjoint A := by
          rw [LinearMap.adjoint_comp]
      _ = B ∘ₗ LinearMap.adjoint B ∘ₗ LinearMap.adjoint A ∘ₗ (A ∘ₗ G) := by
          conv_lhs => rw [hAr]
      _ = (B ∘ₗ LinearMap.adjoint (A ∘ₗ B)) ∘ₗ (A ∘ₗ G) := by
          rw [LinearMap.adjoint_comp]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A ∘ₗ B) ∘ₗ (A ∘ₗ G) := by rw [h3.adjoint_eq]
      _ = B ∘ₗ A ∘ₗ G := by rw [h2]
  have hG : G = B ∘ₗ A ∘ₗ G := by
    calc G = G ∘ₗ A ∘ₗ G := hG2.symm
      _ = (G ∘ₗ A) ∘ₗ G := by rw [LinearMap.comp_assoc]
      _ = LinearMap.adjoint (G ∘ₗ A) ∘ₗ G := by rw [hG4.adjoint_eq]
      _ = (LinearMap.adjoint A ∘ₗ LinearMap.adjoint G) ∘ₗ G := by
          rw [LinearMap.adjoint_comp]
      _ = ((B ∘ₗ A) ∘ₗ LinearMap.adjoint A ∘ₗ LinearMap.adjoint G) ∘ₗ G := by
          conv_lhs => rw [hAl]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A) ∘ₗ (LinearMap.adjoint (G ∘ₗ A) ∘ₗ G) := by
          rw [LinearMap.adjoint_comp]
          simp only [LinearMap.comp_assoc]
      _ = (B ∘ₗ A) ∘ₗ ((G ∘ₗ A) ∘ₗ G) := by rw [hG4.adjoint_eq]
      _ = B ∘ₗ A ∘ₗ G := by simp only [LinearMap.comp_assoc, hG2]
  rw [hB, ← hG]

/-- The construction satisfies the four conditions, so a Moore--Penrose inverse exists. -/
theorem isMoorePenroseInverse_moorePenroseInverse (A : E →ₗ[𝕜] F) :
    IsMoorePenroseInverse A (moorePenroseInverse A) where
  comp_comp_self := comp_moorePenroseInverse_comp A
  comp_comp_self' := moorePenroseInverse_comp_comp A
  isSymmetric_comp := isSymmetric_comp_moorePenroseInverse A
  isSymmetric_comp' := isSymmetric_moorePenroseInverse_comp A

private theorem isMoorePenroseInverse_adjoint_of {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E}
    (h : IsMoorePenroseInverse A B) :
    IsMoorePenroseInverse (LinearMap.adjoint A) (LinearMap.adjoint B) where
  comp_comp_self := by
    have := congrArg LinearMap.adjoint h.comp_comp_self
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc] using this
  comp_comp_self' := by
    have := congrArg LinearMap.adjoint h.comp_comp_self'
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc] using this
  isSymmetric_comp := by
    have : LinearMap.adjoint A ∘ₗ LinearMap.adjoint B = B ∘ₗ A := by
      rw [← LinearMap.adjoint_comp, h.isSymmetric_comp'.adjoint_eq]
    rw [this]; exact h.isSymmetric_comp'
  isSymmetric_comp' := by
    have : LinearMap.adjoint B ∘ₗ LinearMap.adjoint A = A ∘ₗ B := by
      rw [← LinearMap.adjoint_comp, h.isSymmetric_comp.adjoint_eq]
    rw [this]; exact h.isSymmetric_comp

/-- The relation is compatible with adjoints. -/
theorem isMoorePenroseInverse_adjoint {A : E →ₗ[𝕜] F} {B : F →ₗ[𝕜] E} :
    IsMoorePenroseInverse A B ↔
      IsMoorePenroseInverse (LinearMap.adjoint A) (LinearMap.adjoint B) := by
  refine ⟨isMoorePenroseInverse_adjoint_of, fun h => ?_⟩
  simpa [LinearMap.adjoint_adjoint] using isMoorePenroseInverse_adjoint_of h

/-- If `A` is injective, the pseudoinverse is a left inverse. -/
theorem moorePenroseInverse_comp_eq_id_of_injective
    (A : E →ₗ[𝕜] F) (hA : Function.Injective A) :
    moorePenroseInverse A ∘ₗ A = LinearMap.id := by
  apply (TauCeti.rightSingularBasis A).toBasis.ext
  intro i
  -- injectivity rules out a zero singular direction: a right singular vector is
  -- a unit vector, so `A v = 0 = A 0` would force `v = 0`
  have hi : A.singularValues i ≠ 0 := by
    intro hi
    have hz := TauCeti.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi
    have he : TauCeti.rightSingularBasis A i = 0 := hA (by rw [hz, map_zero])
    have hne : TauCeti.rightSingularBasis A i ≠ 0 := by
      simpa using (TauCeti.rightSingularBasis A).toBasis.ne_zero i
    exact hne he
  rw [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    moorePenroseInverse_apply_apply_rightSingularBasis A hi,
    LinearMap.id_apply]


/-! ### Self-adjoint maps: the pseudoinverse inherits every commutation

For a self-adjoint `A` the two Penrose projections `A A⁺` and `A⁺ A` coincide, and
that single fact turns the four identities into the statement that *anything*
commuting with `A` commutes with `A⁺`.  This is what lets a pseudoinverse appear
inside an operator built from commuting pieces without breaking the commutation. -/

/-- **The pseudoinverse of a self-adjoint map is self-adjoint.**

`A⁺⋆` satisfies the four Penrose conditions for `A⋆ = A`, so uniqueness identifies
it with `A⁺`. -/
theorem adjoint_moorePenroseInverse_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    LinearMap.adjoint (moorePenroseInverse A) = moorePenroseInverse A := by
  refine eq_moorePenroseInverse_of_isMoorePenroseInverse ?_
  have h := isMoorePenroseInverse_adjoint.mp (isMoorePenroseInverse_moorePenroseInverse A)
  rwa [hA.adjoint_eq] at h

/-- **For a self-adjoint map the two Penrose projections agree**: `A A⁺ = A⁺ A`.

Both are the orthogonal projection onto `range A`; algebraically, `A⁺A` is
self-adjoint (fourth Penrose identity) and its adjoint is `A⋆ A⁺⋆ = A A⁺`. -/
theorem comp_moorePenroseInverse_comm_of_isSymmetric {A : E →ₗ[𝕜] E} (hA : A.IsSymmetric) :
    A ∘ₗ moorePenroseInverse A = moorePenroseInverse A ∘ₗ A := by
  have h := (isSymmetric_moorePenroseInverse_comp A).adjoint_eq
  rwa [LinearMap.adjoint_comp, hA.adjoint_eq,
    adjoint_moorePenroseInverse_of_isSymmetric hA] at h

/-- **Commutation passes to the Moore--Penrose inverse of a self-adjoint map**:
if `A` is self-adjoint and `B A = A B`, then `B A⁺ = A⁺ B`.

Only `B A = A B` is assumed: because `A⋆ = A`, taking adjoints gives `B⋆ A = A B⋆`
for free, and the two together force `B` to commute with the Penrose projection
`P = A A⁺ = A⁺ A`.  Indeed `P B P = B P` and `P B⋆ P = B⋆ P` hold by the first
Penrose identity alone, and adjoining the second turns it into `P B P = P B`.
With `B P = P B` in hand,
`A⁺ B = A⁺ P B = A⁺ B P = A⁺ B A A⁺ = A⁺ A B A⁺ = P B A⁺ = B P A⁺ = B A⁺`.

Self-adjointness is not decorative: for a general `A`, commuting with `A` alone
does not make `B` commute with `A⁺`. -/
theorem moorePenroseInverse_comm_of_isSymmetric {A B : E →ₗ[𝕜] E} (hA : A.IsSymmetric)
    (hAB : B ∘ₗ A = A ∘ₗ B) :
    B ∘ₗ moorePenroseInverse A = moorePenroseInverse A ∘ₗ B := by
  have hmul : ∀ f g : E →ₗ[𝕜] E, f ∘ₗ g = f * g := fun _ _ => rfl
  have hadjmul : ∀ f g : E →ₗ[𝕜] E,
      LinearMap.adjoint (f * g) = LinearMap.adjoint g * LinearMap.adjoint f :=
    fun f g => LinearMap.adjoint_comp f g
  set G := moorePenroseInverse A with hG
  have h1 : A * G * A = A := by
    have := comp_moorePenroseInverse_comp A
    simpa [hmul, mul_assoc] using this
  have h2 : G * A * G = G := by
    have := moorePenroseInverse_comp_comp A
    simpa [hmul, mul_assoc] using this
  have hP : A * G = G * A := by
    have := comp_moorePenroseInverse_comm_of_isSymmetric hA
    simpa [hmul] using this
  have hab : B * A = A * B := by simpa [hmul] using hAB
  have hab' : LinearMap.adjoint B * A = A * LinearMap.adjoint B := by
    have h := congrArg LinearMap.adjoint hAB
    rw [LinearMap.adjoint_comp, LinearMap.adjoint_comp, hA.adjoint_eq] at h
    simpa [hmul] using h.symm
  -- Name the Penrose projection so that adjoints do not descend into it.
  obtain ⟨P, hPdef⟩ : ∃ P : E →ₗ[𝕜] E, P = A * G := ⟨_, rfl⟩
  have hPsym : LinearMap.adjoint P = P := by
    have h := (isSymmetric_comp_moorePenroseInverse A).adjoint_eq
    rw [hPdef]
    simpa [hmul] using h
  -- `P C P = C P` for anything commuting with `A`; only the first Penrose
  -- identity is used.
  have hkey : ∀ C : E →ₗ[𝕜] E, C * A = A * C → P * C * P = C * P := by
    intro C hC
    rw [hPdef]
    calc A * G * C * (A * G)
        = A * (G * (C * A)) * G := by noncomm_ring
      _ = A * (G * (A * C)) * G := by rw [hC]
      _ = A * G * A * (C * G) := by noncomm_ring
      _ = A * (C * G) := by rw [h1]
      _ = (A * C) * G := by noncomm_ring
      _ = (C * A) * G := by rw [hC]
      _ = C * (A * G) := by noncomm_ring
  have hPB : A * G * B = B * (A * G) := by
    have hBstar := hkey (LinearMap.adjoint B) hab'
    have hadj := congrArg LinearMap.adjoint hBstar
    rw [hadjmul, hadjmul, hadjmul, hPsym, LinearMap.adjoint_adjoint] at hadj
    -- `hadj : P * (B * P) = P * B`
    have hleft : P * B * P = P * B := by rw [mul_assoc]; exact hadj
    have := hleft.symm.trans (hkey B hab)
    rw [hPdef] at this
    exact this
  have hfinal : G * B = B * G := by
    calc G * B = (G * A * G) * B := by rw [h2]
      _ = G * (A * G * B) := by noncomm_ring
      _ = G * (B * (A * G)) := by rw [hPB]
      _ = G * (B * A) * G := by noncomm_ring
      _ = G * (A * B) * G := by rw [hab]
      _ = (G * A) * B * G := by noncomm_ring
      _ = (A * G) * B * G := by rw [hP]
      _ = (A * G * B) * G := by noncomm_ring
      _ = (B * (A * G)) * G := by rw [hPB]
      _ = B * ((G * A) * G) := by rw [hP]; noncomm_ring
      _ = B * G := by rw [h2]
  simpa [hmul] using hfinal.symm

/-- A map that vanishes on `ker A` factors through the initial projection
`A⁺ A`.  This is the finite-dimensional form of the universal property of the
Moore--Penrose initial projection and is the useful orientation for angular
factorizations. -/
theorem comp_moorePenroseInverse_comp_eq_of_ker_le
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    
    (A : E →ₗ[𝕜] F) (B : E →ₗ[𝕜] G) (hker : A.ker ≤ B.ker) :
    B ∘ₗ moorePenroseInverse A ∘ₗ A = B := by
  apply (TauCeti.rightSingularBasis A).toBasis.ext
  intro i
  rw [OrthonormalBasis.coe_toBasis]
  by_cases hi : A.singularValues i = 0
  · have hAi : A (TauCeti.rightSingularBasis A i) = 0 :=
      TauCeti.apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi
    have hBi : B (TauCeti.rightSingularBasis A i) = 0 := by
      apply LinearMap.mem_ker.mp
      apply hker
      exact LinearMap.mem_ker.mpr hAi
    simp [LinearMap.comp_apply, hAi, hBi]
  · change B (moorePenroseInverse A
        (A (TauCeti.rightSingularBasis A i))) =
      B (TauCeti.rightSingularBasis A i)
    rw [moorePenroseInverse_apply_apply_rightSingularBasis A hi]

end TauCeti
