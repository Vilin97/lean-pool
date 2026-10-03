/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Gram.Matrix
public import LeanPool.DavisKahan.ForTauCeti.Analysis.Convex.Majorization
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.DiagonalOperator
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Basic

/-!
# Ky Fan majorization for rectangular unitarily invariant norms

The engine of the theory: a map whose Ky Fan sums are dominated by another's lies in
the convex hull of the latter's two-sided unitary orbit, and therefore has the smaller
value under *every* rectangular unitarily invariant norm.

The majorization step itself is not proved here.  The two-sided unitary orbit's convex hull
pulls back along a diagonal lift to a `FiniteVector.IsSymmetricConvex` set of coordinate
vectors — coordinate swaps and single-coordinate sign changes are two-sided unitary actions —
so the Hardy--Littlewood--Pólya transfer descent
`FiniteVector.IsSymmetricConvex.mem_of_prefixSum_le` applies directly.  What remains here is
the operator-theoretic half: the lift, the extension of coordinate unitaries to the ambient
spaces, and the transport of equal singular-value data by the rectangular SVD.

## Provenance

Adapted from the rectangular majorization and block-sum modules in the Davis--Kahan/DKPS
formalization (Kitware, Inc.). The vector majorization descent remains in
`ForTauCeti.Analysis.Convex.Majorization`.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [FiniteDimensional 𝕜 G]

/-- **The rank of a map is at most either dimension.**

`finrank (range A) ≤ min (finrank E) (finrank F)`: the codomain bound is
`Submodule.finrank_le` and the domain bound is rank–nullity.  Both theorems
below open by establishing this for `A` and for `B`, four blocks in all. -/
theorem finrank_range_le_min (A : E →ₗ[𝕜] F) :
    finrank 𝕜 (LinearMap.range A) ≤ min (finrank 𝕜 E) (finrank 𝕜 F) := by
  refine le_min ?_ (Submodule.finrank_le _)
  have := A.finrank_range_add_finrank_ker
  omega

namespace UnitarilyInvariantSeminorm

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/- `Module ℝ (E →ₗ[𝕜] F)` is a *local* instance in `Basic`, so it does not survive the
import.  Re-enable it here; making it global would put a second `Module ℝ` structure on
every `𝕜`-linear map space, which is why it is local in the first place. -/
attribute [local instance] realModuleLinearMap


/-- Extend a unitary action on an isometrically embedded coordinate space to
an ambient unitary. -/
private theorem exists_ambient_unitary_intertwining
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    (ι : H →ₗᵢ[𝕜] K) (U : H ≃ₗᵢ[𝕜] H) :
    ∃ W : K ≃ₗᵢ[𝕜] K,
      W.toLinearMap ∘ₗ ι.toLinearMap =
        ι.toLinearMap ∘ₗ U.toLinearMap := by
  obtain ⟨W, hW⟩ := exists_linearIsometryEquiv_map_eq_of_inner_eq
    (φ := fun x : H => ι x) (ψ := fun x : H => ι (U x)) (by
      intro x y
      rw [ι.inner_map_map, ι.inner_map_map, U.inner_map_map])
  refine ⟨W, ?_⟩
  ext x
  simpa only [LinearMap.comp_apply, LinearIsometry.coe_toLinearMap,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] using hW x


/-- **The adjoint form of the intertwining**, which is what the coordinate-lift
calculations actually apply.

Taking adjoints in `W ∘ ι = ι ∘ U` and using that the adjoint of an isometric
equivalence is its inverse turns the statement inside out.  Derived twice below
from the same `exists_ambient_unitary_intertwining` call. -/
private theorem adjoint_comp_symm_of_intertwining
    {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K] [FiniteDimensional 𝕜 H]
    {ι : H →ₗᵢ[𝕜] K} {U : H ≃ₗᵢ[𝕜] H} {W : K ≃ₗᵢ[𝕜] K}
    (hW : W.toLinearMap ∘ₗ ι.toLinearMap = ι.toLinearMap ∘ₗ U.toLinearMap) :
    LinearMap.adjoint ι.toLinearMap ∘ₗ W.symm.toLinearMap =
      U.symm.toLinearMap ∘ₗ LinearMap.adjoint ι.toLinearMap := by
  have h := congrArg LinearMap.adjoint hW
  simpa only [LinearMap.adjoint_comp, W.adjoint_toLinearMap_eq_symm,
    U.adjoint_toLinearMap_eq_symm] using h

/-- Lift an endomorphism of a common coordinate space to a rectangular map by
an isometric codomain embedding and a coisometric domain projection. -/
private noncomputable def coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) : E →ₗ[𝕜] F :=
  ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap

private theorem singularValues_coordinateLift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (X : H →ₗ[𝕜] H) :
    (coordinateLift ιE ιF X).singularValues = X.singularValues := by
  unfold coordinateLift
  calc
    (ιF.toLinearMap ∘ₗ X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues =
        (X ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
      singularValues_linearIsometry_comp ιF _
    _ = X.singularValues :=
      singularValues_comp_adjoint_linearIsometry ιE X

/-- The initial coordinate embedding determined by the first `d` vectors of
the standard orthonormal basis. -/
private noncomputable def initialCoordinateIsometry
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K]
    [FiniteDimensional 𝕜 K]
    {d : ℕ} (hd : d ≤ finrank 𝕜 K) :
    EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] K :=
  familyIsometry ((stdOrthonormalBasis 𝕜 K).orthonormal.comp
    (fun i => Fin.castLE hd i) (Fin.castLE_injective hd))

/-- The square diagonal operator carrying the nonzero rectangular singular
coordinates. -/
private noncomputable def singularValueDiagonal (d : ℕ)
    (A : E →ₗ[𝕜] F) :
    EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
  diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
    (fun i => A.singularValues (i : ℕ))

private theorem singularValues_singularValueDiagonal
    {d : ℕ} (A : E →ₗ[𝕜] F) (hrank : finrank 𝕜 A.range ≤ d) :
    (singularValueDiagonal d A).singularValues = A.singularValues := by
  have hanti : Antitone (fun i : Fin d => A.singularValues (i : ℕ)) :=
    fun i j hij => A.singularValues_antitone (Fin.le_def.mp hij)
  have hnonneg : ∀ i : Fin d, 0 ≤ A.singularValues (i : ℕ) :=
    fun i => A.singularValues_nonneg _
  apply Finsupp.ext
  intro i
  rcases lt_or_ge i d with hi | hi
  · simpa [singularValueDiagonal] using
      singularValues_diagOp (𝕜 := 𝕜) finrank_euclideanSpace_fin
        (EuclideanSpace.basisFun (Fin d) 𝕜) hanti hnonneg ⟨i, hi⟩
  · have hcoord : finrank 𝕜 (EuclideanSpace 𝕜 (Fin d)) ≤ i := by
      simpa only [finrank_euclideanSpace_fin] using hi
    rw [(singularValueDiagonal d A).singularValues_of_finrank_le hcoord,
      A.singularValues_eq_zero_iff_le_finrank_range.mpr (hrank.trans hi)]

/-- A real-linear two-sided unitary action on rectangular maps. -/
private noncomputable def twoSidedActionLinear
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (E →ₗ[𝕜] F) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun A := U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap
  map_add' A B := by
    ext x
    simp [LinearMap.comp_apply]
  map_smul' r A := by
    ext x
    -- states the goal through the private file-local helper, which has no
    -- characteristic lemma to rewrite with.
    change U (((r : 𝕜) • A) (V x)) = ((r : 𝕜) •
      (U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap)) x
    simp [LinearMap.comp_apply]

/-- The real convex hull of a two-sided unitary orbit is invariant under any
further two-sided unitary action. -/
private theorem twoSidedAction_mem_convexHull
    {E₀ F₀ : Type*}
    [NormedAddCommGroup E₀] [InnerProductSpace 𝕜 E₀]
    [NormedAddCommGroup F₀] [InnerProductSpace 𝕜 F₀]
    {A C : E₀ →ₗ[𝕜] F₀}
    (hA : A ∈ convexHull ℝ (twoSidedUnitaryOrbit C))
    (U : F₀ ≃ₗᵢ[𝕜] F₀) (V : E₀ ≃ₗᵢ[𝕜] E₀) :
    U.toLinearMap ∘ₗ A ∘ₗ V.toLinearMap ∈
      convexHull ℝ (twoSidedUnitaryOrbit C) := by
  let L := twoSidedActionLinear (𝕜 := 𝕜) U V
  have hmem : L A ∈ L '' convexHull ℝ (twoSidedUnitaryOrbit C) :=
    ⟨A, hA, rfl⟩
  rw [L.image_convexHull] at hmem
  apply convexHull_mono (𝕜 := ℝ) ?_ hmem
  rintro Y ⟨Y0, ⟨U0, V0, rfl⟩, rfl⟩
  refine ⟨U0.trans U, V.trans V0, ?_⟩
  ext x
  rfl

/-- Lift a square coordinate operator to a rectangular map after arbitrary
left and right coordinate unitaries, extending those unitaries to the ambient
spaces. -/
private theorem coordinateLift_unitary_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [FiniteDimensional 𝕜 H]
    (ιE : H →ₗᵢ[𝕜] E) (ιF : H →ₗᵢ[𝕜] F)
    (U V : H ≃ₗᵢ[𝕜] H) (X : H →ₗ[𝕜] H) :
    ∃ (UF : F ≃ₗᵢ[𝕜] F) (VE : E ≃ₗᵢ[𝕜] E),
      coordinateLift ιE ιF
          (U.toLinearMap ∘ₗ X ∘ₗ V.toLinearMap) =
        UF.toLinearMap ∘ₗ coordinateLift ιE ιF X ∘ₗ VE.toLinearMap := by
  obtain ⟨UF, hUF⟩ := exists_ambient_unitary_intertwining ιF U
  obtain ⟨WE, hWE⟩ := exists_ambient_unitary_intertwining ιE V.symm
  have hadj : LinearMap.adjoint ιE.toLinearMap ∘ₗ WE.symm.toLinearMap =
      V.toLinearMap ∘ₗ LinearMap.adjoint ιE.toLinearMap := by
    simpa using adjoint_comp_symm_of_intertwining hWE
  refine ⟨UF, WE.symm, ?_⟩
  ext z
  simp only [coordinateLift, LinearMap.comp_apply]
  calc
    ιF (U (X (V (LinearMap.adjoint ιE.toLinearMap z)))) =
        UF (ιF (X (V (LinearMap.adjoint ιE.toLinearMap z)))) :=
      (LinearMap.congr_fun hUF _).symm
    _ = UF (ιF (X (LinearMap.adjoint ιE.toLinearMap (WE.symm z)))) := by
      have hz := LinearMap.congr_fun hadj z
      simp only [LinearMap.comp_apply,
        LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe] at hz
      exact congrArg (fun q => UF (ιF (X q))) hz.symm

/-- Real-linear map from a singular-value coordinate vector to its rectangular
diagonal lift. -/
private noncomputable def coordinateDiagonalLift
    {d : ℕ}
    (ιE : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E)
    (ιF : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] F) :
    (Fin d → ℝ) →ₗ[ℝ] (E →ₗ[𝕜] F) where
  toFun x := coordinateLift ιE ιF
    (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
  map_add' x y := by
    ext z
    simp [coordinateLift, diagOp_add, LinearMap.comp_apply]
  map_smul' r x := by
    ext z
    -- unfolds the private helper `coordinateLift`. It has no `_apply` lemma because
    -- it is file-local plumbing rather than public API, so there is nothing to
    -- rewrite with; `change` names the unfolded form the next step needs.
    change coordinateLift ιE ιF
      (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) (r • x)) z =
      ((r : 𝕜) • coordinateLift ιE ιF
        (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)) z
    rw [diagOp_real_smul]
    simp only [coordinateLift, LinearMap.comp_apply, LinearMap.smul_apply]
    exact ιF.toLinearMap.map_smul (r : 𝕜)
      ((diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) x)
        (LinearMap.adjoint ιE.toLinearMap z))

/-- Permuting the entries of a real vector conjugates its diagonal operator by
the corresponding coordinate isometry.  This is why the two-sided unitary orbit
is closed under permutations of the singular values. -/
private theorem diagOp_comp_swap {d : ℕ} (q : Fin d → ℝ) (j l : Fin d) :
    diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) (q ∘ Equiv.swap j l) =
      (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜
          (Equiv.swap j l)).symm.toLinearMap ∘ₗ
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ
          (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜
            (Equiv.swap j l)).toLinearMap := by
  set P : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.swap j l) with hP
  set b := EuclideanSpace.basisFun (Fin d) 𝕜 with hb
  refine b.toBasis.ext fun i => ?_
  simp only [LinearMap.comp_apply, OrthonormalBasis.coe_toBasis]
  rw [diagOp_apply_basis]
  have hPi : P (b i) = b (Equiv.swap j l i) := by simp [hP, hb]
  -- states the goal in the permuted-coordinate form the following step matches
  -- against; the permutation has to appear explicitly for it to fire.
  change ((q (Equiv.swap j l i) : ℝ) : 𝕜) • b i = P.symm (diagOp b q (P (b i)))
  rw [hPi, diagOp_apply_basis, map_smul]
  have hPsymm : P.symm (b (Equiv.swap j l i)) = b i := by
    rw [← hPi, LinearIsometryEquiv.symm_apply_apply]
  rw [hPsymm]

/-- Negating one entry of a real vector composes its diagonal operator with the
reflection in that coordinate's orthogonal complement.  This is why the
two-sided unitary orbit is closed under sign flips. -/
private theorem diagOp_update_neg {d : ℕ} (q : Fin d → ℝ) (j : Fin d) :
    diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
        (Function.update q j (-(q j))) =
      diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ
        (((𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ).reflection).toLinearMap := by
  refine (EuclideanSpace.basisFun (Fin d) 𝕜).toBasis.ext fun i => ?_
  simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply,
    LinearIsometryEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe]
  rcases eq_or_ne i j with rfl | hij
  · simp only [Submodule.reflection_orthogonalComplement_singleton_eq_neg,
      map_neg, diagOp_apply_basis,
      Function.update_self, neg_smul]
  · have hmem : (EuclideanSpace.basisFun (Fin d) 𝕜) i ∈
        (𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
        ((EuclideanSpace.basisFun (Fin d) 𝕜).orthonormal.2 (Ne.symm hij))
    rw [Submodule.reflection_mem_subspace_eq_self hmem,
      diagOp_apply_basis, diagOp_apply_basis, Function.update_of_ne hij]

/-- **The coordinate lift of a diagonal is stable under unitary conjugation of
that diagonal.**  If `diagOp f` is a unitary conjugate of `diagOp q`, then the
lift of `f` lies in the convex hull of the two-sided orbit whenever the lift of
`q` does.

This is what both the permutation and the sign-flip steps of
`mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le` were proving from scratch:
each builds its own unitary on `EuclideanSpace 𝕜 (Fin d)`, cites the matching
`diagOp` identity, and then runs the same three lines.  Stating it once is the
fix `change` steps through `coordinateLift` were standing in for. -/
private theorem coordinateLift_diagOp_mem_convexHull_of_conj
    {d : ℕ}
    (ιE : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] E)
    (ιF : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] F)
    {B : E →ₗ[𝕜] F} {q f : Fin d → ℝ}
    (P P' : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d))
    (hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) f =
      P.toLinearMap ∘ₗ
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ P'.toLinearMap)
    (hq : coordinateLift ιE ιF
        (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B)) :
    coordinateLift ιE ιF
        (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) f) ∈
      convexHull ℝ (twoSidedUnitaryOrbit B) := by
  obtain ⟨UF, VE, hfac⟩ := coordinateLift_unitary_factorization
    ιE ιF P P' (diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q)
  rw [hdiag, hfac]
  exact twoSidedAction_mem_convexHull hq UF VE

/-- Weak singular-value majorization is exactly the finite-dimensional
convex-hull order generated by the two-sided unitary orbit.

The proof applies the Hardy--Littlewood--Pólya transfer descent
(`FiniteVector.IsSymmetricConvex.mem_of_prefixSum_le`) to the preimage of the orbit convex
hull under a rectangular diagonal lift.  Coordinate swaps and sign changes become two-sided
unitary actions — which is exactly `FiniteVector.IsSymmetricConvex` for that preimage — while
equal singular-value data is transported by the rectangular SVD factorization already proved
above. -/
theorem mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le
    {A B : E →ₗ[𝕜] F}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) :
    A ∈ convexHull ℝ (twoSidedUnitaryOrbit B) := by
  classical
  let d : ℕ := min (finrank 𝕜 E) (finrank 𝕜 F)
  have hdE : d ≤ finrank 𝕜 E := by
    dsimp [d]
    exact min_le_left _ _
  have hdF : d ≤ finrank 𝕜 F := by
    dsimp [d]
    exact min_le_right _ _
  let ιE := initialCoordinateIsometry (𝕜 := 𝕜) (K := E) hdE
  let ιF := initialCoordinateIsometry (𝕜 := 𝕜) (K := F) hdF
  let L := coordinateDiagonalLift (𝕜 := 𝕜) ιE ιF
  let z : Fin d → ℝ := fun i => A.singularValues (i : ℕ)
  let y : Fin d → ℝ := fun i => B.singularValues (i : ℕ)
  let K : Set (Fin d → ℝ) :=
    L ⁻¹' convexHull ℝ (twoSidedUnitaryOrbit B)
  have hKconv : Convex ℝ K :=
    (convex_convexHull ℝ (twoSidedUnitaryOrbit B)).linear_preimage L
  have hswap : ∀ q ∈ K, ∀ j l : Fin d,
      q ∘ Equiv.swap j l ∈ K := by
    intro q hq j l
    let P : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜]
        EuclideanSpace 𝕜 (Fin d) :=
      LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 (Equiv.swap j l)
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (q ∘ Equiv.swap j l) =
        P.symm.toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ
            P.toLinearMap :=
      diagOp_comp_swap q j l
    exact coordinateLift_diagOp_mem_convexHull_of_conj ιE ιF P.symm P hdiag hq
  have hneg : ∀ q ∈ K, ∀ j : Fin d,
      Function.update q j (-(q j)) ∈ K := by
    intro q hq j
    let R := ((𝕜 ∙ (EuclideanSpace.basisFun (Fin d) 𝕜) j)ᗮ).reflection
    have hdiag : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (Function.update q j (-(q j))) =
        diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap :=
      diagOp_update_neg q j
    -- `hdiag` has no left factor; the extracted lemma wants a two-sided conjugation,
    -- so the identity supplies the missing one.
    have hdiag' : diagOp (EuclideanSpace.basisFun (Fin d) 𝕜)
          (Function.update q j (-(q j))) =
        (LinearIsometryEquiv.refl 𝕜 (EuclideanSpace 𝕜 (Fin d))).toLinearMap ∘ₗ
          diagOp (EuclideanSpace.basisFun (Fin d) 𝕜) q ∘ₗ R.toLinearMap := by
      rw [hdiag]
      ext x
      rfl
    exact coordinateLift_diagOp_mem_convexHull_of_conj ιE ιF
      (LinearIsometryEquiv.refl 𝕜 _) R hdiag' hq
  have hrankA : finrank 𝕜 A.range ≤ d := finrank_range_le_min A
  have hrankB : finrank 𝕜 B.range ≤ d := finrank_range_le_min B
  have hLy : L y ∈ twoSidedUnitaryOrbit B := by
    have hsigma : (L y).singularValues = B.singularValues := by
      -- unfolds the private helper `coordinateLift`. It has no `_apply` lemma because
      -- it is file-local plumbing rather than public API, so there is nothing to
      -- rewrite with; `change` names the unfolded form the next step needs.
      change (coordinateLift ιE ιF (singularValueDiagonal d B)).singularValues =
        B.singularValues
      rw [singularValues_coordinateLift,
        singularValues_singularValueDiagonal B hrankB]
    obtain ⟨U, V, hfac⟩ :=
      exists_unitary_factorization_of_singularValues_eq hsigma
    exact ⟨U, V, hfac⟩
  have hyK : y ∈ K := subset_convexHull ℝ _ hLy
  have hzanti : Antitone z := fun i j hij =>
    A.singularValues_antitone (Fin.le_def.mp hij)
  have hz0 : ∀ i, 0 ≤ z i := fun i => A.singularValues_nonneg _
  have hy0 : ∀ i, 0 ≤ y i := fun i => B.singularValues_nonneg _
  have hpre : ∀ m : ℕ,
      ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), z i ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin d => (i : ℕ) < m), y i := by
    intro m
    rcases le_or_gt m d with hm | hm
    · rw [sum_filter_lt_eq_sum_fin hm (fun k => A.singularValues k),
        sum_filter_lt_eq_sum_fin hm (fun k => B.singularValues k)]
      exact h m
    · have huniv : (Finset.univ.filter
          fun i : Fin d => (i : ℕ) < m) = Finset.univ :=
        Finset.filter_true_of_mem fun i _ => lt_trans i.isLt hm
      rw [huniv]
      exact h d
  have hzK : z ∈ K :=
    (⟨hKconv, hswap, hneg⟩ : FiniteVector.IsSymmetricConvex K).mem_of_prefixSum_le
      hzanti hz0 hy0 hpre hyK
  have hsigmaA : A.singularValues = (L z).singularValues := by
    symm
    -- unfolds the private helper `coordinateLift`. It has no `_apply` lemma because
    -- it is file-local plumbing rather than public API, so there is nothing to
    -- rewrite with; `change` names the unfolded form the next step needs.
    change (coordinateLift ιE ιF (singularValueDiagonal d A)).singularValues =
      A.singularValues
    rw [singularValues_coordinateLift,
      singularValues_singularValueDiagonal A hrankA]
  obtain ⟨U, V, hfac⟩ :=
    exists_unitary_factorization_of_singularValues_eq hsigmaA
  -- restates the hypothesis through the private helper `L`, which has no
  -- characteristic lemma to rewrite with: it is file-local plumbing, not API.
  change L z ∈ convexHull ℝ (twoSidedUnitaryOrbit B) at hzK
  rw [hfac]
  exact twoSidedAction_mem_convexHull hzK U V


/-- Convex-hull domination by a two-sided unitary orbit implies domination in
any rectangular unitarily invariant norm.

The proof extracts the existing finite orbit certificate with mass one and
then applies the certificate norm bound. -/
theorem apply_le_of_mem_convexHull_twoSidedUnitaryOrbit
    {A B : E →ₗ[𝕜] F}
    (h : A ∈ convexHull ℝ (twoSidedUnitaryOrbit B)) :
    N A ≤ N B := by
  have hcert : HasFiniteUnitaryOrbitCertificate 1 A B :=
    hasFiniteUnitaryOrbitCertificate_of_smul_mem_convexHull
      (m := 1) (mass := 1) zero_le_one le_rfl h (by simp)
  simpa using N.apply_le_of_finiteUnitaryOrbitCertificate hcert


/-- Fan dominance for rectangular maps: domination of all Ky Fan sums implies
comparison in every unitarily invariant seminorm on that map space. -/
theorem apply_le_of_kyFanSum_le {A B : E →ₗ[𝕜] F}
    (h : ∀ k, kyFanSum k A ≤ kyFanSum k B) : N A ≤ N B :=
  N.apply_le_of_mem_convexHull_twoSidedUnitaryOrbit
    (mem_convexHull_twoSidedUnitaryOrbit_of_kyFanSum_le h)

/-! ### The operator-ideal property -/

/-- **The ideal property (left factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (C ∘ₗ X) ≤ c * N X` for every unitarily invariant norm.  From Fan dominance
applied to the singular-value domination `σᵢ(C ∘ X) ≤ c σᵢ(X)`. -/
theorem apply_comp_le {C : F →ₗ[𝕜] F} {X : E →ₗ[𝕜] F} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (C ∘ₗ X) ≤ c * N X :=
  calc N (C ∘ₗ X)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le hc hC X i) k
    _ = c * N X := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc]

/-- **The ideal property (right factor).**  If `‖C y‖ ≤ c ‖y‖` for `0 ≤ c`, then
`N (X ∘ₗ C) ≤ N X * c`. -/
theorem apply_comp_le' {X : E →ₗ[𝕜] F} {C : E →ₗ[𝕜] E} {c : ℝ} (hc : 0 ≤ c)
    (hC : ∀ y, ‖C y‖ ≤ c * ‖y‖) : N (X ∘ₗ C) ≤ N X * c :=
  calc N (X ∘ₗ C)
      ≤ N (((c : 𝕜)) • X) :=
        N.apply_le_of_kyFanSum_le fun k =>
          kyFanSum_le_of_singularValues_le (fun i => by
            rw [singularValues_real_smul X hc i]
            exact singularValues_comp_le' hc hC i) k
    _ = N X * c := by rw [N.smul_eq, RCLike.norm_ofReal, abs_of_nonneg hc, mul_comm]



end UnitarilyInvariantSeminorm


end TauCeti
