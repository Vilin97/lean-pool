/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import LeanPool.DavisKahan.ForTauCeti.LinearAlgebra.Matrix.RankFactorization

/-! # Rank-constrained positive-semidefinite factorization

A positive-semidefinite matrix `B` factors as `B = Aᴴ * A` with `A` having at
most `d` rows **iff** its rank is at most `d` — equivalently, a PSD matrix of
rank `≤ d` is the Gram matrix of `n` points in `𝕜^d`, the classical
multidimensional-scaling embedding step.

The factorization is assembled from two reusable pieces:
* the **square** factorization `B = Aᴴ * A` with `A` square, built spectrally
  (`A = √D · Uᴴ` for the spectral decomposition `B = U D Uᴴ`); and
* the **rank factorization** `A = L * R` through `Fin d`
  (`TauCeti.Matrix.exists_eq_mul_of_rank_le`), which compresses the inner
  dimension.

A second application of the square factorization to `Lᴴ * L` then yields the
rank-controlled Gram factor `(S * R)ᴴ * (S * R)`.  The reverse direction is
`posSemidef_conjTranspose_mul_self` with `rank_conjTranspose_mul_self` and
`rank_le_height`.

## Main results

* `TauCeti.Matrix.PosSemidef.exists_eq_conjTranspose_mul_self`: the square
  factorization `B = Aᴴ * A` of a PSD matrix (spectral construction).
* `TauCeti.Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le`: the
  rank-controlled factorization, `A` of size `d × n` for any `rank B ≤ d`.
* `TauCeti.Matrix.posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self`:
  the iff characterization, over `RCLike 𝕜`.

## References

* Cox & Cox, *Multidimensional Scaling*, 2nd ed., §2.2–2.3 (classical scaling).
* Horn & Johnson, *Matrix Analysis*, 2nd ed. (spectral theorem and PSD Gram
  factorizations).

## Staging note

Staged for Tau Ceti, roadmap topic T21.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/LinearAlgebra/Matrix/PosDef.lean`.
Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); rank-controlled direction
reproved through the rank-factorization API by Claude Fable 5 (claude-fable-5[1m]).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `e9379f2`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/LinearAlgebra/Matrix/PosDef.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (rule 2 of
  `scripts/check_dependency_layers.py`); this module imports Mathlib only.

## Provenance

*Moved, not restated.*  This file lived in the retired `ForMathlib` staging tree
before `ForMathlib` was retired entirely: its four
surviving modules moved here and the library, its root module and its directory
were deleted.  Statements, proofs and signatures are unchanged.

**FM-RETIRE was worked twice, and the two versions disagreed on the namespace.**
The `main` version (`c85510d6`) kept `namespace ForMathlib.Matrix` here, reasoning
that `Challenge/**/Conformance.lean` is immutable so its `ForMathlib.*` pins could
not be re-issued.  Reconciled on merge in favour of `TauCeti.Matrix`; the rationale
and the list of pins updated to match is recorded once, in
`ForTauCeti/Topology/Berge.lean`.

-/

public section

/-!
### Provenance

Moved into `ForTauCeti/LinearAlgebra/Matrix/`
as part of the `ForMathlib` retirement.  The
namespace changed from `ForMathlib.Matrix` to `TauCeti.Matrix` to match the
destination package; declaration names, statements and proofs are unchanged.
-/

namespace TauCeti.Matrix

open scoped BigOperators _root_.Matrix ComplexConjugate ComplexOrder InnerProductSpace
open _root_.Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/--
Entrywise spectral expansion of a Hermitian matrix over `𝕜 = ℝ, ℂ`:
`B i j = Σ_k (eigenvalues k) * U i k * conj (U j k)`, where `U` is the
eigenvector unitary.  This is the entrywise form of
`Matrix.IsHermitian.spectral_theorem`.
-/
theorem isHermitian_entry_eq_sum_eigenvalues
    (B : Matrix (Fin n) (Fin n) 𝕜) (hB : B.IsHermitian) (i j : Fin n) :
    B i j = ∑ k : Fin n,
      (hB.eigenvalues k : 𝕜) * (hB.eigenvectorUnitary i k) *
        conj (hB.eigenvectorUnitary j k) := by
  have hspec := hB.spectral_theorem
  have hentry : B i j =
      (hB.eigenvectorUnitary *
        (diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) *
          (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜))) i j := by
    conv_lhs => rw [hspec]
    rw [Unitary.conjStarAlgAut_apply]
    simp [mul_assoc]
  rw [hentry, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply]
  have hdiag : ∑ l : Fin n,
      diagonal ((RCLike.ofReal : ℝ → 𝕜) ∘ hB.eigenvalues) k l *
        (star hB.eigenvectorUnitary : Matrix (Fin n) (Fin n) 𝕜) l j
      = (hB.eigenvalues k : 𝕜) * conj (hB.eigenvectorUnitary j k) := by
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, Matrix.star_apply, RCLike.star_def]
      rfl
    · intro l _ hl
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
    · intro h; exact absurd (Finset.mem_univ k) h
  rw [hdiag]; ring

/--
**Square PSD factorization.** A positive-semidefinite matrix `B` over `𝕜 = ℝ, ℂ`
factors as `B = Aᴴ * A` with `A` square: take `A = √D · Uᴴ` for the spectral
decomposition `B = U D Uᴴ` (row `k` of `A` is the `k`-th eigenvector scaled by
`√λ_k`).
-/
theorem PosSemidef.exists_eq_conjTranspose_mul_self
    {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) :
    ∃ A : Matrix (Fin n) (Fin n) 𝕜, B = Aᴴ * A := by
  have hHerm : B.IsHermitian := hB.1
  -- `Matrix.of` rather than a bare lambda: a lambda is not recognised as a `Matrix`, and
  -- `Matrix.mul_apply` then has no `*` to rewrite.
  refine ⟨Matrix.of fun k i =>
    (Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary i k), ?_⟩
  ext i j
  rw [Matrix.mul_apply, isHermitian_entry_eq_sum_eigenvalues B hHerm i j]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def]
  simp only [Matrix.of_apply]
  have hnn : 0 ≤ hHerm.eigenvalues k := _root_.Matrix.PosSemidef.eigenvalues_nonneg hB k
  simp only [map_mul, RCLike.conj_ofReal, RCLike.conj_conj]
  rw [show RCLike.ofReal (Real.sqrt (hHerm.eigenvalues k)) * hHerm.eigenvectorUnitary i k *
      ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * conj (hHerm.eigenvectorUnitary j k))
    = ((Real.sqrt (hHerm.eigenvalues k) : 𝕜) * (Real.sqrt (hHerm.eigenvalues k) : 𝕜))
        * (hHerm.eigenvectorUnitary i k * conj (hHerm.eigenvectorUnitary j k)) from by ring]
  rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]
  ring

/--
**Rank-constrained PSD factorization, forward direction.** A positive
semidefinite matrix `B` of rank `≤ d` is the Gram matrix of `n` points in
`𝕜^d`: it factors as `B = Aᴴ * A` for some `A : Matrix (Fin d) (Fin n) 𝕜`.

Proof through the factorization API: write `B = A₀ᴴ * A₀` with `A₀` square
(`PosSemidef.exists_eq_conjTranspose_mul_self`), compress `A₀ = L * R` through
`Fin d` by rank factorization (`rank A₀ = rank B ≤ d`), and absorb the leftover
Gram factor `Lᴴ * L` by a second square factorization `Lᴴ * L = Sᴴ * S`, giving
`B = (S * R)ᴴ * (S * R)`.
-/
theorem PosSemidef.exists_conjTranspose_mul_self_of_rank_le
    {d : ℕ} {B : Matrix (Fin n) (Fin n) 𝕜} (hB : B.PosSemidef) (hrank : B.rank ≤ d) :
    ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  -- Square factorization of `B`, whose factor has the same rank as `B`.
  obtain ⟨A₀, hA₀⟩ := PosSemidef.exists_eq_conjTranspose_mul_self hB
  have hrankA₀ : A₀.rank ≤ d := by
    rwa [hA₀, rank_conjTranspose_mul_self] at hrank
  -- Compress the inner dimension to `Fin d` by rank factorization.
  obtain ⟨L, R, hLR⟩ := exists_eq_mul_of_rank_le A₀ hrankA₀
  -- Absorb the leftover Gram factor `Lᴴ * L` by a second square factorization.
  obtain ⟨S, hS⟩ :=
    PosSemidef.exists_eq_conjTranspose_mul_self (posSemidef_conjTranspose_mul_self L)
  refine ⟨S * R, ?_⟩
  calc B = A₀ᴴ * A₀ := hA₀
    _ = Rᴴ * (Lᴴ * L) * R := by
        rw [hLR, Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = Rᴴ * (Sᴴ * S) * R := by rw [← hS]
    _ = (S * R)ᴴ * (S * R) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]

/--
**Rank-constrained PSD factorization.** A matrix `B` over `𝕜 = ℝ, ℂ` is positive
semidefinite with rank at most `d` if and only if `B = Aᴴ * A` for some
`A : Matrix (Fin d) (Fin n) 𝕜` (equivalently, `B` is the Gram matrix of `n`
points in `𝕜^d`).  Splits into the forward direction
`PosSemidef.exists_conjTranspose_mul_self_of_rank_le` and the elementary
converse (`posSemidef_conjTranspose_mul_self` + `rank_conjTranspose_mul_self`).
-/
theorem posSemidef_and_rank_le_iff_exists_conjTranspose_mul_self
    {d : ℕ} (B : Matrix (Fin n) (Fin n) 𝕜) :
    (B.PosSemidef ∧ B.rank ≤ d) ↔ ∃ A : Matrix (Fin d) (Fin n) 𝕜, B = Aᴴ * A := by
  refine ⟨fun h => PosSemidef.exists_conjTranspose_mul_self_of_rank_le h.1 h.2, ?_⟩
  rintro ⟨A, rfl⟩
  refine ⟨posSemidef_conjTranspose_mul_self A, ?_⟩
  rw [rank_conjTranspose_mul_self]
  exact A.rank_le_height

/-- Equal Gram matrices are exactly equal inner products between images. -/
private theorem gram_inner {m d : ℕ} {A A' : Matrix (Fin d) (Fin m) 𝕜} (h : Aᴴ * A = A'ᴴ * A')
    (x y : EuclideanSpace 𝕜 (Fin m)) :
    ⟪Matrix.toEuclideanLin A x, Matrix.toEuclideanLin A y⟫_𝕜
      = ⟪Matrix.toEuclideanLin A' x, Matrix.toEuclideanLin A' y⟫_𝕜 := by
  have key : ∀ B : Matrix (Fin d) (Fin m) 𝕜,
      ⟪Matrix.toEuclideanLin B x, Matrix.toEuclideanLin B y⟫_𝕜
        = ⟪Matrix.toEuclideanLin (Bᴴ * B) x, y⟫_𝕜 := by
    intro B
    rw [show ((Bᴴ * B).toEuclideanLin) = (Bᴴ).toEuclideanLin ∘ₗ B.toEuclideanLin from ?_,
      LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
      LinearMap.adjoint_inner_left]
    · ext v i; simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  rw [key A, key A', h]

/-- **Gram uniqueness: the configuration is determined up to a unitary.**  If two `d × n`
matrices have the same Gram matrix `AᴴA`, they differ by a unitary acting on the `d` side.

This is the rigid-motion indeterminacy of a recovered configuration in multidimensional scaling:
the Gram matrix fixes all pairwise inner products, hence the configuration up to an isometry of
the ambient `d`-dimensional space, and no more.

**The quantifier side matters and the wrong side is plausible-looking.**  The unitary acts on
`Fin d`, the ambient space; a unitary on the `n` side — permuting or mixing the points — is false.

**No rank hypothesis**, which is why this is not a corollary of the rank-factorization statement:
the factor size `d` is fixed in advance and may exceed the rank, and the group is the unitary group
rather than the invertibles because this statement remembers the inner product.

The proof is the standard one: equal Gram matrices make `A x ↦ A' x` a well-defined isometry of
`range A` onto `range A'`, which `LinearIsometry.extend` extends to the ambient space; a linear
isometry of a finite-dimensional space is an equivalence, and its matrix in an orthonormal basis
is unitary. -/
theorem exists_unitary_mul_of_conjTranspose_mul_self_eq {m d : ℕ}
    {A A' : Matrix (Fin d) (Fin m) 𝕜} (h : Aᴴ * A = A'ᴴ * A') :
    ∃ U ∈ Matrix.unitaryGroup (Fin d) 𝕜, A' = U * A := by
  classical
  set f := Matrix.toEuclideanLin A with hf
  set f' := Matrix.toEuclideanLin A' with hf'
  have hinner := gram_inner h
  -- equal kernels
  have hker : LinearMap.ker f ≤ LinearMap.ker f' := by
    intro x hx
    have := hinner x x
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hx, inner_zero_left] at this
    exact inner_self_eq_zero.mp this.symm
  -- the induced map on the range
  set L₀ : LinearMap.range f →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    (LinearMap.ker f).liftQ f' hker ∘ₗ (f.quotKerEquivRange.symm : _ →ₗ[𝕜] _) with hL₀
  -- The membership must stay universally quantified and in its canonical `∈ LinearMap.range f`
  -- form: written as `⟨x, rfl⟩` it appears unfolded, and `simp only` will not match
  -- `quotKerEquivRange_symm_apply_image` against it.
  have hL₀_apply : ∀ (x : EuclideanSpace 𝕜 (Fin m)) (hx : f x ∈ LinearMap.range f),
      L₀ ⟨f x, hx⟩ = f' x := by
    intro x hx
    simp only [hL₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply]
  -- `L₀` preserves inner products, so it is an isometry of the range into the ambient space
  have hL₀_inner : ∀ y z : LinearMap.range f, ⟪L₀ y, L₀ z⟫_𝕜 = ⟪y, z⟫_𝕜 := by
    rintro ⟨-, x, rfl⟩ ⟨-, w, rfl⟩
    rw [Submodule.coe_inner]
    exact (congrArg₂ (inner 𝕜) (hL₀_apply x _) (hL₀_apply w _)).trans (hinner x w).symm
  set L : LinearMap.range f →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    { toLinearMap := L₀
      norm_map' := fun y => by
        simp only [@norm_eq_sqrt_re_inner 𝕜, hL₀_inner] } with hL
  -- extend to a full isometry of the ambient space, which is unitary
  set Lx : EuclideanSpace 𝕜 (Fin d) →ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d) := L.extend with hLx
  set Le : EuclideanSpace 𝕜 (Fin d) ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 (Fin d) :=
    Lx.toLinearIsometryEquiv rfl with hLe
  set b : OrthonormalBasis (Fin d) 𝕜 (EuclideanSpace 𝕜 (Fin d)) :=
    EuclideanSpace.basisFun (Fin d) 𝕜 with hb
  refine ⟨Le.toMatrix b.toBasis b.toBasis,
    LinearIsometryEquiv.toMatrix_mem_unitaryGroup Le b b, ?_⟩
  -- the extension agrees with `f ↦ f'` on the range, so the two matrices agree
  have hmap : ∀ x, Le (Matrix.toEuclideanLin A x) = Matrix.toEuclideanLin A' x := by
    intro x
    have hx : Lx (f x) = L ⟨f x, ⟨x, rfl⟩⟩ :=
      LinearIsometry.extend_apply L ⟨f x, ⟨x, rfl⟩⟩
    have : Le (f x) = f' x := by
      rw [hLe]; change Lx (f x) = f' x
      rw [hx, hL]
      exact hL₀_apply x _
    exact this
  -- transport to matrices through `toEuclideanLin`
  apply Matrix.toEuclideanLin.injective
  ext x i
  have hcomp : Matrix.toEuclideanLin (Le.toMatrix b.toBasis b.toBasis * A)
      = (Matrix.toEuclideanLin (Le.toMatrix b.toBasis b.toBasis)) ∘ₗ Matrix.toEuclideanLin A := by
    ext v j; simp [Matrix.toLpLin_apply, Matrix.mulVec_mulVec]
  have hLeMat : Matrix.toEuclideanLin (Le.toMatrix b.toBasis b.toBasis)
      = (Le : EuclideanSpace 𝕜 (Fin d) →ₗ[𝕜] EuclideanSpace 𝕜 (Fin d)) := by
    rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, hb]
    exact Matrix.toLin_toMatrix _ _ _
  rw [hcomp, LinearMap.comp_apply, hLeMat]
  exact (congrArg (fun w => w i) (hmap x)).symm

end TauCeti.Matrix
