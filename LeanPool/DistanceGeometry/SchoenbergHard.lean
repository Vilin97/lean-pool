/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import LeanPool.DistanceGeometry.Defs
public import LeanPool.DistanceGeometry.Schoenberg
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Algebra.Order.Star.Real

/-!
# Schoenberg's characterization: the sufficiency direction

This file proves the converse of `schoenberg_easy`: if `D` satisfies
`IsPreDistMatrix`, this project's symmetric-and-hollow structural predicate, and its
basepoint-centered Gram matrix is positive semidefinite of rank at most `k`, then `D`
is the squared-distance matrix of some configuration in
`EuclideanSpace ℝ (Fin k)`. Combined with the easy direction this gives the full
Schoenberg characterization `schoenberg`.

The mathematical core is a rank-controlled factorization of a positive
semidefinite matrix, `Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le`,
which states that a PSD matrix `G` with `G.rank ≤ k` factors as `Mᴴ * M` for some
`k × n` matrix `M`. This is proved from the spectral theorem (a full factorization
`Nᴴ * N = G` with `N = diagonal (√eigenvalues) * Uᴴ`) followed by relocating the
support of the nonzero eigenvalues into `Fin k` via a scatter matrix. Given such an
`M`, the columns of `M`, viewed in `EuclideanSpace ℝ (Fin k)`, realize the
configuration, and reverse polarization recovers `D`.

## Main results

* `Matrix.PosSemidef.exists_conjTranspose_mul_self_of_rank_le` : rank-controlled
  Cholesky-type factorization of a PSD matrix.
* `DistanceGeometry.schoenberg_hard` : the sufficiency direction.
* `DistanceGeometry.schoenberg` : the full characterization (an iff).
-/

@[expose] public section

open Matrix
open scoped RealInnerProductSpace

namespace Matrix

variable {n k : ℕ}

/-! ### Rank-controlled factorization of a positive semidefinite matrix -/

section Factorization

variable {G : Matrix (Fin n) (Fin n) ℝ}

/-- The PSD matrix `G` factors as `Nᴴ * N` where `N = diagonal (√eigenvalues) * Uᴴ`
(`U` the eigenvector unitary). Pure matrix algebra from the spectral theorem. The
factor `N` is supplied via the hypothesis `hNdef` to keep the statement readable. -/
private theorem psd_factor_full (hG : G.PosSemidef)
    {N : Matrix (Fin n) (Fin n) ℝ}
    (hNdef : N = diagonal (fun r => Real.sqrt (hG.1.eigenvalues r))
      * (hG.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)ᴴ) :
    Nᴴ * N = G := by
  classical
  set hH := hG.1 with hHdef
  set s : Fin n → ℝ := fun r => Real.sqrt (hH.eigenvalues r) with hs
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  rw [hNdef]
  -- `s r * s r = eigenvalues r` because eigenvalues of a PSD matrix are nonneg
  have hssμ : (fun r => s r * s r) = hH.eigenvalues := by
    funext r
    rw [hs]
    exact Real.mul_self_sqrt (hG.eigenvalues_nonneg r)
  -- spectral theorem in `U D Uᴴ` form
  have hspec : G = U * diagonal hH.eigenvalues * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose] at h
    -- `RCLike.ofReal ∘ eigenvalues = eigenvalues` over ℝ
    have hcoe : (RCLike.ofReal ∘ hH.eigenvalues : Fin n → ℝ) = hH.eigenvalues := by
      rw [RCLike.ofReal_real_eq_id]; rfl
    rw [hcoe] at h
    exact h
  -- expand the factorization
  rw [conjTranspose_mul, conjTranspose_conjTranspose, diagonal_conjTranspose]
  -- star s = s since ℝ has trivial star
  have hstars : (star s : Fin n → ℝ) = s := by funext r; exact star_trivial _
  rw [hstars, Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal s) (diagonal s) Uᴴ,
      diagonal_mul_diagonal, hssμ]
  conv_rhs => rw [hspec, Matrix.mul_assoc]

end Factorization

/-! ### Scatter matrix: relocate the support into `Fin k` -/

section Scatter

variable {p : Fin n → Prop} [DecidablePred p]

/-- The scatter matrix associated to an injection `ι` of the support `{r // p r}`
into `Fin k`: its `(t, r)` entry is `1` if `r` is in the support and `ι` sends it
to `t`, else `0`. -/
private noncomputable def scatter (ι : {r : Fin n // p r} ↪ Fin k) :
    Matrix (Fin k) (Fin n) ℝ :=
  fun t r => if h : p r then (if ι ⟨r, h⟩ = t then (1 : ℝ) else 0) else 0

/-- `Sᴴ * S` is the diagonal indicator of the support. The injectivity of `ι`
collapses the column inner products. -/
private theorem scatter_conjTranspose_mul_self (ι : {r : Fin n // p r} ↪ Fin k) :
    (scatter ι)ᴴ * scatter ι = diagonal (fun r => if p r then (1 : ℝ) else 0) := by
  classical
  ext r r'
  rw [mul_apply]
  simp only [conjTranspose_apply, scatter, star_trivial, diagonal_apply]
  by_cases hr : p r
  · by_cases hr' : p r'
    · -- both in support: sum collapses via injectivity
      simp only [hr, hr', dif_pos]
      -- product of two indicators, summed over the column index
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (ι ⟨r', hr'⟩)
        (fun x => if ι ⟨r, hr⟩ = x then (1 : ℝ) else 0)]
      simp only [Finset.mem_univ, if_true]
      by_cases hrr' : r = r'
      · subst hrr'; simp
      · have hne : ι ⟨r, hr⟩ ≠ ι ⟨r', hr'⟩ := by
          intro h
          exact hrr' (congrArg Subtype.val (ι.injective h))
        rw [if_neg hne, if_neg hrr']
    · -- r in support, r' not: diagonal entry is 0, sum is 0
      have hrr' : r ≠ r' := fun h => hr' (h ▸ hr)
      simp [hr', hrr']
  · -- r not in support: everything 0
    have : ∀ r', r ≠ r' ∨ ¬ p r := fun r' => Or.inr hr
    simp [hr]

end Scatter

/-! ### The `k × n` factor `M` with `Mᴴ * M = G` -/

namespace PosSemidef

variable {G : Matrix (Fin n) (Fin n) ℝ}

/-- A positive semidefinite matrix `G` with `G.rank ≤ k` factors as `Mᴴ * M` for
some matrix `M : Matrix (Fin k) (Fin n) ℝ`. This rank-controlled Cholesky-type
factorization realizes `G` in ambient dimension `k` and uses only `G.rank` active
directions. -/
theorem exists_conjTranspose_mul_self_of_rank_le (hG : G.PosSemidef) (hrank : G.rank ≤ k) :
    ∃ M : Matrix (Fin k) (Fin n) ℝ, Mᴴ * M = G := by
  classical
  set hH := hG.1 with hHdef
  set μ := hH.eigenvalues with hμ
  set s : Fin n → ℝ := fun r => Real.sqrt (μ r) with hs
  set U : Matrix (Fin n) (Fin n) ℝ := (hH.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) with hU
  set N : Matrix (Fin n) (Fin n) ℝ := diagonal s * Uᴴ with hN
  -- the full factorization `Nᴴ * N = G`
  have hNG : Nᴴ * N = G := psd_factor_full hG (by rw [hN, hs, hU, hμ])
  -- support predicate and injection into `Fin k`
  have hcard : Fintype.card {r : Fin n // μ r ≠ 0} ≤ Fintype.card (Fin k) := by
    rw [Fintype.card_fin]
    rw [← hH.rank_eq_card_non_zero_eigs]
    exact hrank
  obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le hcard
  -- scatter matrix and the candidate `M`
  set S : Matrix (Fin k) (Fin n) ℝ := scatter (p := fun r => μ r ≠ 0) ι with hSdef
  refine ⟨S * N, ?_⟩
  -- `Sᴴ * S = diagonal indic`, and `diagonal indic * N = N`
  have hSS : Sᴴ * S = diagonal (fun r => if μ r ≠ 0 then (1 : ℝ) else 0) :=
    scatter_conjTranspose_mul_self ι
  have hdiagN : diagonal (fun r => if μ r ≠ 0 then (1 : ℝ) else 0) * N = N := by
    ext r j
    rw [diagonal_mul]
    by_cases hr : μ r ≠ 0
    · simp [hr]
    · simp only [hr, if_false, zero_mul]
      -- row `r` of `N` is zero because `s r = √0 = 0`
      have hμ0 : μ r = 0 := not_not.mp hr
      have hsr : s r = 0 := by rw [hs]; simp [hμ0]
      have : N r j = 0 := by
        rw [hN, mul_apply]
        apply Finset.sum_eq_zero
        intro x _
        rw [diagonal_apply]
        by_cases hrx : r = x
        · subst hrx; simp [hsr]
        · rw [if_neg hrx]; ring
      rw [this]
  -- assemble: `(S*N)ᴴ * (S*N) = Nᴴ * (Sᴴ*S) * N = Nᴴ * N = G`
  rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Sᴴ S N, hSS, hdiagN, hNG]

end PosSemidef

end Matrix

namespace DistanceGeometry

open Matrix
open scoped RealInnerProductSpace

variable {n k : ℕ} [NeZero n]

/-! ### Schoenberg, sufficiency direction -/

/-- The sufficiency direction of Schoenberg's theorem. If `D` satisfies this project's
`IsPreDistMatrix` predicate (symmetric and hollow) and its basepoint-centered Gram
matrix is positive semidefinite of rank at most `k`, then `D` is the squared-distance
matrix of some configuration in
`EuclideanSpace ℝ (Fin k)`.

This is the converse of `schoenberg_easy`: it reconstructs the point configuration
from the Gram data. -/
theorem schoenberg_hard
    {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : IsPreDistMatrix D)
    (hPSD : (centeredGram D).PosSemidef)
    (hrank : (centeredGram D).rank ≤ k) :
    EmbedsIn D k := by
  classical
  set G := centeredGram D with hGdef
  -- rank-controlled factorization `Mᴴ * M = G`
  obtain ⟨M, hM⟩ := hPSD.exists_conjTranspose_mul_self_of_rank_le hrank
  -- points = columns of `M`, viewed in `EuclideanSpace ℝ (Fin k)`
  refine ⟨fun i => (WithLp.toLp 2 (Mᵀ i) : EuclideanSpace ℝ (Fin k)), ?_⟩
  intro i j
  -- inner product of columns `i` and `j` of `M` is `(Mᴴ * M) i j = G i j`
  have hinner : ∀ a b : Fin n,
      ⟪(WithLp.toLp 2 (Mᵀ a) : EuclideanSpace ℝ (Fin k)),
        (WithLp.toLp 2 (Mᵀ b) : EuclideanSpace ℝ (Fin k))⟫ = G a b := by
    intro a b
    -- `⟪col a, col b⟫ = ∑ t, M t a * M t b = (Mᴴ * M) a b = G a b`
    rw [← hM, mul_apply]
    simp only [PiLp.inner_apply, transpose_apply, conjTranspose_apply, star_trivial]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    calc (inner ℝ (M t a) (M t b) : ℝ) = (starRingEnd ℝ) (M t a) * M t b :=
          RCLike.inner_apply' (M t a) (M t b)
      _ = M t a * M t b := by rw [conj_trivial]
  -- reverse polarization: dist² = ⟪v,v⟫ = ⟪xi,xi⟫ - ⟪xi,xj⟫ - ⟪xj,xi⟫ + ⟪xj,xj⟫
  rw [dist_eq_norm, ← real_inner_self_eq_norm_sq, inner_sub_sub_self]
  beta_reduce
  rw [hinner i i, hinner i j, hinner j i, hinner j j]
  simp only [hGdef, centeredGram_apply]
  -- now purely algebraic: use symmetry and hollowness of `D`
  rw [hD.hollow i, hD.hollow j, hD.symm j i]
  ring

/-- Schoenberg's characterization of Euclidean squared-distance matrices. A matrix
`D` satisfying this project's `IsPreDistMatrix` predicate (symmetric and hollow)
embeds as a squared-distance matrix in `EuclideanSpace ℝ (Fin k)` if and only if its
basepoint-centered Gram matrix is positive semidefinite and has rank at most `k`. -/
theorem schoenberg {D : Matrix (Fin n) (Fin n) ℝ} (hD : IsPreDistMatrix D) :
    EmbedsIn D k ↔ (centeredGram D).PosSemidef ∧ (centeredGram D).rank ≤ k := by
  constructor
  · rintro ⟨x, hx⟩
    exact schoenberg_easy hx
  · rintro ⟨hPSD, hrank⟩
    exact schoenberg_hard hD hPSD hrank

end DistanceGeometry
