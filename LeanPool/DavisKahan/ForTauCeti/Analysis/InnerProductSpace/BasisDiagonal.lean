/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

/-
Staged for Tau Ceti: additions to `Mathlib/Analysis/InnerProductSpace/Spectrum.lean`,
or a new file next to `OrthonormalBasis` in `PiL2`.
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.BasisSpan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.EigenblockSpan
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Spectral.Subspace
public import Mathlib.Analysis.InnerProductSpace.Spectrum

/-! # Operators diagonal in a given orthonormal basis

`TauCeti.basisDiagonal b c` scales the `i`-th vector of the orthonormal basis
`b` by the real number `c i`.  Every concrete spectral example is one of these,
and the point of the file is that its whole spectral theory is *readable off the
data*: the eigenspace at `μ` is the span of the basis vectors whose coefficient
is `μ` (`eigenspace_basisDiagonal`), so multiplicities are cardinalities of
level sets and the spectrum is the range of `c`.

This is what a concrete Davis--Kahan example needs.  Mathlib's
`LinearMap.IsSymmetric.eigenvectorBasis` is a *choice* of eigenbasis and its
`spanIndices` blocks are easy to consume and hard to produce; combined with
`ForTauCeti/Analysis/InnerProductSpace/EigenblockSpan.lean`, the results here
close that gap for any operator presented diagonally.

## Main results

* `TauCeti.basisDiagonal`: the operator, and `basisDiagonal_apply_basis`.
* `TauCeti.isSymmetric_basisDiagonal`: it is symmetric, since `c` is real-valued.
* `TauCeti.eigenspace_basisDiagonal`: `eigenspace (basisDiagonal b c) μ` is
  `b.spanIndices {i | (c i : 𝕜) = μ}`.
* `TauCeti.finrank_eigenspace_basisDiagonal`: multiplicity is the level-set count.
* `TauCeti.le_of_hasEigenvalue_basisDiagonal`: every eigenvalue is a value of `c`,
  so a bound on `c` is a bound on the spectrum.

## Relation to `NearIsometry.lean`

`ForTauCeti/Analysis/InnerProductSpace/NearIsometry.lean` carries a `private`
real-scalar `Fin d`-indexed copy of the definition and of three of the lemmas
below, introduced for the polar-factorization proof before this general API
existed.  Retargeting it is a follow-up: that proof is delicate and the
duplication is inert, not load-bearing.
-/

public section

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*} [Fintype ι]

/-- The operator scaling the `i`-th vector of an orthonormal basis by `c i`. -/
noncomputable def basisDiagonal (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) :
    E →ₗ[𝕜] E :=
  b.toBasis.constr 𝕜 fun i => (c i : 𝕜) • b i

/-- The diagonal operator acts on the basis it is diagonal in by the
corresponding scalar. -/
@[simp]
theorem basisDiagonal_apply_basis (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ)
    (i : ι) : basisDiagonal b c (b i) = (c i : 𝕜) • b i := by
  have := b.toBasis.constr_basis 𝕜 (fun j => (c j : 𝕜) • b j) i
  rwa [OrthonormalBasis.coe_toBasis] at this

/-- Every coordinate subspace is invariant under the diagonal operator. -/
theorem isInvariant_basisDiagonal_spanIndices (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) (S : Set ι) : IsInvariant (basisDiagonal b c) (b.spanIndices S) := by
  intro x hx
  change basisDiagonal b c x ∈ Submodule.span 𝕜 (b '' S)
  change x ∈ Submodule.span 𝕜 (b '' S) at hx
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · rintro y ⟨i, hi, rfl⟩
    rw [basisDiagonal_apply_basis]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  · simp
  · intro x y _ _ hx hy
    simpa only [map_add] using Submodule.add_mem _ hx hy
  · intro a x _ hx
    simpa only [map_smul] using Submodule.smul_mem _ a hx

/-- The basis coordinates of a diagonal operator's value are scaled pointwise. -/
theorem repr_basisDiagonal (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) (x : E)
    (i : ι) : b.repr (basisDiagonal b c x) i = (c i : 𝕜) * b.repr x i := by
  classical
  have hone : ⟪b i, b i⟫_𝕜 = 1 := by
    rw [← b.repr_apply_apply, b.repr_self]
    simp
  have hx : basisDiagonal b c x = ∑ j, b.repr x j • ((c j : 𝕜) • b j) := by
    conv_lhs => rw [← b.sum_repr x, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, basisDiagonal_apply_basis]
  rw [b.repr_apply_apply, hx, inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_right, inner_smul_right, hone]
    ring
  · intro j _ hji
    rw [inner_smul_right, inner_smul_right, b.inner_eq_zero (Ne.symm hji)]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Diagonal operators in a fixed basis subtract coefficientwise. -/
theorem basisDiagonal_sub (b : OrthonormalBasis ι 𝕜 E) (c c' : ι → ℝ) :
    basisDiagonal b c - basisDiagonal b c' = basisDiagonal b (c - c') := by
  refine b.toBasis.ext fun i => ?_
  simp [LinearMap.sub_apply, sub_smul, RCLike.ofReal_sub]

/-- A diagonal operator with real coefficients is symmetric. -/
theorem isSymmetric_basisDiagonal (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) :
    (basisDiagonal b c).IsSymmetric := by
  intro x y
  rw [← b.repr.inner_map_map (basisDiagonal b c x) y,
    ← b.repr.inner_map_map x (basisDiagonal b c y)]
  simp only [PiLp.inner_apply, RCLike.inner_apply, repr_basisDiagonal]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, RCLike.conj_ofReal]
  ring

/-- **The eigenspaces of a diagonal operator are level sets of its data.**  This
is the lemma that makes concrete spectral examples computable: it turns a
question about `eigenspace` into a question about `{i | c i = μ}`. -/
theorem eigenspace_basisDiagonal (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ)
    (μ : 𝕜) :
    eigenspace (basisDiagonal b c) μ = b.spanIndices {i | (c i : 𝕜) = μ} := by
  classical
  ext x
  rw [Module.End.mem_eigenspace_iff, OrthonormalBasis.mem_spanIndices_iff]
  constructor
  · intro hx i hi
    -- Compare the `i`-th coordinate of both sides of `T x = μ • x`.
    have hcoord : (c i : 𝕜) * b.repr x i = μ * b.repr x i := by
      rw [← repr_basisDiagonal b c x i, hx]
      simp
    rcases mul_eq_mul_right_iff.mp hcoord with h | h
    · exact absurd h hi
    · exact h
  · intro hx
    -- Off the level set the coordinates vanish, so both sides agree coordinatewise.
    refine b.repr.injective ?_
    ext i
    rw [map_smul, repr_basisDiagonal]
    by_cases hi : (c i : 𝕜) = μ
    · rw [hi]; simp
    · simp [hx i hi]

open scoped Classical in
/-- The multiplicity of `μ` is the number of indices carrying it. -/
theorem finrank_eigenspace_basisDiagonal (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) (μ : 𝕜) :
    finrank 𝕜 (eigenspace (basisDiagonal b c) μ) =
      ({i | (c i : 𝕜) = μ} : Finset ι).card := by
  classical
  rw [eigenspace_basisDiagonal, OrthonormalBasis.finrank_spanIndices_set]
  congr 1
  ext i
  simp

/-- **A constant diagonal is a scalar.**  `basisDiagonal b (fun _ => c) = c • id`,
so *every* vector is an eigenvector — the extreme case of a repeated
eigenvalue. -/
theorem basisDiagonal_const (b : OrthonormalBasis ι 𝕜 E) (c : ℝ) (x : E) :
    basisDiagonal b (fun _ => c) x = (c : 𝕜) • x := by
  refine b.repr.injective ?_
  ext i
  rw [repr_basisDiagonal, map_smul]
  simp [RCLike.real_smul_eq_coe_mul]

/-- **A bound on the data is a bound on the spectrum.**  Every eigenvalue of a
diagonal operator is one of its coefficients. -/
theorem le_of_hasEigenvalue_basisDiagonal (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) {M : ℝ} (hc : ∀ i, c i ≤ M) {lam : ℝ}
    (hlam : Module.End.HasEigenvalue (basisDiagonal b c) (lam : 𝕜)) :
    lam ≤ M := by
  classical
  -- A nonzero eigenvector has a nonzero coordinate, and that index carries `lam`.
  obtain ⟨x, hxmem₀, hx0⟩ := Submodule.ne_bot_iff _ |>.mp hlam
  have hxmem : x ∈ eigenspace (basisDiagonal b c) (lam : 𝕜) := hxmem₀
  rw [eigenspace_basisDiagonal, OrthonormalBasis.mem_spanIndices_iff] at hxmem
  obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    exact hx0 (b.repr.injective (by ext i; simpa using hall i))
  have : (c i : 𝕜) = (lam : 𝕜) := by
    by_contra hne
    exact hi (hxmem i hne)
  have hci : c i = lam := by exact_mod_cast this
  exact hci ▸ hc i

/-- **The spectrum a block carries is read off the block's data.**  An
eigenvalue of a diagonal operator witnessed inside `b.spanIndices s` is the
coefficient at some index of `s`.

This is what turns a spectral-gap hypothesis into arithmetic on `c`. -/
theorem restrictedPointSpectrum_basisDiagonal_subset (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) (s : Set ι) :
    restrictedPointSpectrum (basisDiagonal b c) (b.spanIndices s) ⊆ c '' s := by
  classical
  intro lam hlam
  obtain ⟨x, hxs, hx0, hxeq⟩ := mem_restrictedPointSpectrum_iff.mp hlam
  -- `x` also lies in the eigenspace, which is the level set block.
  have hxlevel : x ∈ b.spanIndices {i | (c i : 𝕜) = (lam : 𝕜)} := by
    rw [← eigenspace_basisDiagonal]
    exact Module.End.mem_eigenspace_iff.mpr hxeq
  rw [OrthonormalBasis.mem_spanIndices_iff] at hxs hxlevel
  obtain ⟨i, hi⟩ : ∃ i, b.repr x i ≠ 0 := by
    by_contra hall
    simp only [not_exists, ne_eq, not_not] at hall
    exact hx0 (b.repr.injective (by ext i; simpa using hall i))
  refine ⟨i, by_contra fun hs => hi (hxs i hs), ?_⟩
  have : (c i : 𝕜) = (lam : 𝕜) := by_contra fun h => hi (hxlevel i h)
  exact_mod_cast this

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Mathlib's sorted eigenvalue list of a diagonal operator is bounded by any
bound on the data. -/
theorem eigenvalues_basisDiagonal_le {n : ℕ} (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) {M : ℝ} (hc : ∀ i, c i ≤ M) (hn : finrank 𝕜 E = n) (i : Fin n) :
    (isSymmetric_basisDiagonal b c).eigenvalues hn i ≤ M :=
  le_of_hasEigenvalue_basisDiagonal b c hc
    ((isSymmetric_basisDiagonal b c).hasEigenvalue_eigenvalues hn i)

/-- **Counting eigenvalues above a level is reading the data.**

Mathlib's sorted eigenvalue list of a diagonal operator is a rearrangement of
the coefficients, so the number of sorted eigenvalues exceeding `α` is the
number of coefficients exceeding `α`.  The proof avoids exhibiting the
rearrangement: both counts are the dimension of one subspace — the span of the
eigenvectors with eigenvalue above `α` — which the two orthonormal eigenbases
describe by their own index sets.

Together with `LinearMap.IsSymmetric.eigenvalues_level_eq_Ico` this locates any
eigenspace of a diagonal operator inside the sorted eigenbasis, which is what a
concrete example needs in order to produce a block-selection hypothesis for a
*middle* eigenvalue rather than only for the largest one. -/
theorem card_filter_lt_eigenvalues_basisDiagonal {n : ℕ}
    (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) (hn : finrank 𝕜 E = n) (α : ℝ) :
    ({i | α < (isSymmetric_basisDiagonal b c).eigenvalues hn i} :
        Finset (Fin n)).card =
      ({i | α < c i} : Finset ι).card := by
  classical
  have hsym := isSymmetric_basisDiagonal b c
  -- The two descriptions of the span of the eigenvectors above `α` agree.
  have hspan : (hsym.eigenvectorBasis hn).spanIndices
      {i : Fin n | α < hsym.eigenvalues hn i} = b.spanIndices {i : ι | α < c i} := by
    refine le_antisymm ?_ ?_
    · rw [OrthonormalBasis.spanIndices_eq_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, rfl⟩
      have hmem : hsym.eigenvectorBasis hn i ∈
          eigenspace (basisDiagonal b c) ((hsym.eigenvalues hn i : ℝ) : 𝕜) :=
        (hsym.hasEigenvector_eigenvectorBasis hn i).1
      rw [eigenspace_basisDiagonal] at hmem
      refine OrthonormalBasis.spanIndices_mono b (fun j hj => ?_) hmem
      have hcj : c j = hsym.eigenvalues hn i := by exact_mod_cast hj
      simp only [Set.mem_ofPred_eq] at hi ⊢
      exact hcj ▸ hi
    · rw [OrthonormalBasis.spanIndices_eq_span]
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨j, hj, rfl⟩
      have hmem : b j ∈ eigenspace (basisDiagonal b c) ((c j : ℝ) : 𝕜) := by
        rw [Module.End.mem_eigenspace_iff, basisDiagonal_apply_basis]
      rw [← hsym.spanIndices_eigenvalueLevel hn ((c j : ℝ) : 𝕜)] at hmem
      refine OrthonormalBasis.spanIndices_mono _ (fun i hi => ?_) hmem
      have hci : hsym.eigenvalues hn i = c j := by exact_mod_cast hi
      simp only [Set.mem_ofPred_eq] at hj ⊢
      exact hci ▸ hj
  have h1 := (hsym.eigenvectorBasis hn).finrank_spanIndices_set
    {i : Fin n | α < hsym.eigenvalues hn i}
  rw [hspan, b.finrank_spanIndices_set {i : ι | α < c i}] at h1
  simpa using h1.symm

open scoped Classical in
/-- **The sorted eigenvalue at a given index, by counting alone.**

`μ` occupies the sorted positions `[m, m + k)` where `m` is the number of
coefficients above `μ` and `k` the number equal to it, so any index in that range
carries eigenvalue `μ`.  This is the computational form of
`LinearMap.IsSymmetric.eigenvalues_level_eq_Ico` for a diagonal operator: it
identifies a specific entry of Mathlib's sorted list without exhibiting the
sorting permutation, which is what a concrete example needs in order to state an
ordered-eigenframe hypothesis. -/
theorem eigenvalues_basisDiagonal_eq_of_card {n : ℕ} (b : OrthonormalBasis ι 𝕜 E)
    (c : ι → ℝ) (hn : finrank 𝕜 E = n) (μ : ℝ) (i : Fin n)
    (hlo : ({j | μ < c j} : Finset ι).card ≤ (i : ℕ))
    (hhi : (i : ℕ) < ({j | μ < c j} : Finset ι).card
      + ({j | (c j : 𝕜) = ((μ : ℝ) : 𝕜)} : Finset ι).card) :
    (isSymmetric_basisDiagonal b c).eigenvalues hn i = μ := by
  classical
  have hsym := isSymmetric_basisDiagonal b c
  have hmem : i ∈ {k : Fin n | hsym.eigenvalues hn k = μ} := by
    rw [hsym.eigenvalues_level_eq_Ico hn μ]
    simp only [Set.mem_ofPred_eq]
    rw [card_filter_lt_eigenvalues_basisDiagonal b c hn μ,
      finrank_eigenspace_basisDiagonal b c ((μ : ℝ) : 𝕜)]
    exact ⟨hlo, hhi⟩
  simpa using hmem

open scoped Classical in
/-- **The sorted eigenvalues of a scalar operator are all equal to its scalar.**
The extreme degenerate case: `c • id` has one eigenvalue of full multiplicity, so
*every* orthonormal family is an ordered eigenframe for it. -/
theorem eigenvalues_basisDiagonal_const {n : ℕ} (b : OrthonormalBasis ι 𝕜 E)
    (c : ℝ) (hn : finrank 𝕜 E = n) (i : Fin n) :
    (isSymmetric_basisDiagonal b fun _ => c).eigenvalues hn i = c := by
  classical
  have hcard : Fintype.card ι = n := by
    rw [← hn, Module.finrank_eq_card_basis b.toBasis]
  have habove : ({j | c < (fun _ : ι => c) j} : Finset ι).card = 0 := by
    simp
  have hlevel : ({j | (((fun _ : ι => c) j : ℝ) : 𝕜) = ((c : ℝ) : 𝕜)} : Finset ι).card
      = Fintype.card ι := by
    simp
  refine eigenvalues_basisDiagonal_eq_of_card b _ hn c i (by rw [habove]; exact Nat.zero_le _) ?_
  rw [habove, hlevel, hcard, Nat.zero_add]
  exact i.isLt

end FiniteDimensional

/-- **Parseval bound.**  A diagonal operator moves no vector by more than the
sup of its data. -/
theorem norm_basisDiagonal_apply_le (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hc : ∀ i, |c i| ≤ M) (x : E) :
    ‖basisDiagonal b c x‖ ≤ M * ‖x‖ := by
  have hsq : ‖basisDiagonal b c x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [← b.sum_sq_norm_inner_right (basisDiagonal b c x), mul_pow,
      ← b.sum_sq_norm_inner_right x, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← b.repr_apply_apply, ← b.repr_apply_apply, repr_basisDiagonal, norm_mul,
      RCLike.norm_ofReal, mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (abs_nonneg _) (hc i) 2) (by positivity)
  nlinarith [norm_nonneg (basisDiagonal b c x), mul_nonneg hM (norm_nonneg x)]

section OperatorNorm

variable [FiniteDimensional 𝕜 E]

/-- The operator norm of a diagonal operator is at most any bound on its data. -/
theorem norm_basisDiagonal_le (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i, |c i| ≤ M) :
    ‖(basisDiagonal b c).toContinuousLinearMap‖ ≤ M :=
  ContinuousLinearMap.opNorm_le_bound _ hM fun x => by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using
      norm_basisDiagonal_apply_le b c hM hc x

/-- Every coefficient of a diagonal operator is a lower bound for its operator
norm: it is attained on the corresponding basis vector. -/
theorem le_norm_basisDiagonal (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) (i : ι) :
    |c i| ≤ ‖(basisDiagonal b c).toContinuousLinearMap‖ := by
  have h := (basisDiagonal b c).toContinuousLinearMap.le_opNorm (b i)
  rw [LinearMap.coe_toContinuousLinearMap', basisDiagonal_apply_basis, norm_smul,
    RCLike.norm_ofReal, b.orthonormal.norm_eq_one i, mul_one, mul_one] at h
  exact h

/-- **The operator norm of a diagonal operator is the largest coefficient in
absolute value**, when that value is attained at an index `i₀`. -/
theorem norm_basisDiagonal_eq (b : OrthonormalBasis ι 𝕜 E) (c : ι → ℝ) {M : ℝ}
    (hM : 0 ≤ M) (hc : ∀ i, |c i| ≤ M) {i₀ : ι} (hi₀ : |c i₀| = M) :
    ‖(basisDiagonal b c).toContinuousLinearMap‖ = M :=
  le_antisymm (norm_basisDiagonal_le b c hM hc) (hi₀ ▸ le_norm_basisDiagonal b c i₀)

end OperatorNorm

end TauCeti
