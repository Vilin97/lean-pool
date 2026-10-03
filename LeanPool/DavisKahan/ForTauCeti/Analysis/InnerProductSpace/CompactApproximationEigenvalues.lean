/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/

/-
Staged for Tau Ceti: the approximation numbers of a compact positive operator
determine its eigenspace dimensions.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.DFinsupp
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.CompactHilbert
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.CompactSelfAdjointClassification

/-!
# The approximation numbers of a compact positive operator are its eigenvalues

For a compact, positive, self-adjoint `A` on a real or complex Hilbert space the whole
eigenvalue list — values *and* multiplicities — is readable off the
approximation-number sequence `aₙ(A)`.  The precise statement proved here is the
threshold identity

```
μ ≤ aₙ(A)  ↔  n < dim (span of the eigenspaces with eigenvalue ≥ μ)      (μ > 0)
```

from which `#{n | aₙ(A) = μ} = dim ker(A - μ)` follows by subtracting the same
identity at the two thresholds `≥ μ` and `> μ`.

## The two halves

Write `eigenSpan A S` for the span of the eigenspaces whose eigenvalue lies in a
set `S ⊆ ℝ`.

* **Lower half.**  On `eigenSpan A (Set.Ici μ)` the operator is bounded below by
  `μ`: decompose a vector along the (mutually orthogonal) eigenspaces and use
  Pythagoras.  Min--max
  (`ContinuousLinearMap.le_approximationNumber_of_lt_rank`) turns that into
  `μ ≤ aₙ(A)` whenever the span has rank more than `n`.  Run backwards against
  `aₙ(A) → 0` it also *proves* the span is finite-dimensional, so no separate
  Riesz-type argument is needed.
* **Upper half.**  `W := eigenSpan A S` is `A`-invariant, hence so is `Wᗮ`, and
  the restriction of `A` to `Wᗮ` is again compact and self-adjoint.  If `S`
  contains every real `> c` then no eigenvalue of that restriction exceeds `c`;
  since the spectral radius of a self-adjoint operator is its norm and every
  nonzero spectral value of a compact operator is an eigenvalue, the restriction
  has norm at most `c`.  The competitor `A ∘L P_W` then gives `a_{dim W}(A) ≤ c`.

Positivity is what lets the second half quantify over eigenvalues `> c` rather
than `|·| > c`: a negative eigenvalue would escape a one-sided band.

## The gap step

Turning `≤ c` into `< μ` needs a `c` strictly below `μ` with no eigenvalue in
between.  That is available because the eigenvalues above any positive threshold
are finitely many — they are eigenvalues of `A` restricted to the
finite-dimensional `eigenSpan A (Set.Ici t)`, and an endomorphism of a
finite-dimensional space has finitely many eigenvalues.

## Main results

* `TauCeti.le_approximationNumber_iff_lt_finrank_eigenSpan_Ici`: the threshold
  identity.
* `TauCeti.finrank_eigenspace_eq_card_approximationNumber_eq`: the eigenspace
  dimension is the number of indices at which the approximation number equals
  the eigenvalue.
* `TauCeti.finrank_eigenspace_congr_of_approximationNumber_eq`: two compact
  positive self-adjoint operators with trivial kernel and the same approximation
  numbers have the same eigenspace dimensions — the hypothesis
  `TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`
  asks for.
* `TauCeti.exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq`:
  feeding the previous one to the classification, such an operator is determined
  up to unitary equivalence by its approximation-number sequence.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written directly in the Tau Ceti staging library
  against Mathlib's compact spectral theorem and this directory's
  approximation-number min--max layer.
* Spectra influence: **none** — the module imports only `Mathlib.*`, two
  `ForTauCeti` approximation-number leaves, and the compact self-adjoint
  classification.
-/

@[expose] public section

namespace TauCeti

open Module (finrank)
open Module.End (eigenspace)
open scoped InnerProductSpace NNReal ENNReal

noncomputable section

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! ## The span of a band of eigenspaces -/

/-- The span of the eigenspaces of `A` whose eigenvalue is a real number lying in
`S`.  Eigenvalues are indexed by *reals* rather than by scalars because for
a self-adjoint operator that is where they live, and because the bands used
below (`Set.Ici μ`, `Set.Ioi μ`) are intervals of `ℝ`. -/
def eigenSpan (A : E →L[𝕜] E) (S : Set ℝ) : Submodule 𝕜 E :=
  ⨆ s : S, eigenspace A.toLinearMap ((s : ℝ) : 𝕜)

/-- Each eigenspace named by the band sits inside the band's span. -/
theorem eigenspace_le_eigenSpan (A : E →L[𝕜] E) {S : Set ℝ} {s : ℝ} (hs : s ∈ S) :
    eigenspace A.toLinearMap (s : 𝕜) ≤ eigenSpan A S :=
  le_iSup (fun s : S => eigenspace A.toLinearMap ((s : ℝ) : 𝕜)) ⟨s, hs⟩

/-- The band span is determined by the eigenspaces it names, so any submodule
containing all of them contains it. -/
theorem eigenSpan_le (A : E →L[𝕜] E) {S : Set ℝ} {W : Submodule 𝕜 E}
    (h : ∀ s ∈ S, eigenspace A.toLinearMap (s : 𝕜) ≤ W) : eigenSpan A S ≤ W :=
  iSup_le fun s => h s s.2

/-- A larger band spans a larger subspace. -/
theorem eigenSpan_mono (A : E →L[𝕜] E) {S T : Set ℝ} (h : S ⊆ T) :
    eigenSpan A S ≤ eigenSpan A T :=
  eigenSpan_le A fun _ hs => eigenspace_le_eigenSpan A (h hs)

/-- The span of a union of bands is the join of the two spans. -/
theorem eigenSpan_union (A : E →L[𝕜] E) (S T : Set ℝ) :
    eigenSpan A (S ∪ T) = eigenSpan A S ⊔ eigenSpan A T := by
  refine le_antisymm (eigenSpan_le A fun s hs => ?_)
    (sup_le (eigenSpan_mono A Set.subset_union_left)
      (eigenSpan_mono A Set.subset_union_right))
  rcases hs with hs | hs
  · exact le_sup_of_le_left (eigenspace_le_eigenSpan A hs)
  · exact le_sup_of_le_right (eigenspace_le_eigenSpan A hs)

/-- A one-point band spans the single eigenspace it names. -/
theorem eigenSpan_singleton (A : E →L[𝕜] E) (μ : ℝ) :
    eigenSpan A {μ} = eigenspace A.toLinearMap (μ : 𝕜) := by
  refine le_antisymm (eigenSpan_le A fun s hs => ?_) (eigenspace_le_eigenSpan A rfl)
  rw [Set.mem_singleton_iff] at hs
  exact le_of_eq (by rw [hs])

/-- **A band span is invariant.**  Each eigenspace is, and the join of invariant
subspaces is invariant. -/
theorem eigenSpan_invariant (A : E →L[𝕜] E) (S : Set ℝ) :
    ∀ v ∈ eigenSpan A S, A v ∈ eigenSpan A S := by
  intro v hv
  have h : eigenSpan A S ≤ Submodule.comap A.toLinearMap (eigenSpan A S) := by
    refine eigenSpan_le A fun s hs w hw => ?_
    have hw' : A w = ((s : ℝ) : 𝕜) • w := Module.End.mem_eigenspace_iff.mp hw
    have hmem : A w ∈ eigenspace A.toLinearMap ((s : ℝ) : 𝕜) := by
      rw [hw']
      exact Submodule.smul_mem _ _ hw
    exact eigenspace_le_eigenSpan A hs hmem
  exact h hv

/-! ## Orthogonality, reality, and the lower bound -/

variable {A : E →L[𝕜] E} [CompleteSpace E]

/-- The eigenspaces of a self-adjoint operator, indexed by their real eigenvalue,
form an orthogonal family.  This is Mathlib's scalar-indexed family composed with
the injection `ℝ → 𝕜`. -/
theorem orthogonalFamily_eigenspace_real (hAs : IsSelfAdjoint A) :
    OrthogonalFamily 𝕜 (fun s : ℝ => (eigenspace A.toLinearMap (s : 𝕜) : Submodule 𝕜 E))
      (fun s => (eigenspace A.toLinearMap (s : 𝕜)).subtypeₗᵢ) :=
  ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    hAs).orthogonalFamily_eigenspaces).comp (RCLike.ofReal_injective (K := 𝕜))

/-- A band span is orthogonal to any eigenspace the band does not name. -/
theorem eigenSpan_isOrtho_eigenspace (hAs : IsSelfAdjoint A) {S : Set ℝ} {μ : ℝ}
    (hμ : μ ∉ S) : eigenSpan A S ⟂ eigenspace A.toLinearMap (μ : 𝕜) := by
  rw [Submodule.isOrtho_iff_le]
  refine eigenSpan_le A fun s hs => ?_
  rw [← Submodule.isOrtho_iff_le]
  refine Submodule.isOrtho_iff_inner_eq.mpr fun w hw z hz => ?_
  have hne : s ≠ μ := fun h => hμ (h ▸ hs)
  exact orthogonalFamily_eigenspace_real hAs hne ⟨w, hw⟩ ⟨z, hz⟩

/-- **An eigenvalue of a positive self-adjoint operator is a nonnegative real.**
Reality is Mathlib's `conj_eigenvalue_eq_self`; nonnegativity is
`eigenvalue_nonneg_of_nonneg` fed the positivity hypothesis, transported across
the conjugate symmetry of the inner product. -/
theorem eq_ofReal_re_of_eigenspace_ne_bot (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : 𝕜}
    (h : eigenspace A.toLinearMap μ ≠ ⊥) :
    μ = ((RCLike.re μ : ℝ) : 𝕜) ∧ 0 ≤ RCLike.re μ := by
  have hev : Module.End.HasEigenvalue A.toLinearMap μ := Module.End.hasEigenvalue_iff.mpr h
  have hconj :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAs).conj_eigenvalue_eq_self hev
  have hreal : μ = ((RCLike.re μ : ℝ) : 𝕜) := (RCLike.conj_eq_iff_re.mp hconj).symm
  refine ⟨hreal, ?_⟩
  have hev' : Module.End.HasEigenvalue A.toLinearMap ((RCLike.re μ : ℝ) : 𝕜) := by
    rw [← hreal]; exact hev
  refine eigenvalue_nonneg_of_nonneg hev' fun x => ?_
  simp only [ContinuousLinearMap.coe_coe]
  rw [inner_re_symm]
  exact hApos x

/-- **The band span is bounded below by the bottom of the band.**  Decompose a
vector of the span into its finitely many eigencomponents; the components are
mutually orthogonal, `A` scales the one at eigenvalue `s` by `s`, and every `s`
in play is at least `t`. -/
theorem le_norm_apply_of_mem_eigenSpan (hAs : IsSelfAdjoint A) {S : Set ℝ} {t : ℝ}
    (ht : 0 ≤ t) (hS : ∀ s ∈ S, t ≤ s) {x : E} (hx : x ∈ eigenSpan A S) :
    t * ‖x‖ ≤ ‖A x‖ := by
  classical
  have hfam :
      OrthogonalFamily 𝕜
        (fun s : S => (eigenspace A.toLinearMap ((s : ℝ) : 𝕜) : Submodule 𝕜 E))
        (fun s => (eigenspace A.toLinearMap ((s : ℝ) : 𝕜)).subtypeₗᵢ) :=
    (orthogonalFamily_eigenspace_real hAs).comp Subtype.val_injective
  rw [eigenSpan, Submodule.mem_iSup_iff_exists_dfinsupp'] at hx
  obtain ⟨f, hf⟩ := hx
  set u : Finset S := f.support with hu
  have hxsum : x = ∑ s ∈ u, ((f s : E)) := hf.symm
  have hxnorm : ‖x‖ ^ 2 = ∑ s ∈ u, ‖f s‖ ^ 2 := by
    rw [hxsum]
    simpa using hfam.norm_sum (fun s => f s) u
  have hAsum : A x = ∑ s ∈ u, ((((s : ℝ) : 𝕜) • f s : _) : E) := by
    rw [hxsum, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have hfs := Module.End.mem_eigenspace_iff.mp (f s).2
    simpa using hfs
  have hAnorm : ‖A x‖ ^ 2 = ∑ s ∈ u, ‖(((s : ℝ) : 𝕜) • f s : _)‖ ^ 2 := by
    rw [hAsum]
    simpa using hfam.norm_sum (fun s => (((s : ℝ) : 𝕜) • f s : _)) u
  have hkey : t ^ 2 * ‖x‖ ^ 2 ≤ ‖A x‖ ^ 2 := by
    rw [hxnorm, hAnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hts : t ≤ (s : ℝ) := hS s s.2
    have hnorm : ‖(((s : ℝ) : 𝕜) • f s : _)‖ = |(s : ℝ)| * ‖f s‖ := by
      rw [norm_smul, RCLike.norm_ofReal]
    rw [hnorm, mul_pow, sq_abs]
    have h1 : t ^ 2 ≤ (s : ℝ) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  have hsq : (t * ‖x‖) ^ 2 ≤ ‖A x‖ ^ 2 := by rw [mul_pow]; exact hkey
  exact (sq_le_sq₀ (mul_nonneg ht (norm_nonneg x)) (norm_nonneg _)).1 hsq

/-- **Min--max lower bound for a band.**  A band bounded below by `t` whose span
has rank more than `n` forces `t ≤ aₙ(A)`. -/
theorem le_approximationNumber_of_lt_rank_eigenSpan (hAs : IsSelfAdjoint A)
    {S : Set ℝ} {t : ℝ} (ht : 0 ≤ t) (hS : ∀ s ∈ S, t ≤ s) {n : ℕ}
    (hn : (n : Cardinal) < Module.rank 𝕜 (eigenSpan A S)) :
    t ≤ A.approximationNumber n :=
  ContinuousLinearMap.le_approximationNumber_of_lt_rank A n (eigenSpan A S) hn
    fun x => le_norm_apply_of_mem_eigenSpan hAs ht hS x.2

/-- **A band bounded away from `0` spans a finite-dimensional subspace.**  The
approximation numbers of a compact operator tend to `0`, so some `aₙ(A) < t`; by
the min--max bound the span cannot then have rank more than `n`. -/
theorem finiteDimensional_eigenSpan (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {S : Set ℝ} {t : ℝ} (ht : 0 < t) (hS : ∀ s ∈ S, t ≤ s) :
    FiniteDimensional 𝕜 (eigenSpan A S) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, A.approximationNumber n < t := by
    have h := A.tendsto_approximationNumber_atTop_nhds_zero_of_isCompactOperator hAc
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp h) t ht
    refine ⟨N, ?_⟩
    have hd := hN N le_rfl
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (A.approximationNumber_nonneg N)] at hd
  have hrank : Module.rank 𝕜 (eigenSpan A S) ≤ (n : Cardinal) := by
    by_contra hcon
    exact absurd (le_approximationNumber_of_lt_rank_eigenSpan hAs ht.le hS
      (lt_of_not_ge hcon)) (not_le.mpr hn)
  exact Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hrank (Cardinal.natCast_lt_aleph0))

/-- The dimension of a band span bounded below by `t` is at most any index at
which the approximation number has already dropped below `t`. -/
theorem finrank_eigenSpan_le (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {S : Set ℝ} {t : ℝ} (ht : 0 < t) (hS : ∀ s ∈ S, t ≤ s) {n : ℕ}
    (hn : A.approximationNumber n < t) : finrank 𝕜 (eigenSpan A S) ≤ n := by
  have := finiteDimensional_eigenSpan hAc hAs ht hS
  by_contra hcon
  refine absurd (le_approximationNumber_of_lt_rank_eigenSpan hAs ht.le hS ?_)
    (not_le.mpr hn)
  rw [← Module.finrank_eq_rank' 𝕜 (eigenSpan A S)]
  exact_mod_cast Nat.lt_of_not_ge hcon

/-! ## The compression to the orthogonal complement of an invariant subspace -/

/-- The orthogonal complement of an invariant subspace of a self-adjoint operator
is invariant. -/
theorem orthogonal_invariant_of_invariant (hAs : IsSelfAdjoint A) {W : Submodule 𝕜 E}
    (hW : ∀ v ∈ W, A v ∈ W) : ∀ v ∈ Wᗮ, A v ∈ Wᗮ := by
  intro v hv
  have hsymm := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAs
  refine (Submodule.mem_orthogonal _ _).mpr fun w hw => ?_
  have hAw : ⟪A w, v⟫_𝕜 = 0 := (Submodule.mem_orthogonal _ _).mp hv _ (hW w hw)
  have h := hsymm w v
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← h, hAw]

/-- **A one-sided eigenvalue bound off an invariant subspace bounds the
compression.**

The restriction of `A` to `Wᗮ` is compact and self-adjoint, so its norm is its
spectral radius; every nonzero point of the spectrum of a compact operator is an
eigenvalue, and an eigenvector of the restriction is an eigenvector of `A` lying
in `Wᗮ`.  So a bound on those eigenvalues is a bound on the compression. -/
theorem norm_comp_subtypeL_orthogonal_le (hAc : IsCompactOperator A)
    (hAs : IsSelfAdjoint A) {W : Submodule 𝕜 E} (hW : ∀ v ∈ W, A v ∈ W) {c : ℝ}
    (hc : 0 ≤ c)
    (hbd : ∀ (ν : 𝕜) (v : E), v ∈ Wᗮ → v ≠ 0 → A v = ν • v → ‖ν‖ ≤ c) :
    ‖A ∘L (Wᗮ).subtypeL‖ ≤ c := by
  obtain ⟨cn, rfl⟩ : ∃ cn : ℝ≥0, c = (cn : ℝ) := ⟨⟨c, hc⟩, rfl⟩
  have : CompleteSpace (Wᗮ : Submodule 𝕜 E) :=
    (Submodule.isClosed_orthogonal W).completeSpace_coe
  have hinvL : ∀ v ∈ (Wᗮ : Submodule 𝕜 E), A.toLinearMap v ∈ Wᗮ :=
    orthogonal_invariant_of_invariant hAs hW
  set S : (Wᗮ : Submodule 𝕜 E) →L[𝕜] (Wᗮ : Submodule 𝕜 E) := A.restrict hinvL with hSdef
  have hSsa : IsSelfAdjoint S :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hAs).restrict_invariant hinvL)
  have hAcl : IsCompactOperator A.toLinearMap := hAc
  have hSc : IsCompactOperator S := hAcl.restrict' hinvL
  have hnorm : ‖S‖ ≤ (cn : ℝ) := by
    have hsr : spectralRadius 𝕜 S = ‖S‖₊ := S.spectralRadius_eq_nnnorm hSsa
    have hle : (‖S‖₊ : ℝ≥0∞) ≤ (cn : ℝ≥0∞) := by
      rw [← hsr]
      simp only [spectralRadius_eq_of_unital]
      refine iSup₂_le fun k hk => ?_
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · have hev : Module.End.HasEigenvalue (S : Module.End 𝕜 (Wᗮ : Submodule 𝕜 E)) k :=
          (hSc.hasEigenvalue_iff_mem_spectrum hk0).mpr hk
        obtain ⟨y, hy, hy0⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (Module.End.hasEigenvalue_iff.mp hev)
        have hyeq : A (y : E) = k • (y : E) := by
          have hme := Module.End.mem_eigenspace_iff.mp hy
          simpa [hSdef] using congrArg (fun z : (Wᗮ : Submodule 𝕜 E) => (z : E)) hme
        have hkc : ‖k‖ ≤ (cn : ℝ) := by
          refine hbd k (y : E) y.2 ?_ hyeq
          simpa [Submodule.coe_eq_zero] using hy0
        exact_mod_cast hkc
    have hnn : ‖S‖₊ ≤ cn := by exact_mod_cast hle
    exact_mod_cast hnn
  refine le_trans (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun x => ?_) hnorm
  have hval : ‖(A ∘L (Wᗮ).subtypeL) x‖ = ‖S x‖ := rfl
  rw [hval]
  exact S.le_opNorm x

/-! ## The upper half of the threshold identity -/

/-- **A band that captures every eigenvalue above `c` bounds the approximation
number at its own dimension.**

The compression of `A` to the orthogonal complement of the band span has no
eigenvalue above `c`: an eigenvector for such an eigenvalue would lie in the band
span and in its complement at once.  Positivity is what rules out an eigenvalue
*below* `-c`, which the one-sided hypothesis `hcover` does not see. -/
theorem approximationNumber_le_of_eigenSpan_cover (hAc : IsCompactOperator A)
    (hAs : IsSelfAdjoint A) (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {S : Set ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hcover : ∀ s : ℝ, c < s → s ∈ S)
    [FiniteDimensional 𝕜 (eigenSpan A S)] {n : ℕ} (hn : finrank 𝕜 (eigenSpan A S) ≤ n) :
    A.approximationNumber n ≤ c := by
  set W : Submodule 𝕜 E := eigenSpan A S with hWdef
  have hinv : ∀ v ∈ W, A v ∈ W := eigenSpan_invariant A S
  have : CompleteSpace (W : Submodule 𝕜 E) := FiniteDimensional.complete 𝕜 W
  have hbd : ∀ (ν : 𝕜) (v : E), v ∈ Wᗮ → v ≠ 0 → A v = ν • v → ‖ν‖ ≤ c := by
    intro ν v hvmem hv0 hveq
    have hvE : v ∈ eigenspace A.toLinearMap ν := Module.End.mem_eigenspace_iff.mpr hveq
    have hEne : eigenspace A.toLinearMap ν ≠ ⊥ := by
      intro hbot
      exact hv0 (by simpa [hbot] using hvE)
    obtain ⟨hreal, hnonneg⟩ := eq_ofReal_re_of_eigenspace_ne_bot hAs hApos hEne
    have hvE' : v ∈ eigenspace A.toLinearMap ((RCLike.re ν : ℝ) : 𝕜) := by rwa [← hreal]
    have hle : RCLike.re ν ≤ c := by
      by_contra hcon
      have hmem : RCLike.re ν ∈ S := hcover _ (lt_of_not_ge hcon)
      have hvW : v ∈ W := eigenspace_le_eigenSpan A hmem hvE'
      have hinter : v ∈ W ⊓ Wᗮ := ⟨hvW, hvmem⟩
      rw [(Submodule.orthogonal_disjoint W).eq_bot, Submodule.mem_bot] at hinter
      exact hv0 hinter
    have hnormν : ‖ν‖ = |RCLike.re ν| := by
      conv_lhs => rw [hreal]
      exact RCLike.norm_ofReal _
    rw [hnormν, abs_of_nonneg hnonneg]
    exact hle
  calc A.approximationNumber n
      ≤ ‖A ∘L (Wᗮ).starProjection‖ :=
        A.approximationNumber_le_norm_comp_starProjection_orthogonal n W hn
    _ = ‖A ∘L (Wᗮ).subtypeL‖ := A.norm_comp_starProjection_orthogonal_eq_norm_comp_subtypeL W
    _ ≤ c := norm_comp_subtypeL_orthogonal_le hAc hAs hinv hc hbd

/-! ## Discreteness of the eigenvalues above a positive threshold -/

/-- **Only finitely many eigenvalues sit above a positive threshold.**  They are
all eigenvalues of `A` restricted to the finite-dimensional
`eigenSpan A (Set.Ici t)`, and an endomorphism of a finite-dimensional space has
finitely many eigenvalues. -/
theorem finite_eigenvalues_ge (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {t : ℝ} (ht : 0 < t) :
    {s : ℝ | t ≤ s ∧ eigenspace A.toLinearMap (s : 𝕜) ≠ ⊥}.Finite := by
  set W : Submodule 𝕜 E := eigenSpan A (Set.Ici t) with hWdef
  have : FiniteDimensional 𝕜 W :=
    finiteDimensional_eigenSpan hAc hAs ht fun s hs => hs
  have hinv : ∀ v ∈ W, A v ∈ W := eigenSpan_invariant A _
  set B : Module.End 𝕜 W := A.toLinearMap.restrict hinv with hBdef
  have hfin : Set.Finite (Set.ofPred B.HasEigenvalue) := Module.End.finite_hasEigenvalue B
  refine Set.Finite.subset (hfin.preimage (f := fun s : ℝ => (s : 𝕜))
    (RCLike.ofReal_injective (K := 𝕜)).injOn) ?_
  rintro s ⟨hts, hne⟩
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hvW : v ∈ W := eigenspace_le_eigenSpan A hts hv
  have hmem : (⟨v, hvW⟩ : W) ∈ eigenspace B ((s : ℝ) : 𝕜) := by
    refine Module.End.mem_eigenspace_iff.mpr (Subtype.ext ?_)
    have hme := Module.End.mem_eigenspace_iff.mp hv
    simpa [hBdef, LinearMap.restrict_apply] using hme
  refine Module.End.hasEigenvalue_iff.mpr fun hbot => hv0 ?_
  rw [hbot, Submodule.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

/-- A finite set of reals leaves a gap immediately below any point: there is a
`ρ` in `[a, b)` such that no element of the set lies in `(ρ, b)`. -/
theorem exists_gap_below {Λ : Set ℝ} (hΛ : Λ.Finite) {a b : ℝ} (hab : a < b) :
    ∃ ρ : ℝ, a ≤ ρ ∧ ρ < b ∧ ∀ s ∈ Λ, ρ < s → b ≤ s := by
  classical
  set T : Finset ℝ := hΛ.toFinset.filter (fun s => a ≤ s ∧ s < b) with hT
  by_cases hTe : T.Nonempty
  · refine ⟨T.max' hTe, ((Finset.mem_filter.mp (T.max'_mem hTe)).2).1,
      ((Finset.mem_filter.mp (T.max'_mem hTe)).2).2, fun s hs hlt => ?_⟩
    by_contra hcon
    have hmem : s ∈ T :=
      Finset.mem_filter.mpr ⟨hΛ.mem_toFinset.mpr hs,
        le_trans ((Finset.mem_filter.mp (T.max'_mem hTe)).2).1 hlt.le,
        lt_of_not_ge hcon⟩
    exact absurd (T.le_max' s hmem) (not_le.mpr hlt)
  · refine ⟨a, le_rfl, hab, fun s hs hlt => ?_⟩
    by_contra hcon
    exact hTe ⟨s, Finset.mem_filter.mpr
      ⟨hΛ.mem_toFinset.mpr hs, hlt.le, lt_of_not_ge hcon⟩⟩

/-- A finite set of reals leaves a gap immediately above any point: there is a
`ν > a` such that no element of the set lies in `(a, ν)`. -/
theorem exists_gap_above {Λ : Set ℝ} (hΛ : Λ.Finite) (a : ℝ) :
    ∃ ν : ℝ, a < ν ∧ ∀ s ∈ Λ, a < s → ν ≤ s := by
  classical
  set T : Finset ℝ := hΛ.toFinset.filter (fun s => a < s) with hT
  by_cases hTe : T.Nonempty
  · refine ⟨T.min' hTe, (Finset.mem_filter.mp (T.min'_mem hTe)).2, fun s hs hlt => ?_⟩
    exact T.min'_le s (Finset.mem_filter.mpr ⟨hΛ.mem_toFinset.mpr hs, hlt⟩)
  · refine ⟨a + 1, by linarith, fun s hs hlt => ?_⟩
    exact absurd ⟨s, Finset.mem_filter.mpr ⟨hΛ.mem_toFinset.mpr hs, hlt⟩⟩ hTe

/-- **A closed band is an open band slightly lower down.**  Between `ρ` and `μ`
there is no eigenvalue, so the two spans agree. -/
theorem exists_eigenSpan_Ioi_eq_Ici (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < μ ∧ eigenSpan A (Set.Ioi ρ) = eigenSpan A (Set.Ici μ) := by
  obtain ⟨ρ, hρa, hρb, hρ⟩ :=
    exists_gap_below (finite_eigenvalues_ge hAc hAs (t := μ / 2) (by linarith))
      (a := μ / 2) (b := μ) (by linarith)
  refine ⟨ρ, by linarith, hρb, le_antisymm (eigenSpan_le A fun s hs => ?_)
    (eigenSpan_mono A fun s hs => lt_of_lt_of_le hρb hs)⟩
  by_cases hbot : eigenspace A.toLinearMap (s : 𝕜) = ⊥
  · rw [hbot]; exact bot_le
  · have hs2 : μ / 2 ≤ s := le_trans hρa hs.le
    exact eigenspace_le_eigenSpan A (hρ s ⟨hs2, hbot⟩ hs)

/-- **An open band is a closed band slightly higher up.**  Between `μ` and `ν`
there is no eigenvalue, so the two spans agree. -/
theorem exists_eigenSpan_Ici_eq_Ioi (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {μ : ℝ} (hμ : 0 < μ) :
    ∃ ν : ℝ, μ < ν ∧ eigenSpan A (Set.Ici ν) = eigenSpan A (Set.Ioi μ) := by
  obtain ⟨ν, hν, hgap⟩ := exists_gap_above (finite_eigenvalues_ge hAc hAs hμ) μ
  refine ⟨ν, hν, le_antisymm (eigenSpan_mono A fun s hs => lt_of_lt_of_le hν hs)
    (eigenSpan_le A fun s hs => ?_)⟩
  by_cases hbot : eigenspace A.toLinearMap (s : 𝕜) = ⊥
  · rw [hbot]; exact bot_le
  · exact eigenspace_le_eigenSpan A (hgap s ⟨hs.le, hbot⟩ hs)

/-! ## The threshold identity -/

/-- **The approximation numbers count the eigenvalue multiplicities.**

`μ ≤ aₙ(A)` exactly when the eigenspaces with eigenvalue at least `μ` span more
than `n` dimensions.  Both halves are min--max: the forward one uses that a band
capturing everything above a threshold slightly below `μ` gives an admissible
rank-`dim` approximation. -/
theorem le_approximationNumber_iff_lt_finrank_eigenSpan_Ici (hAc : IsCompactOperator A)
    (hAs : IsSelfAdjoint A) (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ)
    (n : ℕ) :
    μ ≤ A.approximationNumber n ↔ n < finrank 𝕜 (eigenSpan A (Set.Ici μ)) := by
  have hfd : FiniteDimensional 𝕜 (eigenSpan A (Set.Ici μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => hs
  constructor
  · intro hle
    by_contra hcon
    obtain ⟨ρ, hρ0, hρμ, hρeq⟩ := exists_eigenSpan_Ioi_eq_Ici hAc hAs hμ
    have : FiniteDimensional 𝕜 (eigenSpan A (Set.Ioi ρ)) := by rw [hρeq]; infer_instance
    have hdim : finrank 𝕜 (eigenSpan A (Set.Ioi ρ)) ≤ n := by
      rw [hρeq]; exact Nat.le_of_not_lt hcon
    have hbound := approximationNumber_le_of_eigenSpan_cover hAc hAs hApos hρ0.le
      (S := Set.Ioi ρ) (fun s hs => hs) hdim
    linarith
  · intro hlt
    refine le_approximationNumber_of_lt_rank_eigenSpan hAs hμ.le (S := Set.Ici μ)
      (fun s hs => hs) ?_
    rw [← Module.finrank_eq_rank' 𝕜 (eigenSpan A (Set.Ici μ))]
    exact_mod_cast hlt

/-- The strict form of the threshold identity, on the open band. -/
theorem lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi (hAc : IsCompactOperator A)
    (hAs : IsSelfAdjoint A) (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ)
    (n : ℕ) :
    μ < A.approximationNumber n ↔ n < finrank 𝕜 (eigenSpan A (Set.Ioi μ)) := by
  obtain ⟨ν, hν, hνeq⟩ := exists_eigenSpan_Ici_eq_Ioi hAc hAs hμ
  have hν0 : 0 < ν := lt_trans hμ hν
  have : FiniteDimensional 𝕜 (eigenSpan A (Set.Ioi μ)) := by
    rw [← hνeq]
    exact finiteDimensional_eigenSpan hAc hAs hν0 fun s hs => hs
  constructor
  · intro hlt
    have hpos : 0 < A.approximationNumber n := lt_trans hμ hlt
    have h1 := (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hpos
      n).mp le_rfl
    have hmono : eigenSpan A (Set.Ici (A.approximationNumber n)) ≤ eigenSpan A (Set.Ioi μ) :=
      eigenSpan_mono A fun s hs => lt_of_lt_of_le hlt hs
    exact lt_of_lt_of_le h1 (Submodule.finrank_mono hmono)
  · intro hlt
    rw [← hνeq] at hlt
    exact lt_of_lt_of_le hν
      ((le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hν0 n).mpr hlt)

/-! ## Counting -/

/-- The closed band splits off the eigenspace at its endpoint, orthogonally. -/
theorem finrank_eigenSpan_Ici (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    {μ : ℝ} (hμ : 0 < μ) :
    finrank 𝕜 (eigenSpan A (Set.Ici μ)) =
      finrank 𝕜 (eigenSpan A (Set.Ioi μ)) +
        finrank 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) := by
  have hfIci : FiniteDimensional 𝕜 (eigenSpan A (Set.Ici μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => hs
  have hfIoi : FiniteDimensional 𝕜 (eigenSpan A (Set.Ioi μ)) :=
    finiteDimensional_eigenSpan hAc hAs hμ fun s hs => le_of_lt hs
  have hfe : FiniteDimensional 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) :=
    Submodule.finiteDimensional_of_le
      (eigenspace_le_eigenSpan A (Set.mem_Ici.mpr (le_refl μ)))
  have hsplit : eigenSpan A (Set.Ici μ) =
      eigenSpan A (Set.Ioi μ) ⊔ eigenspace A.toLinearMap (μ : 𝕜) := by
    rw [← eigenSpan_singleton A μ, ← eigenSpan_union, Set.Ioi_union_left]
  have hdisj : Disjoint (eigenSpan A (Set.Ioi μ)) (eigenspace A.toLinearMap (μ : 𝕜)) :=
    (eigenSpan_isOrtho_eigenspace hAs (S := Set.Ioi μ) (μ := μ) (by simp)).disjoint
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (eigenSpan A (Set.Ioi μ))
    (eigenspace A.toLinearMap (μ : 𝕜))
  rw [hdisj.eq_bot, finrank_bot, add_zero] at hsum
  rw [hsplit, hsum]

/-- **The eigenspace dimension is the number of indices at which the
approximation number equals the eigenvalue.**

This is the missing bridge.  With the two threshold identities the index set is
the half-open interval between the dimensions of the open and the closed band,
and the eigenspace is exactly the difference between them.

No hypothesis on the kernel is needed here: for `μ > 0` the identity holds for
any compact positive self-adjoint operator.  It is the *consequence* below,
which must also cover `μ = 0`, that needs a trivial kernel. -/
theorem finrank_eigenspace_eq_card_approximationNumber_eq (hAc : IsCompactOperator A)
    (hAs : IsSelfAdjoint A) (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) {μ : ℝ} (hμ : 0 < μ) :
    finrank 𝕜 (eigenspace A.toLinearMap (μ : 𝕜)) =
      Nat.card {n : ℕ // A.approximationNumber n = μ} := by
  classical
  set N : ℕ := finrank 𝕜 (eigenSpan A (Set.Ici μ)) with hN
  set M : ℕ := finrank 𝕜 (eigenSpan A (Set.Ioi μ)) with hM
  have hset : {n : ℕ | A.approximationNumber n = μ} = Set.Ico M N := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_Ico]
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · by_contra hcon
        have hstrict := (lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hμ
          n).mpr (Nat.lt_of_not_ge hcon)
        rw [h] at hstrict
        exact lt_irrefl _ hstrict
      · exact (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hμ
          n).mp (le_of_eq h.symm)
    · rintro ⟨h1, h2⟩
      have hge : μ ≤ A.approximationNumber n :=
        (le_approximationNumber_iff_lt_finrank_eigenSpan_Ici hAc hAs hApos hμ n).mpr h2
      have hle : ¬ μ < A.approximationNumber n := fun hcon =>
        absurd ((lt_approximationNumber_iff_lt_finrank_eigenSpan_Ioi hAc hAs hApos hμ
          n).mp hcon) (Nat.not_lt.mpr h1)
      exact le_antisymm (not_lt.mp hle) hge
  have hcard : Nat.card {n : ℕ // A.approximationNumber n = μ} = N - M := by
    have hcongr : Nat.card {n : ℕ // A.approximationNumber n = μ} =
        Nat.card (Set.Ico M N : Set ℕ) := Nat.card_congr (Set.equivOfEq hset)
    rw [hcongr, Nat.card_eq_fintype_card, Fintype.card_Ico, Nat.card_Ico]
  rw [hcard, hN, hM, finrank_eigenSpan_Ici hAc hAs hμ]
  omega

/-! ## The consequence -/

/-- If `μ` is not a positive real then a compact positive self-adjoint operator
with trivial kernel has trivial `μ`-eigenspace. -/
theorem eigenspace_eq_bot_of_not_pos (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜) (hA0 : eigenspace A.toLinearMap 0 = ⊥)
    {μ : 𝕜} (hμ : ¬ ∃ r : ℝ, 0 < r ∧ μ = (r : 𝕜)) :
    eigenspace A.toLinearMap μ = ⊥ := by
  by_contra hne
  obtain ⟨hreal, hnonneg⟩ := eq_ofReal_re_of_eigenspace_ne_bot hAs hApos hne
  rcases eq_or_lt_of_le hnonneg with hz | hlt
  · refine hne ?_
    have hzero : μ = 0 := by rw [hreal, ← hz, RCLike.ofReal_zero]
    rw [hzero]
    exact hA0
  · exact hμ ⟨RCLike.re μ, hlt, hreal⟩

variable {F : Type v} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Equal approximation numbers force equal eigenspace dimensions.**

This is the hypothesis
`TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq` asks
for, so the two together classify a compact positive self-adjoint operator with
trivial kernel by its approximation-number sequence.

The trivial-kernel hypotheses are *essential*, and not only as bookkeeping at
`μ = 0`: without them one may pad either side with an arbitrary kernel, which
changes no approximation number while changing `dim ker A` freely.  With them,
`μ = 0` is the one place the hypothesis is used — a self-adjoint operator has
real eigenvalues and a positive one has nonnegative eigenvalues, so every other
non-positive-real `μ` already has both eigenspaces trivial. -/
theorem finrank_eigenspace_congr_of_approximationNumber_eq {B : F →L[𝕜] F}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hA0 : eigenspace A.toLinearMap 0 = ⊥)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (hBpos : ∀ x, 0 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hB0 : eigenspace B.toLinearMap 0 = ⊥)
    (hAB : ∀ n, A.approximationNumber n = B.approximationNumber n) (μ : 𝕜) :
    finrank 𝕜 (eigenspace A.toLinearMap μ) = finrank 𝕜 (eigenspace B.toLinearMap μ) := by
  by_cases hpos : ∃ r : ℝ, 0 < r ∧ μ = (r : 𝕜)
  · obtain ⟨r, hr, rfl⟩ := hpos
    rw [finrank_eigenspace_eq_card_approximationNumber_eq hAc hAs hApos hr,
      finrank_eigenspace_eq_card_approximationNumber_eq hBc hBs hBpos hr]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun n => by rw [hAB n])
  · rw [eigenspace_eq_bot_of_not_pos hAs hApos hA0 hpos,
      eigenspace_eq_bot_of_not_pos hBs hBpos hB0 hpos]
    rw [finrank_bot, finrank_bot]

/-- **A compact positive self-adjoint operator with trivial kernel is determined,
up to unitary equivalence, by its approximation numbers.**

This is the capstone the Davis--Kahan corollary consumes: the previous theorem
supplies the eigenspace-dimension hypothesis of
`TauCeti.exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq`, and
nothing else about the two operators is needed. -/
theorem exists_linearIsometryEquiv_intertwining_of_approximationNumber_eq {B : F →L[𝕜] F}
    (hAc : IsCompactOperator A) (hAs : IsSelfAdjoint A)
    (hApos : ∀ x, 0 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hA0 : eigenspace A.toLinearMap 0 = ⊥)
    (hBc : IsCompactOperator B) (hBs : IsSelfAdjoint B)
    (hBpos : ∀ x, 0 ≤ RCLike.re ⟪B x, x⟫_𝕜)
    (hB0 : eigenspace B.toLinearMap 0 = ⊥)
    (hAB : ∀ n, A.approximationNumber n = B.approximationNumber n) :
    ∃ W : E ≃ₗᵢ[𝕜] F, ∀ x, W (A x) = B (W x) :=
  exists_linearIsometryEquiv_intertwining_of_finrank_eigenspace_eq hAc hAs hBc hBs hA0 hB0
    (finrank_eigenspace_congr_of_approximationNumber_eq hAc hAs hApos hA0 hBc hBs hBpos hB0
      hAB)

end

end TauCeti
