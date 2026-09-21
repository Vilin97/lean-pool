/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Hilbert
import LeanPool.SNumbers.SNumbers.Uniqueness
import LeanPool.SNumbers.SNumbers.Bernstein
import LeanPool.SNumbers.SNumbers.Gelfand
import LeanPool.SNumbers.SNumbers.Kolmogorov
import LeanPool.SNumbers.SNumbers.SingularValuesFinDim
import LeanPool.SNumbers.BasicResults.Determinant
import LeanPool.SNumbers.BasicResults.GarlingGordon
import LeanPool.SNumbers.BasicResults.KadetsSnobar
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Comparison of `s`-number sequences (general spaces)

Pietsch's classical extremality result: among all `s`-number sequences, the
**Hilbert numbers** `hₙ` are the smallest and the **approximation numbers**
`aₙ` are the largest. This file collects the comparison statements that hold
for operators between **arbitrary** `𝕜`-Banach spaces.

## Main results

* `hilbertNumber_le_sn` — lower bound `hₙ(S) ≤ sₙ(S)`.
* `hilbertNumber_le_sn_le_approximationNumber` — the sandwich theorem
  `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`.
* `bernsteinNumber_le_gelfandNumber` — the direct bound `bₙ(S) ≤ cₙ(S)`
  (constant `1`), via the extremality of the Bernstein numbers among
  injective strict `s`-number sequences.
* `gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert` — the reverse bound
  `cₙ(S) ≤ √(n+1)·bₙ(S)` for a Hilbert codomain.
* `approximationNumber_le_sqrt_mul_gelfandNumber` —
  `aₙ(S) ≤ (1 + √n)·cₙ(S)`.
* `approximationNumber_le_sqrt_mul_kolmogorovNumber` —
  `aₙ(S) ≤ (1 + √n)·dₙ(S)`.
* `approximationNumber_le_sqrt_mul_min` — the combined bound
  `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))` (Pietsch [Pie87, 2.10.2]).
* Ingredients for the **maximal difference theorem**
  `aₙ(S) ≤ e·(n+1)·hₙ(S)` (proved in `SNumbers.MaxDifference` via the
  determinant quantities `Δₖ`): the identity `∏ aₖ(T) = ‖det T‖`
  (`prod_approximationNumber_eq_norm_det`) and the (S3)-type bound
  `aₖ(B∘S∘A) ≤ ‖B‖·‖A‖·hₖ(S)`.
* Point selection below the Gelfand / Kolmogorov numbers
  (`exists_mem_norm_gt_of_lt_gelfandNumber` /
  `exists_norm_mkQL_gt_of_lt_kolmogorovNumber`): from `c < cₙ(S)` (resp.
  `c < dₙ(S)`), a unit vector on which `S` retains norm `> c` on a given
  closed subspace of codimension `≤ n` (resp. modulo a given subspace of
  dimension `≤ n`).

## The `aₙ` vs `cₙ`, `dₙ` bound and its two projection inputs

The bound `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))` says that the *largest*
`s`-number `aₙ` cannot exceed the Gelfand / Kolmogorov numbers by more
than a factor `1 + √n`. Each half is proved by turning a near-optimal
subspace into a finite-rank approximant `L`, using a bounded projection:

* **Gelfand half** (`aₙ ≤ (1+√n)·cₙ`): pick a closed `M ⊆ X` of
  codimension `≤ n` with `‖S|_M‖` near `cₙ(S)`; the **Garling–Gordon**
  theorem supplies, for every `ε > 0`, a projection `P` with kernel `M` and
  `‖P‖ ≤ √n + ε`. Then `L := S ∘ P` has rank `≤ n` and `S - L = S ∘ (id − P)`
  has range inside `M`, so `‖S − L‖ ≤ ‖S|_M‖·‖id − P‖ ≤ (1 + √n + ε)·‖S|_M‖`,
  and `ε → 0` gives the factor `1 + √n`.
* **Kolmogorov half** (`aₙ ≤ (1+√n)·dₙ`): pick `V ⊆ Y` of dimension
  `≤ n` with `‖π_V ∘ S‖` near `dₙ(S)`; the **Kadets–Snobar** theorem
  supplies a projection `P` onto `V` with `‖P‖ ≤ √n`. Then `L := P ∘ S`
  has rank `≤ n` and `S − L = (id − P) ∘ S`, where `id − P` factors
  through the quotient `Y ⧸ V`, so
  `‖S − L‖ ≤ ‖id − P‖·‖π_V ∘ S‖ ≤ (1 + √n)·‖π_V ∘ S‖`.

The two projection theorems are deep results of Banach-space geometry, and come
from `BasicResults.GarlingGordon` (`exists_projection_ker_eq_of_codim_le`) and
`BasicResults.KadetsSnobar` (`exists_projection_range_eq_of_rank_le`), both
resting on John's ellipsoid theorem in `BasicResults.John`.

## Proof strategy for `hₙ ≤ sₙ`

Each ratio `aₙ(B ∘ S ∘ A)/(‖B‖‖A‖)` defining `hₙ(S)` has `B ∘ S ∘ A` an
operator **between Hilbert spaces** (`ℓ₂ → ℓ₂`), so the coincidence gives
`aₙ(B ∘ S ∘ A) ≤ sₙ(B ∘ S ∘ A)`; the (S3) ideal property then bounds this by
`‖B‖ · sₙ(S) · ‖A‖`. Dividing by `‖B‖‖A‖` and taking the supremum over the
admissible `(A, B)` yields `hₙ(S) ≤ sₙ(S)`.

## References

* D. Krieg, E. Novak, M. Ullrich, *On the power of adaption and randomization*,
  Forum of Mathematics, Sigma **13** (2025), e152,
  [doi](https://doi.org/10.1017/fms.2025.10101),
  [arxiv](https://arxiv.org/abs/2406.07108) ([KNU25]); the
  `cₙ ≤ √(n+1)·bₙ` bound is Theorem 8 there.
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Studies in Advanced
  Mathematics 13, Cambridge University Press, 1987,
  [link](https://zbmath.org/3996455) ([Pie87]); the projection theorems are
  1.7.17 (Garling–Gordon) and 1.5.5 (Kadets–Snobar).
* M. Ullrich, *Inequalities between s-numbers*, Advances in Operator
  Theory **9** (2024), no. 4, article no. 82,
  [doi](https://doi.org/10.1007/s43036-024-00386-x),
  [arxiv](https://arxiv.org/abs/2405.05509). The `aₙ ≤ (1+√n)·min(cₙ,dₙ)`
  bound is from here.
-/

universe u

open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **Lower bound.** The Hilbert numbers are the smallest `s`-number
sequence: `hₙ(S) ≤ sₙ(S)` for every `s`-number sequence `s`. -/
theorem hilbertNumber_le_sn {s : Family 𝕜} (hs : IsSNumberSequence s)
    (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (hs.nonneg S n)
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  -- `B ∘ S ∘ A : ℓ₂ → ℓ₂` is between Hilbert spaces, so `aₙ = sₙ` on it.
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ s (B.comp (S.comp A)) n := approximationNumber_le_sn hs (B.comp (S.comp A)) n
    _ ≤ ‖B‖ * s S n * ‖A‖ := hs.ideal A S B n
    _ = s S n * (‖B‖ * ‖A‖) := by ring

/-- **Sandwich theorem.** For every `s`-number sequence `s` and
every bounded operator `S : X → Y`: `hₙ(S) ≤ sₙ(S) ≤ aₙ(S)`. -/
theorem hilbertNumber_le_sn_le_approximationNumber {s : Family 𝕜}
    (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ s S n ∧ s S n ≤ approximationNumber S n :=
  ⟨hilbertNumber_le_sn hs S n, sn_le_approximationNumber hs S n⟩

/-- **Direct bound: Bernstein ≤ Gelfand**, `bₙ(S) ≤ cₙ(S)`.

A sharp, direct bound, with constant `1`. It follows at once from the
extremality of the Bernstein numbers among injective strict `s`-number sequences
(`bernsteinNumber_le_of_injective_strict`), since the Gelfand numbers are both
injective (`injective_gelfandNumber`) and a strict `s`-number sequence
(`isStrictSNumberSequence_gelfandNumber`). -/
theorem bernsteinNumber_le_gelfandNumber (S : X →L[𝕜] Y) (n : ℕ) :
    bernsteinNumber S n ≤ gelfandNumber S n :=
  bernsteinNumber_le_of_injective_strict
    isStrictSNumberSequence_gelfandNumber injective_gelfandNumber S n

/-! ## Reverse bound (Hilbert codomain): `cₙ ≤ √(n+1)·bₙ`

The reverse of `bₙ ≤ cₙ`, when the codomain is a Hilbert space:
`cₙ(S) ≤ √(n+1)·bₙ(S)` (Theorem 8 of [KNU25]). From
`γ < cₙ(S)`, every closed subspace of codimension `≤ n` carries a unit vector
that `S` stretches by more than `γ`; assembling `n+1` of these in nested kernels
makes their images orthonormal, so `S` is bounded below on their span. -/

/-- The common kernel `{x | ∀ i, gᵢ(S x) = 0}` of `k` continuous functionals `gᵢ ∘ S` is a
closed subspace of codimension `≤ k` (kernel of `x ↦ (gᵢ(S x))ᵢ : X → 𝕜ᵏ`). Used by the
oracles in `SNumbers.MaxDifference`. -/
lemma exists_closed_codim_forall_eq_zero (S : X →L[𝕜] Y) {k : ℕ}
    (g : Fin k → (Y →L[𝕜] 𝕜)) :
    ∃ M : Submodule 𝕜 X, IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal) ∧ (∀ x ∈ M, ∀ i, g i (S x) = 0) := by
  set Φ : X →L[𝕜] (Fin k → 𝕜) := ContinuousLinearMap.pi (fun i => (g i).comp S) with hΦ
  refine ⟨LinearMap.ker (Φ : X →ₗ[𝕜] (Fin k → 𝕜)), Φ.isClosed_ker, ?_, ?_⟩
  · rw [(LinearMap.quotKerEquivRange (Φ : X →ₗ[𝕜] (Fin k → 𝕜))).rank_eq]
    calc Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin k → 𝕜)))
        ≤ Module.rank 𝕜 (Fin k → 𝕜) := Submodule.rank_le _
      _ = (k : Cardinal) := rank_fin_fun k
  · intro x hx i
    have h0 := congrFun (LinearMap.mem_ker.mp hx) i
    simpa [hΦ] using h0

/-- **Analytic heart of the construction.** Given functionals `ρ'` and `m ≤ n`,
if `γ < cₙ(S)` there is a unit-image vector `eₘ` (`‖S eₘ‖ = 1`, `‖eₘ‖ ≤ 1/γ`) in
`⋂_i ker(ρ'ᵢ∘S)` and a norming functional `ρₘ`. The kernel `N` is closed with
`codim ≤ m ≤ n`, so `cₙ(S) ≤ ‖S|_N‖` supplies the stretched vector. -/
lemma exists_next_vector (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) {m : ℕ} (hm : m ≤ n) (ρ' : Fin m → (Y →L[𝕜] 𝕜)) :
    ∃ (em : X) (ρm : Y →L[𝕜] 𝕜),
      ‖S em‖ = 1 ∧ ‖em‖ ≤ 1 / γ ∧ ‖ρm‖ = 1 ∧ ρm (S em) = (‖S em‖ : 𝕜) ∧
      (∀ i : Fin m, ρ' i (S em) = 0) := by
  classical
  set Φ : X →L[𝕜] (Fin m → 𝕜) := ContinuousLinearMap.pi (fun i => (ρ' i).comp S) with hΦ
  have hΦapp : ∀ x i, Φ x i = ρ' i (S x) := by intro x i; simp [hΦ]
  set N : Submodule 𝕜 X := LinearMap.ker (Φ : X →ₗ[𝕜] (Fin m → 𝕜)) with hN
  have hN_closed : IsClosed (N : Set X) := Φ.isClosed_ker
  have hN_rank : Module.rank 𝕜 (X ⧸ N) ≤ (n : Cardinal) := by
    have heq : Module.rank 𝕜 (X ⧸ N)
        = Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin m → 𝕜))) :=
      (Φ : X →ₗ[𝕜] (Fin m → 𝕜)).quotKerEquivRange.rank_eq
    rw [heq]
    calc Module.rank 𝕜 (LinearMap.range (Φ : X →ₗ[𝕜] (Fin m → 𝕜)))
        ≤ Module.rank 𝕜 (Fin m → 𝕜) := Submodule.rank_le _
      _ = (m : Cardinal) := rank_fin_fun m
      _ ≤ (n : Cardinal) := by exact_mod_cast hm
  have hdev : γ < ‖S.comp N.subtypeL‖ :=
    lt_of_lt_of_le hγc (gelfandNumber_le_deviation hN_closed hN_rank)
  obtain ⟨ξ, hξ1, hξγ⟩ := (S.comp N.subtypeL).exists_lt_apply_of_lt_opNorm hdev
  set u : X := (ξ : X) with hu
  have hSu : γ < ‖S u‖ := hξγ
  have hSu_pos : 0 < ‖S u‖ := lt_trans hγ hSu
  have hu_le : ‖u‖ ≤ 1 := le_of_lt hξ1
  have hΦu0 : Φ u = 0 := LinearMap.mem_ker.mp ξ.2
  set em : X := ((‖S u‖ : 𝕜))⁻¹ • u with hem
  have hSem : ‖S em‖ = 1 := by
    rw [hem, map_smul, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hSu_pos,
      inv_mul_cancel₀ hSu_pos.ne']
  have hem_norm : ‖em‖ ≤ 1 / γ := by
    rw [hem, norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hSu_pos]
    calc (‖S u‖)⁻¹ * ‖u‖
        ≤ (‖S u‖)⁻¹ * 1 := by apply mul_le_mul_of_nonneg_left hu_le (by positivity)
      _ = (‖S u‖)⁻¹ := mul_one _
      _ ≤ 1 / γ := by rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hγ hSu.le
  have hem_ker : ∀ i : Fin m, ρ' i (S em) = 0 := by
    intro i
    have hui : ρ' i (S u) = 0 := by rw [← hΦapp u i, hΦu0]; rfl
    rw [hem, map_smul, map_smul, hui, smul_zero]
  obtain ⟨ρm, hρm_norm, hρm_app⟩ :=
    exists_dual_vector (𝕜 := 𝕜) (S em) (ne_of_eq_of_ne hSem one_ne_zero)
  exact ⟨em, ρm, hSem, hem_norm, hρm_norm, hρm_app, hem_ker⟩

section Hilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Orthonormal version of the nested construction: the images `S eⱼ` are
pairwise orthogonal and of unit norm. -/
lemma exists_triangular_system_hilbert (S : X →L[𝕜] H) {n : ℕ}
    {γ : ℝ} (hγ : 0 < γ) (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ e : Fin m → X,
      (∀ j, ‖S (e j)‖ = 1) ∧ (∀ j, ‖e j‖ ≤ 1 / γ) ∧
      (∀ i j : Fin m, i < j → inner 𝕜 (S (e i)) (S (e j)) = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, (fun j => j.elim0), (fun j => j.elim0), (fun i => i.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨e', h1, h2, h3⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨em, _, hSem, hemn, _, _, hker⟩ :=
      exists_next_vector S hγ hγc (Nat.le_of_succ_le_succ hk)
        (fun i => (innerSL 𝕜 (S (e' i)) : H →L[𝕜] 𝕜))
    refine ⟨Fin.snoc e' em, ?_, ?_, ?_⟩
    · intro j; induction j using Fin.lastCases with
      | last => simpa using hSem
      | cast j' => simpa using h1 j'
    · intro j; induction j using Fin.lastCases with
      | last => simpa using hemn
      | cast j' => simpa using h2 j'
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hi : i ≠ Fin.last k := ne_of_lt (hij.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact h3 i' j' (Fin.castSucc_lt_castSucc_iff.mp hij)
      · have hi : i ≠ Fin.last k := ne_of_lt hij
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        have hk0 := hker i'
        simpa using hk0

/-- **Reverse bound, Hilbert codomain.** If `H` is a Hilbert space then
`cₙ(S) ≤ √(n+1)·bₙ(S)` — sharp polynomial, product-free, pointwise (Theorem 8 of
[KNU25]). Orthonormal images give `‖S x‖² = ∑ ‖gⱼ‖²` (Parseval) and
`∑‖gⱼ‖ ≤ √(n+1)·‖S x‖` (Cauchy–Schwarz). -/
theorem gelfandNumber_le_sqrt_mul_bernsteinNumber_hilbert
    (S : X →L[𝕜] H) (n : ℕ) :
    gelfandNumber S n ≤ Real.sqrt ((n : ℝ) + 1) * bernsteinNumber S n := by
  have hb : 0 ≤ bernsteinNumber S n := bernsteinNumber_nonneg S n
  have hfacs : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
  by_contra h
  rw [not_le] at h
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between h
  have hγpos : 0 < γ := lt_of_le_of_lt (by positivity) hγ1
  obtain ⟨e, hSe, hen, hortho⟩ := exists_triangular_system_hilbert S hγpos hγ2 (n + 1) le_rfl
  have hon : Orthonormal 𝕜 (fun j => S (e j)) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases lt_trichotomy i j with hlt | heq | hgt
    · rw [hortho i j hlt]; simp [ne_of_lt hlt]
    · subst heq; rw [inner_self_eq_norm_sq_to_K, hSe i]; simp
    · rw [← inner_conj_symm, hortho j i hgt]; simp [ne_of_gt hgt]
  have hSx : ∀ g : Fin (n + 1) → 𝕜, S (∑ i, g i • e i) = ∑ i, g i • S (e i) := by
    intro g; rw [map_sum]; simp_rw [map_smul]
  have hgj : ∀ (g : Fin (n + 1) → 𝕜) (j), inner 𝕜 (S (e j)) (S (∑ i, g i • e i)) = g j := by
    intro g j
    rw [hSx g, inner_sum,
      Finset.sum_eq_single j
        (fun i _ hij => by
          rw [inner_smul_right, (orthonormal_iff_ite (𝕜 := 𝕜)).mp hon j i,
            if_neg (Ne.symm hij), mul_zero])
        (fun hj => absurd (Finset.mem_univ j) hj)]
    rw [inner_smul_right, (orthonormal_iff_ite (𝕜 := 𝕜)).mp hon j j, if_pos rfl, mul_one]
  have hindep : LinearIndependent 𝕜 e := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := hgj g j
    rw [hg, map_zero, inner_zero_right] at hj
    exact hj.symm
  set M : Submodule 𝕜 X := Submodule.span 𝕜 (Set.range e) with hM
  have hrankM : Module.rank 𝕜 M = ((n + 1 : ℕ) : Cardinal) := by
    classical
    have : Fintype (Set.range e) := Set.fintypeRange e
    rw [hM, rank_span hindep, Cardinal.mk_fintype,
      Set.card_range_of_injective hindep.injective, Fintype.card_fin]
  have hgain : γ / Real.sqrt ((n : ℝ) + 1) ≤ gainOnSubspace S M := by
    refine le_gainOnSubspace ?_ ?_
    · intro hbot
      have he0 : e 0 ∈ M := Submodule.subset_span ⟨0, rfl⟩
      rw [hbot, Submodule.mem_bot] at he0
      have h0 : ‖S (e 0)‖ = 0 := by rw [he0, map_zero, norm_zero]
      rw [hSe 0] at h0; norm_num at h0
    · intro x hxM hxne
      obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp hxM
      have hxpos : 0 < ‖∑ i, g i • e i‖ := norm_pos_iff.mpr hxne
      have hpars : ∑ j, ‖g j‖ ^ 2 = ‖S (∑ i, g i • e i)‖ ^ 2 := by
        have hK : (∑ j, ‖g j‖ ^ 2 : 𝕜) = (‖S (∑ i, g i • e i)‖ ^ 2 : 𝕜) := by
          rw [← inner_self_eq_norm_sq_to_K]
          nth_rewrite 1 [hSx g]
          rw [sum_inner]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [inner_smul_left, hgj g i, RCLike.conj_mul]
        exact_mod_cast hK
      have hsum_abs : ∑ j, ‖g j‖ ≤ Real.sqrt ((n : ℝ) + 1) * ‖S (∑ i, g i • e i)‖ := by
        refine (SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq fun j => ‖g j‖).trans ?_
        rw [hpars, Real.sqrt_sq (norm_nonneg _), Fintype.card_fin]
        push_cast
        rfl
      have hnormx : ‖∑ i, g i • e i‖ ≤ Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖ := by
        calc ‖∑ i, g i • e i‖
            ≤ ∑ i, ‖g i • e i‖ := norm_sum_le _ _
          _ = ∑ i, ‖g i‖ * ‖e i‖ := by simp_rw [norm_smul]
          _ ≤ ∑ i, ‖g i‖ * (1 / γ) :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hen i) (norm_nonneg _)
          _ = (∑ i, ‖g i‖) * (1 / γ) := by rw [← Finset.sum_mul]
          _ ≤ Real.sqrt ((n : ℝ) + 1) * ‖S (∑ i, g i • e i)‖ * (1 / γ) :=
              mul_le_mul_of_nonneg_right hsum_abs (by positivity)
          _ = Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖ := by ring
      rw [le_div_iff₀ hxpos]
      calc γ / Real.sqrt ((n : ℝ) + 1) * ‖∑ i, g i • e i‖
          ≤ γ / Real.sqrt ((n : ℝ) + 1) *
              (Real.sqrt ((n : ℝ) + 1) / γ * ‖S (∑ i, g i • e i)‖) :=
            mul_le_mul_of_nonneg_left hnormx (by positivity)
        _ = ‖S (∑ i, g i • e i)‖ := by field_simp
  have hble : gainOnSubspace S M ≤ bernsteinNumber S n :=
    le_csSup (bddAbove_bernsteinSet S n) ⟨M, hrankM, rfl⟩
  have hfin : γ / Real.sqrt ((n : ℝ) + 1) ≤ bernsteinNumber S n := le_trans hgain hble
  rw [div_le_iff₀ hfacs] at hfin
  nlinarith [hγ1, hfin]

end Hilbert

/-! ## Comparison of `aₙ` with the Gelfand and Kolmogorov numbers

We now formalise the bound

  `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))`

between the approximation numbers and the Gelfand / Kolmogorov numbers.
See the module docstring for the overall strategy. We work over an
`RCLike` field with `S : X →L[𝕜] Y` between Banach spaces.
-/

variable [CompleteSpace X] [CompleteSpace Y]

/-! ### Two norm lemmas about compositions through a subspace / quotient -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- If an operator `R : X →L[𝕜] X` has its whole range inside `M`, then
post-composing with `S` is controlled by the restricted norm `‖S|_M‖`:
`‖S ∘ R‖ ≤ ‖S|_M‖·‖R‖`. This is the elementary estimate behind the
Gelfand half. (`deviationFromRestriction S M = ‖S|_M‖`.) -/
lemma norm_comp_le_deviationFromRestriction_mul {S : X →L[𝕜] Y}
    {M : Submodule 𝕜 X} {R : X →L[𝕜] X} (hR : ∀ x, R x ∈ M) :
    ‖S.comp R‖ ≤ deviationFromRestriction S M * ‖R‖ := by
  refine opNorm_le_bound _
    (mul_nonneg (deviationFromRestriction_nonneg S M) (norm_nonneg R)) fun x => ?_
  -- Evaluate `S (R x)` through the inclusion `M ↪ X`: it equals
  -- `(S ∘ ι_M) ⟨R x, hR x⟩`, whose norm is `≤ ‖S|_M‖ · ‖R x‖`.
  have h_eq : (S.comp R) x = (S.comp M.subtypeL) ⟨R x, hR x⟩ := rfl
  rw [h_eq]
  calc ‖(S.comp M.subtypeL) ⟨R x, hR x⟩‖
      ≤ ‖S.comp M.subtypeL‖ * ‖(⟨R x, hR x⟩ : M)‖ := (S.comp M.subtypeL).le_opNorm _
    _ = deviationFromRestriction S M * ‖R x‖ := rfl
    _ ≤ deviationFromRestriction S M * (‖R‖ * ‖x‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm x) (deviationFromRestriction_nonneg S M)
    _ = deviationFromRestriction S M * ‖R‖ * ‖x‖ := by ring

omit [CompleteSpace X] [CompleteSpace Y] in
/-- If an operator `R : Y →L[𝕜] Y` vanishes on `V` (i.e. `V ≤ ker R`),
then pre-composing with `S` is controlled by the quotient norm
`‖π_V ∘ S‖`: `‖R ∘ S‖ ≤ ‖R‖·‖π_V ∘ S‖`. This is the elementary estimate
behind the Kolmogorov half: `R` factors through `Y ⧸ V` via the universal
lift `V.liftQL`. (`deviationFromSubspace S V = ‖π_V ∘ S‖`.) -/
lemma norm_comp_le_norm_mul_deviationFromSubspace {S : X →L[𝕜] Y}
    {V : Submodule 𝕜 Y} {R : Y →L[𝕜] Y}
    (hR : V ≤ LinearMap.ker (R : Y →ₗ[𝕜] Y)) :
    ‖R.comp S‖ ≤ ‖R‖ * deviationFromSubspace S V := by
  -- `R = (V.liftQL R hR) ∘ π_V`, so `R ∘ S = (V.liftQL R hR) ∘ (π_V ∘ S)`.
  have hfac : R.comp S = (V.liftQL R hR).comp (V.mkQL.comp S) := by
    ext x
    show R (S x) = V.liftQL R hR (V.mkQL (S x))
    rw [Submodule.liftQL_mkQL]
  rw [hfac]
  calc ‖(V.liftQL R hR).comp (V.mkQL.comp S)‖
      ≤ ‖V.liftQL R hR‖ * ‖V.mkQL.comp S‖ := opNorm_comp_le _ _
    _ ≤ ‖R‖ * ‖V.mkQL.comp S‖ :=
        mul_le_mul_of_nonneg_right (V.norm_liftQL_le R hR) (norm_nonneg _)
    _ = ‖R‖ * deviationFromSubspace S V := rfl

/-! ### Per-subspace bounds -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Gelfand half, per subspace.** For a closed `M ⊆ X` of codimension
`≤ n`, `aₙ(S) ≤ (1 + √n)·‖S|_M‖`. The approximant is `L := S ∘ P` for the
Garling–Gordon projection `P` with kernel `M`. -/
lemma approximationNumber_le_sqrt_mul_deviationFromRestriction
    (S : X →L[𝕜] Y) {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromRestriction S M := by
  have hdev0 : 0 ≤ deviationFromRestriction S M := deviationFromRestriction_nonneg S M
  -- The Garling–Gordon projection is available only up to `ε`; take `ε → 0`.
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  set ε : ℝ := δ / (deviationFromRestriction S M + 1) with hεdef
  have hε : 0 < ε := div_pos hδ (by positivity)
  obtain ⟨P, hP_idem, hP_ker, hP_norm⟩ :=
    exists_projection_ker_eq_of_codim_le hM_closed hM_codim hε
  -- `rank P = codim (ker P) = codim M ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    have e : Module.rank 𝕜 (X ⧸ LinearMap.ker (P : X →ₗ[𝕜] X))
              = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) :=
      (LinearMap.quotKerEquivRange (P : X →ₗ[𝕜] X)).rank_eq
    rw [hP_ker] at e
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : X →ₗ[𝕜] X)) := rfl
      _ = Module.rank 𝕜 (X ⧸ M) := e.symm
      _ ≤ (n : Cardinal) := hM_codim
  -- `L := S ∘ P` is an admissible rank-≤ n approximant.
  have hL_rank : (S.comp P).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le (ContinuousLinearMap.id 𝕜 X) P S
    rw [ContinuousLinearMap.comp_id] at h
    exact h.trans hPrank
  -- `id − P` lands in `M` (its range is `ker P = M`).
  have hR : ∀ x, (ContinuousLinearMap.id 𝕜 X - P) x ∈ M := by
    intro x
    have hPP : P (P x) = P x := by
      have h : (P.comp P) x = P x := by rw [hP_idem]
      exact h
    have hkey : P ((ContinuousLinearMap.id 𝕜 X - P) x) = 0 := by
      rw [sub_apply, ContinuousLinearMap.id_apply, map_sub,
        hPP, sub_self]
    rw [← hP_ker, LinearMap.mem_ker]
    exact hkey
  -- `‖id − P‖ ≤ 1 + (√n + ε)`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ ≤ 1 + (Real.sqrt n + ε) :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  -- `dev · ε ≤ δ`, so the `ε` term is absorbed into `δ`.
  have hdevε : deviationFromRestriction S M * ε ≤ δ := by
    rw [hεdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [hdev0, hδ.le]
  calc approximationNumber S n
      ≤ ‖S - S.comp P‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖S.comp (ContinuousLinearMap.id 𝕜 X - P)‖ := by
        rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.comp_id]
    _ ≤ deviationFromRestriction S M *
          ‖(ContinuousLinearMap.id 𝕜 X - P : X →L[𝕜] X)‖ :=
        norm_comp_le_deviationFromRestriction_mul hR
    _ ≤ deviationFromRestriction S M * (1 + (Real.sqrt n + ε)) :=
        mul_le_mul_of_nonneg_left h4 hdev0
    _ = (1 + Real.sqrt n) * deviationFromRestriction S M
          + deviationFromRestriction S M * ε := by ring
    _ ≤ (1 + Real.sqrt n) * deviationFromRestriction S M + δ := by gcongr

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Kolmogorov half, per subspace.** For `V ⊆ Y` of dimension `≤ n`,
`aₙ(S) ≤ (1 + √n)·‖π_V ∘ S‖`. The approximant is `L := P ∘ S` for the
Kadets–Snobar projection `P` onto `V`. -/
lemma approximationNumber_le_sqrt_mul_deviationFromSubspace
    (S : X →L[𝕜] Y) {n : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromSubspace S V := by
  obtain ⟨P, hP_idem, hP_range, hP_norm⟩ :=
    exists_projection_range_eq_of_rank_le hV_rank
  -- `rank P = dim (range P) = dim V ≤ n`.
  have hPrank : P.rank ≤ (n : Cardinal) := by
    calc P.rank = Module.rank 𝕜 (LinearMap.range (P : Y →ₗ[𝕜] Y)) := rfl
      _ = Module.rank 𝕜 V := by rw [hP_range]
      _ ≤ (n : Cardinal) := hV_rank
  -- `L := P ∘ S` is an admissible rank-≤ n approximant.
  have hL_rank : (P.comp S).rank ≤ (n : Cardinal) := by
    have h := ContinuousLinearMap.rank_comp_comp_le S P (ContinuousLinearMap.id 𝕜 Y)
    rw [ContinuousLinearMap.id_comp] at h
    exact h.trans hPrank
  -- `id − P` vanishes on `V` (since `P` fixes its range `V`).
  have hVker : V ≤ LinearMap.ker
      ((ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y) : Y →ₗ[𝕜] Y) := by
    intro v hv
    have hPv : P v = v := by
      rw [← hP_range] at hv
      obtain ⟨w, hw⟩ := hv
      have hPP : P (P w) = P w := by
        have h : (P.comp P) w = P w := by rw [hP_idem]
        exact h
      rw [← hw]; exact hPP
    rw [LinearMap.mem_ker]
    show (ContinuousLinearMap.id 𝕜 Y - P) v = 0
    rw [sub_apply, ContinuousLinearMap.id_apply, hPv, sub_self]
  -- `‖id − P‖ ≤ 1 + √n`.
  have h4 : ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ ≤ 1 + Real.sqrt n :=
    (norm_sub_le _ _).trans (add_le_add ContinuousLinearMap.norm_id_le hP_norm)
  calc approximationNumber S n
      ≤ ‖S - P.comp S‖ := approximationNumber_le_norm_sub hL_rank
    _ = ‖(ContinuousLinearMap.id 𝕜 Y - P).comp S‖ := by
        rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.id_comp]
    _ ≤ ‖(ContinuousLinearMap.id 𝕜 Y - P : Y →L[𝕜] Y)‖ * deviationFromSubspace S V :=
        norm_comp_le_norm_mul_deviationFromSubspace hVker
    _ ≤ (1 + Real.sqrt n) * deviationFromSubspace S V :=
        mul_le_mul_of_nonneg_right h4 (deviationFromSubspace_nonneg S V)

/-! ### The infimum bounds and the combined result -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Gelfand bound.** `aₙ(S) ≤ (1 + √n)·cₙ(S)` (Pietsch [Pie87, 2.10.2]).
The per-subspace bound is uniform over the closed codimension-`≤ n`
subspaces, so it passes to the infimum defining `cₙ`. -/
theorem approximationNumber_le_sqrt_mul_gelfandNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * gelfandNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, gelfandNumber]
  refine le_csInf ⟨_, ⊤, by rw [Submodule.top_coe]; exact isClosed_univ,
    by rw [rank_zero_iff.mpr inferInstance]; exact bot_le, rfl⟩ ?_
  rintro r ⟨M, hM_closed, hM_codim, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromRestriction S hM_closed hM_codim

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Kolmogorov bound.** `aₙ(S) ≤ (1 + √n)·dₙ(S)` (Pietsch
[Pie87, 2.10.2]). The per-subspace bound is uniform over the
dimension-`≤ n` subspaces, so it passes to the infimum defining `dₙ`. -/
theorem approximationNumber_le_sqrt_mul_kolmogorovNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * kolmogorovNumber S n := by
  have hc_pos : (0 : ℝ) < 1 + Real.sqrt n := by positivity
  rw [← div_le_iff₀' hc_pos, kolmogorovNumber]
  refine le_csInf ⟨_, ⊥, by rw [rank_bot]; exact bot_le, rfl⟩ ?_
  rintro r ⟨V, hV_rank, rfl⟩
  rw [div_le_iff₀' hc_pos]
  exact approximationNumber_le_sqrt_mul_deviationFromSubspace S hV_rank

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Approximation vs. Gelfand and Kolmogorov numbers.** The combined
bound `aₙ(S) ≤ (1 + √n)·min(cₙ(S), dₙ(S))`: the largest `s`-number `aₙ`
exceeds neither `cₙ` nor `dₙ` by more than the factor `1 + √n`. -/
theorem approximationNumber_le_sqrt_mul_min (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤
      (1 + Real.sqrt n) * min (gelfandNumber S n) (kolmogorovNumber S n) := by
  rcases le_total (gelfandNumber S n) (kolmogorovNumber S n) with h | h
  · rw [min_eq_left h]
    exact approximationNumber_le_sqrt_mul_gelfandNumber S n
  · rw [min_eq_right h]
    exact approximationNumber_le_sqrt_mul_kolmogorovNumber S n

/-! ## Determinant ingredients for the maximal difference theorem

The maximal difference theorem `aₙ(S) ≤ e·(n+1)·hₙ(S)` lives in
`SNumbers.MaxDifference`, built on the determinant quantities `Δₖ(S)` defined
there. This section provides the ingredients that belong to the comparison
theory developed here:

* `approximationNumber_comp_comp_le_mul_hilbertNumber` and its
  finite-dimensional form
  `approximationNumber_eucl_comp_comp_le_mul_hilbertNumber` — the (S3)-type
  bound `aₖ(B∘S∘A) ≤ ‖B‖·‖A‖·hₖ(S)` for factors through `ℓ₂` resp. `ℓ₂ⁿ⁺¹`;
* `prod_approximationNumber_eq_norm_det` — `∏ aₖ(T) = ‖det T‖` for an
  endomorphism of a finite-dimensional Hilbert space;
* `exists_mem_norm_gt_of_lt_gelfandNumber` /
  `exists_norm_mkQL_gt_of_lt_kolmogorovNumber` — point selection below the
  Gelfand / Kolmogorov numbers. -/

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Ingredient (1) of the determinant bound.** The (S3)-type bound for the
Hilbert numbers: `aₙ(B ∘ S ∘ A) ≤ ‖B‖·‖A‖·hₙ(S)` for `A : ℓ₂ → X`,
`B : Y → ℓ₂`. Immediate from the definition of `hₙ` as a supremum of
ratios `aₙ(BSA)/(‖B‖‖A‖)` (`ratio_le_hilbertNumber`); the zero cases are
handled separately since then `B ∘ S ∘ A = 0`. -/
lemma approximationNumber_comp_comp_le_mul_hilbertNumber
    (S : X →L[𝕜] Y) (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero, norm_zero,
      mul_zero, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  rcases eq_or_ne B 0 with rfl | hB
  · rw [ContinuousLinearMap.zero_comp, norm_zero, zero_mul, zero_mul]
    simpa using approximationNumber_le_norm (0 : L2 𝕜 →L[𝕜] L2 𝕜) n
  · have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
    have h := ratio_le_hilbertNumber S n hA hB
    rw [div_le_iff₀ hpos] at h
    exact h.trans_eq (by ring)

/-- **`∏ aₖ(T) = ‖det T‖`** for an endomorphism of a finite-dimensional Hilbert
space. The approximation numbers are Mathlib's singular values
(`sn_eq_singularValues_of_finiteDimensional`), and `‖det T‖ = ∏ σₖ` is Mathlib's
`LinearMap.normDet_eq_prod_singularValues` read through
`LinearMap.normDet_eq_norm_det`. This is the determinant ingredient of the
maximal difference theorem. -/
theorem prod_approximationNumber_eq_norm_det {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [Nontrivial E] (T : E →L[𝕜] E) :
    ∏ k ∈ Finset.range (Module.finrank 𝕜 E), approximationNumber T k
      = ‖LinearMap.det (T : E →ₗ[𝕜] E)‖ := by
  rw [← LinearMap.normDet_eq_norm_det, LinearMap.normDet_eq_prod_singularValues]
  exact Finset.prod_congr rfl fun k _ =>
    sn_eq_singularValues_of_finiteDimensional isSNumberSequence_approximationNumber T k

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Ingredient (1), finite-dimensional form.** For finite factors
`A' : ℓ₂ⁿ⁺¹ → X`, `B' : Y → ℓ₂ⁿ⁺¹`, still `aₖ(B'∘S∘A') ≤ ‖B'‖·‖A'‖·hₖ(S)`.
Compose with the isometric section `ℓ₂ⁿ⁺¹ ↪ ℓ₂` (`exists_l2_section`, both
maps norm `≤ 1`) and apply the `ℓ₂`-form together with the (S3) ideal
property to drop the section maps. -/
lemma approximationNumber_eucl_comp_comp_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n k : ℕ)
    (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
    (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) :
    approximationNumber (B'.comp (S.comp A')) k ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
  obtain ⟨jm, pm, hpj, hp1, hj1⟩ := exists_l2_section (𝕜 := 𝕜) n
  have hpj_apply : ∀ z, pm (jm z) = z := fun z => by
    rw [← ContinuousLinearMap.comp_apply, hpj, ContinuousLinearMap.id_apply]
  set AL : L2 𝕜 →L[𝕜] X := A'.comp pm with hAL
  set BL : Y →L[𝕜] L2 𝕜 := jm.comp B' with hBL
  have hMeq : B'.comp (S.comp A') = pm.comp ((BL.comp (S.comp AL)).comp jm) := by
    ext x
    simp only [hAL, hBL, ContinuousLinearMap.comp_apply]
    rw [hpj_apply x, hpj_apply (B' (S (A' x)))]
  have hak : 0 ≤ approximationNumber (BL.comp (S.comp AL)) k := approximationNumber_nonneg _ _
  calc approximationNumber (B'.comp (S.comp A')) k
      = approximationNumber (pm.comp ((BL.comp (S.comp AL)).comp jm)) k := by rw [hMeq]
    _ ≤ ‖pm‖ * approximationNumber (BL.comp (S.comp AL)) k * ‖jm‖ :=
        approximationNumber_comp_comp_le jm (BL.comp (S.comp AL)) pm k
    _ ≤ 1 * approximationNumber (BL.comp (S.comp AL)) k * 1 :=
        mul_le_mul (mul_le_mul hp1 le_rfl hak zero_le_one) hj1 (norm_nonneg _)
          (mul_nonneg zero_le_one hak)
    _ = approximationNumber (BL.comp (S.comp AL)) k := by ring
    _ ≤ ‖BL‖ * ‖AL‖ * hilbertNumber S k :=
        approximationNumber_comp_comp_le_mul_hilbertNumber S AL BL k
    _ ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by
        have hBLn : ‖BL‖ ≤ ‖B'‖ :=
          (ContinuousLinearMap.opNorm_comp_le jm B').trans
            (mul_le_of_le_one_left (norm_nonneg _) hj1)
        have hALn : ‖AL‖ ≤ ‖A'‖ :=
          (ContinuousLinearMap.opNorm_comp_le A' pm).trans
            (mul_le_of_le_one_right (norm_nonneg _) hp1)
        exact mul_le_mul (mul_le_mul hBLn hALn (norm_nonneg _) (norm_nonneg _)) le_rfl
          (hilbertNumber_nonneg S k) (mul_nonneg (norm_nonneg _) (norm_nonneg _))

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Iterative point selection for the Gelfand numbers.** If `c < cₖ(S)` and `M` is a
closed subspace of `X` of codimension `≤ k`, then `M` contains a vector `x` with `‖x‖ ≤ 1`
and `‖S x‖ > c` (since `cₖ(S) ≤ ‖S|_M‖ = ⨆_{x∈M} ‖S x‖`). -/
lemma exists_mem_norm_gt_of_lt_gelfandNumber (S : X →L[𝕜] Y) {k : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X)) (hM_rank : Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal))
    {c : ℝ} (hc : c < gelfandNumber S k) :
    ∃ x ∈ M, ‖x‖ ≤ 1 ∧ c < ‖S x‖ := by
  have hlt : c < ‖S.comp M.subtypeL‖ :=
    lt_of_lt_of_le hc (gelfandNumber_le_deviation hM_closed hM_rank)
  obtain ⟨w, hw, hwc⟩ := (S.comp M.subtypeL).exists_lt_apply_of_lt_opNorm hlt
  exact ⟨(w : X), w.2, by simpa using hw.le, by simpa using hwc⟩

omit [CompleteSpace X] [CompleteSpace Y] in
/-- **Iterative point selection for the Kolmogorov numbers (dual).** If `c < dₖ(S)` and `V` is a
subspace of `Y` of dimension `≤ k`, there is `x` with `‖x‖ ≤ 1` and `‖π_V(S x)‖ > c`
(since `dₖ(S) ≤ ‖π_V ∘ S‖`). -/
lemma exists_norm_mkQL_gt_of_lt_kolmogorovNumber (S : X →L[𝕜] Y) {k : ℕ} {V : Submodule 𝕜 Y}
    (hV_rank : Module.rank 𝕜 V ≤ (k : Cardinal)) {c : ℝ} (hc : c < kolmogorovNumber S k) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ c < ‖V.mkQL (S x)‖ := by
  have hlt : c < ‖V.mkQL.comp S‖ := lt_of_lt_of_le hc (kolmogorovNumber_le_deviation hV_rank)
  obtain ⟨x, hx, hxc⟩ := (V.mkQL.comp S).exists_lt_apply_of_lt_opNorm hlt
  exact ⟨x, hx.le, by simpa using hxc⟩

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
