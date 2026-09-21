/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Entropy
import LeanPool.SNumbers.SNumbers.Inequalities
import LeanPool.SNumbers.BasicResults.SVD
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Bounding the Gelfand and Kolmogorov numbers by the entropy numbers

The entropy numbers `eₙ` are not an `s`-number sequence — they fail (S4) and
(S5), see `SNumbers.Entropy` — but they dominate the Gelfand and Kolmogorov
numbers, and that is what ties those two sequences to compactness.

## Upper bounds: covering estimates

A finite `ε`-net `y₁, …, y_k` of the image `S(B_X)` of the closed unit ball
bounds both sequences at index `k`:

* the span of the net has dimension `≤ k` and `S(B_X)` deviates from it by at
  most `ε`, so `d_k(S) ≤ ε` (`kolmogorovNumber_le_of_fin_net`);
* the common kernel of norming functionals for the `yᵢ` is closed of
  codimension `≤ k`, and on its unit ball `S` has norm at most `2ε`, so
  `c_k(S) ≤ 2ε` (`gelfandNumber_le_two_mul_of_fin_net`).

The second uses Hahn–Banach, which is why this file works over `RCLike 𝕜`
(that is, `ℝ` or `ℂ`).

## Lower bounds: counting separated points

For the sharp comparison the inequality is needed in the other direction, and
`eₙ` is bounded from below by *counting*: a ball of radius `ε` has diameter at
most `2ε`, so it can hold at most one point of a family whose members are more
than `2ε` apart. A cover of `S(B_X)` by `2 ^ n` such balls therefore admits at
most `2 ^ n` such points — so exhibiting more of them forces `ε` to be large.
This is the pigeonhole principle: more objects than boxes means some box holds
two of them, and here two in one box is a contradiction.

## Main results

* `SNumbers.kolmogorovNumber_le_of_fin_net`,
  `SNumbers.gelfandNumber_le_two_mul_of_fin_net` — the two covering estimates.
* `SNumbers.kolmogorovNumber_two_pow_le_entropyNumber` :
    `d_{2ⁿ} S ≤ eₙ S`.
* `SNumbers.gelfandNumber_two_pow_le_two_mul_entropyNumber` :
    `c_{2ⁿ} S ≤ 2 · eₙ S`.
* `SNumbers.le_entropyNumber_of_separated` — a *lower* bound for `eₙ` from a
  family of well-separated points of `S(B_X)`.
* `SNumbers.exists_kolmogorov_flag`, `SNumbers.exists_gelfand_flag` — the
  triangular systems below `dₙ` resp. `cₙ`.
* `SNumbers.max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber` :
    `max (cₙ S) (dₙ S) ≤ (n+1) · eₙ S`, the sharp bound of [Pie80, 12.3.2].
* `SNumbers.half_le_entropyNumber_id` : `eₙ (id_X) ≥ 1/2` when `dim X > n`,
  by comparing volumes.
* `SNumbers.approximationNumber_le_two_mul_entropyNumber` :
    `aₙ S ≤ 2 · eₙ S` between Hilbert spaces.
* `SNumbers.hilbertNumber_le_two_mul_entropyNumber` : `hₙ S ≤ 2 · eₙ S`.

## Implementation notes

Both kinds of bound are wanted. The dyadic ones transport `eₙ S → 0` to
`dₙ S → 0` and `cₙ S → 0` (`AddOns.Compact`), since shifting the index by a
fixed function of `n` survives a limit. The sharp bound does not do that —
`(n+1)·eₙ` need not tend to `0` when `eₙ` does — but for a fixed `n` it is the
better estimate.

Nets are passed as functions `Fin k → Y` rather than as the `Finset` of
`SNumbers.entropySet`: `k` is exactly the index at which the resulting bound on
`d_k` / `c_k` holds. `exists_fin_net_of_mem_entropySet` translates.

## References

* A. Pietsch, *Operator ideals*, North-Holland Mathematical Library 20,
  North-Holland, 1980, [doi](<https://doi.org/10.1016/S0924-6509(09)X7001-7>),
  12.3 ([Pie80]).
* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Studies in Advanced
  Mathematics 13, Cambridge University Press, 1987,
  [link](https://zbmath.org/3996455), 2.4 ([Pie87]).
-/

universe u

open Filter Topology
open scoped Cardinal ENNReal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-! ### Covering estimates -/

/-- The span of `k` vectors has dimension at most `k`. -/
private lemma rank_span_range_le {k : ℕ} (y : Fin k → Y) :
    Module.rank 𝕜 (Submodule.span 𝕜 (Set.range y)) ≤ (k : Cardinal) := by
  classical
  -- Present the range as a `Finset`, so that the bound is a cast of a
  -- natural number and no universe lifting is involved.
  have hset : Set.range y = ((Finset.univ.image y : Finset Y) : Set Y) := by simp
  rw [hset]
  refine (rank_span_finset_le _).trans ?_
  have hcard : (Finset.univ.image y).card ≤ k := by
    simpa using Finset.card_image_le (s := (Finset.univ : Finset (Fin k))) (f := y)
  exact_mod_cast hcard

/-- **Covering estimate for the Kolmogorov numbers.** If the image of the closed
unit ball is covered by the `ε`-balls around `k` points `y i`, then
`d_k(S) ≤ ε`: the span `V` of the `y i` has dimension at most `k`, and
`‖π_V (S x)‖ = ‖π_V (S x - y i)‖ ≤ ‖S x - y i‖ ≤ ε` for a suitable `i`. -/
lemma kolmogorovNumber_le_of_fin_net {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    kolmogorovNumber S k ≤ ε := by
  set V : Submodule 𝕜 Y := Submodule.span 𝕜 (Set.range y) with hV
  refine (kolmogorovNumber_le_deviation (rank_span_range_le y)).trans ?_
  show ‖V.mkQL.comp S‖ ≤ ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun x hx => ?_
  obtain ⟨i, hi⟩ := hcov x hx
  -- `y i` lies in `V`, so it is killed by the quotient map.
  have hzero : V.mkQL (y i) = 0 := by
    simp only [Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨i, rfl⟩
  calc ‖(V.mkQL.comp S) x‖
      = ‖V.mkQL (S x - y i)‖ := by
        simp only [coe_comp, Function.comp_apply, map_sub, hzero, sub_zero]
    _ ≤ ‖S x - y i‖ := V.norm_mkQL_apply_le _
    _ ≤ ε := hi

/-- **Covering estimate for the Gelfand numbers.** If the image of the closed
unit ball is covered by the `ε`-balls around `k` points `y i`, then
`c_k(S) ≤ 2ε`.

Choose norming functionals `bᵢ` for the `y i` (Hahn–Banach) and let `M` be the
common kernel of the `bᵢ ∘ S`, a closed subspace of codimension `≤ k`. For
`x ∈ M` in the unit ball pick `i` with `‖S x - y i‖ ≤ ε`; since `bᵢ (S x) = 0`,
`‖y i‖ = bᵢ (y i - S x) ≤ ε`, and therefore `‖S x‖ ≤ 2ε`. -/
lemma gelfandNumber_le_two_mul_of_fin_net {S : X →L[𝕜] Y} {k : ℕ} {y : Fin k → Y}
    {ε : ℝ} (hcov : ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε) :
    gelfandNumber S k ≤ 2 * ε := by
  classical
  choose b hb_norm hb_app using fun i : Fin k => exists_dual_vector'' 𝕜 (y i)
  obtain ⟨M, hM_closed, hM_rank, hM_ker⟩ := exists_closed_codim_forall_eq_zero S b
  refine (gelfandNumber_le_deviation hM_closed hM_rank).trans ?_
  show ‖S.comp M.subtypeL‖ ≤ 2 * ε
  refine ContinuousLinearMap.opNorm_le_of_unit_closedBall _ fun z hz => ?_
  obtain ⟨i, hi⟩ := hcov (z : X) (by simpa using hz)
  -- The norming functional of `y i` vanishes on `S x`, so `‖y i‖` is small.
  have h_yi : ‖y i‖ ≤ ε := by
    have h0 : b i (S (z : X)) = 0 := hM_ker (z : X) z.2 i
    have heq : b i (y i - S (z : X)) = ((‖y i‖ : ℝ) : 𝕜) := by
      rw [map_sub, hb_app i, h0, sub_zero]
    have hnorm : ‖y i‖ = ‖b i (y i - S (z : X))‖ := by
      rw [heq, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _)]
    rw [hnorm]
    calc ‖b i (y i - S (z : X))‖
        ≤ ‖b i‖ * ‖y i - S (z : X)‖ := (b i).le_opNorm _
      _ ≤ 1 * ‖y i - S (z : X)‖ :=
          mul_le_mul_of_nonneg_right (hb_norm i) (norm_nonneg _)
      _ = ‖S (z : X) - y i‖ := by rw [one_mul, norm_sub_rev]
      _ ≤ ε := hi
  calc ‖(S.comp M.subtypeL) z‖
      = ‖S (z : X)‖ := by simp
    _ ≤ ‖S (z : X) - y i‖ + ‖y i‖ := by
        simpa using norm_add_le (S (z : X) - y i) (y i)
    _ ≤ ε + ε := add_le_add hi h_yi
    _ = 2 * ε := by ring

/-! ### Dyadic comparison with the entropy numbers -/

/-- Repackaging of an admissible entropy radius: a cover of `S(B_X)` by at most
`2 ^ n` closed `ε`-balls, with the centres presented as a function
`Fin k → Y` where `k ≤ 2 ^ n` is the actual number of centres. -/
private lemma exists_fin_net_of_mem_entropySet {S : X →L[𝕜] Y} {n : ℕ} {ε : ℝ}
    (hε : ε ∈ entropySet S n) :
    ∃ (k : ℕ) (y : Fin k → Y), k ≤ 2 ^ n ∧
      ∀ x : X, ‖x‖ ≤ 1 → ∃ i, ‖S x - y i‖ ≤ ε := by
  classical
  obtain ⟨-, N, hN_card, hcov⟩ := hε
  refine ⟨N.card, fun i => ((N.equivFin.symm i : ↥N) : Y), hN_card, fun x hx => ?_⟩
  have hmem : S x ∈ ⋃ w ∈ (N : Set Y), Metric.closedBall w ε :=
    hcov ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hmem
  obtain ⟨w, hw, hdist⟩ := hmem
  refine ⟨N.equivFin ⟨w, by simpa using hw⟩, ?_⟩
  simpa [dist_eq_norm] using hdist

/-- **`d_{2ⁿ} S ≤ eₙ S`.** A cover of `S(B_X)` by `2 ^ n` balls of radius `ε`
gives a subspace of dimension at most `2 ^ n` — the span of the centres — from
which `S(B_X)` deviates by at most `ε`. -/
theorem kolmogorovNumber_two_pow_le_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S (2 ^ n) ≤ entropyNumber S n := by
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
  obtain ⟨k, y, hk, hnet⟩ := exists_fin_net_of_mem_entropySet hε
  exact (kolmogorovNumber_antitone' S hk).trans (kolmogorovNumber_le_of_fin_net hnet)

/-- **`c_{2ⁿ} S ≤ 2 · eₙ S`.** The Gelfand counterpart of
`kolmogorovNumber_two_pow_le_entropyNumber`; the factor `2` comes from the
norming-functional argument. -/
theorem gelfandNumber_two_pow_le_two_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S (2 ^ n) ≤ 2 * entropyNumber S n := by
  have key : gelfandNumber S (2 ^ n) / 2 ≤ entropyNumber S n := by
    rw [entropyNumber_def]
    refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
    obtain ⟨k, y, hk, hnet⟩ := exists_fin_net_of_mem_entropySet hε
    have h := (gelfandNumber_antitone' S hk).trans
      (gelfandNumber_le_two_mul_of_fin_net hnet)
    linarith
  linarith

/-! ### A lower bound for the entropy numbers -/

/-- **Separation bounds the entropy numbers from below.** If `S(B_X)` contains
more than `2 ^ n` points that are pairwise at distance at least `δ`, then
`eₙ(S) ≥ δ/2`.

The boxes of the pigeonhole are the balls of an admissible cover, the objects
are the given points. Suppose a radius `ε < δ/2` were admissible. Sending each
point to a covering centre is then injective: two points sharing a centre `y`
are both within `ε` of `y`, hence within `2ε < δ` of each other, which the
separation forbids. So there are at least as many centres as points, i.e.
`2 ^ n < P.card ≤ 2 ^ n`. -/
lemma le_entropyNumber_of_separated {S : X →L[𝕜] Y} {n : ℕ} {δ : ℝ} {P : Finset Y}
    (hP : ↑P ⊆ ⇑S '' Metric.closedBall 0 1) (hcard : 2 ^ n < P.card)
    (hsep : ∀ z ∈ P, ∀ z' ∈ P, z ≠ z' → δ ≤ dist z z') :
    δ / 2 ≤ entropyNumber S n := by
  classical
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty S n) fun ε hε => ?_
  by_contra hcon
  have hlt : ε < δ / 2 := not_le.mp hcon
  obtain ⟨-, N, hN_card, hcov⟩ := hε
  -- Assign to every point of `P` a covering centre in `N`.
  have hchoice : ∀ z ∈ P, ∃ y ∈ N, dist z y ≤ ε := by
    intro z hz
    have hz' := hcov (hP (Finset.mem_coe.mpr hz))
    simp only [Set.mem_iUnion, Metric.mem_closedBall, exists_prop] at hz'
    obtain ⟨y, hy, hd⟩ := hz'
    exact ⟨y, by simpa using hy, hd⟩
  choose! g hg_mem hg_dist using hchoice
  -- Distinct points of `P` cannot share a centre.
  have hinj : ∀ z ∈ P, ∀ z' ∈ P, g z = g z' → z = z' := by
    intro z hz z' hz' hgg
    by_contra hne
    have h1 : dist z z' ≤ dist z (g z) + dist (g z) z' := dist_triangle _ _ _
    have h2 : dist (g z) z' = dist z' (g z') := by rw [hgg, dist_comm]
    have h3 := hsep z hz z' hz' hne
    have h4 := hg_dist z hz
    have h5 := hg_dist z' hz'
    rw [h2] at h1
    linarith
  have hcard' : P.card ≤ N.card :=
    Finset.card_le_card_of_injOn g (fun z hz => hg_mem z hz) hinj
  omega

/-! ### Triangular flags

`n+1` vectors of the unit ball whose images are independent at level `γ`:
measured against a chain of subspaces for `dₙ`, by annihilating functionals for
`cₙ`. Both are built by `Fin.snoc` induction on the point-selection lemmas of
`SNumbers.Inequalities`. -/

/-- Distance to a subspace, in additive form: if `y` is more than `γ` away from
`V` in the quotient norm, then `‖y + w‖ > γ` for every `w ∈ V`. -/
private lemma lt_norm_add_of_lt_norm_mkQL {V : Submodule 𝕜 Y} {y w : Y} {γ : ℝ}
    (hy : γ < ‖V.mkQL y‖) (hw : w ∈ V) : γ < ‖y + w‖ := by
  have hw0 : V.mkQL w = 0 := by
    simp only [Submodule.mkQL_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact hw
  calc γ < ‖V.mkQL y‖ := hy
    _ = ‖V.mkQL (y + w)‖ := by rw [map_add, hw0, add_zero]
    _ ≤ ‖y + w‖ := V.norm_mkQL_apply_le _

/-- **Kolmogorov flag.** From `γ < dₙ(S)`: vectors `x j` of the unit ball and
subspaces `V j` containing every earlier image `S (x k)`, `k < j`, with
`‖S (x j) + w‖ > γ` for all `w ∈ V j`. Each `V j` is the span of the images
chosen so far, of dimension at most `n`. -/
lemma exists_kolmogorov_flag (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ}
    (hγd : γ < kolmogorovNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (V : Fin m → Submodule 𝕜 Y),
      (∀ j, ‖x j‖ ≤ 1) ∧
      (∀ j k : Fin m, k < j → S (x k) ∈ V j) ∧
      (∀ (j : Fin m) (w : Y), w ∈ V j → γ < ‖S (x j) + w‖) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, (fun j => j.elim0), (fun j => j.elim0),
      (fun j => j.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨x', V', hx'norm, hx'mem, hx'gt⟩ := ih (Nat.le_of_succ_le hk)
    -- The span of the images chosen so far has dimension at most `k ≤ n`.
    set W : Submodule 𝕜 Y := Submodule.span 𝕜 (Set.range fun i : Fin k => S (x' i))
      with hW
    have hWrank : Module.rank 𝕜 W ≤ (n : Cardinal) :=
      (rank_span_range_le _).trans (by exact_mod_cast Nat.le_of_succ_le_succ hk)
    obtain ⟨xm, hxm_norm, hxm_gt⟩ :=
      exists_norm_mkQL_gt_of_lt_kolmogorovNumber S hWrank hγd
    refine ⟨Fin.snoc x' xm, Fin.snoc V' W, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_norm
      | cast j' => simpa using hx'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last =>
        intro i hi
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last (ne_of_lt hi)
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact Submodule.subset_span ⟨i', rfl⟩
      | cast j' =>
        intro i hi
        have hne : i ≠ Fin.last k := ne_of_lt (hi.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hne
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hx'mem j' i' (Fin.castSucc_lt_castSucc_iff.mp hi)
    · intro j
      induction j using Fin.lastCases with
      | last =>
        intro w hw
        rw [Fin.snoc_last] at hw ⊢
        exact lt_norm_add_of_lt_norm_mkQL hxm_gt hw
      | cast j' =>
        intro w hw
        rw [Fin.snoc_castSucc] at hw ⊢
        exact hx'gt j' w hw

/-- **Gelfand flag.** From `0 < γ < cₙ(S)`: vectors `x j` of the unit ball and
norming functionals `ρ j` with `ρ j (S (x j)) = γ` and `ρ i (S (x j)) = 0` for
`i < j`. Rescaling the unit-image vectors of `exists_next_vector` by `γ` puts
them into the unit ball. -/
lemma exists_gelfand_flag (S : X →L[𝕜] Y) {n : ℕ} {γ : ℝ} (hγ : 0 < γ)
    (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ (x : Fin m → X) (ρ : Fin m → (Y →L[𝕜] 𝕜)),
      (∀ j, ‖x j‖ ≤ 1) ∧ (∀ j, ‖ρ j‖ ≤ 1) ∧
      (∀ j, ρ j (S (x j)) = ((γ : ℝ) : 𝕜)) ∧
      (∀ i j : Fin m, i < j → ρ i (S (x j)) = 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨Fin.elim0, Fin.elim0, (fun j => j.elim0), (fun j => j.elim0),
      (fun j => j.elim0), (fun i => i.elim0)⟩
  | succ k ih =>
    intro hk
    obtain ⟨x', ρ', hx'norm, hρ'norm, hρ'diag, hρ'tri⟩ := ih (Nat.le_of_succ_le hk)
    obtain ⟨em, ρm, hSem, hem_norm, hρm_norm, hρm_diag, hker⟩ :=
      exists_next_vector S hγ hγc (Nat.le_of_succ_le_succ hk) ρ'
    have hxm_norm : ‖((γ : ℝ) : 𝕜) • em‖ ≤ 1 := by
      rw [norm_smul, RCLike.norm_ofReal, abs_of_pos hγ]
      calc γ * ‖em‖ ≤ γ * (1 / γ) := mul_le_mul_of_nonneg_left hem_norm hγ.le
        _ = 1 := by field_simp
    have hxm_diag : ρm (S (((γ : ℝ) : 𝕜) • em)) = ((γ : ℝ) : 𝕜) := by
      rw [map_smul, map_smul, hρm_diag, hSem]
      simp
    have hxm_ker : ∀ i : Fin k, ρ' i (S (((γ : ℝ) : 𝕜) • em)) = 0 := by
      intro i
      rw [map_smul, map_smul, hker i, smul_zero]
    refine ⟨Fin.snoc x' (((γ : ℝ) : 𝕜) • em), Fin.snoc ρ' ρm, ?_, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_norm
      | cast j' => simpa using hx'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hρm_norm.le
      | cast j' => simpa using hρ'norm j'
    · intro j
      induction j using Fin.lastCases with
      | last => simpa using hxm_diag
      | cast j' => simpa using hρ'diag j'
    · intro i j hij
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
      · have hi : i ≠ Fin.last k := ne_of_lt (hij.trans (Fin.castSucc_lt_last j'))
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hρ'tri i' j' (Fin.castSucc_lt_castSucc_iff.mp hij)
      · have hi : i ≠ Fin.last k := ne_of_lt hij
        obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact hxm_ker i'

/-! ### The entropy bound

A flag of `n+1` vectors has `2^(n+1)` signed averages `(n+1)⁻¹ · Σ ±x k`, all in
the unit ball. Two of them differ by `(n+1)⁻¹ · 2 · (S (x j) + w)`, where `j` is
the index where the signs first disagree — last for the Kolmogorov flag, first
for the Gelfand one — and `w` is a combination of the images the flag makes
`S (x j)` independent of. So the difference exceeds `2γ/(n+1)`: more than `2 ^ n`
points, pairwise that far apart, and the count does the rest. -/

/-- Unwinding the constants: a separation of `2γ/(n+1)` gives `γ ≤ (n+1)·e`. -/
private lemma le_succ_mul_of_sep {n : ℕ} {γ e : ℝ} (hn1 : (0 : ℝ) < (n : ℝ) + 1)
    (h : (2 * γ / ((n : ℝ) + 1)) / 2 ≤ e) : γ ≤ ((n : ℝ) + 1) * e := by
  have heq : (2 * γ / ((n : ℝ) + 1)) / 2 = γ / ((n : ℝ) + 1) := by ring
  rw [heq] at h
  calc γ = ((n : ℝ) + 1) * (γ / ((n : ℝ) + 1)) := by field_simp
    _ ≤ ((n : ℝ) + 1) * e := mul_le_mul_of_nonneg_left h hn1.le

/-- The `±1`-signed sum of vectors of the unit ball has norm at most `n+1`. -/
private lemma norm_signedSum_le {n : ℕ} {x : Fin (n + 1) → X}
    (hx : ∀ j, ‖x j‖ ≤ 1) {a : Fin (n + 1) → 𝕜} (ha : ∀ k, ‖a k‖ ≤ 1) :
    ‖∑ k, a k • x k‖ ≤ (n : ℝ) + 1 := by
  calc ‖∑ k, a k • x k‖ ≤ ∑ k, ‖a k • x k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin (n + 1), (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_smul]
        nlinarith [ha k, hx k, norm_nonneg (a k), norm_nonneg (x k)]
    _ = (n : ℝ) + 1 := by simp

/-- `le_entropyNumber_of_separated` for a family indexed by sign patterns: the
`2 ^ (n+1)` patterns give that many distinct points, since separated points are
in particular distinct. -/
private lemma le_entropyNumber_of_sign_family {S : X →L[𝕜] Y} {n : ℕ} {δ : ℝ}
    {z : (Fin (n + 1) → Bool) → Y}
    (hmem : ∀ σ, z σ ∈ ⇑S '' Metric.closedBall 0 1)
    (hδ : 0 < δ) (hsep : ∀ σ τ, σ ≠ τ → δ ≤ dist (z σ) (z τ)) :
    δ / 2 ≤ entropyNumber S n := by
  classical
  have hz_inj : Function.Injective z := by
    intro σ τ hστ
    by_contra hne
    have h1 := hsep σ τ hne
    rw [hστ, dist_self] at h1
    linarith
  have hPcard : (Finset.image z Finset.univ).card = 2 ^ (n + 1) := by
    rw [Finset.card_image_of_injective _ hz_inj, Finset.card_univ, Fintype.card_fun]
    simp
  refine le_entropyNumber_of_separated (P := Finset.image z Finset.univ) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨σ, rfl⟩ := hy
    exact hmem σ
  · rw [hPcard]
    exact Nat.pow_lt_pow_right one_lt_two (Nat.lt_succ_self n)
  · intro y hy y' hy' hyy
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy hy'
    obtain ⟨σ, rfl⟩ := hy
    obtain ⟨τ, rfl⟩ := hy'
    exact hsep σ τ fun h => hyy (by rw [h])

/-- **The entropy bound for the Kolmogorov numbers**: `dₙ(S) ≤ (n+1) · eₙ(S)`
(Pietsch, *Operator ideals*, 12.3.2). -/
theorem kolmogorovNumber_le_succ_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    kolmogorovNumber S n ≤ ((n : ℝ) + 1) * entropyNumber S n := by
  classical
  by_contra hcon
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (not_le.mp hcon)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hγ0 : 0 < γ :=
    lt_of_le_of_lt (by positivity [entropyNumber_nonneg S n]) hγ1
  obtain ⟨x, V, hxnorm, hVmem, hVgt⟩ := exists_kolmogorov_flag S hγ2 (n + 1) le_rfl
  have hnorm_two : ‖(2 : 𝕜)‖ = 2 := by
    rw [show (2 : 𝕜) = ((2 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
    norm_num
  -- The averaging scalar and the `2 ^ (n+1)` signed averages.
  set c : 𝕜 := ((((n : ℝ) + 1)⁻¹ : ℝ) : 𝕜) with hc
  have hcnorm : ‖c‖ = ((n : ℝ) + 1)⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_pos (by positivity)]
  set sgn : Bool → 𝕜 := fun b => if b then 1 else -1 with hsgn
  have hsgn_norm : ∀ b, ‖sgn b‖ = 1 := by intro b; cases b <;> simp [hsgn]
  set z : (Fin (n + 1) → Bool) → Y := fun σ => S (c • ∑ k, sgn (σ k) • x k) with hz
  -- Each signed average lies in the image of the unit ball.
  have hz_mem : ∀ σ, z σ ∈ ⇑S '' Metric.closedBall 0 1 := by
    intro σ
    refine ⟨c • ∑ k, sgn (σ k) • x k, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, hcnorm]
    have h1 : ‖∑ k, sgn (σ k) • x k‖ ≤ (n : ℝ) + 1 :=
      norm_signedSum_le hxnorm fun k => le_of_eq (hsgn_norm (σ k))
    calc ((n : ℝ) + 1)⁻¹ * ‖∑ k, sgn (σ k) • x k‖
        ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn1)
  -- Distinct sign patterns give points more than `2γ/(n+1)` apart.
  have hsep : ∀ σ τ, σ ≠ τ → 2 * γ / ((n : ℝ) + 1) ≤ dist (z σ) (z τ) := by
    intro σ τ hne
    set D : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => σ k ≠ τ k) with hD
    have hDne : D.Nonempty := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
      exact ⟨k, by simp [hD, hk]⟩
    set j := D.max' hDne with hj
    have hjne : σ j ≠ τ j := by
      have := D.max'_mem hDne
      simpa [hD, hj] using this
    set a : Fin (n + 1) → 𝕜 := fun k => sgn (σ k) - sgn (τ k) with ha
    have ha_zero : ∀ k, σ k = τ k → a k = 0 := by intro k h; simp [ha, h]
    have ha_norm : ∀ k, σ k ≠ τ k → ‖a k‖ = 2 := by
      intro k h
      have hcases : a k = 2 ∨ a k = -2 := by
        simp only [ha, hsgn]
        cases hb : σ k <;> cases hb' : τ k <;> simp [hb, hb'] at h ⊢ <;> norm_num
      rcases hcases with h2 | h2
      · rw [h2, hnorm_two]
      · rw [h2, norm_neg, hnorm_two]
    have haj_ne : a j ≠ 0 := by
      intro h0
      have h2 := ha_norm j hjne
      rw [h0, norm_zero] at h2
      norm_num at h2
    -- Split off the largest disagreeing index; the rest lies in `V j`.
    set u : Y := ∑ k ∈ Finset.univ.erase j, a k • S (x k) with hu
    have htail : u ∈ V j := by
      refine Submodule.sum_mem _ fun k hk => ?_
      by_cases hk_eq : σ k = τ k
      · rw [ha_zero k hk_eq, zero_smul]; exact Submodule.zero_mem _
      · have hkD : k ∈ D := by simp [hD, hk_eq]
        have hkj : k < j :=
          lt_of_le_of_ne (D.le_max' k hkD) (Finset.ne_of_mem_erase hk)
        exact Submodule.smul_mem _ _ (hVmem j k hkj)
    have hvec : z σ - z τ = c • (a j • (S (x j) + (a j)⁻¹ • u)) := by
      have h1 : (c • ∑ k, sgn (σ k) • x k) - (c • ∑ k, sgn (τ k) • x k)
          = c • ∑ k, a k • x k := by
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm)
      have h2 : S (c • ∑ k, a k • x k) = c • ∑ k, a k • S (x k) := by
        rw [map_smul, map_sum]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => map_smul S _ _)
      have h3 : ∑ k, a k • S (x k) = a j • S (x j) + u :=
        (Finset.add_sum_erase _ _ (Finset.mem_univ j)).symm
      have h4 : a j • (S (x j) + (a j)⁻¹ • u) = a j • S (x j) + u := by
        rw [smul_add, smul_inv_smul₀ haj_ne]
      rw [hz]
      simp only
      rw [← map_sub, h1, h2, h3, h4]
    have hinner : γ < ‖S (x j) + (a j)⁻¹ • u‖ :=
      hVgt j _ (Submodule.smul_mem _ _ htail)
    rw [dist_eq_norm, hvec, norm_smul, norm_smul, hcnorm, ha_norm j hjne]
    rw [div_eq_inv_mul, mul_comm 2 γ, ← mul_assoc]
    calc ((n : ℝ) + 1)⁻¹ * γ * 2
        ≤ ((n : ℝ) + 1)⁻¹ * (2 * ‖S (x j) + (a j)⁻¹ • u‖) := by
          rw [mul_comm 2 ‖S (x j) + (a j)⁻¹ • u‖, ← mul_assoc]
          have : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
          nlinarith [hinner.le]
      _ = ((n : ℝ) + 1)⁻¹ * (2 * ‖S (x j) + (a j)⁻¹ • u‖) := rfl
  -- Pigeonhole, then unwind the constants.
  exact absurd (le_succ_mul_of_sep hn1
    (le_entropyNumber_of_sign_family hz_mem (by positivity) hsep)) (not_le.mpr hγ1)

/-- **The entropy bound for the Gelfand numbers**: `cₙ(S) ≤ (n+1) · eₙ(S)`
(Pietsch, *Operator ideals*, 12.3.2). -/
theorem gelfandNumber_le_succ_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber S n ≤ ((n : ℝ) + 1) * entropyNumber S n := by
  classical
  by_contra hcon
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (not_le.mp hcon)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hγ0 : 0 < γ :=
    lt_of_le_of_lt (by positivity [entropyNumber_nonneg S n]) hγ1
  obtain ⟨x, ρ, hxnorm, hρnorm, hρdiag, hρtri⟩ :=
    exists_gelfand_flag S hγ0 hγ2 (n + 1) le_rfl
  have hnorm_two : ‖(2 : 𝕜)‖ = 2 := by
    rw [show (2 : 𝕜) = ((2 : ℕ) : 𝕜) by push_cast; ring, RCLike.norm_natCast]
    norm_num
  set c : 𝕜 := ((((n : ℝ) + 1)⁻¹ : ℝ) : 𝕜) with hc
  have hcnorm : ‖c‖ = ((n : ℝ) + 1)⁻¹ := by
    rw [hc, RCLike.norm_ofReal, abs_of_pos (by positivity)]
  set sgn : Bool → 𝕜 := fun b => if b then 1 else -1 with hsgn
  have hsgn_norm : ∀ b, ‖sgn b‖ = 1 := by intro b; cases b <;> simp [hsgn]
  set z : (Fin (n + 1) → Bool) → Y := fun σ => S (c • ∑ k, sgn (σ k) • x k) with hz
  have hz_mem : ∀ σ, z σ ∈ ⇑S '' Metric.closedBall 0 1 := by
    intro σ
    refine ⟨c • ∑ k, sgn (σ k) • x k, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, hcnorm]
    have h1 : ‖∑ k, sgn (σ k) • x k‖ ≤ (n : ℝ) + 1 :=
      norm_signedSum_le hxnorm fun k => le_of_eq (hsgn_norm (σ k))
    calc ((n : ℝ) + 1)⁻¹ * ‖∑ k, sgn (σ k) • x k‖
        ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hn1)
  -- Separation, now read off by the functional at the *smallest* disagreeing index.
  have hsep : ∀ σ τ, σ ≠ τ → 2 * γ / ((n : ℝ) + 1) ≤ dist (z σ) (z τ) := by
    intro σ τ hne
    set D : Finset (Fin (n + 1)) := Finset.univ.filter (fun k => σ k ≠ τ k) with hD
    have hDne : D.Nonempty := by
      obtain ⟨k, hk⟩ := Function.ne_iff.mp hne
      exact ⟨k, by simp [hD, hk]⟩
    set j := D.min' hDne with hj
    have hjne : σ j ≠ τ j := by
      have := D.min'_mem hDne
      simpa [hD, hj] using this
    set a : Fin (n + 1) → 𝕜 := fun k => sgn (σ k) - sgn (τ k) with ha
    have ha_zero : ∀ k, σ k = τ k → a k = 0 := by intro k h; simp [ha, h]
    have ha_norm : ∀ k, σ k ≠ τ k → ‖a k‖ = 2 := by
      intro k h
      have hcases : a k = 2 ∨ a k = -2 := by
        simp only [ha, hsgn]
        cases hb : σ k <;> cases hb' : τ k <;> simp [hb, hb'] at h ⊢ <;> norm_num
      rcases hcases with h2 | h2
      · rw [h2, hnorm_two]
      · rw [h2, norm_neg, hnorm_two]
    -- The functional `ρ j` sees only the `j`-th term.
    have hvec : z σ - z τ = c • ∑ k, a k • S (x k) := by
      have h1 : (c • ∑ k, sgn (σ k) • x k) - (c • ∑ k, sgn (τ k) • x k)
          = c • ∑ k, a k • x k := by
        rw [← smul_sub, ← Finset.sum_sub_distrib]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => (sub_smul _ _ _).symm)
      have h2 : S (c • ∑ k, a k • x k) = c • ∑ k, a k • S (x k) := by
        rw [map_smul, map_sum]
        exact congrArg _ (Finset.sum_congr rfl fun k _ => map_smul S _ _)
      rw [hz]
      simp only
      rw [← map_sub, h1, h2]
    have hval : ρ j (z σ - z τ) = c * (a j * ((γ : ℝ) : 𝕜)) := by
      rw [hvec, map_smul, map_sum]
      congr 1
      rw [Finset.sum_eq_single j]
      · rw [map_smul, hρdiag j, smul_eq_mul]
      · intro k _ hkj
        rcases lt_or_gt_of_ne hkj with hlt | hgt
        · -- `k < j = min D`, so `k ∉ D`, so `a k = 0`
          have hkD : k ∉ D := fun hk => absurd (D.min'_le k hk) (not_le.mpr hlt)
          have : σ k = τ k := by
            by_contra hc'
            exact hkD (by simp [hD, hc'])
          rw [map_smul, ha_zero k this, zero_smul]
        · rw [map_smul, hρtri j k hgt, smul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    -- `‖ρ j w‖ ≤ ‖w‖` turns this into the separation estimate.
    have hbound : ‖ρ j (z σ - z τ)‖ ≤ ‖z σ - z τ‖ := by
      refine ((ρ j).le_opNorm _).trans ?_
      nlinarith [hρnorm j, norm_nonneg (z σ - z τ), norm_nonneg (ρ j)]
    have hcalc : ‖ρ j (z σ - z τ)‖ = 2 * γ / ((n : ℝ) + 1) := by
      rw [hval, norm_mul, norm_mul, hcnorm, ha_norm j hjne, RCLike.norm_ofReal,
        abs_of_pos hγ0]
      field_simp
    rw [dist_eq_norm, ← hcalc]
    exact hbound
  exact absurd (le_succ_mul_of_sep hn1
    (le_entropyNumber_of_sign_family hz_mem (by positivity) hsep)) (not_le.mpr hγ1)

/-! ### Entropy numbers of the identity

Comparing volumes bounds the entropy numbers of the identity from below: a
cover of the unit ball of a `D`-dimensional space by `2 ^ n` balls of radius
`ε` forces `1 ≤ 2 ^ n · ε ^ D`, so `ε > 1/2` as soon as `D > n`. That is where
the constant `2` in the Hilbert-entropy bound comes from. -/

section Identity

open MeasureTheory

/-- **`eₙ(id_X) ≥ 1/2` whenever `dim X > n`.** Scaling a ball by `ε` scales its
volume by `ε ^ D`, so a cover of the unit ball by `2 ^ n` balls of radius `ε`
gives `1 ≤ 2 ^ n · ε ^ D`; with `ε ≤ 1/2` and `D ≥ n+1` the right-hand side
would be at most `1/2`. -/
lemma half_le_entropyNumber_id (X : Type u) [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] [FiniteDimensional 𝕜 X] {n : ℕ}
    (hn : n < Module.finrank 𝕜 X) :
    1 / 2 ≤ entropyNumber (ContinuousLinearMap.id 𝕜 X) n := by
  have : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
  have : FiniteDimensional ℝ X := FiniteDimensional.trans ℝ 𝕜 X
  -- The real dimension is at least the `𝕜`-dimension.
  have hD : n < Module.finrank ℝ X := by
    have hmul := Module.finrank_mul_finrank ℝ 𝕜 X
    have hpos : 0 < Module.finrank ℝ 𝕜 := Module.finrank_pos
    calc n < Module.finrank 𝕜 X := hn
      _ ≤ Module.finrank ℝ 𝕜 * Module.finrank 𝕜 X := Nat.le_mul_of_pos_left _ hpos
      _ = Module.finrank ℝ X := hmul
  borelize X
  set D := Module.finrank ℝ X with hDdef
  set μ : Measure X := (Module.finBasis ℝ X).addHaar with hμ
  have hμ0 : μ (Metric.closedBall (0 : X) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos μ 0 one_pos).ne'
  have hμtop : μ (Metric.closedBall (0 : X) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [entropyNumber_def]
  refine le_csInf (entropySet_nonempty _ n) fun ε hε => ?_
  by_contra hcon
  have hεhalf : ε < 1 / 2 := not_le.mp hcon
  obtain ⟨hε0, N, hNcard, hcov⟩ := hε
  rw [show ⇑(ContinuousLinearMap.id 𝕜 X) '' Metric.closedBall 0 1
      = Metric.closedBall (0 : X) 1 by simp] at hcov
  -- Volume comparison.
  have h1 : μ (Metric.closedBall (0 : X) 1)
      ≤ ∑ _y ∈ N, ENNReal.ofReal (ε ^ D) * μ (Metric.closedBall (0 : X) 1) := by
    refine (measure_mono hcov).trans ?_
    refine (measure_biUnion_finset_le N _).trans ?_
    exact Finset.sum_le_sum fun y _ =>
      le_of_eq (Measure.addHaar_closedBall' μ y hε0.le)
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at h1
  -- Pass to real numbers, where the common factor `vol B` can be cancelled.
  have hfin : (N.card : ℝ≥0∞) * ENNReal.ofReal (ε ^ D)
      * μ (Metric.closedBall (0 : X) 1) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top) hμtop
  have hBpos : 0 < μ.real (Metric.closedBall (0 : X) 1) :=
    ENNReal.toReal_pos hμ0 hμtop
  have h2 : μ.real (Metric.closedBall (0 : X) 1)
      ≤ (N.card : ℝ) * ε ^ D * μ.real (Metric.closedBall (0 : X) 1) := by
    have h := ENNReal.toReal_mono hfin h1
    simpa [Measure.real, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ ε ^ D)] using h
  have h3 : (1 : ℝ) ≤ (N.card : ℝ) * ε ^ D := by nlinarith [h2, hBpos]
  -- But `N.card ≤ 2 ^ n` and `ε < 1/2` make the right-hand side at most `1/2`.
  have h4 : (N.card : ℝ) * ε ^ D ≤ 2 ^ n * ε ^ D := by
    have hcard : (N.card : ℝ) ≤ 2 ^ n := by exact_mod_cast hNcard
    have hpow : (0 : ℝ) ≤ ε ^ D := by positivity
    nlinarith
  have h5 : ε ^ D ≤ (1 / 2 : ℝ) ^ (n + 1) := by
    obtain ⟨d, hd⟩ : ∃ d, D = (n + 1) + d := ⟨D - (n + 1), by omega⟩
    have hεle1 : ε ≤ 1 := by linarith
    rw [hd, pow_add]
    calc ε ^ (n + 1) * ε ^ d ≤ ε ^ (n + 1) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hε0.le hεle1) (by positivity)
      _ = ε ^ (n + 1) := mul_one _
      _ ≤ (1 / 2 : ℝ) ^ (n + 1) := pow_le_pow_left₀ hε0.le hεhalf.le _
  have h6 : (2 : ℝ) ^ n * ((1 : ℝ) / 2) ^ (n + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]
    norm_num
  nlinarith [h3, h4, h5, h6, pow_pos hε0 D]

end Identity

/-- **Pietsch 12.3.2**: `max(cₙ(S), dₙ(S)) ≤ (n+1) · eₙ(S)`. -/
theorem max_gelfandNumber_kolmogorovNumber_le_succ_mul_entropyNumber
    (S : X →L[𝕜] Y) (n : ℕ) :
    max (gelfandNumber S n) (kolmogorovNumber S n) ≤
      ((n : ℝ) + 1) * entropyNumber S n :=
  max_le (gelfandNumber_le_succ_mul_entropyNumber S n)
    (kolmogorovNumber_le_succ_mul_entropyNumber S n)

/-! ### The Hilbert-entropy bound

The Hilbert numbers are the *smallest* `s`-number sequence, and they are also
smaller than twice the entropy numbers. This essentially follows from
`eₙ(id) ≥ 1/2`. -/

section Hilbert

variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- **`aₙ(T) ≤ 2·eₙ(T)` between Hilbert spaces.** For `γ < aₙ(T)` the scalar
factorisation gives contractions with `B ∘ T ∘ A = γ · id` on `ℓ₂ⁿ⁺¹`; rescaling
`B` by `γ⁻¹` makes the composition the identity, so
`1/2 ≤ eₙ(id) ≤ γ⁻¹ · eₙ(T)`. -/
theorem approximationNumber_le_two_mul_entropyNumber (T : H₁ →L[𝕜] H₂) (n : ℕ) :
    approximationNumber T n ≤ 2 * entropyNumber T n := by
  by_contra hcon
  obtain ⟨γ, hγ1, hγ2⟩ := exists_between (not_le.mp hcon)
  have hγ0 : 0 < γ :=
    lt_of_le_of_lt (by positivity [entropyNumber_nonneg T n]) hγ1
  obtain ⟨A, B, hA, hB, hfact⟩ := SVD.exists_scalar_factorisation T n hγ0.le hγ2
  have hγ𝕜 : ((γ : ℝ) : 𝕜) ≠ 0 := by
    simpa using (RCLike.ofReal_ne_zero (K := 𝕜)).mpr (ne_of_gt hγ0)
  -- Rescale `B` so that the composition is exactly the identity.
  set B' : H₂ →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1)) := (((γ : ℝ) : 𝕜)⁻¹) • B with hB'
  have hcomp : B'.comp (T.comp A) =
      ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [hB', ContinuousLinearMap.smul_comp, hfact, smul_smul,
      inv_mul_cancel₀ hγ𝕜, one_smul]
  have hB'norm : ‖B'‖ ≤ γ⁻¹ := by
    rw [hB', norm_smul, norm_inv, RCLike.norm_ofReal, abs_of_pos hγ0]
    calc γ⁻¹ * ‖B‖ ≤ γ⁻¹ * 1 :=
          mul_le_mul_of_nonneg_left hB (by positivity)
      _ = γ⁻¹ := mul_one _
  -- The identity on `ℓ₂ⁿ⁺¹` has entropy numbers at least `1/2`.
  have hid : 1 / 2 ≤ entropyNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n := by
    refine half_le_entropyNumber_id _ ?_
    rw [finrank_euclideanSpace_fin']
    exact Nat.lt_succ_self n
  rw [← hcomp] at hid
  have hchain : entropyNumber (B'.comp (T.comp A)) n ≤ γ⁻¹ * entropyNumber T n := by
    have h0 : (0 : ℝ) ≤ entropyNumber T n := entropyNumber_nonneg T n
    calc entropyNumber (B'.comp (T.comp A)) n
        ≤ ‖B'‖ * entropyNumber T n * ‖A‖ := entropyNumber_comp_comp_le B' T A n
      _ ≤ γ⁻¹ * entropyNumber T n * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_right hB'norm h0) hA (norm_nonneg A)
            (mul_nonneg (inv_pos.mpr hγ0).le h0)
      _ = γ⁻¹ * entropyNumber T n := mul_one _
  have hfinal : γ ≤ 2 * entropyNumber T n := by
    have h1 : 1 / 2 ≤ γ⁻¹ * entropyNumber T n := hid.trans hchain
    have h2 : γ * γ⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hγ0)
    nlinarith [h1, h2, hγ0, entropyNumber_nonneg T n]
  linarith

end Hilbert

/-- **The Hilbert-entropy bound** `hₙ(S) ≤ 2·eₙ(S)`, for operators between
arbitrary Banach spaces. Every factorisation `B ∘ S ∘ A` over `ℓ₂` satisfies
`aₙ(B∘S∘A) ≤ 2·eₙ(B∘S∘A) ≤ 2·‖B‖·eₙ(S)·‖A‖`, and `hₙ` is the supremum of
`aₙ(B∘S∘A)/(‖B‖‖A‖)`. -/
theorem hilbertNumber_le_two_mul_entropyNumber (S : X →L[𝕜] Y) (n : ℕ) :
    hilbertNumber S n ≤ 2 * entropyNumber S n := by
  rw [hilbertNumber_def]
  refine Real.sSup_le ?_ (by positivity [entropyNumber_nonneg S n])
  rintro r ⟨A, B, hA, hB, rfl⟩
  have hpos : 0 < ‖B‖ * ‖A‖ := mul_pos (norm_pos_iff.mpr hB) (norm_pos_iff.mpr hA)
  rw [div_le_iff₀ hpos]
  calc approximationNumber (B.comp (S.comp A)) n
      ≤ 2 * entropyNumber (B.comp (S.comp A)) n :=
        approximationNumber_le_two_mul_entropyNumber _ n
    _ ≤ 2 * (‖B‖ * entropyNumber S n * ‖A‖) := by
        have := entropyNumber_comp_comp_le B S A n
        linarith
    _ = 2 * entropyNumber S n * (‖B‖ * ‖A‖) := by ring

end SNumbers


/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
