/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.AddOns.Approximable
import LeanPool.SNumbers.BasicResults.SVD
import LeanPool.SNumbers.SNumbers.EntropyBounds
import LeanPool.SNumbers.SNumbers.Uniqueness

/-!
# Compactness measured by `s`-numbers

Which `s`-number sequences detect compactness? The answer separates the
sequences sharply, and this file collects the whole picture.

## The general Banach case: `cₙ` and `dₙ`

For the **Gelfand** and **Kolmogorov** numbers, decay to zero is equivalent to
compactness over any Banach space:

`S` is a compact operator ↔ `cₙ(S) → 0` ↔ `dₙ(S) → 0`.

Both proofs run through total boundedness of `S(B_X)`, exactly as the entropy
criterion `SNumbers.isCompactOperator_iff_tendsto_entropyNumber` does.

* *Compactness implies decay.* A totally bounded image has, for every `ε`, a
  finite `ε`-net; the covering estimates of `SNumbers.EntropyBounds` turn a net
  with `k` points into the bounds `d_k(S) ≤ ε` and `c_k(S) ≤ 2ε`, and both
  sequences are antitone.
* *Decay implies compactness.* For the Kolmogorov numbers, `dₙ(S) < ε` puts
  `S(B_X)` within `ε` of a bounded piece of a finite-dimensional subspace of
  `Y`, which is totally bounded. For the Gelfand numbers, `cₙ(S) < ε` gives a
  closed `M ⊆ X` of finite codimension with `‖S|_M‖ < ε`; the image of `B_X` in
  the *finite-dimensional quotient* `X ⧸ M` is totally bounded, and lifting a
  finite `δ`-net of it back to `B_X` produces a finite net for `S(B_X)`.

The second half of the Gelfand argument deserves a comment, because the obvious
alternative fails. One would like to split `x` along `X = M ⊕ F` with `F`
finite-dimensional, but a projection with kernel `M` only satisfies
`‖x - P x‖ ≤ (1 + √n)‖x‖` (Garling–Gordon), and `(1 + √n)·cₙ(S)` need not tend
to `0`. Working in the quotient avoids any projection: a lifted difference
`x - uⱼ` is corrected by some `m ∈ M` with `‖m‖ ≤ 2 + δ`, a bound **independent
of the codimension** `n`.

## The approximation numbers are different

`aₙ(S) → 0` — that is, `SVD.IsApproximable S` — always implies compactness, but
the converse fails on a Banach space without the approximation property (Enflo,
1973): there are compact operators that are not norm limits of finite-rank
operators. On Hilbert spaces the Schmidt representation repairs this, and then
*every* `s`-number sequence detects compactness, since all of them agree with
`aₙ` there (`SNumbers.allSNumbers_eq_on_HilbertSpace`).

## Main results

* `SNumbers.isCompactOperator_iff_totallyBounded_image_closedBall` — the bridge
  between `IsCompactOperator` and total boundedness of `S(B_X)`.
* `SNumbers.isCompactOperator_iff_tendsto_kolmogorovNumber`,
  `SNumbers.isCompactOperator_iff_tendsto_gelfandNumber` — the two criteria.
* `SNumbers.tendsto_kolmogorovNumber_iff_totallyBounded`,
  `SNumbers.tendsto_gelfandNumber_iff_totallyBounded` — the same statements
  without any completeness assumption on the target space.
* `SVD.IsCompactOperator.isApproximable`,
  `SVD.isApproximable_iff_isCompactOperator` — compact ↔ approximable on
  Hilbert spaces.
* `SVD.isCompactOperator_iff_tendsto_sn` — on Hilbert spaces, compactness is
  equivalent to `sₙ(S) → 0` for *every* `s`-number sequence `s`.

## References

* A. Pietsch, *Eigenvalues and s-numbers*, Cambridge Studies in Advanced
  Mathematics 13, Cambridge University Press, 1987,
  [link](https://zbmath.org/3996455), §2.11.
* A. Pietsch, *Operator ideals*, North-Holland Mathematical Library 20,
  North-Holland, 1980, [doi](<https://doi.org/10.1016/S0924-6509(09)X7001-7>),
  12.3.
-/

universe u

open Filter Topology
open scoped Cardinal

namespace SNumbers

/-! ### Compactness and total boundedness -/

section TotallyBounded

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- A compact operator maps the closed unit ball to a totally bounded set. -/
lemma totallyBounded_image_closedBall_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  (tendsto_entropyNumber_iff_totallyBounded S).mp
    (tendsto_entropyNumber_of_isCompactOperator hS)

/-- Conversely, if `S(B_X)` is totally bounded and `Y` is complete, then `S` is
a compact operator: the closure of a totally bounded set is then compact. -/
lemma isCompactOperator_of_totallyBounded_image_closedBall [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    IsCompactOperator S :=
  isCompactOperator_of_tendsto_entropyNumber
    ((tendsto_entropyNumber_iff_totallyBounded S).mpr hS)

/-- For a complete target space, compactness of `S` is total boundedness of
`S(B_X)`. -/
theorem isCompactOperator_iff_totallyBounded_image_closedBall [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  ⟨totallyBounded_image_closedBall_of_isCompactOperator,
    isCompactOperator_of_totallyBounded_image_closedBall⟩

/-- A totally bounded set has, for every `ε > 0`, a finite `ε`-net presented as
a function `Fin k → Y`. This is the form consumed by the covering estimates
`kolmogorovNumber_le_of_fin_net` and `gelfandNumber_le_two_mul_of_fin_net`. -/
private lemma exists_fin_net_of_totallyBounded {s : Set Y} (hs : TotallyBounded s)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (y : Fin k → Y), ∀ z ∈ s, ∃ i, ‖z - y i‖ ≤ ε := by
  classical
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hs ε hε
  have : Fintype ↥t := ht_fin.fintype
  refine ⟨Fintype.card ↥t,
    fun i => (((Fintype.equivFin ↥t).symm i : ↥t) : Y), fun z hz => ?_⟩
  have hmem := ht_cov hz
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hdist⟩ := hmem
  refine ⟨Fintype.equivFin ↥t ⟨w, hw⟩, ?_⟩
  simp only [Equiv.symm_apply_apply]
  exact le_of_lt (by rwa [← dist_eq_norm])

end TotallyBounded

/-! ### The Kolmogorov numbers -/

section Kolmogorov

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `S(B_X)` is totally bounded then `dₙ(S) → 0`: a finite `ε/2`-net with `k`
points bounds `d_k(S)` by `ε/2`, and `dₙ` is antitone. -/
theorem tendsto_kolmogorovNumber_of_totallyBounded {S : X →L[𝕜] Y}
    (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    Tendsto (kolmogorovNumber S) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, y, hnet⟩ := exists_fin_net_of_totallyBounded hS (half_pos hε)
  have hk : kolmogorovNumber S k ≤ ε / 2 :=
    kolmogorovNumber_le_of_fin_net fun x hx =>
      hnet (S x) ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  refine ⟨k, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (kolmogorovNumber_nonneg S n)]
  calc kolmogorovNumber S n
      ≤ kolmogorovNumber S k := kolmogorovNumber_antitone' S hn
    _ ≤ ε / 2 := hk
    _ < ε := by linarith

/-- If `dₙ(S) → 0` then `S(B_X)` is totally bounded.

Given `η > 0`, choose `V` of dimension `≤ n` with `‖π_V ∘ S‖ < η/3`. Every
`S x` with `‖x‖ ≤ 1` is then within `η/3` of a point of `V` of norm at most
`‖S‖ + η/3`; that bounded piece of the finite-dimensional space `V` is compact,
so a finite `η/3`-net of it turns into a finite `η`-net of `S(B_X)`. -/
theorem totallyBounded_of_tendsto_kolmogorovNumber {S : X →L[𝕜] Y}
    (hS : Tendsto (kolmogorovNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  refine Metric.totallyBounded_iff.mpr fun η hη => ?_
  have hε : 0 < η / 3 := by positivity
  obtain ⟨n, hn⟩ := (hS.eventually_lt_const hε).exists
  obtain ⟨-, ⟨V, hV_rank, rfl⟩, hV_lt⟩ :=
    exists_lt_of_csInf_lt (kolmogorovSet_nonempty S n) hn
  have : FiniteDimensional 𝕜 V :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hV_rank (Cardinal.natCast_lt_aleph0))
  -- Every point of `S(B_X)` is `η/3`-close to a point of `V` of norm `≤ ‖S‖ + η/3`.
  have hVne : (V : Set Y).Nonempty := ⟨0, V.zero_mem⟩
  have key : ∀ x : X, ‖x‖ ≤ 1 →
      ∃ v : Y, v ∈ V ∧ ‖v‖ ≤ ‖S‖ + η / 3 ∧ ‖S x - v‖ < η / 3 := by
    intro x hx
    have hop : ‖V.mkQL (S x)‖ ≤ deviationFromSubspace S V := by
      simpa [deviationFromSubspace] using (V.mkQL.comp S).unit_le_opNorm x hx
    have h1 : ‖V.mkQL (S x)‖ < η / 3 := lt_of_le_of_lt hop hV_lt
    have heq : ‖V.mkQL (S x)‖ = Metric.infDist (S x) V :=
      QuotientAddGroup.norm_mk (S := V.toAddSubgroup) (S x)
    rw [heq] at h1
    obtain ⟨v, hv, hdv⟩ := (Metric.infDist_lt_iff hVne).mp h1
    rw [dist_eq_norm] at hdv
    refine ⟨v, hv, ?_, hdv⟩
    have hSx : ‖S x‖ ≤ ‖S‖ := S.unit_le_opNorm x hx
    have hvx : ‖v - S x‖ ≤ η / 3 := by rw [norm_sub_rev]; exact hdv.le
    have hveq : S x + (v - S x) = v := by abel
    calc ‖v‖ = ‖S x + (v - S x)‖ := by rw [hveq]
      _ ≤ ‖S x‖ + ‖v - S x‖ := norm_add_le _ _
      _ ≤ ‖S‖ + η / 3 := add_le_add hSx hvx
  -- The relevant piece of `V` is compact, hence has a finite `η/3`-net.
  have hK : TotallyBounded
      (⇑V.subtypeL '' Metric.closedBall (0 : V) (‖S‖ + η / 3)) :=
    ((isCompact_closedBall (0 : V) (‖S‖ + η / 3)).image
      V.subtypeL.continuous).totallyBounded
  obtain ⟨t, ht_fin, ht_cov⟩ := Metric.totallyBounded_iff.mp hK (η / 3) hε
  refine ⟨t, ht_fin, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨v, hv_mem, hv_norm, hv_dist⟩ := key x (mem_closedBall_zero_iff.mp hx)
  have hvK : v ∈ ⇑V.subtypeL '' Metric.closedBall (0 : V) (‖S‖ + η / 3) :=
    ⟨⟨v, hv_mem⟩, by simpa using hv_norm, rfl⟩
  have hmem := ht_cov hvK
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hwd⟩ := hmem
  refine Set.mem_biUnion hw ?_
  have : dist (S x) w ≤ dist (S x) v + dist v w := dist_triangle _ _ _
  rw [Metric.mem_ball, dist_eq_norm] at *
  calc ‖S x - w‖ ≤ ‖S x - v‖ + ‖v - w‖ := by
        simpa [dist_eq_norm] using dist_triangle (S x) v w
    _ < η / 3 + η / 3 := add_lt_add hv_dist hwd
    _ < η := by linarith

/-- **`dₙ(S) → 0` characterises total boundedness of `S(B_X)`.** No completeness
assumption is needed. -/
theorem tendsto_kolmogorovNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (kolmogorovNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  ⟨totallyBounded_of_tendsto_kolmogorovNumber,
    tendsto_kolmogorovNumber_of_totallyBounded⟩

/-- A compact operator has Kolmogorov numbers tending to zero. -/
theorem tendsto_kolmogorovNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) : Tendsto (kolmogorovNumber S) atTop (𝓝 0) :=
  tendsto_kolmogorovNumber_of_totallyBounded
    (totallyBounded_image_closedBall_of_isCompactOperator hS)

/-- Kolmogorov numbers tending to zero force compactness, provided the target
space is complete. -/
theorem isCompactOperator_of_tendsto_kolmogorovNumber [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (kolmogorovNumber S) atTop (𝓝 0)) :
    IsCompactOperator S :=
  isCompactOperator_of_totallyBounded_image_closedBall
    (totallyBounded_of_tendsto_kolmogorovNumber hS)

/-- **Compactness is measured by the Kolmogorov numbers**: for a complete target
space, `S` is a compact operator if and only if `dₙ(S) → 0`. -/
theorem isCompactOperator_iff_tendsto_kolmogorovNumber [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (kolmogorovNumber S) atTop (𝓝 0) :=
  ⟨tendsto_kolmogorovNumber_of_isCompactOperator,
    isCompactOperator_of_tendsto_kolmogorovNumber⟩

end Kolmogorov

/-! ### The Gelfand numbers -/

section Gelfand

variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- If `S(B_X)` is totally bounded then `cₙ(S) → 0`: a finite `ε/3`-net with `k`
points bounds `c_k(S)` by `2ε/3`, and `cₙ` is antitone. -/
theorem tendsto_gelfandNumber_of_totallyBounded {S : X →L[𝕜] Y}
    (hS : TotallyBounded (⇑S '' Metric.closedBall 0 1)) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨k, y, hnet⟩ := exists_fin_net_of_totallyBounded hS hε3
  have hk : gelfandNumber S k ≤ 2 * (ε / 3) :=
    gelfandNumber_le_two_mul_of_fin_net fun x hx =>
      hnet (S x) ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
  refine ⟨k, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (gelfandNumber_nonneg S n)]
  calc gelfandNumber S n
      ≤ gelfandNumber S k := gelfandNumber_antitone' S hn
    _ ≤ 2 * (ε / 3) := hk
    _ < ε := by linarith

/-- If `cₙ(S) → 0` then `S(B_X)` is totally bounded.

Given `η > 0`, choose a closed `M` of finite codimension with `‖S|_M‖ < η/6`.
The image of `B_X` in the finite-dimensional quotient `X ⧸ M` is bounded, hence
totally bounded; pick a finite `δ`-net of it *inside the image* and lift the
centres to `u₁, …, u_N ∈ B_X`. For `‖x‖ ≤ 1` with `‖[x] - [uⱼ]‖ < δ` there is
`m ∈ M` with `‖(x - uⱼ) - m‖ < δ`, and — this is the crux — `‖m‖ ≤ 2 + δ ≤ 3`
independently of the codimension. Hence
`‖S x - S uⱼ‖ ≤ ‖S m‖ + ‖S‖·δ < 3·(η/6) + η/2 = η`. -/
theorem totallyBounded_of_tendsto_gelfandNumber {S : X →L[𝕜] Y}
    (hS : Tendsto (gelfandNumber S) atTop (𝓝 0)) :
    TotallyBounded (⇑S '' Metric.closedBall 0 1) := by
  classical
  refine Metric.totallyBounded_iff.mpr fun η hη => ?_
  have hε : 0 < η / 6 := by positivity
  have hpos : (0 : ℝ) < ‖S‖ + 1 := by positivity
  have hne : (‖S‖ + 1) ≠ 0 := ne_of_gt hpos
  set δ : ℝ := min 1 ((η / 2) / (‖S‖ + 1)) with hδ_def
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδS : ‖S‖ * δ ≤ η / 2 := by
    have h1 : δ ≤ (η / 2) / (‖S‖ + 1) := min_le_right _ _
    calc ‖S‖ * δ ≤ (‖S‖ + 1) * δ := by nlinarith [hδ.le]
      _ ≤ (‖S‖ + 1) * ((η / 2) / (‖S‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1 hpos.le
      _ = η / 2 := by field_simp
  -- A closed subspace of finite codimension on which `S` is small.
  obtain ⟨n, hn⟩ := (hS.eventually_lt_const hε).exists
  obtain ⟨-, ⟨M, hM_closed, hM_rank, rfl⟩, hM_lt⟩ :=
    exists_lt_of_csInf_lt (gelfandSet_nonempty S n) hn
  have : IsClosed (M : Set X) := hM_closed
  have : FiniteDimensional 𝕜 (X ⧸ M) :=
    Module.rank_lt_aleph0_iff.mp (lt_of_le_of_lt hM_rank (Cardinal.natCast_lt_aleph0))
  have : ProperSpace (X ⧸ M) := FiniteDimensional.proper 𝕜 (X ⧸ M)
  -- The image of the unit ball in the finite-dimensional quotient.
  have hq : TotallyBounded (⇑M.mkQL '' Metric.closedBall (0 : X) 1) := by
    refine TotallyBounded.subset ?_
      (isCompact_closedBall (0 : X ⧸ M) 1).totallyBounded
    rintro _ ⟨x, hx, rfl⟩
    simpa using (M.norm_mkQL_apply_le x).trans (mem_closedBall_zero_iff.mp hx)
  obtain ⟨t, ht_sub, ht_fin, ht_cov⟩ := Metric.finite_approx_of_totallyBounded hq δ hδ
  -- Lift the centres of the net back to the unit ball of `X`.
  have hpre : ∀ w : X ⧸ M, w ∈ t → ∃ u : X, ‖u‖ ≤ 1 ∧ M.mkQL u = w := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := ht_sub hw
    exact ⟨u, mem_closedBall_zero_iff.mp hu, rfl⟩
  choose! u hu_norm hu_eq using hpre
  refine ⟨(fun w => S (u w)) '' t, ht_fin.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp hx
  -- Find a net point close to `[x]`.
  have hmem := ht_cov ⟨x, hx, rfl⟩
  simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hmem
  obtain ⟨w, hw, hwd⟩ := hmem
  -- Correct `x - u w` by an element of `M`.
  have hMne : (M : Set X).Nonempty := ⟨0, M.zero_mem⟩
  have hquot : ‖M.mkQL (x - u w)‖ < δ := by
    rw [map_sub, hu_eq w hw, ← dist_eq_norm]
    exact hwd
  have heq : ‖M.mkQL (x - u w)‖ = Metric.infDist (x - u w) M :=
    QuotientAddGroup.norm_mk (S := M.toAddSubgroup) (x - u w)
  rw [heq] at hquot
  obtain ⟨m, hm_mem, hmd⟩ := (Metric.infDist_lt_iff hMne).mp hquot
  rw [dist_eq_norm] at hmd
  -- `‖m‖ ≤ 2 + δ ≤ 3`, independently of the codimension of `M`.
  have hm_norm : ‖m‖ ≤ 3 := by
    have h1 : ‖x - u w‖ ≤ 2 := by
      calc ‖x - u w‖ ≤ ‖x‖ + ‖u w‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add hx1 (hu_norm w hw)
        _ = 2 := by norm_num
    calc ‖m‖ ≤ ‖x - u w‖ + ‖(x - u w) - m‖ := by
          simpa using norm_sub_le (x - u w) ((x - u w) - m)
      _ ≤ 2 + δ := add_le_add h1 hmd.le
      _ ≤ 3 := by linarith
  -- `S m` is small because `m ∈ M`.
  -- Strictly less than `η/2`: the deviation is *strictly* below `η/6`.
  have hSm : ‖S m‖ < η / 2 := by
    have h1 : ‖S m‖ ≤ deviationFromRestriction S M * ‖m‖ := by
      have := (S.comp M.subtypeL).le_opNorm ⟨m, hm_mem⟩
      simpa [deviationFromRestriction] using this
    have h2 : (0 : ℝ) ≤ deviationFromRestriction S M :=
      deviationFromRestriction_nonneg S M
    calc ‖S m‖ ≤ deviationFromRestriction S M * ‖m‖ := h1
      _ ≤ deviationFromRestriction S M * 3 := mul_le_mul_of_nonneg_left hm_norm h2
      _ < (η / 6) * 3 := mul_lt_mul_of_pos_right hM_lt (by norm_num)
      _ = η / 2 := by ring
  refine Set.mem_biUnion ⟨w, hw, rfl⟩ ?_
  rw [Metric.mem_ball, dist_eq_norm]
  -- `S x - S (u w) = S m + S ((x - u w) - m)`.
  have hsplit : S x - S (u w) = S m + S ((x - u w) - m) := by
    rw [map_sub, map_sub]; abel
  have hSrest : ‖S ((x - u w) - m)‖ ≤ ‖S‖ * δ :=
    (S.le_opNorm _).trans (mul_le_mul_of_nonneg_left hmd.le (norm_nonneg _))
  calc ‖S x - S (u w)‖
      = ‖S m + S ((x - u w) - m)‖ := by rw [hsplit]
    _ ≤ ‖S m‖ + ‖S ((x - u w) - m)‖ := norm_add_le _ _
    _ < η := by linarith

/-- **`cₙ(S) → 0` characterises total boundedness of `S(B_X)`.** No completeness
assumption is needed. -/
theorem tendsto_gelfandNumber_iff_totallyBounded (S : X →L[𝕜] Y) :
    Tendsto (gelfandNumber S) atTop (𝓝 0) ↔
      TotallyBounded (⇑S '' Metric.closedBall 0 1) :=
  ⟨totallyBounded_of_tendsto_gelfandNumber, tendsto_gelfandNumber_of_totallyBounded⟩

/-- A compact operator has Gelfand numbers tending to zero. -/
theorem tendsto_gelfandNumber_of_isCompactOperator {S : X →L[𝕜] Y}
    (hS : IsCompactOperator S) : Tendsto (gelfandNumber S) atTop (𝓝 0) :=
  tendsto_gelfandNumber_of_totallyBounded
    (totallyBounded_image_closedBall_of_isCompactOperator hS)

/-- Gelfand numbers tending to zero force compactness, provided the target space
is complete. -/
theorem isCompactOperator_of_tendsto_gelfandNumber [CompleteSpace Y]
    {S : X →L[𝕜] Y} (hS : Tendsto (gelfandNumber S) atTop (𝓝 0)) :
    IsCompactOperator S :=
  isCompactOperator_of_totallyBounded_image_closedBall
    (totallyBounded_of_tendsto_gelfandNumber hS)

/-- **Compactness is measured by the Gelfand numbers**: for a complete target
space, `S` is a compact operator if and only if `cₙ(S) → 0`. -/
theorem isCompactOperator_iff_tendsto_gelfandNumber [CompleteSpace Y]
    (S : X →L[𝕜] Y) :
    IsCompactOperator S ↔ Tendsto (gelfandNumber S) atTop (𝓝 0) :=
  ⟨tendsto_gelfandNumber_of_isCompactOperator,
    isCompactOperator_of_tendsto_gelfandNumber⟩

end Gelfand

end SNumbers

/-! ### Hilbert spaces: every `s`-number sequence -/

namespace SVD

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H₁ H₂ : Type u}
variable [NormedAddCommGroup H₁] [InnerProductSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [InnerProductSpace 𝕜 H₂] [CompleteSpace H₂]

/-- On Hilbert spaces, every compact operator is approximable. The singular
value decomposition `IsCompactOperator.schmidtRepresentation` produces singular values `σₙ → 0`
which, by Eckart–Young (`svd_sigma_eq_approx`), equal the approximation numbers
`aₙ(S)`; hence `aₙ(S) → 0`. -/
theorem IsCompactOperator.isApproximable {S : H₁ →L[𝕜] H₂}
    (hS : IsCompactOperator S) :
    IsApproximable S := by
  obtain ⟨σ, u, v, hσ0, hσanti, hu, hv, hut, hvt, hσlim, hsum⟩ :=
    IsCompactOperator.schmidtRepresentation hS
  exact (Filter.tendsto_congr fun n =>
    (svd_sigma_eq_approx hσ0 hσanti hu hv hut hvt hsum n).symm).mpr hσlim

/-- On Hilbert spaces, approximable and compact operators coincide. -/
theorem isApproximable_iff_isCompactOperator (S : H₁ →L[𝕜] H₂) :
    IsApproximable S ↔ IsCompactOperator S :=
  ⟨IsApproximable.isCompactOperator, IsCompactOperator.isApproximable⟩

/-- **On Hilbert spaces every `s`-number sequence detects compactness.** All
`s`-number sequences agree with the approximation numbers there
(`SNumbers.allSNumbers_eq_on_HilbertSpace`), and `aₙ(S) → 0` is equivalent to
compactness by `isApproximable_iff_isCompactOperator`.

This fails on general Banach spaces for `s = aₙ` (Enflo), which is why the
Gelfand and Kolmogorov criteria in `SNumbers` are the ones stated there. -/
theorem isCompactOperator_iff_tendsto_sn {s : SNumbers.Family 𝕜}
    (hs : SNumbers.IsSNumberSequence s) (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (fun n => s S n) atTop (𝓝 0) :=
  (isApproximable_iff_isCompactOperator S).symm.trans
    (Filter.tendsto_congr fun n =>
      SNumbers.allSNumbers_eq_on_HilbertSpace hs S n).symm

/-- Hilbert-space case: compactness is equivalent to `bₙ(S) → 0`. On a general
Banach space only the forward implication holds. -/
theorem isCompactOperator_iff_tendsto_bernsteinNumber (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (SNumbers.bernsteinNumber S) atTop (𝓝 0) :=
  isCompactOperator_iff_tendsto_sn SNumbers.isSNumberSequence_bernsteinNumber S

/-- Hilbert-space case: compactness is equivalent to `hₙ(S) → 0`, even though
the Hilbert numbers are the *smallest* `s`-number sequence. -/
theorem isCompactOperator_iff_tendsto_hilbertNumber (S : H₁ →L[𝕜] H₂) :
    IsCompactOperator S ↔ Tendsto (SNumbers.hilbertNumber S) atTop (𝓝 0) :=
  isCompactOperator_iff_tendsto_sn SNumbers.isSNumberSequence_hilbertNumber S

end SVD

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
