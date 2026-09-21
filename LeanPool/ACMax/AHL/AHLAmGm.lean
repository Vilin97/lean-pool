/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
import LeanPool.ACMax.AHL.AHLMarginals
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The AHL weighted AM–GM and the degree convexity — nodes W6–W8

This file lands nodes **W6–W8** of the Alon–Hoory–Linial irregular-Moore walk-count proof, the
analytic heart of the ladder.  Building on the exact weighted marginals of `AHL.AHLMarginals`
(`nbWeightTotal_eq = D`, `nbEndWeight_eq_degree = deg v`) and the walk-weight vocabulary of
`AHL.AHLStationary`, it packages the three moves that turn the degree-bias identity into the
average-degree walk-count lower bound.

## Contents

* **W6 — the entropy recursion.**  `nbEntropy G k = ∑_{walks} wt·log wt⁻¹`.  Its exact one-step
  recursion `nbEntropy_succ` (`T_{k+1} = T_k + ∑_v deg v · log(deg v − 1)`) collapses via the end
  marginal (W4) to the closed form `nbEntropy_eq : nbEntropy G ℓ = (ℓ − 1)·∑_v deg v·log(deg v −
  1)`.
* **W7 — the single AM–GM** (`nb_amgm`).  One application of `Real.geom_mean_le_arith_mean_weighted`
  with weights `wt/D` and values `D/wt` gives `D·exp(nbEntropy G k / D) ≤ mₖ`, the geometric-mean
  lower bound on the walk count.  Repackaged in the sharp `Λ`-form `nb_amgm_lambda`
  (`D·Λ^(ℓ−1) ≤ mₗ`, `Λ = ∏_v (deg v − 1)^(deg v/D)`, AHL Note 3).
* **W8 — the degree convexity** (`sum_deg_mul_log_ge`, `lambda_ge`).  The function
  `x ↦ x·log(x − 1)` is convex on `[2, ∞)` (`convexOn_deg_mul_log`, `f'' = (x−2)/(x−1)² ≥ 0`);
  Jensen
  with uniform weights `1/n` at the degrees yields `D·log((D − n)/n) ≤ ∑_v deg v·log(deg v − 1)`,
  i.e. `Λ ≥ (D − n)/n = d_avg − 1`.
-/

namespace ACMax

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} [DecidableEq V] [DecidableRel G.Adj]

/-! ### W8 — the degree convexity -/

/-- **The AHL convexity** (W8 core).  The function `φ(x) = x·log(x − 1)` is convex on `[2, ∞)`.
Its second derivative is `φ''(x) = (x − 2)/(x − 1)² ≥ 0` there; we feed the explicit first and
second
derivatives to `convexOn_of_hasDerivWithinAt2_nonneg`. -/
theorem convexOn_deg_mul_log :
    ConvexOn ℝ (Set.Ici (2 : ℝ)) (fun x => x * Real.log (x - 1)) := by
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici 2)
    (f' := fun x => Real.log (x - 1) + x * (x - 1)⁻¹)
    (f'' := fun x => (x - 2) / (x - 1) ^ 2)
  · -- continuity on `Ici 2`
    refine ContinuousOn.mul continuousOn_id ?_
    intro x hx
    simp only [Set.mem_Ici] at hx
    exact (Real.continuousAt_log (by linarith)).comp_continuousWithinAt
      (continuousWithinAt_id.sub continuousWithinAt_const)
  · -- first derivative on the interior
    intro x hx
    rw [interior_Ici] at hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (x : ℝ) - 1 ≠ 0 := by linarith
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
    have hlog : HasDerivAt (fun y => Real.log (y - 1)) ((x - 1)⁻¹) x := by
      have h := (hid.sub_const 1).log hx1
      simp only [one_div] at h
      exact h
    have hf : HasDerivAt (fun y => y * Real.log (y - 1))
        (Real.log (x - 1) + x * (x - 1)⁻¹) x := by
      have h := hid.mul hlog
      simp only [one_mul] at h
      exact h
    exact hf.hasDerivWithinAt
  · -- second derivative on the interior
    intro x hx
    rw [interior_Ici] at hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (x : ℝ) - 1 ≠ 0 := by linarith
    have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
    have hlog : HasDerivAt (fun y => Real.log (y - 1)) ((x - 1)⁻¹) x := by
      have h := (hid.sub_const 1).log hx1
      simp only [one_div] at h
      exact h
    have hinv : HasDerivAt (fun y : ℝ => (y - 1)⁻¹) (-1 / (x - 1) ^ 2) x :=
      (hid.sub_const 1).inv hx1
    have hmul : HasDerivAt (fun y => y * (y - 1)⁻¹)
        (1 * (x - 1)⁻¹ + x * (-1 / (x - 1) ^ 2)) x := hid.mul hinv
    have hf' : HasDerivAt (fun y => Real.log (y - 1) + y * (y - 1)⁻¹)
        ((x - 2) / (x - 1) ^ 2) x := by
      have hsum := hlog.add hmul
      have heq : (x - 1)⁻¹ + (1 * (x - 1)⁻¹ + x * (-1 / (x - 1) ^ 2))
          = (x - 2) / (x - 1) ^ 2 := by
        field_simp
        ring
      rw [heq] at hsum
      exact hsum
    exact hf'.hasDerivWithinAt
  · -- nonnegativity of the second derivative on the interior
    intro x hx
    rw [interior_Ici] at hx
    simp only [Set.mem_Ioi] at hx
    exact div_nonneg (by linarith) (by positivity)

omit [DecidableEq V] in
/-- **W8 — the degree-log Jensen bound.**  Under `δ ≥ 2`, the average `d_avg = D/n` satisfies
`D·log((D − n)/n) ≤ ∑_v deg v·log(deg v − 1)`.  Jensen's inequality (`ConvexOn.map_sum_le`) for the
convex `φ(x) = x·log(x − 1)` with uniform weights `1/n` at the degrees `d_v ∈ [2, ∞)` and center
`d_avg ∈ [2, ∞)`; multiplying through by `n`. This is the `Λ ≥ d_avg − 1` step
in logarithmic form. -/
theorem sum_deg_mul_log_ge (hδ2 : ∀ v, 2 ≤ G.degree v) (hn : 0 < Fintype.card V) :
    (∑ v, (G.degree v : ℝ)) *
        Real.log (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V) ≤
      ∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1) := by
  have hn' : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hmem : ∀ v ∈ (univ : Finset V), (G.degree v : ℝ) ∈ Set.Ici (2 : ℝ) := fun v _ => by
    simp only [Set.mem_Ici]; exact_mod_cast hδ2 v
  have hw0 : ∀ v ∈ (univ : Finset V), (0 : ℝ) ≤ 1 / (Fintype.card V : ℝ) := fun v _ => by positivity
  have hw1 : ∑ _v : V, (1 / (Fintype.card V : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp
  have hj := convexOn_deg_mul_log.map_sum_le hw0 hw1 hmem
  simp only [smul_eq_mul] at hj
  have hbar : (∑ v : V, (1 / (Fintype.card V : ℝ)) * (G.degree v : ℝ))
      = (∑ v, (G.degree v : ℝ)) / (Fintype.card V : ℝ) := by
    rw [← Finset.mul_sum]; ring
  rw [hbar, ← Finset.mul_sum] at hj
  rw [show ((∑ v, (G.degree v : ℝ)) - (Fintype.card V : ℝ)) / (Fintype.card V : ℝ)
        = (∑ v, (G.degree v : ℝ)) / (Fintype.card V : ℝ) - 1 from by field_simp]
  rw [show ((∑ v, (G.degree v : ℝ)) / (Fintype.card V : ℝ))
          * Real.log ((∑ v, (G.degree v : ℝ)) / (Fintype.card V : ℝ) - 1)
        = (∑ v, (G.degree v : ℝ))
            * Real.log ((∑ v, (G.degree v : ℝ)) / (Fintype.card V : ℝ) - 1)
            / (Fintype.card V : ℝ) from by ring,
    show (1 / (Fintype.card V : ℝ))
          * (∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1))
        = (∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) / (Fintype.card V : ℝ)
        from by ring] at hj
  exact (div_le_div_iff_of_pos_right hn').mp hj

/-! ### W6 — the entropy recursion -/

/-- **The AHL walk entropy** (W6).  `T_k = ∑_{length-k walks} wt·log wt⁻¹`, the finite-sum stand-in
for the entropy of the non-returning walk distribution.  Its exact one-step recursion is the engine
of the AM–GM lower bound. -/
noncomputable def nbEntropy (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : ℝ :=
  ∑ t ∈ nbAll (G := G) k, nbWeight t.2 * Real.log (nbWeight t.2)⁻¹

/-- **The weight of a one-edge extension.**  Every non-backtracking extension `s` of a non-nil
prefix
`s'` has weight `wt(s') · (deg (end s') − 1)⁻¹` — the new intermediate vertex is the old endpoint.
Immediate from `nbWeight_concat`. -/
theorem nbWeight_of_mem_nbExtend {x : V} {s' s : Σ v : V, G.Walk x v} (hnn : ¬ s'.2.Nil)
    (hs : s ∈ nbExtend G x s') :
    nbWeight s = nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹ := by
  rw [nbExtend, Finset.mem_image] at hs
  obtain ⟨b, hb, hbs⟩ := hs
  rw [Finset.mem_sdiff, mem_neighborFinset] at hb
  simp only [dite_eq_left hb.1] at hbs
  rw [← hbs, nbWeight_concat s'.2 hnn hb.1]

/-- **The entropy as a sum over starts.**  `nbEntropy` regroups `Finset.sum_sigma'`-style as the
double sum over the start `x` and the length-`k` non-backtracking walks from `x`. -/
theorem nbEntropy_sumstart (k : ℕ) :
    nbEntropy G k = ∑ x : V, ∑ s ∈ nbWalksFrom G x k, nbWeight s * Real.log (nbWeight s)⁻¹ := by
  rw [nbEntropy, nbAll, Finset.sum_sigma']

/-- **Base case** (W6).  `T₁ = 0`: every length-`1` walk has weight `1` and `log 1⁻¹ = 0`. -/
theorem nbEntropy_one : nbEntropy G 1 = 0 := by
  rw [nbEntropy]
  refine Finset.sum_eq_zero fun t ht => ?_
  rw [mem_nbAll] at ht
  have h1 : nbWeight t.2 = 1 := nbWeight_one (le_of_eq ht.1)
  rw [h1, inv_one, Real.log_one, mul_zero]

/-- **The per-prefix entropy fiber.**  Summing `wt·log wt⁻¹` over the `deg (end s') − 1`
extensions of
a non-nil prefix `s'` gives `wt(s')·log wt(s')⁻¹ + wt(s')·log(deg (end s') − 1)`: each extension has
the same weight `wt(s')·(deg − 1)⁻¹`, and the mass cancels the multiplicity, leaving the prefix mass
scaled by the log-of-degree increment. -/
theorem fiber_entropy (hδ2 : ∀ w, 2 ≤ G.degree w) {x : V} {s' : Σ v : V, G.Walk x v}
    (hnn : ¬ s'.2.Nil) :
    ∑ s ∈ nbExtend G x s', nbWeight s * Real.log (nbWeight s)⁻¹ =
      nbWeight s' * Real.log (nbWeight s')⁻¹
        + nbWeight s' * Real.log ((G.degree s'.1 : ℝ) - 1) := by
  have hpos : 0 < nbWeight s' := nbWeight_pos hδ2 s'
  have hd2 : (2 : ℝ) ≤ (G.degree s'.1 : ℝ) := by exact_mod_cast hδ2 s'.1
  have hne : (G.degree s'.1 : ℝ) - 1 ≠ 0 := by intro h; linarith
  have hconst : ∑ s ∈ nbExtend G x s', nbWeight s * Real.log (nbWeight s)⁻¹
      = ∑ _s ∈ nbExtend G x s',
          (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)
            * Real.log (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)⁻¹ := by
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [nbWeight_of_mem_nbExtend hnn hs]
  rw [hconst, Finset.sum_const, card_nbExtend hnn, nsmul_eq_mul,
    show ((G.degree s'.1 - 1 : ℕ) : ℝ) = (G.degree s'.1 : ℝ) - 1 from by
      rw [Nat.cast_sub (by have := hδ2 s'.1; omega), Nat.cast_one]]
  have hqlog : Real.log (nbWeight s' * ((G.degree s'.1 : ℝ) - 1)⁻¹)⁻¹
      = Real.log (nbWeight s')⁻¹ + Real.log ((G.degree s'.1 : ℝ) - 1) := by
    rw [Real.log_inv, Real.log_mul (ne_of_gt hpos) (inv_ne_zero hne), Real.log_inv, Real.log_inv]
    ring
  rw [hqlog]
  field_simp

/-- **The degree-log marginal collapse.**  Summing `wt·log(deg (end) − 1)` over all length-`k`
non-backtracking walks partitions by the endpoint and applies the end marginal `nbEndWeight = deg v`
(W4), giving `∑_v deg v · log(deg v − 1)`. -/
theorem sum_weight_log_deg (hδ2 : ∀ w, 2 ≤ G.degree w) {k : ℕ} (hk : 1 ≤ k) :
    ∑ t ∈ nbAll (G := G) k, nbWeight t.2 * Real.log ((G.degree t.2.1 : ℝ) - 1) =
      ∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1) := by
  have hmaps : ∀ t ∈ nbAll (G := G) k, t.2.1 ∈ (univ : Finset V) := fun _ _ => mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (fun t => nbWeight t.2 * Real.log ((G.degree t.2.1 : ℝ) - 1))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have step : ∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = v),
        nbWeight t.2 * Real.log ((G.degree t.2.1 : ℝ) - 1)
      = (∑ t ∈ (nbAll (G := G) k).filter (fun t => t.2.1 = v), nbWeight t.2)
        * Real.log ((G.degree v : ℝ) - 1) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [(Finset.mem_filter.mp ht).2]
  rw [step]
  change nbEndWeight (G := G) k v * Real.log ((G.degree v : ℝ) - 1) = _
  rw [nbEndWeight_eq_degree hδ2 hk]

/-- **The entropy recursion** (W6, II′).  `T_{k+1} = T_k + ∑_v deg v · log(deg v − 1)` for `k ≥ 1`.
Each length-`k` walk spawns `deg (end) − 1` extensions whose fiber contributes its own entropy plus
the degree-log increment (`fiber_entropy`); the increment collapses to the degree sum
(`sum_weight_log_deg`). -/
theorem nbEntropy_succ (hδ2 : ∀ w, 2 ≤ G.degree w) {k : ℕ} (hk : 1 ≤ k) :
    nbEntropy G (k + 1)
      = nbEntropy G k + ∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1) := by
  rw [nbEntropy_sumstart (k := k + 1)]
  have hbi : ∀ x : V,
      ∑ s ∈ nbWalksFrom G x (k + 1), nbWeight s * Real.log (nbWeight s)⁻¹
      = ∑ s' ∈ nbWalksFrom G x k, nbWeight s' * Real.log (nbWeight s')⁻¹
        + ∑ s' ∈ nbWalksFrom G x k, nbWeight s' * Real.log ((G.degree s'.1 : ℝ) - 1) := by
    intro x
    rw [nbWalksFrom_succ_eq_biUnion x hk, Finset.sum_biUnion (pairwiseDisjoint_nbExtend x k),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s' hs' => ?_
    have hnn : ¬ s'.2.Nil := Walk.not_nil_iff_lt_length.mpr (by
      have := (mem_nbWalksFrom.mp hs').1; omega)
    exact fiber_entropy hδ2 hnn
  rw [Finset.sum_congr rfl (fun x _ => hbi x), Finset.sum_add_distrib]
  congr 1
  · rw [nbEntropy_sumstart]
  · rw [Finset.sum_sigma']
    exact sum_weight_log_deg hδ2 hk

/-- **The entropy closed form** (W6).  For `ℓ ≥ 1`, `T_ℓ = (ℓ − 1)·∑_v deg v · log(deg v − 1)` —
telescoping the recursion `nbEntropy_succ` from the `T₁ = 0` base. -/
theorem nbEntropy_eq (hδ2 : ∀ w, 2 ≤ G.degree w) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    nbEntropy G ℓ = ((ℓ : ℝ) - 1) * ∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1) := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => rw [nbEntropy_one]; simp
  | succ k hk ih =>
    rw [nbEntropy_succ hδ2 hk, ih]
    push_cast
    ring

/-! ### W7 — the single AM–GM -/

/-- **The walk finset cardinality.**  `|nbAll k| = mₖ`, the total length-`k` non-backtracking walk
count (`Finset.card_sigma` + `card_nbWalksFrom`). -/
theorem card_nbAll (k : ℕ) : (nbAll (G := G) k).card = nbTotalWalks G k := by
  rw [nbAll, Finset.card_sigma, nbTotalWalks]
  exact Finset.sum_congr rfl fun x _ => card_nbWalksFrom x k

/-- **W7 — the AM–GM lower bound** (IV′).  Under `δ ≥ 2` (and `V` nonempty), the total walk count
dominates the geometric mean: `D·exp(T_k / D) ≤ mₖ`.  One application of
`Real.geom_mean_le_arith_mean_weighted` with weights `wt/D` (summing to `1` by `nbWeightTotal_eq`)
and values `D/wt`: the arithmetic side telescopes to `∑ 1 = mₖ`, and the geometric side is
`∏ (D/wt)^{wt/D} = exp(log D + T_k / D) = D·exp(T_k / D)`. -/
theorem nb_amgm (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] {k : ℕ} (hk : 1 ≤ k) :
    (∑ v, (G.degree v : ℝ)) * Real.exp (nbEntropy G k / (∑ v, (G.degree v : ℝ)))
      ≤ (nbTotalWalks G k : ℝ) := by
  set D : ℝ := ∑ v, (G.degree v : ℝ) with hD
  have hDpos : 0 < D := by
    rw [hD]
    refine Finset.sum_pos (fun v _ => ?_) univ_nonempty
    have h := hδ2 v; exact_mod_cast (show 0 < G.degree v by omega)
  have hD0 : D ≠ 0 := ne_of_gt hDpos
  have hw0 : ∀ t ∈ nbAll (G := G) k, 0 ≤ nbWeight t.2 / D := fun t _ =>
    div_nonneg (le_of_lt (nbWeight_pos hδ2 t.2)) (le_of_lt hDpos)
  have hw1 : ∑ t ∈ nbAll (G := G) k, nbWeight t.2 / D = 1 := by
    rw [← Finset.sum_div]
    have hsumw : (∑ t ∈ nbAll (G := G) k, nbWeight t.2) = D := by
      rw [hD]; exact nbWeightTotal_eq hδ2 hk
    rw [hsumw, div_self hD0]
  have hz0 : ∀ t ∈ nbAll (G := G) k, 0 ≤ D / nbWeight t.2 := fun t _ =>
    div_nonneg (le_of_lt hDpos) (le_of_lt (nbWeight_pos hδ2 t.2))
  have hamgm := Real.geom_mean_le_arith_mean_weighted (nbAll (G := G) k)
    (fun t => nbWeight t.2 / D) (fun t => D / nbWeight t.2) hw0 hw1 hz0
  have hone : ∀ t ∈ nbAll (G := G) k, (nbWeight t.2 / D) * (D / nbWeight t.2) = 1 := by
    intro t _
    have hp : nbWeight t.2 ≠ 0 := ne_of_gt (nbWeight_pos hδ2 t.2)
    rw [div_mul_div_comm, mul_comm (nbWeight t.2) D, div_self (mul_ne_zero hD0 hp)]
  have hrhs : ∑ t ∈ nbAll (G := G) k, (nbWeight t.2 / D) * (D / nbWeight t.2)
      = (nbTotalWalks G k : ℝ) := by
    rw [Finset.sum_congr rfl hone, Finset.sum_const, card_nbAll, nsmul_eq_mul, mul_one]
  have hfac : ∀ t ∈ nbAll (G := G) k, (D / nbWeight t.2) ^ (nbWeight t.2 / D)
      = Real.exp (Real.log (D / nbWeight t.2) * (nbWeight t.2 / D)) := fun t _ => by
    rw [Real.rpow_def_of_pos (div_pos hDpos (nbWeight_pos hδ2 t.2))]
  have hsum : ∑ t ∈ nbAll (G := G) k, Real.log (D / nbWeight t.2) * (nbWeight t.2 / D)
      = Real.log D + nbEntropy G k / D := by
    have hterm : ∀ t ∈ nbAll (G := G) k,
        Real.log (D / nbWeight t.2) * (nbWeight t.2 / D)
        = Real.log D * (nbWeight t.2 / D) + (nbWeight t.2 * Real.log (nbWeight t.2)⁻¹) / D := by
      intro t _
      have hp : 0 < nbWeight t.2 := nbWeight_pos hδ2 t.2
      rw [Real.log_div hD0 (ne_of_gt hp), Real.log_inv]
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hw1, mul_one,
      ← Finset.sum_div, nbEntropy]
  have hlhs : ∏ t ∈ nbAll (G := G) k, (D / nbWeight t.2) ^ (nbWeight t.2 / D)
      = D * Real.exp (nbEntropy G k / D) := by
    rw [Finset.prod_congr rfl hfac, ← Real.exp_sum, hsum, Real.exp_add, Real.exp_log hDpos]
  rw [hlhs, hrhs] at hamgm
  exact hamgm

/-! ### The sharp `Λ`-form (AHL Note 3) -/

/-- **The AHL spectral constant** `Λ = ∏_v (deg v − 1)^(deg v / D)` (`Real.rpow`), the geometric
mean
of `deg v − 1` weighted by the stationary degree measure `deg v / D`.  Keeping this form exposed (as
AHL Note 3 recommends) gives the sharper Moore rung `n ≥ n₀(Λ + 1, g)`. -/
noncomputable def Lambda (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  ∏ v, ((G.degree v : ℝ) - 1) ^ ((G.degree v : ℝ) / ∑ w, (G.degree w : ℝ))

omit [DecidableEq V] in
/-- **`Λ > 0`.**  Each factor `(deg v − 1)^{…}` is positive under `δ ≥ 2`. -/
theorem Lambda_pos (hδ2 : ∀ v, 2 ≤ G.degree v) : 0 < Lambda G := by
  rw [Lambda]
  refine Finset.prod_pos fun v _ => Real.rpow_pos_of_pos ?_ _
  have : (2 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hδ2 v
  linarith

omit [DecidableEq V] in
/-- **`log Λ` in closed form.**  `log Λ = (∑_v deg v · log(deg v − 1)) / D` — the exponent collapse
`log((deg v − 1)^{deg v / D}) = (deg v / D)·log(deg v − 1)`. -/
theorem log_Lambda (hδ2 : ∀ v, 2 ≤ G.degree v) :
    Real.log (Lambda G)
      = (∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1)) / ∑ w, (G.degree w : ℝ) := by
  have hne : ∀ v ∈ (univ : Finset V),
      ((G.degree v : ℝ) - 1) ^ ((G.degree v : ℝ) / ∑ w, (G.degree w : ℝ)) ≠ 0 := by
    intro v _
    refine ne_of_gt (Real.rpow_pos_of_pos ?_ _)
    have : (2 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hδ2 v
    linarith
  rw [Lambda, Real.log_prod hne, Finset.sum_div]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.log_rpow (by
    have : (2 : ℝ) ≤ (G.degree v : ℝ) := by exact_mod_cast hδ2 v
    linarith)]
  ring

/-- **W7 (sharp `Λ`-form).**  Under `δ ≥ 2` (and `V` nonempty), `D·Λ^(ℓ−1) ≤ mₗ` for `ℓ ≥ 1`.
Repackaging `nb_amgm` via `Λ^(ℓ−1) = exp((ℓ−1)·log Λ) = exp(T_ℓ / D)` (`nbEntropy_eq`, `log_Lambda`,
`Real.rpow_def_of_pos`). -/
theorem nb_amgm_lambda (hδ2 : ∀ v, 2 ≤ G.degree v) [Nonempty V] {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    (∑ v, (G.degree v : ℝ)) * (Lambda G) ^ ((ℓ : ℝ) - 1) ≤ (nbTotalWalks G ℓ : ℝ) := by
  have hkey : (Lambda G) ^ ((ℓ : ℝ) - 1) = Real.exp (nbEntropy G ℓ / ∑ v, (G.degree v : ℝ)) := by
    rw [Real.rpow_def_of_pos (Lambda_pos hδ2), log_Lambda hδ2, nbEntropy_eq hδ2 hℓ]
    congr 1
    ring
  rw [hkey]
  exact nb_amgm hδ2 hℓ

omit [DecidableEq V] in
/-- **W8 (sharp `Λ`-form).**  Under `δ ≥ 2`, `Λ ≥ (D − n)/n = d_avg − 1`.  Exponentiating the
logarithmic
Jensen bound `sum_deg_mul_log_ge`: `log((D − n)/n) ≤ (∑_v deg v · log(deg v − 1))/D = log Λ`. -/
theorem lambda_ge (hδ2 : ∀ v, 2 ≤ G.degree v) (hn : 0 < Fintype.card V) :
    ((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V ≤ Lambda G := by
  have hn' : (0 : ℝ) < (Fintype.card V : ℝ) := by exact_mod_cast hn
  have hDge : (2 * Fintype.card V : ℝ) ≤ ∑ v, (G.degree v : ℝ) := by
    have h : ∑ _v : V, (2 : ℝ) ≤ ∑ v, (G.degree v : ℝ) :=
      Finset.sum_le_sum (fun v _ => by exact_mod_cast hδ2 v)
    simpa [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm] using h
  have hDpos : 0 < ∑ v, (G.degree v : ℝ) := by linarith [hDge, hn']
  have hpos : 0 < ((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V :=
    div_pos (by linarith [hDge, hn']) hn'
  have hLpos : 0 < Lambda G := Lambda_pos hδ2
  have hlog : Real.log (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V)
      ≤ Real.log (Lambda G) := by
    rw [log_Lambda hδ2, le_div_iff₀ hDpos]
    calc Real.log (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V)
            * ∑ v, (G.degree v : ℝ)
        = (∑ v, (G.degree v : ℝ))
            * Real.log (((∑ v, (G.degree v : ℝ)) - Fintype.card V) / Fintype.card V) := by ring
      _ ≤ ∑ v, (G.degree v : ℝ) * Real.log ((G.degree v : ℝ) - 1) := sum_deg_mul_log_ge hδ2 hn
  exact (Real.log_le_log_iff hpos hLpos).mp hlog

end ACMax
