/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import Mathlib.Tactic
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.Basic
public import LeanPool.NandakumarRamanaRao.NRR.EMP.VariableBody.CompactSiteFamily
public import LeanPool.NandakumarRamanaRao.NRR.EMP.PowerCellPositiveArea

/-!
# `NRR.EMP.VariableBody.WeightBounds` — uniform coordinate bounds

For a compact metric parameter space `X` carrying a continuous site family `sites : SiteFamily X n`
and a fixed planar parent body `K`, every equal-area (Laguerre) weight for a subbody
`C : BodySpace K A` at a parameter `x : X` obeys an explicit uniform bound expressed through the
compact site and parent radii.

The bound is `weightBound K sites = (parentRadius K + siteRadius sites) ^ 2`. It is independent of
the subbody `C`, the parameter `x`, and the individual weight `w`, and is the compactness input for
the closed-graph selection theorem.

## Proof outline

Equal area forces every restricted cell to have the positive area `C.body.area / n`, so each cell is
nonempty; a point `y` of the `i`-th cell is power-closer to site `i` than to site `j`, which
rearranges to `w j - w i ≤ ‖y - s j‖² - ‖y - s i‖²`. Dropping the nonpositive term and bounding
`‖y - s j‖ ≤ parentRadius K + siteRadius sites` (using `y ∈ C ⊆ K`) gives the pairwise bound; the
coordinate bound follows from normalization `∑ j, w j = 0` and the triangle inequality on the finite
sum `(n : ℝ) * w i = ∑ j, (w i - w j)`.
-/

@[expose] public section

open NRR NRR.Geometry NRR.PowerDiagram

namespace NRR.EMP.VariableBody

variable {X : Type*} [MetricSpace X] [CompactSpace X] {n : ℕ}
variable {K : Geometry.ConvexBody Plane} {A : ℝ}

/-- **Uniform coordinate bound** for equal-area weights: the square of the sum of the compact parent
and site radii. It is independent of the subbody, the parameter, and the individual weight. -/
noncomputable def weightBound
    (K : Geometry.ConvexBody Plane)
    (sites : SiteFamily X n) : ℝ :=
  (parentRadius K + siteRadius sites) ^ 2

theorem weightBound_nonneg
    (K : Geometry.ConvexBody Plane)
    (sites : SiteFamily X n) :
    0 ≤ weightBound K sites := by
  unfold weightBound
  positivity

/-- **Normalized finite-family identity.** For a zero-sum weight vector, `(n : ℝ) * w i` equals the
sum over `j` of the pairwise differences `w i - w j`. Stated independently of power diagrams. -/
theorem cast_mul_eq_sum_sub
    {w : Fin n → ℝ} (h : ∑ j, w j = 0) (i : Fin n) :
    (n : ℝ) * w i = ∑ j, (w i - w j) := by
  rw [Finset.sum_sub_distrib, h, sub_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **Pairwise weight bound.** For any equal-area weight, the difference `w j - w i` is bounded by
the explicit uniform `weightBound K sites`. -/
theorem pairwise_weight_sub_le
    (sites : SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    {C : BodySpace K A} {x : X} {w : Fin n → ℝ}
    (hw : IsEqualAreaWeight hA C (sites x) w)
    (i j : Fin n) :
    w j - w i ≤ weightBound K sites := by
  -- Positive area of the `i`-th equal-area cell gives a nonempty interior; pick a point `y`.
  have hK : 0 < (solidBody hA C).area := by
    simpa using BodySpace.area_pos hA C
  obtain ⟨y, hy⟩ :=
    PowerDiagram.bodyCellSet_interior_nonempty_of_equalArea
      (solidBody hA C) (sites x).pts w hn hK hw i
  have y_mem : y ∈ PowerDiagram.bodyCellSet (solidBody hA C) (sites x).pts w i :=
    interior_subset hy
  -- `y` lies in the parent body `K`.
  have hyK : y ∈ (K : Set Plane) :=
    cellSet_subset_parent hA C (sites x) w i y_mem
  -- `y` is power-closer to `i` than to `j`.
  have hcell : y ∈ cell (sites x).pts w i := y_mem.2
  have hle : powerDist (sites x).pts w i y ≤ powerDist (sites x).pts w j y :=
    (mem_cell _ _ _ _).1 hcell j
  simp only [PowerDiagram.powerDist] at hle
  -- Bound `‖y - s j‖` by the sum of the compact radii, hence its square by `weightBound`.
  have hnorm : ‖y - (sites x).pts j‖ ≤ parentRadius K + siteRadius sites :=
    calc ‖y - (sites x).pts j‖ ≤ ‖y‖ + ‖(sites x).pts j‖ := norm_sub_le _ _
      _ ≤ parentRadius K + siteRadius sites :=
        add_le_add (norm_mem_parent_le_parentRadius K hyK)
          (norm_site_le_siteRadius sites x j)
  have hsq : ‖y - (sites x).pts j‖ ^ 2 ≤ weightBound K sites := by
    unfold weightBound
    nlinarith [hnorm, norm_nonneg (y - (sites x).pts j),
      parentRadius_nonneg K, siteRadius_nonneg sites]
  -- Rearrange the cell inequality and drop the nonpositive term.
  nlinarith [hsq, sq_nonneg ‖y - (sites x).pts i‖, hle]

/-- **Absolute pairwise weight bound.** For any equal-area weight, `|w i - w j|` is bounded by the
explicit uniform `weightBound K sites`. -/
theorem abs_weight_sub_le
    (sites : SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    {C : BodySpace K A} {x : X} {w : Fin n → ℝ}
    (hw : IsEqualAreaWeight hA C (sites x) w)
    (i j : Fin n) :
    |w i - w j| ≤ weightBound K sites := by
  apply abs_le.mpr
  refine ⟨?_, ?_⟩
  · linarith [pairwise_weight_sub_le sites hA hn hw i j]
  · exact pairwise_weight_sub_le sites hA hn hw j i

/-- **Coordinate bound for a normalized equal-area weight.** Each coordinate of a normalized
equal-area weight satisfies `|w i| ≤ weightBound K sites`. -/
theorem abs_weight_le
    (sites : SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    {C : BodySpace K A} {x : X} {w : Fin n → ℝ}
    (hw : IsNormalizedEqualAreaWeight hA C (sites x) w)
    (i : Fin n) :
    |w i| ≤ weightBound K sites := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsum : ∑ j, w j = 0 := hw.2
  have key : (n : ℝ) * w i = ∑ j, (w i - w j) := cast_mul_eq_sum_sub hsum i
  have hbound : |(n : ℝ) * w i| ≤ (n : ℝ) * weightBound K sites := by
    rw [key]
    calc |∑ j, (w i - w j)| ≤ ∑ j, |w i - w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin n, weightBound K sites :=
        Finset.sum_le_sum (fun j _ => abs_weight_sub_le sites hA hn hw.1 i j)
      _ = (n : ℝ) * weightBound K sites := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : (n : ℝ) * |w i| ≤ (n : ℝ) * weightBound K sites := by
    rwa [abs_mul, abs_of_nonneg hn'.le] at hbound
  exact le_of_mul_le_mul_left h2 hn'

/-- **Uniform coordinate bound for the canonical normalized weight.** Every coordinate of the
canonically selected normalized equal-area weight satisfies the explicit uniform bound. -/
theorem normalizedWeight_abs_le
    (sites : SiteFamily X n)
    (hA : 0 < A) (hn : 0 < n)
    (C : BodySpace K A) (x : X) (i : Fin n) :
    |normalizedWeight hA hn C (sites x) i| ≤ weightBound K sites :=
  abs_weight_le sites hA hn
    ⟨normalizedWeight_isEqualArea hA hn C (sites x),
      normalizedWeight_normalized hA hn C (sites x)⟩ i

end NRR.EMP.VariableBody
