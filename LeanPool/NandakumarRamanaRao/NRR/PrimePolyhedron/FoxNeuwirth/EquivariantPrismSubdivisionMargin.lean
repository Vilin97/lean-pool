/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericPerturbation
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Quantitative zero-free margin after staircase refinement

For a fixed common spatial subdivision level, the finitely many unrefined staircase-prism charts
are continuous maps from the compact standard `p`-simplex into the realization cylinder.  A
zero-free homotopy has a positive uniform norm margin on that compact cylinder.  Uniform
continuity, together with diameter shrinking under iterated barycentric subdivision of each
staircase simplex, therefore makes the affine interpolation of homotopy samples uniformly close to
the original homotopy.

Because the target `Fin p → ℝ` carries the finite product sup norm, one coordinate realizes at
least the full vector norm.  Consequently the sampled affine interpolation has a positive local
coordinate norm margin.  This is precisely the quantitative hypothesis required by
`EquivariantPrismGenericPerturbation.exists_generic_perturbation`.

The main result is formulated for an arbitrary preselected spatial level `N`: only the staircase
refinement level `L` must subsequently be increased.  This permits later arguments to choose a
common spatial subdivision for endpoint data first and then refine the entire homotopy prism.
-/

@[expose] public section

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismSubdivisionMargin

open EquivariantCoordinateHomotopy
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGenericPerturbation
open SubdivisionPrismCharts

variable {p : Nat}

/-- The unrefined staircase chart over one fixed spatially refined top simplex. -/
noncomputable def basePrismChart
    (hp : Nat.Prime p) (N : Nat) (q : BasePrismCell hp N) :
    C(Delta p, Realization p × Set.Icc (0 : Real) 1) where
  toFun w :=
    let u : StandardSimplex p := StandardSimplex.ofDelta w
    let st := staircasePoint hp q.2 u
    (RefinedAffineMap.chart hp N q.1 (StandardSimplex.toDelta st.1), st.2)
  continuous_toFun := by
    have hspatial : Continuous fun w : Delta p =>
        StandardSimplex.toDelta
          (spatialPoint hp q.2 (StandardSimplex.ofDelta w)) := by
      apply Continuous.subtype_mk
      change Continuous fun w : Delta p => fun i =>
        ∑ j : Fin (p + 1),
          if Fin.cast (Nat.sub_add_cancel hp.pos).symm (staircaseSpatial p q.2 j) = i then
            StandardSimplex.ofDelta w j else 0
      apply continuous_pi
      intro i
      apply continuous_finsetSum
      intro j hj
      split_ifs
      · exact (continuous_apply j).comp continuous_subtype_val
      · fun_prop
    have hinterval : Continuous fun w : Delta p =>
        intervalPoint q.2 (StandardSimplex.ofDelta w) := by
      apply Continuous.subtype_mk
      change Continuous fun w : Delta p =>
        ∑ j : Fin (p + 1), if staircaseTime q.2 j = 1 then
          StandardSimplex.ofDelta w j else 0
      apply continuous_finsetSum
      intro j hj
      split_ifs
      · exact (continuous_apply j).comp continuous_subtype_val
      · fun_prop
    exact ((RefinedAffineMap.chart hp N q.1).continuous.comp hspatial).prodMk hinterval

/-- A fully refined prism chart factors through its unrefined staircase chart and the iterated
barycentric subdivision map. -/
@[simp] theorem chart_eq_basePrismChart_affineCompMap
    (hp : Nat.Prime p) (N L : Nat) (q : PrismCell hp N L) (w : Delta p) :
    chart hp N L q w =
      basePrismChart hp N q.1 (affineCompMap p L q.2 w) := rfl

/-- A zero-free homotopy has a uniform positive norm margin on the compact realization cylinder. -/
theorem exists_positive_homotopy_norm_margin
    (hp : Nat.Prime p)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ M : Real, 0 < M ∧
      ∀ z : Realization p × Set.Icc (0 : Real) 1, M ≤ ‖H.map z‖ := by
  have hcont : Continuous
      (fun z : Realization p × Set.Icc (0 : Real) 1 => ‖H.map z‖) :=
    H.map.continuous.norm
  obtain ⟨z₀, hz₀⟩ :=
    IsCompact.exists_isMinOn
      (isCompact_univ :
        IsCompact (Set.univ : Set (Realization p × Set.Icc (0 : Real) 1)))
      ⟨Classical.choice inferInstance, Set.mem_univ _⟩ hcont.continuousOn
  refine ⟨‖H.map z₀‖, ?_, ?_⟩
  · exact norm_pos_iff.mpr (H.zeroFree z₀.1 z₀.2)
  · intro z
    exact hz₀.2 (Set.mem_univ z)

/-- In a nonempty finite product, some coordinate has absolute value at least the product norm. -/
theorem exists_coordinate_abs_ge_norm
    (hp : Nat.Prime p) (x : Fin p → Real) :
    ∃ j : Fin p, ‖x‖ ≤ |x j| := by
  classical
  by_cases hx : x = 0
  · exact ⟨⟨0, hp.pos⟩, by simp [hx]⟩
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  by_contra h
  push Not at h
  have hlt : ‖x‖ < ‖x‖ :=
    (pi_norm_lt_iff hnorm).2 (fun j => by
      simpa [Real.norm_eq_abs] using h j)
  exact (lt_irrefl _ hlt)

/-- At every fixed spatial subdivision level, sufficiently deep staircase subdivision makes the
homotopy oscillation on every refined prism simplex smaller than any prescribed positive bound. -/
theorem exists_staircase_refinement_oscillation
    (hp : Nat.Prime p) (N : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {eps : Real} (heps : 0 < eps) :
    ∃ L : Nat, ∀ (q : PrismCell hp N L)
      (u v : StandardSimplex p),
      dist
        (H.map (chart hp N L q (StandardSimplex.toDelta u)))
        (H.map (chart hp N L q (StandardSimplex.toDelta v))) < eps := by
  classical
  let Q := BasePrismCell hp N
  let : NeZero p := ⟨hp.ne_zero⟩
  have huc : ∀ q : Q,
      UniformContinuous (H.map.comp (basePrismChart hp N q)) := by
    intro q
    exact CompactSpace.uniformContinuous_of_continuous
      (H.map.comp (basePrismChart hp N q)).continuous
  obtain ⟨delta, hdelta⟩ :
      ∃ delta : Q → Real, ∀ q, 0 < delta q ∧
        ∀ a b : Delta p, dist a b < delta q →
          dist
            ((H.map.comp (basePrismChart hp N q)) a)
            ((H.map.comp (basePrismChart hp N q)) b) < eps := by
    refine ⟨fun q => Classical.choose
      ((Metric.uniformContinuous_iff.1 (huc q)) eps heps), ?_⟩
    intro q
    exact Classical.choose_spec
      ((Metric.uniformContinuous_iff.1 (huc q)) eps heps)
  let deltas : Finset Real := Finset.univ.image delta
  have hQ : Nonempty Q := ⟨
    (((ReferenceAffineOrbitCount.selectedOrbitEquivTopSupport hp)
      (Quotient.mk'' BarredPermutation.TopCell.evenRepresentative)).1,
      fun _ => Equiv.refl _), ⟨0, hp.pos⟩⟩
  have hdeltas : deltas.Nonempty :=
    ⟨delta (Classical.choice hQ),
      Finset.mem_image_of_mem delta (Finset.mem_univ _)⟩
  let d : Real := deltas.min' hdeltas
  have hdpos : 0 < d := by
    change 0 < deltas.min' hdeltas
    have hdmem := Finset.min'_mem deltas hdeltas
    rcases Finset.mem_image.mp hdmem with ⟨q, hq, heq⟩
    rw [← heq]
    exact (hdelta q).1
  have hdle : ∀ q : Q, d ≤ delta q := by
    intro q
    exact Finset.min'_le deltas (delta q)
      (Finset.mem_image_of_mem delta (Finset.mem_univ q))
  obtain ⟨L, hL⟩ := exists_diam_range_affineCompMap_lt p d hdpos
  refine ⟨L, ?_⟩
  rintro ⟨q, rho⟩ u v
  rw [chart_eq_basePrismChart_affineCompMap,
    chart_eq_basePrismChart_affineCompMap]
  apply (hdelta q).2
  exact lt_of_lt_of_le
    (lt_of_le_of_lt
      (Metric.dist_le_diam_of_mem
        (isCompact_range (affineCompMap p L rho).continuous).isBounded
        ⟨StandardSimplex.toDelta u, rfl⟩
        ⟨StandardSimplex.toDelta v, rfl⟩)
      (hL rho))
    (hdle q)

/-- If the homotopy oscillates by less than `eps` on one refined prism simplex, its affine
interpolation from vertex samples differs from the original homotopy by at most `eps`. -/
theorem norm_affineValue_sub_homotopy_le_of_oscillation
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (q : PrismCell hp N L) (eps : Real)
    (hosc : ∀ u v : StandardSimplex p,
      dist
        (H.map (chart hp N L q (StandardSimplex.toDelta u)))
        (H.map (chart hp N L q (StandardSimplex.toDelta v))) < eps)
    (w : StandardSimplex p) :
    ‖AffinePositiveRayBoundary.VertexMap.affineValue
        (localVertexMap hp N L (homotopyAssignment hp N L H) q) w -
      H.map (chart hp N L q (StandardSimplex.toDelta w))‖ ≤ eps := by
  classical
  let y : Fin p → Real :=
    H.map (chart hp N L q (StandardSimplex.toDelta w))
  have hid :
      AffinePositiveRayBoundary.VertexMap.affineValue
          (localVertexMap hp N L (homotopyAssignment hp N L H) q) w - y =
        ∑ i : Fin (p + 1),
          w i • (H.map (vertex hp N L q i) - y) := by
    funext j
    simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, AffinePositiveRayBoundary.VertexMap.affineValue,
      localVertexMap, localVertexValue_homotopyAssignment]
    change (∑ i : Fin (p + 1),
        w i * H.map (vertex hp N L q i) j) - y j =
      ∑ i : Fin (p + 1), w i * (H.map (vertex hp N L q i) j - y j)
    conv_lhs =>
      rhs
      rw [← one_mul (y j), ← w.sum_eq_one, Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hid]
  calc
    ‖∑ i : Fin (p + 1), w i • (H.map (vertex hp N L q i) - y)‖
        ≤ ∑ i : Fin (p + 1),
          ‖w i • (H.map (vertex hp N L q i) - y)‖ := by
      simpa using norm_sum_le Finset.univ
        (fun i : Fin (p + 1) => w i • (H.map (vertex hp N L q i) - y))
    _ = ∑ i : Fin (p + 1),
        w i * ‖H.map (vertex hp N L q i) - y‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (by
          simpa [dist_eq_norm, vertex, y] using
            hosc
              (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) w))
        (w.nonneg i)
    _ = eps := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- For every fixed spatial level, some staircase refinement gives the homotopy assignment a
strictly positive local affine coordinate norm margin. -/
theorem exists_staircase_refinement_coordinateNormMargin
    (hp : Nat.Prime p) (N : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ (L : Nat) (m : Real), 0 < m ∧
      LocalAffineCoordinateNormMargin hp N L
        (homotopyAssignment hp N L H) m := by
  classical
  obtain ⟨M, hM, hmargin⟩ := exists_positive_homotopy_norm_margin hp H
  obtain ⟨L, hosc⟩ :=
    exists_staircase_refinement_oscillation hp N H
      (show 0 < M / 2 by positivity)
  refine ⟨L, M / 2, by positivity, ?_⟩
  intro q w
  let y : Fin p → Real :=
    H.map (chart hp N L q (StandardSimplex.toDelta w))
  let z : Fin p → Real :=
    AffinePositiveRayBoundary.VertexMap.affineValue
      (localVertexMap hp N L (homotopyAssignment hp N L H) q) w
  have hclose : ‖z - y‖ ≤ M / 2 := by
    simpa [z, y] using
      norm_affineValue_sub_homotopy_le_of_oscillation
        hp N L H q (M / 2) (hosc q) w
  have hy : M ≤ ‖y‖ := hmargin _
  have hy_le : ‖y‖ ≤ ‖z - y‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖-(z - y) + z‖ := by
        congr 1
        module
      _ ≤ ‖-(z - y)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - y‖ + ‖z‖ := by rw [norm_neg]
  have hz : M / 2 ≤ ‖z‖ := by linarith
  obtain ⟨j, hj⟩ := exists_coordinate_abs_ge_norm hp z
  refine ⟨j, le_trans hz ?_⟩
  simpa [z, Real.norm_eq_abs] using hj

/-- After any preselected spatial subdivision, one can choose a staircase refinement and obtain a
compatible equivariant generic perturbation satisfying full local general position and retaining a
positive zero-free margin. -/
theorem exists_generic_perturbation_after_staircase_refinement
    (hp : Nat.Prime p) (N : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    ∃ (L : Nat) (m : Real), 0 < m ∧
      Nonempty (Result hp N L H m) := by
  obtain ⟨L, m, hm, hmargin⟩ :=
    exists_staircase_refinement_coordinateNormMargin hp N H
  exact ⟨L, m, hm,
    exists_generic_perturbation hp N L H hm hmargin⟩

end EquivariantPrismSubdivisionMargin
end FoxNeuwirthOrderComplex
end NRR
