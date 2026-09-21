/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantReferenceCoordinateMap
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CoordinateEquivariance
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.ReferenceSubdivisionRegular
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteGenericPerturbation
import Mathlib.Topology.UniformSpace.HeineCantor
/-!
# Zero-free regular affine approximation after iterated subdivision

This module proves the quantitative approximation step used in S6.  A zero-free continuous
coordinate map on the compact Fox--Neuwirth realization has a positive uniform norm margin.
Uniform continuity and diameter shrinking for iterated barycentric subdivision make the affine
interpolation of vertex samples uniformly close to the original map.  A small scalar perturbation
toward the fixed positive S5 reference map avoids the finitely many determinant roots and hence
makes every refined top simplex regular.  The perturbation is chosen small enough that the entire
straight-line homotopy from the original map to the refined affine interpolation remains zero-free.

The perturbation direction is a single global continuous map.  Consequently values agree on every
shared refined face and prime-symmetry equivariance is preserved.
-/

namespace NRR

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace RefinedAffineMap

variable {p : Nat}

/-- A uniform positive lower bound for the norm of a zero-free continuous map on the compact
realization. -/
theorem exists_positive_norm_margin
    (F : ContinuousCoordinateMap p)
    (hF : ∀ x : Realization p, F x ≠ 0) :
    ∃ m : Real, 0 < m ∧ ∀ x : Realization p, m ≤ ‖F x‖ := by
  have hcont : Continuous (fun x : Realization p => ‖F x‖) := F.continuous.norm
  obtain ⟨x0, hx0⟩ :=
    IsCompact.exists_isMinOn (isCompact_univ : IsCompact (Set.univ : Set (Realization p)))
      ⟨Classical.choice inferInstance, Set.mem_univ _⟩ hcont.continuousOn
  refine ⟨‖F x0‖, norm_pos_iff.mpr (hF x0), ?_⟩
  intro x
  exact hx0.2 (Set.mem_univ x)

/-- A uniform strict upper bound for a continuous map on the compact realization. -/
theorem exists_norm_upper_bound
    (F : ContinuousCoordinateMap p) :
    ∃ B : Real, 0 < B ∧ ∀ x : Realization p, ‖F x‖ < B := by
  have hcont : Continuous (fun x : Realization p => ‖F x‖) := F.continuous.norm
  obtain ⟨x0, hx0⟩ :=
    IsCompact.exists_isMaxOn (isCompact_univ : IsCompact (Set.univ : Set (Realization p)))
      ⟨Classical.choice inferInstance, Set.mem_univ _⟩ hcont.continuousOn
  refine ⟨‖F x0‖ + 1, by positivity, ?_⟩
  intro x
  exact lt_of_le_of_lt (hx0.2 (Set.mem_univ x)) (lt_add_one _)

/-- Uniform oscillation bound on every refined top simplex at one sufficiently deep common
subdivision level. -/
theorem exists_common_refinement_oscillation
    (hp : Nat.Prime p)
    (F : ContinuousCoordinateMap p)
    {eps : Real} (heps : 0 < eps) :
    ∃ N : Nat, ∀ (q : TopCell hp N)
      (u v : StandardSimplex (p - 1)),
      dist (F (chart hp N q (StandardSimplex.toDelta u)))
        (F (chart hp N q (StandardSimplex.toDelta v))) < eps := by
  classical
  let Q := PrimeOrbitCycle.TopOrbit hp
  by_cases hQ : Nonempty Q
  · have huc : ∀ q : Q,
        UniformContinuous
          (F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap) := by
      intro q
      exact CompactSpace.uniformContinuous_of_continuous
        (F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap).continuous
    obtain ⟨delta, hdelta⟩ :
        ∃ delta : Q → Real, ∀ q, 0 < delta q ∧
          ∀ a b : Delta (p - 1), dist a b < delta q →
            dist ((F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap) a)
              ((F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap) b) < eps := by
      refine ⟨fun q => Classical.choose
        ((Metric.uniformContinuous_iff.1 (huc q)) eps heps), ?_⟩
      intro q
      exact Classical.choose_spec ((Metric.uniformContinuous_iff.1 (huc q)) eps heps)
    let deltas : Finset Real := Finset.univ.image delta
    have hdeltas : deltas.Nonempty :=
      ⟨delta (Classical.choice hQ), Finset.mem_image_of_mem delta (Finset.mem_univ _)⟩
    let d : Real := deltas.min' hdeltas
    have hdpos : 0 < d := by
      have hdmem := Finset.min'_mem deltas hdeltas
      obtain ⟨q, _, heq⟩ := Finset.mem_image.mp hdmem
      change 0 < deltas.min' hdeltas
      rw [← heq]
      exact (hdelta q).1
    have hdle : ∀ q : Q, d ≤ delta q := by
      intro q
      exact Finset.min'_le deltas (delta q)
        (Finset.mem_image_of_mem delta (Finset.mem_univ q))
    obtain ⟨N, hN⟩ := exists_diam_range_affineCompMap_lt (p - 1) d hdpos
    refine ⟨N, ?_⟩
    rintro ⟨q, rho⟩ u v
    let rho' : Fin N → Equiv.Perm (Fin (p - 1 + 1)) :=
      fun k => Simplex.refinementIndexPerm (rho k)
    change
      dist
        ((F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap)
          ((affineCompMap (p - 1) N rho') (StandardSimplex.toDelta u)))
        ((F.comp (ReferenceAffineOrbitCount.topRepr hp q).realizationContinuousMap)
          ((affineCompMap (p - 1) N rho') (StandardSimplex.toDelta v))) < eps
    apply (hdelta q).2
    apply lt_of_lt_of_le ?_ (hdle q)
    apply lt_of_le_of_lt (Metric.dist_le_diam_of_mem
      (isCompact_range (affineCompMap (p - 1) N rho').continuous).isBounded
      ⟨StandardSimplex.toDelta u, rfl⟩
      ⟨StandardSimplex.toDelta v, rfl⟩) (hN rho')
  · refine ⟨0, ?_⟩
    intro q
    exact (hQ ⟨q.1⟩).elim

/-- Affine interpolation of samples differs from the original map by at most the oscillation on
the refined simplex. -/
theorem norm_value_sub_original_le_of_oscillation
    (hp : Nat.Prime p) (N : Nat)
    (F : ContinuousCoordinateMap p) (q : TopCell hp N)
    (eps : Real)
    (hosc : ∀ u v : StandardSimplex (p - 1),
      dist (F (chart hp N q (StandardSimplex.toDelta u)))
        (F (chart hp N q (StandardSimplex.toDelta v))) < eps)
    (w : StandardSimplex (p - 1)) :
    ‖value hp N F q w - F (chart hp N q (StandardSimplex.toDelta w))‖ ≤ eps := by
  classical
  let y := F (chart hp N q (StandardSimplex.toDelta w))
  have hid : value hp N F q w - y =
      ∑ i : Fin (p - 1 + 1), w i • (F (vertex hp N q i) - y) := by
    funext j
    simp only [value, vertexValue, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    calc
      (∑ x, (w x : Real) * F (vertex hp N q x) j) - y j =
          (∑ x, (w x : Real) * F (vertex hp N q x) j) -
            (∑ x, (w x : Real)) * y j := by rw [w.sum_eq_one, one_mul]
      _ = (∑ x, (w x : Real) * F (vertex hp N q x) j) -
            ∑ x, (w x : Real) * y j := by rw [Finset.sum_mul]
      _ = ∑ x, ((w x : Real) * F (vertex hp N q x) j - (w x : Real) * y j) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ x, (w x : Real) * (F (vertex hp N q x) j - y j) := by
        apply Finset.sum_congr rfl
        intro x hx
        ring
  rw [hid]
  calc
    ‖∑ i : Fin (p - 1 + 1), w i • (F (vertex hp N q i) - y)‖
        ≤ ∑ i : Fin (p - 1 + 1), ‖w i • (F (vertex hp N q i) - y)‖ := by
      simpa only [Finset.sum_const_zero, add_zero] using
        (norm_sum_le (Finset.univ : Finset (Fin (p - 1 + 1)))
          (fun i => w i • (F (vertex hp N q i) - y)))
    _ = ∑ i : Fin (p - 1 + 1), w i * ‖F (vertex hp N q i) - y‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p - 1 + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (by
          simpa [dist_eq_norm, vertex, y] using
            hosc (StandardSimplex.ofDelta (stdSimplex.vertex (S := Real) i)) w))
        (w.nonneg i)
    _ = eps := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- A refined regular approximation of a zero-free continuous coordinate map.  The stored global
map is the small perturbation used for vertex sampling; `zeroFreeStraightLine` concerns the actual
piecewise-affine interpolation of those samples. -/
structure RegularApproximation
    (hp : Nat.Prime p) (F : ContinuousCoordinateMap p) where
  /-- Common barycentric-subdivision level. -/
  level : Nat
  /-- Global continuous map whose samples define the refined PL approximation. -/
  map : ContinuousCoordinateMap p
  /-- The sampled map respects prime-symmetry relabelling. -/
  equivariant : IsEquivariantCoordinateMap hp map
  /-- Every refined top simplex is transverse to the diagonal ray. -/
  regular : ∀ q : TopCell hp level, determinant hp level map q ≠ 0
  /-- The straight-line interpolation from the original map to the sampled affine map is
  zero-free on every refined simplex. -/
  zeroFreeStraightLine :
    ∀ (q : TopCell hp level) (w : StandardSimplex (p - 1))
      (u : Set.Icc (0 : Real) 1),
      (1 - u.1) • F (chart hp level q (StandardSimplex.toDelta w)) +
        u.1 • value hp level map q w ≠ 0

namespace RegularApproximation

/-- Positive orbit count represented by a regular refined approximation. -/
noncomputable def zeroCount
    {hp : Nat.Prime p} {F : ContinuousCoordinateMap p}
    (A : RegularApproximation hp F) : ZMod p :=
  RefinedAffineMap.zeroCount hp A.level A.map

end RegularApproximation

/-- Existence of a regular zero-free refined approximation. -/
theorem exists_regularApproximation
    (hp : Nat.Prime p)
    (F : ContinuousCoordinateMap p)
    (hEq : IsEquivariantCoordinateMap hp F)
    (hF : ∀ x : Realization p, F x ≠ 0) :
    Nonempty (RegularApproximation hp F) := by
  classical
  let R : ContinuousCoordinateMap p :=
    ofCoordinateAffineVertexMap (AAK.positiveEquivariantReferenceCoordinateMap hp)
  obtain ⟨m, hm0, hm⟩ := exists_positive_norm_margin F hF
  obtain ⟨B, hB0, hB⟩ := exists_norm_upper_bound (R - F)
  obtain ⟨N, hosc⟩ :=
    exists_common_refinement_oscillation hp F (show 0 < m / 8 by positivity)
  let A : TopCell hp N → Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Real :=
    fun q => augmentedMatrix hp N F q
  let D : TopCell hp N → Matrix (Fin (p - 1 + 1)) (Fin (p - 1 + 1)) Real :=
    fun q => augmentedMatrix hp N R q
  have hD : ∀ q, Matrix.det (D q) ≠ 0 := by
    intro q
    exact regular_on_refinement_of_regular hp N
      (AAK.positiveEquivariantReferenceCoordinateMap hp)
      (by
        rw [AAK.positiveEquivariantReferenceCoordinateMap_deviation hp]
        exact ReferenceAffineOrbitCount.referenceMap_regular hp) q
  let eps : Real := min 1 (m / (16 * (B + m + 1)))
  have heps : 0 < eps := by
    exact lt_min_iff.mpr ⟨zero_lt_one, by positivity⟩
  obtain ⟨t, ht0, hteps, htreg⟩ :=
    FiniteGenericPerturbation.exists_small_positive_regular A D hD heps
  have ht1 : t < 1 := lt_of_lt_of_le hteps (min_le_left _ _)
  let G : ContinuousCoordinateMap p := segment F R t
  refine ⟨{
    level := N
    map := G
    equivariant := by
      intro g x
      change (1 - t) • F (g • x) + t • R (g • x) =
        g • ((1 - t) • F x + t • R x)
      rw [hEq g x]
      have hR := AAK.positiveEquivariantReferenceCoordinateMap_global_smul hp g x
      change R (g • x) = g • R x at hR
      rw [hR]
      funext i
      simp only [PrimeSymmetry.smul_coordinate_apply, Pi.add_apply, Pi.smul_apply]
    regular := ?_
    zeroFreeStraightLine := ?_ }⟩
  · intro q
    have hmatrix : augmentedMatrix hp N G q =
        (1 - t) • A q + t • D q := by
      simpa [G, A, D] using augmentedMatrix_segment hp N F R t q
    rw [determinant, hmatrix]
    exact htreg q
  · intro q w u
    let x := chart hp N q (StandardSimplex.toDelta w)
    have happ : ‖value hp N F q w - F x‖ ≤ m / 8 :=
      norm_value_sub_original_le_of_oscillation hp N F q (m / 8) (hosc q) w
    have hvalueDiff : value hp N G q w - value hp N F q w =
        t • value hp N (R - F) q w := by
      funext i
      simp only [G, segment, value, vertexValue, Pi.sub_apply, Pi.smul_apply,
        ContinuousMap.sub_apply, smul_eq_mul]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      change (w j : Real) * ((1 - t) * F (vertex hp N q j) i +
        t * R (vertex hp N q j) i) - (w j : Real) * F (vertex hp N q j) i = _
      ring
    have hvalueSum : value hp N (R - F) q w =
        ∑ i : Fin (p - 1 + 1), w i • ((R - F) (vertex hp N q i)) := by
      funext j
      simp [value, vertexValue]
    have hvalueBound : ‖value hp N (R - F) q w‖ ≤ B := by
      rw [hvalueSum]
      calc
        ‖∑ i : Fin (p - 1 + 1), w i • ((R - F) (vertex hp N q i))‖
            ≤ ∑ i : Fin (p - 1 + 1), ‖w i • ((R - F) (vertex hp N q i))‖ := by
              exact norm_sum_le (Finset.univ : Finset (Fin (p - 1 + 1))) _
        _ = ∑ i : Fin (p - 1 + 1), w i * ‖(R - F) (vertex hp N q i)‖ := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
        _ ≤ ∑ i : Fin (p - 1 + 1), w i * B := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (le_of_lt (hB _)) (w.nonneg i)
        _ = B := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]
    have hpert : ‖value hp N G q w - value hp N F q w‖ < m / 8 := by
      rw [hvalueDiff, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have htE : t < m / (16 * (B + m + 1)) :=
        lt_of_lt_of_le hteps (min_le_right _ _)
      have hden : 0 < B + m + 1 := by positivity
      have htSmall : t * B < m / 8 := by
        have hBaux : B < 2 * (B + m + 1) := by nlinarith [hB0, hm0]
        calc
          t * B < (m / (16 * (B + m + 1))) * B :=
            mul_lt_mul_of_pos_right htE hB0
          _ < (m / (16 * (B + m + 1))) * (2 * (B + m + 1)) :=
            mul_lt_mul_of_pos_left hBaux (by positivity)
          _ = m / 8 := by field_simp [ne_of_gt hden] ; ring
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hvalueBound (le_of_lt ht0)) htSmall
    have hclose : ‖value hp N G q w - F x‖ < m / 2 := by
      calc
        ‖value hp N G q w - F x‖
            ≤ ‖value hp N G q w - value hp N F q w‖ +
                ‖value hp N F q w - F x‖ := by
              simpa [dist_eq_norm] using
                dist_triangle (value hp N G q w) (value hp N F q w) (F x)
        _ < m / 2 := by linarith [hpert, happ]
    intro hzero
    have hu0 : 0 ≤ u.1 := u.2.1
    have hu1 : u.1 ≤ 1 := u.2.2
    have hzero' : (1 - u.1) • F x + u.1 • value hp N G q w = 0 := by
      simpa [x] using hzero
    have hFx : ‖F x‖ ≤ ‖value hp N G q w - F x‖ := by
      have hbase : (1 - u.1) • F x = -u.1 • value hp N G q w := by
        calc
          (1 - u.1) • F x =
              ((1 - u.1) • F x + u.1 • value hp N G q w) -
                u.1 • value hp N G q w := by module
          _ = -u.1 • value hp N G q w := by rw [hzero']; simp
      have heq : F x = -u.1 • (value hp N G q w - F x) := by
        calc
          F x = (1 - u.1) • F x + u.1 • F x := by module
          _ = -u.1 • value hp N G q w + u.1 • F x := by rw [hbase]
          _ = -u.1 • (value hp N G q w - F x) := by module
      calc
        ‖F x‖ = ‖-u.1 • (value hp N G q w - F x)‖ := congrArg norm heq
        _ = u.1 * ‖value hp N G q w - F x‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hu0]
        _ ≤ ‖value hp N G q w - F x‖ :=
          mul_le_of_le_one_left (norm_nonneg _) hu1
    have hFxlt : ‖F x‖ < m :=
      lt_trans (lt_of_le_of_lt hFx hclose) (half_lt_self hm0)
    exact (not_lt_of_ge (hm x)) hFxlt
end RefinedAffineMap
end FoxNeuwirthOrderComplex
end NRR
