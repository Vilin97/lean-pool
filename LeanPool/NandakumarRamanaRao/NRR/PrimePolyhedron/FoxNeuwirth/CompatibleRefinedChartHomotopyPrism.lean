/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/
module


public import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.FiniteSimplex
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CompatibleChartMapOneStep
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RelativeCollarMiddlePrismEndpoints
public import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismSubdivisionMargin
/-!
# Fine prism assignments for compatible chart homotopies

A compatible chart homotopy can be sampled on the fully refined staircase prism without first
constructing a global continuous quotient map.  Decorated chart compatibility is exactly the
condition needed to descend local samples to global collar vertices.

Because there are finitely many base prism charts, compactness gives a positive norm margin and a
uniform modulus of continuity.  Iterated barycentric subdivision then makes the affine
interpolation of the samples remain within half that margin.  The resulting middle-prism
assignment is origin-free and its two horizontal boundaries are the exact endpoint chart maps.
-/

@[expose] public section

namespace NRR
namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace CompatibleRefinedChartHomotopyPrism

open scoped BigOperators
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision
open RefinedAffineMap
open ExplicitAffineRelativeCollar
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollarAssignmentCompose
open AffinePositiveRayBoundary
open CompatibleRefinedChartHomotopy
open SubdivisionPrismCharts
open EquivariantPrismSubdivisionMargin
open ExplicitAffineRelativeCollar.Polynomials
open AffinePositiveRayBoundary.VertexMap


variable {p : Nat}

/-- The project simplex presentation is nonempty. -/
instance nonempty_standardSimplex (d : Nat) : Nonempty (StandardSimplex d) :=
  ⟨StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) 0)⟩

/-- The project simplex presentation is compact. -/
instance compactSpace_standardSimplex (d : Nat) : CompactSpace (StandardSimplex d) := by
  have hrange : Set.range (StandardSimplex.ofDelta (d := d)) = Set.univ := by
    ext w
    exact ⟨fun _ => Set.mem_univ _,
      fun _ => ⟨StandardSimplex.toDelta w, StandardSimplex.ofDelta_toDelta w⟩⟩
  let : CompactSpace (Delta d) :=
    isCompact_iff_compactSpace.mp (SphereOddDegree.isCompact_finiteSimplex Real (Fin (d + 1)))
  refine isCompact_univ_iff.mp ?_
  have := isCompact_range (continuous_ofDelta (d := d))
  rwa [hrange] at this


/-- Value of a chart homotopy on one unrefined staircase chart. -/
noncomputable def basePrismValue
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (q : BasePrismCell hp N) (w : StandardSimplex p) : Fin p → Real :=
  let z := staircasePoint hp q.2 w
  J.value q.1 z.1 z.2

/-- The staircase chart is continuous. -/
theorem continuous_staircasePoint (hp : Nat.Prime p) (k : Fin p) :
    Continuous fun w : StandardSimplex p => staircasePoint hp k w := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    change Continuous fun w : StandardSimplex p => fun i =>
      ∑ j : Fin (p + 1),
        if Fin.cast (Nat.sub_add_cancel hp.pos).symm (staircaseSpatial p k j) = i then
          w j else 0
    apply continuous_pi
    intro i
    apply continuous_finsetSum
    intro j _
    split_ifs
    · exact (continuous_apply j).comp continuous_subtype_val
    · fun_prop
  · apply Continuous.subtype_mk
    change Continuous fun w : StandardSimplex p =>
      ∑ j : Fin (p + 1), if staircaseTime k j = 1 then w j else 0
    apply continuous_finsetSum
    intro j _
    split_ifs
    · exact (continuous_apply j).comp continuous_subtype_val
    · fun_prop

/-- The staircase chart is continuous in the topological-simplex presentation. -/
theorem continuous_staircasePoint_ofDelta (hp : Nat.Prime p) (k : Fin p) :
    Continuous fun w : Delta p =>
      staircasePoint hp k (StandardSimplex.ofDelta w) :=
  (continuous_staircasePoint hp k).comp continuous_ofDelta

/-- Continuous base-prism value. -/
noncomputable def basePrismValueMap
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (q : BasePrismCell hp N) : C(Delta p, Fin p → Real) where
  toFun w := basePrismValue hp J q (StandardSimplex.ofDelta w)
  continuous_toFun := by
    exact (J.continuous_value q.1).comp (continuous_staircasePoint_ofDelta hp q.2)

/-- Value on a fully refined prism chart. -/
noncomputable def refinedPrismValue
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat) (q : PrismCell hp N L) (w : StandardSimplex p) : Fin p → Real :=
  basePrismValue hp J q.1
    (StandardSimplex.ofDelta
      (affineCompMap p L q.2 (StandardSimplex.toDelta w)))

/-- The refined value is the chart homotopy evaluated at the represented prism point. -/
theorem refinedPrismValue_eq
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat) (q : PrismCell hp N L) (w : StandardSimplex p) :
    refinedPrismValue hp J L q w =
      J.value q.1.1
        (staircasePoint hp q.1.2
          (StandardSimplex.ofDelta
            (affineCompMap p L q.2 (StandardSimplex.toDelta w)))).1
        (staircasePoint hp q.1.2
          (StandardSimplex.ofDelta
            (affineCompMap p L q.2 (StandardSimplex.toDelta w)))).2 := by
  rfl

/-- Local sample at one prism vertex. -/
noncomputable def localVector
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat) (s : (RelativeCollarMiddlePrism.cellSystem hp N L).VertexSlot) : Fin p → Real :=
  refinedPrismValue hp J L s.1
    (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2))

/-- Prime-decorated local prism sample. -/
noncomputable def decoratedVector
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat) (s : CoverVertexSlot hp (RelativeCollarMiddlePrism.cellSystem hp N L)) : Fin p →
      Real :=
  s.1 • localVector hp J L s.2

/-- Refined prism samples agree on every shared decorated geometric vertex. -/
theorem decoratedVector_eq_of_coverPoint_eq
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat)
    {a b : CoverVertexSlot hp (RelativeCollarMiddlePrism.cellSystem hp N L)}
    (hab : coverPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) a =
      coverPoint hp (RelativeCollarMiddlePrism.cellSystem hp N L) b) :
    decoratedVector hp J L a = decoratedVector hp J L b := by
  have hspatial := congrArg EquivariantPrismVertexParameters.CylinderPoint.spatial hab
  have htime := congrArg (fun z : EquivariantPrismVertexParameters.CylinderPoint p => z.time) hab
  let wa : StandardSimplex p :=
    StandardSimplex.ofDelta
      (affineCompMap p L a.2.1.2
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) a.2.2))
  let wb : StandardSimplex p :=
    StandardSimplex.ofDelta
      (affineCompMap p L b.2.1.2
        (SphereOddDegree.FiniteSimplex.vertex (S := Real) b.2.2))
  let za := staircasePoint hp a.2.1.1.2 wa
  let zb := staircasePoint hp b.2.1.1.2 wb
  have hzspatial :
      a.1 • RefinedAffineMap.chart hp N a.2.1.1.1 (StandardSimplex.toDelta za.1) =
      b.1 • RefinedAffineMap.chart hp N b.2.1.1.1 (StandardSimplex.toDelta zb.1) := by
    simpa [wa, wb, za, zb, coverPoint,
      RelativeAffineCellSystem.slotPoint, RelativeCollarMiddlePrism.cellSystem,
      RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex, SubdivisionPrismCharts.chart,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hspatial
  have hztime : za.2 = zb.2 := by
    simpa [wa, wb, za, zb, coverPoint,
      RelativeAffineCellSystem.slotPoint, RelativeCollarMiddlePrism.cellSystem,
      RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex, SubdivisionPrismCharts.chart,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using htime
  unfold decoratedVector localVector
  rw [refinedPrismValue_eq, refinedPrismValue_eq]
  change a.1 • J.value a.2.1.1.1 za.1 za.2 =
    b.1 • J.value b.2.1.1.1 zb.1 zb.2
  rw [← hztime]
  exact J.decorated_compatible a.1 b.1 a.2.1.1.1 b.2.1.1.1
    za.1 zb.1 za.2 hzspatial

/-- Global prism vector by quotient descent. -/
noncomputable def globalVector
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat) :
    GlobalVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L) → Fin p → Real :=
  Quotient.lift (decoratedVector hp J L) (by
    intro a b hab
    exact decoratedVector_eq_of_coverPoint_eq hp J L hab)

/-- Equivariance of the descended middle-prism vector. -/
theorem globalVector_smul
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat)
    (g : PrimeSymmetry p) (x : GlobalVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L)) :
    globalVector hp J L (g • x) = g • globalVector hp J L x := by
  refine Quotient.inductionOn x ?_
  intro s
  rfl

/-- Compatible assignment obtained from chart-homotopy samples. -/
noncomputable def assignment
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat) :
    Assignment hp (RelativeCollarMiddlePrism.cellSystem hp N L) :=
  assignmentOfEquivariantVector (RelativeCollarMiddlePrism.cellSystem hp N L)
    (globalVector hp J L) (globalVector_smul hp J L)

@[simp] theorem localVertexMap_assignment_value
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat)
    (q : PrismCell hp N L) (i : Fin (p + 1)) :
    (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L)
      q).value i =
      refinedPrismValue hp J L q
        (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) := by
  rfl

/-- A positive norm margin valid on every base chart of a compatible chart homotopy. -/
theorem exists_positive_norm_margin
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) :
    ∃ M : Real, 0 < M ∧
      ∀ (q : BasePrismCell hp N) (w : StandardSimplex p),
        M ≤ ‖basePrismValue hp J q w‖ := by
  classical
  let Q := BasePrismCell hp N
  let : Nonempty Q := ⟨(RelativeCollarMiddlePrism.defaultTopCell hp N, ⟨0, hp.pos⟩)⟩
  have hmin : ∀ q : Q, ∃ w : StandardSimplex p,
      ∀ v : StandardSimplex p,
        ‖basePrismValue hp J q w‖ ≤ ‖basePrismValue hp J q v‖ := by
    intro q
    obtain ⟨w, hw⟩ := IsCompact.exists_isMinOn
      (isCompact_univ : IsCompact (Set.univ : Set (StandardSimplex p)))
      ⟨Classical.choice inferInstance, Set.mem_univ _⟩
      (continuous_norm.comp
        ((J.continuous_value q.1).comp (continuous_staircasePoint hp q.2))).continuousOn
    exact ⟨w, fun v => hw.2 (Set.mem_univ v)⟩
  let m : Q → Real := fun q =>
    ‖basePrismValue hp J q (Classical.choose (hmin q))‖
  let ms : Finset Real := Finset.univ.image m
  have hms : ms.Nonempty := by
    classical
    exact ⟨m (Classical.choice (inferInstance : Nonempty Q)),
      Finset.mem_image_of_mem m (Finset.mem_univ _)⟩
  refine ⟨ms.min' hms, ?_, ?_⟩
  · have hmem := Finset.min'_mem ms hms
    rcases Finset.mem_image.mp hmem with ⟨q, hq, hqe⟩
    rw [← hqe]
    exact norm_pos_iff.mpr (J.zeroFree q.1 _ _)
  · intro q w
    exact le_trans
      (Finset.min'_le ms (m q)
        (Finset.mem_image_of_mem m (Finset.mem_univ q)))
      ((Classical.choose_spec (hmin q)) w)

/-- Sufficient prism refinement makes every chart-homotopy value oscillate by less than `eps` on
one refined prism cell. -/
theorem exists_refinement_oscillation
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    {eps : Real} (heps : 0 < eps) :
    ∃ L : Nat, ∀ (q : PrismCell hp N L) (u v : StandardSimplex p),
      dist (refinedPrismValue hp J L q u)
        (refinedPrismValue hp J L q v) < eps := by
  classical
  let Q := BasePrismCell hp N
  let : Nonempty Q := ⟨(RelativeCollarMiddlePrism.defaultTopCell hp N, ⟨0, hp.pos⟩)⟩
  have huc : ∀ q : Q, UniformContinuous (basePrismValueMap hp J q) := by
    intro q
    exact CompactSpace.uniformContinuous_of_continuous
      (basePrismValueMap hp J q).continuous
  obtain ⟨delta, hdelta⟩ :
      ∃ delta : Q → Real, ∀ q, 0 < delta q ∧
        ∀ a b : Delta p, dist a b < delta q →
          dist ((basePrismValueMap hp J q) a)
            ((basePrismValueMap hp J q) b) < eps := by
    refine ⟨fun q => Classical.choose
      ((Metric.uniformContinuous_iff.1 (huc q)) eps heps), ?_⟩
    intro q
    exact Classical.choose_spec
      ((Metric.uniformContinuous_iff.1 (huc q)) eps heps)
  let ds : Finset Real := Finset.univ.image delta
  have hds : ds.Nonempty :=
    ⟨delta (Classical.choice (inferInstance : Nonempty Q)),
      Finset.mem_image_of_mem delta (Finset.mem_univ _)⟩
  let d := ds.min' hds
  have hdpos : 0 < d := by
    have hmem := Finset.min'_mem ds hds
    rcases Finset.mem_image.mp hmem with ⟨q, hq, hqe⟩
    change 0 < ds.min' hds
    rw [← hqe]
    exact (hdelta q).1
  have hdle : ∀ q : Q, d ≤ delta q := by
    intro q
    exact Finset.min'_le ds (delta q)
      (Finset.mem_image_of_mem delta (Finset.mem_univ q))
  obtain ⟨L, hL⟩ := exists_diam_range_affineCompMap_lt p d hdpos
  refine ⟨L, ?_⟩
  rintro ⟨q, rho⟩ u v
  apply (hdelta q).2
  apply lt_of_lt_of_le _ (hdle q)
  refine lt_of_le_of_lt
    (Metric.dist_le_diam_of_mem (s := Set.range (affineCompMap p L rho)) ?_ ?_ ?_) (hL rho)
  · exact (isCompact_range (affineCompMap p L rho).continuous).isBounded
  · exact ⟨StandardSimplex.toDelta u, rfl⟩
  · exact ⟨StandardSimplex.toDelta v, rfl⟩

/-- Affine interpolation of samples differs from the chart homotopy by at most the cell
oscillation. -/
theorem norm_affineValue_sub_refinedPrismValue_le
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1)
    (L : Nat) (q : PrismCell hp N L) (eps : Real)
    (hosc : ∀ u v : StandardSimplex p,
      dist (refinedPrismValue hp J L q u)
        (refinedPrismValue hp J L q v) < eps)
    (w : StandardSimplex p) :
    ‖affineValue
        (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L) q) w -
      refinedPrismValue hp J L q w‖ ≤ eps := by
  classical
  let y := refinedPrismValue hp J L q w
  have hid :
      affineValue
          (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L)
            q) w - y =
        ∑ i : Fin (p + 1), w i •
          (refinedPrismValue hp J L q
            (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) - y)
              := by
    funext c
    simp only [affineValue, localVertexMap_assignment_value, y, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, w.sum_eq_one, one_mul]
  rw [hid]
  calc
    ‖∑ i : Fin (p + 1), w i •
        (refinedPrismValue hp J L q
          (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) - y)‖
        ≤ ∑ i : Fin (p + 1),
          ‖w i • (refinedPrismValue hp J L q
            (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) - y)‖ :=
      norm_sum_le _ _
    _ = ∑ i : Fin (p + 1), w i *
        ‖refinedPrismValue hp J L q
          (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) - y‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (w.nonneg i)
      exact le_of_lt (by
        simpa [dist_eq_norm, y] using
          hosc (StandardSimplex.ofDelta (SphereOddDegree.FiniteSimplex.vertex (S := Real) i)) w)
    _ = eps := by rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- A sufficiently fine compatible chart-homotopy prism assignment avoids the origin on every
cell. -/
theorem exists_refinement_avoidsOrigin
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) :
    ∃ L : Nat, ∀ q : PrismCell hp N L,
      AvoidsOrigin
        (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L) q)
          := by
  obtain ⟨M, hM, hmargin⟩ := exists_positive_norm_margin hp J
  obtain ⟨L, hosc⟩ := exists_refinement_oscillation hp J
    (show 0 < M / 2 by positivity)
  refine ⟨L, ?_⟩
  intro q w
  let y := refinedPrismValue hp J L q w
  let z := affineValue
    (localVertexMap hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L) q) w
  have hclose : ‖z - y‖ ≤ M / 2 := by
    simpa [z, y] using
      norm_affineValue_sub_refinedPrismValue_le hp J L q (M / 2) (hosc q) w
  have hy : M ≤ ‖y‖ :=
    hmargin q.1
      (StandardSimplex.ofDelta (affineCompMap p L q.2 (StandardSimplex.toDelta w)))
  have hy_le : ‖y‖ ≤ ‖z - y‖ + ‖z‖ := by
    calc
      ‖y‖ = ‖-(z - y) + z‖ := by congr 1; module
      _ ≤ ‖-(z - y)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - y‖ + ‖z‖ := by rw [norm_neg]
  have hz : 0 < ‖z‖ := by linarith
  exact norm_pos_iff.mp hz

/-- Exact lower boundary value of the middle assignment. -/
theorem lower_boundary_value
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat)
    (s : (RelativeCollarMiddlePrism.cellSystem hp N L).VertexSlot)
    (hs : ((RelativeCollarMiddlePrism.cellSystem hp N L).slotPoint s).time.1 = 0) :
    vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L)
        (sampleVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L) s) =
      K0.value s.1.1.1
        (staircasePoint hp s.1.1.2
          (StandardSimplex.ofDelta
            (affineCompMap p L s.1.2
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).1 := by
  rw [assignment, vectorValue_assignmentOfEquivariantVector]
  change J.value s.1.1.1
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).1
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).2 = _
  have ht :
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).2 =
        (⟨0, by simp⟩ : Set.Icc (0 : Real) 1) := by
    apply Subtype.ext
    simpa [RelativeAffineCellSystem.slotPoint, RelativeCollarMiddlePrism.cellSystem,
      RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex, SubdivisionPrismCharts.chart,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hs
  rw [ht]
  exact J.value_zero _ _

/-- Exact upper boundary value of the middle assignment. -/
theorem upper_boundary_value
    (hp : Nat.Prime p) {N : Nat} {K0 K1 : ChartMap hp N}
    (J : ChartHomotopy hp N K0 K1) (L : Nat)
    (s : (RelativeCollarMiddlePrism.cellSystem hp N L).VertexSlot)
    (hs : ((RelativeCollarMiddlePrism.cellSystem hp N L).slotPoint s).time.1 = 1) :
    vectorValue hp (RelativeCollarMiddlePrism.cellSystem hp N L) (assignment hp J L)
        (sampleVertex hp (RelativeCollarMiddlePrism.cellSystem hp N L) s) =
      K1.value s.1.1.1
        (staircasePoint hp s.1.1.2
          (StandardSimplex.ofDelta
            (affineCompMap p L s.1.2
              (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).1 := by
  rw [assignment, vectorValue_assignmentOfEquivariantVector]
  change J.value s.1.1.1
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).1
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2 (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).2 = _
  have ht :
      (staircasePoint hp s.1.1.2
        (StandardSimplex.ofDelta
          (affineCompMap p L s.1.2
            (SphereOddDegree.FiniteSimplex.vertex (S := Real) s.2)))).2 =
        (⟨1, by simp⟩ : Set.Icc (0 : Real) 1) := by
    apply Subtype.ext
    simpa [RelativeAffineCellSystem.slotPoint, RelativeCollarMiddlePrism.cellSystem,
      RelativeCollarMiddlePrism.vertex,
      SubdivisionPrismCharts.vertex, SubdivisionPrismCharts.chart,
      EquivariantPrismVertexParameters.CylinderPoint.ofProd] using hs
  rw [ht]
  exact J.value_one _ _



end CompatibleRefinedChartHomotopyPrism
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
