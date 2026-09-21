/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaSmooth
public import LeanPool.PoincareGeometry.AlmostSchur.DivergenceCoordinates
public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothLocalFlow
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Smoothness of actual coordinate connection coefficients -/

@[expose] public noncomputable section
open Bundle FiberBundle Set AlmostSchur
open scoped Manifold ContDiff Topology BigOperators

namespace LichnerowiczObata
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle ∞ E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

local instance bundle_order (n : ℕ) : ContMDiffVectorBundle (n : ℕ∞ω) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞)
    (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))

local instance bundle_order_succ (n : ℕ) : ContMDiffVectorBundle ((n : ℕ∞ω) + 1) E TM I :=
  ContMDiffVectorBundle.of_le (n := ∞) (by exact_mod_cast (le_top : (n + 1 : ℕ∞) ≤ ⊤))

omit [FiniteDimensional ℝ E] in
/-- Finite-order regularity of a section transfers to its actual coordinates
in any fixed chart containing the evaluation point. -/
theorem contDiffAt_coordinateVectorField_of_order (n : ℕ) (X : Π y : M, TM y)
    (c x : M) (hx : x ∈ (chartAt H c).source)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n (T% X) x) :
    ContDiffAt ℝ n (coordinateVectorField (I := I) c X) (extChartAt I c x) := by
  let e := trivializationAt E TM c
  have hg := (e.contMDiffAt_section_iff (IB := I) hx).mp hX
  have he : ContMDiffAt I 𝓘(ℝ, E) n
      (fun y => e.continuousLinearMapAt ℝ y (X y)) x := by
    apply hg.congr_of_eventuallyEq
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    exact e.continuousLinearMapAt_apply_of_mem ℝ hy _
  have hi : ContMDiffAt 𝓘(ℝ, E) I n (extChartAt I c).symm (extChartAt I c x) :=
    (contMDiffOn_extChartAt_symm c).contMDiffAt
      ((isOpen_extChartAt_target c).mem_nhds ((extChartAt I c).map_source (by simpa using hx)))
  exact (he.comp_of_eq hi ((extChartAt I c).left_inv (by simpa using hx))).contDiffAt

variable [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]

/-- Every basis entry of the genuine metric torsion-free connection is smooth
in the coordinate point. No independent Christoffel regularity is assumed. -/
theorem contDiffOn_coordinateConnection_basis (n : ℕ)
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) (i j : ι) :
    ContDiffOn ℝ n (fun z => frameConnectionCoefficients cov (trivializationAt E TM c)
      b ((extChartAt I c).symm z) (b i) (b j)) (extChartAt I c).target := by
  intro z hz
  let x := (extChartAt I c).symm z
  let e := trivializationAt E TM c
  have hx : x ∈ (chartAt H c).source := by
    simpa only [extChartAt_source] using (extChartAt I c).map_target hz
  have hX := contMDiffAt_localFrame_of_mem (I := I) ((n : ℕ∞ω) + 1) e b i hx
  have hY := contMDiffAt_localFrame_of_mem (I := I) ((n : ℕ∞ω) + 1) e b j hx
  have hC := contMDiffAt_covariantAlong_of_metric_torsion_of_order n cov hm ht hX hY
  have hcoord := contDiffAt_coordinateVectorField_of_order n _ c x hx hC
  have he : extChartAt I c x = z := (extChartAt I c).right_inv hz
  rw [he] at hcoord
  have hfun : (fun y => frameConnectionCoefficients cov e b ((extChartAt I c).symm y) (b i) (b j)) =
      coordinateVectorField c (fun y => cov (e.localFrame b j) y (e.localFrame b i y)) := by
    funext y
    simp only [frameConnectionCoefficients_basis, coordinateVectorField, localFrame_eq_symmL, e]
  rw [hfun]
  exact hcoord.contDiffWithinAt

omit [FiniteDimensional ℝ E] in
/-- Finite-basis expansion of a continuous bilinear map on a repeated vector. -/
theorem bilinear_diagonal_basis_expansion {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] F) (v : E) :
    B v v = ∑ i, ∑ j, (b.repr v i * b.repr v j) • B (b i) (b j) := by
  classical
  calc
    B v v = B (∑ i, b.repr v i • b i) (∑ j, b.repr v j • b j) := by rw [b.sum_repr]
    _ = _ := by
      simp only [map_sum, sum_apply, map_smul, smul_apply, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_comm]

/-- The coordinate geodesic vector field on position-velocity pairs, using
the actual connection coefficients. -/
def coordinateGeodesicSpray (cov : CovariantDerivative I E TM)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) (q : E × E) : E × E :=
  (q.2, -frameConnectionCoefficients cov (trivializationAt E TM c)
    b ((extChartAt I c).symm q.1) q.2 q.2)

/-- The geodesic vector field inherits every finite smoothness order from
the genuine smooth metric connection. -/
theorem contDiffOn_coordinateGeodesicSpray (n : ℕ)
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) :
    ContDiffOn ℝ n (coordinateGeodesicSpray cov b c)
      ((extChartAt I c).target ×ˢ (univ : Set E)) := by
  classical
  let Γ := fun z => frameConnectionCoefficients cov (trivializationAt E TM c)
    b ((extChartAt I c).symm z)
  have he (q : E × E) : Γ q.1 q.2 q.2 =
      ∑ i, ∑ j, (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j) :=
    bilinear_diagonal_basis_expansion b (Γ q.1) q.2
  have ha : ContDiffOn ℝ n (fun q : E × E => Γ q.1 q.2 q.2)
      ((extChartAt I c).target ×ˢ (univ : Set E)) := by
    have hs : ContDiffOn ℝ n (fun q : E × E =>
        ∑ i, ∑ j, (b.repr q.2 i * b.repr q.2 j) • Γ q.1 (b i) (b j))
        ((extChartAt I c).target ×ˢ (univ : Set E)) := by
      apply ContDiffOn.sum
      intro i _
      apply ContDiffOn.sum
      intro j _
      have hi : ContDiff ℝ n (fun q : E × E => b.repr q.2 i) :=
        (b.coord i).toContinuousLinearMap.contDiff.comp contDiff_snd
      have hj : ContDiff ℝ n (fun q : E × E => b.repr q.2 j) :=
        (b.coord j).toContinuousLinearMap.contDiff.comp contDiff_snd
      exact (hi.mul hj).contDiffOn.smul
        ((contDiffOn_coordinateConnection_basis n cov hm ht b c i j).comp
          contDiffOn_fst (fun _ hq => hq.1))
    exact hs.congr (fun q _ => he q)
  exact contDiffOn_snd.prodMk ha.neg

/-- The genuine coordinate geodesic equation has a jointly smooth local
solution family near every position-velocity pair in the chart. -/
theorem exists_smooth_coordinate_geodesic_flow (n : ℕ) (hn : n ≠ 0)
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E) (c : M) {z u : E}
    (hz : z ∈ (extChartAt I c).target) :
    ∃ V ∈ 𝓝 (z, u), ∃ δ : ℝ, 0 < δ ∧
      ∃ α : (E × E) × ℝ → E × E,
        ContDiffOn ℝ n α (V ×ˢ Metric.ball 0 δ) ∧
        ∀ q ∈ V, α (q, 0) = q ∧
          ∀ s ∈ Metric.ball 0 δ, (α (q, s)).1 ∈ (extChartAt I c).target ∧
            HasDerivAt (fun t => α (q, t))
              (coordinateGeodesicSpray cov b c (α (q, s))) s := by
  have hD : IsOpen ((extChartAt I c).target ×ˢ (univ : Set E)) :=
    (isOpen_extChartAt_target c).prod isOpen_univ
  have hp : (z, u) ∈ (extChartAt I c).target ×ˢ (univ : Set E) := ⟨hz, mem_univ _⟩
  have hs := (contDiffOn_coordinateGeodesicSpray n cov hm ht b c).contDiffAt (hD.mem_nhds hp)
  obtain ⟨V, hV, δ, hδ, α, hα, hsol⟩ := exists_smooth_local_flow n hn hs (hD.mem_nhds hp)
  refine ⟨V, hV, δ, hδ, α, hα, ?_⟩
  intro q hq
  refine ⟨(hsol q hq).1, ?_⟩
  intro s hs
  exact ⟨((hsol q hq).2 s hs).1.1, ((hsol q hq).2 s hs).2⟩

end LichnerowiczObata
