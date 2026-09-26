/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Transport
public import LeanPool.PoincareGeometry.BonnetMyers.MetricParallelAlgebra
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.DowngradeNormFree

/-!
# The local covariant derivative of a coordinate field

This file supplies the first genuinely geometric transport bridge.  A model
vector is converted to a tangent section by the inverse of the chart
trivialization.  In a region where the smooth frame used to define the
coefficient germ agrees with the canonical local frame, the bundled
covariant-derivative API gives exactly the coordinate formula used by the
parallel ODE.

The agreement hypothesis is explicit because `LocalGeodesicData` uses smooth
global extensions of local frame vectors in order to expose regularity to the
ODE theorem.  It is discharged on a neighbourhood of the chart centre, and
must not be silently replaced by a global frame identity.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

namespace LocalGeodesicData

variable [RiemannianBundle (TangentSpace I : M → Type _)]

lemma coordinateFrameCombination_contMDiffAt
    (x₀ y : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u : E) (hy : y ∈ (chartAt H x₀).source) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u z)) y := by
  let e := trivializationAt E TM x₀
  have hbase : y ∈ e.baseSet := by
    simpa [e] using hy
  have hterm : ∀ j : Fin (Module.finrank ℝ E),
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
        (fun z ↦ TotalSpace.mk' E z
          ((b.repr u j) • e.localFrame b j z)) y := by
    intro j
    have hframe := contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
      (n := (1 : WithTop ℕ∞)) j hbase
    have hconst : ContMDiffAt I 𝓘(ℝ) 1 (fun _ : M ↦ b.repr u j) y :=
      contMDiffAt_const
    simpa [e] using hconst.smul_section hframe
  have hsum := ContMDiffAt.sum_section
    (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
    (fun j _hj ↦ hterm j)
  simpa [coordinateFrameCombination, e] using hsum

lemma cov_coordinateFrameCombination_apply
    (cov : CovariantDerivative I E TM) (x₀ y : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u w : E) (hy : y ∈ (chartAt H x₀).source)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    cov (fun z ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b w z) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) =
      coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
        (coordinateParallelOperator (I := I) (M := M) (E := E)
          cov x₀ b (extChartAt I x₀ y) u w) y := by
  let e := trivializationAt E TM x₀
  have hbase : y ∈ e.baseSet := by
    simpa [e] using hy
  have hσ : MDiffAt (T% (fun z ↦ coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b w z)) y := by
    exact (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b w hy).mdifferentiableAt one_ne_zero
  have hdecomp := CovariantDerivative.TangentFrame.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I) (E := E) e b cov hbase hσ
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
  have hcoeff_const : ∀ i : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        e.localFrameCoeff I b i z
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w z) =
        b.repr w i := by
    intro i
    have hbase' : ∀ᶠ z in 𝓝 y, z ∈ e.baseSet :=
      e.open_baseSet.mem_nhds hbase
    filter_upwards [hbase'] with z hz
    have hcoeff := e.localFrameCoeff_apply_of_mem_baseSet
      (I := I) (b := b) hz
      (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w) i
    rw [hcoeff]
    have hlocal : ∀ j : Fin (Module.finrank ℝ E),
        e.localFrame b j z =
          (b.map (e.linearEquivAt ℝ z hz).symm) j := by
      intro j
      exact e.localFrame_apply_of_mem_baseSet (b := b) hz
    have hsum : (e.basisAt b hz).repr
        (∑ j : Fin (Module.finrank ℝ E), (b.repr w j) • e.localFrame b j z) =
        ∑ j : Fin (Module.finrank ℝ E),
          (b.repr w j) • (e.basisAt b hz).repr (e.localFrame b j z) := by
      simpa using
        (map_sum (e.basisAt b hz).repr
          (fun j : Fin (Module.finrank ℝ E) ↦ (b.repr w j) • e.localFrame b j z)
          Finset.univ)
    have hrepr : ∀ j : Fin (Module.finrank ℝ E),
        (e.basisAt b hz).repr (e.localFrame b j z) i =
          if i = j then 1 else 0 := by
      intro j
      rw [e.localFrame_apply_of_mem_baseSet (b := b) hz]
      simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
    have hsum_i := congrArg
      (fun r : (Fin (Module.finrank ℝ E) →₀ ℝ) ↦ r i) hsum
    simpa [coordinateFrameCombination, e, hrepr] using hsum_i
  have hcoeff : ∀ i j k : Fin (Module.finrank ℝ E),
      connectionCoefficient (I := I) (M := M) (E := E)
          cov x₀ b i j k y =
        e.localFrameCoeff I b i y
          (cov (e.localFrame b j) y (e.localFrame b k y)) := by
    intro i j k
    let sj : Set M := {z |
      smoothFrame (I := I) (M := M) (E := E) x₀ b j z = e.localFrame b j z}
    let sk : Set M := {z |
      smoothFrame (I := I) (M := M) (E := E) x₀ b k z = e.localFrame b k z}
    have hs : sj ∩ sk ∈ 𝓝 y := by
      filter_upwards [hframe j, hframe k] with z hzj hzk
      exact ⟨hzj, hzk⟩
    have hsmj : MDiffAt (T% (smoothFrame
        (I := I) (M := M) (E := E) x₀ b j)) y := by
      have h := CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x₀
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j x₀)
      have h' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
          (fun z ↦ TotalSpace.mk' E z
            (smoothFrame (I := I) (M := M) (E := E) x₀ b j z)) y :=
        (h.contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
          (fun z ↦ TotalSpace.mk' E z
            (smoothFrame (I := I) (M := M) (E := E) x₀ b j z)) y).of_le
          (by norm_num)
      simpa only [ModelWithCorners.tangent] using h'.mdifferentiableAt
        (by norm_num)
    have hsmk : MDiffAt (T% (smoothFrame
        (I := I) (M := M) (E := E) x₀ b k)) y := by
      have h := CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x₀
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b k x₀)
      have h' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
          (fun z ↦ TotalSpace.mk' E z
            (smoothFrame (I := I) (M := M) (E := E) x₀ b k z)) y :=
        (h.contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2
          (fun z ↦ TotalSpace.mk' E z
            (smoothFrame (I := I) (M := M) (E := E) x₀ b k z)) y).of_le
          (by norm_num)
      simpa only [ModelWithCorners.tangent] using h'.mdifferentiableAt
        (by norm_num)
    have hlocj : MDiffAt (T% (e.localFrame b j)) y :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := (1 : WithTop ℕ∞)) j hbase).mdifferentiableAt one_ne_zero
    have hlock : MDiffAt (T% (e.localFrame b k)) y :=
      (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := (1 : WithTop ℕ∞)) k hbase).mdifferentiableAt one_ne_zero
    have hcovj : cov (smoothFrame (I := I) (M := M) (E := E) x₀ b j) y =
        cov (e.localFrame b j) y := by
      apply (cov.isCovariantDerivativeOn (s := sj ∩ sk)).congr_of_eqOn
        hsmj hlocj hs
      intro z hz
      exact hz.1
    have hcovk : cov (smoothFrame (I := I) (M := M) (E := E) x₀ b k) y =
        cov (e.localFrame b k) y := by
      apply (cov.isCovariantDerivativeOn (s := sj ∩ sk)).congr_of_eqOn
        hsmk hlock hs
      intro z hz
      exact hz.2
    have hyk : smoothFrame (I := I) (M := M) (E := E) x₀ b k y =
        e.localFrame b k y := by
      have hy_mem : y ∈ {z : M |
          smoothFrame (I := I) (M := M) (E := E) x₀ b k z = e.localFrame b k z} :=
        mem_of_mem_nhds (show {z : M |
          smoothFrame (I := I) (M := M) (E := E) x₀ b k z = e.localFrame b k z} ∈
            𝓝 y from hframe k)
      exact hy_mem
    simp [connectionCoefficient, e, hcovj, hcovk, hyk]
  have hcoeff_point : ∀ i : Fin (Module.finrank ℝ E),
      (LinearMap.piApply (e.localFrameCoeff I b i))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w) y =
        b.repr w i := by
    intro i
    have hy_mem : y ∈ {z : M |
        e.localFrameCoeff I b i z
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w z) =
          b.repr w i} :=
      mem_of_mem_nhds (show {z : M |
        e.localFrameCoeff I b i z
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w z) =
          b.repr w i} ∈ 𝓝 y from hcoeff_const i)
    exact hy_mem
  have hderiv_zero : ∀ i : Fin (Module.finrank ℝ E),
      mvfderiv (I := I)
          ((LinearMap.piApply (e.localFrameCoeff I b i))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w)) y = 0 := by
    intro i
    have heq :
        (LinearMap.piApply (e.localFrameCoeff I b i))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w) =ᶠ[𝓝 y]
          (fun _ : M ↦ b.repr w i) := by
      filter_upwards [hcoeff_const i] with z hz
      simpa only [LinearMap.piApply_apply] using hz
    have hconst : HasMFDerivAt I 𝓘(ℝ)
        (fun _ : M ↦ b.repr w i) y 0 := by
      simpa using (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ))
        (x := y) (c := b.repr w i))
    have hhas : HasMFDerivAt I 𝓘(ℝ)
        ((LinearMap.piApply (e.localFrameCoeff I b i))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w)) y 0 :=
      hconst.congr_of_eventuallyEq heq
    simp only [mvfderiv]
    rw [hhas.mfderiv]
    ext v
    rw [ContinuousLinearMap.comp_apply]
    rw [ContinuousLinearMap.zero_apply]
    exact map_zero _
  have hframe_expand : ∀ i k : Fin (Module.finrank ℝ E),
      cov (e.localFrame b i) y (e.localFrame b k y) =
        ∑ l, e.localFrameCoeff I b l y
          (cov (e.localFrame b i) y (e.localFrame b k y)) • e.localFrame b l y := by
    intro i k
    let v : TangentSpace I y := cov (e.localFrame b i) y (e.localFrame b k y)
    have hsum := Module.Basis.sum_repr (e.basisAt b hbase) v
    have hsum' : v = ∑ l, e.localFrameCoeff I b l y v • e.localFrame b l y := by
      symm
      calc
        ∑ l, e.localFrameCoeff I b l y v • e.localFrame b l y =
            ∑ l, ((e.basisAt b hbase).repr v) l • (e.basisAt b hbase) l := by
              apply Finset.sum_congr rfl
              intro l hl
              have hcoeff_v := e.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (b := b) hbase (FiberBundle.extend E v) l
              have hcoeff_v' : e.localFrameCoeff I b l y v =
                  ((e.basisAt b hbase).repr v) l := by
                simpa only [FiberBundle.extend_apply_self] using hcoeff_v
              rw [hcoeff_v', e.localFrame_apply_of_mem_baseSet (b := b) hbase]
        _ = v := hsum
    simpa [v] using hsum'
  have hconnection_expand : ∀ i k : Fin (Module.finrank ℝ E),
      cov (e.localFrame b i) y (e.localFrame b k y) =
        ∑ l, connectionCoefficient (I := I) (M := M) (E := E)
          cov x₀ b l i k y • e.localFrame b l y := by
    intro i k
    rw [hframe_expand i k]
    apply Finset.sum_congr rfl
    intro l hl
    rw [← hcoeff l i k]
  have hcov_expand : ∀ i : Fin (Module.finrank ℝ E),
      cov (e.localFrame b i) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) =
        ∑ k, (b.repr u k) • cov (e.localFrame b i) y (e.localFrame b k y) := by
    intro i
    unfold coordinateFrameCombination
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [map_smul]
  have hderiv_term :
      (∑ i, (mvfderiv (I := I)
          ((LinearMap.piApply (e.localFrameCoeff I b i))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w)) y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) •
        e.localFrame b i y) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hderiv_zero i]
    simp
  have hcoeff_term :
      (∑ i, (LinearMap.piApply (e.localFrameCoeff I b i))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w) y •
        cov (e.localFrame b i) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)) =
      ∑ i, (b.repr w i) • cov (e.localFrame b i) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hcoeff_point i]
  calc
    cov (fun z ↦ coordinateFrameCombination (I := I) (M := M)
        (x₀ := x₀) b w z) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) =
      (∑ i, (mvfderiv (I := I)
          ((LinearMap.piApply (e.localFrameCoeff I b i))
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w)) y)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) •
        e.localFrame b i y) +
      ∑ i, (LinearMap.piApply (e.localFrameCoeff I b i))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w) y •
        cov (e.localFrame b i) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) := hdecomp
    _ = ∑ i, (b.repr w i) • cov (e.localFrame b i) y
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) := by
      rw [hderiv_term, zero_add, hcoeff_term]
    _ = ∑ i, (b.repr w i) •
          (∑ k, (b.repr u k) • cov (e.localFrame b i) y
            (e.localFrame b k y)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcov_expand i]
    _ = coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u w) y := by
      simp_rw [hconnection_expand]
      simp only [Finset.smul_sum]
      unfold coordinateFrameCombination
      have hop : ∀ j : Fin (Module.finrank ℝ E),
          b.repr (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u w) j =
            ∑ i, ∑ k, (b.repr w i) * (b.repr u k) *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b j i k y := by
        intro j
        have hsource : y ∈ (extChartAt I x₀).source := by
          rw [extChartAt_source]
          exact hy
        have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) y) = y :=
          (extChartAt I x₀).left_inv hsource
        rw [coordinateParallelOperator_apply]
        rw [hleft]
        simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
      simp_rw [hop]
      simp_rw [smul_smul]
      simp only [mul_assoc, e]
      simp only [Finset.sum_smul]
      calc
        (∑ i, ∑ k, ∑ l,
            ((b.repr w i) * ((b.repr u k) *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b l i k y)) •
              (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b l y) =
          ∑ i, ∑ l, ∑ k,
            ((b.repr w i) * ((b.repr u k) *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b l i k y)) •
              (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b l y := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ k,
            ((b.repr w i) * ((b.repr u k) *
              connectionCoefficient (I := I) (M := M) (E := E)
                cov x₀ b l i k y)) •
              (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b l y := by
            exact Finset.sum_comm

/-! ### Metric compatibility in the same local frame

The preceding identity reads the connection coefficients from the canonical
chart frame.  The next lemma combines it with the metric-compatibility field
of the actual Levi--Civita connection.  This is deliberately pointwise and
keeps the frame-agreement hypothesis explicit; it is the local ingredient
needed before a global transport or continuation argument can be assembled.
-/

lemma coordinateFrameCombination_metric_deriv
    (cov : CovariantDerivative I E TM) (x₀ y : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u w v : E) (hy : y ∈ (chartAt H x₀).source)
    (hmetric : cov.IsMetricCompatibleTangent)
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 y,
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    mvfderiv (I := I)
        (fun z ↦ inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w z)
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v z)) y
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y) =
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u w) y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y) +
      inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w y)
        (coordinateFrameCombination (I := I) (M := M) (E := E)
          (x₀ := x₀) b
          (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ y) u v) y) := by
  have hσ : MDiffAt (T% (coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b w)) y :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b w hy).mdifferentiableAt one_ne_zero
  have hτ : MDiffAt (T% (coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b v)) y :=
    (coordinateFrameCombination_contMDiffAt (I := I) (M := M)
      (x₀ := x₀) y b v hy).mdifferentiableAt one_ne_zero
  have hmetric' := hmetric (x := y) (σ := coordinateFrameCombination
      (I := I) (M := M) (x₀ := x₀) b w)
    (τ := coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v)
    hσ hτ (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
  have hcovw := cov_coordinateFrameCombination_apply
    (I := I) (M := M) (E := E) cov x₀ y b u w hy hframe
  have hcovv := cov_coordinateFrameCombination_apply
    (I := I) (M := M) (E := E) cov x₀ y b u v hy hframe
  simpa only [hcovw, hcovv] using hmetric'

lemma coordinateFrameCombination_inner_hasDerivAt
    (cov : CovariantDerivative I E TM) (x₀ : M)
    (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    {γ : ℝ → M} {t : ℝ}
    {γ' : TangentSpace 𝓘(ℝ, ℝ) t →L[ℝ] TangentSpace I (γ t)}
    (u w v : E)
    (hγ : HasMFDerivAt (𝓘(ℝ, ℝ)) I γ t γ')
    (hγ' : γ' 1 = coordinateFrameCombination (I := I) (M := M)
      (x₀ := x₀) b u (γ t))
    (hy : γ t ∈ (chartAt H x₀).source)
    (hmetric : cov.IsMetricCompatibleTangent)
    [IsContMDiffRiemannianBundle I 1 E TM]
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    (hframe : ∀ j : Fin (Module.finrank ℝ E),
      ∀ᶠ z in 𝓝 (γ t),
        smoothFrame (I := I) (M := M) (E := E) x₀ b j z =
          (trivializationAt E TM x₀).localFrame b j z) :
    HasDerivAt
      (fun s ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w (γ s))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v (γ s)))
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b
          (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ (γ t)) u w) (γ t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v (γ t)) +
       inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w (γ t))
        (coordinateFrameCombination (I := I) (M := M) (E := E)
          (x₀ := x₀) b
          (coordinateParallelOperator (I := I) (M := M) (E := E)
            cov x₀ b (extChartAt I x₀ (γ t)) u v) (γ t))) t := by
  have hσ := coordinateFrameCombination_contMDiffAt (I := I) (M := M)
    (x₀ := x₀) (γ t) b w hy
  have hτ := coordinateFrameCombination_contMDiffAt (I := I) (M := M)
    (x₀ := x₀) (γ t) b v hy
  have hinner : ContMDiffAt I 𝓘(ℝ) 1
      (fun y ↦ inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y)) (γ t) :=
    ContMDiffAt.inner_bundle (F := E) (B := M)
      (E := (TangentSpace I : M → Type _)) (IM := I) (b := fun y : M ↦ y)
      hσ hτ
  have hcomp := hinner.mdifferentiableAt one_ne_zero |>.hasMFDerivAt.comp t hγ
  have hpoint := coordinateFrameCombination_metric_deriv
    (I := I) (M := M) (E := E) cov x₀ (γ t) b u w v hy hmetric hframe
  have htan : HasFDerivAt
      (fun s : TangentSpace 𝓘(ℝ, ℝ) t ↦
        inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w (γ s))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v (γ s)))
      ((mfderiv (I := I) 𝓘(ℝ)
          (fun y ↦ inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y))
          (γ t)) ∘SL γ') t :=
    hcomp.hasFDerivAt
  have hstd := htan.comp_semilinear
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ)
      (inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w (γ t))
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v (γ t)))).toContinuousLinearMap)
    ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm.toContinuousLinearMap)
  have hstd' := hstd.hasDerivAt
  refine (hstd'.congr_deriv ?_).congr_of_eventuallyEq ?_
  · change
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ)
        (inner ℝ
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w (γ t))
          (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v (γ t)))).toContinuousLinearMap)
        ((mfderiv (I := I) 𝓘(ℝ)
          (fun y ↦ inner ℝ
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b w y)
            (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y))
          (γ t)) (γ' ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1))) = _
    simp only [mvfderiv] at hpoint
    rw [ContinuousLinearMap.comp_apply] at hpoint
    have hunit :
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1 =
          (1 : TangentSpace 𝓘(ℝ, ℝ) t) := by
      rfl
    rw [hunit]
    simpa only [NormedSpace.fromTangentSpace, hγ'] using hpoint
  · filter_upwards [] with s
    rfl

lemma coordinateFrameCombination_inner_expand
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (u v : E) (y : M) :
    inner ℝ
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b u y)
        (coordinateFrameCombination (I := I) (M := M) (x₀ := x₀) b v y) =
      ∑ i, ∑ j, (b.repr u i) * (b.repr v j) *
        inner ℝ
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i y)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j y) := by
  simp only [coordinateFrameCombination, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right]
  calc
    _ = ∑ j, ∑ i, (b.repr v i) * (b.repr u j) *
        inner ℝ
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j y)
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b i y) := by
      rw [Finset.sum_comm]
      simp_rw [mul_assoc]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring

end LocalGeodesicData

end BonnetMyersEntry
