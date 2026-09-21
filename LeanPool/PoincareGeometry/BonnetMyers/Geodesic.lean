/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.Connection
import LeanPool.PoincareGeometry.BonnetMyers.ODE

/-!
# Local coordinate geodesic data

This file begins the geodesic part of the Bonnet--Myers argument.  The
coordinate acceleration is built from the supplied covariant derivative and
the tangent-bundle trivialization of an extended chart.  In particular, the
Christoffel data below is not an additional input field.
-/

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
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
  (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)

noncomputable def smoothFrame
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
  CovariantDerivative.smoothExtend (I := I) (F := E) (V := TM) x₀
    ((trivializationAt E TM x₀).localFrame b j x₀)

lemma smoothFrame_eventuallyEq_localFrame
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) :
    ∀ᶠ y in 𝓝 x₀,
      smoothFrame (I := I) (M := M) (E := E) x₀ b j y =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j y := by
  simpa [smoothFrame] using
    (CovariantDerivative.smoothExtend_trivializationAt_localFrame_eventuallyEq
      (I := I) (F := E) (V := (TangentSpace I : M → Type _)) b x₀ j)

/-- The `i,j,k` connection coefficient in the tangent frame of the chart at `x₀`.

The two frame sections are the canonical smooth extensions of the local
tangent frame.  They agree with that local frame on a neighbourhood of `x₀`,
so this is the actual Levi--Civita coefficient germ, while remaining a global
section to which the regularity API applies. -/
def connectionCoefficient
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (i j k : Fin (Module.finrank ℝ E)) (y : M) : ℝ :=
  (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrameCoeff I b i y
    (cov (smoothFrame (x₀ := x₀) (b := b) j) y
      (smoothFrame (x₀ := x₀) (b := b) k y))

lemma connectionCoefficient_eventuallyEq_localFrame
    (i j k : Fin (Module.finrank ℝ E)) :
    ∀ᶠ y in 𝓝 x₀,
      connectionCoefficient cov x₀ b i j k y =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrameCoeff I b i y
          (cov ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) y
            ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b k y)) := by
  have hje := smoothFrame_eventuallyEq_localFrame
    (I := I) (M := M) (E := E) x₀ b j
  have hke := smoothFrame_eventuallyEq_localFrame
    (I := I) (M := M) (E := E) x₀ b k
  have hframej : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) z
        (smoothFrame (x₀ := x₀) (b := b) j z)) :=
    by simpa [smoothFrame] using
      CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x₀
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j x₀)
  have hframek : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) z
        (smoothFrame (x₀ := x₀) (b := b) k z)) :=
    by simpa [smoothFrame] using
      CovariantDerivative.smoothExtend_contMDiff_two
        (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x₀
          ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b k x₀)
  have hbase : (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀)
  obtain ⟨Uj, hUj, hUjopen, hxUj⟩ := mem_nhds_iff.mp hje
  obtain ⟨Uk, hUk, hUkopen, hxUk⟩ := mem_nhds_iff.mp hke
  let U : Set M := Uj ∩ Uk ∩
    (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (hUjopen.inter hUkopen).inter
      (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet
  have hxU : x₀ ∈ U := by
    dsimp [U]
    exact ⟨⟨hxUj, hxUk⟩, mem_baseSet_trivializationAt E
      (TangentSpace I : M → Type _) x₀⟩
  have hUmem : U ∈ 𝓝 x₀ := hUopen.mem_nhds hxU
  filter_upwards [hUmem] with y hy
  have hy' : y ∈ Uj ∩ Uk ∩
      (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
    simpa [U] using hy
  have hyj : smoothFrame (x₀ := x₀) (b := b) j y =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j y :=
    hUj hy'.1.1
  have hyk : smoothFrame (x₀ := x₀) (b := b) k y =
      (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b k y :=
    hUk hy'.1.2
  have hcovj : cov (smoothFrame (x₀ := x₀) (b := b) j) y =
      cov ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j) y := by
    apply IsCovariantDerivativeOn.congr_of_eqOn cov.isCovariantDerivativeOn
    · simpa only [ModelWithCorners.tangent] using
        (hframej.contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 _ y).mdifferentiableAt
          (by norm_num)
    · exact ((Bundle.Trivialization.contMDiffOn_localFrame_baseSet
        (I := I) (e := trivializationAt E (TangentSpace I : M → Type _) x₀)
        (n := (2 : WithTop ℕ∞)) b j) y hy'.2).contMDiffAt
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds hy'.2)
        |>.mdifferentiableAt (by norm_num)
    · exact hUopen.mem_nhds hy
    · intro z hz
      exact hUj hz.1.1
  have hcovk : cov (smoothFrame (x₀ := x₀) (b := b) k) y =
      cov ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b k) y := by
    apply IsCovariantDerivativeOn.congr_of_eqOn cov.isCovariantDerivativeOn
    · simpa only [ModelWithCorners.tangent] using
        (hframek.contMDiffAt : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 _ y).mdifferentiableAt
          (by norm_num)
    · exact ((Bundle.Trivialization.contMDiffOn_localFrame_baseSet
        (I := I) (e := trivializationAt E (TangentSpace I : M → Type _) x₀)
        (n := (2 : WithTop ℕ∞)) b k) y hy'.2).contMDiffAt
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds hy'.2)
        |>.mdifferentiableAt (by norm_num)
    · exact hUopen.mem_nhds hy
    · intro z hz
      exact hUk hz.1.2
  simp only [connectionCoefficient, hcovj, hcovk, hyk]

private noncomputable def smoothConnectionSection
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j k : Fin (Module.finrank ℝ E)) : Π y : M, TangentSpace I y :=
  fun y ↦ cov (smoothFrame (x₀ := x₀) (b := b) j) y
    (smoothFrame (x₀ := x₀) (b := b) k y)

include I M E
private lemma smoothFrame_contMDiff
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (j : Fin (Module.finrank ℝ E)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) 2
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) y
        (smoothFrame (x₀ := x₀) (b := b) j y)) := by
  simpa [smoothFrame] using
    (CovariantDerivative.smoothExtend_contMDiff_two
      (I := I) (F := E) (V := (TangentSpace I : M → Type _)) x₀
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).localFrame b j x₀))

private lemma smoothConnectionSection_contMDiffAt
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) y
        (smoothConnectionSection cov x₀ b j k y)) x₀ := by
  let hcov :=
    (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative cov 1).contMDiff
  have hcov' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        y (cov (smoothFrame (x₀ := x₀) (b := b) j) y)) := by
    have hframe_global : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) y
          (smoothFrame (x₀ := x₀) (b := b) j y)) :=
      smoothFrame_contMDiff (I := I) (M := M) (E := E) (x₀ := x₀) (b := b) j
    have hframe_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) y
          (smoothFrame (x₀ := x₀) (b := b) j y)) (Set.univ : Set M) := by
      simpa only [contMDiffOn_univ] using hframe_global
    simpa [contMDiffOn_univ, smoothFrame] using
      hcov.contMDiff
        (hframe_on.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞)))
  have hcov_at := hcov' x₀
  have hframe_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E (E := TangentSpace I) y
        (smoothFrame (x₀ := x₀) (b := b) k y)) x₀ :=
    (smoothFrame_contMDiff (I := I) (M := M) (E := E)
      (x₀ := x₀) (b := b) k) x₀ |>.of_le (by norm_num)
  simpa [smoothConnectionSection] using hcov_at.clm_bundle_apply hframe_at

lemma connectionCoefficient_contMDiffAt
    (i j k : Fin (Module.finrank ℝ E)) :
    ContMDiffAt I 𝓘(ℝ) 1
      (connectionCoefficient cov x₀ b i j k) x₀ := by
  let τ := smoothConnectionSection cov x₀ b j k
  have hτ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun y ↦ TotalSpace.mk' E y (τ y)) x₀ := by
    simpa [τ] using
      smoothConnectionSection_contMDiffAt (cov := cov) (x₀ := x₀) (b := b) i j k
  have hcoeff : ContMDiffAt I 𝓘(ℝ) 1
      (fun y ↦ (trivializationAt E TM x₀).localFrameCoeff I b i y (τ y)) x₀ := by
    exact contMDiffAt_localFrameCoeff (I := I)
      (e := trivializationAt E TM x₀) (b := b)
      (x := x₀) (s := τ) (i := i)
      (mem_baseSet_trivializationAt E TM x₀) hτ
  change ContMDiffAt I 𝓘(ℝ) 1
    (fun y ↦ (trivializationAt E (TangentSpace I : M → Type _) x₀).localFrameCoeff I b i y
      (cov (smoothFrame (x₀ := x₀) (b := b) j) y
        (smoothFrame (x₀ := x₀) (b := b) k y))) x₀
  exact hcoeff

/-! The coefficient germ is regular at every point of the chosen
trivialization, not only at its centre.  This is the local fact needed when a
geodesic is continued through overlapping coordinate neighborhoods. -/

lemma connectionCoefficient_contMDiffAt_of_mem_baseSet
    (i j k : Fin (Module.finrank ℝ E)) {y : M}
    (hy : y ∈ (trivializationAt E TM x₀).baseSet) :
    ContMDiffAt I 𝓘(ℝ) 1
      (connectionCoefficient cov x₀ b i j k) y := by
  let hcov :=
    (inferInstance : CovariantDerivative.ContMDiffCovariantDerivative cov 1).contMDiff
  have hcov' : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun z ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun z : M ↦ TangentSpace I z →L[ℝ] TangentSpace I z)
        z (cov (smoothFrame (x₀ := x₀) (b := b) j) z)) := by
    have hframe_global : ContMDiff I (I.prod 𝓘(ℝ, E)) 2
        (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) z
          (smoothFrame (x₀ := x₀) (b := b) j z)) :=
      smoothFrame_contMDiff (I := I) (M := M) (E := E)
        (x₀ := x₀) (b := b) j
    have hframe_on : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) z
          (smoothFrame (x₀ := x₀) (b := b) j z)) (Set.univ : Set M) := by
      simpa only [contMDiffOn_univ] using hframe_global
    simpa [contMDiffOn_univ, smoothFrame] using
      hcov.contMDiff
        (hframe_on.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ (2 : WithTop ℕ∞)))
  have hcov_at := hcov' y
  have hframe_at : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E (E := TangentSpace I) z
        (smoothFrame (x₀ := x₀) (b := b) k z)) y :=
    (smoothFrame_contMDiff (I := I) (M := M) (E := E)
      (x₀ := x₀) (b := b) k) y |>.of_le (by norm_num)
  have hτ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun z ↦ TotalSpace.mk' E z
        (cov (smoothFrame (x₀ := x₀) (b := b) j) z
          (smoothFrame (x₀ := x₀) (b := b) k z))) y := by
    simpa [smoothFrame] using hcov_at.clm_bundle_apply hframe_at
  have hcoeff : ContMDiffAt I 𝓘(ℝ) 1
      (fun z ↦ (trivializationAt E TM x₀).localFrameCoeff I b i z
        (cov (smoothFrame (x₀ := x₀) (b := b) j) z
          (smoothFrame (x₀ := x₀) (b := b) k z))) y := by
    exact contMDiffAt_localFrameCoeff (I := I)
      (e := trivializationAt E TM x₀) (b := b)
      (x := y) (s := fun z ↦
        cov (smoothFrame (x₀ := x₀) (b := b) j) z
          (smoothFrame (x₀ := x₀) (b := b) k z)) (i := i) hy hτ
  exact hcoeff

lemma connectionCoefficient_comp_extChartAt_symm_contDiffAt
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffAt ℝ 1
      (fun z : E ↦ connectionCoefficient cov x₀ b i j k
        ((extChartAt I x₀).symm z))
      (extChartAt I x₀ x₀) := by
  have hcoef := connectionCoefficient_contMDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) i j k
  have hsymm :
      ContMDiffWithinAt 𝓘(ℝ, E) I 1 (extChartAt I x₀).symm
        (extChartAt I x₀).target (extChartAt I x₀ x₀) :=
    contMDiffWithinAt_extChartAt_symm_target
      (I := I) (n := (1 : WithTop ℕ∞)) (x := x₀) (y := extChartAt I x₀ x₀)
        (by exact mem_extChartAt_target (I := I) x₀)
  have hcoef0 :
      ContMDiffAt I 𝓘(ℝ) 1 (connectionCoefficient cov x₀ b i j k)
        ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) := by
    convert hcoef using 1
    exact (extChartAt I x₀).left_inv
      (mem_extChartAt_source (I := I) x₀)
  have hcoef_univ :
      ContMDiffWithinAt I 𝓘(ℝ) 1 (connectionCoefficient cov x₀ b i j k)
        (Set.univ : Set M) ((extChartAt I x₀).symm (extChartAt I x₀ x₀)) :=
    hcoef0.contMDiffWithinAt
  have hcomp :
      ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1
        (connectionCoefficient cov x₀ b i j k ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀).target (extChartAt I x₀ x₀) := by
    exact hcoef_univ.comp (extChartAt I x₀ x₀)
      hsymm (by intro z hz; simp)
  apply hcomp.contDiffWithinAt.contDiffAt
  exact extChartAt_target_mem_nhds' (I := I) (x := x₀)
    (y := extChartAt I x₀ x₀) (mem_extChartAt_target (I := I) x₀)

lemma connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
    (i j k : Fin (Module.finrank ℝ E)) {z : E}
    (hz : z ∈ (extChartAt I x₀).target) :
    ContDiffAt ℝ 1
      (fun z : E ↦ connectionCoefficient cov x₀ b i j k
        ((extChartAt I x₀).symm z)) z := by
  have hy : (extChartAt I x₀).symm z ∈
      (trivializationAt E TM x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet (I := I) (E := E) x₀,
      ← extChartAt_source I x₀]
    exact (extChartAt I x₀).map_target hz
  have hcoef := connectionCoefficient_contMDiffAt_of_mem_baseSet
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    i j k hy
  have hsymmWithin : ContMDiffWithinAt 𝓘(ℝ, E) I 1
      (extChartAt I x₀).symm (extChartAt I x₀).target z :=
    contMDiffWithinAt_extChartAt_symm_target
      (I := I) (n := (1 : WithTop ℕ∞)) (x := x₀) (y := z) hz
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1
      (extChartAt I x₀).symm z :=
    hsymmWithin.contMDiffAt (extChartAt_target_mem_nhds' (I := I) hz)
  have hcomp : ContDiffAt ℝ 1
      (connectionCoefficient cov x₀ b i j k ∘ (extChartAt I x₀).symm) z := by
    exact (hcoef.comp z hsymm).contDiffAt
  simpa [Function.comp_def] using hcomp

def coordinateAcceleration
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u : E) : E :=
  -∑ i, (∑ j, ∑ k,
    (b.repr u j) * (b.repr u k) *
      connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm z)) • b i

/-- The coordinate geodesic acceleration is even in velocity.  This is the
algebraic time-reversal symmetry of the geodesic equation. -/
@[simp] lemma coordinateAcceleration_neg
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u : E) :
    coordinateAcceleration cov x₀ b z (-u) = coordinateAcceleration cov x₀ b z u := by
  simp [coordinateAcceleration]

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M]
  [RiemannianBundle (TangentSpace I : M → Type _)] in
/-- The coordinate geodesic acceleration is homogeneous of degree two in
velocity.  Together with time reversal this is the exact algebraic input for
reparameterizing local geodesics. -/
lemma coordinateAcceleration_smul
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (a : ℝ) (z u : E) :
    coordinateAcceleration cov x₀ b z (a • u) =
      a ^ 2 • coordinateAcceleration cov x₀ b z u := by
  simp only [coordinateAcceleration, map_smul]
  rw [smul_neg, Finset.smul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finsupp.smul_apply, smul_eq_mul]
  ring

/-- Reverse a chart-level second-order solution for a velocity-even system.
The new curve is `t ↦ z(-t)` and its velocity is `t ↦ -u(-t)`. -/
noncomputable def LocalChartSecondOrderSolution.reverse
    {F : E → E → E} {x : M} {u : E}
    (heven : ∀ z v, F z (-v) = F z v)
    (sol : LocalChartSecondOrderSolution I F x u) :
    LocalChartSecondOrderSolution I F x (-u) where
  coordinate := fun t ↦ sol.coordinate (-t)
  velocity := fun t ↦ -sol.velocity (-t)
  radius := sol.radius
  radius_pos := sol.radius_pos
  coordinate_initial := by simpa using sol.coordinate_initial
  velocity_initial := by simpa using sol.velocity_initial
  coordinate_hasDeriv := by
    intro t ht
    have ht' : -t ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [ht.1, ht.2]
    change HasDerivAt (sol.coordinate ∘ Neg.neg) (-sol.velocity (-t)) t
    simpa only [neg_one_smul] using
      HasDerivAt.scomp t (sol.coordinate_hasDeriv (-t) ht') (hasDerivAt_neg t)
  velocity_hasDeriv := by
    intro t ht
    have ht' : -t ∈ Ioo (-sol.radius) sol.radius := by
      constructor <;> linarith [ht.1, ht.2]
    change HasDerivAt (-sol.velocity ∘ Neg.neg)
      (F (sol.coordinate (-t)) (-sol.velocity (-t))) t
    rw [heven]
    simpa only [neg_one_smul, neg_neg] using
      (HasDerivAt.scomp t (sol.velocity_hasDeriv (-t) ht') (hasDerivAt_neg t)).neg
  coordinate_mem_target := by
    intro t ht
    apply sol.coordinate_mem_target (-t)
    constructor <;> linarith [ht.1, ht.2]

/-- Positively rescale time in a chart-level geodesic.  If `sol` starts with
velocity `u`, the new solution follows the same trace at speed factor `a` and
starts with `a • u`.  Its radius is scaled by `a⁻¹`; the proof uses the true
quadratic Christoffel acceleration, rather than an unproved spray axiom. -/
noncomputable def LocalChartSecondOrderSolution.rescale
    {u₀ : E} (sol : LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀)
    (a : ℝ) (ha : 0 < a) :
    LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ (a • u₀) where
  coordinate := fun t ↦ sol.coordinate (a * t)
  velocity := fun t ↦ a • sol.velocity (a * t)
  radius := sol.radius / a
  radius_pos := div_pos sol.radius_pos ha
  coordinate_initial := by simpa using sol.coordinate_initial
  velocity_initial := by
    simpa using congrArg (fun w : E ↦ a • w) sol.velocity_initial
  coordinate_hasDeriv := by
    intro t ht
    have hat : a * t ∈ Ioo (-sol.radius) sol.radius := by
      constructor
      · have hleft : (-sol.radius) / a < t := by
          simpa [neg_div] using ht.1
        have h := (div_lt_iff₀ ha).mp hleft
        simpa [mul_comm] using h
      · have h := (lt_div_iff₀ ha).mp ht.2
        simpa [mul_comm] using h
    have hscale : HasDerivAt (fun s : ℝ ↦ a * s) a t :=
      hasDerivAt_const_mul a
    change HasDerivAt (sol.coordinate ∘ fun s : ℝ ↦ a * s)
      (a • sol.velocity (a * t)) t
    simpa [Function.comp_def] using
      HasDerivAt.scomp t (sol.coordinate_hasDeriv (a * t) hat) hscale
  velocity_hasDeriv := by
    intro t ht
    have hat : a * t ∈ Ioo (-sol.radius) sol.radius := by
      constructor
      · have hleft : (-sol.radius) / a < t := by
          simpa [neg_div] using ht.1
        have h := (div_lt_iff₀ ha).mp hleft
        simpa [mul_comm] using h
      · have h := (lt_div_iff₀ ha).mp ht.2
        simpa [mul_comm] using h
    have hscale : HasDerivAt (fun s : ℝ ↦ a * s) a t :=
      hasDerivAt_const_mul a
    rw [coordinateAcceleration_smul]
    change HasDerivAt (a • (sol.velocity ∘ fun s : ℝ ↦ a * s))
      (a ^ 2 • coordinateAcceleration cov x₀ b
        (sol.coordinate (a * t)) (sol.velocity (a * t))) t
    simpa [smul_smul, pow_two] using
      (HasDerivAt.scomp t (sol.velocity_hasDeriv (a * t) hat) hscale).const_smul a
  coordinate_mem_target := by
    intro t ht
    have hat : a * t ∈ Ioo (-sol.radius) sol.radius := by
      constructor
      · have hleft : (-sol.radius) / a < t := by
          simpa [neg_div] using ht.1
        have h := (div_lt_iff₀ ha).mp hleft
        simpa [mul_comm] using h
      · have h := (lt_div_iff₀ ha).mp ht.2
        simpa [mul_comm] using h
    exact sol.coordinate_mem_target (a * t) hat

/-- The connection contribution in the coordinate frame.  It is kept separate
from `coordinateAcceleration` so that the geodesic equation is visible as
`u' + Γ(z,u,u) = 0`, rather than being hidden in the right-hand side of the
ODE. -/
def coordinateConnectionTerm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u : E) : E :=
  ∑ i, (∑ j, ∑ k,
    (b.repr u j) * (b.repr u k) *
      connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm z)) • b i

/-- The coordinate covariant acceleration associated with the actual
connection coefficient germ. -/
def coordinateCovariantAcceleration
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u a : E) : E :=
  a + coordinateConnectionTerm cov x₀ b z u

@[simp] lemma coordinateAcceleration_eq_neg_connectionTerm
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (x₀ : M) (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E)
    (z u : E) :
    coordinateAcceleration cov x₀ b z u = -coordinateConnectionTerm cov x₀ b z u := by
  rfl

lemma local_solution_coordinateCovariantAcceleration_eq_zero
    {F : E → E → E} {x₀ : M} {v₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ v₀)
    {t : ℝ} (ht : t ∈ Ioo (-sol.radius) sol.radius) :
    coordinateCovariantAcceleration cov x₀ b (sol.coordinate t) (sol.velocity t)
      (deriv sol.velocity t) = 0 := by
  have hderiv : deriv sol.velocity t =
      coordinateAcceleration cov x₀ b (sol.coordinate t) (sol.velocity t) :=
    (sol.velocity_hasDeriv t ht).deriv
  rw [hderiv, coordinateCovariantAcceleration]
  simp [coordinateAcceleration, coordinateConnectionTerm]

lemma coordinateAcceleration_contDiffAt
    (u₀ : E) :
    ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateAcceleration cov x₀ b q.1 q.2)
      (extChartAt I x₀ x₀, u₀) := by
  let p : E × E := (extChartAt I x₀ x₀, u₀)
  have hterm : ∀ (i j k : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 1
        (fun q : E × E ↦
          ((b.repr q.2 j) * (b.repr q.2 k) *
            connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) • b i) p := by
    intro i j k
    have hj : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 j) p := by
      exact (b.coord j).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hk : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 k) p := by
      exact (b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hc := connectionCoefficient_comp_extChartAt_symm_contDiffAt
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) i j k
    have hc' : ContDiffAt ℝ 1
        (fun q : E × E ↦ connectionCoefficient cov x₀ b i j k
          ((extChartAt I x₀).symm q.1)) p := by
      exact hc.comp p contDiffAt_fst
    have hp : ContDiffAt ℝ 1
        (fun q : E × E ↦ (b.repr q.2 j) * (b.repr q.2 k) *
          connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) p :=
      (hj.mul hk).mul hc'
    exact hp.smul_const (b i)
  have hinner : ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 1
        (fun q : E × E ↦ ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) *
            connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) p := by
    intro i j
    apply ContDiffAt.sum
    intro k hk
    have hj : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 j) p := by
      exact (b.coord j).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hk' : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 k) p := by
      exact (b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hc := connectionCoefficient_comp_extChartAt_symm_contDiffAt
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) i j k
    have hc' : ContDiffAt ℝ 1
        (fun q : E × E ↦ connectionCoefficient cov x₀ b i j k
          ((extChartAt I x₀).symm q.1)) p := hc.comp p contDiffAt_fst
    exact (hj.mul hk').mul hc'
  have hrow : ∀ (i : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ 1
        (fun q : E × E ↦ (∑ j, ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) *
            connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) • b i) p := by
    intro i
    have hs : ContDiffAt ℝ 1
        (fun q : E × E ↦ ∑ j, ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) *
            connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) p := by
      apply ContDiffAt.sum
      intro j hj
      exact hinner i j
    exact hs.smul_const (b i)
  have hout : ContDiffAt ℝ 1
      (fun q : E × E ↦ ∑ i, (∑ j, ∑ k,
        (b.repr q.2 j) * (b.repr q.2 k) *
          connectionCoefficient cov x₀ b i j k ((extChartAt I x₀).symm q.1)) • b i) p := by
    apply ContDiffAt.sum
    intro i hi
    exact hrow i
  simpa only [coordinateAcceleration] using hout.neg

private lemma quadraticAcceleration_contDiffAt_of_coeff
    {n : ℕ} (b : Module.Basis (Fin n) ℝ E)
    (Γ : Fin n → Fin n → Fin n → E → ℝ)
    {z₀ : E} (hΓ : ∀ i j k, ContDiffAt ℝ 1 (Γ i j k) z₀)
    (u₀ : E) :
    ContDiffAt ℝ 1
      (fun q : E × E ↦ -∑ i, (∑ j, ∑ k,
        (b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) • b i)
      (z₀, u₀) := by
  let p : E × E := (z₀, u₀)
  have hterm : ∀ (i j k : Fin n),
      ContDiffAt ℝ 1
        (fun q : E × E ↦
          ((b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) • b i) p := by
    intro i j k
    have hj : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 j) p := by
      exact (b.coord j).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hk : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 k) p := by
      exact (b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hΓ' : ContDiffAt ℝ 1
        (fun q : E × E ↦ Γ i j k q.1) p := by
      exact (hΓ i j k).comp p contDiffAt_fst
    exact ((hj.mul hk).mul hΓ').smul_const (b i)
  have hinner : ∀ (i j : Fin n),
      ContDiffAt ℝ 1
        (fun q : E × E ↦ ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) p := by
    intro i j
    apply ContDiffAt.sum
    intro k hk
    have hj : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 j) p := by
      exact (b.coord j).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hk' : ContDiffAt ℝ 1 (fun q : E × E ↦ b.repr q.2 k) p := by
      exact (b.coord k).toContinuousLinearMap.contDiff.contDiffAt.comp p contDiffAt_snd
    have hΓ' : ContDiffAt ℝ 1
        (fun q : E × E ↦ Γ i j k q.1) p := by
      exact (hΓ i j k).comp p contDiffAt_fst
    exact (hj.mul hk').mul hΓ'
  have hrow : ∀ (i : Fin n),
      ContDiffAt ℝ 1
        (fun q : E × E ↦ (∑ j, ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) • b i) p := by
    intro i
    have hs : ContDiffAt ℝ 1
        (fun q : E × E ↦ ∑ j, ∑ k,
          (b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) p := by
      apply ContDiffAt.sum
      intro j hj
      exact hinner i j
    exact hs.smul_const (b i)
  have hout : ContDiffAt ℝ 1
      (fun q : E × E ↦ ∑ i, (∑ j, ∑ k,
        (b.repr q.2 j) * (b.repr q.2 k) * Γ i j k q.1) • b i) p := by
    apply ContDiffAt.sum
    intro i hi
    exact hrow i
  simpa [p] using hout.neg

lemma coordinateAcceleration_contDiffAt_of_mem_target
    {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x₀).target) (u₀ : E) :
    ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateAcceleration cov x₀ b q.1 q.2)
      (z₀, u₀) := by
  refine quadraticAcceleration_contDiffAt_of_coeff (I := I) (M := M) (H := H)
    (E := E)
    (n := Module.finrank ℝ E) b
    (fun i j k z ↦ connectionCoefficient cov x₀ b i j k
      ((extChartAt I x₀).symm z)) ?_ u₀
  intro i j k
  exact connectionCoefficient_comp_extChartAt_symm_contDiffAt_of_mem_target
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    i j k hz₀

/-- On a compact coordinate state set whose position component stays in the
extended-chart target, the genuine coordinate geodesic acceleration has a
single finite norm bound.  This is the compactness input for endpoint
continuation; it bounds the actual Christoffel expression rather than an
auxiliary extension. -/
theorem exists_pos_norm_le_coordinateAcceleration_on_isCompact
    (K : Set (E × E)) (hK : IsCompact K)
    (hKtarget : ∀ q ∈ K, q.1 ∈ (extChartAt I x₀).target) :
    ∃ C > (0 : ℝ), ∀ q ∈ K,
      ‖coordinateAcceleration cov x₀ b q.1 q.2‖ ≤ C := by
  have hcont : ContinuousOn
      (fun q : E × E ↦ coordinateAcceleration cov x₀ b q.1 q.2) K := by
    intro q hq
    exact (coordinateAcceleration_contDiffAt_of_mem_target
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
      (hKtarget q hq) q.2).continuousAt.continuousWithinAt
  obtain ⟨C, hC, hbound⟩ :=
    (hK.image_of_continuousOn hcont).isBounded.exists_pos_norm_le
  refine ⟨C, hC, ?_⟩
  intro q hq
  exact hbound _ ⟨q, hq, rfl⟩

/-- Product form of compact acceleration control, convenient when a base
coordinate compact set and a velocity compact set are obtained separately. -/
theorem exists_pos_norm_le_coordinateAcceleration_on_isCompact_prod
    (K V : Set E) (hK : IsCompact K) (hV : IsCompact V)
    (hKtarget : ∀ z ∈ K, z ∈ (extChartAt I x₀).target) :
    ∃ C > (0 : ℝ), ∀ z ∈ K, ∀ u ∈ V,
      ‖coordinateAcceleration cov x₀ b z u‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_norm_le_coordinateAcceleration_on_isCompact
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
      (K ×ˢ V) (hK.prod hV) (by
        intro q hq
        exact hKtarget q.1 hq.1)
  refine ⟨C, hC, ?_⟩
  intro z hz u hu
  exact hbound (z, u) ⟨hz, hu⟩

lemma coordinateAcceleration_system_contDiffAt_of_mem_target
    {z₀ : E} (hz₀ : z₀ ∈ (extChartAt I x₀).target) (u₀ : E) :
    ContDiffAt ℝ 1
      (fun q : E × E ↦
        secondOrderSystem (coordinateAcceleration cov x₀ b) q)
      (z₀, u₀) := by
  have ha : ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateAcceleration cov x₀ b q.1 q.2)
      (z₀, u₀) := coordinateAcceleration_contDiffAt_of_mem_target
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) hz₀ u₀
  simpa [secondOrderSystem] using contDiffAt_snd.prodMk ha


lemma coordinateAcceleration_system_contDiffAt
    (u₀ : E) :
    ContDiffAt ℝ 1
      (fun q : E × E ↦
        secondOrderSystem (coordinateAcceleration cov x₀ b) q)
      (extChartAt I x₀ x₀, u₀) := by
  have ha : ContDiffAt ℝ 1
      (fun q : E × E ↦ coordinateAcceleration cov x₀ b q.1 q.2)
      (extChartAt I x₀ x₀, u₀) :=
    coordinateAcceleration_contDiffAt (I := I) (M := M) (E := E)
      (cov := cov) (x₀ := x₀) (b := b) u₀
  simpa [secondOrderSystem] using contDiffAt_snd.prodMk ha

theorem exists_local_geodesic_solution (u₀ : E) :
    Nonempty (BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀) :=
  BonnetMyersEntry.exists_localChartSecondOrderSolution_of_contDiffAt
    (I := I) (M := M) (E := E) (F := coordinateAcceleration cov x₀ b)
    (x₀ := x₀) (v₀ := u₀)
    (coordinateAcceleration_system_contDiffAt
      (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀)

/-! ### Initial tangent data

The ODE is solved in the extended chart.  The tangent-bundle trivialization
converts an actual tangent vector at `x₀` into the corresponding chart
velocity, and the inverse-chart derivative converts it back.  The explicit
`fromTangentSpace` occurrence below is intentional: the model-space tangent
fiber is only definitionally equal to `E` through an opaque type synonym. -/

def coordinateVelocity (v : TangentSpace I x₀) : E :=
  (trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearMapAt ℝ x₀ v

lemma coordinateVelocity_inverse_derivative (v : TangentSpace I x₀) :
    (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (extChartAt I x₀ x₀))
        (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) = v := by
  have hx : x₀ ∈ (chartAt H x₀).source := mem_chart_source H x₀
  have hsymm := TangentBundle.symmL_trivializationAt
    (I := I) (𝕜 := ℝ) (x₀ := x₀) (x := x₀) hx
  rw [← hsymm]
  rw [coordinateVelocity]
  exact (trivializationAt E (TangentSpace I : M → Type _) x₀).symmL_continuousLinearMapAt
    (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀) v

lemma coordinateVelocity_inverse_derivative_explicit (v : TangentSpace I x₀) :
    (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (extChartAt I x₀ x₀))
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
          (extChartAt I x₀ x₀)).symm
          (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)) = v := by
  change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (extChartAt I x₀ x₀))
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) = v
  exact coordinateVelocity_inverse_derivative (I := I) (M := M) (E := E)
    (x₀ := x₀) v

lemma exists_local_geodesic_solution_for_velocity (v : TangentSpace I x₀) :
    Nonempty (BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)) := by
  exact exists_local_geodesic_solution
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b)
    (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)

/-! ### The local geodesic predicate

The coordinate ODE is now recorded as a geometric local geodesic statement.
The predicate is deliberately phrased using the covariant acceleration built
from the actual connection coefficient germ above.  Thus the existence result
below is stronger than an unlabelled ODE existence claim, while remaining
local until the global spray and continuation argument is supplied.
-/

def IsCoordinateGeodesic
    {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀) : Prop :=
  ∀ {t : ℝ}, t ∈ Ioo (-sol.radius) sol.radius →
    coordinateCovariantAcceleration cov x₀ b (sol.coordinate t) (sol.velocity t)
      (deriv sol.velocity t) = 0

theorem local_solution_isCoordinateGeodesic
    {u₀ : E}
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀) :
    IsCoordinateGeodesic (cov := cov) (x₀ := x₀) (b := b) sol := by
  intro t ht
  exact local_solution_coordinateCovariantAcceleration_eq_zero
    (F := coordinateAcceleration cov x₀ b)
    (cov := cov) (x₀ := x₀) (b := b) sol ht

theorem exists_local_coordinateGeodesic (u₀ : E) :
    Nonempty {sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
        (coordinateAcceleration cov x₀ b) x₀ u₀ //
      IsCoordinateGeodesic (cov := cov) (x₀ := x₀) (b := b) sol} := by
  obtain ⟨sol⟩ := exists_local_geodesic_solution
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀
  exact ⟨⟨sol, local_solution_isCoordinateGeodesic
    (cov := cov) (x₀ := x₀) (b := b) sol⟩⟩

theorem exists_local_coordinateGeodesic_for_velocity (v : TangentSpace I x₀) :
    Nonempty {sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
        (coordinateAcceleration cov x₀ b) x₀
          (coordinateVelocity (I := I) (M := M) (E := E) x₀ v) //
      IsCoordinateGeodesic (cov := cov) (x₀ := x₀) (b := b) sol} := by
  obtain ⟨sol⟩ := exists_local_geodesic_solution_for_velocity
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) v
  exact ⟨⟨sol, local_solution_isCoordinateGeodesic
    (cov := cov) (x₀ := x₀) (b := b) sol⟩⟩

theorem coordinateGeodesic_eventuallyEq_of_same_initial
    {u₀ : E}
    (sol₁ sol₂ : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀ u₀) :
    (fun t ↦ (sol₁.coordinate t, sol₁.velocity t)) =ᶠ[𝓝 (0 : ℝ)]
      (fun t ↦ (sol₂.coordinate t, sol₂.velocity t)) := by
  apply BonnetMyersEntry.LocalChartSecondOrderSolution.eventuallyEq_of_same_initial
    (F := coordinateAcceleration cov x₀ b) sol₁ sol₂
  exact coordinateAcceleration_system_contDiffAt
    (I := I) (M := M) (E := E) (cov := cov) (x₀ := x₀) (b := b) u₀

lemma curve_initial_hasMFDerivAt
    (v : TangentSpace I x₀)
    (sol : BonnetMyersEntry.LocalChartSecondOrderSolution I
      (coordinateAcceleration cov x₀ b) x₀
      (coordinateVelocity (I := I) (M := M) (E := E) x₀ v)) :
    HasMFDerivAt (𝓘(ℝ, ℝ)) I
      (BonnetMyersEntry.LocalChartSecondOrderSolution.curve sol) 0
      (ContinuousLinearMap.toSpanSingleton ℝ v) := by
  have hzero : (0 : ℝ) ∈ Ioo (-sol.radius) sol.radius := by
    constructor <;> linarith [sol.radius_pos]
  have h := BonnetMyersEntry.LocalChartSecondOrderSolution.curve_hasMFDerivAt sol hzero
  have hmap :
      (mfderiv[range (I : H → E)] (extChartAt I x₀).symm (sol.coordinate 0)) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (sol.velocity 0) =
        ContinuousLinearMap.toSpanSingleton ℝ v := by
    rw [sol.coordinate_initial, sol.velocity_initial]
    apply ContinuousLinearMap.ext
    intro t
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply]
    change (mfderiv[range (I : H → E)] (extChartAt I x₀).symm
      (extChartAt I x₀ x₀))
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (E := E)
        (extChartAt I x₀ x₀)).symm (t • coordinateVelocity x₀ v)) =
      t • v
    rw [map_smul, map_smul]
    rw [coordinateVelocity_inverse_derivative_explicit (I := I) (M := M) (E := E)
      (x₀ := x₀) v]
    rfl
  exact h.congr_mfderiv hmap

end LocalGeodesicData

end BonnetMyersEntry
