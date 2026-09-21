/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.RicciTraceDerivative
public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaBianchiCore

/-! # Comparing actual tensor differentiation with the attributed Bianchi core

Local C³ representatives suffice. The first covariant derivative is compared
by germ locality; all three differentiated curvature slots are then evaluated
using the proved local raw-to-tensor theorem.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- The corrected derivative of actual bundled curvature equals the raw
corrected expression used in the Bianchi core, on locally C³ fields. -/
theorem curvatureDirectionalDerivative_eq_secondBianchiAux
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X U Y Z : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% U) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    curvatureDirectionalDerivative cov X U Y Z x = cov.secondBianchiAuxAlmostSchur X U Y Z x := by
  have hR := contMDiffAt_curvatureTensor_apply_one cov hm ht hU hY hZ
  have hraw := contMDiffAt_curvatureAux_one cov hm ht hU hY hZ
  have he : (fun y ↦ cov.curvatureTensorAlmostSchur y (U y) (Y y) (Z y)) =ᶠ[𝓝 x]
      cov.curvatureAuxAlmostSchur U Y Z := by
    filter_upwards [(contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hU,
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hY,
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp hZ] with y hUy hYy hZy
    exact (curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
      (hUy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
      (hYy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
      (hZy.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))).symm
  have hc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    (hR.mdifferentiableAt (by norm_num)) (hraw.mdifferentiableAt (by norm_num)) (by simp) he
  have hDU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.alongAlmostSchur X U)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht hX hU
  have hDY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.alongAlmostSchur X Y)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht hX hY
  have hDZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 2 (T% (cov.alongAlmostSchur X Z)) x :=
    contMDiffAt_covariantAlong_of_metric_torsion_two cov hm ht hX hZ
  have h1 := curvatureAux_eq_curvatureTensor_of_contMDiffAt cov hDU
    (hY.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) (hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
  have h2 := curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
    (hU.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) hDY (hZ.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3))
  have h3 := curvatureAux_eq_curvatureTensor_of_contMDiffAt cov
    (hU.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) (hY.of_le (by norm_num : (2 : ℕ∞ω) ≤ 3)) hDZ
  simp only [curvatureDirectionalDerivative, CovariantDerivative.secondBianchiAuxAlmostSchur, Pi.sub_apply,
    hc, h1, h2, h3, CovariantDerivative.along_applyAlmostSchur]

/-- Actual corrected Ricci differentiation contracts the raw Bianchi expression;
the scalar derivative and all slot corrections are already identified. -/
theorem ricciDirectionalDerivative_eq_secondBianchiAux_contraction
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X Y Z : Π y, TM y) (x : M)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ E) (hx : x ∈ e.baseSet) :
    ricciDirectionalDerivative cov X Y Z x =
      ∑ i, e.localFrameCoeff I b i x
        (cov.secondBianchiAuxAlmostSchur X (e.localFrame b i) Y Z x) := by
  rw [ricciDirectionalDerivative_eq_contraction cov hm ht X Y Z x hY hZ e b hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [curvatureDirectionalDerivative_eq_secondBianchiAux cov hm ht hX
    (contMDiffAt_localFrame_of_mem 3 e b i hx) hY hZ]

end AlmostSchur
