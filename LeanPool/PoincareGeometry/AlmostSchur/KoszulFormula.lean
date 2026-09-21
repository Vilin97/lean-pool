/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.LeviCivitaConnection

/-! # Koszul formula and the precise uniqueness of Levi–Civita derivatives

Connection objects can have arbitrary values on nondifferentiable sections.
Uniqueness is therefore proved on differentiable sections, which is exactly
the scope of the connection laws and subsequent geometric calculations.
-/

@[expose] public noncomputable section
open Bundle FiberBundle VectorField
open scoped Manifold ContDiff
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Koszul's identity derived from actual metric compatibility and torsion. -/
theorem koszul_formula (cov : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X Y Z : Π x, TM x) (x : M)
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiffAt (T% Z) x) :
    2 * inner ℝ (cov Y x (X x)) (Z x) =
      mvfderiv I (fun y ↦ inner ℝ (Y y) (Z y)) x (X x) +
      mvfderiv I (fun y ↦ inner ℝ (X y) (Z y)) x (Y x) -
      mvfderiv I (fun y ↦ inner ℝ (X y) (Y y)) x (Z x) -
      inner ℝ (X x) (mlieBracket I Y Z x) +
      inner ℝ (Y x) (mlieBracket I Z X x) +
      inner ℝ (Z x) (mlieBracket I X Y x) := by
  have hbr (U V : Π y, TM y) (hU : MDiffAt (T% U) x) (hV : MDiffAt (T% V) x) :
      mlieBracket I U V x = cov V x (U x) - cov U x (V x) := by
    have h := cov.torsion_apply hU hV
    rw [congrFun ht x] at h
    change 0 = cov V x (U x) - cov U x (V x) - mlieBracket I U V x at h
    exact (sub_eq_zero.mp h.symm).symm
  rw [CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm X hY hZ,
    CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm Y hX hZ,
    CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm Z hX hY,
    hbr Y Z hY hZ, hbr Z X hZ hX, hbr X Y hX hY]
  simp only [inner_sub_right, real_inner_comm]
  ring

/-- Two metric-compatible torsion-free connections agree when applied to
fields differentiable at the evaluation point. -/
theorem metric_torsion_connections_agree (cov cov' : CovariantDerivative I E TM)
    (hm : tangentMetricCompatible cov) (hm' : tangentMetricCompatible cov')
    (ht : cov.torsion = 0) (ht' : cov'.torsion = 0)
    {Y : Π y, TM y} {x : M} (hY : MDiffAt (T% Y) x) : cov Y x = cov' Y x := by
  ext u
  apply ext_inner_right ℝ
  intro w
  let X := FiberBundle.extend E u
  let Z := FiberBundle.extend E w
  have hX : MDiffAt (T% X) x := mdifferentiableAt_extend ..
  have hZ : MDiffAt (T% Z) x := mdifferentiableAt_extend ..
  have h := koszul_formula cov hm ht X Y Z x hX hY hZ
  have h' := koszul_formula cov' hm' ht' X Y Z x hX hY hZ
  have hXu : X x = u := by simp [X]
  have hZw : Z x = w := by simp [Z]
  rw [hXu, hZw] at h h'
  linarith

/-- Every metric-compatible torsion-free derivative agrees with the constructed
connection on differentiable sections; no equality of junk values is claimed. -/
theorem eq_leviCivitaConnection_on_differentiable
    (cov : CovariantDerivative I E TM) (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {Y : Π y, TM y} {x : M} (hY : MDiffAt (T% Y) x) :
    cov Y x = leviCivitaConnection (I := I) Y x :=
  metric_torsion_connections_agree cov leviCivitaConnection hm
    leviCivitaConnection_metricCompatible ht leviCivitaConnection_torsion hY

end AlmostSchur
