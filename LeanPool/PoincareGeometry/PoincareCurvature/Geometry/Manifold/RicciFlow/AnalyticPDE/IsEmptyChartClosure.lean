/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothRealization

/-!
# IsEmpty-manifold Ricci-DeTurck Banach chart, closure data, and point-4 assembly

This leaf module constructs the **first genuine inhabitants** of the two named structures on the
Ricci-DeTurck chart-closure critical path — the time-dependent geometric Banach chart
(`TimeDependentGeometricRicciDeTurckBanachChart`) and its closure data
(`RicciDeTurckChartClosureData`) — on the empty-manifold sub-class, and feeds them through the
already-proved bridge `intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData` to a
genuine `IntrinsicLocalExistenceUniquenessFamily` witness.

On `[IsEmpty M]` the continuous-section space is trivial, so the honest Banach representative of the
Ricci-DeTurck operator can be taken to be the **constant field** at the initial section; every
Picard-Lindelöf estimate is then either an equality (`‖·‖ ≤ ‖·‖₊`) or a constant-map bound, and the
geometric identification, realization, and encoding obligations are all vacuous over the empty base.
This exercises the whole chart → closure-data → bridge assembly end to end (the general
positive-dimensional case additionally requires the parabolic Schauder a-priori bound that supplies a
genuinely Lipschitz Banach representative).
-/

@[expose] public noncomputable section

open Set
open scoped Bundle Manifold ContDiff NNReal Topology

namespace RicciFlow
namespace AnalyticPDE
namespace MetricLocusEvolution

open PoincareCurvature.Bundle.Trivialization
open PoincareCurvature.Bundle.Trivialization.ContinuousSectionSpace
section IsEmptyChart

variable {M : Type*} [TopologicalSpace M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H}
variable [ChartedSpace H M] [SigmaCompactSpace M] [IsManifold I ∞ M]
variable [ContMDiffVectorBundle 2 F (TangentSpace I : M → Type _) I]
variable [IsManifold I (minSmoothness ℝ 3) M]
variable [IsManifold I ((2 : ℕ∞) + 1) M]
variable [CompleteSpace F]
variable {κ : Type*} [Finite κ] [T2Space M]
variable [FiniteDimensional ℝ F] [Nontrivial F]
variable [IsEmpty M]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "TM" => (TangentSpace I : M → Type _)

/-- The initial continuous section carried by a continuous Riemannian metric, viewed in the
finite-cover bundled section space.  This is exactly the Picard-Lindelöf center used by the chart. -/
def isEmptyInitialSection
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM) :
    ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover :=
  ⟨g₀.toSection, g₀.continuous_toSection⟩

/-- The first genuine inhabitant of `TimeDependentGeometricRicciDeTurckBanachChart`: on an empty
manifold the honest Banach representative of the Ricci-DeTurck operator is the constant field at the
initial section, all Picard-Lindelöf constants are supplied concretely, and the geometric
identification is vacuous over the empty base. -/
noncomputable def isEmptyRicciDeTurckBanachChart
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := TM)) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (g₀ : _root_.Bundle.ContinuousRiemannianMetric F TM)
    (gF : MetricFamily (I := I) (M := M))
    (t₀ T : ℝ) (hT : t₀ < T) :
    TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover g₀ t₀ T
      (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊ * (T - t₀).toNNReal + 1)
      (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊) 0 0 where
  A := fun _ _ => isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀
  hT := hT
  picard :=
    { lipschitzOnWith := fun _ _ => by
        intro p _ q _
        exact (edist_self _).trans_le (zero_le _)
      continuousOn := fun _ _ => continuousOn_const
      norm_le := fun _ _ _ _ => le_of_eq (coe_nnnorm _).symm
      mul_max_le := by
        have ht0 : ((⟨t₀, ⟨le_rfl, le_of_lt hT⟩⟩ : Set.Icc t₀ T) : ℝ) = t₀ := rfl
        rw [ht0, sub_self, max_eq_left (by linarith : (0 : ℝ) ≤ T - t₀)]
        push_cast [Real.coe_toNNReal _ (by linarith : (0 : ℝ) ≤ T - t₀)]
        nlinarith [NNReal.coe_nonneg
          (‖isEmptyInitialSection (I := I) et Kc hKc Ko hKo hKoEq hcover g₀‖₊)] }
  lipschitz := fun _ => by
    intro p _ q _
    exact (edist_self _).trans_le (zero_le _)
  geometric := fun _ _ _ =>
    ⟨gF, chosenLeviCivitaFamily (I := I) (M := M) gF, fun x => isEmptyElim x⟩

/-- On an empty manifold the bundled continuous-section space is a subsingleton: two sections agree
because there are no points at which to compare them. -/
theorem continuousSectionSpace_subsingleton_of_isEmpty
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Subsingleton (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
      (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover) :=
  ⟨fun a b => ContinuousSectionSpace.ext fun x => isEmptyElim x⟩

/-- The first genuine inhabitant of `RicciDeTurckChartClosureData`: on an empty manifold every
Banach solution has a smooth chosen-background realization (all pointwise obligations are vacuous),
and every chosen DeTurck candidate encodes back into the chart via the constant Banach solution at
the initial section (whose ODE holds because the state space is a subsingleton, so the chart velocity
vanishes).  This completes the `{realization, encode}` fraction of the closure-data critical path. -/
noncomputable def isEmptyRicciDeTurckChartClosureData
    (x0 : κ → M)
    (et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj :
        _root_.Bundle.TotalSpace BilF
          (_root_.Bundle.BilinearFormBundle (V := TM)) → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF
      (_root_.Bundle.BilinearFormBundle (V := TM)) (x0 i))
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {ivp : InitialValueProblem (E := F) (H := H) (I := I) (M := M)}
    {T : ℝ} {a L Kpic Kstate : ℝ≥0}
    (chart : TimeDependentGeometricRicciDeTurckBanachChart
      (M := M) (F := F) (I := I)
      x0 et het Kc hKc Ko hKo hKoEq hcover
      ivp.initialMetric.toContinuousRiemannianMetric ivp.initialTime T a L Kpic Kstate)
    (gF : MetricFamily (I := I) (M := M)) :
    RicciDeTurckChartClosureData x0 et het Kc hKc Ko hKo hKoEq hcover chart := by
  haveI hSub :
      Subsingleton (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
        (V := _root_.Bundle.BilinearFormBundle (V := TM)) et Kc hKc Ko hKo hKoEq hcover) :=
    continuousSectionSpace_subsingleton_of_isEmpty (I := I)
      et Kc hKc Ko hKo hKoEq hcover
  exact
    { realization := fun _ =>
        { metric := gF
          background := chosenLeviCivitaFamily (I := I) (M := M) gF
          metric_eq_curve := fun _ _ x => isEmptyElim x
          boundary_hasTimeDerivative := fun _ _ _ x => isEmptyElim x
          chartRHS_eq_intrinsic := fun _ _ x => isEmptyElim x
          hbackground := rfl }
      encode := fun candidate =>
        { sol :=
            { terminalTime := candidate.1.terminalTime
              initial_lt_terminal := candidate.1.initial_lt_terminal
              curve := fun _ => InitialValueProblem.toContinuousSectionSpace
                (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp
              initial_eq := rfl
              equation := by
                intro t _
                have h0 : chart.A t ((fun _ : ℝ => InitialValueProblem.toContinuousSectionSpace
                    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp) t)
                    = (0 : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF)
                      (V := _root_.Bundle.BilinearFormBundle (V := TM))
                      et Kc hKc Ko hKo hKoEq hcover) := Subsingleton.elim _ _
                simp only [h0]
                exact hasDerivWithinAt_const t
                  (Set.Icc ivp.initialTime candidate.1.terminalTime)
                  (InitialValueProblem.toContinuousSectionSpace
                    (M := M) (F := F) (I := I) et Kc hKc Ko hKo hKoEq hcover ivp)
              mem_state := fun _ _ x => isEmptyElim x }
          realization :=
            { metric := gF
              metricVelocity := intrinsicRicciDeTurckRHS (I := I) (M := M) gF
                (chosenLeviCivitaFamily (I := I) (M := M) gF)
              background := chosenLeviCivitaFamily (I := I) (M := M) gF
              metric_eq_curve := fun _ _ x => isEmptyElim x
              hasTimeDerivative := fun _ _ x => isEmptyElim x
              equation := fun _ _ x => isEmptyElim x }
          terminal_eq := rfl
          metric_eq := fun _ _ x => isEmptyElim x } }

/-- **First chart/closure-data assembly of a genuine point-4 witness.**  On an empty manifold, the
constant-field Banach chart `isEmptyRicciDeTurckBanachChart` and its closure data
`isEmptyRicciDeTurckChartClosureData` compose through the already-proved bridge
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData` to a genuine
`IntrinsicLocalExistenceUniquenessFamily`.  This is the first end-to-end instantiation of the
chart → closure-data → bridge critical path (the empty cover `κ := Empty` is used, so the finite
cover condition `⋃ = univ` reduces to `∅ = ∅`). -/
noncomputable def intrinsicLocalExistenceUniquenessFamily_isEmpty :
    IntrinsicLocalExistenceUniquenessFamily (E := F) (H := H) (I := I) (M := M) := by
  haveI hMem : ∀ i : Empty, MemTrivializationAtlas
      ((fun i : Empty => i.elim :
        Empty → _root_.Bundle.Trivialization BilF
          (_root_.Bundle.TotalSpace.proj :
            _root_.Bundle.TotalSpace BilF
              (_root_.Bundle.BilinearFormBundle (V := TM)) → M)) i) :=
    fun i => i.elim
  exact intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData
    (κ := Empty)
    (x0 := fun i => i.elim) (et := fun i => i.elim) (het := fun i => i.elim)
    (Kc := fun i => i.elim) (hKc := fun i => i.elim) (Ko := fun i => i.elim)
    (hKo := fun i => i.elim) (hKoEq := fun i => i.elim)
    (hcover := Set.eq_univ_of_forall fun x => isEmptyElim x)
    (T := _) (a := _) (L := _) (Kpic := _) (Kstate := _)
    (chart := fun ivp => isEmptyRicciDeTurckBanachChart (κ := Empty)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (Set.eq_univ_of_forall fun x => isEmptyElim x)
      ivp.initialMetric.toContinuousRiemannianMetric
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M)
        ivp.initialMetric)
      ivp.initialTime (ivp.initialTime + 1) (by linarith))
    (D := fun ivp => isEmptyRicciDeTurckChartClosureData (κ := Empty)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
      (Set.eq_univ_of_forall fun x => isEmptyElim x)
      (isEmptyRicciDeTurckBanachChart (κ := Empty)
        (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
        (fun i => i.elim) (fun i => i.elim) (fun i => i.elim) (fun i => i.elim)
        (Set.eq_univ_of_forall fun x => isEmptyElim x)
        ivp.initialMetric.toContinuousRiemannianMetric
        (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M)
          ivp.initialMetric)
        ivp.initialTime (ivp.initialTime + 1) (by linarith))
      (CovariantDerivative.TimeDependentRiemannianMetric.const (I := I) (M := M)
        ivp.initialMetric))

end IsEmptyChart

end MetricLocusEvolution
end AnalyticPDE
end RicciFlow
