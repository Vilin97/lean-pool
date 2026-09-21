/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/

import LeanPool.FullyDynamicMatching.FD1D.V5.QuantileSquared

/-!
# Squared matching cost for the v5 policy

This module combines the exact squared-quantile identity with the one-cell
spatial coupling. It proves the manuscript's conditional and count-law RMS
bounds while allowing arbitrary occupied locations inside their certified
dyadic cells.
-/

namespace FD1D.V5.Transport

noncomputable section

open scoped BigOperators
open Set MeasureTheory

variable {L m : ℕ}

/-- Conditional squared distance to the actual selected supply point. -/
def expectedActualSquaredDistance
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) : ℝ :=
  ∫ u in Icc (0 : ℝ) 1,
    (C.selectedSupplyPoint q fallback u - u) ^ 2

private theorem selectedSquaredDistance_integrable
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (fallback : Fin m) :
    IntegrableOn
      (fun u => (C.selectedSupplyPoint q fallback u - u) ^ 2)
      (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (((C.selectedSupplyPoint_measurable q fallback).sub
      measurable_id).pow_const 2).aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖(C.selectedSupplyPoint q fallback u - u) ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hs := C.selectedSupplyPoint_mem_unit q fallback u
  have habs :
      |C.selectedSupplyPoint q fallback u - u| ≤ 1 :=
    abs_le.2 ⟨by linarith [hs.1, hu.2], by linarith [hs.2, hu.1]⟩
  calc
    (C.selectedSupplyPoint q fallback u - u) ^ 2 =
        |C.selectedSupplyPoint q fallback u - u| ^ 2 := by
      rw [sq_abs]
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) habs

private theorem quantileDisplacement_integrable
    (q : DyadicMass L) (hq : q.IsProbability) :
    IntegrableOn (fun u => q.quantile u - u) (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    (q.quantile_measurable.sub measurable_id).aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖q.quantile u - u‖ ≤ 1
  rw [Real.norm_eq_abs]
  have hqUnit := q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  exact abs_le.2
    ⟨by linarith [hqUnit.1, hu.2], by linarith [hqUnit.2, hu.1]⟩

private theorem quantileSquaredDisplacement_integrable
    (q : DyadicMass L) (hq : q.IsProbability) :
    IntegrableOn (fun u => (q.quantile u - u) ^ 2)
      (Icc (0 : ℝ) 1) := by
  apply Measure.integrableOn_of_bounded (by simp [Real.volume_Icc])
    ((q.quantile_measurable.sub measurable_id).pow_const
      2).aestronglyMeasurable (M := 1)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  change ‖(q.quantile u - u) ^ 2‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hqUnit := q.quantile_mem_unit hq.nonneg hu.1
    (by simpa [hq.total_eq_one] using hu.2)
  have habs : |q.quantile u - u| ≤ 1 :=
    abs_le.2
      ⟨by linarith [hqUnit.1, hu.2],
        by linarith [hqUnit.2, hu.1]⟩
  calc
    (q.quantile u - u) ^ 2 = |q.quantile u - u| ^ 2 := by
      rw [sq_abs]
    _ ≤ 1 := pow_le_one₀ (abs_nonneg _) habs

/--
Minkowski's inequality for the actual selected supply and the recursive
quantile, with the deterministic one-cell error made explicit.
-/
theorem expectedActualSquaredDistance_le
    (C : SupplyConfiguration L m) (q : DyadicMass L)
    (hq : q.IsProbability) (hsupport : C.Supports q)
    (fallback : Fin m) :
    expectedActualSquaredDistance C q fallback ≤
      (dyadicCellWidth L +
        Real.sqrt
          (∫ u in Icc (0 : ℝ) 1, (q.quantile u - u) ^ 2)) ^ 2 := by
  let d : ℝ → ℝ := fun u => q.quantile u - u
  let w : ℝ := dyadicCellWidth L
  have hw : 0 ≤ w := (dyadicCellWidth_pos L).le
  have hselected :=
    selectedSquaredDistance_integrable C q fallback
  have hd : IntegrableOn d (Icc (0 : ℝ) 1) := by
    simpa [d] using quantileDisplacement_integrable q hq
  have hdabs : IntegrableOn (fun u => |d u|) (Icc (0 : ℝ) 1) :=
    hd.norm
  have hdsq : IntegrableOn (fun u => d u ^ 2) (Icc (0 : ℝ) 1) := by
    simpa [d] using quantileSquaredDisplacement_integrable q hq
  have hconst :
      IntegrableOn (fun _ : ℝ => w ^ 2) (Icc (0 : ℝ) 1) :=
    integrableOn_const (C := w ^ 2) (by simp [Real.volume_Icc])
  have hlinear :
      IntegrableOn (fun u => 2 * w * |d u|) (Icc (0 : ℝ) 1) :=
    hdabs.const_mul (2 * w)
  have hrhs :
      IntegrableOn
        (fun u => w ^ 2 + 2 * w * |d u| + d u ^ 2)
        (Icc (0 : ℝ) 1) :=
    (hconst.add hlinear).add hdsq
  have hclose := C.selectedSupplyPoint_sub_quantile_le_ae
    q hq hsupport fallback
  have hpoint :
      ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
        (C.selectedSupplyPoint q fallback u - u) ^ 2 ≤
          w ^ 2 + 2 * w * |d u| + d u ^ 2 := by
    have hclose' :
        ∀ᵐ u ∂volume.restrict (Icc (0 : ℝ) 1),
          |C.selectedSupplyPoint q fallback u - q.quantile u| ≤ w := by
      simpa [DyadicMass.uniformDemand, w] using hclose
    filter_upwards [hclose'] with u hu
    have htriangle :
        |C.selectedSupplyPoint q fallback u - u| ≤ w + |d u| := by
      calc
        |C.selectedSupplyPoint q fallback u - u| ≤
            |C.selectedSupplyPoint q fallback u - q.quantile u| +
              |q.quantile u - u| := abs_sub_le _ _ _
        _ ≤ w + |d u| := by
          have h := add_le_add_right hu |q.quantile u - u|
          simpa [d, add_comm] using h
    have hnonneg : 0 ≤ w + |d u| :=
      add_nonneg hw (abs_nonneg _)
    have hsquare :
        |C.selectedSupplyPoint q fallback u - u| ^ 2 ≤
          (w + |d u|) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) hnonneg).2 htriangle
    calc
      (C.selectedSupplyPoint q fallback u - u) ^ 2 =
          |C.selectedSupplyPoint q fallback u - u| ^ 2 := by
        rw [sq_abs]
      _ ≤ (w + |d u|) ^ 2 := hsquare
      _ = w ^ 2 + 2 * w * |d u| + d u ^ 2 := by
        rw [← sq_abs (d u)]
        ring
  have hintegral :
      expectedActualSquaredDistance C q fallback ≤
        w ^ 2 + 2 * w * cdfTransportArea d +
          ∫ u in Icc (0 : ℝ) 1, d u ^ 2 := by
    calc
      expectedActualSquaredDistance C q fallback ≤
          ∫ u in Icc (0 : ℝ) 1,
            (w ^ 2 + 2 * w * |d u| + d u ^ 2) :=
        integral_mono_ae hselected hrhs hpoint
      _ = (∫ u in Icc (0 : ℝ) 1,
            (w ^ 2 + 2 * w * |d u|)) +
          ∫ u in Icc (0 : ℝ) 1, d u ^ 2 :=
        MeasureTheory.integral_add (hconst.add hlinear) hdsq
      _ = ((∫ u in Icc (0 : ℝ) 1, w ^ 2) +
            ∫ u in Icc (0 : ℝ) 1, 2 * w * |d u|) +
          ∫ u in Icc (0 : ℝ) 1, d u ^ 2 := by
        rw [MeasureTheory.integral_add hconst hlinear]
      _ = w ^ 2 +
          2 * w * (∫ u in Icc (0 : ℝ) 1, |d u|) +
          ∫ u in Icc (0 : ℝ) 1, d u ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
        simp
      _ = _ := rfl
  let D : ℝ := ∫ u in Icc (0 : ℝ) 1, d u ^ 2
  have hD : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  have harea : 0 ≤ cdfTransportArea d :=
    cdfTransportArea_nonneg d
  have hareaSq : cdfTransportArea d ^ 2 ≤ D := by
    simpa [D] using integral_abs_sq_le_integral_sq hd hdsq
  have hareaSqrt : cdfTransportArea d ≤ Real.sqrt D :=
    (Real.le_sqrt harea hD).2 hareaSq
  have hsqrtD := Real.sq_sqrt hD
  calc
    expectedActualSquaredDistance C q fallback ≤
        w ^ 2 + 2 * w * cdfTransportArea d + D := hintegral
    _ ≤ (w + Real.sqrt D) ^ 2 := by
      nlinarith
    _ = (dyadicCellWidth L +
          Real.sqrt
            (∫ u in Icc (0 : ℝ) 1, (q.quantile u - u) ^ 2)) ^ 2 := by
      rfl

/-- Count-state envelope for the actual conditional squared matching cost. -/
def stateSquaredCostEnvelope
    (a : ℝ) (x : InventoryState (DyadicNode L) m) : ℝ :=
  (dyadicCellWidth L +
    Real.sqrt
      (haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
        (stateHaarCoefficient a x))) ^ 2

theorem expectedActualSquaredDistance_le_stateEnvelope
    (a : ℝ) (ha : 0 < a) (hm : 0 < m)
    (C : SupplyConfiguration L m) (fallback : Fin m) :
    expectedActualSquaredDistance C
        (stateDyadicMass a C.countState) fallback ≤
      stateSquaredCostEnvelope a C.countState := by
  let q := stateDyadicMass a C.countState
  have hq := stateDyadicMass_isProbability a ha hm C.countState
  have hsupport : C.Supports q :=
    C.supports_of_deletionRule q
      (Dynamics.deletionRule a ha hm)
      (stateDyadicMass_leafMass_eq_deletionRule
        a ha hm C.countState)
  have hbound :=
    expectedActualSquaredDistance_le C q hq hsupport fallback
  rw [DyadicMass.quantile_sq_integral_eq_haarL2 q hq] at hbound
  dsimp [q] at hbound
  have hcoeff :
      (stateDyadicMass a C.countState).nodeCoefficient =
        stateHaarCoefficient a C.countState := by
    funext i
    exact stateDyadicMass_nodeCoefficient a C.countState i
  rw [hcoeff] at hbound
  simpa [stateSquaredCostEnvelope] using hbound

private theorem stateHaarEnergy_nonneg
    (a : ℝ) (x : InventoryState (DyadicNode L) m) :
    0 ≤ haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
      (stateHaarCoefficient a x) := by
  unfold haarL2
  exact integral_nonneg fun _ => sq_nonneg _

/--
Finite-law Minkowski/Jensen inequality for a deterministic error plus a
state-dependent nonnegative squared error.
-/
theorem sqrt_expect_add_sqrt_sq_le
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteLaw Omega) (w : ℝ) (hw : 0 ≤ w)
    (H : Omega → ℝ) (hH : ∀ omega, 0 ≤ H omega) :
    Real.sqrt (mu.expect (fun omega =>
        (w + Real.sqrt (H omega)) ^ 2)) ≤
      w + Real.sqrt (mu.expect H) := by
  let EH : ℝ := mu.expect H
  have hEH : 0 ≤ EH := mu.expect_nonneg hH
  have hsqrtMean :
      mu.expect (fun omega => Real.sqrt (H omega)) ≤
        Real.sqrt EH := by
    apply mu.expect_le_sqrt_expect_sq
    · exact fun _ => Real.sqrt_nonneg _
    · exact hH
    · intro omega
      exact (Real.sq_sqrt (hH omega)).le
  have hexpand :
      mu.expect (fun omega => (w + Real.sqrt (H omega)) ^ 2) =
        w ^ 2 +
          2 * w * mu.expect (fun omega => Real.sqrt (H omega)) +
          EH := by
    rw [show (fun omega => (w + Real.sqrt (H omega)) ^ 2) =
        fun omega =>
          w ^ 2 + 2 * w * Real.sqrt (H omega) + H omega by
      funext omega
      calc
        (w + Real.sqrt (H omega)) ^ 2 =
            w ^ 2 + 2 * w * Real.sqrt (H omega) +
              Real.sqrt (H omega) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (hH omega)]]
    rw [mu.expect_add, mu.expect_add, mu.expect_const,
      mu.expect_const_mul]
  have hbound :
      mu.expect (fun omega => (w + Real.sqrt (H omega)) ^ 2) ≤
        (w + Real.sqrt EH) ^ 2 := by
    rw [hexpand]
    nlinarith [Real.sq_sqrt hEH]
  exact (Real.sqrt_le_iff).2
    ⟨add_nonneg hw (Real.sqrt_nonneg _), hbound⟩

/--
The count-law RMS envelope. Tree symmetry converts its mean Haar energy to
`E[G]/12`, yielding exactly the transport-cost inequality in the manuscript.
-/
theorem sqrt_expected_stateSquaredCostEnvelope_le
    (a : ℝ)
    (μ : FiniteLaw (InventoryState (DyadicNode L) m))
    (hinv : ∀ (d : Fin L) (v : DyadicNode d.val),
      FiniteKernel.LawInvariant μ
        (FD1D.TreeSymmetry.inventorySwap d.isLt v)) :
    Real.sqrt (μ.expect (stateSquaredCostEnvelope a)) ≤
      dyadicCellWidth L +
        Real.sqrt ((1 / 12) *
          μ.expect (Dynamics.stateTransportEnergy a)) := by
  let H : InventoryState (DyadicNode L) m → ℝ := fun x =>
    haarL2 (haarNodeLeft (L := L)) (haarNodeWidth (L := L))
      (stateHaarCoefficient a x)
  let w : ℝ := dyadicCellWidth L
  have hw : 0 ≤ w := (dyadicCellWidth_pos L).le
  have hH (x : InventoryState (DyadicNode L) m) : 0 ≤ H x := by
    exact stateHaarEnergy_nonneg a x
  have hsqrt :
      Real.sqrt (μ.expect (stateSquaredCostEnvelope a)) ≤
        w + Real.sqrt (μ.expect H) := by
    change Real.sqrt (μ.expect (fun x =>
      (w + Real.sqrt (H x)) ^ 2)) ≤
        w + Real.sqrt (μ.expect H)
    exact sqrt_expect_add_sqrt_sq_le μ w hw H hH
  have henergy :=
    expected_haarL2_eq_transportEnergy a μ hinv
  change μ.expect H = (1 / 12) *
    μ.expect (Dynamics.stateTransportEnergy a) at henergy
  simpa [w, henergy] using hsqrt

end

end FD1D.V5.Transport
