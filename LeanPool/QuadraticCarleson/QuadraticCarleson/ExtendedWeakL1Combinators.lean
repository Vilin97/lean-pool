/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KaltonPaperApplication
import LeanPool.QuadraticCarleson.QuadraticCarleson.HardyLittlewoodMaximal

/-!
# Elementary weak-L¹ combinators for extended nonnegative outputs

These lemmas transfer distribution estimates through the concrete pointwise
comparison `F ≤ 2 H + 16 M` used for the finite low-modulation block.
-/

open MeasureTheory Set
open scoped ENNReal

namespace QuadraticCarleson
namespace ExtendedWeakL1Combinators

open KaltonPaperApplication


theorem HasExtendedWeakL1Bound.mono_output
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {A : ℝ} {F G : X → ENNReal}
    (h : HasExtendedWeakL1Bound mu A G) (hFG : ∀ x, F x ≤ G x) :
    HasExtendedWeakL1Bound mu A F := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact (mul_le_mul' le_rfl (measure_mono fun x hx ↦ hx.trans_le (hFG x))).trans
    (h.2 a ha)

theorem HasExtendedWeakL1Bound.mono_constant
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {A B : ℝ} {F : X → ENNReal}
    (h : HasExtendedWeakL1Bound mu A F) (hAB : A ≤ B) :
    HasExtendedWeakL1Bound mu B F := by
  refine ⟨h.1.trans hAB, ?_⟩
  intro a ha
  exact (h.2 a ha).trans (ENNReal.ofReal_le_ofReal hAB)

theorem HasExtendedWeakL1Bound.restrict
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {A : ℝ} {F : X → ENNReal} (h : HasExtendedWeakL1Bound mu A F)
    (s : Set X) : HasExtendedWeakL1Bound (mu.restrict s) A F := by
  refine ⟨h.1, ?_⟩
  intro a ha
  exact (mul_le_mul' le_rfl (Measure.restrict_le_self _)).trans (h.2 a ha)

/-- A directed countable supremum inherits any weak `L¹` constant which is
uniform over the approximating family.  This is the distribution-function
form of continuity from below and does not require choosing pointwise-finite
representatives of the limiting extended-valued output. -/
theorem hasExtendedWeakL1Bound_iSup_of_directed
    {X ι : Type*} [MeasurableSpace X] [Countable ι] [Nonempty ι]
    {mu : Measure X} {A : ℝ} {F : ι → X → ENNReal}
    (hdir : Directed (fun G H : X → ENNReal ↦ ∀ x, G x ≤ H x) F)
    (hweak : ∀ i, HasExtendedWeakL1Bound mu A (F i)) :
    HasExtendedWeakL1Bound mu A (fun x ↦ ⨆ i, F i x) := by
  classical
  refine ⟨(hweak (Classical.choice inferInstance)).1, ?_⟩
  intro a ha
  let E : ι → Set X := fun i ↦ {x | ENNReal.ofReal a < F i x}
  have hEdir : Directed (· ⊆ ·) E := by
    intro i j
    obtain ⟨k, hik, hjk⟩ := hdir i j
    exact ⟨k, fun x hx ↦ hx.trans_le (hik x), fun x hx ↦ hx.trans_le (hjk x)⟩
  have hEunion : (⋃ i, E i) = {x | ENNReal.ofReal a < ⨆ i, F i x} := by
    ext x
    simp only [E, mem_iUnion, mem_setOf_eq, lt_iSup_iff]
  rw [← hEunion, hEdir.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun i ↦ (hweak i).2 a ha

/-- Weak bounds for two outputs combine across the exact coefficients that
occur in the smooth-to-sharp quadratic-kernel comparison. -/
theorem hasExtendedWeakL1Bound_of_le_two_mul_add_sixteen_mul
    {X : Type*} [MeasurableSpace X] {mu : Measure X}
    {AH AM : ℝ} {F H M : X → ENNReal}
    (hF : ∀ x, F x ≤ 2 * H x + 16 * M x)
    (hH : HasExtendedWeakL1Bound mu AH H)
    (hM : HasExtendedWeakL1Bound mu AM M) :
    HasExtendedWeakL1Bound mu (4 * AH + 32 * AM) F := by
  have hAH : 0 ≤ AH := hH.1
  have hAM : 0 ≤ AM := hM.1
  refine ⟨by positivity, ?_⟩
  intro a ha
  let E : Set X := {x | ENNReal.ofReal a < F x}
  let EH : Set X := {x | ENNReal.ofReal (a / 4) < H x}
  let EM : Set X := {x | ENNReal.ofReal (a / 32) < M x}
  have ha4 : 0 < a / 4 := by positivity
  have ha32 : 0 < a / 32 := by positivity
  have hfour : (4 : ENNReal) * ENNReal.ofReal (a / 4) = ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    ring
  have hthirtytwo : (32 : ENNReal) * ENNReal.ofReal (a / 32) =
      ENNReal.ofReal a := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32)]
    congr 1
    ring
  have htwo : (2 : ENNReal) * ENNReal.ofReal (a / 4) =
      ENNReal.ofReal (a / 2) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsixteen : (16 : ENNReal) * ENNReal.ofReal (a / 32) =
      ENNReal.ofReal (a / 2) := by
    rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul
      (by norm_num : (0 : ℝ) ≤ 16)]
    congr 1
    ring
  have hhalf : ENNReal.ofReal (a / 2) + ENNReal.ofReal (a / 2) =
      ENNReal.ofReal a := by
    rw [← two_mul, ← ENNReal.ofReal_ofNat,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsub : E ⊆ EH ∪ EM := by
    intro x hx
    by_contra hxunion
    have hxH : H x ≤ ENNReal.ofReal (a / 4) := by
      exact le_of_not_gt fun hlt ↦ hxunion (Or.inl hlt)
    have hxM : M x ≤ ENNReal.ofReal (a / 32) := by
      exact le_of_not_gt fun hlt ↦ hxunion (Or.inr hlt)
    have hupper : 2 * H x + 16 * M x ≤ ENNReal.ofReal a := by
      calc
        2 * H x + 16 * M x ≤
            2 * ENNReal.ofReal (a / 4) +
              16 * ENNReal.ofReal (a / 32) := add_le_add
                (mul_le_mul' le_rfl hxH) (mul_le_mul' le_rfl hxM)
        _ = ENNReal.ofReal a := by rw [htwo, hsixteen, hhalf]
    exact (not_lt_of_ge ((hF x).trans hupper)) hx
  calc
    ENNReal.ofReal a * mu E ≤ ENNReal.ofReal a * (mu EH + mu EM) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans (measure_union_le EH EM))
    _ = ENNReal.ofReal a * mu EH + ENNReal.ofReal a * mu EM := by
      rw [mul_add]
    _ = 4 * (ENNReal.ofReal (a / 4) * mu EH) +
        32 * (ENNReal.ofReal (a / 32) * mu EM) := by
      have htermH : ENNReal.ofReal a * mu EH =
          4 * (ENNReal.ofReal (a / 4) * mu EH) := by
        rw [← hfour, mul_assoc]
      have htermM : ENNReal.ofReal a * mu EM =
          32 * (ENNReal.ofReal (a / 32) * mu EM) := by
        rw [← hthirtytwo, mul_assoc]
      exact congrArg₂ (· + ·) htermH htermM
    _ ≤ 4 * ENNReal.ofReal AH + 32 * ENNReal.ofReal AM := by
      gcongr
      · exact hH.2 (a / 4) ha4
      · exact hM.2 (a / 32) ha32
    _ = ENNReal.ofReal (4 * AH + 32 * AM) := by
      rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) hAH),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
        ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 32),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_ofNat]
      positivity

/-- The concrete centered Hardy--Littlewood maximal function, applied to the
norm of an integrable input, in the extended weak-bound interface. -/
theorem hasExtendedWeakL1Bound_centeredHardyLittlewoodMaximal_enorm
    {f : ℝ → ℂ} (hf : Measurable f) (hfi : Integrable f) :
    HasExtendedWeakL1Bound volume
      (4 * (∫⁻ x, ‖f x‖ₑ).toReal)
      (centeredHardyLittlewoodMaximal fun x ↦ ‖f x‖ₑ) := by
  have hmass : (∫⁻ x, ‖f x‖ₑ) ≠ ∞ := hfi.hasFiniteIntegral.ne
  refine ⟨mul_nonneg (by norm_num) ENNReal.toReal_nonneg, ?_⟩
  intro a ha
  have h := centeredHardyLittlewoodMaximal_weak_bound
    (fun x ↦ ‖f x‖ₑ) (ENNReal.ofReal a)
  apply h.trans_eq
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_ofNat, ENNReal.ofReal_toReal hmass]


end ExtendedWeakL1Combinators
end QuadraticCarleson
