/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.TimePathGluing
public import LeanPool.NavierStokesAndEuler.Euler.DuhamelDifferentiation

/-! Exact pasting of genuine heat-Duhamel solutions on adjacent time intervals. -/

section

/-! Exact restart identities for the genuine cylinder heat and Bochner Duhamel integrals. -/

@[expose] public section

noncomputable section

namespace EulerHeatRestart

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerDuhamelDifferentiation EulerVolterraConvolution
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- Actual viscous heat obeys the semigroup law at nonnegative physical times. -/
theorem heatFlow_semigroup {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (u : SobolevSpace period q) :
    heatFlow period q ν s (heatFlow period q ν t u) = heatFlow period q ν (s+t) u := by
  unfold heatFlow
  rw [heatOperator_semigroup]
  apply congrArg (fun v : ℝ≥0 => heatOperator period q v u)
  rw [mul_add, Real.toNNReal_add (by positivity : 0 ≤ 2*ν*s) (by positivity : 0 ≤ 2*ν*t)]

/-- Heat propagates the earlier Duhamel history exactly to a later time. -/
theorem heatFlow_duhamel_history {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heatFlow period q ν (t-a) (duhamel period ν T hT f a) =
      ∫ s in (0 : ℝ)..a, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  unfold duhamel
  rw [← (heatFlow period q ν (t-a)).intervalIntegral_comp_comm
    ((shiftedHeat_continuous period ν T hT f a).intervalIntegrable 0 a)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with s hs
  rw [uIoc_of_le ha] at hs
  have hh := heatFlow_semigroup period ν hν (t-a) (a-s) (sub_nonneg.mpr hat) (sub_nonneg.mpr hs.2)
    (extendPath T hT f s)
  simpa only [sub_add_sub_cancel] using hh

/-- The actual Bochner Duhamel integral splits into propagated history and forcing after the restart
time. -/
theorem duhamel_restart {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    duhamel period ν T hT f t = heatFlow period q ν (t-a) (duhamel period ν T hT f a) +
      ∫ s in a..t, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  rw [heatFlow_duhamel_history period ν hν T hT f a t ha hat]
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable (μ := volume) 0 a)
    ((shiftedHeat_continuous period ν T hT f t).intervalIntegrable (μ := volume) a t)).symm

/-- The full genuine inhomogeneous heat solution restarts from its attained state. -/
theorem inhomogeneous_heat_restart {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (u₀ : SobolevSpace period q)
    (a t : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) :
    heatFlow period q ν t u₀ + duhamel period ν T hT f t =
      heatFlow period q ν (t-a) (heatFlow period q ν a u₀ + duhamel period ν T hT f a) +
        ∫ s in a..t, heatFlow period q ν (t-s) (extendPath T hT f s) := by
  rw [map_add, heatFlow_semigroup period ν hν (t-a) a (sub_nonneg.mpr hat) ha,
    sub_add_cancel, duhamel_restart period ν hν T hT f a t ha hat, add_assoc]

/-- The old-history and new-source identity written in elapsed time after the restart. -/
theorem duhamel_restart_shifted {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (T : ℝ) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q)) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    duhamel period ν T hT f (a+t) = heatFlow period q ν t (duhamel period ν T hT f a) +
      ∫ r in (0 : ℝ)..t, heatFlow period q ν (t-r) (extendPath T hT f (a+r)) := by
  have hh := duhamel_restart period ν hν T hT f a (a+t) ha (by linarith)
  rw [add_sub_cancel_left] at hh
  rw [hh]
  congr 1
  have hi := intervalIntegral.integral_comp_add_left
    (fun s => heatFlow period q ν (a+t-s) (extendPath T hT f s)) a (a := 0) (b := t)
  simp only [add_zero] at hi
  have he : (fun r => heatFlow period q ν (a+t-(a+r)) (extendPath T hT f (a+r))) =
      fun r => heatFlow period q ν (t-r) (extendPath T hT f (a+r)) := by
    funext r
    congr 2
    ring
  rw [he] at hi
  exact hi.symm

end EulerHeatRestart

end
end

end

@[expose] public section

noncomputable section

namespace EulerDuhamelPasting

open MeasureTheory Set EulerCylinderSobolevSpace EulerSobolevHeat EulerSobolevHeatGenerator
  EulerVolterraConvolution EulerDuhamelDifferentiation EulerHeatRestart EulerTimePathGluing
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual Duhamel integrals agree whenever their source fields agree on the integration interval.
-/
theorem duhamel_congr_initial {q : ℕ} (ν T1 T2 : ℝ) (hT1 : 0 ≤ T1) (hT2 : 0 ≤ T2)
    (f1 : C(Icc (0 : ℝ) T1, SobolevSpace period q))
    (f2 : C(Icc (0 : ℝ) T2, SobolevSpace period q)) (t : ℝ) (ht : 0 ≤ t)
    (hf : ∀ r ∈ Icc 0 t, extendPath T1 hT1 f1 r = extendPath T2 hT2 f2 r) :
    duhamel period ν T1 hT1 f1 t = duhamel period ν T2 hT2 f2 t := by
  unfold duhamel
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht] at hr
  exact congrArg (heatFlow period q ν (t-r)) (hf r hr)

/-- The exact inhomogeneous heat restart identity in elapsed time. -/
theorem inhomogeneous_restart_shifted {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν)
    (T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (u₀ : SobolevSpace period q) (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    heatFlow period q ν (a+t) u₀+duhamel period ν T hT f (a+t) =
      heatFlow period q ν t (heatFlow period q ν a u₀+duhamel period ν T hT f a) +
        ∫ r in (0 : ℝ)..t, heatFlow period q ν (t-r) (extendPath T hT f (a+r)) := by
  rw [map_add, heatFlow_semigroup period ν hν t a ht ha,
    duhamel_restart_shifted period ν hν T hT f a t ha ht]
  have he : t+a = a+t := add_comm _ _
  rw [he]
  abel

/-- The elapsed-time part of a genuine Duhamel integral is the restarted source integral. -/
theorem shifted_source_integral {q : ℕ} (ν a b T : ℝ) (hb : 0 ≤ b) (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, SobolevSpace period q))
    (g : C(Icc (0 : ℝ) b, SobolevSpace period q)) (t : ℝ) (ht : t ∈ Icc 0 b)
    (hfg : ∀ r ∈ Icc 0 b, extendPath T hT f (a + r) = extendPath b hb g r) :
    (∫ r in (0 : ℝ)..t, heatFlow period q ν (t-r) (extendPath T hT f (a+r))) =
      duhamel period ν b hb g t := by
  unfold duhamel
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le ht.1] at hr
  exact congrArg (heatFlow period q ν (t-r)) (hfg r ⟨hr.1,hr.2.trans ht.2⟩)

/-- The literal pasting of two actual mild solutions solves the complete Duhamel equation on their
union. -/
theorem glue_ordinary_mild {q : ℕ} (ν : ℝ) (hν : 0 ≤ ν) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, SobolevSpace period q))
    (v : C(Icc (0 : ℝ) b, SobolevSpace period q))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩)
    (f : C(Icc (0 : ℝ) (a + b), SobolevSpace period q))
    (f1 : C(Icc (0 : ℝ) a, SobolevSpace period q))
    (f2 : C(Icc (0 : ℝ) b, SobolevSpace period q)) (u₀ : SobolevSpace period q)
    (hF1 : ∀ r ∈ Icc 0 a, extendPath (a + b) (add_nonneg ha hb) f r = extendPath a ha f1 r)
    (hF2 : ∀ r ∈ Icc 0 b, extendPath (a + b) (add_nonneg ha hb) f (a + r) = extendPath b hb f2 r)
    (hsolu : ∀ t : Icc (0 : ℝ) a, u t = heatFlow period q ν t.val u₀+duhamel period ν a ha f1 t.val)
    (hsolv : ∀ t : Icc (0 : ℝ) b, v t = heatFlow period q ν t.val (u ⟨a,ha,le_rfl⟩)+duhamel period
        ν b hb f2 t.val) :
    ∀ t : Icc (0 : ℝ) (a+b), gluePath a b ha hb u v hmatch t =
      heatFlow period q ν t.val u₀+duhamel period ν (a+b) (add_nonneg ha hb) f t.val := by
  intro t
  by_cases hta : t.val ≤ a
  · have hf := duhamel_congr_initial period ν a (a+b) ha (add_nonneg ha hb) f1 f t.val t.property.1
      (fun r hr => (hF1 r ⟨hr.1,hr.2.trans hta⟩).symm)
    calc
      _ = extendPath a ha u t.val := glueFunction_left a b ha hb u v t.val hta
      _ = u ⟨t.val,t.property.1,hta⟩ := congrArg u (projIcc_of_mem ha ⟨t.property.1,hta⟩)
      _ = heatFlow period q ν t.val u₀+duhamel period ν a ha f1 t.val := hsolu _
      _ = _ := congrArg (fun x => heatFlow period q ν t.val u₀+x) hf
  · have hat : a ≤ t.val := (lt_of_not_ge hta).le
    let r := t.val-a
    have hr : r ∈ Icc 0 b := ⟨sub_nonneg.mpr hat, by dsimp [r]; linarith [t.property.2]⟩
    have htval : a+r = t.val := by dsimp [r]; ring
    have hf := duhamel_congr_initial period ν a (a+b) ha (add_nonneg ha hb) f1 f a ha
      (fun x hx => (hF1 x hx).symm)
    have hua : u ⟨a,ha,le_rfl⟩ = heatFlow period q ν a u₀+duhamel period ν (a+b) (add_nonneg ha hb)
        f a :=
      (hsolu _).trans (congrArg (fun x => heatFlow period q ν a u₀+x) hf)
    have hrestart := inhomogeneous_restart_shifted period ν hν (a+b) (add_nonneg ha hb) f u₀ a r ha
        hr.1
    have hs := shifted_source_integral period ν a b (a+b) hb (add_nonneg ha hb) f f2 r hr hF2
    rw [← hua,hs,htval] at hrestart
    calc
      _ = extendPath b hb v r := glueFunction_right a b ha hb u v hmatch t.val hat
      _ = v ⟨r,hr⟩ := congrArg v (projIcc_of_mem hb hr)
      _ = heatFlow period q ν r (u ⟨a,ha,le_rfl⟩)+duhamel period ν b hb f2 r := hsolv _
      _ = _ := hrestart.symm

end EulerDuhamelPasting
