/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TimePathGluing
public import LeanPool.NavierStokesAndEuler.Euler.DuhamelDifferentiation
import LeanPool.NavierStokesAndEuler.Euler.HeatRestart

/-! Exact pasting of genuine heat-Duhamel solutions on adjacent time intervals. -/

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
