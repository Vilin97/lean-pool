/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FiniteSpatialJet
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.LinearGlobalExistence

/-! Global recursive jet flows, built by solving each new derivative level as
a linear equation along the preceding jet trajectory. -/

@[expose] public section

open Homogenization
open scoped ContDiff Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- Linear coefficient governing the next spatial jet along the lower-order jet flow. -/
def FiniteSpatialJetGlobal.spatialJetLinearCoefficient
    (b : ℝ → Vec 2 → Vec 2) (n : ℕ)
    (Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n)
    (z : SpatialJetState n) (s t : ℝ) :
    SpatialJetState n →L[ℝ] SpatialJetState n :=
  (fderiv ℝ (Function.uncurry (spatialJetField b n)) (t, Y t z s)).comp
    (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))

theorem FiniteSpatialJetGlobal.spatialJetLinearCoefficient_continuous
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {n : ℕ} {Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n}
    (hY : IsFlowOn (spatialJetField b n) Y) (z : SpatialJetState n) (s : ℝ) :
    Continuous (FiniteSpatialJetGlobal.spatialJetLinearCoefficient b n Y z s) := by
  have hF : ContDiff ℝ ∞ (Function.uncurry (spatialJetField b n)) :=
    spatialJetField_smooth hb n
  have hD : ContDiff ℝ ∞ (fun p : ℝ × SpatialJetState n =>
      (fderiv ℝ (Function.uncurry (spatialJetField b n)) p).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) := by
    exact (hF.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hYcontinuous : Continuous (fun t => Y t z s) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hY.2 z s t).continuousAt
  have hparam : Continuous (fun t : ℝ => (t, Y t z s)) :=
    continuous_id.prodMk hYcontinuous
  exact hD.continuous.comp hparam

/-- Choose the unique global flow of a continuous linear differential equation. -/
noncomputable def FiniteSpatialJetGlobal.chosenLinearFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) : ℝ → E → ℝ → E :=
  Classical.choose (existsUnique_linearFlowOn A hA)

theorem FiniteSpatialJetGlobal.chosenLinearFlow_isFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (hA : Continuous A) :
    IsFlowOn (fun t z => A t z) (FiniteSpatialJetGlobal.chosenLinearFlow A hA) :=
  (Classical.choose_spec (existsUnique_linearFlowOn A hA)).1

/-- Linear flow used to extend a given spatial jet by one derivative order. -/
noncomputable def FiniteSpatialJetGlobal.spatialJetLinearFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {n : ℕ} (Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n)
    (hY : IsFlowOn (spatialJetField b n) Y) (z : SpatialJetState n) (s : ℝ) :
    ℝ → SpatialJetState n → ℝ → SpatialJetState n :=
  FiniteSpatialJetGlobal.chosenLinearFlow (FiniteSpatialJetGlobal.spatialJetLinearCoefficient b n
      Y z s)
    (FiniteSpatialJetGlobal.spatialJetLinearCoefficient_continuous hb hY z s)

theorem FiniteSpatialJetGlobal.spatialJetLinearFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {n : ℕ} (Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n)
    (hY : IsFlowOn (spatialJetField b n) Y) (z : SpatialJetState n) (s : ℝ) :
    IsFlowOn (fun t v => FiniteSpatialJetGlobal.spatialJetLinearCoefficient b n Y z s t v)
      (FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z s) := by
  exact FiniteSpatialJetGlobal.chosenLinearFlow_isFlow _ _

/-- One recursive jet extension over an already constructed lower flow. -/
noncomputable def FiniteSpatialJetGlobal.spatialJetFlowNext
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {n : ℕ} (Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n)
    (hY : IsFlowOn (spatialJetField b n) Y) :
    ℝ → SpatialJetState (n + 1) → ℝ → SpatialJetState (n + 1) :=
  fun t z s =>
    (Y t z.1 s, fun i => FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z.1 s t (z.2 i) s)

theorem FiniteSpatialJetGlobal.spatialJetFlowNext_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {n : ℕ} (Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n)
    (hY : IsFlowOn (spatialJetField b n) Y) :
    IsFlowOn (spatialJetField b (n + 1)) (FiniteSpatialJetGlobal.spatialJetFlowNext hb Y hY) := by
  constructor
  · intro z s
    rcases z with ⟨z, columns⟩
    apply Prod.ext
    · exact hY.1 z s
    · funext i
      exact (FiniteSpatialJetGlobal.spatialJetLinearFlow_isFlow hb Y hY z s).1 (columns i) s
  · intro z s t
    rcases z with ⟨z, columns⟩
    have hbase := hY.2 z s t
    have hlinear := FiniteSpatialJetGlobal.spatialJetLinearFlow_isFlow hb Y hY z s
    have hcolumns (i : Fin 2) :
        HasDerivAt
          (fun r => FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z s r (columns i) s)
          (FiniteSpatialJetGlobal.spatialJetLinearCoefficient b n Y z s t
            (FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z s t (columns i) s)) t :=
      hlinear.2 (columns i) s t
    have hcolumns' : HasDerivAt
        (fun r => fun i => FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z s r (columns i) s)
        (fun i => FiniteSpatialJetGlobal.spatialJetLinearCoefficient b n Y z s t
          (FiniteSpatialJetGlobal.spatialJetLinearFlow hb Y hY z s t (columns i) s)) t :=
      hasDerivAt_pi.mpr hcolumns
    have hpair := hbase.prodMk hcolumns'
    convert hpair using 1 <;> rfl

/-- Compatible spatial jet flows constructed inductively from the underlying flow. -/
noncomputable def FiniteSpatialJetGlobal.spatialJetFlowData
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (X : ℝ → Vec 2 → ℝ → Vec 2) (hX : IsFlowOn b X) :
    (n : ℕ) → {Y : ℝ → SpatialJetState n → ℝ → SpatialJetState n //
      IsFlowOn (spatialJetField b n) Y}
  | 0 => ⟨X, hX⟩
  | n + 1 =>
      let prev := FiniteSpatialJetGlobal.spatialJetFlowData hb X hX n
      ⟨FiniteSpatialJetGlobal.spatialJetFlowNext hb prev.val prev.property,
        FiniteSpatialJetGlobal.spatialJetFlowNext_isFlow hb prev.val prev.property⟩

/-- The initial value of each recursive jet flow is the corresponding jet of
the identity map: position is `x`, the first derivative is the identity, and
every higher derivative is zero. -/
noncomputable def spatialJetIdentitySeed :
    (n : ℕ) → Vec 2 → SpatialJetState n
  | 0 => id
  | n + 1 => fun x =>
      (spatialJetIdentitySeed n x,
        fun i => fderiv ℝ (spatialJetIdentitySeed n) x (Pi.single i 1))

/-- Every identity-jet seed is smooth. -/
theorem spatialJetIdentitySeed_smooth :
    ∀ n, ContDiff ℝ ∞ (spatialJetIdentitySeed n) := by
  intro n
  induction n with
  | zero => exact contDiff_id
  | succ n ih =>
      have hD : ContDiff ℝ ∞ (fun x => fderiv ℝ (spatialJetIdentitySeed n) x) :=
        ih.fderiv_right (by norm_num)
      have hcols : ContDiff ℝ ∞
          (fun x => fun i => fderiv ℝ (spatialJetIdentitySeed n) x (Pi.single i 1)) := by
        apply contDiff_pi.2
        intro i
        exact hD.clm_apply contDiff_const
      exact ih.prodMk hcols

/-- The first identity jet consists of the point and its two coordinate
directions. -/
theorem spatialJetIdentitySeed_one (x : Vec 2) :
    spatialJetIdentitySeed 1 x = (x, fun i => Pi.single i 1) := by
  change (x, fun i => fderiv ℝ id x (Pi.single i 1)) =
    (x, fun i => Pi.single i 1)
  apply Prod.ext
  · rfl
  · funext i
    rw [fderiv_id]
    rfl

/-- A recursively augmented jet flow. Each new column is obtained from the
global linear variational equation along the preceding jet trajectory. -/
noncomputable def spatialJetFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    (X : ℝ → Vec 2 → ℝ → Vec 2) (hX : IsFlowOn b X)
    (n : ℕ) : ℝ → SpatialJetState n → ℝ → SpatialJetState n :=
  (FiniteSpatialJetGlobal.spatialJetFlowData hb X hX n).val

/-- Every recursive finite jet equation has a global flow. Existence at each
new level follows from global existence for its linear variational columns. -/
theorem spatialJetFlow_isFlow
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : IsFlowOn b X) (n : ℕ) :
    IsFlowOn (spatialJetField b n) (spatialJetFlow hb X hX n) :=
  (FiniteSpatialJetGlobal.spatialJetFlowData hb X hX n).property

end

end AVenhance.Infra.Flow
