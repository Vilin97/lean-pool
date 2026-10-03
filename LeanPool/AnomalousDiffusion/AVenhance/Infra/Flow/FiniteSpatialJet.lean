/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.JointSmoothBootstrap
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.FirstJet
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Topology.MetricSpace.ProperSpace

/-! Recursive finite spatial-jet state spaces and their smooth augmented ODE fields. -/

@[expose] public section

open Homogenization
open Set
open scoped ContDiff NNReal Topology

namespace AVenhance.Infra.Flow

noncomputable section

/-- The state of the `n`th spatial-jet system: at each stage append the
derivative of the preceding jet with respect to the original base point. -/
def SpatialJetState : ℕ → Type
  | 0 => Vec 2
  | n + 1 => SpatialJetState n × (Fin 2 → SpatialJetState n)

instance (n : ℕ) : NormedAddCommGroup (SpatialJetState n) := by
  induction n with
  | zero => change NormedAddCommGroup (Vec 2); infer_instance
  | succ n ih =>
      change NormedAddCommGroup (SpatialJetState n × (Fin 2 → SpatialJetState n))
      letI : NormedAddCommGroup (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : NormedSpace ℝ (SpatialJetState n) := by
  induction n with
  | zero => change NormedSpace ℝ (Vec 2); infer_instance
  | succ n ih =>
      change NormedSpace ℝ (SpatialJetState n × (Fin 2 → SpatialJetState n))
      letI : NormedAddCommGroup (SpatialJetState n) := inferInstance
      letI : NormedSpace ℝ (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : CompleteSpace (SpatialJetState n) := by
  induction n with
  | zero => change CompleteSpace (Vec 2); infer_instance
  | succ n ih =>
      change CompleteSpace (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : CompleteSpace (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : FiniteDimensional ℝ (SpatialJetState n) := by
  induction n with
  | zero => change FiniteDimensional ℝ (Vec 2); infer_instance
  | succ n ih =>
      change FiniteDimensional ℝ (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : FiniteDimensional ℝ (SpatialJetState n) := ih
      infer_instance

instance (n : ℕ) : Nontrivial (SpatialJetState n) := by
  induction n with
  | zero => change Nontrivial (Vec 2); infer_instance
  | succ n ih =>
      change Nontrivial (SpatialJetState n × (Fin 2 → SpatialJetState n))
      let : Nontrivial (SpatialJetState n) := ih
      infer_instance

/-- The recursive augmented field. Its new component is the state derivative
of the preceding augmented field, composed with the appended jet direction. -/
def spatialJetField (b : ℝ → Vec 2 → Vec 2) :
    (n : ℕ) → ℝ → SpatialJetState n → SpatialJetState n :=
  Nat.rec b (fun n F t z =>
    (F t z.1, fun i =>
      ((fderiv ℝ (Function.uncurry F) (t, z.1)).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) (z.2 i)))

/-- Every finite augmented spatial-jet field is smooth when the original field
is smooth. The induction uses smoothness of Fréchet derivatives and evaluation. -/
theorem spatialJetField_smooth
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) :
    ∀ n, ContDiff ℝ ∞ (Function.uncurry (spatialJetField b n)) := by
  intro n
  induction n with
  | zero =>
      change ContDiff ℝ ∞ (Function.uncurry b)
      exact hb.smooth
  | succ n ih =>
      let F : ℝ → SpatialJetState n → SpatialJetState n := spatialJetField b n
      have hF : ContDiff ℝ ∞ (Function.uncurry F) := by
        simpa [F] using ih
      have hDbase : ContDiff ℝ ∞
          (fun p : ℝ × SpatialJetState n =>
            fderiv ℝ (Function.uncurry F) p) :=
        hF.fderiv_right (by norm_num)
      let D : ℝ × SpatialJetState n → SpatialJetState n →L[ℝ] SpatialJetState n :=
        fun p => (fderiv ℝ (Function.uncurry F) p).comp
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))
      have hD : ContDiff ℝ ∞ D := by
        have hcomp : ContDiff ℝ ∞
            (fun p : ℝ × SpatialJetState n =>
              (fderiv ℝ (Function.uncurry F) p).comp
                (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) :=
          hDbase.clm_comp contDiff_const
        exact hcomp
      have hstate : ContDiff ℝ ∞
          (fun q : ℝ × (SpatialJetState n ×
            (Fin 2 → SpatialJetState n)) => (q.1, q.2.1)) := by
        fun_prop
      have hbase : ContDiff ℝ ∞
          (fun q : ℝ × (SpatialJetState n ×
            (Fin 2 → SpatialJetState n)) => F q.1 q.2.1) :=
        hF.comp hstate
      have hDstate : ContDiff ℝ ∞
          (fun q : ℝ × (SpatialJetState n ×
            (Fin 2 → SpatialJetState n)) => D (q.1, q.2.1)) :=
        hD.comp hstate
      have htop : ContDiff ℝ ∞
          (fun q : ℝ × (SpatialJetState n × (Fin 2 → SpatialJetState n)) =>
            fun i => D (q.1, q.2.1) (q.2.2 i)) := by
        apply contDiff_pi.2
        intro i
        have hdirection : ContDiff ℝ ∞
            (fun q : ℝ × (SpatialJetState n × (Fin 2 → SpatialJetState n)) =>
              q.2.2 i) := by fun_prop
        exact hDstate.clm_apply hdirection
      change ContDiff ℝ ∞
        (fun q : ℝ × (SpatialJetState n × (Fin 2 → SpatialJetState n)) =>
          (F q.1 q.2.1, fun i => D (q.1, q.2.1) (q.2.2 i)))
      exact hbase.prodMk htop

/-- On a compact time window and a closed ball of jet states, one common
spatial Lipschitz constant controls the recursive jet field. The constant is
obtained by bounding the state derivative on the compact product. -/
theorem spatialJetField_lipschitzOnWith_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    (a d : ℝ) (z₀ : SpatialJetState n) (R : ℝ) :
    ∃ K : ℝ≥0, ∀ t, t ∈ Set.Icc a d →
      LipschitzOnWith K (spatialJetField b n t) (Metric.closedBall z₀ R) := by
  let F : ℝ × SpatialJetState n → SpatialJetState n :=
    Function.uncurry (spatialJetField b n)
  have hF : ContDiff ℝ ∞ F := spatialJetField_smooth hb n
  have hderiv : Continuous (fun p => fderiv ℝ F p) :=
    hF.continuous_fderiv (by norm_num)
  let region : Set (ℝ × SpatialJetState n) :=
    Set.Icc a d ×ˢ Metric.closedBall z₀ R
  have hcompact : IsCompact region := by
    exact isCompact_Icc.prod (isCompact_closedBall z₀ R)
  have hnorm : Continuous (fun p => ‖fderiv ℝ F p‖) :=
    continuous_norm.comp hderiv
  have hbounded : BddAbove ((fun p => ‖fderiv ℝ F p‖) '' region) :=
    hcompact.bddAbove_image hnorm.continuousOn
  let C : ℝ := max (sSup ((fun p => ‖fderiv ℝ F p‖) '' region)) 0
  have hC : 0 ≤ C := le_max_right _ _
  have hbound (t : ℝ) (ht : t ∈ Set.Icc a d) (z : SpatialJetState n)
      (hz : z ∈ Metric.closedBall z₀ R) :
      ‖fderiv ℝ F (t, z)‖ ≤ C := by
    apply le_trans (le_csSup hbounded ⟨(t, z), ⟨ht, hz⟩, rfl⟩)
    exact le_max_left _ _
  let K : ℝ≥0 := ⟨C, hC⟩
  refine ⟨K, ?_⟩
  intro t ht
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le (𝕜 := ℝ)
  · intro z hz
    have hslice : ContDiff ℝ ∞ (spatialJetField b n t) := by
      have hmap : ContDiff ℝ ∞ (fun z : SpatialJetState n => (t, z)) := by
        fun_prop
      exact hF.comp hmap
    exact (hslice.differentiable (by norm_num)) z
  · intro z hz
    have htotal : HasFDerivAt F (fderiv ℝ F (t, z)) (t, z) :=
      (hF.differentiable (by norm_num) (t, z)).hasFDerivAt
    have hpairRaw := htotal.comp z (hasFDerivAt_prodMk_right t z)
    have hpair : HasFDerivAt (spatialJetField b n t)
        ((fderiv ℝ F (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) z := by
      change HasFDerivAt (spatialJetField b n t)
        ((fderiv ℝ F (t, z)).comp
          (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))) z at hpairRaw
      exact hpairRaw
    rw [hpair.fderiv]
    have hnormcomp : ‖(fderiv ℝ F (t, z)).comp
        (ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n))‖ ≤
        ‖fderiv ℝ F (t, z)‖ := by
      calc
        _ ≤ ‖fderiv ℝ F (t, z)‖ *
            ‖ContinuousLinearMap.inr ℝ ℝ (SpatialJetState n)‖ :=
          (fderiv ℝ F (t, z)).opNorm_comp_le _
        _ = ‖fderiv ℝ F (t, z)‖ := by
          rw [ContinuousLinearMap.norm_inr, mul_one]
    exact_mod_cast (hnormcomp.trans (hbound t ht z hz))
  · exact convex_closedBall z₀ R

/-- Any two global solutions of a finite jet equation agree on a finite time
window when they start from the same state. The proof uses boundedness of each
continuous trajectory on the window, then the common ball Lipschitz estimate. -/
theorem spatialJetField_flow_unique_on_window
    {b : ℝ → Vec 2 → Vec 2} (hb : SmoothPeriodicField b) (n : ℕ)
    {Y Z : ℝ → SpatialJetState n → ℝ → SpatialJetState n}
    (hY : IsFlowOn (spatialJetField b n) Y)
    (hZ : IsFlowOn (spatialJetField b n) Z)
    (a d s : ℝ) (hs : s ∈ Set.Icc a d)
    (z : SpatialJetState n) :
    ∀ t, t ∈ Set.Icc a d → Y t z s = Z t z s := by
  have hYcont : Continuous (fun r => Y r z s) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hY.2 z s r).continuousAt
  have hZcont : Continuous (fun r => Z r z s) := by
    apply continuous_iff_continuousAt.mpr
    intro r
    exact (hZ.2 z s r).continuousAt
  let ycurve : Set.Icc a d → SpatialJetState n := fun r => Y r z s
  let zcurve : Set.Icc a d → SpatialJetState n := fun r => Z r z s
  have hycompact : IsCompact (Set.range ycurve) :=
    isCompact_range (hYcont.comp continuous_subtype_val)
  have hzcompact : IsCompact (Set.range zcurve) :=
    isCompact_range (hZcont.comp continuous_subtype_val)
  obtain ⟨R, hR⟩ := hycompact.isBounded.union hzcompact.isBounded |>.subset_closedBall z
  obtain ⟨K, hK⟩ := spatialJetField_lipschitzOnWith_on_window hb n a d z R
  have hmemY (r : ℝ) (hr : r ∈ Set.Icc a d) :
      Y r z s ∈ Metric.closedBall z R := by
    apply hR
    exact Or.inl ⟨⟨r, hr⟩, rfl⟩
  have hmemZ (r : ℝ) (hr : r ∈ Set.Icc a d) :
      Z r z s ∈ Metric.closedBall z R := by
    apply hR
    exact Or.inr ⟨⟨r, hr⟩, rfl⟩
  intro t ht
  by_cases hst : s ≤ t
  · have hright := ODE_solution_unique_of_mem_Icc_right
      (v := spatialJetField b n) (s := fun _ => Metric.closedBall z R)
      (K := K) (f := fun r => Y r z s) (g := fun r => Z r z s)
      (a := s) (b := t)
      (fun r hr => hK r ⟨le_trans hs.1 hr.1,
        le_trans (le_of_lt hr.2) ht.2⟩)
      (hYcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hY.2 z s r).hasDerivWithinAt)
      (fun r hr => hmemY r ⟨le_trans hs.1 hr.1,
        le_trans (le_of_lt hr.2) ht.2⟩)
      (hZcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hZ.2 z s r).hasDerivWithinAt)
      (fun r hr => hmemZ r ⟨le_trans hs.1 hr.1,
        le_trans (le_of_lt hr.2) ht.2⟩)
      (by rw [hY.1 z s, hZ.1 z s])
    exact hright ⟨hst, le_rfl⟩
  · have hts : t ≤ s := le_of_not_ge hst
    have hleft := ODE_solution_unique_of_mem_Icc_left
      (v := spatialJetField b n) (s := fun _ => Metric.closedBall z R)
      (K := K) (f := fun r => Y r z s) (g := fun r => Z r z s)
      (a := t) (b := s)
      (fun r hr => hK r ⟨le_trans ht.1 (le_of_lt hr.1),
        le_trans hr.2 hs.2⟩)
      (hYcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hY.2 z s r).hasDerivWithinAt)
      (fun r hr => hmemY r ⟨le_trans ht.1 (le_of_lt hr.1),
        le_trans hr.2 hs.2⟩)
      (hZcont.continuousOn.mono (Set.subset_univ _))
      (fun r hr => (hZ.2 z s r).hasDerivWithinAt)
      (fun r hr => hmemZ r ⟨le_trans ht.1 (le_of_lt hr.1),
        le_trans hr.2 hs.2⟩)
      (by rw [hY.1 z s, hZ.1 z s])
    exact hleft ⟨le_rfl, hts⟩

/-- The first recursive jet field agrees with the established position and
Jacobian augmented field. -/
theorem spatialJetField_one_eq_firstJetField
    {b : ℝ → Vec 2 → Vec 2} :
    spatialJetField b 1 = firstJetField b := by
  funext t z
  rcases z with ⟨x, columns⟩
  apply Prod.ext
  · rfl
  · funext i
    change (fderiv ℝ (Function.uncurry b) (t, x)).comp
        (ContinuousLinearMap.inr ℝ ℝ (Vec 2)) (columns i) =
      jointSpatialFDeriv b t x (columns i)
    rfl

end

end AVenhance.Infra.Flow
