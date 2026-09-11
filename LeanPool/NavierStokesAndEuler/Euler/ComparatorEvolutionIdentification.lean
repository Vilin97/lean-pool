/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SolutionDefinitions
import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerUniqueness
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
public import LeanPool.NavierStokesAndEuler.Euler.OrdinaryEulerDifference

/-!
# Identification after local regularity recovery

The only analytic input of this module is a local conversion of a classical
Comparator solution with compact initial vorticity into an ordinary smooth
Euler evolution. Restarting that conversion at times of agreement, ordinary
Euler uniqueness and continuity identify the entire maximal interval.
-/

section

/-! Restriction of an ordinary Euler evolution to a translated closed interval. -/

@[expose] public section

noncomputable section

namespace EulerOrdinarySobolev

open Set Filter EulerSmoothLimit
open scoped Topology

/-- Embed the shifted time interval into the original evolution interval. -/
def shiftTimeMap (S T a : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) S) where
  toFun t := ⟨a + t, add_nonneg ha t.property.1,
    (add_le_add le_rfl t.property.2).trans haT⟩
  continuous_toFun := (continuous_subtype_val.const_add a).subtype_mk _

@[simp] theorem shiftTimeMap_val (S T a : ℝ) (ha : 0 ≤ a) (haT : a + T ≤ S)
    (t : Icc (0 : ℝ) T) : ((shiftTimeMap S T a ha haT t) : ℝ) = a + t := rfl

namespace Evolution

variable {S : ℝ} {hS : 0 ≤ S}

/-- Restart an evolution at time `a`, retaining its next `T` units of time. -/
def shiftTime (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) : Evolution T hT where
  velocity t := U.velocity (shiftTimeMap S T a ha haT t)
  pressureForce t := U.pressureForce (shiftTimeMap S T a ha haT t)
  velocity_continuous n :=
    (U.velocity_continuous n).comp (shiftTimeMap S T a ha haT).continuous
  pressure_continuous n :=
    (U.pressure_continuous n).comp (shiftTimeMap S T a ha haT).continuous
  solenoidal t := U.solenoidal (shiftTimeMap S T a ha haT t)
  gradient t := U.gradient (shiftTimeMap S T a ha haT t)
  time_law t ht x := by
    have hat : a + t ∈ Ioo (0 : ℝ) S :=
      ⟨add_pos_of_nonneg_of_pos ha ht.1,
        (add_lt_add_of_le_of_lt le_rfl ht.2).trans_le haT⟩
    have hd := (U.time_law (a + t) hat x).comp_const_add a t
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
    have hrT : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
    have har : a + r ∈ Icc (0 : ℝ) S :=
      ⟨add_nonneg ha hr.1.le, (add_le_add le_rfl hr.2.le).trans haT⟩
    rw [projIcc_of_mem hT hrT, projIcc_of_mem hS har]
    rfl

@[simp] theorem shiftTime_velocity (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) (t : Icc (0 : ℝ) T) :
    (U.shiftTime a ha T hT haT).velocity t =
      U.velocity (shiftTimeMap S T a ha haT t) := rfl

@[simp] theorem shiftTime_pressureForce (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) (t : Icc (0 : ℝ) T) :
    (U.shiftTime a ha T hT haT).pressureForce t =
      U.pressureForce (shiftTimeMap S T a ha haT t) := rfl

theorem shiftTime_initial (U : Evolution S hS) (a : ℝ) (ha : 0 ≤ a)
    (T : ℝ) (hT : 0 ≤ T) (haT : a + T ≤ S) :
    (U.shiftTime a ha T hT haT).velocity ⟨0, le_rfl, hT⟩ =
      U.velocity ⟨a, ha, (le_add_of_nonneg_right hT).trans haT⟩ := by
  rw [shiftTime_velocity]
  congr 1
  apply Subtype.ext
  exact add_zero a

end Evolution
end EulerOrdinarySobolev

end
end

end

section

/-! Time translation preserves the independent whole-space Euler class,
including its one-sided initial-time equation and uniform energy bound. -/

@[expose] public section

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Euler.EulerExistenceAndSmoothnessR3

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

variable {u₀ : ℝ³ → ℝ³} {v : ℝ³ → ℝ → ℝ³} {p : ℝ³ → ℝ → ℝ}

theorem shiftTime (h : EulerExistenceAndSmoothnessR3 u₀ v p)
    (a : ℝ) (ha : 0 ≤ a) :
    EulerExistenceAndSmoothnessR3 (v · a)
      (fun x t => v x (a + t)) (fun x t => p x (a + t)) := by
  have hv (x : ℝ³) : ContDiffOn ℝ ∞ (v x ·) (Ici 0) :=
    h.velocity_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun r hr => ⟨mem_univ x, hr⟩)
  refine {
    euler := ?_
    div_free := fun x t ht => h.div_free x (a + t) (add_nonneg ha ht)
    initial_condition := fun x => by simp
    velocity_smooth := ?_
    pressure_smooth := ?_
    integrable := fun t ht => h.integrable (a + t) (add_nonneg ha ht)
    globally_bounded_energy := ?_ }
  · intro x t ht
    have hd := ((hv x).differentiableOn (by simp) (a + t)
      (add_nonneg ha ht)).hasDerivWithinAt
    have hi : HasDerivWithinAt (fun r : ℝ => a + r) 1 (Ici 0) t := by
      simpa only [zero_add, id_eq] using ((hasDerivAt_id t).const_add a).hasDerivWithinAt
    have hc := hd.scomp t hi (fun r hr => add_nonneg ha hr)
    have he : derivWithin (fun r => v x (a + r)) (Ici 0) t =
        derivWithin (v x ·) (Ici 0) (a + t) := by
      simpa only [Function.comp_def, one_smul] using
        hc.derivWithin (uniqueDiffOn_Ici 0 t ht)
    rw [he]
    exact h.euler x (a + t) (add_nonneg ha ht)
  · exact h.velocity_smooth.comp
      (contDiff_fst.prodMk (contDiff_const.add contDiff_snd)).contDiffOn
      (fun z hz => ⟨mem_univ z.1, add_nonneg ha hz.2⟩)
  · exact h.pressure_smooth.comp
      (contDiff_fst.prodMk (contDiff_const.add contDiff_snd)).contDiffOn
      (fun z hz => ⟨mem_univ z.1, add_nonneg ha hz.2⟩)
  · obtain ⟨E, hE⟩ := h.globally_bounded_energy
    exact ⟨E, fun t ht => hE (a + t) (add_nonneg ha ht)⟩

end Euler.EulerExistenceAndSmoothnessR3

end
end

end

@[expose] public section

noncomputable section

open Set Filter MeasureTheory EulerSmoothLimit EulerLpTranslation
  EulerLpTranslation.SmoothL2Field EulerOrdinarySobolev EulerVectorCalculus EulerMeanCutoffCurl
open scoped ContDiff Topology

namespace Euler.ComparatorBridge

variable {A : SmoothL2Field Space}
  {v : Space → ℝ → Space} {p : Space → ℝ → ℝ}

/-- Local recovery is needed only at compact-vorticity slices. It asks for
an actual ordinary evolution representing the given velocity, so it contains
no comparison or uniqueness conclusion. -/
def HasLocalEvolutionAtCompactCurl (v : Space → ℝ → Space) : Prop :=
  ∀ a : ℝ, 0 ≤ a → HasCompactSupport (vectorCurl (v · a)) →
    ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ U : Evolution δ hδ.le,
      ∀ t : Icc (0 : ℝ) δ, (U.velocity t).field = (v · (a + (t : ℝ)))

/-- The reusable analytic conversion obligation, before any uniqueness
argument: compact initial vorticity gives a short ordinary realization. -/
def CompactCurlLocalUpgrade : Prop :=
  ∀ (u₀ : Space → Space) (v : Space → ℝ → Space) (p : Space → ℝ → ℝ),
    EulerExistenceAndSmoothnessR3 u₀ v p → HasCompactSupport (vectorCurl u₀) →
      ∃ δ : ℝ, ∃ hδ : 0 < δ, ∃ U : Evolution δ hδ.le,
        ∀ t : Icc (0 : ℝ) δ, (U.velocity t).field = (v · (t : ℝ))

theorem hasLocalEvolutionAtCompactCurl_of_upgrade
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (hupgrade : CompactCurlLocalUpgrade) : HasLocalEvolutionAtCompactCurl v := by
  intro a ha hc
  exact hupgrade (v · a) (fun x t => v x (a + t)) (fun x t => p x (a + t))
    (h.shiftTime a ha) hc

/-- A classical field locally recoverable as an ordinary evolution agrees
with every ordinary evolution from the same data whose vorticity stays compact. -/
theorem evolution_field_eq_of_local_evolution
    {S : ℝ} {hS : 0 ≤ S} (U : Evolution S hS)
    (h : EulerExistenceAndSmoothnessR3 A.field v p)
    (hU : U.velocity ⟨0, le_rfl, hS⟩ = A)
    (hcompact : ∀ t, HasCompactSupport (vectorCurl (U.velocity t).field))
    (hlocal : HasLocalEvolutionAtCompactCurl v) :
    ∀ t : Icc (0 : ℝ) S, (U.velocity t).field = (v · (t : ℝ)) := by
  let s : Set ℝ := {r | ∀ x, (U.velocity (projIcc 0 S hS r)).field x =
    v x (projIcc 0 S hS r)}
  have hcU (x : Space) : Continuous (fun r : ℝ =>
      (U.velocity (projIcc 0 S hS r)).field x) := by
    have hc := (EulerMeanSobolevBoundedField.continuous_finiteField U.velocity
      U.velocity_continuous).eval (continuous_const (y := x))
    simpa only [EulerMeanSobolevBoundedField.finiteField_apply, Function.comp_def] using
      hc.comp (continuous_projIcc (a := (0 : ℝ)) (b := S) (h := hS))
  have hcv (x : Space) : Continuous (fun r : ℝ => v x (projIcc 0 S hS r)) := by
    have hc : Continuous (fun r : Icc (0 : ℝ) S => v x r) :=
      h.velocity_smooth.continuousOn.comp_continuous
        (continuous_const.prodMk continuous_subtype_val)
        (fun r => ⟨mem_univ x, r.property.1⟩)
    exact hc.comp continuous_projIcc
  have hs : IsClosed s := by
    change IsClosed {r | ∀ x, (U.velocity (projIcc 0 S hS r)).field x =
      v x (projIcc 0 S hS r)}
    simpa only [ofPred_forall] using
      (isClosed_iInter fun x => isClosed_eq (hcU x) (hcv x))
  have hzero : (0 : ℝ) ∈ s := by
    intro x
    rw [projIcc_of_mem hS ⟨le_rfl, hS⟩]
    change (U.velocity ⟨0, le_rfl, hS⟩).field x = v x 0
    rw [hU]
    exact (h.initial_condition x).symm
  have hright : ∀ a ∈ s ∩ Ico 0 S, ∀ b ∈ Ioi a, (s ∩ Ioc a b).Nonempty := by
    intro a ha b hb
    have haS : a ∈ Icc (0 : ℝ) S := ⟨ha.2.1, ha.2.2.le⟩
    have hmatch : (U.velocity ⟨a, haS⟩).field = (v · a) := by
      funext x
      have hx := ha.1 x
      simpa only [projIcc_of_mem hS haS] using hx
    have hcurl : HasCompactSupport (vectorCurl (v · a)) := by
      rw [← hmatch]
      exact hcompact _
    obtain ⟨δ, hδ, W, hW⟩ := hlocal a ha.2.1 hcurl
    let d := min δ (min (S - a) (b - a))
    have hd : 0 < d := lt_min hδ (lt_min (sub_pos.mpr ha.2.2) (sub_pos.mpr hb))
    have hdδ : d ≤ δ := min_le_left _ _
    have had : a + d ≤ S := by
      have hh : d ≤ S - a := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hab : a + d ≤ b := by
      have hh : d ≤ b - a := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    let R := U.shiftTime a ha.2.1 d hd.le had
    let Q := W.restrictTime d hd.le hdδ
    have hinit : R.velocity ⟨0, le_rfl, hd.le⟩ = Q.velocity ⟨0, le_rfl, hd.le⟩ := by
      apply field_ext
      calc
        (R.velocity ⟨0, le_rfl, hd.le⟩).field = (v · a) := by
          simpa only [R, Evolution.shiftTime_initial] using hmatch
        _ = (Q.velocity ⟨0, le_rfl, hd.le⟩).field := by
          simpa only [Q, Evolution.restrictTime_initial, add_zero] using
            (hW ⟨0, le_rfl, hδ.le⟩).symm
    have heq := Q.velocity_eq_of_initial R (congrArg SmoothL2Field.toLp hinit)
      ⟨d, hd.le, le_rfl⟩
    refine ⟨a + d, ?_, by linarith, hab⟩
    intro x
    have hmem : a + d ∈ Icc (0 : ℝ) S := ⟨add_nonneg ha.2.1 hd.le, had⟩
    rw [projIcc_of_mem hS hmem]
    calc
      (U.velocity ⟨a + d, hmem⟩).field x = (R.velocity ⟨d, hd.le, le_rfl⟩).field x := rfl
      _ = (Q.velocity ⟨d, hd.le, le_rfl⟩).field x := congrArg (fun B => B.field x) heq
      _ = v x (a + d) := congrFun (hW ⟨d, hd.le, hdδ⟩) x
  have hall : Icc (0 : ℝ) S ⊆ s :=
    (hs.inter isClosed_Icc).Icc_subset_of_forall_exists_gt hzero hright
  intro t
  funext x
  have hx := hall t.property x
  simpa only [projIcc_of_mem hS t.property] using hx

end Euler.ComparatorBridge
