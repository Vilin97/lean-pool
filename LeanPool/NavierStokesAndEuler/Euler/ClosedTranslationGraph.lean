/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PressureSpatialRegularity
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Closed graphs of the genuine strong cylinder translation derivatives. -/

@[expose] public section


noncomputable section

namespace EulerClosedTranslationGraph

open MeasureTheory EulerLiftedGradientSpace EulerPressureSpatialRegularity
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

omit [Fact (0 < period)] in
/-- A covering-space direction gives an additive one-parameter cylinder translation. -/
theorem translationPath_add (a : LiftTangent) (s t : ℝ) :
    translationPath period a (s + t) = translationPath period a s + translationPath period a t := by
  ext <;> simp [translationPath, coveringMap, add_smul]

/-- Strong differentiation of a translation orbit at zero determines its derivative everywhere. -/
theorem translation_hasDerivAt_all (a : LiftTangent) (f g : LiftL2 period)
    (h : HasDerivAt (fun s => translation period (translationPath period a s) f) g 0) (t : ℝ) :
    HasDerivAt (fun s => translation period (translationPath period a s) f)
      (translation period (translationPath period a t) g) t := by
  have hshift : HasDerivAt
      (fun s => translation period (translationPath period a t)
        (translation period (translationPath period a s) f))
      (translation period (translationPath period a t) g) 0 :=
    (translation period (translationPath period a
        t)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt 0 h
  have hd := hshift.scomp_of_eq t ((hasDerivAt_id t).sub_const t) (by simp)
  have hshape : (fun s => translation period (translationPath period a t)
      (translation period (translationPath period a (s - t)) f)) =
      fun s => translation period (translationPath period a s) f := by
    funext s
    rw [translation_add, ← translationPath_add]
    rw [show t + (s - t) = s by ring]
  simpa only [Function.comp_def, id_eq, hshape, one_smul] using hd

/-- Convergence of L² fields gives uniform convergence of their entire isometric translation orbits.
-/
theorem translation_orbits_tendstoUniformly {ι : Type*} {l : Filter ι}
    (a : LiftTangent) (f : ι → LiftL2 period) (g : LiftL2 period)
    (hf : Filter.Tendsto f l (𝓝 g)) :
    TendstoUniformly (fun n t => translation period (translationPath period a t) (f n))
      (fun t => translation period (translationPath period a t) g) l := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have he := hf.eventually (Metric.ball_mem_nhds g hε)
  filter_upwards [he] with n hn t
  rw [(translation period (translationPath period a t)).dist_map]
  simpa only [Metric.mem_ball, dist_comm] using hn

/-- The graph of one genuine strong L² translation derivative, as a linear subspace. -/
def translationDerivativeGraph (a : LiftTangent) : Submodule ℝ (LiftL2 period × LiftL2 period) where
  carrier := {p | HasDerivAt (fun t => translation period (translationPath period a t) p.1) p.2 0}
  zero_mem' := by
    change HasDerivAt (fun t => translation period (translationPath period a t) 0) 0 0
    simpa only [map_zero] using hasDerivAt_const (0 : ℝ) (0 : LiftL2 period)
  add_mem' := by
    intro p q hp hq
    change HasDerivAt (fun t => translation period (translationPath period a t) (p.1 + q.1)) (p.2 +
        q.2) 0
    simpa only [map_add] using hp.fun_add hq
  smul_mem' := by
    intro r p hp
    change HasDerivAt (fun t => translation period (translationPath period a t) (r • p.1)) (r •
        p.2) 0
    simpa only [map_smul, Pi.smul_def] using hp.const_smul r

/-- The strong translation derivative is a closed operator on the actual cylinder L² space. -/
theorem translationDerivativeGraph_closed (a : LiftTangent) :
    IsClosed (translationDerivativeGraph period a : Set (LiftL2 period × LiftL2 period)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro v p hv hvp
  have hfst : Filter.Tendsto (fun n => (v n).1) Filter.atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hvp
  have hsnd : Filter.Tendsto (fun n => (v n).2) Filter.atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hvp
  have hder : ∀ᶠ n : ℕ in Filter.atTop, ∀ t : ℝ,
      HasDerivAt (fun s => translation period (translationPath period a s) (v n).1)
        (translation period (translationPath period a t) (v n).2) t :=
    Filter.Eventually.of_forall (fun n t => translation_hasDerivAt_all period a (v n).1 (v n).2 (hv
        n) t)
  have hlim := hasDerivAt_of_tendstoUniformly
    (translation_orbits_tendstoUniformly period a (fun n => (v n).2) p.2 hsnd) hder
    (fun t => (translation period (translationPath period a
        t)).continuous.continuousAt.tendsto.comp hfst) 0
  change HasDerivAt (fun t => translation period (translationPath period a t) p.1) p.2 0
  simpa only [translationPath_zero, translation_zero] using hlim

end EulerClosedTranslationGraph
