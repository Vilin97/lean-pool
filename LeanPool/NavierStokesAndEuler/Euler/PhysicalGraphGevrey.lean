/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderGraphGevrey
public import LeanPool.NavierStokesAndEuler.Euler.PhysicalL2Scaling
public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldJets
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-! Concrete smooth L² fields obtained from the periodic cover, its
oscillating graph, a linear projection and the physical label dilation.
The resulting bounds apply to the literal derivatives of those fields. -/

@[expose] public section


noncomputable section

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory Filter EulerSmoothLimit EulerPhysicalL2Scaling
open scoped ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem norm_jetLp_map_le (L : V →L[ℝ] W) (A : SmoothL2Field V) (n : ℕ) :
    ‖(mapField L A).jetLp n‖ ≤ ‖L‖*‖A.jetLp n‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(mapField L A).jetLp_ae n,A.jetLp_ae n] with x hx hy
  rw [hx,hy]
  exact L.norm_iteratedFDeriv_comp_left A.smooth.contDiffAt (by simp)

theorem HasJetBound.map_contracting {A : SmoothL2Field V} {C R : ℝ}
    (h : A.HasJetBound C R) (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) :
    (mapField L A).HasJetBound C R := by
  intro n
  exact (norm_jetLp_map_le L A n).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul] using h n))

/-- Scale field, bundling `field`, `smooth`, `integrable`. -/
def scaleField (ell : ℝ) (hell : 0 < ell) (A : SmoothL2Field V) : SmoothL2Field V where
  field := scale ell A.field
  smooth := scale_contDiff ell A.field A.smooth
  integrable n := scale_jet_memLp ell hell A.field A.smooth n (A.integrable n)

@[simp] theorem scaleField_apply (ell : ℝ) (hell : 0 < ell) (A : SmoothL2Field V) (x : Space) :
    (scaleField ell hell A).field x = ell • A.field (ell⁻¹ • x) := rfl

theorem norm_jetLp_scale_le (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (A : SmoothL2Field V) (n : ℕ) :
    ‖(scaleField ell hell A).jetLp n‖ ≤ (ell⁻¹)^n*‖A.jetLp n‖ := by
  rw [norm_jetLp,norm_jetLp,
    toReal_eLpNorm ((scaleField ell hell A).integrable n).aestronglyMeasurable,
    toReal_eLpNorm (A.integrable n).aestronglyMeasurable]
  exact lpNorm_scale_jet_le ell hell hell1 A.field A.smooth n (A.integrable n)

theorem HasJetBound.scale {A : SmoothL2Field V} {C R : ℝ}
    (h : A.HasJetBound C R) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    (scaleField ell hell A).HasJetBound C (ell⁻¹*R) := by
  intro n
  exact (norm_jetLp_scale_le ell hell hell1 A n).trans
    ((mul_le_mul_of_nonneg_left (h n) (pow_nonneg (inv_nonneg.mpr hell.le) n)).trans_eq
      (by rw [mul_pow]; ring))

theorem scale_sup_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (f : Space → V) (hf : ContDiff ℝ ∞ f) (B R : ℝ)
    (hb : ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (x : Space) :
    ‖iteratedFDeriv ℝ n (scale ell f) x‖ ≤ B*(ell⁻¹*R)^n*(n.factorial : ℝ)^2 := by
  rw [iteratedFDeriv_scale ell f hf,norm_smul,Real.norm_of_nonneg (by
      positivity : 0 ≤ ell*(ell⁻¹)^n)]
  have hscale : ell*(ell⁻¹)^n ≤ (ell⁻¹)^n := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hell1 (pow_nonneg (inv_nonneg.mpr hell.le) n)
  calc
    _ ≤ (ell⁻¹)^n*‖iteratedFDeriv ℝ n f (ell⁻¹ • x)‖ :=
      mul_le_mul_of_nonneg_right hscale (norm_nonneg _)
    _ ≤ (ell⁻¹)^n*(B*R^n*(n.factorial : ℝ)^2) :=
      mul_le_mul_of_nonneg_left (hb n _) (pow_nonneg (inv_nonneg.mpr hell.le) n)
    _ = _ := by rw [mul_pow]; ring

end EulerLpTranslation.SmoothL2Field

namespace EulerPhysicalGraphGevrey

open Set MeasureTheory EulerLiftedGradientSpace EulerCylinderCoverDescent
  EulerGraphPullback EulerCylinderGraphGevrey EulerLpTranslation EulerLpTranslation.SmoothL2Field
open scoped ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  (P : ℝ) [Fact (0 < P)] (f : LiftTangent → V)
  (hperiod : ∀ (c : AddSubgroup.zmultiples P) z, f (z.1, (c : ℝ) + z.2) = f z)
  (hf : ContDiff ℝ ∞ f) (k : ℝ) (m : Vector3) (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
  (hLp : ∀ n, MemLp (fun q => jetSeries P f q n) 2 (liftMeasure P))
  (hn : ∀ n, (eLpNorm (fun q => jetSeries P f q n) 2 (liftMeasure P)).toReal ≤
    C * R ^ n * (n.factorial : ℝ) ^ 2)

/-- Graph field, bundling `field`, `smooth`, `integrable`. -/
def graphField : SmoothL2Field V where
  field := f ∘ graphMap k m
  smooth := hf.comp (graphMap k m).contDiff
  integrable n := (graph_Lp_bound P f hperiod hf k m C R hC hR hLp hn n).1

theorem graphField_bound :
    (graphField P f hperiod hf k m C R hC hR hLp hn).HasJetBound
      (Real.sqrt (2/P+2*P)*C*(1+R)) (4*R*graphFactor k m) := by
  intro n
  rw [norm_jetLp]
  exact (graph_Lp_bound P f hperiod hf k m C R hC hR hLp hn n).2

/-- Physical field, given by `scaleField ell hell (mapField L (graphField P f hperiod hf k m C R
hC hR hLp hn))`. -/
def physicalField (ell : ℝ) (hell : 0 < ell) (L : V →L[ℝ] W) : SmoothL2Field W :=
  scaleField ell hell (mapField L (graphField P f hperiod hf k m C R hC hR hLp hn))

@[simp] theorem physicalField_apply (ell : ℝ) (hell : 0 < ell) (L : V →L[ℝ] W) (x : Vector3) :
    (physicalField P f hperiod hf k m C R hC hR hLp hn ell hell L).field x =
      ell • L (f (graphMap k m (ell⁻¹ • x))) := rfl

theorem physicalField_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) :
    (physicalField P f hperiod hf k m C R hC hR hLp hn ell hell L).HasJetBound
      (Real.sqrt (2/P+2*P)*C*(1+R)) (ell⁻¹*(4*R*graphFactor k m)) :=
  ((graphField_bound P f hperiod hf k m C R hC hR hLp hn).map_contracting L hL).scale
    ell hell hell1

theorem physicalField_sup_bound (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (L : V →L[ℝ] W) (hL : ‖L‖ ≤ 1) (B S : ℝ)
    (hb : ∀ n z, ‖iteratedFDeriv ℝ n f z‖ ≤ B * S ^ n * (n.factorial : ℝ) ^ 2)
    (n : ℕ) (x : Vector3) :
    ‖iteratedFDeriv ℝ n (physicalField P f hperiod hf k m C R hC hR hLp hn ell hell L).field x‖ ≤
      B*(ell⁻¹*(S*graphFactor k m))^n*(n.factorial : ℝ)^2 := by
  apply scale_sup_bound ell hell hell1 (L ∘ (f ∘ graphMap k m))
    (L.contDiff.comp (hf.comp (graphMap k m).contDiff)) B (S*graphFactor k m)
  intro j y
  have hp := L.norm_iteratedFDeriv_comp_left ((hf.comp (graphMap k m).contDiff).contDiffAt (x := y))
    (by simp : (j : WithTop ℕ∞) ≤ ∞)
  exact hp.trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul] using graph_sup_bound f hf k m B S hb j y))

end EulerPhysicalGraphGevrey
