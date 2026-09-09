/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SmoothL2Gevrey
import LeanPool.NavierStokesAndEuler.Euler.GevreyComposition
import LeanPool.NavierStokesAndEuler.Euler.GevreyCompositionLp
import LeanPool.NavierStokesAndEuler.Euler.GevreyFixedShift
import LeanPool.NavierStokesAndEuler.Euler.GevreyGeneratingDerivatives
public import LeanPool.NavierStokesAndEuler.Euler.GevreyProductLp
import LeanPool.NavierStokesAndEuler.Euler.OperatorGevreyCalculus
import LeanPool.NavierStokesAndEuler.ForMathlib.SmoothnessOrder
import Mathlib.Algebra.Order.Star.Real

/-! Quantitative calculus for concrete smooth L² fields, with the outer
factor in L² and the inner coordinate change preserving volume. -/

@[expose] public section


noncomputable section

namespace EulerGevrey

open EulerOperatorGevreyCalculus
open scoped ContDiff

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Has sup bound, given by `∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*R^n*(n.factorial : ℝ)^2`. -/
def HasSupBound (f : E → V) (C R : ℝ) : Prop :=
  ∀ n x, ‖iteratedFDeriv ℝ n f x‖ ≤ C*R^n*(n.factorial : ℝ)^2

theorem HasSupBound.mono {f : E → V} {C R D S : ℝ}
    (h : HasSupBound f C R) (hC : 0 ≤ C) (hR : 0 ≤ R) (hCD : C ≤ D) (hRS : R ≤ S) :
    HasSupBound f D S := by
  intro n x
  exact (h n x).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul hCD (pow_le_pow_left₀ hR hRS n) (pow_nonneg hR n) (hC.trans hCD)) (sq_nonneg _))

theorem HasSupBound.derivative {f : E → V} {C R : ℝ}
    (h : HasSupBound f C R) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    HasSupBound (fderiv ℝ f) (C*R) (4*R) := by
  intro n x
  rw [norm_iteratedFDeriv_fderiv]
  apply (h (n+1) x).trans
  simpa only [majorant,Nat.add_zero,mul_assoc] using
    mul_le_mul_of_nonneg_left (majorant_one_le_radius_four R hR n) hC

theorem HasSupBound.comp {f : E → E} {g : E → V} {C B R S : ℝ}
    (hg : HasSupBound g C S) (hf : ContDiff ℝ ∞ f) (hgsm : ContDiff ℝ ∞ g)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hfb : ∀ n, 0 < n → ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2) :
    HasSupBound (g ∘ f) C (R*(B*S+2)) :=
  EulerGevreyComposition.norm_iteratedFDeriv_comp_gevrey f g hf hgsm C B R S hC hB hR hS hg hfb

theorem HasSupBound.apply {f : E → V →L[ℝ] W} {g : E → V} {B C R : ℝ}
    (hf : HasSupBound f B R) (hg : HasSupBound g C R)
    (hfsm : ContDiff ℝ ∞ f) (hgsm : ContDiff ℝ ∞ g)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    HasSupBound (fun x => f x (g x)) (3*B*C) R := by
  intro n x
  have h := clm_apply_bound f g hfsm hgsm R B C hR hB hC 0 0
    (fun j y => by simpa only [majorant,Nat.add_zero,mul_assoc] using hf j y)
    (fun j y => by simpa only [majorant,Nat.add_zero,mul_assoc] using hg j y) n x
  simpa only [majorant,Nat.add_zero,mul_assoc] using h

theorem positive_id_add_bound (f : E → E) (hf : ContDiff ℝ ∞ f) (B R : ℝ)
    (hB : 0 ≤ B) (hR : 0 ≤ R) (hb : HasSupBound f B R)
    (n : ℕ) (hn : 0 < n) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y => y+f y) x‖ ≤ (1+B)*(1+R)^n*(n.factorial : ℝ)^2 := by
  rw [show (fun y => y+f y) = id+f from rfl,
    iteratedFDeriv_add_apply contDiffAt_id (hf.contDiffAt.of_le (by simp))]
  have hi : ‖iteratedFDeriv ℝ n (id : E → E) x‖ ≤ 1 := by
    have h := EulerGevreyGeneratingDerivatives.norm_iteratedFDeriv_id_le n hn x
    split_ifs at h <;> linarith
  have hfact : (1 : ℝ) ≤ n.factorial := by exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos n)
  have hweight : (1 : ℝ) ≤ (1+R)^n*(n.factorial : ℝ)^2 := by
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (by nlinarith)
  have hdisp : ‖iteratedFDeriv ℝ n f x‖ ≤ B*(1+R)^n*(n.factorial : ℝ)^2 :=
    (hb.mono hB hR le_rfl (by linarith)) n x
  exact (norm_add_le _ _).trans ((add_le_add (hi.trans hweight) hdisp).trans_eq (by ring))

end EulerGevrey

namespace EulerLpTranslation.SmoothL2Field

open MeasureTheory EulerSmoothLimit EulerGevrey
open scoped ContDiff

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

variable (f : Space → Space) (hf : ContDiff ℝ ∞ f) (hmp : MeasurePreserving f volume volume)
  (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
  (hfb : ∀ n, 0 < n → ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ B * R ^ n * (n.factorial : ℝ) ^ 2)
  (A : SmoothL2Field V) (C S : ℝ) (hC : 0 ≤ C) (hS : 0 ≤ S) (ha : A.HasJetBound C S)

include hf hmp hB hR hfb hC hS ha in
theorem compose_memLp_and_bound (n : ℕ) :
    MemLp (iteratedFDeriv ℝ n (A.field ∘ f)) 2 volume ∧
      (eLpNorm (iteratedFDeriv ℝ n (A.field ∘ f)) 2 volume).toReal ≤
        C*(R*(B*S+2))^n*(n.factorial : ℝ)^2 :=
  EulerGevreyCompositionLp.composition_memLp_and_bound volume f A.field hf A.smooth hmp n
    (((A.smooth.comp hf).continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable)
    C B R S hC hB hR hS (fun j _ => A.integrable j)
    (fun j _ => by simpa only [← norm_jetLp] using ha j) (fun j hj _ => hfb j hj)

/-- Compose field, bundling `field`, `smooth`, `integrable`. -/
def composeField : SmoothL2Field V where
  field := A.field ∘ f
  smooth := A.smooth.comp hf
  integrable n := (compose_memLp_and_bound f hf hmp B R hB hR hfb A C S hC hS ha n).1

theorem composeField_bound :
    (composeField f hf hmp B R hB hR hfb A C S hC hS ha).HasJetBound C (R*(B*S+2)) := by
  intro n
  rw [norm_jetLp]
  exact (compose_memLp_and_bound f hf hmp B R hB hR hfb A C S hC hS ha n).2

omit f hf hmp B R hB hR hfb A C S hC hS ha in
/-- Product field, bundling `field`, `smooth`, `integrable`. -/
def productField (g : Space → V →L[ℝ] W) (hg : ContDiff ℝ ∞ g) (A : SmoothL2Field V)
    (B C R : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hgb : HasSupBound g B R) (hab : A.HasJetBound C R) : SmoothL2Field W where
  field x := g x (A.field x)
  smooth := hg.clm_apply A.smooth
  integrable n := (EulerGevreyProductLp.clm_apply_memLp_and_bound volume id g A.field hg A.smooth n
    (((hg.clm_apply A.smooth).continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable)
    R B C hR hB hC 0 0
    (fun j _ x => by simpa only [id_eq,majorant,Nat.add_zero,mul_assoc] using hgb j x)
    (fun j _ => A.integrable j)
    (fun j _ => by simpa only [id_eq,← norm_jetLp,majorant,Nat.add_zero,mul_assoc] using hab j)).1

omit f hf hmp B R hB hR hfb A C S hC hS ha in
theorem productField_bound (g : Space → V →L[ℝ] W) (hg : ContDiff ℝ ∞ g) (A : SmoothL2Field V)
    (B C R : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hgb : HasSupBound g B R) (hab : A.HasJetBound C R) :
    (productField g hg A B C R hB hC hR hgb hab).HasJetBound (3*B*C) R := by
  intro n
  have h := (EulerGevreyProductLp.clm_apply_memLp_and_bound volume id g A.field hg A.smooth n
    (((hg.clm_apply A.smooth).continuous_iteratedFDeriv (m := n) (by simp)).aestronglyMeasurable)
    R B C hR hB hC 0 0
    (fun j _ x => by simpa only [id_eq,majorant,Nat.add_zero,mul_assoc] using hgb j x)
    (fun j _ => A.integrable j)
    (fun j _ => by simpa only [id_eq,← norm_jetLp,majorant,Nat.add_zero,mul_assoc] using hab j)).2
  simpa only [id_eq,norm_jetLp,productField,majorant,Nat.add_zero,mul_assoc] using h

end EulerLpTranslation.SmoothL2Field
