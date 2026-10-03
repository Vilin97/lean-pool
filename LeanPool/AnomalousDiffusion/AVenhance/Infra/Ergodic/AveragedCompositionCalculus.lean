/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Formula
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.Resummation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ergodic.FlowAverages

/-! Coordinate expansions for averaged Faà di Bruno estimates. Positions are
labelled even when coordinate directions repeat. -/

@[expose] public section

noncomputable section
open scoped ContDiff
open MeasureTheory Homogenization
open AVenhance.FaaDiBruno AVenhance.Infra.Torus
namespace AVenhance.Infra.Ergodic

/-- An ordered spatial derivative evaluated on coordinate directions. -/
def spatialJet {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : Vec d → F) (w : Fin n → Fin d) (x : Vec d) : F :=
  iteratedFDeriv ℝ n f x (fun i => basisVec (w i))

theorem spatialJet_continuous {d n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Vec d → F}
    (hf : ContDiff ℝ ∞ f) (w : Fin n → Fin d) : Continuous (spatialJet n f w) := by
  unfold spatialJet
  have hc := hf.continuous_iteratedFDeriv (m := n) (by simp)
  fun_prop

theorem spatialJet_periodic {d n : ℕ} {f : Vec d → ℂ}
    (hper : IsZdPeriodic f) (w : Fin n → Fin d) : IsZdPeriodic (spatialJet n f w) := by
  intro k x
  have he : (fun y => f (y + intVector k)) = f := funext (hper k)
  have hj := congrArg (fun g => iteratedFDeriv ℝ n g x) he
  simp only [iteratedFDeriv_comp_add_right] at hj
  exact congrArg (fun T => T (fun i => basisVec (w i))) hj

theorem spatialJet_const_eq_coordDerivIter {d : ℕ} {f : Vec d → ℂ}
    (hf : ContDiff ℝ ∞ f) (i : Fin d) (n : ℕ) :
    spatialJet n f (fun _ => i) = coordDerivIter i n f := by
  induction n with
  | zero => funext x; simp [spatialJet, coordDerivIter]
  | succ n ih =>
    funext x
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      hf.differentiable_iteratedFDeriv (m := n) (by exact_mod_cast ENat.natCast_lt_top n) x
    rw [spatialJet, hd.iteratedFDeriv_succ_apply_left']
    change fderiv ℝ (spatialJet n f (fun _ => i)) x (basisVec i) = _
    rw [ih]
    rfl

/-- Coordinate expansion of a multilinear evaluation. -/
theorem multilinear_coordinate_expansion {d k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => Vec d) F)
    (v : Fin k → Vec d) :
    T v = ∑ j : Fin k → Fin d,
      (∏ b, v b (j b)) • T (fun b => basisVec (j b)) := by
  classical
  have hv : v = fun b => ∑ a : Fin d, v b a • basisVec a := by
    funext b a
    simp [basisVec, Pi.single_apply]
  calc
    T v = T.toMultilinearMap (fun b => ∑ a : Fin d, v b a • basisVec a) :=
      congrArg T hv
    _ = ∑ j : Fin k → Fin d, T (fun b => v b (j b) • basisVec (j b)) :=
      T.toMultilinearMap.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact T.map_smul_univ _ _

/-- Total size of all blocks in a partition of the derivative positions. -/
theorem composition_block_size_sum {n : ℕ} (c : OrderedFinpartition n) :
    ∑ b, c.partSize b = n := by
  classical
  calc
    ∑ b, c.partSize b = Fintype.card (Σ b : Fin c.length, Fin (c.partSize b)) := by
      simp [Fintype.card_sigma]
    _ = Fintype.card (Fin n) := Fintype.card_congr c.equivSigma
    _ = n := Fintype.card_fin n

/-- The scalar summand of the coordinate Faà di Bruno expansion. -/
def compositionJetTerm {d n : ℕ} (f : Vec d → ℂ) (X : Vec d → Vec d)
    (w : Fin n → Fin d) (c : OrderedFinpartition n) (j : Fin c.length → Fin d)
    (x : Vec d) : ℂ :=
  (∏ b, (spatialJet (c.partSize b) X (fun a => w (c.emb b a)) x) (j b)) •
    spatialJet c.length f j (X x)

/-- Exact finite chain-rule sum, with every coordinate assignment retained. -/
theorem spatialJet_comp_expansion {d n : ℕ} {f : Vec d → ℂ} {X : Vec d → Vec d}
    (hf : ContDiff ℝ ∞ f) (hX : ContDiff ℝ ∞ X) (w : Fin n → Fin d) (x : Vec d) :
    spatialJet n (f ∘ X) w x =
      ∑ c : OrderedFinpartition n, ∑ j : Fin c.length → Fin d,
        compositionJetTerm f X w c j x := by
  classical
  rw [spatialJet, multivariateFaaDiBruno (hf.of_le (by simp)).contDiffAt
    (hX.of_le (by simp)).contDiffAt]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    multilinear_coordinate_expansion]
  rfl

end AVenhance.Infra.Ergodic
