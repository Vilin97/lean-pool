/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.Form
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Tensor-independent directional calculus for LeftJacobian iterates.
The operators and proofs are the generic calculus in Amnr/Calculus, isolated
in a namespace so repairs of the Amnr base cannot supply stale proof artifacts.
Their literal formulas agree with the original operators. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
namespace AVenhance.Infra.Section4.IterateCalculus

/-! The mixed calculus below keeps spatial and material operations ordered. -/

/-- Scalar material operator. This calculus does not depend on a corrector tensor. -/
def amnrMaterial (b : ℝ → Vec 2 → Vec 2) (f : ℝ → Vec 2 → ℝ)
    (t : ℝ) (x : Vec 2) : ℝ :=
  deriv (fun s => f s x) t + vecDot (b t x) (AVenhance.spaceGrad (f t) x)

/-- Space-time coordinate carrier used only to express the differential operators. -/
abbrev AmnrSpace := ℝ × Vec 2

/-- `none` is the material direction; `some i` is the i-th spatial direction. -/
def amnrDirection (b : AmnrSpace → Vec 2) (d : Option (Fin 2)) (z : AmnrSpace) : AmnrSpace :=
  match d with
  | none => (1, b z)
  | some i => (0, basisVec i)

/-- A directional differential operator on the actual space-time function. -/
def amnrOp (b : AmnrSpace → Vec 2) (d : Option (Fin 2))
    (f : AmnrSpace → ℝ) (z : AmnrSpace) : ℝ := fderiv ℝ f z (amnrDirection b d z)

/-- Ordered differential words, with the outermost operator at the head. -/
def amnrWord (b : AmnrSpace → Vec 2) : List (Option (Fin 2)) →
    (AmnrSpace → ℝ) → AmnrSpace → ℝ
  | [], f => f
  | d :: w, f => amnrOp b d (amnrWord b w f)

theorem DirectionalCalculus.amnrDirection_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    {n : ℕ} (hb : ContDiffOn ℝ n b U) (d : Option (Fin 2)) :
    ContDiffOn ℝ n (amnrDirection b d) U := by
  cases d with
  | none => exact contDiffOn_const.prodMk hb
  | some i => exact contDiffOn_const

/-- Every word consumes exactly one ordinary derivative per letter. -/
theorem amnrWord_contDiffOn {b : AmnrSpace → Vec 2} {U : Set AmnrSpace}
    (hU : IsOpen U) {N : ℕ} (hb : ContDiffOn ℝ N b U)
    {f : AmnrSpace → ℝ} (hf : ContDiffOn ℝ N f U)
    (w : List (Option (Fin 2))) {n : ℕ} (hn : n + w.length ≤ N) :
    ContDiffOn ℝ n (amnrWord b w f) U := by
  induction w generalizing n with
  | nil => exact hf.of_le (by exact_mod_cast hn)
  | cons d w ih =>
    have hlen : (n + 1) + w.length ≤ N := by simp only [List.length_cons] at hn; omega
    have hw := ih hlen
    have hd := hw.fderiv_of_isOpen hU (show (n : WithTop ℕ∞) + 1 ≤ (n + 1 : ℕ) by norm_cast)
    have hdir := DirectionalCalculus.amnrDirection_contDiffOn (hb.of_le (by exact_mod_cast (by
        omega : n ≤ N))) d
    exact hd.clm_apply hdir

/-- Directional Leibniz rule, with no quantitative hypothesis. -/
theorem amnrOp_mul {b : AmnrSpace → Vec 2} (d : Option (Fin 2))
    {f g : AmnrSpace → ℝ} {z : AmnrSpace}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    amnrOp b d (f * g) z = amnrOp b d f z * g z + f z * amnrOp b d g z := by
  unfold amnrOp
  rw [fderiv_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Directional differentiation commutes with finite sums of differentiable functions. -/
theorem amnrOp_sum {ι : Type*} (S : Finset ι) {b : AmnrSpace → Vec 2}
    (d : Option (Fin 2)) (f : ι → AmnrSpace → ℝ) (z : AmnrSpace)
    (hf : ∀ i ∈ S, DifferentiableAt ℝ (f i) z) :
    amnrOp b d (∑ i ∈ S, f i) z = ∑ i ∈ S, amnrOp b d (f i) z := by
  unfold amnrOp
  rw [fderiv_sum hf]
  simp only [sum_apply]

theorem amnrOp_material {b : AmnrSpace → Vec 2} {f : AmnrSpace → ℝ}
    {z : AmnrSpace} (hf : DifferentiableAt ℝ f z) :
    amnrOp b none f z = amnrMaterial (fun t x => b (t, x))
      (fun t x => f (t, x)) z.1 z.2 := by
  have ht := (hf.hasFDerivAt.comp z.1 (hasFDerivAt_prodMk_left (𝕜 := ℝ) z.1 z.2)).hasDerivAt.deriv
  have hx := (hf.hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)).fderiv
  have hvec : b z = ∑ i : Fin 2, b z i • basisVec i := by
    funext i
    simp [basisVec_apply]
  unfold amnrOp amnrDirection amnrMaterial AVenhance.spaceGrad vecDot
  change fderiv ℝ f z (1, b z) = deriv (f ∘ fun s => (s, z.2)) z.1 +
    ∑ i : Fin 2, b z i * fderiv ℝ (f ∘ fun y => (z.1, y)) z.2 (basisVec i)
  rw [ht]
  have hsplit : (1, b z) = ((1, 0) : AmnrSpace) + (0, b z) := by ext <;> simp
  rw [hsplit, map_add]
  congr 1
  conv_lhs => rw [hvec]
  have hpair : ((0, ∑ i : Fin 2, b z i • basisVec i) : AmnrSpace) =
      ∑ i : Fin 2, b z i • ((0, basisVec i) : AmnrSpace) := by
    apply Prod.ext
    · simp
    · funext i
      fin_cases i <;> simp [basisVec_apply]
  rw [hpair, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hx]
  rfl

end AVenhance.Infra.Section4.IterateCalculus
