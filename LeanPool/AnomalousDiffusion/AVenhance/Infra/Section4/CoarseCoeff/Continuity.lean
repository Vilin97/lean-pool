/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWeightedIntegrability
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.CoarseCoeff.SpatialWords

/-! # Continuity

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- All ordered coefficient jets are jointly continuous up to the initial time.
The only conditional regularity inputs concern the flow; the polynomial and
locally finite cutoff calculus apply to both structural instances. -/
theorem CoarseCoeffForm.word_joint_continuousOn {β : ℝ} {I : Ingredients β}
    {Φ : ℕ → ℝ → Vec 2 → ℝ} {hΦ : IsStreamSeq I Φ}
    {m : ℕ} {κ : ℝ} {s : ℝ → Vec 2 → CoarseMatrix}
    (hs : CoarseCoeffForm I hΦ m κ s) (hm : 1 ≤ m) (hκ : 0 < κ)
    (hflow : ∀ l : ℤ, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : AmnrSpace => I.flowGrad hΦ m l z.1 z.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (w : List (Fin 2)) (i j : Fin 2) :
    ContinuousOn (fun z : AmnrSpace => iterateSpatialWord w
      (fun y => s z.1 y i j) z.2) (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  classical
  obtain ⟨a, b, _, _, he⟩ := hs.window_form
  let U : Set AmnrSpace := Set.Ici (0 : ℝ) ×ˢ Set.univ
  have hK := Infra.Section5.RelativeError.Kmat_contDiff_top I hm hκ
  have hkernel (l : ℤ) : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : AmnrSpace =>
      coarseCoeffPolynomial a b κ (I.Kmat κ m z.1) (I.flowGrad hΦ m l z.1 z.2) i j) U :=
    contDiffOn_pi.1 (contDiffOn_pi.1 (coarseCoeffPolynomial_contDiffOn a b κ
      ((hK.comp contDiff_fst).contDiffOn) (hflow l)) i) j
  have hkernelc (l : ℤ) : ContinuousOn (fun z : AmnrSpace =>
      iterateSpatialWord w (fun y => coarseCoeffPolynomial a b κ
        (I.Kmat κ m z.1) (I.flowGrad hΦ m l z.1 y) i j) z.2) U :=
    (iterateSpatialWord_smooth_up_to_initial (u := fun t y =>
      coarseCoeffPolynomial a b κ (I.Kmat κ m t) (I.flowGrad hΦ m l t y) i j)
      (hkernel l) w).continuousOn
  have hξ (l : ℤ) : Continuous (I.hatXiML m l) :=
    (Infra.Section5.RelativeError.hatXiML_contDiff I m l).continuous
  intro z₀ hz₀
  obtain ⟨S, hS⟩ := Infra.Section5.RelativeError.exists_finset_hatXi_vanish I hm z₀.1
  let f : AmnrSpace → ℝ := fun z => ∑ l ∈ S, I.hatXiML m l z.1 *
    iterateSpatialWord w (fun y => coarseCoeffPolynomial a b κ
      (I.Kmat κ m z.1) (I.flowGrad hΦ m l z.1 y) i j) z.2
  have hfc : ContinuousOn f U := by
    apply continuousOn_finsetSum S
    intro l _
    exact ((hξ l).comp continuous_fst).continuousOn.mul (hkernelc l)
  have hnear : ∀ᶠ z : AmnrSpace in nhdsWithin z₀ U, |z.1 - z₀.1| < 1 := by
    have hc : Continuous (fun z : AmnrSpace => |z.1 - z₀.1|) := by fun_prop
    exact (hc.continuousAt.eventually (gt_mem_nhds (by simp))).filter_mono nhdsWithin_le_nhds
  have hpoint (z : AmnrSpace) (hz : z ∈ U) (ht : |z.1 - z₀.1| < 1) :
      iterateSpatialWord w (fun y => s z.1 y i j) z.2 = f z := by
    have hfs (l : ℤ) : ContDiff ℝ (⊤ : ℕ∞) (I.flowGrad hΦ m l z.1) := by
      have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => (z.1, y)) := by fun_prop
      exact (hflow l).comp_contDiff hmap (fun y => ⟨hz.1, Set.mem_univ y⟩)
    have hse : (fun y => s z.1 y i j) =
        fun y => coarseCoeffWindow I hΦ m κ a b z.1 y i j := by
      funext y
      rw [he]
    rw [hse, coarseCoeffWindow_word_formula I hΦ hm κ a b z.1 hfs]
    exact tsum_eq_sum (s := S) (fun l hl => by rw [hS z.1 ht l hl, zero_mul])
  have heq : (fun z : AmnrSpace => iterateSpatialWord w
      (fun y => s z.1 y i j) z.2) =ᶠ[nhdsWithin z₀ U] f := by
    filter_upwards [hnear, self_mem_nhdsWithin] with z ht hz
    exact hpoint z hz ht
  exact (hfc z₀ hz₀).congr_of_eventuallyEq heq (hpoint z₀ hz₀ (by simp))

end AVenhance.Infra.Section4
