/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSupport

/-!
# A measurable weak gradient on a countable union of time windows

The pressure gradient in `paper/ckn.tex`, Section `sec:pressure`, is first
constructed on spatial slices. Selection on integrable time windows and
countable pasting give a jointly measurable representative on their union.
The representative remains locally integrable and a weak derivative on almost
every spatial slice, so uniqueness identifies it with every derivative on
an open subdomain of the carrier.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open CKN.Foundation.Parabolic

namespace CKN

/-- Slice gradients on a countable union of integrable time windows have a
jointly measurable representative on every relatively compact open inner
carrier. All coordinates and all open subdomains share one exceptional time set. -/
theorem exists_measurable_weakGradient_on_time_union
    {B U : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ}
    (hB : IsOpen B) (hU : IsOpen U) (hUc : IsCompact (closure U))
    (hUB : closure U ⊆ B) {J : ℕ → Set ℝ}
    (hJ : ∀ n, MeasurableSet (J n)) (hJI : (⋃ n, J n) = I)
    (hp : ∀ n, IntegrableOn p (B ×ˢ J n) volume)
    (hslice : ∀ k : Fin 3, ∀ᵐ s ∂volume.restrict I, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g B volume ∧
      HasWeakPartialDerivOn B k (fun x => p (x, s)) g) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
        LocallyIntegrableOn (fun x => Dp (x, s) k) U volume ∧
        HasWeakPartialDerivOn U k (fun x => p (x, s)) (fun x => Dp (x, s) k) ∧
        ∀ W : Set Vec3, IsOpen W → W ⊆ U → ∀ g : Vec3 → ℝ,
          LocallyIntegrableOn g W volume →
          HasWeakPartialDerivOn W k (fun x => p (x, s)) g →
          (fun x => Dp (x, s) k) =ᵐ[volume.restrict W] g := by
  classical
  have hJsub (n : ℕ) : J n ⊆ I := by
    rw [← hJI]
    exact subset_iUnion J n
  have hex (n : ℕ) (k : Fin 3) := exists_spacetime_weak_gradient_of_slices
    k hB hU.measurableSet hUc hUB (hp n)
      (ae_restrict_of_ae_restrict_of_subset (hJsub n) (hslice k))
  choose D hDmeas hDid hDpair hDprod using hex
  let F : ℕ → Fin 3 → ParabolicPoint → ℝ := fun n k => (hDmeas n k).mk (D n k)
  have hFmeas (n : ℕ) (k : Fin 3) : Measurable (F n k) := (hDmeas n k).measurable_mk
  have hFeq (n : ℕ) (k : Fin 3) : ∀ᵐ s ∂volume.restrict (J n),
      (fun x => D n k (x, s)) =ᵐ[volume.restrict U] (fun x => F n k (x, s)) := by
    have hprod : (volume : Measure (Vec3 × ℝ)).restrict (U ×ˢ J n) =
        (volume.restrict U).prod (volume.restrict (J n)) := by
      rw [volume_eq_prod, ← Measure.prod_restrict]
    have heq : (fun z : Vec3 × ℝ => D n k z)
        =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict (U ×ˢ J n)]
          (fun z : Vec3 × ℝ => F n k z) := (hDmeas n k).ae_eq_mk
    rw [hprod] at heq
    exact ae_ae_of_ae_prod_snd heq
  have hFspec (n : ℕ) : ∀ᵐ s ∂volume.restrict (J n), ∀ k : Fin 3,
      LocallyIntegrableOn (fun x => F n k (x, s)) U volume ∧
      HasWeakPartialDerivOn U k (fun x => p (x, s)) (fun x => F n k (x, s)) := by
    filter_upwards [ae_all_iff.mpr (hFeq n), ae_all_iff.mpr (hDid n),
      ae_restrict_of_ae_restrict_of_subset (hJsub n) (ae_all_iff.mpr hslice)]
      with s hsEq hsId hsEx k
    obtain ⟨g, hgloc, hgweak⟩ := hsEx k
    have hFg : (fun x => F n k (x, s)) =ᵐ[volume.restrict U] g :=
      (hsEq k).symm.trans (hsId k g hgloc hgweak)
    have hUsubB : U ⊆ B := subset_closure.trans hUB
    exact ⟨(hgloc.mono_set hUsubB).congr hFg.symm,
      (hgweak.restrict hU hUsubB).congr_deriv_ae hFg.symm⟩
  let A : ℕ → Set ℝ := disjointed J
  have hAsub (n : ℕ) : A n ⊆ J n := disjointed_subset J n
  have hAmeas (n : ℕ) : MeasurableSet (A n) := MeasurableSet.disjointed hJ n
  have hAI : (⋃ n, A n) = I := by
    change (⋃ n, disjointed J n) = I
    rw [iUnion_disjointed, hJI]
  have hdisj : Pairwise (Function.onFun Disjoint A) := disjoint_disjointed J
  obtain ⟨Dp, hDpmeas, hDp⟩ := exists_measurable_piecewise
    (fun n => (univ : Set Vec3) ×ˢ A n)
    (fun n => MeasurableSet.univ.prod (hAmeas n)) (fun n z k => F n k z)
    (fun n => Measurable.of_eval (hFmeas n)) (by
      intro m n hmn z hz
      exact False.elim (Set.disjoint_left.mp (hdisj hmn) hz.1.2 hz.2.2))
  refine ⟨Dp, hDpmeas, ?_⟩
  rw [← hAI, ae_restrict_iUnion_iff]
  intro n
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (hAsub n) (hFspec n),
    ae_restrict_mem (hAmeas n)] with s hs hsA k
  have heq : (fun x => Dp (x, s) k) = fun x => F n k (x, s) := by
    funext x
    exact congrFun (hDp n ⟨mem_univ x, hsA⟩) k
  rw [heq]
  refine ⟨(hs k).1, (hs k).2, ?_⟩
  intro W hW hWU g' hg'loc hg'weak
  exact HasWeakPartialDerivOn.ae_eq hW ((hs k).1.mono_set hWU) hg'loc
    ((hs k).2.restrict hW hWU) hg'weak

end CKN
