/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreyGradientPackage
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientProduct
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationGradientTransfer
public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceIntegrability
public import LeanPool.CaffarelliKohnNirenberg.Setting.DivergenceFreeSlice
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceGradientSelection

/-!
# Localized Equation Gradient Transfers

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
open CKN.Foundation.Parabolic
open CKN.Core.Step3
open CKN.Core.Step4

noncomputable section
namespace CKN.Core.Step3

private lemma product_partial_of_slice
    {U : Set Vec3} (hU : IsOpen U)
    {a : Vec3 → Vec3} {Da : Vec3 → Fin 3 → Vec3}
    (ha : ∀ i : Fin 3, MemLp (fun x => a x i) 2 (volume.restrict U))
    (hDa : ∀ i j : Fin 3, MemLp (fun x => Da x i j) 2 (volume.restrict U))
    (hweak : ∀ i : Fin 3,
      HasWeakGradientOn U (fun x => a x i) (fun x => Da x i))
    (i j k : Fin 3) :
    HasWeakPartialDerivOn U k (fun x => a x i * a x j)
      (fun x => Da x i k * a x j + a x i * Da x j k) := by
  have hprod := CKN.Core.Step4.weak_gradient_product_indicator hU ha hDa hweak i j
  intro η hη hηc hηU
  have htest := hprod k η hη hηc hηU
  calc
    (∫ x in U, a x i * a x j * (fderiv ℝ η x) (basisVec k)) =
        ∫ x in U, U.indicator (fun y => a y i) x *
          U.indicator (fun y => a y j) x * (fderiv ℝ η x) (basisVec k) := by
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      simp [Set.indicator_of_mem hx]
    _ = -∫ x in U, (U.indicator (fun y => Da y i k) x *
          U.indicator (fun y => a y j) x +
          U.indicator (fun y => a y i) x *
            U.indicator (fun y => Da y j k) x) * η x := htest
    _ = -∫ x in U, (Da x i k * a x j + a x i * Da x j k) * η x := by
      congr 1
      apply setIntegral_congr_fun hU.measurableSet
      intro x hx
      simp [Set.indicator_of_mem hx]

theorem localized_convection_transfer_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ)
    (i j : Fin 3) :
    (∫ z, u z i * u z j *
      spatialPartial (fun w => φ w * ψ w i) j z) =
      -(∫ z, (Du z i j * u z j + u z i * Du z j j) *
        (φ z * ψ z i)) := by
  obtain ⟨hu, hDu, -, -, -, henergy, -, -, hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  haveI : IsFiniteMeasure μ := local_box_isFiniteMeasure
    hbox.2.1 hbox.2.2.2.2.1
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have huComp (k : Fin 3) : MemLp (fun z => u z k) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
  have hDuComp (k l : Fin 3) : MemLp (fun z => Du z k l) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj k : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj l : Vec3 →L[ℝ] ℝ)
  have hUU : Integrable (fun z => u z i * u z j) μ :=
    (huComp i).integrable_mul (huComp j)
  have hUD₁ : Integrable (fun z => Du z i j * u z j) μ := by
    have h := (huComp j).integrable_mul (hDuComp i j)
    change Integrable (fun z => u z j * Du z i j) μ at h
    convert h using 1
    funext z
    ring
  have hUD₂ : Integrable (fun z => u z i * Du z j j) μ :=
    (huComp i).integrable_mul (hDuComp j j)
  have hD : Integrable
      (fun z => Du z i j * u z j + u z i * Du z j j) μ := hUD₁.add hUD₂
  have hφd := hφ.1
  have hψd := hψ.1
  let b : Vec3 × ℝ → ℝ := fun z => φ z * ψ z i
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    dsimp [b]
    exact hφd.mul ((contDiff_apply ℝ ℝ i).comp hψd)
  have hbc : HasCompactSupport b := by
    dsimp [b]
    exact hφ.2.1.mul_right (f' := fun z => ψ z i)
  have hbs : tsupport b ⊆ Ω' ×ˢ J := by
    exact (tsupport_mul_subset_left (f := φ) (g := fun z => ψ z i)).trans hφbox
  have hbsp : ∀ k : Fin 3, HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from b) k (z.1, z.2)) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact hbc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hb hnot k
  have hbsts : ∀ k : Fin 3, tsupport
      (fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from b) k (z.1, z.2)) ⊆ tsupport b := by
    intro k
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hb hnot k
    · exact isClosed_tsupport b
  have hDb : Integrable (fun z =>
      (Du z i j * u z j + u z i * Du z j j) * b z) volume := by
    exact compact_factor_integrable (a := fun z =>
      Du z i j * u z j + u z i * Du z j j) (b := b) hD
      hb.continuous hbc hbs
  have hUUb : Integrable (fun z => u z i * u z j *
      spatialPartial b j z) volume := by
    exact compact_factor_integrable (a := fun z => u z i * u z j)
      (b := fun z : Vec3 × ℝ => spatialPartial
        (show ParabolicPoint → ℝ from b) j (z.1, z.2)) hUU
      (spatialPartial_contDiff hb j).continuous (hbsp j) ((hbsts j).trans hbs)
  have hzeroD : ∀ z ∉ spaceTimeSet Ω' J,
      (Du z i j * u z j + u z i * Du z j j) * b z = 0 := by
    intro z hz
    have hz' : (z.1, z.2) ∉ tsupport b := by
      intro hm
      apply hz
      exact hbs hm
    have hbzero : b (z.1, z.2) = 0 :=
      image_eq_zero_of_notMem_tsupport hz'
    change (Du z i j * u z j + u z i * Du z j j) * b (z.1, z.2) = 0
    rw [hbzero, mul_zero]
  have hzeroUU : ∀ z ∉ spaceTimeSet Ω' J,
      u z i * u z j * spatialPartial b j z = 0 := by
    intro z hz
    have hz' : (z.1, z.2) ∉ tsupport b := by
      intro hm
      apply hz
      exact hbs hm
    have hspzero := spatialPartial_zero_of_not_mem_tsupport_public hb hz' j
    change u z i * u z j * spatialPartial b j (z.1, z.2) = 0
    rw [hspzero, mul_zero]
  have hgradAll : ∀ᵐ t ∂volume.restrict J, ∀ k : Fin 3,
      HasWeakGradientOn Ω' (fun x => u (x, t) k)
        (fun x => Du (x, t) k) := by
    rw [ae_all_iff]
    intro k
    exact hgrad k
  have hsliceMem := slice_memLp_ae_of_sws hsol hbox
  have hprodGrad : ∀ᵐ t ∂volume.restrict J,
      HasWeakPartialDerivOn Ω' j
        (fun x => u (x, t) i * u (x, t) j)
        (fun x => Du (x, t) i j * u (x, t) j +
          u (x, t) i * Du (x, t) j j) := by
    filter_upwards [hsliceMem, hgradAll] with t hmem hgt
    exact product_partial_of_slice hbox.1
      (fun k => MemLp.eval hmem.1 k)
      (fun k l => MemLp.eval (MemLp.eval hmem.2 k) l)
      hgt i j j
  have htransfer := spacetime_weak_partial_transfer
      (Ω' := Ω') (J := J) (a := fun z => u z i * u z j)
      (d := fun z => Du z i j * u z j + u z i * Du z j j)
      (b := b) (j := j) hbox.2.2.2.1.measurableSet hDb hUUb
      hzeroD hzeroUU hprodGrad
      (fun t => (CKN.slice_testFunction hb hbc hbs t).1)
      (fun t => (CKN.slice_testFunction hb hbc hbs t).2.1)
      (fun t => (CKN.slice_testFunction hb hbc hbs t).2.2)
  have htransfer' :
      (∫ z, (Du z i j * u z j + u z i * Du z j j) *
        (φ z * ψ z i)) =
        -(∫ z, u z i * u z j *
        spatialPartial (fun w => φ w * ψ w i) j z) := by
    have hfun : (fun z : ParabolicPoint => φ z * ψ z i) =
        (fun z => b (z.1, z.2)) := by
      funext z
      rfl
    rw [hfun]
    exact htransfer
  calc
    (∫ z, u z i * u z j *
        spatialPartial (fun w => φ w * ψ w i) j z) =
        -(-(∫ z, u z i * u z j *
          spatialPartial (fun w => φ w * ψ w i) j z)) := by ring
    _ = -(∫ z, (Du z i j * u z j + u z i * Du z j j) *
        (φ z * ψ z i)) := by rw [htransfer']

theorem localized_diffusion_transfer_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I)
    {Ω' : Set Vec3} {J : Set ℝ} (hbox : localBox Ω I Ω' J)
    (hφbox : tsupport φ ⊆ Ω' ×ˢ J)
    {ψ : Vec3 × ℝ → Vec3}
    (hψ : ψ ∈ spaceTimeTestFunction (V := Vec3) Set.univ Set.univ)
    (i j : Fin 3) :
    -(∫ z, Du z i j * spatialPartial φ j z * ψ z i) +
        (∫ z, u z i * (spatialPartial φ j z *
          spatialPartial (fun w => ψ w i) j z)) =
      (∫ z, u z i * ((spatialSecondPartial
          (show ParabolicPoint → ℝ from φ) j j z) * ψ z i)) +
        2 * (∫ z, u z i * (spatialPartial φ j z *
          spatialPartial (fun w => ψ w i) j z)) := by
  obtain ⟨hu, hDu, -, -, -, henergy, -, -, hgrad⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  let μ : Measure ParabolicPoint := volume.restrict (spaceTimeSet Ω' J)
  haveI : IsFiniteMeasure μ := local_box_isFiniteMeasure
    hbox.2.1 hbox.2.2.2.2.1
  have hLp := local_memLp_two_of_energy (hu := hu) (hDu := hDu) henergy
  have huComp (k : Fin 3) : MemLp (fun z => u z k) 2 μ :=
    hLp.1.continuousLinearMap_comp
      (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
  have hDuComp (k l : Fin 3) : MemLp (fun z => Du z k l) 2 μ :=
    (hLp.2.continuousLinearMap_comp
      (ContinuousLinearMap.proj k : (Fin 3 → Vec3) →L[ℝ] Vec3)).continuousLinearMap_comp
      (ContinuousLinearMap.proj l : Vec3 →L[ℝ] ℝ)
  have hUi : Integrable (fun z => u z i) μ :=
    (huComp i).integrable (by norm_num)
  have hDij : Integrable (fun z => Du z i j) μ :=
    (hDuComp i j).integrable (by norm_num)
  have hφd := hφ.1
  have hψd := hψ.1
  have hφsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial φ j z) :=
    spatialPartial_contDiff hφd j
  have hφspc : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialPartial φ j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hφ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
  have hφspts : tsupport
      (fun z : Vec3 × ℝ => spatialPartial φ j z) ⊆ tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hφd hnot j
    · exact isClosed_tsupport φ
  have hφsecondc : HasCompactSupport
      (fun z : Vec3 × ℝ => spatialSecondPartial φ j j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hφ.2.1.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hnot j j
  have hφseconds : tsupport
      (fun z : Vec3 × ℝ => spatialSecondPartial φ j j z) ⊆ tsupport φ := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialSecondPartial_zero_of_not_mem_tsupport_public hφd hnot j j
    · exact isClosed_tsupport φ
  let b : Vec3 × ℝ → ℝ := fun z => spatialPartial φ j z * ψ z i
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    dsimp [b]
    exact hφsp.mul ((contDiff_apply ℝ ℝ i).comp hψd)
  have hbc : HasCompactSupport b := by
    dsimp [b]
    exact hφspc.mul_right (f' := fun z => ψ z i)
  have hbs : tsupport b ⊆ Ω' ×ˢ J := by
    exact (tsupport_mul_subset_left (f := fun z : Vec3 × ℝ => spatialPartial φ j z)
      (g := fun z => ψ z i)).trans (hφspts.trans hφbox)
  have hbspc : HasCompactSupport (fun z : Vec3 × ℝ => spatialPartial b j z) := by
    apply HasCompactSupport.of_support_subset_isCompact hbc.isCompact
    intro z hz
    by_contra hnot
    apply hz
    exact spatialPartial_zero_of_not_mem_tsupport_public hb hnot j
  have hbspts : tsupport (fun z : Vec3 × ℝ => spatialPartial b j z) ⊆ tsupport b := by
    apply closure_minimal
    · intro z hz
      by_contra hnot
      apply hz
      exact spatialPartial_zero_of_not_mem_tsupport_public hb hnot j
    · exact isClosed_tsupport b
  have hDb : Integrable (fun z => Du z i j * b z) volume :=
    compact_factor_integrable (a := fun z => Du z i j) (b := b) hDij
      hb.continuous hbc hbs
  have hUb : Integrable (fun z => u z i * spatialPartial b j z) volume :=
    compact_factor_integrable (a := fun z => u z i)
      (b := fun z : Vec3 × ℝ => spatialPartial b j z) hUi
      (spatialPartial_contDiff hb j).continuous hbspc (hbspts.trans hbs)
  have hzeroD : ∀ z ∉ spaceTimeSet Ω' J, Du z i j * b z = 0 := by
    intro z hz
    have hz' : (z.1, z.2) ∉ tsupport b := by
      intro hm
      apply hz
      exact hbs hm
    have hbzero : b (z.1, z.2) = 0 :=
      image_eq_zero_of_notMem_tsupport hz'
    change Du z i j * b (z.1, z.2) = 0
    rw [hbzero, mul_zero]
  have hzeroU : ∀ z ∉ spaceTimeSet Ω' J,
      u z i * spatialPartial b j z = 0 := by
    intro z hz
    have hz' : (z.1, z.2) ∉ tsupport b := by
      intro hm
      apply hz
      exact hbs hm
    have hspzero := spatialPartial_zero_of_not_mem_tsupport_public hb hz' j
    change u z i * spatialPartial b j (z.1, z.2) = 0
    rw [hspzero, mul_zero]
  have hgradI : ∀ᵐ t ∂volume.restrict J,
      HasWeakPartialDerivOn Ω' j (fun x => u (x, t) i)
        (fun x => Du (x, t) i j) := by
    exact hgrad i |>.mono (fun t ht => ht j)
  have htransfer := spacetime_weak_partial_transfer
      (Ω' := Ω') (J := J) (a := fun z => u z i)
      (d := fun z => Du z i j) (b := b) (j := j)
      hbox.2.2.2.1.measurableSet hDb hUb hzeroD hzeroU hgradI
      (fun t => (CKN.slice_testFunction hb hbc hbs t).1)
      (fun t => (CKN.slice_testFunction hb hbc hbs t).2.1)
      (fun t => (CKN.slice_testFunction hb hbc hbs t).2.2)
  have htransfer' :
    (∫ z, Du z i j * spatialPartial φ j z * ψ z i) =
        -(∫ z, u z i *
        (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
            spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
    calc
      (∫ z, Du z i j * spatialPartial φ j z * ψ z i) =
          ∫ z, Du z i j * b z := by
            apply integral_congr_ae
            filter_upwards [] with z
            dsimp [b]
            ring
      _ = -(∫ z, u z i * spatialPartial b j z) := htransfer
      _ = -(∫ z, u z i *
          (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
            spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with z
        have hprod := spatialPartial_mul_full hφsp
          ((contDiff_apply ℝ ℝ i).comp hψd) j (z.1, z.2)
        change u z i * spatialPartial b j z =
          u z i *
            (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
              spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)
        dsimp [b] at hprod ⊢
        have hψcomp : ((fun f : Vec3 => f i) ∘ ψ) =
            (fun w => ψ w i) := by
          funext w
          rfl
        rw [hψcomp] at hprod
        have hprod' := congrArg (fun x : ℝ => u z i * x) hprod
        convert hprod' using 1 <;> rfl
  have hsplit :
      (∫ z, u z i *
          (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
            spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) =
        (∫ z, u z i *
          (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i)) +
          (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
    have hA := compact_factor_integrable (a := fun z => u z i)
      (b := fun z : Vec3 × ℝ => spatialSecondPartial φ j j z * ψ z i)
      hUi ((spatialSecondPartial_contDiff_full hφd j j).mul
        ((contDiff_apply ℝ ℝ i).comp hψd)).continuous
      (hφsecondc.mul_right (f' := fun z => ψ z i))
      ((tsupport_mul_subset_left
        (f := fun z : Vec3 × ℝ => spatialSecondPartial φ j j z)
        (g := fun z => ψ z i)).trans (hφseconds.trans hφbox))
    have hB := compact_factor_integrable (a := fun z => u z i)
      (b := fun z : Vec3 × ℝ => spatialPartial φ j z *
        spatialPartial (fun w => ψ w i) j z)
      hUi ((hφsp.mul (spatialPartial_contDiff
        ((contDiff_apply ℝ ℝ i).comp hψd) j))).continuous
      (hφspc.mul_right (f' := fun z : Vec3 × ℝ =>
        spatialPartial (fun w : Vec3 × ℝ => ψ w i) j z))
      ((tsupport_mul_subset_left
        (f := fun z : Vec3 × ℝ => spatialPartial φ j z)
        (g := fun z : Vec3 × ℝ =>
          spatialPartial (fun w : Vec3 × ℝ => ψ w i) j z)).trans
          (hφspts.trans hφbox))
    calc
      (∫ z, u z i *
          (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
            spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) =
          (∫ z, (u z i * spatialSecondPartial
            (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
            u z i * spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
        apply integral_congr_ae
        filter_upwards [] with z
        ring
      _ = (∫ z, u z i *
            (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i)) +
          (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
            simpa only [mul_assoc] using (integral_add hA hB)
  have hfinal :
      -(∫ z, Du z i j * spatialPartial φ j z * ψ z i) +
          (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) =
        (∫ z, u z i *
            (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i)) +
          2 * (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
    calc
      -(∫ z, Du z i j * spatialPartial φ j z * ψ z i) +
          (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) =
        -(-(∫ z, u z i *
            (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i +
              spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z))) +
          (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
          rw [htransfer']
      _ = (∫ z, u z i *
            (spatialSecondPartial (show ParabolicPoint → ℝ from φ) j j z * ψ z i)) +
          2 * (∫ z, u z i *
            (spatialPartial φ j z * spatialPartial (fun w => ψ w i) j z)) := by
          rw [hsplit]
          ring
  simpa only [mul_assoc] using hfinal
