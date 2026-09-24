/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Measure.CompactMultiplier
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Product rules for compactly supported smooth multipliers

The statements here use the representative functions carried by the weak-derivative
predicate.  Compact support keeps every test-function product inside the open set, so
the resulting derivative is a global weak derivative of the zero extension.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace CKN

private theorem support_fderiv_apply_subset_tsupport
    {d : ℕ} {η : Vec d → ℝ} (i : Fin d) :
    Function.support (fun x => (fderiv ℝ η x) (basisVec i)) ⊆ tsupport η := by
  intro x hx
  by_contra hxt
  have hηzero : η =ᶠ[nhds x] 0 :=
    (isClosed_tsupport (f := η)).isOpen_compl.eventually_mem hxt |>.mono
      (fun y hy => image_eq_zero_of_notMem_tsupport hy)
  have hderivzero := Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hηzero
  change (fderiv ℝ η x) (basisVec i) ≠ 0 at hx
  apply hx
  rw [hderivzero]
  simp

theorem HasWeakPartialDerivOn.mul_smooth_zeroExtend
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hgi : LocallyIntegrableOn gi U volume)
    (hweak : HasWeakPartialDerivOn U i u gi)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    HasWeakPartialDerivOn Set.univ i (fun x => η x * u x)
      (fun x => η x * gi x + u x * (fderiv ℝ η x) (basisVec i)) := by
  intro φ hφ hφCompact hφSub
  let dη : Vec d → ℝ := fun x => (fderiv ℝ η x) (basisVec i)
  let dφ : Vec d → ℝ := fun x => (fderiv ℝ φ x) (basisVec i)
  have hηDiff : Differentiable ℝ η := hη.differentiable (by simp)
  have hφDiff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdηCont : Continuous dη := by
    simpa [dη] using (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφCont : Continuous dφ := by
    simpa [dφ] using (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdηCompact : HasCompactSupport dη := by
    simpa [dη] using hηCompact.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηφCompact : HasCompactSupport (fun x => η x * φ x) :=
    hηCompact.mul_right (f' := φ)
  have hdηφCompact : HasCompactSupport (fun x => dη x * φ x) :=
    hdηCompact.mul_right (f' := φ)
  have hηdφCompact : HasCompactSupport (fun x => η x * dφ x) :=
    hηCompact.mul_right (f' := dφ)
  have hηφSub : tsupport (fun x => η x * φ x) ⊆ U :=
    (tsupport_mul_subset_left (f := η) (g := φ)).trans hηU
  have hdηSub : tsupport dη ⊆ tsupport η := by
    apply closure_minimal (support_fderiv_apply_subset_tsupport i)
    exact isClosed_tsupport (f := η)
  have hdηφSub : tsupport (fun x => dη x * φ x) ⊆ U :=
    (tsupport_mul_subset_left (f := dη) (g := φ)).trans
      (hdηSub.trans hηU)
  have hηdφSub : tsupport (fun x => η x * dφ x) ⊆ U :=
    (tsupport_mul_subset_left (f := η) (g := dφ)).trans hηU
  have hηφSmooth := hη.mul hφ
  have hηφWeak := hweak (fun x => η x * φ x) hηφSmooth hηφCompact hηφSub
  have hA : IntegrableOn (fun x => u x * (dη x * φ x)) U volume :=
    CKN.integrableOn_mul_continuous_of_tsupport_subset hU hu
      (hdηCont.mul hφ.continuous) hdηφCompact hdηφSub
  have hB : IntegrableOn (fun x => u x * (η x * dφ x)) U volume :=
    CKN.integrableOn_mul_continuous_of_tsupport_subset hU hu
      (hη.continuous.mul hdφCont) hηdφCompact hηdφSub
  have hC : IntegrableOn (fun x => gi x * (η x * φ x)) U volume :=
    CKN.integrableOn_mul_continuous_of_tsupport_subset hU hgi
      (hη.continuous.mul hφ.continuous) hηφCompact hηφSub
  have hbasic :
      (∫ x in U, u x * (dη x * φ x) + u x * (η x * dφ x)) =
        -∫ x in U, gi x * (η x * φ x) := by
    calc
      (∫ x in U, u x * (dη x * φ x) + u x * (η x * dφ x)) =
          ∫ x in U, u x * ((fderiv ℝ (fun y => η y * φ y) x) (basisVec i)) := by
        apply setIntegral_congr_fun hU.measurableSet
        intro x hx
        have hmul := congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i))
          (fderiv_mul (hηDiff x) (hφDiff x))
        have hfun : (fun y => η y * φ y) = η * φ := by
          funext y
          rfl
        have hmul' : dη x * φ x + η x * dφ x =
            (fderiv ℝ (η * φ) x) (basisVec i) := by
          calc
            dη x * φ x + η x * dφ x =
                η x * dφ x + φ x * dη x := by ring
            _ = (fderiv ℝ (η * φ) x) (basisVec i) := by
              simpa [dη, dφ, smul_eq_mul, Pi.mul_apply] using hmul.symm
        change u x * (dη x * φ x) + u x * (η x * dφ x) =
          u x * (fderiv ℝ (fun y => η y * φ y) x) (basisVec i)
        rw [hfun]
        rw [← mul_add, hmul']
      _ = -∫ x in U, gi x * (η x * φ x) := hηφWeak
  have hset :
      (∫ x in U, u x * (η x * dφ x)) =
        -∫ x in U, (η x * gi x + u x * dη x) * φ x := by
    calc
      (∫ x in U, u x * (η x * dφ x)) =
          (∫ x in U, u x * (dη x * φ x) + u x * (η x * dφ x)) -
            ∫ x in U, u x * (dη x * φ x) := by
        rw [integral_add (μ := volume.restrict U) hA hB]
        abel
      _ = (-∫ x in U, gi x * (η x * φ x)) -
            ∫ x in U, u x * (dη x * φ x) := by rw [hbasic]
      _ = -∫ x in U, (η x * gi x + u x * dη x) * φ x := by
        have hCA :
            (∫ x in U, gi x * (η x * φ x) + u x * (dη x * φ x)) =
              (∫ x in U, gi x * (η x * φ x)) +
                ∫ x in U, u x * (dη x * φ x) :=
          integral_add (μ := volume.restrict U) hC hA
        calc
          (-∫ x in U, gi x * (η x * φ x)) -
              ∫ x in U, u x * (dη x * φ x) =
              -((∫ x in U, gi x * (η x * φ x)) +
                ∫ x in U, u x * (dη x * φ x)) := by ring
          _ = -∫ x in U, gi x * (η x * φ x) + u x * (dη x * φ x) := by
            rw [hCA]
          _ = -∫ x in U, (η x * gi x + u x * dη x) * φ x := by
            congr 1
            apply setIntegral_congr_fun hU.measurableSet
            intro x hx
            ring
  have hηOutside : ∀ x, x ∉ U → η x = 0 := by
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun hx' => hx (hηU hx'))
  have hdηOutside : ∀ x, x ∉ U → dη x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport η := fun hxt => hx (hηU hxt)
    simp [dη, fderiv_of_notMem_tsupport (𝕜 := ℝ) hxt]
  have hleftOutside : ∀ x, x ∉ U → η x * u x * dφ x = 0 := by
    intro x hx
    simp [hηOutside x hx]
  have hrightOutside : ∀ x, x ∉ U → (η x * gi x + u x * dη x) * φ x = 0 := by
    intro x hx
    simp [hηOutside x hx, hdηOutside x hx]
  simp only [Measure.restrict_univ]
  change (∫ x, η x * u x * dφ x) =
    -∫ x, (η x * gi x + u x * dη x) * φ x
  calc
    (∫ x, η x * u x * dφ x) = ∫ x in U, η x * u x * dφ x := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact hleftOutside
    _ = -∫ x in U, (η x * gi x + u x * dη x) * φ x := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hset
    _ = -∫ x, (η x * gi x + u x * dη x) * φ x := by
      congr 1
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      exact hrightOutside
  

theorem HasWeakGradientOn.mul_smooth_zeroExtend
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d}
    (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume)
    (hweak : HasWeakGradientOn U u g)
    {η : Vec d → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηCompact : HasCompactSupport η) (hηU : tsupport η ⊆ U) :
    HasWeakGradientOn Set.univ (fun x => η x * u x)
      (fun x => η x • g x + u x • classicalGradient η x) := by
  intro i
  have hi := HasWeakPartialDerivOn.mul_smooth_zeroExtend hU hu (hg i) (hweak i)
    hη hηCompact hηU
  simpa [classicalGradient, Pi.smul_apply, smul_eq_mul] using hi

theorem HasWeakPartialDerivOn.mono {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {i : Fin d} {u gi : Vec d → ℝ}
    (h : HasWeakPartialDerivOn U i u gi) :
    HasWeakPartialDerivOn V i u gi :=
  h.restrict hVOpen hVU

theorem HasWeakGradientOn.mono {d : ℕ}
    {U V : Set (Vec d)} (hVOpen : IsOpen V) (hVU : V ⊆ U)
    {u : Vec d → ℝ} {Du : Vec d → Vec d}
    (h : HasWeakGradientOn U u Du) :
    HasWeakGradientOn V u Du :=
  h.restrict hVOpen hVU

end CKN
