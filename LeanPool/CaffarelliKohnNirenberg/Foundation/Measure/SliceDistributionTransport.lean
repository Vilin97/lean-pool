/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Measure.SliceMollifierIdentity

/-!
# Change of variables for mollifier pairings

This module records the two reflection identities that move the mollifier
weight off a function and onto the other factor of an integral. In the
elliptic-regularity analysis of Caffarelli--Kohn--Nirenberg (1982), the
convolution `mollify u ε hε x` is the pairing of `u` against the reflected
kernel `y ↦ mollifier ε hε (x - y)`; identifying the two presentations of this
pairing, with `u` replaced by a weak partial derivative, is what lets a weak
derivative be moved from the function onto the test kernel.

Integrating against the volume measure, the change of variables `y ↦ x - y`
(the `ε`-ball reflection) converts the pairing into the convolution itself.
The second identity combines this reflection with the already-proved integral
form of the weak partial derivative, so that a smooth `ψ` may be differentiated
inside the pairing.
-/

@[expose] public section

open MeasureTheory Metric
open scoped Convolution Topology


noncomputable section

namespace CKN

/-- Integrating a function against the reflected mollifier reproduces its
mollification: the convolution pairing `mollify ψ ε hε x` equals the integral
of `ψ y` against `mollifier ε hε (x - y)` over the ambient volume measure.
This is the change of variables `y ↦ x - y` for the (reflected) mollifier
pairing of Caffarelli--Kohn--Nirenberg (1982). -/
theorem integral_mul_mollifier_sub {d : ℕ} (ψ : Vec d → ℝ) {ε : ℝ} (hε : 0 < ε)
    (x : Vec d) :
    ∫ y, ψ y * mollifier (d := d) ε hε (x - y) ∂MeasureTheory.volume =
      mollify ψ ε hε x := by
  have hmoll :
      mollify ψ ε hε x =
        ∫ t, mollifier (d := d) ε hε t * ψ (x - t) ∂MeasureTheory.volume := by
    simp only [mollify, MeasureTheory.convolution, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
  rw [hmoll]
  have hchange :
      (∫ y, ψ y * mollifier (d := d) ε hε (x - y) ∂MeasureTheory.volume) =
        ∫ t, ψ (x - t) * mollifier (d := d) ε hε t ∂MeasureTheory.volume := by
    have h := (MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume x).integral_comp
      (Homeomorph.subLeft x).measurableEmbedding
      (fun y => ψ y * mollifier (d := d) ε hε (x - y))
    rw [← h]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simp [sub_sub_cancel]
  rw [hchange]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  ring

/-- Differentiating a smooth function inside the reflected mollifier pairing:
for `ContDiff` `ψ`, the integral of `ψ y` against the `i`th partial derivative
of the reflected kernel equals the mollification of the `i`th partial derivative
of `ψ`. The change of variables `y ↦ x - y` reduces the claim to the integral
form of the weak partial derivative of `ψ` on all of space
(Caffarelli--Kohn--Nirenberg, 1982). -/
theorem integral_mul_fderiv_mollifier_sub {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) (x : Vec d) :
    ∫ y, ψ y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i)
        ∂MeasureTheory.volume
      = mollify (fun z => (fderiv ℝ ψ z) (basisVec i)) ε hε x := by
  have hgiCont : Continuous (fun z => (fderiv ℝ ψ z) (basisVec i)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hweak : HasWeakPartialDerivOn (Set.univ : Set (Vec d)) i ψ
      (fun z => (fderiv ℝ ψ z) (basisVec i)) :=
    HasWeakPartialDerivOn.of_contDiff (hψ.of_le (by simp))
  have hmain := integral_fderiv_mollifier_mul_eq_mollify
    (d := d) (U := (Set.univ : Set (Vec d))) (u := ψ)
    (gi := fun z => (fderiv ℝ ψ z) (basisVec i)) (i := i) (x := x)
    hψ.continuous.locallyIntegrable hgiCont.locallyIntegrable hweak hε
    (Set.subset_univ _)
  have hchange :
      (∫ y, ψ y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i)
          ∂MeasureTheory.volume) =
        ∫ t, ψ (x - t) * (fderiv ℝ (mollifier (d := d) ε hε) t) (basisVec i)
          ∂MeasureTheory.volume := by
    have h := (MeasureTheory.Measure.measurePreserving_sub_left MeasureTheory.volume x).integral_comp
      (Homeomorph.subLeft x).measurableEmbedding
      (fun y => ψ y * (fderiv ℝ (mollifier (d := d) ε hε) (x - y)) (basisVec i))
    rw [← h]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with t
    simp [sub_sub_cancel]
  rw [hchange, ← hmain]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  ring

end CKN

end
