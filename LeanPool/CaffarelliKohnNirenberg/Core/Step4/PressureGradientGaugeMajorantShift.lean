/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRemainder

/-!
# Constant shifts of a weak spatial derivative

The pressure of a suitable weak solution is determined only up to a function
of time.  Subtracting such a function leaves every weak spatial derivative of
the pressure slice unchanged, so a slice estimate proved for the shifted
pressure is an estimate for the original pressure gradient.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- A constant function has vanishing weak spatial derivative. -/
theorem hasWeakPartialDerivOn_const {B : Set Vec3} (hB : IsOpen B)
    (c : ℝ) (k : Fin 3) :
    HasWeakPartialDerivOn B k (fun _ => c) (fun _ => 0) := by
  have h := hasWeakPartialDerivOn_classicalGradient hB k
    (contDiffOn_const (c := c) (s := B) :
      ContDiffOn ℝ (1 : ℕ∞) (fun _ : Vec3 => c) B)
  simpa only [classicalGradient_apply, fderiv_const_apply, zero_apply] using h

/-- Adding a constant to the function leaves a weak spatial derivative
unchanged. -/
theorem hasWeakPartialDerivOn_add_const {B : Set Vec3} (hB : IsOpen B)
    {u g : Vec3 → ℝ} {k : Fin 3}
    (hu : LocallyIntegrableOn u B volume) (hg : LocallyIntegrableOn g B volume)
    (hug : HasWeakPartialDerivOn B k u g) (c : ℝ) :
    HasWeakPartialDerivOn B k (fun x => u x + c) g := by
  have h := hasWeakPartialDerivOn_add hB hug (hasWeakPartialDerivOn_const hB c k)
    hu (locallyIntegrableOn_const c) hg (locallyIntegrableOn_const 0)
  simpa only [add_zero] using h

/-- Subtracting a constant from the function leaves a weak spatial derivative
unchanged. -/
theorem hasWeakPartialDerivOn_sub_const {B : Set Vec3} (hB : IsOpen B)
    {u g : Vec3 → ℝ} {k : Fin 3}
    (hu : LocallyIntegrableOn u B volume) (hg : LocallyIntegrableOn g B volume)
    (hug : HasWeakPartialDerivOn B k u g) (c : ℝ) :
    HasWeakPartialDerivOn B k (fun x => u x - c) g := by
  have h := hasWeakPartialDerivOn_add_const hB hu hg hug (-c)
  simpa only [sub_eq_add_neg] using h

end CKN.Core.Step4
