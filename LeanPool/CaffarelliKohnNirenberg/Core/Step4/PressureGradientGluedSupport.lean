/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative

/-!
# Support and almost-everywhere stability of weak partial derivatives

Three elementary facts used when weak derivatives produced on small sets are
combined on a larger one: a weak derivative may be replaced by any function
equal to it almost everywhere on the domain; the product of a locally
integrable function with a compactly supported continuous function is
integrable on the domain; and a set integral of a function supported in a
common subset does not see the ambient set.
-/

public section

open MeasureTheory Set
noncomputable section
namespace CKN

/-- A weak partial derivative may be replaced by any function that agrees with
it almost everywhere on the domain: the defining integral identity only sees
the values of the derivative through the ambient measure restricted to `U`. -/
theorem HasWeakPartialDerivOn.congr_deriv_ae {d : ℕ} {U : Set (Vec d)}
    {i : Fin d} {u g h : Vec d → ℝ}
    (hgh : g =ᵐ[volume.restrict U] h)
    (hg : HasWeakPartialDerivOn U i u g) :
    HasWeakPartialDerivOn U i u h := by
  intro φ hφ hφc hφU
  have hInt :
      ∫ x in U, g x * φ x ∂MeasureTheory.volume =
        ∫ x in U, h x * φ x ∂MeasureTheory.volume :=
    MeasureTheory.integral_congr_ae (hgh.mono (fun x hx => by simp [hx]))
  rw [hg φ hφ hφc hφU, hInt]

/-- A locally integrable function times a compactly supported continuous
function is integrable on a measurable domain containing the support of the
continuous factor. -/
theorem integrableOn_mul_continuous_of_locallyIntegrableOn {d : ℕ} {U : Set (Vec d)}
    (hU : MeasurableSet U) {u c : Vec d → ℝ}
    (hu : LocallyIntegrableOn u U volume)
    (hc : Continuous c) (hcc : IsCompact (tsupport c)) (hcU : tsupport c ⊆ U) :
    IntegrableOn (fun x => u x * c x) U volume := by
  have huK : IntegrableOn u (tsupport c) volume :=
    hu.integrableOn_compact_subset hcU hcc
  have h1 : IntegrableOn (fun x => u x * c x) (tsupport c) volume := by
    simpa [smul_eq_mul] using huK.smul_continuousOn hc.continuousOn hcc
  have hzero : ∀ x ∈ U \ tsupport c, u x * c x = 0 := by
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx.2]
  exact h1.of_forall_sdiff_eq_zero hU hzero

/-- A set integral of a function that vanishes off a set `S` agrees on any two
ambient sets containing `S`: the integrand is invisible outside `S`, so neither
ambient set contributes anything beyond it. -/
theorem setIntegral_eq_of_support_subset {d : ℕ} {A B S : Set (Vec d)}
    {F : Vec d → ℝ} (hzero : ∀ x, x ∉ S → F x = 0) (hA : S ⊆ A) (hB : S ⊆ B) :
    ∫ x in A, F x ∂volume = ∫ x in B, F x ∂volume := by
  rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzero x (fun hS => hx (hA hS))),
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzero x (fun hS => hx (hB hS)))]

end CKN
