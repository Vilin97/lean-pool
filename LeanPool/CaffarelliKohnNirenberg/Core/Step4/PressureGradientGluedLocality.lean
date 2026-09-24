/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedPartition
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedSupport

/-!
# Weak partial derivatives are a local property

Being the `i`th weak partial derivative is checked against test functions with
compact support, so it is local: if a single locally integrable function is the
`i`th weak partial derivative of `u` on every member of an open cover of `U`,
then it is the `i`th weak partial derivative of `u` on `U` itself.

The proof decomposes a test function with the finite smooth partition of unity
of `exists_smooth_partition_of_unity_of_isCompact`, applies the hypothesis to
each piece, and reassembles the integrals.  The corresponding statement was not
available anywhere: the previously existing interface for weak derivatives
consisted only of restriction, transport and almost-everywhere uniqueness.
-/

@[expose] public section

open MeasureTheory Set
noncomputable section
namespace CKN

/-- Locality of weak partial derivatives.  If `g` is the `i`th weak partial
derivative of `u` on each member of an open cover of `U`, and both `u` and `g`
are locally integrable on `U`, then `g` is the `i`th weak partial derivative of
`u` on `U`.

The cover members are not required to be contained in `U`; only that they cover
`U` and that the identity holds on each of them. -/
theorem hasWeakPartialDerivOn_of_isOpen_cover {d : ℕ} {ι : Type*}
    {U : Set (Vec d)} {V : ι → Set (Vec d)} {i : Fin d} {u g : Vec d → ℝ}
    (hU : MeasurableSet U) (hV : ∀ b, IsOpen (V b))
    (hcover : U ⊆ ⋃ b, V b)
    (hu : LocallyIntegrableOn u U volume)
    (hg : LocallyIntegrableOn g U volume)
    (hloc : ∀ b, HasWeakPartialDerivOn (V b) i u g) :
    HasWeakPartialDerivOn U i u g := by
  classical
  intro φ hφ hφc hφU
  obtain ⟨N, χ, hχsm, hχc, hχsub, hχsum⟩ :=
    exists_smooth_partition_of_unity_of_isCompact hφc.isCompact V hV (hφU.trans hcover)
  set Φ : ℕ → Vec d → ℝ := fun k x => χ k x * φ x with hΦdef
  have hΦsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (Φ k) := fun k => (hχsm k).mul hφ
  have hΦc : ∀ k, HasCompactSupport (Φ k) := fun k => (hχc k).mul_right
  have hΦsupχ : ∀ k, tsupport (Φ k) ⊆ tsupport (χ k) := fun k =>
    closure_mono (Function.support_mul_subset_left _ _)
  have hΦsupφ : ∀ k, tsupport (Φ k) ⊆ tsupport φ := fun k =>
    closure_mono (Function.support_mul_subset_right _ _)
  have hΦU : ∀ k, tsupport (Φ k) ⊆ U := fun k => (hΦsupφ k).trans hφU
  have hsum : ∀ x, ∑ k ∈ Finset.range N, Φ k x = φ x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · calc ∑ k ∈ Finset.range N, Φ k x
          = (∑ k ∈ Finset.range N, χ k x) * φ x := by rw [Finset.sum_mul]
        _ = φ x := by rw [hχsum x hx, one_mul]
    · have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hΦdef, hφx]
  have hφeq : φ = fun y => ∑ k ∈ Finset.range N, Φ k y := funext fun y => (hsum y).symm
  have hdiff : ∀ k, Differentiable ℝ (Φ k) := fun k => (hΦsm k).differentiable (by simp)
  have hfd : ∀ x, (fderiv ℝ φ x) (basisVec i)
      = ∑ k ∈ Finset.range N, (fderiv ℝ (Φ k) x) (basisVec i) := by
    intro x
    have h1 : fderiv ℝ φ x = ∑ k ∈ Finset.range N, fderiv ℝ (Φ k) x := by
      rw [hφeq]
      exact fderiv_fun_sum (fun k _ => (hdiff k) x)
    rw [h1, sum_apply]
  have hDsup : ∀ k, tsupport (fun x => (fderiv ℝ (Φ k) x) (basisVec i)) ⊆ tsupport (Φ k) := by
    intro k
    refine closure_minimal ?_ isClosed_closure
    intro x hx
    by_contra hnot
    refine hx ?_
    change (fderiv ℝ (Φ k) x) (basisVec i) = 0
    rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hnot]
    simp
  have hDcont : ∀ k, Continuous (fun x => (fderiv ℝ (Φ k) x) (basisVec i)) := fun k =>
    ((hΦsm k).continuous_fderiv (by simp)).clm_apply continuous_const
  have hDcompact : ∀ k, IsCompact (tsupport (fun x => (fderiv ℝ (Φ k) x) (basisVec i))) :=
    fun k => (hΦc k).isCompact.of_isClosed_subset isClosed_closure (hDsup k)
  have hIu : ∀ k, IntegrableOn (fun x => u x * (fderiv ℝ (Φ k) x) (basisVec i)) U volume :=
    fun k => integrableOn_mul_continuous_of_locallyIntegrableOn hU hu (hDcont k) (hDcompact k)
      ((hDsup k).trans (hΦU k))
  have hIg : ∀ k, IntegrableOn (fun x => g x * Φ k x) U volume :=
    fun k => integrableOn_mul_continuous_of_locallyIntegrableOn hU hg
      (hΦsm k).continuous (hΦc k).isCompact (hΦU k)
  have hL : ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i) ∂volume
      = ∑ k ∈ Finset.range N, ∫ x in U, u x * (fderiv ℝ (Φ k) x) (basisVec i) ∂volume := by
    rw [← integral_finsetSum _ (fun k _ => hIu k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change u x * (fderiv ℝ φ x) (basisVec i)
      = ∑ k ∈ Finset.range N, u x * (fderiv ℝ (Φ k) x) (basisVec i)
    rw [hfd x, Finset.mul_sum]
  have hpiece : ∀ k ∈ Finset.range N,
      ∫ x in U, u x * (fderiv ℝ (Φ k) x) (basisVec i) ∂volume
        = -∫ x in U, g x * Φ k x ∂volume := by
    intro k hk
    obtain ⟨b, hb⟩ := hχsub k hk
    have hsub : tsupport (Φ k) ⊆ V b := (hΦsupχ k).trans hb
    have h1 : ∫ x in U, u x * (fderiv ℝ (Φ k) x) (basisVec i) ∂volume
        = ∫ x in V b, u x * (fderiv ℝ (Φ k) x) (basisVec i) ∂volume := by
      refine setIntegral_eq_of_support_subset (S := tsupport (Φ k)) ?_ (hΦU k) hsub
      intro x hx
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp
    have h2 : ∫ x in V b, g x * Φ k x ∂volume = ∫ x in U, g x * Φ k x ∂volume := by
      refine setIntegral_eq_of_support_subset (S := tsupport (Φ k)) ?_ hsub (hΦU k)
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport hx]
      simp
    rw [h1, hloc b (Φ k) (hΦsm k) (hΦc k) hsub, h2]
  have hR : ∫ x in U, g x * φ x ∂volume
      = ∑ k ∈ Finset.range N, ∫ x in U, g x * Φ k x ∂volume := by
    rw [← integral_finsetSum _ (fun k _ => hIg k)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change g x * φ x = ∑ k ∈ Finset.range N, g x * Φ k x
    rw [← Finset.mul_sum, hsum x]
  rw [hL, hR, Finset.sum_congr rfl hpiece, Finset.sum_neg_distrib]

end CKN
