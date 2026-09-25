/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch04.Measurability
public import LeanPool.CoarseGraining.Homogenization.Probability.LocalObservable
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.SliceMeasurability
public import LeanPool.CoarseGraining.Homogenization.Probability.RegCoeffField.RestrictionBridge

/-! # Local Coefficient -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch04

open MeasureTheory

/-!
# Local coefficient observables (carrier re-type, Packet P5e)

This file starts the Ch4 theorem surface for coefficient-field observables.
The primitive observable is the smooth local test used to generate
the restriction-local observable interface; downstream code should compose from
bundled `RestrictionObservable`s instead of reproving measurability in Chapter 5.

Following the carrier redesign, the local test observable is evaluated on the
honest sample `a.toFun` of a carrier field `a : RegCoeffField d`.  Its locality
is established by the **carrier mixing identity**: the smooth local test is a
finite `(e' i · e j)`-weighted sum of the localized linear entry-test generators
`entryTestR i j φ` of the carrier, each of which is genuinely `LocalSigmaR U`-
measurable (probe supported in `U`), hence restriction-local by
`localSigmaR_le_restrictionSigmaR`.  (The observation set's measurability is a
D7-approved side-condition making `RestrictionSigmaR` well defined.)

Reference: the paper (Armstrong–Kuusi–Loher, to appear).
-/

/-- **The carrier mixing identity for the smooth local test.**  The smooth local
test on the honest sample of a carrier field is a finite `(e' i · e j)`-weighted
sum of localized linear entry-test generators of the carrier field.  It is proved
by expanding the bilinear form and splitting the integral term-by-term (each term
integrable: locally-integrable carrier entry times bounded compactly-supported
probe). -/
theorem localTestObservable_toFun_eq_sum_entryTestR {d : ℕ}
    (e e' : Vec d) {φ : Vec d → ℝ} (hφ : IsProbeR φ) (a : RegCoeffField d) :
    localTestObservable e e' φ a.toFun =
      ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a := by
  have hpt : ∀ x : Vec d,
      vecDot e' (matVecMul (a.toFun x) e) * φ x =
        ∑ i, ∑ j, (e' i * e j) * (a x i j * φ x) := by
    intro x
    simp only [vecDot, matVecMul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hintegrable : ∀ i j : Fin d,
      Integrable (fun x => (e' i * e j) * (a x i j * φ x)) volume :=
    fun i j => (integrable_entry_mul_probe i j hφ a).const_mul _
  calc
    localTestObservable e e' φ a.toFun
        = ∫ x, ∑ i, ∑ j, (e' i * e j) * (a x i j * φ x) ∂volume := by
          unfold localTestObservable
          exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, ∫ x, ∑ j, (e' i * e j) * (a x i j * φ x) ∂volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          exact integrable_finsetSum _ (fun j _ => hintegrable i j)
    _ = ∑ i, ∑ j, ∫ x, (e' i * e j) * (a x i j * φ x) ∂volume := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [MeasureTheory.integral_finsetSum]
          intro j _
          exact hintegrable i j
    _ = ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
          rw [integral_const_mul]
          rfl

namespace RestrictionObservable

/-- The smooth coefficient-field test observable, evaluated on the honest sample,
bundled with its Ch4 locality proof.  The observation-set measurability `hU` is
the D7-approved side-condition making `RestrictionSigmaR` well defined. -/
noncomputable def localTest {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) :
    RestrictionObservable d U ℝ where
  measurableSet := hU
  toFun := fun a => localTestObservable e e' φ a.toFun
  isLocal := by
    have hφ : IsProbeR φ := IsProbeR.of_smooth hφ_cont hφ_compact
    have hsupp : Function.support φ ⊆ U := (subset_tsupport φ).trans hφ_support
    have hrw :
        (fun a : RegCoeffField d => localTestObservable e e' φ a.toFun) =
          fun a => ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a := by
      funext a
      exact localTestObservable_toFun_eq_sum_entryTestR e e' hφ a
    show @Measurable (RegCoeffField d) ℝ (RestrictionSigmaR U hU) _
      (fun a => localTestObservable e e' φ a.toFun)
    rw [hrw]
    let : MeasurableSpace (RegCoeffField d) := LocalSigmaR U
    have hlocal :
        Measurable
          (fun a : RegCoeffField d => ∑ i, ∑ j, (e' i * e j) * entryTestR i j φ a) := by
      refine Finset.measurable_sum _ (fun i _ => Finset.measurable_sum _ (fun j _ => ?_))
      exact (measurable_entryTestR_localSigmaR i j hφ hsupp).const_mul _
    exact hlocal.mono (localSigmaR_le_restrictionSigmaR U hU) le_rfl

@[simp]
theorem localTest_apply {d : ℕ} {U : Set (Vec d)} (hU : MeasurableSet U)
    (e e' : Vec d) {φ : Vec d → ℝ}
    (hφ_cont : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_support : tsupport φ ⊆ U) (a : RegCoeffField d) :
    localTest hU e e' hφ_cont hφ_compact hφ_support a =
      localTestObservable e e' φ a.toFun :=
  rfl

end RestrictionObservable

end Ch04
end Book
end Homogenization
