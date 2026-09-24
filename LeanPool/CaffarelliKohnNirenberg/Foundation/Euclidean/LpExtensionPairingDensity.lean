/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtension
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.Holder

/-! # Density form of the distributional pairing identity

A continuous dual pairing on `Lᵖ` agrees on a dense set if it agrees there
pointwise.  Here the dense set is that of classes represented by smooth
compactly supported functions, which is the form in which the distributional
identity is checked against test functions in the Caffarelli–Kohn–Nirenberg
argument.  The continuous linear maps `testPairing` implement the pairing
against a fixed dual class and are the device used to pass the identity from
the dense set to every `Lᵖ` input.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Continuous test-function pairing used to pass operator identities through Lᵖ limits. -/
def testPairing {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) :
    Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ g).comp
    (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ))

private lemma testPairing_apply {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (g : Lp ℝ q (volume : Measure Vec3)) (f : Lp ℝ p (volume : Measure Vec3)) :
    testPairing g f = ∫ x, f x * g x := by
  change (ContinuousLinearMap.lpPairing volume p q (ContinuousLinearMap.mul ℝ ℝ) f) g = _
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  rfl

/-- The distributional pairing identity for an `Lᵖ` extension, assumed on the
dense set of smooth compactly supported classes, holds for every `Lᵖ` input.
This is the Caffarelli–Kohn–Nirenberg distributional pairing step in the form
used when the identity is available against smooth test functions. -/
theorem lpExtension_pairing_of_smooth_identity
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {C : ℝ} (hp : p ≠ ∞) (h : LpExtensionInput p C)
    {test rhs : Vec3 → ℝ} (htest : MemLp test q volume) (hrhs : MemLp rhs q volume)
    (hidentity : ∀ F : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∫ x, lpExtensionRepresentative hp h F x * test x) = ∫ x, F x * rhs x)
    {f : Vec3 → ℝ} (hf : MemLp f p volume) :
    (∫ x, lpExtensionRepresentative hp h f x * test x) = ∫ x, f x * rhs x := by
  let s : Set (Lp ℝ p (volume : Measure Vec3)) :=
    {v | ∃ F : Vec3 → ℝ, (v : Vec3 → ℝ) =ᵐ[volume] F ∧
      HasCompactSupport F ∧ ContDiff ℝ (⊤ : ℕ∞) F}
  have hs : Dense s := by
    apply (MeasureTheory.Lp.dense_hasCompactSupport_contDiff
      (F := ℝ) (p := p) (μ := (volume : Measure Vec3)) hp).mono
    rintro v ⟨F, hvF, hFc, hF⟩
    exact ⟨F, hvF, hFc, hF⟩
  let testLp : Lp ℝ q (volume : Measure Vec3) := htest.toLp test
  let rhsLp : Lp ℝ q (volume : Measure Vec3) := hrhs.toLp rhs
  let left : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    (testPairing (p := p) (q := q) testLp).comp (lpExtensionCore hp h)
  let right : Lp ℝ p (volume : Measure Vec3) →L[ℝ] ℝ :=
    testPairing (p := p) (q := q) rhsLp
  have hEq : left = right := by
    apply ContinuousLinearMap.ext
    intro u
    have hfun : (fun v : Lp ℝ p (volume : Measure Vec3) => left v) =
        (fun v => right v) := by
      apply Continuous.ext_on hs
        left.continuous right.continuous
      intro v hv
      obtain ⟨F, hvF, hFc, hF⟩ := hv
      have hFmem : MemLp F p volume :=
        hF.continuous.memLp_of_hasCompactSupport hFc
      have hFv : hFmem.toLp F = v :=
        Lp.ext (hFmem.coeFn_toLp.trans hvF.symm)
      have hcore : (lpExtensionCore hp h v : Vec3 → ℝ) =ᵐ[volume]
          lpExtensionRepresentative hp h F := by
        have hrep := lpExtensionRepresentative_ae_eq_core hp h hFmem
        rw [hFv] at hrep
        exact hrep.symm
      have hleft : left v = ∫ x, lpExtensionRepresentative hp h F x * test x := by
        change (testPairing testLp) (lpExtensionCore hp h v) = _
        rw [testPairing_apply]
        apply integral_congr_ae
        filter_upwards [hcore, htest.coeFn_toLp] with x hx hy
        rw [hx, hy]
      have hright : right v = ∫ x, F x * rhs x := by
        change (testPairing rhsLp) v = _
        rw [testPairing_apply]
        apply integral_congr_ae
        filter_upwards [hrhs.coeFn_toLp, hvF] with x hx hy
        rw [hx, hy]
      rw [hleft, hright]
      exact hidentity F hF hFc
    exact congrFun hfun u
  have hpair : left (hf.toLp f) = right (hf.toLp f) := by rw [hEq]
  have hpair' : (testPairing testLp) (lpExtensionCore hp h (hf.toLp f)) =
      (testPairing rhsLp) (hf.toLp f) := hpair
  have hrep : lpExtensionRepresentative hp h f =ᵐ[volume]
      (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) :=
    lpExtensionRepresentative_ae_eq_core hp h hf
  calc
    ∫ x, lpExtensionRepresentative hp h f x * test x =
        ∫ x, (lpExtensionCore hp h (hf.toLp f) : Vec3 → ℝ) x * test x := by
      apply integral_congr_ae
      filter_upwards [hrep] with x hx
      rw [hx]
    _ = (testPairing testLp) (lpExtensionCore hp h (hf.toLp f)) := by
      rw [testPairing_apply]
      apply integral_congr_ae
      filter_upwards [htest.coeFn_toLp] with x hx
      rw [hx]
    _ = (testPairing rhsLp) (hf.toLp f) := hpair'
    _ = ∫ x, (hf.toLp f : Vec3 → ℝ) x * rhs x := by
      rw [testPairing_apply]
      apply integral_congr_ae
      filter_upwards [hrhs.coeFn_toLp] with x hx
      rw [hx]
    _ = ∫ x, f x * rhs x := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp] with x hx
      rw [hx]

end CKN.Foundation.Euclidean
