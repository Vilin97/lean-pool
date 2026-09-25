/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.SymmetryClassification

/-!
Signed coordinate transformations preserve the kernel and commute with infimal smoothing.
-/

@[expose] public section

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair

theorem lowerKernelPhi_signed_invariant {p r theta : ℝ} (hp : 2 < p)
    (hr : r ≠ 0) {Q Qdual : Point d → Point d}
    (hsym : SignedLpSymmetry p Q Qdual) (x : Point d) :
    lowerKernelPhi r theta (Q x) = lowerKernelPhi r theta x := by
  rw [lowerKernelPhi_eq_norm_power hr, lowerKernelPhi_eq_norm_power hr,
    show lpNorm r (Q x) = lpNorm r x by
      change O3.lpNorm r (Q x) = O3.lpNorm r x
      exact signedLpSymmetry_lpNorm_all hp hsym x]

lemma signedLpLinearMap_injective {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual) :
    Function.Injective (signedLpLinearMap Q Qdual hsym) := by
  intro x y hxy
  have hsub : Q (x - y) = 0 := by
    change (signedLpLinearMap Q Qdual hsym) (x - y) = 0
    rw [map_sub, hxy, sub_self]
  have hn := hsym.1 (x - y)
  change O3.lpNorm p (Q (x - y)) = O3.lpNorm p (x - y) at hn
  rw [hsub, O3.lpNorm_zero (by linarith : 0 < p)] at hn
  have hz : x - y = 0 := (O3.lpNorm_eq_zero_iff (by linarith : 0 < p)).mp hn.symm
  exact sub_eq_zero.mp hz

lemma signedLpLinearMap_surjective {p : ℝ} (hp : 2 < p)
    {Q Qdual : Point d → Point d} (hsym : SignedLpSymmetry p Q Qdual) :
    Function.Surjective (signedLpLinearMap Q Qdual hsym) :=
  LinearMap.surjective_of_injective (signedLpLinearMap_injective hp hsym)

lemma smoothingCost_signed_change {p r theta chi : ℝ} (hp : 2 < p)
    (hr : r ≠ 0) (kernel : SmoothingKernelData p d)
    (hphi : kernel.phi = lowerKernelPhi r theta)
    (ell : Point d → ℝ) {Q Qdual : Point d → Point d}
    (hsym : SignedLpSymmetry p Q Qdual) (x v : Point d) :
    smoothingCost kernel chi (fun z ↦ ell (Q z)) x v =
    smoothingCost kernel chi ell (Q x) (Q v) := by
  unfold smoothingCost
  change ell (Q (x + v)) + chi * kernel.phi ((1 / chi) • v) =
    ell (Q x + Q v) + chi * kernel.phi ((1 / chi) • Q v)
  rw [signedLpSymmetry_Q_add hsym]
  have hscale : Q ((1 / chi) • v) = (1 / chi) • Q v :=
    signedLpSymmetry_Q_smul hsym _ _
  rw [hphi, ← hscale, lowerKernelPhi_signed_invariant hp hr hsym]

/-- Exact change of variables in the literal infimum. -/
theorem localSmoothingValue_signed_equivariant {p r theta chi : ℝ}
    (hp : 2 < p) (hr : r ≠ 0) (kernel : SmoothingKernelData p d)
    (hphi : kernel.phi = lowerKernelPhi r theta)
    (ell : Point d → ℝ) {Q Qdual : Point d → Point d}
    (hsym : SignedLpSymmetry p Q Qdual) (x : Point d) :
    localSmoothingValue kernel chi (fun z ↦ ell (Q z)) x =
      localSmoothingValue kernel chi ell (Q x) := by
  unfold localSmoothingValue
  congr 1
  ext a
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨Q v, (smoothingCost_signed_change hp hr kernel hphi ell hsym x v)⟩
  · rintro ⟨w, rfl⟩
    obtain ⟨v, hv⟩ := signedLpLinearMap_surjective hp hsym w
    change Q v = w at hv
    subst w
    exact ⟨v, (smoothingCost_signed_change hp hr kernel hphi ell hsym x v).symm⟩

theorem repairKernel_phi_signed_invariant {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    ∀ (Q Qdual : Point d → Point d), SignedLpSymmetry p Q Qdual →
      ∀ x, (repairKernel p d).phi (Q x) = (repairKernel p d).phi x := by
  intro Q Qdual hsym x
  exact lowerKernelPhi_signed_invariant hp
    (by linarith [two_lt_kernelR0 hp hd] : kernelR0 p d ≠ 0) hsym x

theorem repairKernel_smooth_value_signed_equivariant {p : ℝ} {d : ℕ}
    (hp : 2 < p) (hd : 2 ≤ d) :
    ∀ (chi : ℝ), 0 < chi → ∀ (ell : Point d → ℝ)
      (Q Qdual : Point d → Point d),
      O3.IsConvexObjective ell → IsOneLipschitz p ell →
      SignedLpSymmetry p Q Qdual → ∀ x,
      ((repairKernel p d).smooth chi (fun z ↦ ell (Q z))).value x =
        ((repairKernel p d).smooth chi ell).value (Q x) := by
  intro chi hchi ell Q Qdual hconv hlip hsym x
  exact localSmoothingValue_signed_equivariant hp
    (by linarith [two_lt_kernelR0 hp hd] : kernelR0 p d ≠ 0)
    (repairKernelBase p d) rfl ell hsym x

end V7.Stage5AboveTwoLowerS5A2Envelope
