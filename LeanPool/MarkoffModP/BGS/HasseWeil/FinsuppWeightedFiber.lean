/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantExtensionClosedPlaceCount

/-!
# Weighted degree cancellation over finite-support fibers

This file upgrades the unweighted finite-family constant-extension identity to
finitely supported multiplicities.  The ambient types need not be finite: a
nonzero downstairs coefficient forces every point in its fiber into the
finite upstairs support, so the relevant fiber can be counted there.
-/

namespace Finsupp

/-- Weighted form of the constant-extension degree cancellation.  Suppose
upstairs multiplicities are pulled back from downstairs, upstairs degrees are
obtained by division by `gcd(r, degree)`, and the full fiber has that gcd as
its cardinality.  Then the two finitely supported weighted degree sums agree.

No finiteness assumption is imposed on `Base` or `Up`; only the supports of
the two `Finsupp`s are used as finite indexing sets. -/
theorem sum_mul_degree_eq_of_div_gcd_fibers
    {Base Up : Type*}
    (down : Up → Base)
    (baseDegree : Base → ℕ) (upDegree : Up → ℕ)
    (baseMultiplicity : Base →₀ ℕ)
    (upMultiplicity : Up →₀ ℕ)
    (extensionDegree : ℕ)
    (hmultiplicity : ∀ Q,
      upMultiplicity Q = baseMultiplicity (down Q))
    (hdegree : ∀ Q,
      upDegree Q = baseDegree (down Q) /
        Nat.gcd extensionDegree (baseDegree (down Q)))
    (hfiber : ∀ P,
      Nat.card {Q : Up // down Q = P} =
        Nat.gcd extensionDegree (baseDegree P)) :
    upMultiplicity.sum (fun Q m ↦ m * upDegree Q) =
      baseMultiplicity.sum (fun P m ↦ m * baseDegree P) := by
  classical
  rw [Finsupp.sum, Finsupp.sum]
  have hmaps : ∀ Q ∈ upMultiplicity.support,
      down Q ∈ baseMultiplicity.support := by
    intro Q hQ
    rw [Finsupp.mem_support_iff] at hQ ⊢
    simpa only [← hmultiplicity Q] using hQ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro P hP
  have hfiber_subset : {Q : Up | down Q = P} ⊆
      (upMultiplicity.support : Set Up) := by
    intro Q hQP
    change Q ∈ upMultiplicity.support
    rw [Finsupp.mem_support_iff, hmultiplicity Q, hQP]
    exact Finsupp.mem_support_iff.mp hP
  let : Fintype {Q : Up // down Q = P} :=
    (upMultiplicity.support.finite_toSet.subset hfiber_subset).fintype
  let fiberSupport := upMultiplicity.support.filter (fun Q ↦ down Q = P)
  let fiberEquiv : {Q : Up // Q ∈ fiberSupport} ≃
      {Q : Up // down Q = P} :=
    { toFun := fun Q ↦
        ⟨Q.1, (Finset.mem_filter.mp Q.2).2⟩
      invFun := fun Q ↦
        ⟨Q.1, Finset.mem_filter.mpr ⟨hfiber_subset Q.2, Q.2⟩⟩
      left_inv := fun Q ↦ Subtype.ext rfl
      right_inv := fun Q ↦ Subtype.ext rfl }
  have hcard : fiberSupport.card =
      Nat.gcd extensionDegree (baseDegree P) := by
    calc
      fiberSupport.card = Fintype.card fiberSupport :=
        (Fintype.card_coe fiberSupport).symm
      _ = Fintype.card {Q : Up // down Q = P} :=
        Fintype.card_congr fiberEquiv
      _ = Nat.card {Q : Up // down Q = P} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.gcd extensionDegree (baseDegree P) := hfiber P
  rw [Finset.sum_const_nat]
  · rw [hcard]
    calc
      Nat.gcd extensionDegree (baseDegree P) *
          (baseMultiplicity P *
            (baseDegree P / Nat.gcd extensionDegree (baseDegree P))) =
          baseMultiplicity P *
            (Nat.gcd extensionDegree (baseDegree P) *
              (baseDegree P / Nat.gcd extensionDegree (baseDegree P))) := by
        ac_rfl
      _ = baseMultiplicity P * baseDegree P := by
        rw [Nat.mul_div_cancel'
          (Nat.gcd_dvd_right extensionDegree (baseDegree P))]
  · intro Q hQ
    simp only [hmultiplicity, hdegree]
    rw [(Finset.mem_filter.mp hQ).2]

end Finsupp
