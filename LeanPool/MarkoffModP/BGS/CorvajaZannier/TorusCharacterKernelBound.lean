/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveSupportDeterminant
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Rank-two character kernels in a two-dimensional torus

Two independent integer characters cut out a finite subgroup of a
two-dimensional torus.  This file proves the sharp elementary bound: the
number of common kernel points is at most the absolute determinant of the
two character vectors.  The proof is valid over an arbitrary field and does
not assume that all roots of unity are present.

Applied to three monomials in the support of a plane curve, this bounds the
diagonal support stabilizer by the corresponding support determinant and
hence by twice the product of the two coordinate degrees.
-/

namespace BGS.CorvajaZannier

noncomputable section

/-- The fiber of the `g`-th power map on units. -/
def unitPowerFiber {F : Type*} [Field F] (g : ℕ) (c : Fˣ) :=
  {z : Fˣ // z ^ g = c}

instance unitPowerFiber_finite {F : Type*} [Field F]
    (g : ℕ) [NeZero g] (c : Fˣ) : Finite (unitPowerFiber g c) := by
  classical
  let e : unitPowerFiber g c →
      {x : F // x ∈ Polynomial.nthRoots g (c : F)} := fun z =>
    ⟨z.1.1, (Polynomial.mem_nthRoots (NeZero.pos g)).mpr
      (congrArg (fun u : Fˣ => (u : F)) z.2)⟩
  exact Finite.of_injective e (fun z w h => by
    apply Subtype.ext
    apply Units.ext
    exact congrArg Subtype.val h)

/-- A nonzero power equation in one unit has at most its exponent many
solutions. -/
theorem natCard_unitPowerFiber_le {F : Type*} [Field F]
    (g : ℕ) (hg : 0 < g) (c : Fˣ) :
    Nat.card (unitPowerFiber g c) ≤ g := by
  classical
  by_cases h : Nonempty (unitPowerFiber g c)
  · let z₀ : unitPowerFiber g c := Classical.choice h
    let e : unitPowerFiber g c → rootsOfUnity g F := fun z =>
      ⟨z.1 * z₀.1⁻¹, by
        rw [mem_rootsOfUnity, mul_pow, inv_pow, z.2, z₀.2]
        simp⟩
    have he : Function.Injective e := by
      intro z w hzw
      apply Subtype.ext
      have hval := congrArg (fun u : rootsOfUnity g F => (u.1 : Fˣ)) hzw
      dsimp only [e] at hval
      exact mul_right_cancel hval
    haveI : NeZero g := ⟨hg.ne'⟩
    exact (Nat.card_le_card_of_injective e he).trans
      (card_rootsOfUnity F g)
  · letI : IsEmpty (unitPowerFiber g c) := ⟨fun z => h ⟨z⟩⟩
    simp

/-- The common kernel of two integer characters of a two-dimensional
algebraic torus. -/
def torusCharacterKernel (F : Type*) [Field F]
    (a b c d : ℤ) :=
  {z : Fˣ × Fˣ //
    z.1 ^ a * z.2 ^ b = 1 ∧ z.1 ^ c * z.2 ^ d = 1}

private theorem pow_natAbs_eq_one_of_zpow_eq_one
    {F : Type*} [Field F] (z : Fˣ) (k : ℤ) (h : z ^ k = 1) :
    z ^ k.natAbs = 1 := by
  rcases (Int.natAbs_eq_iff.mp
    (rfl : k.natAbs = k.natAbs)) with hk | hk
  · rw [← zpow_natCast, ← hk]
    exact h
  · have hinv := congrArg Inv.inv h
    rw [hk] at hinv
    simpa [← zpow_neg] using hinv

/-- A nonzero determinant makes the common character kernel finite.  This
coarse finiteness proof embeds it into a product of two root-of-unity groups;
the sharper cardinal estimate below uses Hermite reduction. -/
theorem finite_torusCharacterKernel_of_det_ne_zero
    {F : Type*} [Field F] (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0) :
    Finite (torusCharacterKernel F a b c d) := by
  classical
  let D := a * d - b * c
  have hD : D ≠ 0 := hdet
  have hDpos : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  have hfirst (z : torusCharacterKernel F a b c d) :
      z.1.1 ^ D = 1 := by
    rcases z.2 with ⟨h₁, h₂⟩
    have hprod :
        (z.1.1 ^ a * z.1.2 ^ b) ^ d *
            (z.1.1 ^ c * z.1.2 ^ d) ^ (-b) =
          z.1.1 ^ (a * d + c * (-b)) *
            z.1.2 ^ (b * d + d * (-b)) := by
      simp only [mul_zpow, zpow_mul, zpow_add]
      ac_rfl
    have hx : a * d + c * (-b) = D := by dsimp only [D]; ring
    have hy : b * d + d * (-b) = 0 := by ring
    calc
      z.1.1 ^ D = z.1.1 ^ (a * d + c * (-b)) *
          z.1.2 ^ (b * d + d * (-b)) := by rw [hx, hy]; simp
      _ = (z.1.1 ^ a * z.1.2 ^ b) ^ d *
          (z.1.1 ^ c * z.1.2 ^ d) ^ (-b) := hprod.symm
      _ = 1 := by rw [h₁, h₂]; simp
  have hsecond (z : torusCharacterKernel F a b c d) :
      z.1.2 ^ D = 1 := by
    rcases z.2 with ⟨h₁, h₂⟩
    have hprod :
        (z.1.1 ^ a * z.1.2 ^ b) ^ (-c) *
            (z.1.1 ^ c * z.1.2 ^ d) ^ a =
          z.1.1 ^ (a * (-c) + c * a) *
            z.1.2 ^ (b * (-c) + d * a) := by
      simp only [mul_zpow, zpow_mul, zpow_add]
      ac_rfl
    have hx : a * (-c) + c * a = 0 := by ring
    have hy : b * (-c) + d * a = D := by dsimp only [D]; ring
    calc
      z.1.2 ^ D = z.1.1 ^ (a * (-c) + c * a) *
          z.1.2 ^ (b * (-c) + d * a) := by rw [hx, hy]; simp
      _ = (z.1.1 ^ a * z.1.2 ^ b) ^ (-c) *
          (z.1.1 ^ c * z.1.2 ^ d) ^ a := hprod.symm
      _ = 1 := by rw [h₁, h₂]; simp
  haveI : NeZero D.natAbs := ⟨hDpos.ne'⟩
  let e : torusCharacterKernel F a b c d →
      rootsOfUnity D.natAbs F × rootsOfUnity D.natAbs F := fun z =>
    ⟨⟨z.1.1, by
        rw [mem_rootsOfUnity]
        exact pow_natAbs_eq_one_of_zpow_eq_one z.1.1 D (hfirst z)⟩,
      ⟨z.1.2, by
        rw [mem_rootsOfUnity]
        exact pow_natAbs_eq_one_of_zpow_eq_one z.1.2 D (hsecond z)⟩⟩
  exact Finite.of_injective e (fun z w hzw => by
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun u => u.1.1) hzw
    · exact congrArg (fun u => u.2.1) hzw)

/-- The sharp determinant bound for the common kernel of two characters. -/
theorem natCard_torusCharacterKernel_le_det
    {F : Type*} [Field F] (a b c d : ℤ)
    (hdet : a * d - b * c ≠ 0) :
    Nat.card (torusCharacterKernel F a b c d) ≤
      (a * d - b * c).natAbs := by
  classical
  let g : ℕ := Int.gcd a c
  have hg : 0 < g := by
    rw [Int.gcd_pos_iff]
    by_contra h
    push Not at h
    rcases h with ⟨rfl, rfl⟩
    simp at hdet
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a c
  obtain ⟨c', hc'⟩ := Int.gcd_dvd_right a c
  have ha : a = (g : ℤ) * a' := ha'
  have hc : c = (g : ℤ) * c' := hc'
  let q : ℤ := b * c' - d * a'
  have hdetq : a * d - b * c = -(g : ℤ) * q := by
    dsimp only [q]
    rw [ha, hc]
    ring
  have hq : q ≠ 0 := by
    intro h
    apply hdet
    rw [hdetq, h, mul_zero]
  have hqpos : 0 < q.natAbs := Int.natAbs_pos.mpr hq
  let base := rootsOfUnity q.natAbs F
  let fiber (η : base) := unitPowerFiber g
    (η.1 ^ (-(b * Int.gcdA a c + d * Int.gcdB a c)))
  have hηq (z : torusCharacterKernel F a b c d) :
      z.1.2 ^ q = 1 := by
    rcases z.2 with ⟨h₁, h₂⟩
    have hx : a * c' + c * (-a') = 0 := by
      rw [ha, hc]
      ring
    have hy : b * c' + d * (-a') = q := by
      dsimp only [q]
      ring
    have hprod :
        (z.1.1 ^ a * z.1.2 ^ b) ^ c' *
            (z.1.1 ^ c * z.1.2 ^ d) ^ (-a') =
          z.1.1 ^ (a * c' + c * (-a')) *
            z.1.2 ^ (b * c' + d * (-a')) := by
      simp only [mul_zpow, zpow_mul, zpow_add]
      ac_rfl
    calc
      z.1.2 ^ q = z.1.1 ^ (a * c' + c * (-a')) *
            z.1.2 ^ (b * c' + d * (-a')) := by rw [hx, hy]; simp
      _ = (z.1.1 ^ a * z.1.2 ^ b) ^ c' *
            (z.1.1 ^ c * z.1.2 ^ d) ^ (-a') := hprod.symm
      _ = 1 := by rw [h₁, h₂]; simp
  have hηabs (z : torusCharacterKernel F a b c d) :
      z.1.2 ^ q.natAbs = 1 := by
    rcases (Int.natAbs_eq_iff.mp
      (rfl : q.natAbs = q.natAbs)) with hqcast | hqcast
    · rw [← zpow_natCast, ← hqcast]
      exact hηq z
    · have hinv := congrArg Inv.inv (hηq z)
      rw [hqcast] at hinv
      simpa [← zpow_neg] using hinv
  have hfirst (z : torusCharacterKernel F a b c d) :
      z.1.1 ^ g =
        z.1.2 ^ (-(b * Int.gcdA a c + d * Int.gcdB a c)) := by
    rcases z.2 with ⟨h₁, h₂⟩
    have hbez : (g : ℤ) = a * Int.gcdA a c + c * Int.gcdB a c :=
      Int.gcd_eq_gcd_ab a c
    let A := Int.gcdA a c
    let B := Int.gcdB a c
    let w := b * A + d * B
    have hprod :
        (z.1.1 ^ a * z.1.2 ^ b) ^ A *
            (z.1.1 ^ c * z.1.2 ^ d) ^ B =
          z.1.1 ^ (a * A + c * B) * z.1.2 ^ w := by
      dsimp only [w]
      simp only [mul_zpow, zpow_mul, zpow_add]
      ac_rfl
    have hone : z.1.1 ^ (g : ℤ) * z.1.2 ^ w = 1 := by
      rw [hbez]
      rw [← hprod, h₁, h₂]
      simp
    have hinv : z.1.1 ^ (g : ℤ) = (z.1.2 ^ w)⁻¹ :=
      (mul_eq_one_iff_eq_inv).mp hone
    rw [← zpow_natCast]
    simpa [w, A, B, ← zpow_neg] using hinv
  let e : torusCharacterKernel F a b c d → Sigma fiber := fun z =>
    ⟨⟨z.1.2, by
        rw [mem_rootsOfUnity]
        exact hηabs z⟩,
      ⟨z.1.1, hfirst z⟩⟩
  have he : Function.Injective e := by
    intro z w hzw
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun s : Sigma fiber => s.2.1) hzw
    · exact congrArg (fun s : Sigma fiber => s.1.1) hzw
  haveI : NeZero q.natAbs := ⟨hqpos.ne'⟩
  haveI : NeZero g := ⟨hg.ne'⟩
  letI : Fintype base := Fintype.ofFinite base
  letI (η : base) : Finite (fiber η) := unitPowerFiber_finite g _
  have hbase : Nat.card base ≤ q.natAbs := card_rootsOfUnity F q.natAbs
  have hfiber : ∀ η : base, Nat.card (fiber η) ≤ g := by
    intro η
    exact natCard_unitPowerFiber_le g hg _
  calc
    Nat.card (torusCharacterKernel F a b c d) ≤ Nat.card (Sigma fiber) :=
      Nat.card_le_card_of_injective e he
    _ = ∑ η : base, Nat.card (fiber η) := Nat.card_sigma
    _ ≤ ∑ _η : base, g := Finset.sum_le_sum fun _ _ => hfiber _
    _ = Nat.card base * g := by simp
    _ ≤ q.natAbs * g := Nat.mul_le_mul_right g hbase
    _ = (a * d - b * c).natAbs := by
      rw [hdetq, Int.natAbs_mul]
      simp [Nat.mul_comm]

/-- Diagonal scalings on which every support character of `f` has the same
value.  These are precisely the possible diagonal stabilizers detected from
the monomial support. -/
def planeCurveSupportCharacterStabilizer
    (F : Type*) [Field F] {K : Type*} [Field K]
    (f : MvPolynomial (Fin 2) K) :=
  {z : Fˣ × Fˣ // ∀ r ∈ f.support, ∀ s ∈ f.support,
    z.1 ^ ((s 0 : ℤ) - (r 0 : ℤ)) *
      z.2 ^ ((s 1 : ℤ) - (r 1 : ℤ)) = 1}

/-- A nonzero support determinant bounds every diagonal support stabilizer. -/
theorem natCard_planeCurveSupportCharacterStabilizer_le_supportDet
    {F K : Type*} [Field F] [Field K]
    {f : MvPolynomial (Fin 2) K}
    {r s t : Fin 2 →₀ ℕ}
    (hr : r ∈ f.support) (hs : s ∈ f.support) (ht : t ∈ f.support)
    (hdet : planeCurveSupportDifferenceDet r s t ≠ 0) :
    Nat.card (planeCurveSupportCharacterStabilizer F f) ≤
      (planeCurveSupportDifferenceDet r s t).natAbs := by
  let a : ℤ := (s 0 : ℤ) - (r 0 : ℤ)
  let b : ℤ := (s 1 : ℤ) - (r 1 : ℤ)
  let c : ℤ := (t 0 : ℤ) - (r 0 : ℤ)
  let d : ℤ := (t 1 : ℤ) - (r 1 : ℤ)
  have hdet' : a * d - b * c ≠ 0 := by
    simpa [a, b, c, d, planeCurveSupportDifferenceDet] using hdet
  letI : Finite (torusCharacterKernel F a b c d) :=
    finite_torusCharacterKernel_of_det_ne_zero a b c d hdet'
  let e : planeCurveSupportCharacterStabilizer F f →
      torusCharacterKernel F a b c d := fun z =>
    ⟨z.1, z.2 r hr s hs, z.2 r hr t ht⟩
  have he : Function.Injective e := by
    intro z w hzw
    apply Subtype.ext
    exact congrArg (fun u : torusCharacterKernel F a b c d => u.1) hzw
  calc
    Nat.card (planeCurveSupportCharacterStabilizer F f) ≤
        Nat.card (torusCharacterKernel F a b c d) :=
      Nat.card_le_card_of_injective e he
    _ ≤ (a * d - b * c).natAbs :=
      natCard_torusCharacterKernel_le_det a b c d hdet'
    _ = (planeCurveSupportDifferenceDet r s t).natAbs := by
      simp [a, b, c, d, planeCurveSupportDifferenceDet]

/-- Rank-two support gives the public bidegree bound for every diagonal
support stabilizer. -/
theorem natCard_planeCurveSupportCharacterStabilizer_le_twice_bidegree
    {F K : Type*} [Field F] [Field K]
    {f : MvPolynomial (Fin 2) K}
    (hrank : PlaneCurveSupportHasRankTwo f) :
    Nat.card (planeCurveSupportCharacterStabilizer F f) ≤
      2 * MvPolynomial.degreeOf 0 f * MvPolynomial.degreeOf 1 f := by
  obtain ⟨r, s, t, hr, hs, ht, hdet⟩ := hrank
  exact (natCard_planeCurveSupportCharacterStabilizer_le_supportDet
    (F := F) hr hs ht hdet).trans
      (natAbs_planeCurveSupportDifferenceDet_le_twice_bidegree hr hs ht)

end

end BGS.CorvajaZannier
