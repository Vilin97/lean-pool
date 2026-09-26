/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInversionCount

/-!
# Finite-period inversion sums

This file supplies the finite counting normalization used in the proof of
paper Lemma `lem:invtau` (Lemma 4.10).  The public definition of
`kInversionCount` normalizes the first coordinate of an inversion, whereas
the paper sums over representatives whose second coordinate lies in a
fundamental period.  The first theorem proves that these two choices count
the same period orbits.  The second theorem decomposes that count into the
northwest quadrants which are already identified with complementary divisor
ranks in `ThetaNonrecurrence`.
-/

@[expose] public section

namespace Bananas

open Utilities

/-- Reduction of an affine permutation's values to one fundamental period. -/
def affineResidueMap (k : ℕ) (tau : ℤ → ℤ) (hk : 0 < k) (b : Fin k) : Fin k :=
  ⟨((tau b) % k).toNat, by
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    have h0 : 0 ≤ (tau b) % k := Int.emod_nonneg _ (by omega)
    have hlt : (tau b) % k < k := Int.emod_lt_of_pos _ hkZ
    exact (Int.toNat_lt h0).mpr hlt⟩

/-- The value-residue map of a bijective affine permutation is injective.
Thus a transmission permutation permutes the `k` torsion residue classes,
which is the finite reindexing step in Lemma 4.10. -/
theorem affineResidueMap_injective
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau) :
    Function.Injective (affineResidueMap k tau hk) := by
  intro b c hbc
  have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
  have hMod : tau b % k = tau c % k := by
    have h := congrArg Fin.val hbc
    change (tau b % k).toNat = (tau c % k).toNat at h
    have h' := congrArg (fun x : ℕ => (x : ℤ)) h
    have hb0 : 0 ≤ tau b % k := Int.emod_nonneg _ (by omega)
    have hc0 : 0 ≤ tau c % k := Int.emod_nonneg _ (by omega)
    rw [Int.toNat_of_nonneg hb0, Int.toNat_of_nonneg hc0] at h'
    exact h'
  have hDiv : (k : ℤ) ∣ tau b - tau c :=
    (Int.dvd_iff_emod_eq_zero).mpr
      ((Int.emod_eq_emod_iff_emod_sub_eq_zero).mp hMod)
  obtain ⟨q, hq⟩ := hDiv
  have hValue : tau b = tau c + q * k := by
    linarith
  have hTranslate : tau (c + q * k) = tau c + q * k := by
    simpa [mul_comm] using hAffine.iterate_int (c : ℤ) q
  have hIndex : (b : ℤ) = c + q * k := hBij.injective (by
    rw [hTranslate]
    exact hValue)
  have hb0 : 0 ≤ (b : ℤ) := by exact_mod_cast Nat.zero_le b.val
  have hbK : (b : ℤ) < k := by exact_mod_cast b.isLt
  have hc0 : 0 ≤ (c : ℤ) := by exact_mod_cast Nat.zero_le c.val
  have hcK : (c : ℤ) < k := by exact_mod_cast c.isLt
  have hq0 : q = 0 := by
    by_contra hq0
    rcases lt_or_gt_of_ne hq0 with hqneg | hqpos
    · have : (b : ℤ) < 0 := by nlinarith
      omega
    · have : (k : ℤ) ≤ (b : ℤ) := by nlinarith
      omega
  apply Fin.ext
  exact_mod_cast (by rw [hIndex, hq0]; ring : (b : ℤ) = c)

/-- Consequently, an affine bijection permutes the finite residue type. -/
theorem affineResidueMap_bijective
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hBij : Function.Bijective tau) (hAffine : IsKAffine k tau) :
    Function.Bijective (affineResidueMap k tau hk) := by
  refine ⟨affineResidueMap_injective hk hBij hAffine, ?_⟩
  exact Finite.surjective_of_injective
    (affineResidueMap_injective hk hBij hAffine)

/-- Normalizing either coordinate of every inversion gives the same number
of affine-period inversion classes. -/
theorem kInversions_ncard_eq_kInversionsBySecond
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) :
    (kInversions k tau).ncard = (kInversionsBySecond k tau).ncard := by
  let normalizeSecond : (ℤ × ℤ) → (ℤ × ℤ) := fun p =>
    (p.1 - (p.2 / k) * k, p.2 % k)
  apply Set.ncard_congr (fun p _ => normalizeSecond p)
  · intro p hp
    apply inversion_normalize_second_coordinate hk hAffine
    exact ⟨hp.1, hp.2.1⟩
  · rintro ⟨x, y⟩ ⟨x', y'⟩ hxy hxy' heq
    change (x - (y / k) * k, y % k) =
      (x' - (y' / k) * k, y' % k) at heq
    injection heq with hFirst hSecond
    have hyRepr : y = y % k + (y / k) * k := by
      simpa [add_comm, mul_comm] using
        int_eq_emod_add_ediv_period (k := k) hk (b := y)
    have hy'Repr : y' = y' % k + (y' / k) * k := by
      simpa [add_comm, mul_comm] using
        int_eq_emod_add_ediv_period (k := k) hk (b := y')
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    have hx0 : 0 ≤ x := hxy.2.2.1
    have hxk : x < k := hxy.2.2.2
    have hx'0 : 0 ≤ x' := hxy'.2.2.1
    have hx'k : x' < k := hxy'.2.2.2
    have hQuotient : y / k = y' / k := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hmul : (y / k) * (k : ℤ) + k ≤ (y' / k) * k := by
          nlinarith
        omega
      · have hmul : (y' / k) * (k : ℤ) + k ≤ (y / k) * k := by
          nlinarith
        omega
    have hx : x = x' := by
      rw [hQuotient] at hFirst
      omega
    have hy : y = y' := by omega
    exact Prod.ext hx hy
  · rintro ⟨m, n⟩ hmn
    let p : ℤ × ℤ := (m % k, n - (m / k) * k)
    have hp : p ∈ kInversions k tau := by
      apply inversion_normalize_first_coordinate hk hAffine
      exact ⟨hmn.1, hmn.2.1⟩
    refine ⟨p, hp, ?_⟩
    have hkZ : (0 : ℤ) < k := by exact_mod_cast hk
    have hn0 : 0 ≤ n := hmn.2.2.1
    have hnk : n < k := hmn.2.2.2
    have hnMod : n % (k : ℤ) = n := Int.emod_eq_of_lt hn0 hnk
    have hnDiv : n / (k : ℤ) = 0 := by
      apply Int.ediv_eq_zero_of_lt_abs hn0
      rw [abs_of_pos hkZ]
      exact hnk
    have hpSecondMod : (n - (m / k) * k) % (k : ℤ) = n := by
      calc
        (n - (m / k) * k) % (k : ℤ) =
            (n + k * (-(m / k))) % k := by congr 2 ; ring
        _ = n % k := Int.add_mul_emod_self_left n k (-(m / k))
        _ = n := hnMod
    have hpSecondDiv : (n - (m / k) * k) / (k : ℤ) = -(m / k) := by
      calc
        (n - (m / k) * k) / (k : ℤ) =
            (n + k * (-(m / k))) / k := by congr 2 ; ring
        _ = n / k + (-(m / k)) :=
          Int.add_mul_ediv_left n (-(m / k)) (by omega)
        _ = -(m / k) := by rw [hnDiv]; omega
    have hmRepr : m = m % k + (m / k) * k := by
      simpa [add_comm, mul_comm] using
        int_eq_emod_add_ediv_period (k := k) hk (b := m)
    change (m % k - ((n - (m / k) * k) / k) * k,
      (n - (m / k) * k) % k) = (m, n)
    rw [hpSecondDiv, hpSecondMod]
    apply Prod.ext
    · nlinarith [hmRepr]
    · rfl

/-- In the second-coordinate normalization, the fiber over `b` is exactly
the northwest quadrant at the graph of `tau`. -/
noncomputable def kInversionsBySecondEquivNorthwestSigma
    (k : ℕ) (tau : ℤ → ℤ) :
    {p // p ∈ kInversionsBySecond k tau} ≃
      Σ b : Fin k, {m // m ∈ northwestSet tau (tau b + 1) b} where
  toFun p := by
    have hp0 : 0 ≤ p.val.2 := p.property.2.2.1
    have hpCast : (p.val.2.toNat : ℤ) = p.val.2 :=
      Int.toNat_of_nonneg hp0
    have hpk : p.val.2.toNat < k := by
      have hpkZ : (p.val.2.toNat : ℤ) < k := by
        rw [hpCast]
        exact p.property.2.2.2
      exact_mod_cast hpkZ
    let b : Fin k := ⟨p.val.2.toNat, hpk⟩
    have hb : (b : ℤ) = p.val.2 := by
      simp [b, Int.toNat_of_nonneg hp0]
    refine ⟨b, ⟨p.val.1, ?_⟩⟩
    change p.val.1 < (b : ℤ) ∧ tau b + 1 ≤ tau p.val.1
    rw [hb]
    have hOrder : p.val.1 < p.val.2 := p.property.1
    have hTau : tau p.val.1 > tau p.val.2 := p.property.2.1
    exact ⟨hOrder, by omega⟩
  invFun q := by
    refine ⟨(q.2.val, (q.1.val : ℤ)), ?_⟩
    change q.2.val < (q.1.val : ℤ) ∧
      tau q.2.val > tau (q.1.val : ℤ) ∧
      0 ≤ (q.1.val : ℤ) ∧ (q.1.val : ℤ) < k
    have hq := q.2.property
    change q.2.val < (q.1 : ℤ) ∧
      tau (q.1 : ℤ) + 1 ≤ tau q.2.val at hq
    exact ⟨hq.1, by omega, by omega, by exact_mod_cast q.1.isLt⟩
  left_inv p := by
    apply Subtype.ext
    change (p.val.1, (p.val.2.toNat : ℤ)) = p.val
    apply Prod.ext
    · rfl
    · exact Int.toNat_of_nonneg p.property.2.2.1
  right_inv q := by
    rcases q with ⟨⟨b, hb⟩, m⟩
    rfl

/-- The `k`-inversion count is a finite sum of northwest quadrant sizes,
with one summand for each value in a fundamental period. -/
theorem kInversionCount_eq_sum_northwest
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : 0 < k) (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau) :
    kInversionCount k tau =
      ∑ b : Fin k, (northwestSet tau (tau b + 1) b).ncard := by
  obtain ⟨sigma, hSigmaTau, -⟩ :=
    transmissionPermutation_rankSlipFace M D hconn tau hTau
  have hFinite : ∀ b : Fin k,
      (northwestSet tau (tau b + 1) b).Finite := by
    intro b
    rw [← hSigmaTau]
    exact sigma.nw_finite _ _
  let (b : Fin k) : Fintype
      {m // m ∈ northwestSet tau (tau b + 1) b} :=
    (hFinite b).fintype
  calc
    kInversionCount k tau = (kInversionsBySecond k tau).ncard :=
      kInversions_ncard_eq_kInversionsBySecond hk hAffine
    _ = Nat.card {p // p ∈ kInversionsBySecond k tau} := by
      rw [Nat.card_coe_set_eq]
    _ = Nat.card (Σ b : Fin k,
        {m // m ∈ northwestSet tau (tau b + 1) b}) :=
      Nat.card_congr (kInversionsBySecondEquivNorthwestSigma k tau)
    _ = ∑ b : Fin k,
        Nat.card {m // m ∈ northwestSet tau (tau b + 1) b} :=
      Nat.card_sigma
    _ = ∑ b : Fin k,
        (northwestSet tau (tau b + 1) b).ncard := by
      apply Finset.sum_congr rfl
      intro b _
      exact Nat.card_coe_set_eq _

/-- Rank-theoretic form of the finite inversion-row sum.  Each northwest
fiber is the complementary rank appearing in paper Lemma `lem:tauChars`.
This is the finite, Lean-ready starting point for the inclusion--exclusion
calculation in Lemma 4.10. -/
theorem intCast_kInversionCount_eq_sum_complement_rank
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph)
    (k : ℕ) (tau : ℤ → ℤ)
    (hk : 0 < k) (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau) :
    (kInversionCount k tau : ℤ) =
      ∑ b : Fin k,
        (rank M.graph
          (canonicalDivisor M.graph - D -
            (tau b) • oneChip M.u + (b : ℤ) • oneChip M.v) + 1) := by
  rw [kInversionCount_eq_sum_northwest M D hconn k tau hk hTau hAffine]
  push_cast
  apply Finset.sum_congr rfl
  intro b _
  exact (transmission_complement_rank_eq_northwest_ncard
    M D hconn tau hTau (tau b) b).symm

end Bananas
