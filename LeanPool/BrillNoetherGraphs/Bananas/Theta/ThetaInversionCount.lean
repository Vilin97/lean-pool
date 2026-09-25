/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence
import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineInversionFinite
import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ExactTorsionAPI

/-!
# Genus-two transmission inversions

This file begins the formalization of paper Lemma `lem:invtau` (Lemma 4.10).
The first ingredient is the paper's pointwise construction: a rank-zero,
degree-one twist determines a unique inversion crossing the corresponding
row and column of the transmission permutation.
-/

namespace Bananas

open Utilities

/-- The same `k`-inversion classes, represented by putting the *second*
coordinate in the fundamental period.  The proof of Lemma 4.10 sums the
inversion rows in precisely this normalization.  We retain the original
`kInversions` definition (which normalizes the first coordinate) for the
public K-general-transmission contract. -/
def kInversionsBySecond (k : ℕ) (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  {p | p.1 < p.2 ∧ τ p.1 > τ p.2 ∧ 0 ≤ p.2 ∧ p.2 < k}

/-- The effective degree-one members of the finite torsion orbit of `D`.
This is the concrete `Fin k` model for the paper's set of effective classes
in `T_D^1`. -/
def effectiveDegreeOneTwistResidues
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) : Set (Fin k) :=
  {b | 0 ≤ rank M.graph (degreeTwistInt M D 1 b.val)}

@[simp] theorem mem_effectiveDegreeOneTwistResidues_iff
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) (b : Fin k) :
    b ∈ effectiveDegreeOneTwistResidues M D k ↔
      0 ≤ rank M.graph (degreeTwistInt M D 1 b.val) := Iff.rfl

/-- A finite set whose only possible collision away from a designated base
point is equality has cardinality at most two. -/
theorem Set.ncard_le_two_of_zero_or_eq
    {α : Type*} (S : Set α) (z : α)
    (hPair : ∀ x y, x ∈ S → y ∈ S → x = z ∨ y = z ∨ x = y) :
    S.ncard ≤ 2 := by
  by_cases hNonzero : ∃ x ∈ S, x ≠ z
  · obtain ⟨x, hxS, hxz⟩ := hNonzero
    have hSub : S ⊆ ({z, x} : Set α) := by
      intro y hy
      rcases hPair y x hy hxS with hyz | hxz' | hyx
      · simp [hyz]
      · exact False.elim (hxz hxz')
      · simp [hyx]
    have hfin : ({z, x} : Set α).Finite := by simp
    have hle := Set.ncard_le_ncard hSub hfin
    rw [Set.ncard_pair (Ne.symm hxz)] at hle
    exact hle
  · have hSub : S ⊆ ({z} : Set α) := by
      intro x hx
      by_contra hne
      exact hNonzero ⟨x, hx, hne⟩
    have hle := Set.ncard_le_ncard hSub (Set.finite_singleton z)
    rw [Set.ncard_singleton] at hle
    omega

/-- Translate a finite torsion index by a fixed index, retaining its integer
Euclidean representative in the half-open fundamental period. -/
def residueShift (k : ℕ) (b c : Fin k) : Fin k := b - c

@[simp] theorem residueShift_val (k : ℕ) (b c : Fin k) :
    ((residueShift k b c : Fin k) : ℤ) = ((b : ℤ) - c) % k := by
  unfold residueShift
  exact Fin.coe_int_sub_eq_mod b c

/-- Translating finite residue indices is injective. -/
theorem residueShift_injective (k : ℕ) (c : Fin k) :
    Function.Injective (fun b : Fin k => residueShift k b c) := by
  intro b d hbd
  apply Fin.ext
  have hk : 0 < (k : ℤ) := by
    have := b.isLt
    omega
  have hb0 : 0 ≤ (b.val : ℤ) := by omega
  have hb : (b.val : ℤ) < k := by exact_mod_cast b.isLt
  have hd0 : 0 ≤ (d.val : ℤ) := by omega
  have hd : (d.val : ℤ) < k := by exact_mod_cast d.isLt
  have hmod : ((b.val : ℤ) - d.val) % k = 0 := by
    have hVal : ((b : ℤ) - c) % k =
        ((d : ℤ) - c) % k := by
      rw [← residueShift_val, ← residueShift_val]
      exact congrArg (fun x : Fin k => (x : ℤ)) hbd
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hVal
    convert hVal using 1 ; ring_nf
  have hEq := int_eq_of_emod_sub_eq_zero_of_fundamental hk hb0 hb hd0 hd hmod
  exact_mod_cast hEq

/-- Every member of the finite twist family has degree one. -/
theorem deg_effectiveDegreeOneTwistResidue
    (M : TwiceMarked) (D : CFDiv M.graph) (k : ℕ) (b : Fin k) :
    deg (degreeTwistInt M D 1 b.val) = 1 :=
  deg_degreeTwistInt M D 1 b.val

/-- Rebase a degree-one twist family at any one of its representatives. -/
theorem degreeTwistInt_rebase_linearEquiv
    {M : TwiceMarked} (D : CFDiv M.graph) (b c : ℤ) (w : M.graph.V)
    (hc : linearEquiv M.graph (degreeTwistInt M D 1 c) (oneChip w)) :
    linearEquiv M.graph (degreeTwistInt M D 1 b)
      (oneChip w + (b - c) • (oneChip M.u - oneChip M.v)) := by
  unfold degreeTwistInt linearEquiv at hc ⊢
  have hDiff :
      (oneChip w + (b - c) • (oneChip M.u - oneChip M.v)) -
          (D + (1 - deg D + b) • oneChip M.u - b • oneChip M.v) =
        (oneChip w - (D + (1 - deg D + c) • oneChip M.u - c • oneChip M.v)) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hDiff]
  exact hc

/-- Rebased twists may be reduced to their Euclidean residue at a torsion
period. -/
theorem degreeTwistInt_rebase_mod_period_linearEquiv
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (b c : ℤ) (w : M.graph.V)
    (hc : linearEquiv M.graph (degreeTwistInt M D 1 c) (oneChip w)) :
    linearEquiv M.graph (degreeTwistInt M D 1 b)
      (oneChip w + ((b - c) % k) • (oneChip M.u - oneChip M.v)) := by
  have hRebase := degreeTwistInt_rebase_linearEquiv D b c w hc
  have hMod := marked_difference_mod_period_linearEquiv hk (b - c)
  exact hRebase.trans (linearEquiv_add_left_of_linearEquiv hMod)

/-- Effectiveness of a finite degree-one twist transfers to the corresponding
residue twist at any chosen vertex representative. -/
theorem rank_nonneg_rebased_residue_of_effectiveDegreeOneTwist
    {M : TwiceMarked} {k : ℕ} (hk : TorsionWitness M k)
    (D : CFDiv M.graph) (b c : Fin k) (w : M.graph.V)
    (hc : linearEquiv M.graph (degreeTwistInt M D 1 c.val) (oneChip w))
    (hb : b ∈ effectiveDegreeOneTwistResidues M D k) :
    0 ≤ rank M.graph
      (oneChip w + ((b.val - c.val : ℤ) % k) •
        (oneChip M.u - oneChip M.v)) := by
  have hEq := degreeTwistInt_rebase_mod_period_linearEquiv
    hk D b.val c.val w hc
  have hRankEq := rank_eq_of_linear_equiv M.graph hEq
  rw [← hRankEq]
  exact hb

/-- On a genus-two banana, every degree-one divisor of nonnegative rank has
rank exactly zero.  This lets the effective degree-one twists in Lemma 4.10
feed directly into the unique-crossing construction below. -/
theorem rank_eq_zero_of_deg_one_rank_nonneg_banana_two
    (B : Banana 2) (X : CFDiv B.graph)
    (hDegree : deg X = 1) (hRank : 0 ≤ rank B.graph X) :
    rank B.graph X = 0 := by
  have hWin : winnable B.graph X :=
    (rank_nonneg_iff_winnable B.graph X).mp
      ((rank_geq_iff B.graph X 0).mpr hRank)
  obtain ⟨E, hEff, hXE⟩ := (winnable_iff_exists_effective B.graph X).mp hWin
  have hEDeg : deg E = 1 := by
    rw [← linear_equiv_preserves_deg B.graph X E hXE, hDegree]
  obtain ⟨w, hw⟩ := effective_degree_one_eq_one_chip E hEff hEDeg
  have hRankEq := rank_eq_of_linear_equiv B.graph hXE
  rw [hw, rank_one_chip_zero_banana_two] at hRankEq
  exact hRankEq

/-- Effective degree-one torsion residues on a theta graph have rank zero. -/
theorem rank_effectiveDegreeOneTwistResidue_eq_zero
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (k : ℕ)
    (b : Fin k)
    (hb : b ∈ effectiveDegreeOneTwistResidues (mark B.graph u v) D k) :
    rank B.graph (degreeTwistInt (mark B.graph u v) D 1 b.val) = 0 := by
  apply rank_eq_zero_of_deg_one_rank_nonneg_banana_two B
  · exact deg_effectiveDegreeOneTwistResidue (mark B.graph u v) D k b
  · exact hb

/-- Nonrecurrence bounds the number of effective degree-one classes in a
finite exact torsion orbit by two.  This is the main term estimate in the
genus-two inversion formula. -/
theorem effectiveDegreeOneTwistResidues_ncard_le_two_of_nonRecurrent
    (B : Banana 2) (u v : B.graph.V) (D : CFDiv B.graph) (k : ℕ)
    (hk : IsTorsionOrder (mark B.graph u v) k)
    (hNonrec : NonRecurrent (mark B.graph u v) k) :
    (effectiveDegreeOneTwistResidues (mark B.graph u v) D k).ncard ≤ 2 := by
  let M := mark B.graph u v
  let S := effectiveDegreeOneTwistResidues M D k
  by_cases hEmpty : S = ∅
  · change S.ncard ≤ 2
    rw [hEmpty]
    simp
  obtain ⟨c, hcS⟩ := Set.nonempty_iff_ne_empty.mpr hEmpty
  have hRankC : rank B.graph (degreeTwistInt M D 1 c.val) = 0 := by
    dsimp [M, S] at hcS ⊢
    exact rank_effectiveDegreeOneTwistResidue_eq_zero B u v D k c hcS
  obtain ⟨w, hw⟩ :=
    exists_one_chip_representative_of_rank_zero_degree_one B.graph
      (degreeTwistInt M D 1 c.val) hRankC
      (deg_effectiveDegreeOneTwistResidue M D k c)
  let T : Set (Fin k) := {r | 0 ≤ rank B.graph
    (oneChip w + (r.val : ℤ) • (oneChip u - oneChip v))}
  have hMap : ∀ b ∈ S, residueShift k b c ∈ T := by
    intro b hb
    have h := rank_nonneg_rebased_residue_of_effectiveDegreeOneTwist
      hk.1 D b c w hw (by simpa [S] using hb)
    change 0 ≤ rank B.graph
      (oneChip w + ((residueShift k b c).val : ℤ) •
        (oneChip u - oneChip v))
    rw [residueShift_val]
    exact h
  have hTtwo : T.ncard ≤ 2 := by
    let z : Fin k := ⟨0, hk.1.1⟩
    apply Set.ncard_le_two_of_zero_or_eq T z
    intro x y hx hy
    have hx' : 0 ≤ rank B.graph
        (oneChip w + (x.val : ℤ) • (oneChip u - oneChip v)) := hx
    have hy' : 0 ≤ rank B.graph
        (oneChip w + (y.val : ℤ) • (oneChip u - oneChip v)) := hy
    rcases hNonrec.zero_or_eq_of_two_rank_nonneg w x y hx' hy' with hx0 | hy0 | hxy
    · exact Or.inl (Fin.ext (by simpa [z] using hx0))
    · exact Or.inr (Or.inl (Fin.ext (by simpa [z] using hy0)))
    · exact Or.inr (Or.inr hxy)
  have hle := Set.ncard_le_ncard_of_injOn
    (s := S) (t := T) (fun b : Fin k => residueShift k b c)
    hMap (residueShift_injective k c).injOn
  exact hle.trans hTtwo

/-- A rank-zero degree-one twist on a connected genus-two graph determines a
unique inversion crossing its transmission corner.  More explicitly, if
`X = D + a*u - b*v`, there is a unique pair `(m,n)` with
`m < b ≤ n` and `τ(m) > a ≥ τ(n)`.

This is the pointwise construction used at the start of the proof of paper
Lemma `lem:invtau` (Lemma 4.10).  The two singleton sets are respectively
the northwest and southeast quadrants at `(a+1,b)`; Riemann--Roch makes both
cardinalities equal to one. -/
theorem degree_one_rank_zero_twist_unique_crossing_inversion
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph)
    (hGenus : genus M.graph = 2)
    (tau : ℤ → ℤ) (hTau : IsTransmissionPermutation M D tau)
    (a b : ℤ)
    (hDegree : deg (D + a • oneChip M.u - b • oneChip M.v) = 1)
    (hRank : rank M.graph
        (D + a • oneChip M.u - b • oneChip M.v) = 0) :
    ∃! p : ℤ × ℤ,
      p.1 < b ∧ b ≤ p.2 ∧ tau p.1 > a ∧ tau p.2 ≤ a := by
  let X : CFDiv M.graph :=
    D + a • oneChip M.u - b • oneChip M.v
  have hRR := riemann_roch_for_graphs hconn X
  have hComplementRank :
      rank M.graph (canonicalDivisor M.graph - X) = 0 := by
    rw [hGenus, hDegree, hRank] at hRR
    omega
  have hSECard : (southeastSet tau (a + 1) b).ncard = 1 := by
    have h := transmission_rank_eq_southeast_ncard M D hconn tau hTau a b
    rw [hRank] at h
    exact_mod_cast h.symm
  have hNWCard : (northwestSet tau (a + 1) b).ncard = 1 := by
    have h := transmission_complement_rank_eq_northwest_ncard
      M D hconn tau hTau a b
    have hRewrite :
        canonicalDivisor M.graph - D - a • oneChip M.u +
            b • oneChip M.v = canonicalDivisor M.graph - X := by
      dsimp [X]
      abel
    rw [hRewrite, hComplementRank] at h
    exact_mod_cast h.symm
  obtain ⟨n, hSE⟩ := Set.ncard_eq_one.mp hSECard
  obtain ⟨m, hNW⟩ := Set.ncard_eq_one.mp hNWCard
  have hmMem : m ∈ northwestSet tau (a + 1) b := by
    rw [hNW]
    simp
  have hnMem : n ∈ southeastSet tau (a + 1) b := by
    rw [hSE]
    simp
  refine ⟨(m, n), ?_, ?_⟩
  · rcases hmMem with ⟨hmb, hmTau⟩
    rcases hnMem with ⟨hbn, hnTau⟩
    change m < b ∧ b ≤ n ∧ tau m > a ∧ tau n ≤ a
    exact ⟨hmb, hbn, by omega, by omega⟩
  · rintro p' hp'
    rcases p' with ⟨m', n'⟩
    change m' < b ∧ b ≤ n' ∧ tau m' > a ∧ tau n' ≤ a at hp'
    rcases hp' with ⟨hm'b, hbn', hm'Tau, hn'Tau⟩
    have hm'Mem : m' ∈ northwestSet tau (a + 1) b := by
      exact ⟨hm'b, by omega⟩
    have hn'Mem : n' ∈ southeastSet tau (a + 1) b := by
      exact ⟨hbn', by omega⟩
    have hm' : m' = m := by
      rw [hNW] at hm'Mem
      simpa using hm'Mem
    have hn' : n' = n := by
      rw [hSE] at hn'Mem
      simpa using hn'Mem
    subst m'
    subst n'
    rfl

/-- The pair produced by
`degree_one_rank_zero_twist_unique_crossing_inversion` is, in particular, an
ordinary inversion of the transmission permutation. -/
theorem degree_one_rank_zero_twist_exists_inversion
    (M : TwiceMarked) (D : CFDiv M.graph)
    (hconn : _root_.graphConnected M.graph)
    (hGenus : genus M.graph = 2)
    (tau : ℤ → ℤ) (hTau : IsTransmissionPermutation M D tau)
    (a b : ℤ)
    (hDegree : deg (D + a • oneChip M.u - b • oneChip M.v) = 1)
    (hRank : rank M.graph
        (D + a • oneChip M.u - b • oneChip M.v) = 0) :
    ∃ m n : ℤ,
      (m, n) ∈ invSet tau ∧ m < b ∧ b ≤ n ∧
        tau m > a ∧ tau n ≤ a := by
  obtain ⟨⟨m, n⟩, hmn, -⟩ :=
    degree_one_rank_zero_twist_unique_crossing_inversion
      M D hconn hGenus tau hTau a b hDegree hRank
  change m < b ∧ b ≤ n ∧ tau m > a ∧ tau n ≤ a at hmn
  refine ⟨m, n, ?_, hmn⟩
  exact ⟨by omega, by omega⟩

/-- Crossing-inversion inequalities are equivariant under an affine period.
Together with uniqueness of the crossing inversion, this is the descent of
the pointwise twist construction to period-`k` inversion classes. -/
theorem crossing_inversion_conditions_add_period
    {k : ℕ} {tau : ℤ → ℤ} (hAffine : IsKAffine k tau)
    {a b m n : ℤ}
    (hCross : m < b ∧ b ≤ n ∧ tau m > a ∧ tau n ≤ a) :
    m + k < b + k ∧ b + k ≤ n + k ∧
      tau (m + k) > a + k ∧ tau (n + k) ≤ a + k := by
  rcases hCross with ⟨hmb, hbn, hma, hna⟩
  have hm := hAffine m
  have hn := hAffine n
  rw [hm, hn]
  omega

/-- Every ordinary inversion of a positive-period affine permutation has its
unique simultaneous period translate whose first coordinate lies in the
fundamental range used by `kInversions`. -/
theorem inversion_normalize_first_coordinate
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) {m n : ℤ}
    (hInv : (m, n) ∈ invSet tau) :
    (m % k, n - (m / k) * k) ∈ kInversions k tau := by
  rcases hInv with ⟨hmn, hTau⟩
  have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
  have hm0 : 0 ≤ m % k := Int.emod_nonneg _ (by omega)
  have hmK : m % k < k := Int.emod_lt_of_pos _ hkZ
  have hmRepr : m = m % k + (m / k) * k := by
    simpa [add_comm, mul_comm] using int_eq_emod_add_ediv_period (k := k) hk (b := m)
  have hnRepr : n = (n - (m / k) * k) + (m / k) * k := by ring
  have hTauM : tau m = tau (m % k) + (m / k) * k := by
    calc
      tau m = tau (m % k + (m / k) * k) := congrArg tau hmRepr
      _ = tau (m % k) + (m / k) * k := hAffine.iterate_int _ _
  have hTauN : tau n = tau (n - (m / k) * k) + (m / k) * k := by
    calc
      tau n = tau ((n - (m / k) * k) + (m / k) * k) := congrArg tau hnRepr
      _ = tau (n - (m / k) * k) + (m / k) * k := hAffine.iterate_int _ _
  change m % k < n - (m / k) * k ∧
    tau (m % k) > tau (n - (m / k) * k) ∧
      0 ≤ m % k ∧ m % k < k
  rw [hTauM, hTauN] at hTau
  exact ⟨by omega, by omega, hm0, hmK⟩

/-- Every ordinary inversion of a positive-period affine permutation also has
its unique simultaneous period translate whose *second* coordinate lies in
the fundamental range.  This is the normalization used in the double-sum
proof of Lemma 4.10. -/
theorem inversion_normalize_second_coordinate
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau) {m n : ℤ}
    (hInv : (m, n) ∈ invSet tau) :
    (m - (n / k) * k, n % k) ∈ kInversionsBySecond k tau := by
  rcases hInv with ⟨hmn, hTau⟩
  have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
  have hn0 : 0 ≤ n % k := Int.emod_nonneg _ (by omega)
  have hnK : n % k < k := Int.emod_lt_of_pos _ hkZ
  have hnRepr : n = n % k + (n / k) * k := by
    simpa [add_comm, mul_comm] using int_eq_emod_add_ediv_period (k := k) hk (b := n)
  have hmRepr : m = (m - (n / k) * k) + (n / k) * k := by ring
  have hTauM : tau m = tau (m - (n / k) * k) + (n / k) * k := by
    calc
      tau m = tau ((m - (n / k) * k) + (n / k) * k) := congrArg tau hmRepr
      _ = tau (m - (n / k) * k) + (n / k) * k := hAffine.iterate_int _ _
  have hTauN : tau n = tau (n % k) + (n / k) * k := by
    calc
      tau n = tau (n % k + (n / k) * k) := congrArg tau hnRepr
      _ = tau (n % k) + (n / k) * k := hAffine.iterate_int _ _
  change m - (n / k) * k < n % k ∧
    tau (m - (n / k) * k) > tau (n % k) ∧ 0 ≤ n % k ∧ n % k < k
  rw [hTauM, hTauN] at hTau
  exact ⟨by omega, by omega, hn0, hnK⟩

end Bananas
