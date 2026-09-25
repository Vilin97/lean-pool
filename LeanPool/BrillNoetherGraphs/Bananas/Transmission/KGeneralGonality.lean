/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralBNGeneral

/-!
# Gonality forced by `k`-general transmission

The Hurwitz--Brill--Noether consequence needed here is considerably smaller
than the full splitting-type census.  If a divisor `D` has degree `d < k`,
then `D - k u` has negative degree.  In the transmission permutation of `D`
this says that the deeper southeast quadrant is empty.  Hence the dots in the
ordinary southeast quadrant occupy distinct residue classes modulo `k`, and
normalizing the full northwest-by-southeast rectangle gives an injection into
the `k`-inversions.

Together with the defining inversion bound, this excludes rank-one divisors
of degree below `k` whenever `k` is at most the generic gonality.  The reverse
inequality is the elementary observation from Pflueger--Solomon Lemma
`lem:Fg1k`: affine periodicity applied to the transmission permutation of the
zero divisor gives a rank-one divisor `k u`.
-/

namespace Bananas

open Utilities

/-- If the deeper southeast quadrant is empty, normalization is injective on
the rectangle of inversions crossing the origin.  The point is that a
collision would put two southeast dots in the same residue class; translating
the lower one by affine periodicity would then put a dot in the forbidden
deeper quadrant. -/
theorem normalizeFirstInversion_injective_on_crossing_of_deep_empty
    {k : ℕ} {tau : ℤ → ℤ} (hk : 0 < k)
    (hAffine : IsKAffine k tau)
    (hDeep : southeastSet tau (1 - (k : ℤ)) 0 = ∅) :
    Set.InjOn (normalizeFirstInversion k) (crossingInversions tau) := by
  rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' hSame
  rcases hp with ⟨ha, hb⟩
  rcases hp' with ⟨ha', hb'⟩
  change a < 0 ∧ 1 ≤ tau a at ha
  change 0 ≤ b ∧ tau b < 1 at hb
  change a' < 0 ∧ 1 ≤ tau a' at ha'
  change 0 ≤ b' ∧ tau b' < 1 at hb'
  change (a % k, b - (a / k) * k) =
    (a' % k, b' - (a' / k) * k) at hSame
  have hMod : a % k = a' % k := congrArg Prod.fst hSame
  have hSecond : b - (a / k) * k = b' - (a' / k) * k :=
    congrArg Prod.snd hSame
  let q : ℤ := a' / k - a / k
  have haRepr := int_eq_emod_add_ediv_period (k := k) (b := a) hk
  have ha'Repr := int_eq_emod_add_ediv_period (k := k) (b := a') hk
  have haa' : a' = a + q * k := by
    calc
      a' = a' % k + k * (a' / k) := ha'Repr
      _ = a % k + k * (a' / k) := by rw [hMod]
      _ = (a % k + k * (a / k)) + q * k := by dsimp [q]; ring
      _ = a + q * k := by rw [← haRepr]
  have hbb' : b' = b + q * k := by
    dsimp [q]
    linarith
  have hq : q = 0 := by
    by_contra hq0
    rcases lt_or_gt_of_ne hq0 with hqNeg | hqPos
    · have hShift := hAffine.iterate_int b' (-q)
      have hArg : b' + (-q) * (k : ℤ) = b := by rw [hbb']; ring
      rw [hArg] at hShift
      have hDeepMem : b' ∈ southeastSet tau (1 - (k : ℤ)) 0 := by
        change 0 ≤ b' ∧ tau b' < 1 - (k : ℤ)
        constructor
        · exact hb'.1
        · have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
          nlinarith [hShift]
      rw [hDeep] at hDeepMem
      exact hDeepMem
    · have hShift := hAffine.iterate_int b q
      have hArg : b + q * (k : ℤ) = b' := hbb'.symm
      rw [hArg] at hShift
      have hDeepMem : b ∈ southeastSet tau (1 - (k : ℤ)) 0 := by
        change 0 ≤ b ∧ tau b < 1 - (k : ℤ)
        constructor
        · exact hb.1
        · have hkZ : 0 < (k : ℤ) := by exact_mod_cast hk
          nlinarith [hShift]
      rw [hDeep] at hDeepMem
      exact hDeepMem
  have : a = a' ∧ b = b' := by
    rw [hbb', haa', hq]
    simp
  rcases this with ⟨rfl, rfl⟩
  rfl

/-- A rank-positive divisor of degree below the affine period forces its full
Brill--Noether rectangle to inject into the `k`-inversions. -/
theorem crossingInversions_ncard_le_kInversionCount_of_degree_lt_period
    {M : TwiceMarked} {D : CFDiv M.graph} {d : ℤ} {k : ℕ}
    (hk : 0 < k)
    (hconn : _root_.graphConnected M.graph)
    (hdeg : deg D = d) (hdk : d < k)
    {tau : ℤ → ℤ} (hTau : IsTransmissionPermutation M D tau)
    (hAffine : IsKAffine k tau) :
    (crossingInversions tau).ncard ≤ kInversionCount k tau := by
  have hTwistDeg :
      deg (D + (-(k : ℤ)) • oneChip M.u - (0 : ℤ) • oneChip M.v) < 0 := by
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip, hdeg]
    simp
    omega
  have hTwistRank :
      rank M.graph
        (D + (-(k : ℤ)) • oneChip M.u - (0 : ℤ) • oneChip M.v) = -1 :=
    rank_neg_one_of_deg_neg M.graph _ hTwistDeg
  have hDeepCard := transmission_rank_eq_southeast_ncard
    M D hconn tau hTau (-(k : ℤ)) 0
  have hDeepFinite : (southeastSet tau (1 - (k : ℤ)) 0).Finite := by
    obtain ⟨sigma, hSigmaTau, -⟩ :=
      transmissionPermutation_rankSlipFace M D hconn tau hTau
    rw [← hSigmaTau]
    exact sigma.se_finite _ _
  have hDeep : southeastSet tau (1 - (k : ℤ)) 0 = ∅ := by
    apply (Set.ncard_eq_zero hDeepFinite).mp
    rw [show -(k : ℤ) + 1 = 1 - (k : ℤ) by ring] at hDeepCard
    omega
  have hfinite := kInversions_finite_of_isKAffine hk hAffine
  exact Set.ncard_le_ncard_of_injOn
    (normalizeFirstInversion k)
    (fun p hp => normalizeFirstInversion_mem_kInversions_of_crossing
      hk hAffine hp)
    (normalizeFirstInversion_injective_on_crossing_of_deep_empty
      hk hAffine hDeep)
    hfinite

/-- Pflueger--Solomon Lemma `lem:Fg1k`, rank half: `k`-general transmission
supplies the degree-`k` pencil `k u`. -/
theorem KGeneralTransmission.rank_period_smul_one_chip_ge_one
    {M : TwiceMarked} {k : ℕ} (hK : KGeneralTransmission M k)
    (hconn : _root_.graphConnected M.graph) :
    rank M.graph ((k : ℤ) • oneChip M.u) ≥ 1 := by
  obtain ⟨tau, hTau, hAffine, _hfinite, _hCount⟩ :=
    hK.2.2 (0 : CFDiv M.graph)
  have hk : 0 < k := hK.1.1
  have hZero := transmission_rank_eq_southeast_ncard
    M 0 hconn tau hTau 0 0
  have hZeroRank : rank M.graph (0 : CFDiv M.graph) = 0 :=
    zero_divisor_rank M.graph
  have hCardOne : (southeastSet tau 1 0).ncard = 1 := by
    simpa [hZeroRank] using hZero.symm
  have hFinite : (southeastSet tau 1 0).Finite := by
    obtain ⟨sigma, hSigmaTau, -⟩ :=
      transmissionPermutation_rankSlipFace M 0 hconn tau hTau
    rw [← hSigmaTau]
    exact sigma.se_finite _ _
  have hNonempty : (southeastSet tau 1 0).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    omega
  obtain ⟨m, hm⟩ := hNonempty
  have hm' : 0 ≤ m ∧ tau m < 1 := hm
  have hmk : m + k ∈ southeastSet tau ((k : ℤ) + 1) 0 := by
    change 0 ≤ m + (k : ℤ) ∧ tau (m + k) < (k : ℤ) + 1
    rw [hAffine m]
    omega
  have hmBig : m ∈ southeastSet tau ((k : ℤ) + 1) 0 := by
    change 0 ≤ m ∧ tau m < (k : ℤ) + 1
    omega
  have hPair : ({m, m + (k : ℤ)} : Set ℤ) ⊆
      southeastSet tau ((k : ℤ) + 1) 0 := by
    intro x hx
    rcases hx with (rfl | rfl)
    · exact hmBig
    · exact hmk
  have hPairCard : ({m, m + (k : ℤ)} : Set ℤ).ncard = 2 := by
    rw [Set.ncard_pair]
    omega
  have hBigFinite : (southeastSet tau ((k : ℤ) + 1) 0).Finite := by
    obtain ⟨sigma, hSigmaTau, -⟩ :=
      transmissionPermutation_rankSlipFace M 0 hconn tau hTau
    rw [← hSigmaTau]
    exact sigma.se_finite _ _
  have hTwo : 2 ≤ (southeastSet tau ((k : ℤ) + 1) 0).ncard := by
    rw [← hPairCard]
    exact Set.ncard_le_ncard hPair hBigFinite
  have hRank := transmission_rank_eq_southeast_ncard
    M 0 hconn tau hTau (k : ℤ) 0
  simpa using (show rank M.graph
      ((0 : CFDiv M.graph) + (k : ℤ) • oneChip M.u -
        (0 : ℤ) • oneChip M.v) ≥ 1 by
    omega)

/-- A `k`-general twice-marked graph has no positive-rank divisor of degree
below `k`, provided `k` is no larger than the generic gonality
`floor((g+3)/2)`. -/
theorem KGeneralTransmission.no_rank_one_below_period
    {M : TwiceMarked} {g k : ℕ}
    (hconn : _root_.graphConnected M.graph)
    (hgenus : genus M.graph = g)
    (hK : KGeneralTransmission M k)
    (hsmall : k ≤ (g + 3) / 2)
    {D : CFDiv M.graph} {d : ℤ}
    (hdeg : deg D = d) (hrank : rank M.graph D ≥ 1)
    (hdk : d < k) : False := by
  obtain ⟨tau, hTau, hAffine, hfinite, hCount⟩ := hK.2.2 D
  have hCrossLe :=
    crossingInversions_ncard_le_kInversionCount_of_degree_lt_period
      hK.1.1 hconn hdeg hdk hTau hAffine
  have hSE := transmission_rank_eq_southeast_ncard
    M D hconn tau hTau 0 0
  have hNW := transmission_complement_rank_eq_northwest_ncard
    M D hconn tau hTau 0 0
  have hRR := riemann_roch_for_graphs hconn D
  have hSEcard : ((southeastSet tau 1 0).ncard : ℤ) =
      rank M.graph D + 1 := by simpa using hSE.symm
  have hNWcard : ((northwestSet tau 1 0).ncard : ℤ) =
      genus M.graph - d + rank M.graph D := by
    have hComplement : canonicalDivisor M.graph - D -
        (0 : ℤ) • oneChip M.u + (0 : ℤ) • oneChip M.v =
          canonicalDivisor M.graph - D := by simp
    rw [hComplement] at hNW
    norm_num at hNW
    rw [hdeg] at hRR
    omega
  have hCrossCard : ((crossingInversions tau).ncard : ℤ) =
      (rank M.graph D + 1) *
        (genus M.graph - d + rank M.graph D) := by
    rw [crossingInversions_ncard]
    push_cast
    rw [hNWcard, hSEcard]
    ring
  have hGenusNonneg : 0 ≤ genus M.graph := by rw [hgenus]; omega
  have hDegreePos : 1 ≤ d := by
    have := rank_le_degree M.graph D 1 (by norm_num)
      ((rank_geq_iff M.graph D 1).mpr hrank)
    rw [hdeg] at this
    exact this
  have hRectangleLarge : genus M.graph <
      (rank M.graph D + 1) *
        (genus M.graph - d + rank M.graph D) := by
    rw [hgenus]
    have hDiv : 2 * k ≤ g + 3 := by
      simpa [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp hsmall
    nlinarith
  have hCrossGt : g < (crossingInversions tau).ncard := by
    rw [hgenus] at hCrossCard hRectangleLarge
    exact_mod_cast (hCrossCard ▸ hRectangleLarge)
  have hCountLeG : kInversionCount k tau ≤ g := by
    simpa [hgenus] using hCount
  omega

/-- Exact witness-form gonality for a `k`-general twice-marked graph in the
special range. -/
theorem KGeneralTransmission.exact_gonality
    {M : TwiceMarked} {g k : ℕ}
    (hconn : _root_.graphConnected M.graph)
    (hgenus : genus M.graph = g)
    (hK : KGeneralTransmission M k)
    (hsmall : k ≤ (g + 3) / 2) :
    BNExists M.graph 1 (k : ℤ) ∧
      ∀ d : ℤ, d < k → ¬ BNExists M.graph 1 d := by
  constructor
  · refine ⟨(k : ℤ) • oneChip M.u, ?_, ?_⟩
    · rw [map_zsmul, deg_one_chip]
      simp
    · exact hK.rank_period_smul_one_chip_ge_one hconn
  · intro d hdk
    rintro ⟨D, hdeg, hrank⟩
    exact hK.no_rank_one_below_period hconn hgenus hsmall hdeg hrank hdk

end Bananas
