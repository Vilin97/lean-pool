/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ChainTwoLoopsSameLeft
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.ExactTorsionAPI
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineReduction

/-!
# Rank differences in genus one

For a connected genus-one graph, Riemann--Roch makes the marked second rank
difference completely local in degrees `0`, `1`, and `2`.  This is the
rank-theoretic core needed to identify genus-one transmission permutations as
an affine translation with at most one adjacent interchange.
-/

@[expose] public section

namespace Bananas

open Utilities

section Generic

variable {G : CFGraph} {u v : G.V} {X : CFDiv G}

/-- A translated identity permutation has no affine inversion classes, at any
period.  This is the zero-principal-orbit case of genus-one transmission. -/
theorem kInversionCount_eq_zero_of_translation
    (k : ℕ) (tau : ℤ → ℤ) (c : ℤ)
    (hTau : ∀ n : ℤ, tau n = n + c) :
    kInversionCount k tau = 0 := by
  have hEmpty : kInversions k tau = ∅ := by
    ext p
    rcases p with ⟨a, b⟩
    simp only [kInversions, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨hab, hInv, -, -⟩
    rw [hTau a, hTau b] at hInv
    omega
  simp [kInversionCount, hEmpty]

/-- Translating all values of a permutation leaves its normalized inversion
classes unchanged. -/
theorem kInversionCount_output_translate
    (k : ℕ) (tau : ℤ → ℤ) (s : ℤ) :
    kInversionCount k (fun n => tau n + s) = kInversionCount k tau := by
  unfold kInversionCount
  apply congrArg Set.ncard
  apply Set.ext
  intro p
  rcases p with ⟨a, b⟩
  change (a < b ∧ tau a + s > tau b + s ∧ 0 ≤ a ∧ a < k) ↔
    (a < b ∧ tau a > tau b ∧ 0 ≤ a ∧ a < k)
  constructor <;> rintro ⟨hab, hInv, ha0, hak⟩ <;>
    exact ⟨hab, by omega, ha0, hak⟩

/-- Hence a value-translate of one periodic affine simple reflection has at
most one inversion class. -/
theorem kInversionCount_output_translate_affineReflection_le_one
    (k : ℕ) (i s : ℤ) (hk : 2 ≤ k) :
    kInversionCount k (fun n => affineReflection k i hk n + s) ≤ 1 := by
  rw [kInversionCount_output_translate]
  exact kInversionCount_affineReflection_le_one k i hk

private theorem rankDelta_unfold_mark (G : CFGraph) (u v : G.V) (X : CFDiv G) :
    rankDelta (mark G u v) X =
      rank G X - rank G (X - oneChip u) - rank G (X - oneChip v) +
        rank G (X - oneChip u - oneChip v) := rfl

private theorem degree_sub_chip (G : CFGraph) (X : CFDiv G) (x : G.V) :
    deg (X - oneChip x) = deg X - 1 := by
  rw [deg.map_sub, deg_one_chip]

private theorem degree_sub_two_chips (G : CFGraph) (X : CFDiv G)
    (u v : G.V) :
    deg (X - oneChip u - oneChip v) = deg X - 2 := by
  rw [degree_sub_chip, degree_sub_chip]
  ring

/-- In negative degree, every term in the marked rank difference vanishes. -/
theorem rankDelta_genusOne_of_degree_neg
    (hDegree : deg X < 0) :
    rankDelta (mark G u v) X = 0 := by
  have hX := rank_neg_one_of_deg_neg G X hDegree
  have hXu := rank_neg_one_of_deg_neg G (X - oneChip u) (by
    rw [degree_sub_chip]
    omega)
  have hXv := rank_neg_one_of_deg_neg G (X - oneChip v) (by
    rw [degree_sub_chip]
    omega)
  have hXuv := rank_neg_one_of_deg_neg G (X - oneChip u - oneChip v) (by
    rw [degree_sub_two_chips]
    omega)
  rw [rankDelta_unfold_mark, hX, hXu, hXv, hXuv]
  norm_num

/-- The degree-zero row is exactly the principality indicator, written as
`rank X + 1`. -/
theorem rankDelta_genusOne_of_degree_zero
    (hDegree : deg X = 0) :
    rankDelta (mark G u v) X = rank G X + 1 := by
  have hXu := rank_neg_one_of_deg_neg G (X - oneChip u) (by
    rw [degree_sub_chip, hDegree]
    norm_num)
  have hXv := rank_neg_one_of_deg_neg G (X - oneChip v) (by
    rw [degree_sub_chip, hDegree]
    norm_num)
  have hXuv := rank_neg_one_of_deg_neg G (X - oneChip u - oneChip v) (by
    rw [degree_sub_two_chips, hDegree]
    norm_num)
  rw [rankDelta_unfold_mark, hXu, hXv, hXuv]
  ring

/-- In degree one, only the two degree-zero residual classes can affect the
marked rank difference. -/
theorem rankDelta_genusOne_of_degree_one
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (hDegree : deg X = 1) :
    rankDelta (mark G u v) X =
      - rank G (X - oneChip u) - rank G (X - oneChip v) - 1 := by
  have hX := genusOne_rank_eq_degree_sub_one hConnected hGenus X (by
    rw [hDegree]
    norm_num)
  have hXuv := rank_neg_one_of_deg_neg G (X - oneChip u - oneChip v) (by
    rw [degree_sub_two_chips, hDegree]
    norm_num)
  rw [rankDelta_unfold_mark, hX, hXuv, hDegree]
  ring

/-- The degree-two row is the principality indicator of the double deletion. -/
theorem rankDelta_genusOne_of_degree_two
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (hDegree : deg X = 2) :
    rankDelta (mark G u v) X = rank G (X - oneChip u - oneChip v) + 1 := by
  have hX := genusOne_rank_eq_degree_sub_one hConnected hGenus X (by
    rw [hDegree]
    norm_num)
  have hXu := genusOne_rank_eq_degree_sub_one hConnected hGenus
    (X - oneChip u) (by rw [degree_sub_chip, hDegree]; norm_num)
  have hXv := genusOne_rank_eq_degree_sub_one hConnected hGenus
    (X - oneChip v) (by rw [degree_sub_chip, hDegree]; norm_num)
  have hDu : deg (X - oneChip u) = 1 := by
    rw [degree_sub_chip, hDegree]
    norm_num
  have hDv : deg (X - oneChip v) = 1 := by
    rw [degree_sub_chip, hDegree]
    norm_num
  rw [rankDelta_unfold_mark, hX, hXu, hXv, hDegree,
    hDu, hDv]
  ring

/-- Above degree two, Riemann--Roch makes the four ranks affine-linear, so
their second difference is zero. -/
theorem rankDelta_genusOne_of_degree_gt_two
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (hDegree : 2 < deg X) :
    rankDelta (mark G u v) X = 0 := by
  have hX := genusOne_rank_eq_degree_sub_one hConnected hGenus X (by omega)
  have hXu := genusOne_rank_eq_degree_sub_one hConnected hGenus
    (X - oneChip u) (by rw [degree_sub_chip]; omega)
  have hXv := genusOne_rank_eq_degree_sub_one hConnected hGenus
    (X - oneChip v) (by rw [degree_sub_chip]; omega)
  have hXuv := genusOne_rank_eq_degree_sub_one hConnected hGenus
    (X - oneChip u - oneChip v) (by rw [degree_sub_two_chips]; omega)
  have hDu : deg (X - oneChip u) = deg X - 1 := degree_sub_chip G X u
  have hDv : deg (X - oneChip v) = deg X - 1 := degree_sub_chip G X v
  have hDuv : deg (X - oneChip u - oneChip v) = deg X - 2 :=
    degree_sub_two_chips G X u v
  rw [rankDelta_unfold_mark, hX, hXu, hXv, hXuv,
    hDu, hDv, hDuv]
  ring

/-- The degree-zero member of the marked twist orbit at index `b`. -/
def genusOneZeroTwist (D : CFDiv G) (b : ℤ) : CFDiv G :=
  D + (b - deg D) • oneChip u - b • oneChip v

private theorem degree_genusOneZeroTwist (D : CFDiv G) (b : ℤ) :
    deg (genusOneZeroTwist (u := u) (v := v) D b) = 0 := by
  unfold genusOneZeroTwist
  rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
    deg_one_chip, deg_one_chip]
  ring

private theorem genusOneDegreeOneTwist_sub_u (D : CFDiv G) (b : ℤ) :
    D + (b - deg D + 1) • oneChip u - b • oneChip v - oneChip u =
      genusOneZeroTwist (u := u) (v := v) D b := by
  unfold genusOneZeroTwist
  funext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

private theorem genusOneDegreeOneTwist_sub_v (D : CFDiv G) (b : ℤ) :
    D + (b - deg D + 1) • oneChip u - b • oneChip v - oneChip v =
      genusOneZeroTwist (u := u) (v := v) D (b + 1) := by
  unfold genusOneZeroTwist
  funext z
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
  ring

/-- If a genus-one marked twist orbit has no principal degree-zero member,
the transmission permutation is the corresponding translated identity. -/
theorem transmission_eq_translation_of_no_principal_genusOne
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (D : CFDiv G) (tau : ℤ → ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hNoPrincipal : ∀ b : ℤ,
      ¬ linearEquiv G (genusOneZeroTwist (u := u) (v := v) D b) 0) :
    ∀ b : ℤ, tau b = b - deg D + 1 := by
  intro b
  let X : CFDiv G := D + (b - deg D + 1) • oneChip u - b • oneChip v
  have hDegree : deg X = 1 := by
    dsimp [X]
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip]
    ring
  have hXu : rank G (X - oneChip u) = -1 := by
    rw [genusOneDegreeOneTwist_sub_u]
    exact rank_eq_neg_one_of_degree_zero_not_linear_equiv G _
      (degree_genusOneZeroTwist D b) (hNoPrincipal b)
  have hXv : rank G (X - oneChip v) = -1 := by
    rw [genusOneDegreeOneTwist_sub_v]
    exact rank_eq_neg_one_of_degree_zero_not_linear_equiv G _
      (degree_genusOneZeroTwist D (b + 1)) (hNoPrincipal (b + 1))
  have hDelta : rankDelta (mark G u v) X = 1 := by
    rw [rankDelta_genusOne_of_degree_one hConnected hGenus hDegree, hXu, hXv]
    norm_num
  have hDelta' : rankDelta (mark G u v)
      (D + (b - deg D + 1) • oneChip u - b • oneChip v) = 1 := by
    simpa only [X] using hDelta
  have hValue := hTau.2 (b - deg D + 1) b
  change (if tau b = b - deg D + 1 then (1 : ℤ) else 0) =
    rankDelta (mark G u v)
      (D + (b - deg D + 1) • oneChip u - b • oneChip v) at hValue
  rw [hDelta'] at hValue
  by_contra hNot
  simp [hNot] at hValue

/-- Consequently, the no-principal-orbit transmission has zero inversion
classes at every period. -/
theorem kInversionCount_eq_zero_of_no_principal_genusOne
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (D : CFDiv G) (tau : ℤ → ℤ) (k : ℕ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hNoPrincipal : ∀ b : ℤ,
      ¬ linearEquiv G (genusOneZeroTwist (u := u) (v := v) D b) 0) :
    kInversionCount k tau = 0 := by
  apply kInversionCount_eq_zero_of_translation k tau (1 - deg D)
  intro b
  rw [transmission_eq_translation_of_no_principal_genusOne
    hConnected hGenus D tau hTau hNoPrincipal]
  ring

/-- A principal degree-zero twist supplies the lowered transmission row at
its own index. -/
theorem transmission_value_of_principal_genusOneZeroTwist
    (D : CFDiv G) (tau : ℤ → ℤ) (c : ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hPrincipal : linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D c) 0) :
    tau c = c - deg D := by
  let X := genusOneZeroTwist (u := u) (v := v) D c
  have hRank : rank G X = 0 := by
    rw [rank_eq_of_linear_equiv G hPrincipal, zero_divisor_rank]
  have hXu := rank_neg_one_of_deg_neg G (X - oneChip u) (by
    rw [degree_sub_chip, degree_genusOneZeroTwist]
    norm_num)
  have hXv := rank_neg_one_of_deg_neg G (X - oneChip v) (by
    rw [degree_sub_chip, degree_genusOneZeroTwist]
    norm_num)
  have hXuv := rank_neg_one_of_deg_neg G (X - oneChip u - oneChip v) (by
    rw [degree_sub_two_chips, degree_genusOneZeroTwist]
    norm_num)
  have hDelta : rankDelta (mark G u v) X = 1 := by
    rw [rankDelta_unfold_mark, hRank, hXu, hXv, hXuv]
    norm_num
  have hValue := hTau.2 (c - deg D) c
  change (if tau c = c - deg D then (1 : ℤ) else 0) =
    rankDelta (mark G u v)
      (D + (c - deg D) • oneChip u - c • oneChip v) at hValue
  have hX : D + (c - deg D) • oneChip u - c • oneChip v = X := by
    dsimp [X, genusOneZeroTwist]
  rw [hX, hDelta] at hValue
  by_contra hNot
  simp [hNot] at hValue

/-- The row immediately preceding a principal degree-zero twist is raised
by one.  This is the other half of the affine adjacent interchange. -/
theorem transmission_value_before_principal_genusOneZeroTwist
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (D : CFDiv G) (tau : ℤ → ℤ) (c : ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hPrincipal : linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D c) 0) :
    tau (c - 1) = c - deg D + 1 := by
  let X : CFDiv G := D + (c - deg D + 1) • oneChip u - (c - 1) • oneChip v
  have hDegree : deg X = 2 := by
    dsimp [X]
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip]
    ring
  have hXuv : linearEquiv G (X - oneChip u - oneChip v) 0 := by
    have hEq : X - oneChip u - oneChip v =
        genusOneZeroTwist (u := u) (v := v) D c := by
      dsimp [X, genusOneZeroTwist]
      funext z
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      ring
    rw [hEq]
    exact hPrincipal
  have hRankUV : rank G (X - oneChip u - oneChip v) = 0 := by
    rw [rank_eq_of_linear_equiv G hXuv, zero_divisor_rank]
  have hDelta : rankDelta (mark G u v) X = 1 := by
    rw [rankDelta_genusOne_of_degree_two hConnected hGenus hDegree, hRankUV]
    norm_num
  have hValue := hTau.2 (c - deg D + 1) (c - 1)
  change (if tau (c - 1) = c - deg D + 1 then (1 : ℤ) else 0) =
    rankDelta (mark G u v)
      (D + (c - deg D + 1) • oneChip u - (c - 1) • oneChip v) at hValue
  rw [show D + (c - deg D + 1) • oneChip u - (c - 1) • oneChip v = X by rfl,
    hDelta] at hValue
  by_contra hNot
  simp [hNot] at hValue

/-- At an exact torsion order, a principal degree-zero twist can occur only
in its own residue class. -/
theorem not_principal_genusOneZeroTwist_of_not_dvd
    (hOrder : IsTorsionOrder (mark G u v) k)
    (D : CFDiv G) (b c : ℤ)
    (hPrincipal : linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D c) 0)
    (hNotDvd : ¬ k ∣ (b - c).natAbs) :
    ¬ linearEquiv G (genusOneZeroTwist (u := u) (v := v) D b) 0 := by
  intro hB
  apply hNotDvd
  apply isTorsionOrder_dvd_natAbs_sub_of_degreeTwistInt_linearEquiv
    hOrder D 0 b c
  have hBC : linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D b)
      (genusOneZeroTwist (u := u) (v := v) D c) := hB.trans hPrincipal.symm
  change linearEquiv G
    (D + (0 - deg D + b) • oneChip u - b • oneChip v)
    (D + (0 - deg D + c) • oneChip u - c • oneChip v)
  have hB' : D + (0 - deg D + b) • oneChip u - b • oneChip v =
      genusOneZeroTwist (u := u) (v := v) D b := by
    unfold genusOneZeroTwist
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  have hC' : D + (0 - deg D + c) • oneChip u - c • oneChip v =
      genusOneZeroTwist (u := u) (v := v) D c := by
    unfold genusOneZeroTwist
    funext z
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    ring
  rw [hB', hC']
  exact hBC

/-- Away from a principal degree-zero twist and its successor, the genus-one
transmission row is the ordinary translated-identity row. -/
theorem transmission_value_of_two_nonprincipal_genusOneZeroTwists
    (hConnected : _root_.graphConnected G) (hGenus : genus G = 1)
    (D : CFDiv G) (tau : ℤ → ℤ) (b : ℤ)
    (hTau : IsTransmissionPermutation (mark G u v) D tau)
    (hB : ¬ linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D b) 0)
    (hNext : ¬ linearEquiv G
      (genusOneZeroTwist (u := u) (v := v) D (b + 1)) 0) :
    tau b = b - deg D + 1 := by
  let X : CFDiv G := D + (b - deg D + 1) • oneChip u - b • oneChip v
  have hDegree : deg X = 1 := by
    dsimp [X]
    rw [deg.map_sub, deg.map_add, map_zsmul, map_zsmul,
      deg_one_chip, deg_one_chip]
    ring
  have hXu : rank G (X - oneChip u) = -1 := by
    rw [genusOneDegreeOneTwist_sub_u]
    exact rank_eq_neg_one_of_degree_zero_not_linear_equiv G _
      (degree_genusOneZeroTwist D b) hB
  have hXv : rank G (X - oneChip v) = -1 := by
    rw [genusOneDegreeOneTwist_sub_v]
    exact rank_eq_neg_one_of_degree_zero_not_linear_equiv G _
      (degree_genusOneZeroTwist D (b + 1)) hNext
  have hDelta : rankDelta (mark G u v) X = 1 := by
    rw [rankDelta_genusOne_of_degree_one hConnected hGenus hDegree, hXu, hXv]
    norm_num
  have hValue := hTau.2 (b - deg D + 1) b
  change (if tau b = b - deg D + 1 then (1 : ℤ) else 0) =
    rankDelta (mark G u v)
      (D + (b - deg D + 1) • oneChip u - b • oneChip v) at hValue
  rw [show D + (b - deg D + 1) • oneChip u - b • oneChip v = X by rfl,
    hDelta] at hValue
  by_contra hNot
  simp [hNot] at hValue

end Generic

end Bananas
