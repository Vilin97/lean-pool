/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.Classification.GenusOneRankDelta
public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.EndpointInversions
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineReduction
public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineInversionFinite
public import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaInvTauCorrection

/-!
# General transmission in genus one

The periodic assembly of the three row formulas in `GenusOneRankDelta`: an
exact principal residue gives a translated affine simple reflection, while no
principal residue gives a translation.  The resulting inversion bounds are
already checked in that module, so this file is composition and case analysis.

The shape of the argument, for a fixed divisor `D`:

* submodularity supplies a transmission permutation `τ`, affine at the torsion
  witness (`exists_affineTransmissionPermutation_of_submodular`);
* if no degree-zero member of the marked twist orbit is principal, `τ` is a
  translation and has no inversion classes at all;
* otherwise fix a principal index `c`.  At an exact torsion order the principal
  indices are exactly `c` mod `k`, so `τ` lowers the row at `c`, raises the row
  at `c - 1`, and is the ordinary translated identity everywhere else.  That is
  precisely `affineReflection k (c-1)` translated by `1 - deg D`, which has at
  most one inversion class.

The `k = 1` case is separated out because `affineReflection` needs `2 ≤ k`.
There every index is principal, so `τ` is again a translation.
-/

@[expose] public section

namespace Bananas

open Utilities

section Genus

variable {G : CFGraph} {u v : G.V}

/-- The degree-zero twist orbit of `GenusOneRankDelta` is the `d = 0` slice of
the integer-indexed twist used by the torsion API. -/
private theorem genusOneZeroTwist_eq_degreeTwistInt (D : CFDiv G) (b : ℤ) :
    genusOneZeroTwist (u := u) (v := v) D b = degreeTwistInt (mark G u v) D 0 b := by
  change D + (b - deg D) • oneChip u - b • oneChip v
      = D + (0 - deg D + b) • oneChip u - b • oneChip v
  have hcoeff : b - deg D = 0 - deg D + b := by ring
  rw [hcoeff]

/-- Divisibility of an integer by a natural number, in the two shapes the
lemmas of `GenusOneRankDelta` and `AffineReduction` respectively use. -/
private theorem natAbs_dvd_iff {k : ℕ} (m : ℤ) : k ∣ m.natAbs ↔ (k : ℤ) ∣ m := by
  simpa using (Int.natAbs_dvd_natAbs (a := (k : ℤ)) (b := m))

/-- Congruent indices have simultaneously principal degree-zero twists. -/
private theorem principal_genusOneZeroTwist_of_dvd {k : ℕ}
    (hWitness : TorsionWitness (mark G u v) k) (D : CFDiv G) (b c : ℤ)
    (hDvd : (k : ℤ) ∣ b - c)
    (hc : linearEquiv G (genusOneZeroTwist (u := u) (v := v) D c) 0) :
    linearEquiv G (genusOneZeroTwist (u := u) (v := v) D b) 0 := by
  rw [genusOneZeroTwist_eq_degreeTwistInt] at hc ⊢
  refine degreeTwistInt_linearEquiv_zero_of_emod_eq hWitness D 0 b c ?_ hc
  have hmod : Int.ModEq (k : ℤ) b c :=
    Int.modEq_iff_dvd.mpr (by simpa using dvd_neg.mpr hDvd)
  exact hmod

end Genus

/-- A connected genus-one twice-marked graph with exact torsion order and
all divisors submodular has general transmission at that order. -/
theorem kGeneralTransmission_genusOne_of_torsionOrder_and_allSubmodular
    {M : TwiceMarked} {k : ℕ}
    (hConnected : _root_.graphConnected M.graph) (hGenus : genus M.graph = 1)
    (hOrder : IsTorsionOrder M k) (hSub : AllSubmodular M) :
    KGeneralTransmission M k := by
  obtain ⟨G, u, v⟩ := M
  obtain ⟨hWitness, hMin⟩ := hOrder
  refine ⟨hWitness, hSub, ?_⟩
  intro D
  obtain ⟨τ, hτ, hAffine⟩ :=
    exists_affineTransmissionPermutation_of_submodular _ D hConnected (hSub D) hWitness
  have hkpos : 0 < k := hWitness.1
  refine ⟨τ, hτ, hAffine, kInversions_finite_of_isKAffine hkpos hAffine, ?_⟩
  have hGenusNat : Int.toNat (genus G) = 1 := by rw [hGenus]; rfl
  rw [hGenusNat]
  by_cases hAny : ∃ c : ℤ, linearEquiv G (genusOneZeroTwist (u := u) (v := v) D c) 0
  · obtain ⟨c, hc⟩ := hAny
    by_cases hk2 : 2 ≤ k
    case neg =>
      -- `k = 1`: every index is principal, so `τ` is a translation.
      have hk1' : k = 1 := by omega
      have hAll : ∀ b : ℤ, linearEquiv G
          (genusOneZeroTwist (u := u) (v := v) D b) 0 := by
        intro b
        refine principal_genusOneZeroTwist_of_dvd hWitness D b c ?_ hc
        simp [hk1']
      have hTrans : ∀ b : ℤ, τ b = b + (-deg D) := by
        intro b
        have := transmission_value_of_principal_genusOneZeroTwist D τ b hτ (hAll b)
        omega
      rw [kInversionCount_eq_zero_of_translation k τ (-deg D) hTrans]
      norm_num
    case pos =>
      -- `2 ≤ k`: `τ` is `affineReflection k (c-1)` translated by `1 - deg D`.
      have hEq : ∀ n : ℤ,
          τ n = affineReflection k (c - 1) hk2 n + (1 - deg D) := by
        intro n
        by_cases hn : n ∈ affineReflectionSupport k (c - 1)
        · -- `n ≡ c - 1`, so `n + 1` is principal and this row is raised.
          rw [affineReflection_apply_of_mem k (c - 1) hk2 hn]
          have hShift : n - (c - 1) = n + 1 - c := by ring
          have hDvd : (k : ℤ) ∣ (n + 1) - c := by
            have h := (mem_affineReflectionSupport_iff k (c - 1) n).mp hn
            rwa [hShift] at h
          have hPrinc := principal_genusOneZeroTwist_of_dvd hWitness D (n + 1) c hDvd hc
          have hRow := transmission_value_before_principal_genusOneZeroTwist
            hConnected hGenus D τ (n + 1) hτ hPrinc
          simp only [add_sub_cancel_right] at hRow
          omega
        · by_cases hp : n - 1 ∈ affineReflectionSupport k (c - 1)
          · -- `n ≡ c`, the lowered row at a principal index.
            rw [affineReflection_apply_of_pred_mem k (c - 1) hk2 hp]
            have hDvd : (k : ℤ) ∣ n - c := by
              have := (mem_affineReflectionSupport_iff k (c - 1) (n - 1)).mp hp
              simpa using this
            have hPrinc := principal_genusOneZeroTwist_of_dvd hWitness D n c hDvd hc
            have hRow := transmission_value_of_principal_genusOneZeroTwist D τ n hτ hPrinc
            omega
          · -- neither: the ordinary translated-identity row.
            rw [affineReflection_apply_of_neither k (c - 1) hk2 hn hp]
            have hNotN : ¬ (k : ℤ) ∣ n - c := by
              intro hdvd
              exact hp ((mem_affineReflectionSupport_iff k (c - 1) (n - 1)).mpr (by
                simpa using hdvd))
            have hNotN1 : ¬ (k : ℤ) ∣ (n + 1) - c := by
              intro hdvd
              refine hn ((mem_affineReflectionSupport_iff k (c - 1) n).mpr ?_)
              have hShift : n - (c - 1) = n + 1 - c := by ring
              rwa [hShift]
            have hB : ¬ linearEquiv G
                (genusOneZeroTwist (u := u) (v := v) D n) 0 :=
              not_principal_genusOneZeroTwist_of_not_dvd ⟨hWitness, hMin⟩ D n c hc
                (fun h => hNotN ((natAbs_dvd_iff (n - c)).mp h))
            have hNext : ¬ linearEquiv G
                (genusOneZeroTwist (u := u) (v := v) D (n + 1)) 0 :=
              not_principal_genusOneZeroTwist_of_not_dvd ⟨hWitness, hMin⟩ D (n + 1) c hc
                (fun h => hNotN1 ((natAbs_dvd_iff (n + 1 - c)).mp h))
            have hRow := transmission_value_of_two_nonprincipal_genusOneZeroTwists
              hConnected hGenus D τ n hτ hB hNext
            omega
      have hRewrite : kInversionCount k τ
          = kInversionCount k (fun n => affineReflection k (c - 1) hk2 n + (1 - deg D)) := by
        congr 1
        funext n
        exact hEq n
      rw [hRewrite]
      exact kInversionCount_output_translate_affineReflection_le_one k (c - 1) (1 - deg D) hk2
  · simp only [not_exists] at hAny
    rw [kInversionCount_eq_zero_of_no_principal_genusOne hConnected hGenus D τ k hτ hAny]
    norm_num

end Bananas
