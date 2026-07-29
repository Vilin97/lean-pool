/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.DedekindZeta.EncodedIdealSummand
public import LeanPool.Odlyzko.DedekindZeta.PrimeIdealSummability
public import LeanPool.Odlyzko.DedekindZeta.SummableZeroExtension

/-! TODO: Add doc-string. -/

@[expose] public section

noncomputable section

open Ideal IsDedekindDomain

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K]

theorem summable_nonzeroIdeal_norm_inverseNormPower {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : NonzeroIdeal K ↦
      ‖((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))‖) := by
  have hreal :
      Summable (fun I : NonzeroIdeal K ↦
        (absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-s.re)) := by
    change Summable
      ((fun I : Ideal (𝓞 K) ↦ (absNorm I : ℝ) ^ (-s.re)) ∘
        Subtype.val)
    exact (summable_ideal_absNorm_rpow K hs).comp_injective
      Subtype.val_injective
  apply hreal.congr
  intro I
  rw [show ((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s)) =
      inverseNormPower (absNorm (I : Ideal (𝓞 K))) s by rfl,
    norm_inverseNormPower]
  exact Nat.pos_of_ne_zero (by
    simpa [Ideal.absNorm_eq_zero_iff] using I.2)

lemma norm_encodedIdealSummand_eq_extendByZero (s : ℂ) :
    (fun n ↦ ‖encodedIdealSummand K s n‖) =
      extendByZero (idealPrimeCode K)
        (fun I : NonzeroIdeal K ↦
          ‖((absNorm (I : Ideal (𝓞 K)) : ℂ) ^ (-s))‖) := by
  funext n
  by_cases hn : encodedIdealSummand K s n = 0
  · rw [hn, norm_zero]
    symm
    apply extendByZero_eq_zero_of_not_mem_range
      (idealPrimeCode K) _
    intro hrange
    obtain ⟨I, hI⟩ := hrange
    apply (encodedIdealSummand_ne_zero_iff K s n).2 ⟨I, hI⟩
    simp_all
  · obtain ⟨I, hI⟩ :=
      (encodedIdealSummand_ne_zero_iff K s n).1 hn
    subst n
    rw [extendByZero_apply (idealPrimeCode K)
      (idealPrimeCode_injective K),
      encodedIdealSummand_idealPrimeCode]

theorem summable_norm_encodedIdealSummand {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n ↦ ‖encodedIdealSummand K s n‖) := by
  rw [norm_encodedIdealSummand_eq_extendByZero]
  exact summable_extendByZero
    (idealPrimeCode K) (idealPrimeCode_injective K)
    (summable_nonzeroIdeal_norm_inverseNormPower K hs)

end NumberField.Odlyzko
