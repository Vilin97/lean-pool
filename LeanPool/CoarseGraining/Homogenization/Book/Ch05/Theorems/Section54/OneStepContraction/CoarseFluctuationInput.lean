/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section54.OneStepContraction.CoarseRHSPrep
import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundCoarseFluctuations

/-! # Coarse Fluctuation Input -/

namespace Homogenization
namespace Book
namespace Ch05
namespace Section54
namespace OneStepContraction

noncomputable section

/-!
# Section 5.3 input for the one-step contraction

This file is the narrow bridge from the public Section 5.3
coarse-fluctuation lemma to the `k = 0` special-vector estimate used in the
Section 5.4 one-step contraction proof.
-/

open Section53.JUpperBoundCoarseFluctuations

/-- The public Section 5.3 coarse-fluctuation lemma, specialized to `k = 0`
and to the Section 5.4 unit-vector convention, with the constant chosen from
the fixed `(P4)` parameters before the law is introduced. -/
theorem exists_expectedCenteredResponseJAtScale_special_le_coarseFluctuationRHS_zero_uniform
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P) (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      ∀ {m : ℕ}, 0 < m → ∀ e : Vec d, Ch02.vecNorm e = 1 →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 →
        let p_e := specialPAtScale hP hStruct (m : ℤ) e
        let q_e := specialQAtScale hP hStruct (m : ℤ) e
        expectedCenteredResponseJAtScale hP hStruct (m : ℤ) p_e q_e ≤
          coarseFluctuationManuscriptRHSAtScale hP hStruct hP4 C ε 0 m e := by
  rcases JUpperBoundCoarseFluctuations_homogenizationScale
      params with ⟨C, hC_nonneg, hC⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro P hP hStruct hP4 hparams m hm_pos e he ε hε hε_le
  exact hC hP hStruct.stationary hStruct hP4 hparams
    (k := 0) (m := m) (by simpa using hm_pos)
    e (GoodScale.vecNormSq_eq_one_of_vecNorm_eq_one he) (ε := ε) hε hε_le

end

end OneStepContraction
end Section54
end Ch05
end Book
end Homogenization
