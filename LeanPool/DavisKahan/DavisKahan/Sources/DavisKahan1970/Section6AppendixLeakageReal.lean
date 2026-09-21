/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/

import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section6AppendixLeakage
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Subspace

/-! # Section6Appendix Leakage Real -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Lemma 6.3 over a real Hilbert space

Standing assumption 1 of the transcription puts the paper on a separable
Hilbert space that may be **real or complex**, with finite dimensionality only
a special case.  `Section6AppendixLeakage.lean` proves Lemma 6.3 over `ℂ`; this
module supplies the real form, at arbitrary dimension.

The engine `lemma6_3_approximationNumber_leakage_of_energySplit` is already
scalar generic.  The single step that was stated over `ℂ` is the Pythagorean
splitting of the rectangular square energy over the orthogonal domain
decomposition `P + (1 - P)`, because the column-energy bridge it uses is
complex.  That step is recovered over `ℝ` here by complexification, and nothing
else has to be redone:

* real complexification preserves the whole approximation singular-value
  sequence, hence the square energy exactly
  (`approximationNumberEnergy_complexify`);
* the orthogonal projection onto a complexified real subspace is the
  complexification of the real orthogonal projection
  (`starProjection_complexifySubmodule`);
* complexification is a ring map on operators, so it carries `1 - P` to
  `1 - complexify P`.

So the complex splitting, read at `complexify L` and `complexifySubmodule P`,
is literally the real splitting.  The resulting real lemma is a statement about
`InnerProductSpace ℝ` throughout: real operator, real subspaces, real
approximation numbers, real operator norm.
-/

open scoped InnerProductSpace BigOperators ENNReal
open Finset

namespace TauCeti
namespace DavisKahan1970
namespace Section6Appendix

open TauCeti.DavisKahan
open TauCeti.DavisKahan.ExactSinTheta
open TauCeti.RealComplexification
open TauCeti.DavisKahan.Foundation.RealComplexification

universe u v

variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [CompleteSpace E] in
/-- Complexification carries the identity operator to the identity operator,
in the `1` spelling used by the complementary projection `1 - P`. -/
theorem complexify_one_eq :
    complexify (1 : E →L[ℝ] E) =
      (1 : RealComplexification E →L[ℂ] RealComplexification E) :=
  complexify_id

omit [CompleteSpace E] in
/-- Complexification carries a complementary orthogonal projection to the
complementary orthogonal projection of the complexified subspace. -/
theorem complexify_one_sub_starProjection
    (P : Submodule ℝ E) [P.HasOrthogonalProjection] :
    complexify (1 - P.starProjection) =
      1 - (complexifySubmodule P).starProjection := by
  rw [complexify_sub, complexify_one_eq, starProjection_complexifySubmodule]

/-- **The real Pythagorean splitting of the rectangular square energy.**

The real form of `hilbertSchmidtEnergy_domain_projection_add_complex`, obtained by
reading the complex splitting at the complexified operator and the complexified
subspace.  No complex object survives in the statement. -/
theorem hilbertSchmidtEnergy_domain_projection_add_real
    (L : E →L[ℝ] F)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    -- carried for source fidelity, exactly as in the complex form
    (hfinite : approximationNumberEnergy L ≠ ⊤) :
    approximationNumberEnergy L =
      approximationNumberEnergy (L ∘L P.starProjection) +
      approximationNumberEnergy
        (L ∘L (1 - P.starProjection)) := by
  have hc :=
    hilbertSchmidtEnergy_domain_projection_add_complex (complexify L)
      (complexifySubmodule P) ((approximationNumberEnergy_ne_top_complexify_iff L).2 hfinite)
  have h1 :
      complexify L ∘L (complexifySubmodule P).starProjection =
        complexify (L ∘L P.starProjection) := by
    rw [starProjection_complexifySubmodule, complexify_comp]
  have h2 :
      complexify L ∘L (1 - (complexifySubmodule P).starProjection) =
        complexify (L ∘L (1 - P.starProjection)) := by
    rw [complexify_comp, complexify_one_sub_starProjection]
  rw [h1, h2, approximationNumberEnergy_complexify,
    approximationNumberEnergy_complexify,
    approximationNumberEnergy_complexify] at hc
  exact hc

/-- **Davis--Kahan 1970, Lemma 6.3, over a real Hilbert space of arbitrary
dimension.**

Word for word the statement of `lemma6_3_approximationNumber_leakage_complex` with
`InnerProductSpace ℂ` replaced by `InnerProductSpace ℝ`: the source-faithful
block hypothesis `K ∘ P = Q ∘ K ∘ P`, a rank bound on the selected target
block, and near-saturation of the first-`n` square energy force the off-block
operator norm below `η`.  The rank bound on `P` is retained for source symmetry;
only the bound on `Q` is used. -/
theorem lemma6_3_approximationNumber_leakage_real
    (K : E →L[ℝ] F)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℝ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (_hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear : approximationEnergy (K ∘L P.starProjection) n >
      approximationEnergy K n - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  refine lemma6_3_approximationNumber_leakage_of_energySplit
    K P Q n hn η hη hKP hrankQ ?_ hnear
  refine hilbertSchmidtEnergy_domain_projection_add_real
    (Q.starProjection ∘L K) P ?_
  exact approximationNumberEnergy_ne_top_of_rank_le
    ((rank_starProjection_comp_le K Q).trans hrankQ)

/-- Finite-dimensional real singular-value specialization of Lemma 6.3. -/
theorem lemma6_3_singularValue_leakage_real
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (K : E →L[ℝ] F)
    (P : Submodule ℝ E) [P.HasOrthogonalProjection]
    (Q : Submodule ℝ F) [Q.HasOrthogonalProjection]
    (n : ℕ) (hn : 0 < n) (η : ℝ) (hη : 0 < η)
    (hKP : K ∘L P.starProjection = Q.starProjection ∘L K ∘L P.starProjection)
    (hrankP : P.starProjection.rank ≤ (n : Cardinal))
    (hrankQ : Q.starProjection.rank ≤ (n : Cardinal))
    (hnear :
      ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues
            (K ∘L P.starProjection).toLinearMap i : ℝ) ^ 2) >
        ∑ i ∈ Finset.range n,
          ((LinearMap.singularValues K.toLinearMap i : ℝ) ^ 2) - η ^ 2) :
    ‖Q.starProjection ∘L K ∘L (1 - P.starProjection)‖ < η := by
  apply lemma6_3_approximationNumber_leakage_real
    K P Q n hn η hη hKP hrankP hrankQ
  simpa only [approximationEnergy_eq_singularValues] using hnear

end Section6Appendix
end DavisKahan1970
end TauCeti
