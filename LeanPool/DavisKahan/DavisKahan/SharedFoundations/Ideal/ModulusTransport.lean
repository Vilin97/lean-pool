/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module


/-
The proof route uses the bounded polar decomposition, taken from `ForTauCeti`,
originally authored by Adam Bornemann.  The declaration-level mapping is
recorded in the accompanying provenance ledger.
-/
public import LeanPool.DavisKahan.DavisKahan.SharedFoundations.Ideal.TwoWayFactorization
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.CanonicalRealView
public import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.PartialIsometry

/-!
# Absolute-value transport for square symmetric ideals

A unitarily invariant norm is absolute: `T` and `|T|` lie in the same ideal and
have the same gauge.  The proof here is the elementary one -- the polar
factorization `T = U|T|` and `|T| = U*T` are two contraction factorizations, so
the two-way principle of `TwoWayFactorization` applies directly.  No unitary
*extension* of the polar partial isometry is needed, which is what makes the
argument work on an arbitrary Hilbert space rather than only where `U` extends
to a unitary.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace SharedFoundations
namespace Ideal

open scoped InnerProductSpace
open ExactSinTheta

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- The polar partial isometry is a contraction.

`polarPartial` is an isometry on the initial space precomposed with the
orthogonal projection onto it, so it is norm non-increasing everywhere. -/
theorem norm_polarPartial_le_one (T : E →L[ℂ] E) : ‖T.polarPartial‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [one_mul, T.polarPartial_apply, T.norm_polarInitialMap_apply]
  exact T.polarInitial.norm_orthogonalProjectionOnto_apply_le x

/-- The polar factor and its adjoint are contractions. -/
theorem polarPartial_and_adjoint_norm_le_one (T : E →L[ℂ] E) :
    ‖T.polarPartial‖ ≤ 1 ∧ ‖T.polarPartial.adjoint‖ ≤ 1 := by
  refine ⟨norm_polarPartial_le_one T, ?_⟩
  calc
    ‖T.polarPartial.adjoint‖ = ‖T.polarPartial‖ :=
      ContinuousLinearMap.adjoint.norm_map _
    _ ≤ 1 := norm_polarPartial_le_one T

/-- Every square symmetric ideal contains `|T|` exactly when it contains `T`,
and assigns them equal gauge. -/
theorem SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E))
    (T : E →L[ℂ] E) :
    (I.mem (ContinuousLinearMap.modulus T) ↔ I.mem T) ∧
      (I.mem T → I.gauge (ContinuousLinearMap.modulus T) = I.gauge T) := by
  let U : E →L[ℂ] E := T.polarPartial
  let J : E →L[ℂ] E := ContinuousLinearMap.id ℂ E
  have hTfactor : T = U ∘L ContinuousLinearMap.modulus T ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact (T.polarPartial_comp_modulus).symm
  have hAbsfactor : ContinuousLinearMap.modulus T = U.adjoint ∘L T ∘L J := by
    rw [ContinuousLinearMap.comp_id]
    exact (T.adjoint_polarPartial_comp_self).symm
  have hU := (polarPartial_and_adjoint_norm_le_one T).1
  have hUa := (polarPartial_and_adjoint_norm_le_one T).2
  have hJ : ‖J‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  constructor
  · constructor
    · intro hAbs
      exact SymmetricNormIdeal.mem_of_eq_comp_comp I hAbs hTfactor
    · intro hT
      exact SymmetricNormIdeal.mem_of_eq_comp_comp I hT hAbsfactor
  · intro hT
    have hAbs : I.mem (ContinuousLinearMap.modulus T) :=
      SymmetricNormIdeal.mem_of_eq_comp_comp I hT hAbsfactor
    apply le_antisymm
    · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hT hAbsfactor hUa hJ
    · exact SymmetricNormIdeal.gauge_le_of_contraction_factorization I hAbs hTfactor hU hJ

/-- Direct form used by the `sin Θ` ideal layer. -/
theorem SymmetricNormIdeal.modulus_mem_and_gauge_eq
    (I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E))
    {T : E →L[ℂ] E} (hT : I.mem T) :
    I.mem (ContinuousLinearMap.modulus T) ∧
      I.gauge (ContinuousLinearMap.modulus T) = I.gauge T := by
  have h := SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq I T
  exact ⟨h.1.mpr hT, h.2 hT⟩

/-- Square specialization to an operator ideal family. -/
theorem SymmetricOperatorIdealFamily.modulus_mem_and_gauge_eq
    (N : TauCeti.SymmetricOperatorIdealFamily.{0, u} ℂ)
    [N.toOperatorIdealFamily.IsComplete]
    {T : E →L[ℂ] E} (hT : N.Mem T) :
    N.Mem (ContinuousLinearMap.modulus T) ∧
      N.gaugeReal (ContinuousLinearMap.modulus T) = N.gaugeReal T := by
  let I : DavisKahanExt.SymmetricNormIdeal (𝕜 := ℂ) (E := E) :=
    DavisKahanExt.SymmetricNormIdeal.ofCanonical N
  have h := SymmetricNormIdeal.operatorAbs_mem_iff_and_gauge_eq I T
  exact ⟨h.1.mpr hT, h.2 hT⟩

/-- The Ky Fan dominant family inherits the transport, since its gauge is that
of its underlying symmetric family. -/
theorem KyFanDominantIdealFamily.modulus_mem_and_gauge_eq
    (N : KyFanDominantIdealFamily (𝕜 := ℂ))
    {T : E →L[ℂ] E}
    (hT : N.Mem T) :
    N.Mem (ContinuousLinearMap.modulus T) ∧
      N.gauge (ContinuousLinearMap.modulus T) = N.gauge T :=
  SymmetricOperatorIdealFamily.modulus_mem_and_gauge_eq
    N.toSymmetricOperatorIdealFamily hT

end Ideal
end SharedFoundations
end DavisKahan
end TauCeti
