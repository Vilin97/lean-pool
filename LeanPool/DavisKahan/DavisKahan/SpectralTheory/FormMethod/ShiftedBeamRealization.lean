/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.CoerciveFormResolvent
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.FormCompactness
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.FormMethod.BoundedGraphCompactness
import LeanPool.DavisKahan.DavisKahan.SinTheta.BoundedPerturbation
import Mathlib.Tactic

/-! # Shifted Beam Realization -/

open TauCeti.DavisKahan.Sylvester

/-!
# Shifted coercive realization of the free beam

The unshifted bending form has a two-dimensional affine kernel, so the direct
coercive construction uses

`a₁(u,v) = integral u'' * conj(v'') + integral u * conj(v)`.

Its associated operator is `B + I`.  Subtracting the bounded identity produces
the free-beam operator `B` without changing the domain, self-adjointness, or
compactness of the graph embedding.

This file carries out that assembly abstractly.  The only beam-specific input
is the decomposition of the represented shifted form energy into ambient
`L²` norm plus a nonnegative bending energy.
-/

open scoped InnerProductSpace

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Analytic


noncomputable section

open Abstract

universe u v

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]
variable {V : Type v} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [CompleteSpace V]

/-- Coercive shifted form together with its bending-energy decomposition. -/
structure ShiftedBeamFormData extends
    Abstract.CoerciveFormData (𝕜 := 𝕜) (H := H) (V := V) where
  bendingEnergy : V → ℝ
  bending_nonnegative : ∀ u, 0 ≤ bendingEnergy u
  form_energy_decomposition : ∀ u,
    RCLike.re ⟪formOperator u, u⟫_𝕜 =
      ‖embed u‖ ^ 2 + bendingEnergy u

namespace ShiftedBeamFormData

/-- The positive self-adjoint operator associated to the shifted beam form. -/
noncomputable def shiftedOperator
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  D.toCoerciveFormData.associatedOperator

/-- The free-beam operator is the shifted realization minus the identity. -/
noncomputable def beamOperator
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    H →ₗ.[𝕜] H :=
  TauCeti.LinearPMap.addBounded D.shiftedOperator (-(1 : H →L[𝕜] H))

/-- The domain of the shifted beam operator is the form domain. -/
@[simp] theorem beamOperator_domain
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    D.beamOperator.domain = D.shiftedOperator.domain := rfl

/-- The shifted beam operator acts as the form operator plus the identity shift. -/
@[simp] theorem beamOperator_apply
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    D.beamOperator x =
      D.shiftedOperator x - (x : H) := by
  change D.shiftedOperator x + -(x : H) =
    D.shiftedOperator x - (x : H)
  rw [sub_eq_add_neg]

/-- Form-space representative of a vector in the shifted operator domain. -/
noncomputable def formRepresentative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) : V :=
  D.toCoerciveFormData.solutionOperator
    (D.shiftedOperator x)

/-- The form representative embeds to the original ambient domain vector. -/
theorem embed_formRepresentative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    D.embed (D.formRepresentative x) = (x : H) := by
  change D.toCoerciveFormData.resolvent
      (D.shiftedOperator x) = (x : H)
  exact Abstract.R_inversePartialMap_apply
    D.toCoerciveFormData.resolvent
    D.toCoerciveFormData.resolvent_isSelfAdjoint
    D.toCoerciveFormData.resolvent_injective x

/-- The shifted operator quadratic form is the represented shifted form
energy. -/
theorem shifted_quadratic_eq_form_energy
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.shiftedOperator.domain) :
    RCLike.re ⟪D.shiftedOperator x, (x : H)⟫_𝕜 =
      RCLike.re
        ⟪D.formOperator (D.formRepresentative x),
          D.formRepresentative x⟫_𝕜 := by
  let f := D.shiftedOperator x
  have henergy := D.toCoerciveFormData.resolvent_energy_identity f
  have hRx : D.toCoerciveFormData.resolvent f = (x : H) :=
    D.embed_formRepresentative x
  calc
    RCLike.re ⟪f, (x : H)⟫_𝕜 =
        RCLike.re ⟪(x : H), f⟫_𝕜 := inner_re_symm _ _
    _ = RCLike.re ⟪D.toCoerciveFormData.resolvent f, f⟫_𝕜 := by rw [hRx]
    _ = RCLike.re
        ⟪D.formOperator (D.toCoerciveFormData.solutionOperator f),
          D.toCoerciveFormData.solutionOperator f⟫_𝕜 :=
      congrArg RCLike.re henergy
    _ = RCLike.re
        ⟪D.formOperator (D.formRepresentative x),
          D.formRepresentative x⟫_𝕜 := rfl

/-- The unshifted beam quadratic form is exactly the bending energy. -/
theorem beam_quadratic_eq_bendingEnergy
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    RCLike.re ⟪D.beamOperator x, (x : H)⟫_𝕜 =
      D.bendingEnergy (D.formRepresentative x) := by
  rw [D.beamOperator_apply]
  rw [inner_sub_left, map_sub, inner_self_eq_norm_sq]
  -- Spelled as a closed equation: `x : D.beamOperator.domain` is only definitionally
  -- `D.shiftedOperator.domain`, so `rw` cannot instantiate the lemma's argument itself.
  rw [show RCLike.re ⟪D.shiftedOperator x, (x : H)⟫_𝕜 =
      RCLike.re ⟪D.formOperator (D.formRepresentative x), D.formRepresentative x⟫_𝕜 from
    D.shifted_quadratic_eq_form_energy x]
  rw [D.form_energy_decomposition]
  -- Closed equation again, for the same reason as the rewrite above.
  rw [show D.embed (D.formRepresentative x) = (x : H) from D.embed_formRepresentative x]
  ring

/-- The free-beam realization is nonnegative. -/
theorem beam_nonnegative
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (x : D.beamOperator.domain) :
    0 ≤ RCLike.re ⟪D.beamOperator x, (x : H)⟫_𝕜 := by
  rw [D.beam_quadratic_eq_bendingEnergy]
  exact D.bending_nonnegative _

/-- The shifted form realization is self-adjoint. -/
theorem shiftedOperator_isSelfAdjoint
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    _root_.IsSelfAdjoint D.shiftedOperator :=
  D.toCoerciveFormData.associatedOperator_isSelfAdjoint

omit [CompleteSpace H] in
/-- The identity perturbation is symmetric. -/
theorem negIdentity_isSelfAdjointOperator :
    (-(1 : H →L[𝕜] H)).IsSymmetric := by
  intro x y
  simp

/-- Subtracting the identity preserves self-adjointness, so the unshifted free
beam is self-adjoint. -/
theorem beamOperator_isSelfAdjoint
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V)) :
    _root_.IsSelfAdjoint D.beamOperator := by
  exact addBounded_isSelfAdjoint
    D.shiftedOperator D.shiftedOperator_isSelfAdjoint
    (-(1 : H →L[𝕜] H)) negIdentity_isSelfAdjointOperator

/-- Compact form embedding gives compact graph embedding of the shifted
operator. -/
theorem shiftedOperator_graph_compact
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : Abstract.SequentiallyCompactEmbedding D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.shiftedOperator :=
  D.toCoerciveFormData.associatedOperator_graph_compact hcompact

/-- Compact form embedding also gives compact graph embedding of the
unshifted free-beam operator. -/
theorem beamOperator_graph_compact
    (D : ShiftedBeamFormData (𝕜 := 𝕜) (H := H) (V := V))
    (hcompact : Abstract.SequentiallyCompactEmbedding D.embed) :
    Abstract.SequentiallyCompactGraphEmbedding D.beamOperator := by
  exact Abstract.graphCompact_addBounded
    D.shiftedOperator (-(1 : H →L[𝕜] H))
    (D.shiftedOperator_graph_compact hcompact)

end ShiftedBeamFormData

end

end Analytic
end FreeBeam
end DavisKahan
end TauCeti
