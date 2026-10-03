/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorModulus
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence

/-!
# Approximation singular values of the rectangular operator modulus

For a bounded operator `T : E -> F`, its source modulus is the positive square
root of `T* T` on `E`.  The paper uses this object to define the cosine and sine
of a directed operator angle.  Its complete approximation-singular-value
sequence is exactly that of `T`.

The proof avoids any choice of polar factor.  The repository's exact min--max
characterization shows that pointwise equality of norms determines every
approximation number, while the square-root identity gives
`norm (|T| x) = norm (T x)`.
-/

@[expose] public section

namespace TauCeti
namespace DavisKahan
namespace ExactSinTheta

open scoped InnerProductSpace

noncomputable section

universe v vF vG

variable {E : Type v} {F : Type vF}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A rectangular operator and its positive source modulus have the same
complete approximation-number sequence.  The modulus acts on `E` while `T` maps
into `F`, so this is the heterogeneous relation.

Named for its conclusion.  The previous name said *singular values* where the
conclusion says `HasSameApproximationNumbers`; the two agree in this
development, but a name has to describe the statement it is attached to.

The former `modulus_sameApproximationSingularValues`, a "square-operator
specialization", is gone: its body was identical to this one and `F := E` is a
legal instantiation, so it was the same theorem under a second name. -/
theorem modulus_hasSameApproximationNumbers
    (T : E →L[ℂ] F) :
    (ContinuousLinearMap.modulus T).HasSameApproximationNumbers T :=
  T.modulus_hasSameApproximationNumbers

end

end ExactSinTheta
end DavisKahan
end TauCeti
