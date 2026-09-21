/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFan
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFanFiniteCarrier
import LeanPool.DavisKahan.DavisKahan.FiniteDimensional.DoubleAngle.TanTheta
import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.UnboundedIdeal
import LeanPool.DavisKahan.DavisKahan.TanTwoTheta.Unbounded

/-!
# Literal Davis--Kahan 1970 Section 7 tangent-double-angle surface

Source anchor: Section 7, equation (7.6) and the following argument, together
with the Section 2 statement `DK-tan2` and the Section 8 acute-branch
conclusion of Theorem 8.1.

## Audited source scope

**Corrected 2026-08-07.**  This section previously said the source conclusion is
`δ · ‖tan 2Θ‖ ≤ 2 ‖H‖` "together with the strict quarter-turn branch
`Θ < π/4`".  That conflates two different theorems and must not be repeated.

The printed Section 2 `tan 2θ` theorem assumes **only**

* `spectrum(A₀) ⊆ [β, α]` and `spectrum(A₁) ⊆ [α + δ, ∞)` — both conditions on
  the blocks of the *unperturbed* `A`; and
* `H₀ = 0` and `H₁ = 0`, i.e. `H` fully off-diagonal for the unperturbed
  splitting;

and concludes, for every unitarily invariant norm,
`δ ‖tan 2Θ₀‖ ≤ 2 ‖R‖` and `δ ‖tan 2Θ‖ ≤ 2 ‖H‖`.

It assumes **nothing** about the spectral placement of `Λ₀` and `Λ₁`, the blocks
of `A + H` for the chosen reducing subspace `Q`, and it does **not** conclude
`Θ < π/4`.  `Q` is an arbitrary reducing subspace of `A + H`.  The paper is
explicit that this is deliberate, at the head of Section 8:

> The double-angle conclusions also allow angles close to `π/2`. … The
> explanation is that the double-angle theorems imposed no special choice of the
> reducing subspace `QH` of `A + H`.

`Θ < π/4` is the conclusion of **Theorem 8.1**, which earns it from the extra
hypotheses that `P` is the spectral projector of `A` for `(-∞, α]` and `Q` the
spectral projector of `A + H` for the same interval.  A theorem that assumes
ordered form bounds on `A + H` restricted to `V` and `Vᗮ` is therefore a
*selected-branch* theorem, not the unrestricted Section 2 statement, and must
not be cited as the latter.

The source text develops the argument through paired singular vectors, claiming
every unitary-invariant norm.

## What is compiled, at which scope

* `tanTwoTheta_principalBranch_finiteDimensional_uiNorm_rclike` — **the source norm scope of equation (7.6)**: for
  every rectangular unitarily invariant norm,
  `(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`, in the finite-dimensional
  graph-coordinate formulation, proved by the paper's paired-singular-vector
  argument (`kyFan_tanTwoTheta0_offDiagonal_le` is the Ky Fan prefix root).
  The `tan 2Θ₀` representative freedom matches the paper: any operator with
  the double-angle-tangent singular values is admissible.  Quarter-acuteness
  enters as the hypothesis that the graph coordinate is a strict
  contraction; for spectral subspaces it is discharged by the acute-branch
  conclusion of `tanTwoTheta_sharpness_opNorm_rclike`.
* `tanTwoTheta_sharpness_opNorm_rclike` — the sharp subspace-level theorem at operator
  norm, on an **arbitrary inner-product space over any `RCLike` field** (no
  finite-dimensionality, no completeness): form gap `[a, b]`-split on the
  `T`-invariant pair, mirrored bounds for the perturbed pair, off-diagonal
  perturbation of norm `ε`.  The conclusion is pole-free and carries the
  Section 8 acute branch explicitly: with `t = ‖P_U - P_V‖ = sin θ_max`,
  `t² < 1/2` and `(b - a) sin 2θ_max ≤ 2 ε cos 2θ_max` — together
  `tan 2θ_max ≤ 2ε/(b - a)`, with the sharp constant.
* `tanTwoTheta_spectral_repulsion` — an off-diagonal perturbation admits no
  eigenvalue in the open form gap; this is the source's mechanism keeping the
  selected branch acute.
* unbounded operator-norm and ideal-gauge companions with genuine spectral
  subspaces, under an explicit quarter-acuteness hypothesis and with the
  non-sharp extended-cosine denominator `1 - 2 g²`.

* `tanTwoTheta_principalBranch_finiteSubspace_idealFamily_rclike` — **the infinite-dimensional sharp
  ideal form**: on an arbitrary `RCLike` Hilbert space with a
  finite-dimensional invariant configuration (finite-dimensional `U`,
  graph coordinate supported on `U`), every Fan-dominant unitary-invariant
  ideal family transports membership of the off-diagonal perturbation to
  the `tan 2Θ₀` representative with the sharp constant:
  `(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`.  The Ky Fan approximation-number
  root `tanTwoTheta_principalBranch_finiteSubspace_kyFan_rclike` holds with no ideal hypothesis at
  all.  Proof: compression to the finite carrier `U ⊔ T''U` and
  approximation-number transport.

## What remains open (recorded, not claimed)

1. The infinite-dimensional ideal form with an
   **infinite-dimensional invariant subspace** `U`: the compiled sharp
   theorem requires the graph coordinate to be supported on a
   finite-dimensional `U` (so that principal angles are attained); the
   unbounded companions below cover genuine spectral subspaces at the
   non-sharp extended-cosine denominator.
2. The sharp Riccati route
   (`quarterAcuteAngularCoordinate_sharp_bound_of_orderedInternalGap` and its
   family under `Experimental/InfiniteDimensional/TanTwoTheta/`) currently
   depends on the Section 8 continuation modules and the
   `GraphSubspace`/`Ideals.Symmetric`/`Sylvester.Resolvent` modules, which do
   not compile at present; that repair belongs to the Section 8 ownership
   area and is deliberately not attempted here.
3. The **unrestricted** sharp infinite-dimensional ideal theorem is not
   exported, and this is a refutation rather than a gap: the approximate
   graph-domain singular-family route used by the retired completion
   workspace is invalid, and the genuine unbounded Sylvester equation has a
   nonzero commutator defect in general (`doubleAngleTangent_sylvesterEquation`
   carries that defect explicitly).  Excluding the unsupported statement is
   part of completing the surface correctly, not a weakening of anything
   proved above.
-/

namespace TauCeti
namespace DavisKahan1970

/-! ## The source norm scope: every unitarily invariant norm -/

/-- The double-angle tangent scalar function `t ↦ 2t/(1 - t²)`. -/
alias tanTwoThetaDoubleAngleTangent := DavisKahan.TanTwoTheta.doubleAngleTangent

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, every rectangular unitarily
invariant norm** (Section 7, equation (7.6), paired-singular-vector proof;
finite-dimensional graph-coordinate form): `(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`
for a fully off-diagonal symmetric perturbation `H` across the form gap
`[a, b]`, where `tan 2Θ₀` is any operator whose singular values are the
double-angle tangents of the principal angles between `U` and the perturbed
invariant graph subspace. -/
alias tanTwoTheta_principalBranch_finiteDimensional_uiNorm_rclike := DavisKahan.FiniteDimensional.tanTwoTheta0_offDiagonal_le

/-- The Ky Fan prefix root of `tanTwoTheta_principalBranch_finiteDimensional_uiNorm_rclike`: equation (7.6) summed
over paired singular vectors. -/
alias tanTwoTheta_principalBranch_finiteDimensional_kyFan_rclike := DavisKahan.FiniteDimensional.kyFan_tanTwoTheta0_offDiagonal_le

/-- The paired-singular-vector scalar inequality at the heart of the source
argument. -/
alias tanTwoTheta_pairedSingularVector_scalar :=
  DavisKahan.FiniteDimensional.doubleAngleTangent_scalar

/-! ## The infinite-dimensional sharp ideal form -/

/-- **Davis--Kahan 1970, `tan 2Θ` theorem on an arbitrary Hilbert space,
every Fan-dominant unitary-invariant ideal** (finite-dimensional invariant
configuration): membership of the off-diagonal perturbation in the ideal
transports to any `tan 2Θ₀` representative, with
`(b - a) · N(tan 2Θ₀) ≤ 2 · N(H)`. -/
alias tanTwoTheta_principalBranch_finiteSubspace_idealFamily_rclike :=
  DavisKahan.TanTwoTheta.tanTwoTheta0_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace

/-- The Ky Fan approximation-number root of the infinite-dimensional sharp
form; holds for every `k` with no ideal hypothesis. -/
alias tanTwoTheta_principalBranch_finiteSubspace_kyFan_rclike :=
  DavisKahan.TanTwoTheta.kyFan_tanTwoTheta0_offDiagonal_le_of_finiteDimensional_invariantSubspace

/-- Representative-free infinite-dimensional Ky Fan root, phrased directly
in the double-angle tangents of the graph-coordinate approximation
numbers. -/
alias tanTwoTheta_doubleAngleTangent_finiteSubspace_kyFan_rclike :=
  DavisKahan.TanTwoTheta.kyFan_doubleAngleTangent_offDiagonal_le_of_finiteDimensional_invariantSubspace

/-- The Ky Fan variational bound for approximation-number prefixes: the
infinite-dimensional max--min principle used alongside the compression
argument. -/
alias kyFanApproximationGauge_orthonormal_bound :=
  DavisKahan.ExactSinTheta.re_sum_inner_map_le_kyFanApproximationGauge

/-! ## The sharp subspace theorem with the acute branch -/

/-- **Davis--Kahan 1970, `tan 2Θ` theorem, sharp subspace form at operator
norm, with the Section 8 acute branch.**  Ambient scope: any inner-product
space over any `RCLike` field.  Conclusion: `sin² θ_max < 1/2` and
`(b - a) sin 2θ_max ≤ 2 ε cos 2θ_max`, i.e. `tan 2θ_max ≤ 2ε/(b - a)` with
the strict quarter-turn branch. -/
alias tanTwoTheta_sharpness_opNorm_rclike := TauCeti.tan_two_theta_norm_sub_le

/-- **Spectral repulsion for off-diagonal perturbations**: no eigenvalue
enters the open form gap.  This is the source's reason the selected branch
stays acute. -/
alias tanTwoTheta_spectral_repulsion :=
  TauCeti.eigenvalue_notMem_gap_of_diagonal_form

/-! ## Unbounded genuine-spectral-subspace companions

`A` is an unbounded self-adjoint closed operator, `H` a bounded self-adjoint
perturbation, and both subspaces are genuine spectral subspaces.  These
companions divide the sharp `sin 2Θ` estimate by the extended double-angle
cosine, so their constant carries the non-sharp denominator `1 - 2 g²` with
`g` the directed gap; quarter-acuteness is an explicit hypothesis rather than
a derived branch conclusion. -/

/-- Unbounded operator-norm `tan 2Θ` estimate with the extended-cosine
denominator, under explicit quarter-acuteness. -/
alias tanTwoTheta_unbounded_opNorm_complex :=
  DavisKahan.tanTwoTheta_addBounded_of_spectrum_gap

/-- Set-localized interval/exterior form of the unbounded operator-norm
estimate. -/
alias tanTwoTheta_unbounded_intervalExterior_opNorm_complex :=
  DavisKahan.tanTwoTheta_addBounded_of_intervalExterior

/-- The ideal-theoretic tangent companion of the reflected overlap block. -/
alias tanTwoThetaBlock :=
  DavisKahan.tanTwoThetaIdealBlock

/-- Rectangular ideal-gauge membership and estimate for the tangent
companion block. -/
alias tanTwoThetaBlock_mem_and_gauge_le :=
  DavisKahan.tanTwoThetaIdealBlock_mem_and_gauge_le

/-- Unbounded `tan 2Θ` estimate at rectangular ideal-gauge scope. -/
alias tanTwoTheta_unbounded_blockRepresentative_symmetricIdealFamily_complex :=
  DavisKahan.tanTwoTheta_addBounded_gauge_of_spectrum_gap

/-- Unbounded `tan 2Θ` estimate for every source unitary-invariant ideal
family. -/
alias tanTwoTheta_unbounded_blockRepresentative_idealFamily_complex :=
  DavisKahan.tanTwoTheta_addBounded_unitaryInvariant_of_spectrum_gap

/-- Set-localized interval/exterior form at unitary-invariant ideal scope. -/
alias tanTwoTheta_unbounded_intervalExterior_blockRepresentative_idealFamily_complex :=
  DavisKahan.tanTwoTheta_addBounded_unitaryInvariant_of_intervalExterior

end DavisKahan1970
end TauCeti
