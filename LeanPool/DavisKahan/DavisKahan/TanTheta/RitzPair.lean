/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.DavisKahan.TanTheta.Theorem63UnboundedCompression
public import LeanPool.DavisKahan.DavisKahan.TanTheta.UnboundedSpectrum

/-! # Ritz Pair -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# The unbounded Ritz pair, and the reducing complement

The most general unbounded tangent theorem asks its caller for four separate
facts tying an `UnboundedCompressionTrialData` to the ambient operator and to the
chosen subspace:

```
(hZA     : ∀ z, ((z : U) : E) ∈ A.domain)
(haction : ∀ z, D.action z = A ⟨_, hZA z⟩)
(hVdom   : ∀ x : A.domain, Vᗮ.starProjection (x : E) ∈ A.domain)
(hVcomm  : ∀ x : A.domain, Vᗮ.starProjection (A x) = A ⟨_, hVdom x⟩)
```

None of that is Davis--Kahan mathematics.  The first two say the compression data
*is* the compression of `A`; the second two say `Vᗮ` reduces `A`.  Both are
properties of ordinary mathematical objects and belong in the objects.

* `UnboundedRitzPair A U` is compression data together with the two facts that
  make it `A`'s Ritz pair on `U`.
* `ReducingComplement A V` is the domain-aware statement that `Vᗮ` reduces `A`.

`UnboundedRitzPair.ofTrialBlock` builds the first from an
`BoundedCompressionTrialBlock`, so a caller who already has the bounded-compression
bundle -- the common case -- constructs nothing by hand.

What deliberately does *not* move into these objects is the mathematics: the
semiboundedness of the compression, the coercivity on the unwanted subspace, and
the crossed-defect condition (3.5) stay hypotheses of the theorem, because they
are what the theorem is about.
-/

namespace TauCeti
namespace DavisKahan

open TauCeti.DavisKahan.ExactSinTheta TauCeti.DavisKahan.TanTheta
  TauCeti.DavisKahan.TanTheta

universe u v

variable {𝕜 : Type u} [RCLike 𝕜]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [CompleteSpace H]

/-- **An unbounded Ritz pair for `A` on the trial subspace `Z`.**

Compression data together with exactly the two facts that make it the Ritz pair
of the ambient operator: the compression's domain sits inside `A`'s domain, and
the compression's ambient action is `A`'s. -/
structure UnboundedRitzPair (A : H →ₗ.[𝕜] H) (Z : Submodule 𝕜 H)
    [Z.HasOrthogonalProjection] [CompleteSpace Z] where
  /-- The compression and residual data. -/
  trial : UnboundedCompressionTrialData Z
  /-- Trial vectors in the compression's domain lie in the ambient domain. -/
  mem_domain : ∀ z : trial.compression.domain, ((z : Z) : H) ∈ A.domain
  /-- The compression's ambient action `A₀ z + R z` is the ambient action. -/
  action_eq : ∀ z : trial.compression.domain,
    trial.action z = A ⟨((z : Z) : H), mem_domain z⟩

/-- **`Vᗮ` reduces `A`, in the domain-aware sense.**

The projection onto `Vᗮ` preserves the domain of `A` and commutes with `A` on
it.  This is the hypothesis the tangent theorems use to move the ambient
operator past the complementary projection. -/
structure ReducingComplement (A : H →ₗ.[𝕜] H) (V : Submodule 𝕜 H)
    [V.HasOrthogonalProjection] where
  /-- The complementary projection preserves the domain. -/
  mapsDomain : ∀ x : A.domain, Vᗮ.starProjection ((x : H)) ∈ A.domain
  /-- The complementary projection commutes with the operator on the domain. -/
  commutes : ∀ x : A.domain,
    Vᗮ.starProjection (A x) = A ⟨Vᗮ.starProjection ((x : H)), mapsDomain x⟩

namespace UnboundedRitzPair

variable {A : H →ₗ.[𝕜] H} {Z : Submodule 𝕜 H}
  [Z.HasOrthogonalProjection] [CompleteSpace Z]

/-- **Every bounded trial block is an unbounded Ritz pair.**

The common case: the caller holds an `BoundedCompressionTrialBlock`, whose compression is
a bounded self-adjoint operator on the trial subspace and whose residual is the
ambient action's orthogonal part.  Nothing is assumed beyond what that bundle
already carries. -/
noncomputable def ofTrialBlock (D : BoundedCompressionTrialBlock A Z) :
    UnboundedRitzPair A Z where
  trial :=
    { compression := D.operator.toLinearMap.toPMap ⊤
      compression_isSelfAdjoint :=
        TauCeti.LinearPMap.isSelfAdjoint_toPMap_top D.operator_selfAdjoint
      residual := D.residual
      residual_orthogonal := fun z z' =>
        (Submodule.mem_orthogonal' _ _).mp (D.residual_mem_orthogonal z) _ z'.2 }
  mem_domain := fun z => D.domain_le (z : Z).2
  action_eq := fun z => by
    change ((D.operator (z : Z) : Z) : H) + D.residual ((z : Z)) = _
    rw [D.residual_apply]
    abel

omit [CompleteSpace H] in
/-- The Ritz pair built from a trial block keeps the block's residual. -/
@[simp]
theorem ofTrialBlock_residual (D : BoundedCompressionTrialBlock A Z) :
    (ofTrialBlock D).trial.residual = D.residual := rfl

end UnboundedRitzPair

namespace ReducingComplement

variable {A : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- **A reducing subspace gives a reducing complement.**

`TauCeti.LinearPMap.ReducesSubspace A V` is the repository's generic vocabulary
for "`V` reduces `A`": both projections preserve the domain and both summands are
invariant.  `ReducingComplement` is the single consequence the tangent theorems
consume -- that the complementary projection commutes with `A` on the domain --
and this is the bridge, so a caller who already holds a `ReducesSubspace`, for
instance from a spectral subspace, does not meet a competing reduction
vocabulary. -/
theorem ofReducesSubspace (h : TauCeti.LinearPMap.ReducesSubspace A V) :
    ReducingComplement A V where
  mapsDomain x := h.orthogonalProjection_mem_domain x
  commutes x := by
    have hVdom : V.starProjection ((x : H)) ∈ A.domain := h.projection_mem_domain x
    have hVpdom : Vᗮ.starProjection ((x : H)) ∈ A.domain :=
      h.orthogonalProjection_mem_domain x
    have hsplit :
        (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)
            + ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ = x := by
      apply Subtype.ext
      change V.starProjection ((x : H)) + Vᗮ.starProjection ((x : H)) = (x : H)
      rw [Submodule.starProjection_orthogonal_apply]
      abel
    have hmap : A x = A ⟨V.starProjection ((x : H)), hVdom⟩
        + A ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ := by
      have hadd := A.map_add (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)
        ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩
      rwa [hsplit] at hadd
    have hinV : A (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain) ∈ V :=
      h.invariant _ (V.starProjection_apply_mem _)
    have hinVp : A (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : A.domain) ∈ Vᗮ :=
      h.orthogonal_invariant _ (Vᗮ.starProjection_apply_mem _)
    rw [hmap, map_add]
    have h0 : Vᗮ.starProjection (A (⟨V.starProjection ((x : H)), hVdom⟩ : A.domain)) = 0 := by
      rw [Submodule.starProjection_orthogonal_apply,
        Submodule.starProjection_eq_self_iff.mpr hinV, sub_self]
    have h1 : Vᗮ.starProjection (A (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : A.domain))
        = A ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ :=
      Submodule.starProjection_eq_self_iff.mpr hinVp
    rw [h0, h1, zero_add]

end ReducingComplement

/-! ## The reflection in a subspace, as a hypothesis about the subspace

The unbounded `tan 2Θ` theorem is about a self-adjoint involution `Z` that
commutes with the perturbed operator.  For the source theorem `Z` is the
reflection in the chosen subspace, and self-adjointness and involutivity are then
theorems rather than hypotheses.  What genuinely remains is that reflecting
preserves the domain and commutes with `A + B` there. -/

omit [CompleteSpace H] in
/-- **A reducing subspace commutes with its own reflection.**

If `V` reduces the partial map `T`, then `J_V = 2 P_V - 1` preserves `T`'s domain
and `T J_V = J_V T` there.  Stated with the domain fact bound existentially,
because the commutation cannot be written without it.

This is the generic principal-angle-layer fact behind
`ReflectionIntertwines.ofReducesSubspace`; nothing in it is specific to a
perturbed operator or to Davis--Kahan. -/
theorem reflection_commutes_of_reducesSubspace
    {T : H →ₗ.[𝕜] H} {V : Submodule 𝕜 H} [V.HasOrthogonalProjection]
    (h : TauCeti.LinearPMap.ReducesSubspace T V) :
    ∃ hmaps : TauCeti.LinearPMap.MapsDomainTo T T (V.reflectionOperator),
      ∀ x : T.domain,
        T ⟨V.reflectionOperator ((x : H)), hmaps x⟩
          = V.reflectionOperator (T x) := by
  have hzeroV : ∀ z : H, z ∈ Vᗮ → V.starProjection z = 0 := by
    intro z hz
    have hs := Submodule.starProjection_orthogonal_apply (U := V) z
    rw [Submodule.starProjection_eq_self_iff.mpr hz] at hs
    exact sub_eq_self.mp hs.symm
  have hzeroVp : ∀ z : H, z ∈ V → Vᗮ.starProjection z = 0 := by
    intro z hz
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.starProjection_eq_self_iff.mpr hz, sub_self]
  have hrefl : ∀ y : H, V.reflectionOperator y
      = V.starProjection y - Vᗮ.starProjection y := by
    intro y
    rw [Submodule.starProjection_orthogonal_apply,
      Submodule.reflectionOperator_apply, two_smul]
    abel
  have hmaps : TauCeti.LinearPMap.MapsDomainTo T T (V.reflectionOperator) := by
    intro x
    rw [hrefl]
    exact T.domain.sub_mem (h.projection_mem_domain x)
      (h.orthogonalProjection_mem_domain x)
  refine ⟨hmaps, fun x => ?_⟩
  have hVdom : V.starProjection ((x : H)) ∈ T.domain := h.projection_mem_domain x
  have hVpdom : Vᗮ.starProjection ((x : H)) ∈ T.domain :=
    h.orthogonalProjection_mem_domain x
  have hsum :
      (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain)
          + ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ = x := by
    apply Subtype.ext
    change V.starProjection ((x : H)) + Vᗮ.starProjection ((x : H)) = (x : H)
    rw [Submodule.starProjection_orthogonal_apply]
    abel
  have hsplit :
      (⟨V.reflectionOperator ((x : H)), hmaps x⟩ : T.domain)
          = (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain)
            - ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ := by
    apply Subtype.ext
    exact hrefl ((x : H))
  have hTx : T x = T (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain)
      + T ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ := by
    have hadd := T.map_add (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain)
      ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩
    rwa [hsum] at hadd
  have hinV : T (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain) ∈ V :=
    h.invariant _ (V.starProjection_apply_mem _)
  have hinVp : T (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : T.domain) ∈ Vᗮ :=
    h.orthogonal_invariant _ (Vᗮ.starProjection_apply_mem _)
  have hproj : V.starProjection (T x)
      = T (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain) := by
    rw [hTx, map_add, Submodule.starProjection_eq_self_iff.mpr hinV,
      hzeroV _ hinVp, add_zero]
  have hprojp : Vᗮ.starProjection (T x)
      = T (⟨Vᗮ.starProjection ((x : H)), hVpdom⟩ : T.domain) := by
    rw [hTx, map_add, Submodule.starProjection_eq_self_iff.mpr hinVp,
      hzeroVp _ hinV, zero_add]
  have hsub := T.map_sub (⟨V.starProjection ((x : H)), hVdom⟩ : T.domain)
    ⟨Vᗮ.starProjection ((x : H)), hVpdom⟩
  rw [hsplit, hsub, ← hproj, ← hprojp, hrefl]

/-- **The reflection in `V` intertwines the perturbed operator.**

The domain-aware statement that `V.reflectionOperator` maps `A`'s domain into
itself and that reflecting commutes with `A + B` on that domain.  Self-adjointness
and involutivity of the reflection are *not* fields: they hold for every
subspace. -/
structure ReflectionIntertwines (A : H →ₗ.[𝕜] H) (B : H →L[𝕜] H)
    (V : Submodule 𝕜 H) [V.HasOrthogonalProjection] where
  /-- The reflection preserves the domain of `A`. -/
  mapsDomain : TauCeti.LinearPMap.MapsDomainTo A A (V.reflectionOperator)
  /-- Reflecting commutes with the perturbed operator on the domain. -/
  commutes : ∀ x : A.domain,
    A ⟨V.reflectionOperator (x : H), mapsDomain x⟩ +
        B (V.reflectionOperator (x : H))
      = V.reflectionOperator (A x) + V.reflectionOperator (B (x : H))

namespace ReflectionIntertwines

variable {A : H →ₗ.[𝕜] H} {B : H →L[𝕜] H} {V : Submodule 𝕜 H}
  [V.HasOrthogonalProjection]

omit [CompleteSpace H] in
/-- **A subspace that reduces the perturbed operator gives a reflection
intertwiner.**

`TauCeti.LinearPMap.ReducesSubspace (A.addBounded B) V` is the generic vocabulary
for "`V` reduces `A + B`", and `A + B` has exactly `A`'s domain, so the reflection
`2 P_V - 1` preserves that domain.  Commutation is
`TauCeti.DavisKahan.reflection_commutes_of_reducesSubspace` read through
`addBounded_apply`.

This is the bridge that keeps the source theorem free of a competing reduction
vocabulary: a caller holding a `ReducesSubspace` -- from a spectral subspace of the
perturbed operator, say -- constructs nothing by hand. -/
theorem ofReducesSubspace
    (h : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A B) V) :
    ReflectionIntertwines A B V := by
  obtain ⟨hmaps, hcomm⟩ := reflection_commutes_of_reducesSubspace h
  refine ⟨hmaps, fun x => ?_⟩
  have hx := hcomm x
  simp only [TauCeti.LinearPMap.addBounded_apply] at hx
  refine hx.trans ?_
  have hsplit : ((TauCeti.LinearPMap.addBounded A B) x : H) = A x + B ((x : H)) := rfl
  rw [hsplit, map_add]

end ReflectionIntertwines

end DavisKahan
end TauCeti
