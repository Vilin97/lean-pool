/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing

/-!
# Completion-model independence via the whole-space topology equality (P2.11)

The localization topology of the **whole-space datum** `globalLocData P` on
`Localization.Away (1 : A)` does not depend on the pair of definition `P`: its
`0`-neighborhoods are the `algebraMap`-images of the `Iₚⁿ`, and any two pairs of
definition present the *same* neighborhood filter of `0 ∈ A`
(`PairOfDefinition.hasBasis_nhds_zero`), so the two subgroup-bases mutually absorb
(`locTopology_globalLocData_eq`).

Consequently any two completion models are canonically isomorphic **with no
ambient hypotheses whatsoever** beyond the Huber structure — no `PlusSubring A`,
no `HasLocLiftPowerBounded A`, no `IsNoetherianRing A`, no
`CompatiblePlusSubring A`, no `CompleteSpace A` (P2.11's demand):
`completionModelCompare` is a ring equivalence, continuous in both directions
(`…_continuous`, `…_symm_continuous`), compatible with the canonical maps from `A`
(`…_canonicalMap`). It is the identity map of `Localization.Away 1` read across
the (equal) topologies, extended to the completions.

## Reference

Wedhorn Definition 6.1 / §6.1: the pair `(A₀, I)` *defines* the topology of `A`,
and any two pairs of definition present the same topology — that is the content of
`locTopology_globalLocData_eq`. The uniqueness making `completionModelCompare`
canonical is the universal property of the uniform completion
(`UniformSpace.Completion`, via `DenseRange.equalizer`); Wedhorn Remark 8.3 itself
is the identification of the global sections `𝒪_X(X)` with `Â` — it is *not* the
uniqueness statement.
-/

@[expose] public section

noncomputable section

open TopologicalSpace Filter Topology

universe u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsHuberRing A]

/-! ### The whole-space localization topology is pair-independent -/

omit [IsHuberRing A] in
/-- Membership in the `n`-th basic neighborhood of the whole-space datum: exactly
the `algebraMap`-images of `Iⁿ` (mem-form of `locNhd_singleton_one_eq`). -/
theorem mem_locNhd_globalLocData {P : PairOfDefinition A} {n : ℕ}
    {x : Localization.Away (1 : A)} :
    x ∈ locNhd P ({1} : Finset A) (1 : A) n ↔
      ∃ b : P.A₀, b ∈ (P.I ^ n : Ideal P.A₀) ∧
        algebraMap A (Localization.Away (1 : A)) (b : A) = x := by
  rw [← SetLike.mem_coe, locNhd_singleton_one_eq]
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨(b : A), ⟨b, hb, rfl⟩, rfl⟩

/-- **The whole-space localization topology does not depend on the pair of
definition** (Wedhorn §6.1: any two pairs of definition present the same
topology of `A`; the whole-space basic neighborhoods are the images of the
`Iⁿ`). -/
theorem locTopology_globalLocData_eq (P P' : PairOfDefinition A) :
    locTopology P ({1} : Finset A) (1 : A) (globalLocData P).hopen =
      locTopology P' ({1} : Finset A) (1 : A) (globalLocData P').hopen := by
  have h₁ := (locBasis P ({1} : Finset A) (1 : A)
    (globalLocData P).hopen).toRingFilterBasis.isTopologicalRing
  have h₂ := (locBasis P' ({1} : Finset A) (1 : A)
    (globalLocData P').hopen).toRingFilterBasis.isTopologicalRing
  refine IsTopologicalAddGroup.ext
    (@IsTopologicalRing.to_topologicalAddGroup _ _
      (locTopology P ({1} : Finset A) (1 : A) (globalLocData P).hopen) h₁)
    (@IsTopologicalRing.to_topologicalAddGroup _ _
      (locTopology P' ({1} : Finset A) (1 : A) (globalLocData P').hopen) h₂) ?_
  -- mutual absorption of the two `0`-neighborhood bases via the `A`-level bases
  have habs : ∀ (Q Q' : PairOfDefinition A) (n : ℕ), ∃ m : ℕ,
      (locNhd Q' ({1} : Finset A) (1 : A) m : Set (Localization.Away (1 : A))) ⊆
        locNhd Q ({1} : Finset A) (1 : A) n := by
    intro Q Q' n
    -- the `A`-level absorption
    have hmem : (Subtype.val '' ((Q.I ^ n : Ideal Q.A₀) : Set Q.A₀)) ∈ 𝓝 (0 : A) :=
      Q.hasBasis_nhds_zero.mem_of_mem (i := n) trivial
    obtain ⟨m, -, hm⟩ := Q'.hasBasis_nhds_zero.mem_iff.mp hmem
    refine ⟨m, ?_⟩
    intro x hx
    obtain ⟨b, hb, rfl⟩ := mem_locNhd_globalLocData.mp hx
    obtain ⟨⟨c, hcA₀⟩, hcI, hcb⟩ := hm ⟨b, hb, rfl⟩
    refine mem_locNhd_globalLocData.mpr ⟨⟨c, hcA₀⟩, hcI, ?_⟩
    show algebraMap A (Localization.Away (1 : A)) c = _
    rw [show c = (b : A) from hcb]
  refine Filter.HasBasis.ext
    ((locBasis P ({1} : Finset A) (1 : A)
      (globalLocData P).hopen).hasBasis_nhds_zero)
    ((locBasis P' ({1} : Finset A) (1 : A)
      (globalLocData P').hopen).hasBasis_nhds_zero) ?_ ?_
  · intro n _
    obtain ⟨m, hm⟩ := habs P P' n
    exact ⟨m, trivial, hm⟩
  · intro n _
    obtain ⟨m, hm⟩ := habs P' P n
    exact ⟨m, trivial, hm⟩


/-! ### The clean comparison of completion models -/

section Compare

instance (P : PairOfDefinition A) : UniformSpace (CompletionModel A P) :=
  inferInstanceAs (UniformSpace (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : IsUniformAddGroup (CompletionModel A P) :=
  inferInstanceAs (IsUniformAddGroup (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : T0Space (CompletionModel A P) :=
  inferInstanceAs (T0Space (presheafValue (globalLocData P)))

instance (P : PairOfDefinition A) : CompleteSpace (CompletionModel A P) :=
  inferInstanceAs (CompleteSpace (presheafValue (globalLocData P)))

variable (P P' : PairOfDefinition A)

/-- The `P'`-side completion map, retyped on the (definitionally equal) `P`-side
localization, is continuous for the `P`-side topology — the two whole-space
topologies coincide (`locTopology_globalLocData_eq`). -/
private theorem coe_continuous_cross :
    @Continuous _ _ (globalLocData P).topology _
      ((⇑((globalLocData P').coeRingHom) :
        Localization.Away ((globalLocData P).s) → CompletionModel A P')) := by
  have heq : (globalLocData P).topology = (globalLocData P').topology := by
    show locTopology P ({1} : Finset A) (1 : A) (globalLocData P).hopen =
      locTopology P' ({1} : Finset A) (1 : A) (globalLocData P').hopen
    exact locTopology_globalLocData_eq P P'
  rw [heq]
  exact @UniformSpace.Completion.continuous_coe _ (globalLocData P').uniformSpace

/-- One direction of the clean comparison: the identity of the whole-space
localization read across the equal topologies, extended to the completions. -/
noncomputable def compareHom : CompletionModel A P →+* CompletionModel A P' := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : IsTopologicalRing (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom
    (((globalLocData P').coeRingHom :
      Localization.Away ((globalLocData P).s) →+* CompletionModel A P'))
    (coe_continuous_cross P P')

theorem compareHom_coe (l : Localization.Away ((globalLocData P).s)) :
    compareHom P P' ((globalLocData P).coeRingHom l) =
      (globalLocData P').coeRingHom l := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  letI : IsTopologicalRing (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe _ _ l

theorem compareHom_continuous : Continuous (compareHom P P') := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  exact UniformSpace.Completion.continuous_extension

theorem compareHom_compareHom (x : CompletionModel A P) :
    compareHom P' P (compareHom P P' x) = x := by
  letI : UniformSpace (Localization.Away ((globalLocData P).s)) :=
    (globalLocData P).uniformSpace
  have hdense : DenseRange (⇑((globalLocData P).coeRingHom)) :=
    @UniformSpace.Completion.denseRange_coe _ (globalLocData P).uniformSpace
  have hfun : ⇑(compareHom P' P) ∘ ⇑(compareHom P P') =
      (id : CompletionModel A P → CompletionModel A P) := by
    refine @DenseRange.equalizer _ _ _ _ _
      (inferInstanceAs (T2Space (presheafValue (globalLocData P)))) _ hdense _ _
      ?_ continuous_id ?_
    · exact (compareHom_continuous P' P).comp (compareHom_continuous P P')
    · funext l
      show compareHom P' P (compareHom P P' ((globalLocData P).coeRingHom l)) =
        (globalLocData P).coeRingHom l
      rw [compareHom_coe P P' l]
      exact compareHom_coe P' P l
  exact congr_fun hfun x

/-- **The clean comparison of completion models** (P2.11): a ring equivalence
requiring only the Huber structure on `A` — no `PlusSubring`, no
`HasLocLiftPowerBounded`, no `IsNoetherianRing`, no `CompatiblePlusSubring`, no
`CompleteSpace`. -/
noncomputable def completionModelCompare :
    CompletionModel A P ≃+* CompletionModel A P' where
  toFun := compareHom P P'
  invFun := compareHom P' P
  left_inv := compareHom_compareHom P P'
  right_inv := compareHom_compareHom P' P
  map_mul' := map_mul _
  map_add' := map_add _

theorem completionModelCompare_continuous :
    Continuous (completionModelCompare P P') :=
  compareHom_continuous P P'

theorem completionModelCompare_symm_continuous :
    Continuous (completionModelCompare P P').symm :=
  compareHom_continuous P' P

/-- The clean comparison intertwines the canonical maps `A → Â` (the completion
maps into the global sections of Wedhorn Remark 8.3; the compatibility itself is
the universal property of the completion). -/
theorem completionModelCompare_canonicalMap (a : A) :
    completionModelCompare P P' ((globalLocData P).canonicalMap a) =
      (globalLocData P').canonicalMap a :=
  compareHom_coe P P'
    (algebraMap A (Localization.Away ((globalLocData P).s)) a)

end Compare

end ValuationSpectrum
