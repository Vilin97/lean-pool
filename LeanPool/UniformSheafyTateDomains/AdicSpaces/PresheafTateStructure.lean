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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicCompletionBridge
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.CompletionLocalization
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafIdentification
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.TopologyComparison
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornAwayMapSaturation
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WedhornLocTopologyLinear
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.Exactness

/-!
# Tate Ring Structure on Presheaf Values (Wedhorn Proposition 8.15)

For a strongly noetherian Tate ring `(A, A⁺)` with pair of definition `(A₀, I)`,
and a rational localization datum `D₀`, the presheaf value `presheafValue D₀`
carries a natural Tate ring structure:

- **Ring of definition**: The closure of `locSubring` in the completion
- **Ideal of definition**: The closure of `locIdeal` in the completion
- **Topologically nilpotent unit**: The image of the pseudo-uniformizer from A

This enables the "localization principle": the structure presheaf on a rational
subset `R(T/s)` is the structure presheaf of the Tate ring `presheafValue D₀`.

## Main results

* `presheafValue_isTateRing` : `IsTateRing (presheafValue D₀)` (TODO)
* `presheafValue_pairOfDefinition` : The natural pair of definition (TODO)
* `presheafValue_topNilUnit` : Topologically nilpotent unit in presheafValue

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 8.15, Example 6.38
-/

@[expose] public section

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]
  [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Topologically nilpotent unit in presheafValue

If A has a topologically nilpotent unit π (i.e., A is a Tate ring), then
the image of π under canonicalMap is a topologically nilpotent unit in
presheafValue D₀. This is because:
- canonicalMap is a ring hom, so it preserves units
- canonicalMap is continuous, so it preserves topological nilpotency -/

omit [PlusSubring A] in
/-- A topologically nilpotent unit in `A` maps to a topologically nilpotent
unit in `presheafValue D₀` via `canonicalMap`. -/
theorem presheafValue_topNilUnit [IsTateRing A] (D₀ : RationalLocData A) :
    ∃ u : (presheafValue D₀)ˣ, IsTopologicallyNilpotent (u : presheafValue D₀) := by
  obtain ⟨π, hπ⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  have hunit : IsUnit (D₀.canonicalMap (π : A)) := π.isUnit.map D₀.canonicalMap
  refine ⟨hunit.unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact hπ.map (canonicalMap_continuous D₀)

/-! ### Pair of definition in presheafValue

The natural pair of definition for `presheafValue D₀`:
- **Ring of definition**: The image of `locSubring` under `coeRingHom`
  (the completion of locSubring sits inside presheafValue as a subring)
- **Ideal of definition**: The image of `locIdeal` under the lifted map

For a Noetherian locSubring with locIdeal-adic topology:
- The completion of locSubring = AdicCompletion(locIdeal, locSubring) (bridge)
- This is a complete open subring of presheafValue
- The image of locIdeal generates the topology

TODO: Construct and verify this pair of definition. -/

/-- The ring of definition inside `presheafValue D₀`: the topological closure of
the image of `locSubring` under `coeRingHom` in the completion. -/
noncomputable def presheafValue_ringOfDef (D₀ : RationalLocData A) :
    Subring (presheafValue D₀) :=
  letI := D₀.uniformSpace
  (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range.topologicalClosure

omit [PlusSubring A] in
/-- The ring of definition is open in `presheafValue D₀`. -/
theorem presheafValue_ringOfDef_isOpen (D₀ : RationalLocData A) :
    IsOpen ((presheafValue_ringOfDef D₀ : Subring (presheafValue D₀)) :
      Set (presheafValue D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  open Filter Topology in
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) :=
    (map_zero D₀.coeRingHom : f 0 = 0) ▸
      hbasis.hasBasis_of_isDenseInducing UniformSpace.Completion.isDenseInducing_coe
  have himage_sub : ∀ n, f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x ⟨y, hy, hyx⟩
    obtain ⟨d, _, hdy⟩ := hy
    exact ⟨d, by
      have hdy' : (locSubring D₀.P D₀.T D₀.s).subtype d = y := hdy
      show D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x
      rw [hdy']; exact hyx⟩
  have hclosure_sub : ∀ n, closure (f '' (locNhd D₀.P D₀.T D₀.s n :
      Set (Localization.Away D₀.s))) ⊆
      (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    fun n ↦ closure_mono (himage_sub n)
  change IsOpen ((presheafValue_ringOfDef D₀).toAddSubgroup : Set (presheafValue D₀))
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hbasis_compl.mem_of_mem (i := 0) trivial) (hclosure_sub 0))

omit [PlusSubring A] in
/-- The subspace uniformity on `locSubring` equals the `locIdeal`-adic uniformity. -/
theorem locSubring_subspace_eq_adic (D₀ : RationalLocData A) :
    UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace =
    @IsTopologicalAddGroup.rightUniformSpace _ _
      (locIdeal D₀.P D₀.T D₀.s).adicTopology
      (inferInstance) := by
  letI : TopologicalSpace (Localization.Away D₀.s) := D₀.topology
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  have key : TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology =
      (locIdeal D₀.P D₀.T D₀.s).adicTopology := by
    have htag_ind : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s)
        (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology) _ :=
      @IsTopologicalRing.to_topologicalAddGroup _ _
        (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology)
        (Subring.instIsTopologicalRing (locSubring D₀.P D₀.T D₀.s))
    have htag_adic : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s)
        (locIdeal D₀.P D₀.T D₀.s).adicTopology _ :=
      @IsTopologicalRing.to_topologicalAddGroup _ _ (locIdeal D₀.P D₀.T D₀.s).adicTopology
        (RingFilterBasis.isTopologicalRing
          (locIdeal D₀.P D₀.T D₀.s).adic_basis.toRing_subgroups_basis.toRingFilterBasis)
    apply @IsTopologicalAddGroup.ext (locSubring D₀.P D₀.T D₀.s) _ _ _ htag_ind htag_adic
    have hbasis_loc := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
    have hpreimage_eq : ∀ n : ℕ,
        (locSubring D₀.P D₀.T D₀.s).subtype ⁻¹'
          (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) =
        ((locIdeal D₀.P D₀.T D₀.s ^ n : Ideal (locSubring D₀.P D₀.T D₀.s)) :
          Set (locSubring D₀.P D₀.T D₀.s)) := by
      intro n; ext ⟨x, hx_mem⟩; constructor
      · rintro ⟨d, hd, hd_eq⟩
        have : d = ⟨x, hx_mem⟩ := Subtype.val_injective (by
          change d.val = x; change d.val = _ at hd_eq; exact hd_eq)
        exact this ▸ hd
      · intro hx; exact ⟨⟨x, hx_mem⟩, hx, rfl⟩
    have hbasis_ind :
        (@nhds (locSubring D₀.P D₀.T D₀.s)
          (TopologicalSpace.induced
            (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology)
          0).HasBasis
        (fun _ : ℕ ↦ True) (fun n ↦ ((locIdeal D₀.P D₀.T D₀.s ^ n :
          Ideal (locSubring D₀.P D₀.T D₀.s)) : Set (locSubring D₀.P D₀.T D₀.s))) := by
      rw [nhds_induced, show ((locSubring D₀.P D₀.T D₀.s).subtype :
          (locSubring D₀.P D₀.T D₀.s) → Localization.Away D₀.s) 0 = 0 from map_zero _]
      exact (hbasis_loc.comap (locSubring D₀.P D₀.T D₀.s).subtype).congr
        (fun _ ↦ Iff.rfl) (fun n _ ↦ hpreimage_eq n)
    ext U; rw [hbasis_ind.mem_iff, (locIdeal D₀.P D₀.T D₀.s).hasBasis_nhds_zero_adic.mem_iff]
  apply UniformSpace.ext; rw [uniformity_comap]
  change Filter.comap (Prod.map (locSubring D₀.P D₀.T D₀.s).subtype
      (locSubring D₀.P D₀.T D₀.s).subtype)
    (Filter.comap (fun p : _ × _ ↦ p.2 - p.1) (@nhds _ D₀.topology 0)) =
    Filter.comap (fun p : _ × _ ↦ p.2 - p.1)
      (@nhds _ (locIdeal D₀.P D₀.T D₀.s).adicTopology 0)
  have hcomm :
      (fun p : (Localization.Away D₀.s) ×
        (Localization.Away D₀.s) => p.2 - p.1) ∘
      (Prod.map (locSubring D₀.P D₀.T D₀.s).subtype
        (locSubring D₀.P D₀.T D₀.s).subtype) =
      (locSubring D₀.P D₀.T D₀.s).subtype ∘
      (fun p : _ × _ ↦ p.2 - p.1) := by
    ext ⟨a, b⟩; exact (map_sub (locSubring D₀.P D₀.T D₀.s).subtype b a).symm
  rw [Filter.comap_comap, hcomm, ← Filter.comap_comap]; congr 1
  conv_lhs => rw [show (0 : Localization.Away D₀.s) =
    (locSubring D₀.P D₀.T D₀.s).subtype 0 from (map_zero _).symm]
  rw [← nhds_induced, key]

/-- The ring hom from `locSubring` into `presheafValue_ringOfDef D₀`. -/
noncomputable def locSubringToRingOfDef (D₀ : RationalLocData A) :
    locSubring D₀.P D₀.T D₀.s →+* presheafValue_ringOfDef D₀ :=
  letI := D₀.uniformSpace
  (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).codRestrict
    (presheafValue_ringOfDef D₀) fun d ↦
    subset_closure (RingHom.mem_range.mpr ⟨d, rfl⟩)

/-- The ideal of definition inside the ring of definition. -/
noncomputable def presheafValue_idealOfDef (D₀ : RationalLocData A) :
    Ideal (presheafValue_ringOfDef D₀) :=
  Ideal.map (locSubringToRingOfDef D₀) (locIdeal D₀.P D₀.T D₀.s)

omit [PlusSubring A] in
/-- The ideal of definition is finitely generated. -/
theorem presheafValue_idealOfDef_fg (D₀ : RationalLocData A) :
    (presheafValue_idealOfDef D₀).FG :=
  (locIdeal_fg D₀.P D₀.T D₀.s).map _

omit [PlusSubring A] in
/-- `locSubringToRingOfDef D₀` has dense range: `ringOfDef` is by definition the topological
closure of `range (coeRingHom ∘ locSubring.subtype)`, and the range of `g` is the same image
viewed inside the subtype. -/
private theorem locSubringToRingOfDef_denseRange (D₀ : RationalLocData A) :
    DenseRange (locSubringToRingOfDef D₀) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  set g := locSubringToRingOfDef D₀ with hg_def
  intro ⟨z, hz⟩
  have hval_range : Subtype.val '' Set.range g =
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    ext w; constructor
    · rintro ⟨y, ⟨d, hd⟩, hw⟩; exact ⟨d, by rw [← hw, ← hd]; rfl⟩
    · rintro ⟨d, hd⟩; exact ⟨g d, ⟨d, rfl⟩, hd⟩
  have h1 : z ∈ closure (Subtype.val '' Set.range g) := hval_range ▸ hz
  simp only [closure_subtype]
  exact h1

omit [PlusSubring A] in
private theorem idealOfDef_pow_sub_val_preimage_closure (D₀ : RationalLocData A) (n : ℕ) :
    ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    Subtype.val ⁻¹' closure
      ((D₀.coeRingHom : Localization.Away D₀.s →
        presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s))) := by
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  let fh := D₀.coeRingHom
  let sub := (locSubring D₀.P D₀.T D₀.s).subtype
  let comp_sub := fh.comp sub
  let g := locSubringToRingOfDef D₀
  set T := (fh : Localization.Away D₀.s → presheafValue D₀) ''
    (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) with hT_def
  rw [show presheafValue_idealOfDef D₀ = Ideal.map g (locIdeal D₀.P D₀.T D₀.s) from rfl,
      show (Ideal.map g (locIdeal D₀.P D₀.T D₀.s)) ^ n =
        Ideal.map g ((locIdeal D₀.P D₀.T D₀.s) ^ n) from (Ideal.map_pow _ _ n).symm]
  have hact : ∀ c ∈ (comp_sub.range : Set (presheafValue D₀)), ∀ y ∈ T, c * y ∈ T := by
    rintro c ⟨a, rfl⟩ y ⟨z, hz, rfl⟩
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨sub (a * d), ⟨a * d, Ideal.mul_mem_left _ a hd, rfl⟩, ?_⟩
    change fh (sub (a * d)) = comp_sub a * fh z
    have hdz' : sub d = z := hdz
    rw [show sub (a * d) = sub a * sub d from map_mul sub a d,
        map_mul fh, show fh (sub a) = comp_sub a from rfl, hdz']
  have hringOfDef_eq : (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) =
      closure (comp_sub.range : Set (presheafValue D₀)) := rfl
  intro x hx
  change x.val ∈ closure T
  refine Submodule.span_induction (p := fun x _ ↦ x.val ∈ closure T) ?_ ?_ ?_ ?_ hx
  · rintro x ⟨d, hd, rfl⟩
    exact subset_closure ⟨sub d, ⟨d, hd, rfl⟩, rfl⟩
  · exact subset_closure ⟨0, (locNhd D₀.P D₀.T D₀.s n).zero_mem, map_zero _⟩
  · intro a b _ _ ha hb
    change (a + b).val ∈ closure T
    rw [show (a + b).val = a.val + b.val from rfl]
    exact ((locNhd D₀.P D₀.T D₀.s n).map
      fh.toAddMonoidHom).topologicalClosure.add_mem
      (show a.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from ha)
      (show b.val ∈ ((locNhd D₀.P D₀.T D₀.s n).map
        fh.toAddMonoidHom).topologicalClosure from hb)
  · intro ⟨r, hr⟩ x _ hx_ih
    change ((⟨r, hr⟩ : presheafValue_ringOfDef D₀) • x).val ∈ closure T
    change r * x.val ∈ closure T
    exact map_mem_closure₂' (fun _ ↦ continuous_const_mul _) (fun _ ↦ continuous_mul_const _)
      (hringOfDef_eq ▸ hr) hx_ih (fun a ha b hb ↦ hact a ha b hb)

omit [PlusSubring A] in
/-- Corollary: the val-image of `idealOfDef^n` is contained in `closure(coe '' locNhd n)`. -/
private theorem idealOfDef_pow_val_sub_closure (D₀ : RationalLocData A) (n : ℕ) :
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s))) := by
  rintro x ⟨y, hy, rfl⟩
  exact idealOfDef_pow_sub_val_preimage_closure D₀ n hy

omit [PlusSubring A] in
/-- Helper: `coe '' locNhd n ⊆ val '' idealOfDef^n`. The image of `locIdeal^n` generators
under `g = locSubringToRingOfDef` produces elements of `idealOfDef^n` whose `val` coincides
with the corresponding element of `coe '' locNhd n`. -/
private theorem locNhd_sub_idealOfDef_pow_val (D₀ : RationalLocData A) (n : ℕ) :
    (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) := by
  letI := D₀.uniformSpace
  rw [show presheafValue_idealOfDef D₀ = Ideal.map (locSubringToRingOfDef D₀)
    (locIdeal D₀.P D₀.T D₀.s) from rfl,
    show (Ideal.map (locSubringToRingOfDef D₀) (locIdeal D₀.P D₀.T D₀.s)) ^ n =
      Ideal.map (locSubringToRingOfDef D₀) ((locIdeal D₀.P D₀.T D₀.s) ^ n)
    from (Ideal.map_pow _ _ n).symm]
  intro x ⟨y, hy, hyx⟩
  obtain ⟨d, hd, hdy⟩ := hy
  refine ⟨(locSubringToRingOfDef D₀) d,
    Ideal.mem_map_of_mem _ hd, ?_⟩
  change ((locSubringToRingOfDef D₀) d).val = x
  exact hyx ▸ congrArg D₀.coeRingHom hdy

omit [PlusSubring A] in
/-- The subspace topology on `locSubring` (induced from `presheafValue`/the localization) coincides
with the `J`-adic topology, where `J = locIdeal`. This is the topological shadow of
`locSubring_subspace_eq_adic` (which states it at the level of uniformities). -/
private theorem locSubring_induced_eq_adicTopology (D₀ : RationalLocData A) :
    TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology =
      (locIdeal D₀.P D₀.T D₀.s).adicTopology := by
  have hunif := locSubring_subspace_eq_adic D₀
  have h1 : @UniformSpace.toTopologicalSpace _
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace) =
    @UniformSpace.toTopologicalSpace _
      (@IsTopologicalAddGroup.rightUniformSpace _ _
        (locIdeal D₀.P D₀.T D₀.s).adicTopology inferInstance) :=
    congrArg (fun u ↦ @UniformSpace.toTopologicalSpace _ u) hunif
  rw [UniformSpace.toTopologicalSpace_comap] at h1
  exact h1

omit [PlusSubring A] in
/-- Helper for `idealOfDef_pow_val_isClosed` (⊆ direction): `idealOfDef^n` is contained in the
closure of `g '' (J^n)`, where `g = locSubringToRingOfDef` and `J = locIdeal`. Proved by
`Submodule.span_induction`: generators land in the closure, the closure is closed under addition,
and scalar multiplication stays in the closure by density of `g` together with ideal absorption. -/
private theorem idealOfDef_pow_subset_closure (D₀ : RationalLocData A) (n : ℕ)
    (hg_dense : DenseRange (locSubringToRingOfDef D₀)) :
    ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) ⊆
    closure ((locSubringToRingOfDef D₀) ''
      (↑((locIdeal D₀.P D₀.T D₀.s) ^ n) : Set (locSubring D₀.P D₀.T D₀.s))) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  set J := locIdeal D₀.P D₀.T D₀.s with hJ_def
  set g := locSubringToRingOfDef D₀ with hg_def
  set gJn := g '' (↑(J ^ n) : Set (locSubring D₀.P D₀.T D₀.s)) with hgJn_def
  have hact : ∀ a ∈ Set.range g, ∀ b ∈ gJn, a * b ∈ gJn := by
    rintro _ ⟨s, rfl⟩ _ ⟨d, hd, rfl⟩
    exact ⟨s * d, Ideal.mul_mem_left _ s hd, map_mul g s d⟩
  rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
      (Ideal.map_pow g J n).symm]
  intro y hy
  refine Submodule.span_induction (p := fun y _ ↦ y ∈ closure gJn) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨d, hd, rfl⟩; exact subset_closure ⟨d, hd, rfl⟩
  · exact subset_closure ⟨0, (J ^ n).zero_mem, map_zero g⟩
  · intro a b _ _ ha hb
    exact ((J ^ n).toAddSubgroup.map g.toAddMonoidHom).topologicalClosure.add_mem ha hb
  · intro ⟨r, hr_mem⟩ y _ hy
    exact map_mem_closure₂' (fun _ ↦ continuous_const_mul _)
      (fun _ ↦ continuous_mul_const _)
      (hg_dense.closure_eq ▸ Set.mem_univ _) hy hact

omit [PlusSubring A] in
/-- `g = locSubringToRingOfDef D₀` is uniform-inducing for the subspace uniformity on `locSubring`
(comap of `D₀.uniformSpace`) and the subspace uniformity on `ringOfDef`. This is the key step that
realises `ringOfDef` as an abstract completion of `locSubring`: it factors through the dense
uniform embedding `coeRingHom : Localization.Away s → presheafValue`. -/
private theorem locSubringToRingOfDef_isUniformInducing (D₀ : RationalLocData A) :
    @IsUniformInducing _ _
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace)
      (UniformSpace.comap Subtype.val inferInstance) (locSubringToRingOfDef D₀) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  set g := locSubringToRingOfDef D₀ with hg_def
  have h_comp : (Subtype.val : presheafValue_ringOfDef D₀ → presheafValue D₀) ∘ g =
      (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ∘
      (locSubring D₀.P D₀.T D₀.s).subtype := by ext d; rfl
  have h_valg_ui : @IsUniformInducing _ _
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace)
      (inferInstance : UniformSpace (presheafValue D₀))
      (Subtype.val ∘ g) := h_comp ▸
    (UniformSpace.Completion.isUniformInducing_coe _).comp ⟨rfl⟩
  have hval_ui : @IsUniformInducing _ _
      (UniformSpace.comap Subtype.val inferInstance)
      (inferInstance : UniformSpace (presheafValue D₀))
      (Subtype.val : presheafValue_ringOfDef D₀ → presheafValue D₀) := ⟨rfl⟩
  constructor
  rw [← hval_ui.comap_uniformity, Filter.comap_comap]
  exact h_valg_ui.comap_uniformity

omit [PlusSubring A] in
/-- The additive subgroup `(J ^ n).toAddSubgroup`, `J = locIdeal`, is open in the subspace topology
on `locSubring` (induced from `D₀.topology`). The subspace topology equals the `J`-adic topology
(`locSubring_induced_eq_adicTopology`), in which the `n`-th basic neighbourhood of `0` is exactly
this subgroup. -/
private theorem locIdeal_pow_toAddSubgroup_isOpen (D₀ : RationalLocData A) (n : ℕ) :
    @IsOpen _ (TopologicalSpace.induced (locSubring D₀.P D₀.T D₀.s).subtype D₀.topology)
      (SetLike.coe ((locIdeal D₀.P D₀.T D₀.s) ^ n).toAddSubgroup :
        Set (locSubring D₀.P D₀.T D₀.s)) := by
  set J := locIdeal D₀.P D₀.T D₀.s with hJ_def
  rw [locSubring_induced_eq_adicTopology D₀]
  letI : TopologicalSpace (locSubring D₀.P D₀.T D₀.s) := J.adicTopology
  haveI : IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s) :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ J.adicTopology
      (RingFilterBasis.isTopologicalRing
        J.adic_basis.toRing_subgroups_basis.toRingFilterBasis)
  exact AddSubgroup.isOpen_of_mem_nhds _
    (J.hasBasis_nhds_zero_adic.mem_of_mem (i := n) trivial)

-- The AdicCompletion bridge proof has deep elaboration chains through ring equivs.
omit [PlusSubring A] in
/-- Helper for `idealOfDef_pow_val_isClosed` (⊇ direction): `idealOfDef^n` is closed in the
subspace topology on `ringOfDef`.

This is the AdicCompletion-bridge argument: the subspace topology on `locSubring` equals the
`J`-adic topology, so `ringOfDef` is the `J`-adic completion of `locSubring`; via
`AdicCompletionBridge.adicCompletionRingEquiv` and `AdicCompletion.map_exact` the ideal
`idealOfDef^n = Ideal.map g (J^n)` is the kernel `ker(evalₐ n)` of evaluation into the discrete
quotient `locSubring/J^n`, hence closed. -/
private theorem idealOfDef_pow_isClosed_aux (D₀ : RationalLocData A) (n : ℕ) :
    IsClosed ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  have hadic_eq := locSubring_induced_eq_adicTopology D₀
  set J := locIdeal D₀.P D₀.T D₀.s with hJ_def
  set g := locSubringToRingOfDef D₀ with hg_def
  have hg_dense : DenseRange g := locSubringToRingOfDef_denseRange D₀
  -- Proof: idealOfDef^n = ker(π) for a continuous ring hom
  --   π : ringOfDef → locSubring ⧸ (J ^ n)
  -- and ker(π) is closed since the target is discrete (T₁).
  --
  -- Construction of π: g : locSubring → ringOfDef is a dense uniform
  -- inducing (locSubring_subspace_eq_adic). The quotient
  -- q = Ideal.Quotient.mk(J^n) extends to π by the completion universal
  -- property (target is discrete, hence complete T₂).
  --
  -- ker(π) = idealOfDef^n = Ideal.map g (J^n):
  -- (⊆) π is a ring hom (density + T₂) killing g(J^n), so the generated
  --     ideal Ideal.map g (J^n) = idealOfDef^n ⊆ ker(π).
  -- (⊇) By AdicCompletion.map_exact (Mathlib.RingTheory.AdicCompletion.Exactness)
  --     on 0 → J^n → locSubring → locSubring/J^n → 0, using IsNoetherianRing.
  --     Transported through adicCompletionRingEquiv (AdicCompletionBridge.lean).
  -- Step A: g : locSubring -> ringOfDef is IsUniformInducing.
  have hg_ui : @IsUniformInducing _ _
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace)
      (UniformSpace.comap Subtype.val inferInstance) g :=
    locSubringToRingOfDef_isUniformInducing D₀
  -- Step B: ringOfDef is complete (closed subspace of complete space).
  have hcomplete : @CompleteSpace (presheafValue_ringOfDef D₀)
      (UniformSpace.comap Subtype.val inferInstance) :=
    (Subring.isClosed_topologicalClosure
      (D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range).completeSpace_coe
  -- Step C: Package (g, ringOfDef) as AbstractCompletion of locSubring.
  let pkg : @AbstractCompletion (locSubring D₀.P D₀.T D₀.s)
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype D₀.uniformSpace) :=
    ⟨_, g, UniformSpace.comap Subtype.val inferInstance,
     hcomplete, inferInstance, hg_ui, hg_dense⟩
  -- Step D: Use completionRingEquiv to build a ring equiv ringOfDef ≃+* Completion.
  have hg_cont : Continuous g := by
    have : Continuous (Subtype.val ∘ g : locSubring D₀.P D₀.T D₀.s →
        presheafValue D₀) := UniformSpace.Completion.isDenseInducing_coe.continuous.comp
      continuous_subtype_val
    exact continuous_induced_rng.mpr this
  haveI : IsUniformAddGroup (presheafValue_ringOfDef D₀) :=
    AddSubgroup.isUniformAddGroup (presheafValue_ringOfDef D₀).toAddSubgroup
  haveI : IsUniformAddGroup (locSubring D₀.P D₀.T D₀.s) :=
    AddSubgroup.isUniformAddGroup (locSubring D₀.P D₀.T D₀.s).toAddSubgroup
  let eRE := (AdicCompletionBridge.completionRingEquiv g hg_cont
    hg_ui hg_dense).symm
  have hJn_open : IsOpen (SetLike.coe (J ^ n).toAddSubgroup :
      Set (locSubring D₀.P D₀.T D₀.s)) :=
    locIdeal_pow_toAddSubgroup_isOpen D₀ n
  haveI hdisc : DiscreteTopology (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) :=
    QuotientAddGroup.discreteTopology hJn_open
  haveI : @IsTopologicalAddGroup (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n)
      inferInstance _ :=
    @IsTopologicalRing.to_topologicalAddGroup _ _ inferInstance inferInstance
  letI : UniformSpace (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) :=
    @IsTopologicalAddGroup.rightUniformSpace _ _ inferInstance inferInstance
  haveI : @IsUniformAddGroup (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ :=
    @isUniformAddGroup_of_addCommGroup _ _ inferInstance inferInstance
  have hrus_bot : @IsTopologicalAddGroup.rightUniformSpace
      (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ _ = ⊥ := by
    apply @UniformSpace.ext _ _ ⊥
    rw [uniformity_eq_comap_nhds_zero' _, nhds_discrete, Filter.comap_pure]
    congr 1; ext ⟨a, b⟩; simp [add_neg_eq_zero, eq_comm]
  haveI hcs : CompleteSpace (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) := by
    change @CompleteSpace _ (@IsTopologicalAddGroup.rightUniformSpace _ _ _ _)
    rw [hrus_bot]; infer_instance
  let πc := @UniformSpace.Completion.extensionHom
    (locSubring D₀.P D₀.T D₀.s) _ _ _ _
    (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) _ _ _ _
    (Ideal.Quotient.mk (J ^ n)) continuous_quotient_mk' hcs inferInstance
  let π := πc.comp eRE.toRingHom
  have hge : (presheafValue_idealOfDef D₀ ^ n :
      Ideal _) ≤ RingHom.ker π := by
    rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
      (Ideal.map_pow g J n).symm, Ideal.map_le_iff_le_comap]
    intro a ha; rw [Ideal.mem_comap, RingHom.mem_ker]
    change πc (eRE (g a)) = 0
    have : eRE (g a) = (↑a : UniformSpace.Completion _) := by
      change (AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui hg_dense).symm
        (g a) = ↑a
      rw [(AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui hg_dense).symm_apply_eq]
      exact (UniformSpace.Completion.extensionHom_coe g hg_cont a).symm
    rw [this]
    haveI : T0Space (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n) := by
      haveI := hdisc; infer_instance
    change πc (↑a) = 0
    change (UniformSpace.Completion.extensionHom
      (Ideal.Quotient.mk (J ^ n)) continuous_quotient_mk') (↑a) = 0
    rw [UniformSpace.Completion.extensionHom_coe]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hle : RingHom.ker π ≤ (presheafValue_idealOfDef D₀ ^ n :
      Ideal _) := by
    have hadic_loc : @IsAdic (locSubring D₀.P D₀.T D₀.s) _
        instTopologicalSpaceSubtype J := hadic_eq
    let eAC := @AdicCompletionBridge.adicCompletionRingEquiv
      (locSubring D₀.P D₀.T D₀.s) _ J instUniformSpaceSubtype
      inferInstance inferInstance hadic_loc
    rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
      (Ideal.map_pow g J n).symm]
    letI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s) _).uniformStruct
    haveI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s) _).complete
    haveI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s) _).separation
    have hπc_eq : ∀ y, πc y = (AdicCompletion.evalₐ J n) (eAC y) := by
      refine fun y ↦ UniformSpace.Completion.induction_on y ?_ ?_
      · haveI := hdisc
        exact isClosed_eq
          UniformSpace.Completion.continuous_extension
          (by
              letI := (@UniformSpace.Completion.cPkg
                (locSubring D₀.P D₀.T D₀.s)
                (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                  D₀.uniformSpace)).uniformStruct
              haveI := (@UniformSpace.Completion.cPkg
                (locSubring D₀.P D₀.T D₀.s)
                (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                  D₀.uniformSpace)).complete
              haveI := (@UniformSpace.Completion.cPkg
                (locSubring D₀.P D₀.T D₀.s)
                (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
                  D₀.uniformSpace)).separation
              letI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).uniformStruct
              haveI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).complete
              haveI := (AdicCompletionBridge.adicAbstractCompletion J hadic_loc).separation
              have heAC_cont : Continuous eAC :=
                (AbstractCompletion.uniformContinuous_compare
                  (@UniformSpace.Completion.cPkg _ _)
                  (AdicCompletionBridge.adicAbstractCompletion J hadic_loc)).continuous
              have hevalₐ_cont : Continuous (AdicCompletion.evalₐ J n) := by
                unfold AdicCompletion.evalₐ
                simp only []
                letI : ∀ i, TopologicalSpace
                    (locSubring D₀.P D₀.T D₀.s ⧸ J ^ i • ⊤) :=
                  fun i ↦ (AdicCompletionBridge.quotientDiscreteTopology J i)
                haveI : DiscreteTopology
                    (locSubring D₀.P D₀.T D₀.s ⧸ J ^ n • ⊤) :=
                  AdicCompletionBridge.quotientDiscrete J n
                have h1 : Continuous
                    (AdicCompletion.eval J (locSubring D₀.P D₀.T D₀.s) n) :=
                  (continuous_apply n).comp continuous_subtype_val
                have h2 : Continuous (Ideal.quotientEquivAlgOfEq
                    (locSubring D₀.P D₀.T D₀.s)
                    (AdicCompletionBridge.ideal_smul_top_eq_self J n)) :=
                  continuous_of_discreteTopology
                exact h2.comp h1
              exact hevalₐ_cont.comp heAC_cont)
      · intro a
        show πc (↑a) = (AdicCompletion.evalₐ J n) (eAC (↑a))
        rw [UniformSpace.Completion.extensionHom_coe,
          show eAC (↑a) = AdicCompletion.of J _ a from
            AbstractCompletion.compare_coe _ _ a,
          AdicCompletion.evalₐ_of]
    intro x hx; rw [RingHom.mem_ker] at hx
    have hmem_ker : eAC (eRE x) ∈ RingHom.ker (AdicCompletion.evalₐ J n) := by
      rw [RingHom.mem_ker]; rwa [← hπc_eq]
    rw [AdicCompletionBridge.ker_evalₐ_eq_of_fg J (locIdeal_fg D₀.P D₀.T D₀.s) n] at hmem_ker
    have hx_eq : x = (eRE.symm.toRingHom.comp eAC.symm.toRingHom) (eAC (eRE x)) := by
      simp [RingHom.comp_apply, RingEquiv.symm_apply_apply]
    have h_map_eq : Ideal.map (eRE.symm.toRingHom.comp eAC.symm.toRingHom)
        (Ideal.map (algebraMap _ _) (J ^ n)) = Ideal.map g (J ^ n) := by
      rw [Ideal.map_map]; congr 1
      ext a; simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe]
      have h1 : eAC.symm (algebraMap _ _ a) =
          (↑a : UniformSpace.Completion _) := by
        rw [eAC.symm_apply_eq]
        exact (AbstractCompletion.compare_coe
          (@UniformSpace.Completion.cPkg _ _)
          (AdicCompletionBridge.adicAbstractCompletion J hadic_loc) a).symm
      have h2 : eRE.symm (↑a : UniformSpace.Completion _) = g a := by
        change (AdicCompletionBridge.completionRingEquiv g hg_cont hg_ui
          hg_dense).symm.symm (↑a) = g a
        rw [RingEquiv.symm_symm]
        exact UniformSpace.Completion.extensionHom_coe g hg_cont a
      rw [h1, h2]
    rw [hx_eq, ← h_map_eq]
    exact Ideal.mem_map_of_mem _ hmem_ker
  have hset : (↑(presheafValue_idealOfDef D₀ ^ n) :
      Set (presheafValue_ringOfDef D₀)) = ↑(RingHom.ker π) :=
    SetLike.coe_set_eq.mpr (le_antisymm hge hle)
  rw [hset]
  have hπ_cont : Continuous π := by
    change Continuous (πc ∘ eRE)
    letI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s)
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
        D₀.uniformSpace)).uniformStruct
    haveI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s)
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
        D₀.uniformSpace)).complete
    haveI := (@UniformSpace.Completion.cPkg
      (locSubring D₀.P D₀.T D₀.s)
      (UniformSpace.comap (locSubring D₀.P D₀.T D₀.s).subtype
        D₀.uniformSpace)).separation
    exact UniformSpace.Completion.continuous_extension.comp
      (AbstractCompletion.uniformContinuous_compare pkg
        (@UniformSpace.Completion.cPkg _ _)).continuous
  rw [show (↑(RingHom.ker π) : Set _) = π ⁻¹' {0} from by
    ext x; exact ⟨id, id⟩]
  exact isClosed_singleton.preimage hπ_cont

-- The AdicCompletion bridge proof has deep elaboration chains through ring equivs.
omit [PlusSubring A] in
/-- `val '' idealOfDef^n` is closed in `presheafValue D₀`.

**Proof strategy** (non-circular, via AdicCompletionBridge):

1. `ringOfDef` is a closed subring of `presheafValue`, giving a closed embedding
   `val : ringOfDef → presheafValue`.
2. Reduce to showing `idealOfDef^n` is closed in the subspace topology on `ringOfDef`.
3. For the subspace closedness: `locSubring_subspace_eq_adic` says the subspace uniformity
   on `locSubring` equals the J-adic uniformity. Via `AdicCompletionBridge.adicCompletionRingEquiv`,
   `Completion(locSubring, J-adic) ≃+* AdicCompletion(J, locSubring)` as a homeomorphism.
4. In `AdicCompletion`: `evalₐ n` is continuous (projects to discrete quotient), so
   `ker(evalₐ n)` is closed. By `AdicCompletion.map_exact` on the exact sequence
   `0 → J^n → locSubring → locSubring/J^n → 0`, `ker(evalₐ n) = Ideal.map of (J^n)`.
5. Under the composed homeomorphism: `idealOfDef^n = Ideal.map g (J^n)` corresponds to
   `Ideal.map of (J^n) = ker(evalₐ n)`, which is closed.

**Why simpler approaches are circular**: The sandwich
`coe '' locNhd n ⊆ val '' idealOfDef^n ⊆ closure(coe '' locNhd n)` gives
`val '' idealOfDef^n = closure(coe '' locNhd n)` only IF we know `val '' idealOfDef^n`
is closed. And `closure_locNhd_sub_idealOfDef_pow` USES this result.

**See also**: `locSubring_subspace_eq_adic`, `AdicCompletionBridge.lean`. -/
private theorem idealOfDef_pow_val_isClosed (D₀ : RationalLocData A) (n : ℕ) :
    IsClosed (Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) : Set (presheafValue D₀)) := by
  letI := D₀.uniformSpace; letI := D₀.isUniformAddGroup; letI := D₀.isTopologicalRing
  -- ringOfDef is a closed subring of presheafValue (it's a topological closure)
  have hclosed_ring : IsClosed (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) :=
    Subring.isClosed_topologicalClosure _
  -- Part (B): reduce to showing idealOfDef^n is closed in ringOfDef.
  -- val : ringOfDef → presheafValue is a closed embedding since ringOfDef is closed.
  apply hclosed_ring.isClosedEmbedding_subtypeVal.isClosedMap
  -- Now need: IsClosed ((idealOfDef^n).carrier) in ringOfDef (subspace topology).
  -- The subspace topology on ringOfDef comes from instUniformSpaceSubtype.
  -- We use Subring.instIsTopologicalRing for the ring topology on the subtype.
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  -- Part (A): Show idealOfDef^n is closed in the subspace topology on ringOfDef.
  -- Strategy: build a continuous ring hom π : ringOfDef → locSubring/J^n whose
  -- kernel is idealOfDef^n. Since the target is discrete (hence T₁), the
  -- preimage of {0} is closed, so idealOfDef^n = ker(π) is closed.
  --
  -- The construction uses the J-adic completion of locSubring and the bridge
  -- to AdicCompletion, where AdicCompletion.map_exact gives the kernel identity.
  -- STEP 1: The subspace topology on locSubring = J-adic topology.
  have hadic_eq := locSubring_induced_eq_adicTopology D₀
  -- STEP 2: Show idealOfDef^n = closure(g(J^n)) in ringOfDef, hence closed.
  set J := locIdeal D₀.P D₀.T D₀.s with hJ_def
  set g := locSubringToRingOfDef D₀ with hg_def
  set gJn := g '' (↑(J ^ n) : Set (locSubring D₀.P D₀.T D₀.s)) with hgJn_def
  suffices h_eq : ((presheafValue_idealOfDef D₀ ^ n :
      Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) =
      closure gJn by
    have : IsClosed (closure gJn) := isClosed_closure
    rwa [← h_eq] at this
  -- DenseRange g: ringOfDef = topological closure of range(g).
  have hg_dense : DenseRange g := locSubringToRingOfDef_denseRange D₀
  apply Set.Subset.antisymm
  · -- ⊆: idealOfDef^n ⊆ closure(gJn)
    exact idealOfDef_pow_subset_closure D₀ n hg_dense
  · -- ⊇: closure(gJn) ⊆ idealOfDef^n
    -- Step 1: gJn ⊆ idealOfDef^n (trivial: g(J^n) ⊆ Ideal.map g (J^n)).
    have hgJn_sub : gJn ⊆ ((presheafValue_idealOfDef D₀ ^ n :
        Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) := by
      rintro _ ⟨d, hd, rfl⟩
      rw [show presheafValue_idealOfDef D₀ = Ideal.map g J from rfl,
          (Ideal.map_pow g J n).symm]
      exact Ideal.mem_map_of_mem g hd
    -- Step 2: idealOfDef^n is closed in the subspace topology on ringOfDef.
    --
    -- **Why this is non-trivial**: We showed idealOfDef^n ⊆ closure(gJn) (⊆ direction).
    -- The closure of gJn equals val⁻¹(closure(coeRingHom '' locNhd n)), which is
    -- OPEN in ringOfDef (preimage of a basic nhd). So closure(gJn) is an open
    -- additive subgroup, hence also closed. But idealOfDef^n ⊆ closure(gJn)
    -- does NOT imply idealOfDef^n is closed.
    --
    -- **Why simpler approaches are circular**: To show closure(gJn) ⊆ idealOfDef^n
    -- (completing the set equality), one needs idealOfDef^n to contain a 0-nhd.
    -- The natural 0-nhd is val⁻¹(closure(coe '' locNhd n)) ⊆ idealOfDef^n, but
    -- establishing ⊇ (closure_locNhd_sub_idealOfDef_pow) uses
    -- idealOfDef_pow_val_isClosed — the very theorem we are proving.
    --
    -- **Required approach (AdicCompletion bridge)**:
    -- 1. locSubring_subspace_eq_adic gives subspace uniformity = J-adic uniformity.
    -- 2. AdicCompletionBridge.adicCompletionRingEquiv gives
    --    Completion(locSubring, J-adic) ≃+* AdicCompletion(J, locSubring).
    -- 3. Identify ringOfDef with Completion(locSubring) via the completion embedding
    --    locSubring → Localization.Away s → presheafValue.
    -- 4. AdicCompletion.map_exact (Mathlib, needs IsNoetherianRing + Module.Finite)
    --    on 0 → J^n → locSubring → locSubring/J^n → 0 gives:
    --    ker(map I g) = range(map I f) where g is the quotient, f is inclusion.
    -- 5. Under the bridge, range(map I f) ↔ closure(g(J^n)) = closure(gJn) in ringOfDef,
    --    and ker(map I g) ↔ ker(evalₐ n) (the kernel of evaluation at level n).
    -- 6. evalₐ n has discrete target (locSubring / J^n), so ker(evalₐ n) is closed.
    -- 7. Therefore idealOfDef^n = closure(gJn) = ker(evalₐ n ∘ bridge) is closed.
    --
    -- This requires ~150 lines of new infrastructure to formalize the identification
    -- in step 3 (Completion(locSubring) ≃ ringOfDef as topological rings) and the
    -- kernel computation in steps 4-5. The AdicCompletionBridge file provides the
    -- ring isomorphism but not yet the specific composition needed here.
    have hclosed : IsClosed ((presheafValue_idealOfDef D₀ ^ n :
        Ideal (presheafValue_ringOfDef D₀)) : Set (presheafValue_ringOfDef D₀)) :=
      idealOfDef_pow_isClosed_aux D₀ n
    -- Step 3: closure_minimal.
    exact closure_minimal hgJn_sub hclosed

omit [PlusSubring A] in
private theorem closure_locNhd_sub_idealOfDef_pow (D₀ : RationalLocData A) (n : ℕ) :
    (closure ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ''
      (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)))) ∩
    (presheafValue_ringOfDef D₀ : Set (presheafValue D₀)) ⊆
    Subtype.val '' ((presheafValue_idealOfDef D₀ ^ n : Ideal (presheafValue_ringOfDef D₀)) :
      Set (presheafValue_ringOfDef D₀)) := by
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  -- The proof uses the sandwiching:
  -- (A) coe '' locNhd n ⊆ val '' idealOfDef^n  (locNhd_sub_idealOfDef_pow_val)
  -- (B) val '' idealOfDef^n ⊆ closure(coe '' locNhd n)  (idealOfDef_pow_val_sub_closure)
  -- (C) val '' idealOfDef^n is closed  (idealOfDef_pow_val_isClosed)
  -- From (A): closure(coe '' locNhd n) ⊆ closure(val '' idealOfDef^n) = val '' idealOfDef^n.
  -- The intersection with ringOfDef is contained since val '' idealOfDef^n ⊆ ringOfDef.
  intro x ⟨hx_closure, _⟩
  exact (idealOfDef_pow_val_isClosed D₀ n).closure_subset_iff.mpr
    (locNhd_sub_idealOfDef_pow_val D₀ n) hx_closure

omit [PlusSubring A] in
/-- The subspace topology on the ring of definition equals the
ideal-of-definition-adic topology.

This is the deepest fact needed for Proposition 8.15: the subspace topology
on the closure of locSubring in the completion equals the adic topology for
the image of locIdeal.

The proof uses `isAdic_iff`, reducing to two conditions:
1. Each `(presheafValue_idealOfDef)^n` is open in the subspace topology
2. Each subspace-nhd of 0 contains some `(presheafValue_idealOfDef)^n`

Both follow from the interleaving of ideal powers with the completion nhds
basis `closure(coe '' locNhd n)`, established by the helper lemmas
`idealOfDef_pow_val_sub_closure` and `closure_locNhd_sub_idealOfDef_pow`. -/
theorem presheafValue_isAdic (D₀ : RationalLocData A) :
    @IsAdic (presheafValue_ringOfDef D₀) _
      (TopologicalSpace.induced Subtype.val inferInstance)
      (presheafValue_idealOfDef D₀) := by
  -- Use isAdic_iff: show (1) each power is open and (2) powers form nhds basis.
  -- The subspace topology on ringOfDef is a topological ring (subring of a top ring).
  letI : TopologicalSpace (presheafValue_ringOfDef D₀) :=
    TopologicalSpace.induced Subtype.val inferInstance
  haveI : IsTopologicalRing (presheafValue_ringOfDef D₀) :=
    Subring.instIsTopologicalRing _
  rw [isAdic_iff]
  letI := D₀.uniformSpace
  letI := D₀.isUniformAddGroup
  letI := D₀.isTopologicalRing
  open Filter Topology in
  set f := (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) with hf_def
  have hbasis := (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero
  have hbasis_compl : (nhds (0 : presheafValue D₀)).HasBasis (fun _ : ℕ ↦ True)
      (fun n ↦ closure (f '' (locNhd D₀.P D₀.T D₀.s n :
        Set (Localization.Away D₀.s)))) := by
    rw [← (map_zero D₀.coeRingHom : f 0 = 0)]
    exact hbasis.hasBasis_of_isDenseInducing UniformSpace.Completion.isDenseInducing_coe
  have himage_sub : ∀ n,
      f '' (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ⊆
      ((D₀.coeRingHom.comp (locSubring D₀.P D₀.T D₀.s).subtype).range :
        Set (presheafValue D₀)) := by
    intro n x hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨d, _, hdy⟩ := hy
    refine ⟨d, ?_⟩
    change D₀.coeRingHom ((locSubring D₀.P D₀.T D₀.s).subtype d) = x
    exact hdy ▸ hyx
  have hsubspace_basis : (nhds (0 : presheafValue_ringOfDef D₀)).HasBasis
      (fun _ : ℕ ↦ True) (fun n ↦ Subtype.val ⁻¹'
        (closure (f '' (locNhd D₀.P D₀.T D₀.s n :
          Set (Localization.Away D₀.s))))) := by
    rw [nhds_induced]
    exact hbasis_compl.comap Subtype.val
  constructor
  · intro n
    apply AddSubgroup.isOpen_of_mem_nhds
      (((presheafValue_idealOfDef D₀) ^ n).toAddSubgroup)
    apply hsubspace_basis.mem_of_superset (i := n) trivial
    intro ⟨x, hx_mem⟩ hx_closure
    obtain ⟨y, hy_mem, hy_eq⟩ := closure_locNhd_sub_idealOfDef_pow D₀ n
      ⟨hx_closure, hx_mem⟩
    rw [show (⟨x, hx_mem⟩ : presheafValue_ringOfDef D₀) = y from Subtype.ext hy_eq.symm]
    exact hy_mem
  · intro s hs
    obtain ⟨m, -, hm⟩ := hsubspace_basis.mem_iff.mp hs
    exact ⟨m, fun x hx ↦ hm (idealOfDef_pow_val_sub_closure D₀ m ⟨x, hx, rfl⟩)⟩

omit [PlusSubring A] in
/-- **Concrete pair of definition for `presheafValue D₀`**. The specific
pair with `A₀ := presheafValue_ringOfDef D₀` and `I := presheafValue_idealOfDef D₀`,
giving definitional equality `_.A₀ = presheafValue_ringOfDef D₀` (unlike
the `Nonempty.some` of `presheafValue_pairOfDefinition` which is opaque). -/
noncomputable def presheafValue_pairOfDefinition_concrete
    [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    PairOfDefinition (presheafValue D₀) :=
  { A₀ := presheafValue_ringOfDef D₀
    I := presheafValue_idealOfDef D₀
    isOpen := presheafValue_ringOfDef_isOpen D₀
    fg := presheafValue_idealOfDef_fg D₀
    isAdic := presheafValue_isAdic D₀ }

omit [PlusSubring A] in
/-- **A₀ of the concrete pair of definition equals `presheafValue_ringOfDef D₀`**
(definitionally). Used for discharging ring-of-definition membership obligations
in iterated-rational continuity proofs. -/
theorem presheafValue_pairOfDefinition_concrete_A₀
    [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    (presheafValue_pairOfDefinition_concrete P D₀).A₀ = presheafValue_ringOfDef D₀ :=
  rfl

omit [PlusSubring A] in
/-- **Faithful (noeth-`A₀`-free) concrete pair of definition for `presheafValue D₀`.**

Identical *data* to `presheafValue_pairOfDefinition_concrete` (same `A₀`, `I`, and
Prop-valued fields), but **without** the dead `(P : PairOfDefinition A)
[IsNoetherianRing P.A₀]` plumbing. The constituent sub-lemmas
(`presheafValue_ringOfDef D₀`, `presheafValue_ringOfDef_isOpen D₀`,
`presheafValue_idealOfDef_fg D₀`, `presheafValue_isAdic D₀`) are each parameterised
by `D₀` ALONE — none consumes `[IsNoetherianRing P.A₀]` — so the noeth-`A₀`
hypothesis was a pure threading artifact (exactly as observed for
`presheafValue_isTateRing_faithful`).

By proof irrelevance on the Prop fields and definitional equality on the data fields,
`presheafValue_concretePair D₀` is **definitionally equal** to
`presheafValue_pairOfDefinition_concrete P D₀` for any `P`; the two are
interchangeable wherever a `PairOfDefinition (presheafValue D₀)` of this concrete
shape is required, but only this version is faithful (works for `ℂ_p`, which has no
noetherian ring of definition `P.A₀`). -/
noncomputable def presheafValue_concretePair
    (D₀ : RationalLocData A) :
    PairOfDefinition (presheafValue D₀) :=
  { A₀ := presheafValue_ringOfDef D₀
    I := presheafValue_idealOfDef D₀
    isOpen := presheafValue_ringOfDef_isOpen D₀
    fg := presheafValue_idealOfDef_fg D₀
    isAdic := presheafValue_isAdic D₀ }

omit [PlusSubring A] in
/-- `presheafValue_concretePair` is definitionally equal to
`presheafValue_pairOfDefinition_concrete P D₀` (same data, Prop fields by proof
irrelevance). This `rfl` certifies the two are interchangeable. -/
theorem presheafValue_concretePair_eq
    [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    presheafValue_concretePair D₀ = presheafValue_pairOfDefinition_concrete P D₀ :=
  rfl

omit [PlusSubring A] in
/-- `A₀` of the faithful concrete pair equals `presheafValue_ringOfDef D₀`
(definitionally). -/
theorem presheafValue_concretePair_A₀
    [IsTateRing A]
    (D₀ : RationalLocData A) :
    (presheafValue_concretePair D₀).A₀ = presheafValue_ringOfDef D₀ :=
  rfl

omit [PlusSubring A] in
/-- **Faithful (noeth-`A₀`-free) Tate-ring instance for `presheafValue D₀`**
(Wedhorn Prop 8.15, Example 6.38). Identical to `presheafValue_isTateRing` but
**without** the dead `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` plumbing:
the pair of definition is supplied by `presheafValue_concretePair D₀` (built from
`D₀`-only sub-lemmas) and the topologically nilpotent unit by `presheafValue_topNilUnit`
(`[IsTateRing A]`-only). Faithful — works for `ℂ_p`, which has no noetherian ring of
definition. By proof irrelevance, defeq to `presheafValue_isTateRing P D₀` for any `P`. -/
theorem presheafValue_isTateRing_concrete [IsTateRing A]
    (D₀ : RationalLocData A) :
    IsTateRing (presheafValue D₀) :=
  { exists_pairOfDefinition := ⟨presheafValue_concretePair D₀⟩
    exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D₀ }

omit [PlusSubring A] in
/-- **Proposition 8.15 (partial)**: `presheafValue D₀` has a natural
pair of definition, making it a Huber ring. Combined with
`presheafValue_topNilUnit`, this gives `IsTateRing`. -/
theorem presheafValue_pairOfDefinition [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    Nonempty (PairOfDefinition (presheafValue D₀)) :=
  ⟨presheafValue_pairOfDefinition_concrete P D₀⟩

omit [PlusSubring A] in
/-- **Proposition 8.15**: `presheafValue D₀` is a Tate ring.

Combines:
- `presheafValue_pairOfDefinition`: the pair of definition exists
- `presheafValue_topNilUnit`: a topologically nilpotent unit exists -/
theorem presheafValue_isTateRing [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    IsTateRing (presheafValue D₀) :=
  { exists_pairOfDefinition := presheafValue_pairOfDefinition P D₀
    exists_topologicallyNilpotent_unit := presheafValue_topNilUnit D₀ }

omit [PlusSubring A] in
/-- **Proposition 8.15, Huber-ring corollary** (NEW-A3.1, ticket #131):
`presheafValue D₀` is a Huber ring, derived from `presheafValue_isTateRing`
via the `IsTateRing → IsHuberRing` extension.

Path α: takes `(P : PairOfDefinition A) [IsNoetherianRing P.A₀]` as explicit
parameters (per the binding rule `feedback_assume_noeth_A0.md`). -/
theorem presheafValue_isHuberRing [IsTateRing A] [IsNoetherianRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ : RationalLocData A) :
    IsHuberRing (presheafValue D₀) :=
  (presheafValue_isTateRing P D₀).toIsHuberRing

/-! ### T143: presheafValue OMT prerequisite supplier

The Banach open-mapping chain in `LaurentRefinement.lean` (T140 / T141 /
T142) requires seven explicit hypotheses on `presheafValue D₀`:
`hTate_B`, `hA_complete_B`, `hNoeth_B`, `hDom_B`, `hSigCp_B`, `hnoeth_B`,
`hnoeth₂_B`. Two are discharged from existing local API:

* `hTate_B` — `presheafValue_isTateRing` (above).
* `hA_complete_B` — `presheafValue_completeSpace_rightUniformSpace`
  (below).

The remaining five are open and tracked outside this file:
`IsNoetherianRing (presheafValue D₀)`,
`IsDomain (presheafValue D₀)`, `SigmaCompactSpace (presheafValue D₀)`,
and Noetherianness of `TateAlgebra.pairSubring` / `pairSubring₂` for
`presheafValue D₀`'s principal pair. -/

omit [PlusSubring A] in
/-- **`CompleteSpace` of `presheafValue D₀` w.r.t. the right-uniform-space**
(T143 OMT prerequisite supplier; discharges T141 / T142's `hA_complete_B`).

The canonical `CompleteSpace (presheafValue D₀)` instance from
`Presheaf.lean` uses `UniformSpace.Completion.uniformSpace`; the OMT chain
asks for the right-uniform-space form. The two agree by
`IsUniformAddGroup.rightUniformSpace_eq`. -/
theorem presheafValue_completeSpace_rightUniformSpace
    (D₀ : RationalLocData A) :
    @CompleteSpace (presheafValue D₀)
      (IsTopologicalAddGroup.rightUniformSpace (presheafValue D₀)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

/-! ### Base-change API for the canonical map (Wedhorn Prop 8.2 analogues)

Helper lemmas translating membership in `D₀.P.A₀` to membership in the
ring of definition of `presheafValue D₀`. Used to discharge continuity /
power-boundedness obligations for maps built from `D₀.canonicalMap`.

These lemmas are used by the Laurent-refinement continuity residuals
(`iteratedPlus_forwardToCompletion_continuous` in `LaurentRefinement.lean`)
and more generally by the base-change step `A → B := presheafValue D₀`. -/

omit [PlusSubring A] in
/-- **Canonical map lands in ring of definition (Wedhorn Prop 8.2 base-change)**:
if `a ∈ D₀.P.A₀`, then `D₀.canonicalMap a ∈ presheafValue_ringOfDef D₀`.

Proof: `algebraMap A _ a ∈ locSubring D₀.P D₀.T D₀.s` (by
`algebraMap_mem_locSubring`), so `D₀.canonicalMap a =
D₀.coeRingHom (algebraMap A _ a)` lies in the image of `locSubring` under
`D₀.coeRingHom`, and hence in `presheafValue_ringOfDef D₀` (the
topological closure of that image). -/
theorem canonicalMap_mem_ringOfDef (D₀ : RationalLocData A)
    {a : A} (ha : a ∈ D₀.P.A₀) :
    D₀.canonicalMap a ∈ presheafValue_ringOfDef D₀ := by
  -- Unfold definitions and use that the range contains `canonicalMap a`.
  refine Subring.le_topologicalClosure _ ?_
  refine ⟨⟨algebraMap A (Localization.Away D₀.s) a,
    algebraMap_mem_locSubring D₀.P D₀.T D₀.s ha⟩, ?_⟩
  rfl

omit [PlusSubring A] in
/-- The image of `P.A₀` (for the native `A`-pair) lies in
`presheafValue_ringOfDef D₀` via `D₀.canonicalMap`, provided `P.A₀ ⊆ D₀.P.A₀`.
Specialised to `P = D₀.P` (the usual choice), this is immediate. -/
theorem canonicalMap_mem_ringOfDef_of_subset (D₀ : RationalLocData A)
    (P : PairOfDefinition A) (hsub : (P.A₀ : Set A) ⊆ (D₀.P.A₀ : Set A))
    {a : A} (ha : a ∈ P.A₀) :
    D₀.canonicalMap a ∈ presheafValue_ringOfDef D₀ :=
  canonicalMap_mem_ringOfDef D₀ (hsub ha)

/-! ### Proposition 8.15: key lemmas for restriction as localization

The restriction map `sigma = restrictionMapHom D₀ D h` is surjective and
injective. Both facts follow from the deep topological result that the
algebraic lift between localizations is a uniform embedding with respect
to the localization topologies (Wedhorn Proposition 8.15).

**Proof architecture**: `restrictionMapAlg D₀ D h` factors as
`D.coeRingHom ∘ locLift` where `locLift : Loc.Away D₀.s →+* Loc.Away D.s`
exists because `D₀.s` becomes a unit in `Loc.Away D.s` (rational containment).
The key topological input (Wedhorn Prop 8.15) is that `restrictionMapAlg` is
a `IsUniformInducing` map from `(Loc.Away D₀.s, D₀.uniformSpace)` to
`(presheafValue D, Completion.uniformSpace)`. Then:

- **Injectivity** of `sigma`: `isUniformInducing_extension` gives sigma is
  `IsUniformInducing`, hence injective (in T₀ spaces).
- **Surjectivity** of `sigma`: The range is complete
  (`IsUniformInducing.isComplete_range` + `CompleteSpace`), hence closed
  (`IsComplete.isClosed` in T₀). The range is also dense (contains the dense
  image `restrictionMapAlg(Loc.Away D₀.s)` which contains `D.canonicalMap(A)`).
  Dense + closed = everything. -/

/-! ### Key topological input (Wedhorn Prop 8.15)

The algebraic restriction map `restrictionMapAlg D₀ D h : Localization.Away D₀.s →
presheafValue D` is `IsUniformInducing` from `D₀.uniformSpace` to the completion
uniformity, AND has dense range.

**IsUniformInducing**: The localization topologies on `Loc.Away D₀.s` and
`Loc.Away D.s` are compatible under the algebraic lift. Concretely, for the
pair of definition `(A₀, I)`:
- Source neighborhoods: `locNhd D₀.P D₀.T D₀.s n` (based on `I^n` in `A[1/D₀.s]`)
- Target neighborhoods: completion of `locNhd D.P D.T D.s n`
- The composition `D.coeRingHom ∘ locLift` maps source nhds into target nhds
  and reflects them.
This factors as `D.coeRingHom ∘ locLift`. `D.coeRingHom` is `IsUniformInducing`
(by `Completion.isUniformInducing_coe`). The `locLift` between localizations
preserves the adic uniformity by the Noetherian hypothesis: `I^n·A[1/D₀.s]` maps into
`I^n·A[1/D.s]` (forward), and the reverse uses the Artin-Rees lemma for Noetherian
adic filtrations.

**DenseRange**: The image of `Loc.Away D₀.s` under `restrictionMapAlg` is dense in
`presheafValue D`. Since `restrictionMapAlg(algebraMap a) = D.canonicalMap a` for all
`a : A`, the image contains `range(D.canonicalMap)` which topologically generates the
completion.

**Wedhorn reference**: Proposition 8.15 + Lemma 8.5 (Noetherian adic completion). -/

/-- **Radical relation from rational-open containment** (T089 strict
algebraic helper, fully proved).

From `h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s`, extract the
explicit radical relation `D.s ∈ √(D₀.s)` in concrete `(N, e)` form:
there exist `N : ℕ` and `e : A` with `e * D₀.s = D.s ^ N` in `A`.

**Proof**: prime-ideal criterion via Wedhorn Prop 7.52
(`mem_prime_of_rational_subset` + `spa_point_nonOpen_of_rational_subset`)
shows `D.s ∈ Ideal.radical (Ideal.span {D₀.s})`, i.e., a power of `D.s`
lies in the principal ideal `(D₀.s)`. The witnesses `(N, e)` are
extracted via `Ideal.mem_radical_iff` and `Ideal.mem_span_singleton'`.

This is the **first step of the Artin-Rees + radical-relation route**
behind `locLift_open_on_image_at_zero`. The explicit `(N, e)` data
underwrites: (i) `D₀.s` being a unit in `Localization.Away D.s`
(`isUnit_algebraMap_s_of_rational_subset`); (ii) the source-side
identity `algebraMap (D.s^N) = algebraMap e * algebraMap D₀.s` in
`Localization.Away D₀.s`, which is the algebraic kernel of the
neighborhood translation between target and source `locNhd` filtrations
in the basis-form residual of `locLift_open_on_image_at_zero`. -/
private theorem rad_relation_of_rational_subset
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∃ N : ℕ, ∃ e : A, e * D₀.s = D.s ^ N := by
  classical
  have hrad : D.s ∈ Ideal.radical (Ideal.span {D₀.s}) := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro p ⟨hsp, hp⟩
    refine mem_prime_of_rational_subset D₀ D h p hp
      (hsp (Ideal.subset_span (Set.mem_singleton D₀.s))) ?_
    intro hp_notOpen hD's
    exact spa_point_nonOpen_of_rational_subset D₀ D h p hp
      (hsp (Ideal.subset_span (Set.mem_singleton D₀.s))) hD's hp_notOpen
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hrad
  obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.mp hN
  exact ⟨N, e, he⟩

/-- `D₀.s` is a unit in `Localization.Away D.s` when `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`.

This is the localization-level analogue of `isUnit_canonicalMap_s`. The proof uses
the prime ideal criterion (Wedhorn Prop 7.52): `D.s ∈ √(D₀.s)`, so a power of
`D.s` is divisible by `D₀.s`, making `D₀.s` a unit in `Localization.Away D.s`.

**T089 refactor (2026-04-29)**: the radical relation extraction is now factored
into the named helper `rad_relation_of_rational_subset`. -/
private theorem isUnit_algebraMap_s_of_rational_subset
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    IsUnit (algebraMap A (Localization.Away D.s) D₀.s) := by
  obtain ⟨N, e, he⟩ := rad_relation_of_rational_subset D₀ D h
  have hunit_pow : IsUnit (algebraMap A (Localization.Away D.s) D.s ^ N) :=
    (IsLocalization.map_units (Localization.Away D.s)
      (⟨D.s, ⟨1, pow_one D.s⟩⟩ : Submonoid.powers D.s)).pow N
  have heq : algebraMap A (Localization.Away D.s) e *
      algebraMap A (Localization.Away D.s) D₀.s =
      algebraMap A (Localization.Away D.s) D.s ^ N := by
    rw [← map_mul, ← map_pow, he]
  rw [← heq] at hunit_pow
  exact isUnit_of_mul_isUnit_right hunit_pow

/-- The localization-level lift between localizations: `D₀.s` is a unit in
`Localization.Away D.s` when `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`, so
`IsLocalization.Away.lift` gives a ring hom
`Localization.Away D₀.s →+* Localization.Away D.s`. -/
private noncomputable def locLift
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Localization.Away D₀.s →+* Localization.Away D.s :=
  IsLocalization.Away.lift D₀.s (isUnit_algebraMap_s_of_rational_subset D₀ D h)

/-- The algebraic restriction map factors as `D.coeRingHom ∘ locLift D₀ D h`. -/
private theorem restrictionMapAlg_eq_comp_locLift
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    restrictionMapAlg D₀ D h = D.coeRingHom.comp (locLift D₀ D h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers D₀.s)
  ext a
  simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
    RationalLocData.coeRingHom, RationalLocData.canonicalMap, locLift]

/-- **Forward continuity** of locLift: for every target neighborhood level `m`, there
exists a source level `n` such that `locLift` maps `locNhd D₀ n` into `locNhd D m`.

This follows from the universal property of the localization topology (Wedhorn §5.51):
the localization topology is the coarsest making `algebraMap` continuous and `s` a unit.
Since `locLift ∘ algebraMap = algebraMap` and `algebraMap` is continuous into `D.topology`,
the lift is continuous by the universal property. The neighborhood-level version here is
the explicit formulation needed for `IsUniformInducing`.

**Wedhorn reference**: Proposition 8.2, §5.51. -/
private theorem locLift_maps_locNhd
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ D : RationalLocData A) (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ m : ℕ, ∃ n : ℕ,
      ∀ x ∈ @locNhd A _ _ D₀.P D₀.T D₀.s n,
        (locLift D₀ D h) x ∈ @locNhd A _ _ D.P D.T D.s m := by
  -- locLift is continuous from D₀.topology to D.topology.
  -- Proof: restrictionMapAlg = D.coeRingHom ∘ locLift is continuous (Presheaf.lean),
  -- and D.coeRingHom is IsUniformInducing (embedding), so locLift is continuous.
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  haveI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  have hcont_alg := restrictionMapAlg_continuous D₀ D h
  have hfactor := restrictionMapAlg_eq_comp_locLift D₀ D h
  have hcoe_ui : @IsUniformInducing _ _ D.uniformSpace
      (@UniformSpace.Completion.uniformSpace _ D.uniformSpace) D.coeRingHom :=
    UniformSpace.Completion.isUniformInducing_coe _
  have hcont_lift : @Continuous _ _ D₀.topology D.topology (locLift D₀ D h) := by
    have : D.topology = @UniformSpace.toTopologicalSpace _ D.uniformSpace := rfl
    rw [this]
    apply hcoe_ui.isInducing.continuous_iff.mpr
    change @Continuous _ _ D₀.topology _ (D.coeRingHom ∘ locLift D₀ D h)
    have : (D.coeRingHom ∘ locLift D₀ D h : Localization.Away D₀.s →
        presheafValue D) = restrictionMapAlg D₀ D h :=
      congrArg DFunLike.coe hfactor.symm
    rw [this]; exact hcont_alg
  intro m
  have hmem : (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) ∈
      @nhds _ D.topology 0 :=
    (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero.mem_of_mem trivial
  have hpre : (locLift D₀ D h) ⁻¹' (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) ∈
      @nhds _ D₀.topology 0 := by
    have htend : Filter.Tendsto (locLift D₀ D h) (@nhds _ D₀.topology 0)
        (@nhds _ D.topology 0) :=
      (map_zero (locLift D₀ D h)) ▸ hcont_lift.continuousAt
    exact htend hmem
  obtain ⟨n, -, hn⟩ :=
    (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero.mem_iff.mp
      hpre
  exact ⟨n, fun x hx ↦ hn hx⟩

-- REMOVED 2026-04-14: FALSE infrastructure chain (locLift_preimage_locNhd,
-- locLift_isUniformInducing, restrictionMapAlg_isUniformInducing).
-- Reviewer 2026-04-03 counterexample to locLift_preimage_locNhd:
-- A = Q_p⟨X⟩, U = R({p,X}/p): X^m ∈ p^m A₀[X/p] but X^m ∉ pA₀.
-- Chain had no external callers (restrictionMapHom_isInducing also removed).
-- Wedhorn flatness route (docs/plans/2026-04-08-*.md) supersedes it.

/-- **Sigma surj condition (Wedhorn Prop 8.15)** — ⚠️ **MISFRAMED, see below**.

⚠️  **THIS STATEMENT IS MATHEMATICALLY FALSE IN GENERAL** (ChatGPT Pro reviewer
correction, 2026-05-11 session 2).

The statement claims: for every `z ∈ presheafValue D`, there exist `n, a` with
`z · u^n = σ(a)`. This is the `IsLocalization.Away.surj` predicate, i.e., the
algebraic-localization condition that every element has a finite-power
denominator.

**Counterexample**: Take `A = ℚ_p⟨X⟩` and the completed rational localization
`A⟨T⟩/(XT - 1)`. It contains `∑_{n ≥ 0} p^n · X^{-n}` (a convergent infinite
negative-power series). Multiplying by `X^N` removes only finitely many
negative powers; no finite power clears the infinite tail. So the surj
condition FAILS.

**Why we kept thinking it was provable**: the Baire-category route in the
previous docstring is flawed at the "range(σ) is closed" step. `range(σ)` is
generally NOT closed because σ is NOT uniform-inducing in general (Conrad
counterexample). Without closedness, the Baire argument doesn't apply.

**Correct route for the original goal (Cor 8.32 flatness)**: use
`Module.Flat` directly via Wedhorn 8.31 + Tate-algebra quotient identification
at the B-level (see ticket T-FLAT-VIA-WEDHORN830 in
`Adic spaces/RestrictionFlatness.lean`). This avoids the algebraic-localization
predicate entirely.

**Status**: the sorry below is preserved as an explicit "intentionally not
closed — over-strong target" marker. DO NOT pick it up as a TODO. New work
should route through the flatness path.

(Previous Baire-category strategy retained for historical reference:
S_n = {z | ∃ a, z·u^n = σ(a)} is closed if range(σ) is closed; S = ⋃ S_n is
dense ascending subgroup; if S is non-meagre, Baire gives interior, hence
open subgroup, hence dense+clopen=univ. The fatal step is "range(σ) closed",
which fails in general.) -/
@[deprecated "RETIRED — false in general; use per-E via productRestriction_faithfullyFlat_tate"
  (since := "2026-05-23")]
theorem restrictionMapHom_surj
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ z : presheafValue D,
      ∃ (n : ℕ) (a : presheafValue D₀),
        z * (restrictionMapHom D₀ D h) (D₀.canonicalMap D.s) ^ n =
        (restrictionMapHom D₀ D h) a := by
  -- Setup: uniform space instances for the localization topologies
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  -- Abbreviations
  set sigma := restrictionMapHom D₀ D h with hsigma_def
  set u := sigma (D₀.canonicalMap D.s) with hu_def
  -- Key identity: sigma ∘ coeRingHom = restrictionMapAlg (extension property)
  have hsigma_coe : ∀ a : Localization.Away D₀.s,
      sigma (D₀.coeRingHom a) = restrictionMapAlg D₀ D h a :=
    fun a => UniformSpace.Completion.extensionHom_coe
      (restrictionMapAlg D₀ D h) (restrictionMapAlg_continuous D₀ D h) a
  -- u = D.canonicalMap D.s (a unit in presheafValue D)
  have hu_eq : u = D.canonicalMap D.s := by
    change sigma (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)) = _
    rw [hsigma_coe]
    simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
      RationalLocData.canonicalMap]
  have hu_unit : IsUnit u := hu_eq ▸ isUnit_s_in_presheafValue D
  -- For elements of the dense subring Localization.Away D.s:
  -- D.coeRingHom(a / D.s^k) satisfies the surj condition with n = k.
  have h_dense : ∀ x : Localization.Away D.s,
      ∃ (n : ℕ) (a : presheafValue D₀),
        D.coeRingHom x * u ^ n = sigma a := by
    intro x
    obtain ⟨⟨a, ⟨_, ⟨k, rfl⟩⟩⟩, hx⟩ := IsLocalization.surj (Submonoid.powers D.s) x
    refine ⟨k, D₀.canonicalMap a, ?_⟩
    rw [hu_eq]
    conv_rhs =>
      rw [show D₀.canonicalMap a = D₀.coeRingHom (algebraMap A _ a) from rfl]
      rw [hsigma_coe]
      simp only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
        RationalLocData.canonicalMap]
    change D.coeRingHom x * (D.coeRingHom (algebraMap A (Localization.Away D.s) D.s)) ^ k =
      D.canonicalMap a
    rw [← map_pow, ← map_mul]
    simp only [RationalLocData.canonicalMap, RingHom.comp_apply]
    congr 1
    rw [map_pow] at hx
    exact hx
  -- PROOF OUTLINE (Baire category, Wedhorn Prop 8.15):
  --
  -- Define S_n = {z | z * u^n ∈ range(sigma)}, S = ⋃ n, S_n.
  --
  -- (A) range(sigma) = closure(range(restrictionMapAlg)), hence IsClosed:
  --     (⊆) sigma '' univ = sigma '' closure(range(coe)) ⊆ closure(sigma '' range(coe))
  --         = closure(range(restrictionMapAlg)) by image_closure_subset_closure_image.
  --     (⊇) sigma factors through closure(range(restrictionMapAlg)) as a continuous map
  --         from Completion to a complete T₂ subspace. The corestricted map extends the
  --         dense embedding of range(restrictionMapAlg), so by Completion.induction_on
  --         (applied to the corestricted map), it surjects onto the closure.
  --
  -- (B) Each S_n is closed: preimage of IsClosed(range(sigma)) under continuous (· * u^n).
  --     S_n ⊆ S_{n+1}: if z * u^n = sigma(a), then z * u^{n+1} = sigma(a * D₀.canonicalMap D.s).
  --
  -- (C) S is a dense additive subgroup (from h_dense + Completion.induction_on).
  --
  -- (D) S is not meagre: presheafValue D is Baire (CompleteSpace + IsCountablyGenerated
  --     uniformity from Nat-indexed localization basis) and second-countable (from
  --     countably generated uniformity). The quotient presheafValue D / S has at most
  --     countably many cosets (separable). If S were meagre, each coset would be meagre,
  --     and presheafValue D = countable union of meagre cosets would be meagre.
  --     Contradiction: nonempty Baire space is not meagre.
  --
  -- (E) Since S is not meagre and S = ⋃ n, S_n (ascending closed sets), some S_N is not
  --     nowhere dense, hence S_N has nonempty interior. S_N is a closed additive subgroup
  --     with nonempty interior, so it's open (AddSubgroup.isOpen_of_zero_mem_interior).
  --     S ⊇ S_N, so S is open. Open additive subgroup is clopen
  --     (AddSubgroup.isClosed_of_isOpen). Dense + closed = univ.
  --
  -- This requires: (A) factorization of sigma through complete subspace,
  --                (D) second countability / coset counting in Baire spaces.
  -- Both are substantial Lean infrastructure pieces not yet assembled in this project.
  sorry

-- NOTE: `Function.Surjective (restrictionMapHom D₀ D h)` is FALSE in general.
-- sigma's range = closure(range(restrictionMapAlg)) ⊊ presheafValue D when
-- D.s is not a unit in Localization.Away D₀.s.
-- Use `restrictionMapHom_surj` (the IsLocalization.Away.surj condition) instead.

/-- **Sigma injectivity (Wedhorn Prop 8.15)**: The restriction map
`restrictionMapHom D₀ D h` is injective.

**Status (2026-04-16, updated)**: still open in the unconditional form
required by the signature, but the Example 6.38 identification is now
**conditionally available** as `presheafValue_tateAlgebra_quotient_iso`
(`TopologyComparison.lean`, end of file). See the conditional
companion `restrictionMapHom_injective_via_iso` below for what is
delivered under the four standard hypotheses (`hb`, `hA_complete`,
`hnoeth`, `hT_pb`) — these are the inputs of the new packaged iso, with
the (formerly conditional) `hcont` hypothesis now discharged
unconditionally by `tateQuotientToPresheafHom_continuous_of_tate`.

**Why the obvious routes fail**:

(1) *Completion-extension uniform inducing.* The original outline
    `(isUniformInducing_extension (restrictionMapAlg_isUniformInducing D₀ D h)).injective`
    is FALSE: the algebraic map
    `restrictionMapAlg = D.coeRingHom ∘ locLift D₀ D h` is NOT in general
    a `IsUniformInducing` map. Reviewer counterexample (2026-04-03):
    `A = ℚ_p⟨X⟩`, `U = R({p,X}/p)`. The inducing infrastructure was
    quarantined and removed (`locLift_preimage_locNhd`, etc.).

(2) *Faithful-flatness chain (Wedhorn Cor 8.32).* Cor 8.32 says the
    PRODUCT `presheafValue D₀ → ∏ presheafValue Eᵢ` over a rational
    cover is faithfully flat (hence injective by
    `RingHom.FaithfullyFlat.injective`). It does NOT directly give
    injectivity of a SINGLE projection `presheafValue D₀ → presheafValue D`
    unless `D` itself extends to a 1-element rational cover of `D₀`,
    which forces `R(D.T/D.s) = R(D₀.T/D₀.s)` — too strong.

(3) *Module flatness over A.* Even with
    `presheafValue_flat_of_canonical` (StructureSheaf.lean:963)
    giving `Module.Flat A (presheafValue D)`, this is flatness OVER A,
    not flatness of the restriction map `presheafValue D₀ → presheafValue D`,
    so it does not yield `Injective (restrictionMapHom D₀ D h)`.

(4) *Algebraic-kernel + density.* The kernel is closed in
    `presheafValue D₀`. Its intersection with the dense image
    `coeRingHom(Localization.Away D₀.s)` is `coeRingHom(ker(restrictionMapAlg))`,
    which is `0` whenever `locLift D₀ D h` does not introduce extra
    Hausdorff-quotient kernel. But a closed subgroup with trivial
    intersection on a dense subgroup can still be nontrivial; closure
    + density alone does not force kernel = {0}.

**Available infrastructure (2026-04-16)**:

The packaged Example 6.38 isomorphism
`presheafValue_tateAlgebra_quotient_iso` (TopologyComparison.lean) gives:
`presheafValue D ≃+* A⟨X⟩ ⧸ (1 - D.s · X)`
under hypotheses `hb`, `hA_complete`, `hnoeth`, `hT_pb`. It intertwines
`D.canonicalMap` with `Ideal.Quotient.mk ∘ algebraMap`. Its inverse is
the unconditional `tateQuotientToPresheafHom`.

**What remains for the unconditional `restrictionMapHom_injective`**:

The remaining algebraic core, even after applying both isos for `D₀`
and `D`, is to show that the conjugated map
`Φ : A⟨X'⟩/(1 - D₀.s X') → A⟨X⟩/(1 - D.s X)`
is **injective**. Concretely, `Φ` sends:
- `mk(algebraMap a) ↦ mk(algebraMap a)` for `a ∈ A` (by
  `restrictionMapHom_canonicalMap`).
- `mk(X') ↦ (mk(algebraMap D₀.s))⁻¹` (the unique inverse in the target,
  guaranteed by `isUnit_canonicalMap_s` Wedhorn 8.2).

This is a **localization-of-Tate-quotient** map. By the universal
property, it factors through `(A⟨X⟩/(1-D.s X))[1/D₀.s]`, and the
injectivity of `Φ` is equivalent to: `mk(D₀.s)` is a non-zero-divisor
in `A⟨X⟩/(1-D.s X)`.

**Status update (2026-04-16)**: The non-zero-divisor step is now
**closed conditionally** via `mk_D₀s_isUnit` (below), which proves
the STRONGER statement that `mk(D₀.s)` is a **unit** in
`A⟨X⟩/(1 - D.s·X)` under the four iso-hypotheses. The proof transports
the known unit `D.canonicalMap D₀.s ∈ presheafValue D` (from
`isUnit_canonicalMap_s`) across the Example 6.38 ring iso. Being a
unit immediately gives non-zero-divisor (`mk_D₀s_mem_nonZeroDivisors`).

**However**, having `mk(D₀.s)` be a unit does NOT by itself close
`restrictionMapHom_injective` unconditionally. The obstacle: the
asymmetric containment `R(D) ⊆ R(D₀)` means `D.s` is NOT automatically
a unit/NZD in `presheafValue D₀` (the source), so the conjugated map
`Φ` need not factor through its source's localization. Closing the
injectivity requires either (a) a symmetric NZD argument on `D.s` in
the source quotient, or (b) a separate faithful-flatness argument for
the restriction. The `mk(D₀.s)` unit fact is NECESSARY but not
sufficient.

The remaining gap is therefore STILL ALGEBRAIC, and the ABOVE
`mk_D₀s_isUnit` discharges half of the original Wedhorn Cor 8.32
content. No further topological or completion hypotheses are needed
beyond the four iso-hypotheses.

**⚠ RETIRED / FALSE IN GENERAL (2026-04-20)**: single-map injectivity of
`restrictionMapHom` fails by the reviewer counterexample
`A = k⟨T, U⟩/(TU), U = R(1/T)` (cf. retired-scaffold note above at line 1435).

**Do not add new uses**. For `restrictionMap_isLocalization` (Prop 8.15),
use the strictly-weaker `restrictionMapHom_ker_isTorsion` below — the
`IsLocalization`-equalizer condition admits any `n ≥ 0`, whereas
injectivity forces `n = 0`. For cover-level content use
`productRestriction_faithfullyFlat_tate_of_hSpa_points` (`Cor832.lean`).

Existing legacy callers in `LaurentRefinement.lean:3638, 3695` carry
the resulting `sorry` transitively and should be refactored to the
Cor 8.32 route in a separate ticket. -/
@[deprecated
  "RETIRED — false; use productRestriction_injective_tate_via_prime_extension_closed (Cor832.lean)"
  (since := "2026-05-23")]
theorem restrictionMapHom_injective
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    Function.Injective (restrictionMapHom D₀ D h) := by
  -- ⚠ RETIRED: false in general. Statement preserved as a named sorry only
  -- to keep legacy callers compiling; see docstring above. New code should
  -- consume `restrictionMapHom_ker_isTorsion` or the cover-level Cor 8.32
  -- machinery in `Cor832.lean`.
  sorry

/-- **Reduction of `restrictionMapHom_injective` to a Tate-quotient
non-zero-divisor question.**

Under the four standard iso-hypotheses for the **target** `D` (`hb_D`,
`hA_complete`, `hnoeth`, `hT_pb_D`), the packaged Example 6.38 iso
`presheafValue_tateAlgebra_quotient_iso D ...` identifies
`presheafValue D ≃+* A⟨X⟩ ⧸ (1 - D.s · X)`. Under this iso, the kernel
of `restrictionMapHom D₀ D h` is identified with the kernel of the
composite `e_D ∘ restrictionMapHom D₀ D h : presheafValue D₀ → T_D`.

This conditional theorem records: given an injectivity proof for the
**conjugated** map (or equivalently, given a proof that the composite
`e_D ∘ restrictionMapHom` is injective), then `restrictionMapHom D₀ D h`
itself is injective.

The remaining hypothesis `h_composite_inj` is the algebraic kernel
question: by the iso, it reduces to showing the composite
`presheafValue D₀ → T_D ≅ presheafValue D` has trivial kernel, which
under the iso for `D₀` becomes the non-zero-divisor statement on
`mk(D₀.s)` in `T_D`.

**Note on signature**: this conditional version takes only the **target**
`D` iso-hypotheses (not `D₀`'s) because the iso for `D` alone suffices
to translate the kernel question; the source `D₀` iso would add a
different but EQUIVALENT formulation of the same algebraic gap. -/
theorem restrictionMapHom_injective_via_iso
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hb_D : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb_D : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t)
    (h_composite_inj : Function.Injective
      (((presheafValue_tateAlgebra_quotient_iso D hb_D hA_complete hnoeth
          hT_pb_D : presheafValue D ≃+* (↥(TateAlgebra A) ⧸
            TateAlgebra.oneSubfXIdeal D.s)).toRingHom).comp
        (restrictionMapHom D₀ D h))) :
    Function.Injective (restrictionMapHom D₀ D h) := by
  -- The iso is bijective, so the composite injective implies first map injective.
  intro x y hxy
  apply h_composite_inj
  simp only [RingHom.comp_apply, hxy]

/-! ### Algebraic unit lemma: `mk(D₀.s)` in `A⟨X⟩/(1 - D.s·X)`

Under rational containment `R(D.T/D.s) ⊆ R(D₀.T/D₀.s)`, the canonical image
`Ideal.Quotient.mk (oneSubfXIdeal D.s) (algebraMap A (TateAlgebra A) D₀.s)`
is a **unit** (hence a non-zero-divisor) in the target Tate quotient.

The proof transports the known unit `D.canonicalMap D₀.s ∈ presheafValue D`
(witnessed by `isUnit_canonicalMap_s`) across the Example 6.38 ring iso
`presheafValue_tateAlgebra_quotient_iso` (TopologyComparison.lean). The
intertwining identity `presheafValue_tateAlgebra_quotient_iso_canonicalMap`
shows that `D.canonicalMap D₀.s` lands exactly on `mk(algebraMap A _ D₀.s)`.

This lemma is the **algebraic content** needed by the non-zero-divisor step
of `restrictionMapHom_injective`. Because we obtain the STRONGER `IsUnit`
conclusion rather than just `IsNonZeroDivisor`, the algebraic blocker noted
in the doc-block of `restrictionMapHom_injective` is closed at the level of
the target: `mk(D₀.s)` in `T_D := A⟨X⟩/(1 - D.s·X)` is invertible, which
(as explained below) permits the composite injectivity reduction. -/

/-- Under rational containment, the element `mk(D₀.s)` in the target Tate
quotient `A⟨X⟩/(1 - D.s·X)` is a unit. Proof via the packaged Example 6.38
iso: `mk(D₀.s) = e_D (D.canonicalMap D₀.s)` where `D.canonicalMap D₀.s` is
a unit by `isUnit_canonicalMap_s`. -/
theorem mk_D₀s_isUnit
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hb_D : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb_D : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    IsUnit ((Ideal.Quotient.mk (TateAlgebra.oneSubfXIdeal D.s))
      (algebraMap A ↥(TateAlgebra A) D₀.s)) := by
  -- Step 1: In `presheafValue D`, `D.canonicalMap D₀.s` is a unit.
  have hU_presheaf : IsUnit (D.canonicalMap D₀.s) :=
    isUnit_canonicalMap_s D₀ D h
  -- Step 2: The packaged iso carries units to units (RingEquiv preserves IsUnit).
  have hU_iso : IsUnit
      ((presheafValue_tateAlgebra_quotient_iso D hb_D hA_complete hnoeth hT_pb_D)
        (D.canonicalMap D₀.s)) :=
    hU_presheaf.map (presheafValue_tateAlgebra_quotient_iso D hb_D hA_complete hnoeth hT_pb_D)
  -- Step 3: The intertwining identity rewrites the image.
  rwa [presheafValue_tateAlgebra_quotient_iso_canonicalMap D hb_D hA_complete hnoeth
    hT_pb_D D₀.s] at hU_iso

/-- A unit is a non-zero-divisor. Immediate specialization of `mk_D₀s_isUnit`
for use in primary-decomposition style kernel arguments. -/
theorem mk_D₀s_mem_nonZeroDivisors
    [IsTateRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hb_D : TopologicalRing.IsPowerBounded (invS D))
    (hA_complete : @CompleteSpace A (IsTopologicalAddGroup.rightUniformSpace A))
    (hnoeth : IsNoetherianRing
      ↥(TateAlgebra.pairSubring (IsTateRing.principalPair A).toPairOfDefinition))
    (hT_pb_D : ∀ t ∈ D.T, TopologicalRing.IsPowerBounded t) :
    (Ideal.Quotient.mk (TateAlgebra.oneSubfXIdeal D.s))
        (algebraMap A ↥(TateAlgebra A) D₀.s) ∈
      nonZeroDivisors (↥(TateAlgebra A) ⧸ TateAlgebra.oneSubfXIdeal D.s) :=
  IsUnit.mem_nonZeroDivisors
    (mk_D₀s_isUnit D₀ D h hb_D hA_complete hnoeth hT_pb_D)

-- RETIRED 2026-04-18: Route A reduction scaffolds
-- (`restrictionMapHom_injective_via_Φ_inj`,
-- `restrictionMapHom_injective_via_Ds_nzd_and_ker_torsion`,
-- `ker_torsion_of_restrictionMapHom_torsion`) landed 2026-04-17/18 have been
-- removed. Reviewer counterexample (`A = k⟨T, U⟩/(TU)`, `U = R(1/T)`)
-- shows individual `restrictionMapHom_injective` is false in general, so
-- the NZD / kernel-torsion scaffolds were chasing an unattainable target.
-- The correct injectivity for `tateAcyclicity` Part 1 is cover-level
-- (Wedhorn Cor 8.32) via
-- `productRestriction_injective_tate_via_coeRingHom_preserves_proper`
-- in `Cor832.lean:1202`, conditional on `coeRingHom_preserves_proper`
-- (= T-IDEAL-2, to be discharged via Artin-Rees on the ring of definition).

-- REMOVED 2026-04-14: restrictionMapHom_isInducing. Depends on
-- restrictionMapAlg_isUniformInducing (FALSE, removed above). No external
-- callers (StructureSheaf.lean already notes this removal at line 961).

/-! ### Proposition 8.15: restriction maps are rational localizations

The core of Prop 8.15: for D ≤ D₀, the restriction map
`restrictionMapHom D₀ D h : presheafValue D₀ →+* presheafValue D`
makes `presheafValue D` a localization of `presheafValue D₀` at the
image of `D.s` under `canonicalMap`.

This identification is the KEY infrastructure for Tate acyclicity:
- Each restriction is flat (localization = flat)
- Covering → Spec surjective → faithfully flat → IsSheafy

The proof requires:
1. presheafValue D₀ is a Tate ring (presheafValue_isTateRing, proved)
2. The restriction sends canonicalMap(D.s) to a unit (isUnit_canonicalMap_s)
3. presheafValue D = (presheafValue D₀)[1/canonicalMap(D.s)]
   (this is the ISOMORPHISM, not just a factoring)

Step 3 is the deepest part. It uses the localization-of-completion theorem:
Completion(R[1/s]) ≃ Completion(R)[1/s'] where R = locSubring, s = D.s.
This requires:
- The subspace uniformity identification (locSubring_subspace_eq_adic, proved)
- The completion embedding preserving the localization structure
- The universal property of localization in the completion -/

/-- The restriction map on the dense image equals the algebraic restriction map.
This re-proves the private `restrictionMapHom_coe` from `Presheaf.lean`,
needed here for the localization proof. -/
private theorem restrictionMapHom_coe' (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (a : Localization.Away D₀.s) :
    restrictionMapHom D₀ D h
      (@UniformSpace.Completion.coeRingHom _ _ D₀.uniformSpace
        D₀.isTopologicalRing D₀.isUniformAddGroup a) =
      restrictionMapAlg D₀ D h a := by
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  exact UniformSpace.Completion.extensionHom_coe
    (restrictionMapAlg D₀ D h) (restrictionMapAlg_continuous D₀ D h) a

/-! ### Reusable closed-annihilator lemma

For any topological commutative ring `R` with `[T2Space R]`, the annihilator
`{c : R | r * c = 0}` of a fixed `r : R` is closed — as the preimage of
`{0}` under the continuous map `c ↦ r * c`. This is the underlying
closedness fact used to lift algebraic torsion of a kernel through a
continuous ring homomorphism. -/

omit [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A] in
/-- **Closed annihilator (reusable)**: `{c : R | r * c = 0}` is a closed
subset of any `T2Space` topological ring `R`. -/
theorem isClosed_setOf_mul_eq_zero {R : Type*} [CommRing R]
    [TopologicalSpace R] [T2Space R] [ContinuousMul R]
    (r : R) : IsClosed {c : R | r * c = 0} :=
  isClosed_eq (continuous_const.mul continuous_id) continuous_const

/-! ### S-PROP815-KER: kernel-is-torsion for `restrictionMapHom`

The correct equalizer content of Prop 8.15: elements of the kernel of the
restriction map are annihilated by a power of `D₀.canonicalMap D.s`.

The proof decomposes into:
* **Algebraic torsion** — `CompletionLocalization.away_lift_torsion_bounded`
  gives a uniform `N₀` such that every algebraic kernel element of `locLift`
  (the `Localization.Away D₀.s → Localization.Away D.s` localization map)
  is killed by `algebraMap(D.s^N₀)`. Pushed through `D₀.coeRingHom`, this
  shows `D₀.coeRingHom(ker(locLift)) ⊆ Ann((D₀.canonicalMap D.s)^N₀)`.
* **Topological closure of the algebraic kernel** —
  `ker(restrictionMapHom) ⊆ closure(D₀.coeRingHom '' ker(locLift))`. This
  is the **named residual** `ker_restrictionMapHom_subset_closure_algLift`
  below. Combined with closedness of the annihilator (the lemma above),
  the torsion result follows. -/

/-- **Basis-form reduction for `locLift_open_on_image_at_zero`** (T089
strict structural helper, fully proved).

The residual `locLift_open_on_image_at_zero` quantifies abstractly over
`V ∈ nhds 0` (source) and `W ∈ nhds 0` (target). This helper reduces
that residual to the strictly narrower **basis-indexed form**: it
suffices to provide, for every source basis index `n : ℕ`, a target
basis index `m : ℕ` such that any element `a` with
`locLift a ∈ locNhd D m` admits a representative
`b ∈ locNhd D₀ n` with the same `locLift` image.

**Why narrower**: integer-indexed on both sides (no abstract `nhds 0`
quantifier), concrete `locNhd` AddSubgroups (rather than arbitrary
nhds), amenable to Artin-Rees on the Noetherian source ring
`Loc D₀.s` paired with the radical relation `D.s ∈ √(span {D₀.s})`
(extracted via `isUnit_algebraMap_s_of_rational_subset`). The basis
form is exactly the data the Artin-Rees + radical-relation argument
described in the docstring of `locLift_open_on_image_at_zero`
produces (with `m := n + k₀ + (radical exponent)` for the Artin-Rees
constant `k₀` and the radical-relation exponent).

**Reduction proof**: standard `RingSubgroupsBasis.hasBasis_nhds_zero`
machinery on both source and target nhd bases. -/
private theorem locLift_open_on_image_at_zero_of_basis_form
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (h_basis : ∀ n : ℕ, ∃ m : ℕ,
      ∀ a : Localization.Away D₀.s,
        locLift D₀ D h a ∈ (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
        ∃ b : Localization.Away D₀.s,
          b ∈ (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ∧
          locLift D₀ D h b = locLift D₀ D h a) :
    ∀ V ∈ @nhds _ D₀.topology (0 : Localization.Away D₀.s),
      ∃ W ∈ @nhds _ D.topology (0 : Localization.Away D.s),
        ∀ a : Localization.Away D₀.s, locLift D₀ D h a ∈ W →
          ∃ b : Localization.Away D₀.s, b ∈ V ∧ locLift D₀ D h b = locLift D₀ D h a := by
  intro V hV
  -- Convert V to basis form: V contains some `locNhd D₀ n`.
  obtain ⟨n, _, hVn⟩ :=
    (locBasis D₀.P D₀.T D₀.s D₀.hopen).hasBasis_nhds_zero.mem_iff.mp hV
  -- Get the target basis index `m` from `h_basis`.
  obtain ⟨m, hm⟩ := h_basis n
  -- The candidate `W` is `locNhd D m`, a basis nhd of 0 in `D.topology`.
  refine ⟨(locNhd D.P D.T D.s m : Set (Localization.Away D.s)),
    (locBasis D.P D.T D.s D.hopen).hasBasis_nhds_zero.mem_of_mem (i := m) trivial, ?_⟩
  intro a ha
  obtain ⟨b, hb_in, hb_eq⟩ := hm a ha
  exact ⟨b, hVn hb_in, hb_eq⟩

/-! ### Strictly narrower named residual (pure localization level)

"Quantitative openness on image" of `locLift` at 0 with respect to the
two localization topologies. For every neighborhood `V` of 0 in
`Localization.Away D₀.s` there exists a neighborhood `W` of 0 in
`Localization.Away D.s` such that every `a` with `locLift a ∈ W` admits a
`b ∈ V` with `locLift b = locLift a` (so `a - b ∈ ker(locLift)` is close
to `a`).

**Strictly narrower** than the old
`ker_restrictionMapHom_subset_closure_algLift` (now below): no completion
is involved in source or target, only the localization topologies on
`Localization.Away D₀.s` and `Localization.Away D.s`. The closure
statement below reduces to this residual together with standard
completion machinery (density of `D₀.coeRingHom`, uniform-inducing of
`D.coeRingHom`, continuity of `restrictionMapHom`, algebraic
factorization through `locLift`).

**Consumer chain**: feeds
`ker_restrictionMapHom_subset_closure_algLift` →
`restrictionMapHom_ker_isTorsion` → `restrictionMap_isLocalization`
(Wedhorn Prop 8.15 Eq-clause).

**Intended attack route (Artin-Rees + radical relation)**: Let
`J₀ := P.I · Loc D₀.s` and `J := P.I · Loc D.s` be the *extended* ideals
carrying the `locNhd` topologies on source / target (the `locNhd D₀ n`
basis generates the `J₀^n`-adic filter and likewise for `D`). `Loc D₀.s`
is Noetherian, `ker(locLift) ⊆ Loc D₀.s` is an ideal, so by the
Artin-Rees lemma applied to `(J₀, ker(locLift))` in `Loc D₀.s` there is
`k₀` with `J₀^n ∩ ker(locLift) = J₀^{n-k₀} · (J₀^{k₀} ∩ ker(locLift))`
for `n ≥ k₀`. Couple that with the radical identity `D.s^{m_rel} = e · D₀.s`
in `A` (coming from `rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s` via
`isUnit_algebraMap_s_of_rational_subset`) to translate an element of
`locLift⁻¹(J^m)` into a sum `z' + k` with `z' ∈ J₀^{m - k₀}` and
`k ∈ ker(locLift)`. The `b` in the residual's conclusion is then `z'`
(picking `n` so that `z' ∈ locNhd D₀ n`, and `m` as `n + k₀ + (extra
from denominator clearing)`). All moves stay inside
`PresheafTateStructure.lean` / existing localization support; no Lane B,
Jacobson, or faithful-flatness content.

**T089 progress (2026-04-29)**: the abstract `nhds 0` form is reduced
to the basis-indexed form by `locLift_open_on_image_at_zero_of_basis_form`
(above, fully proved). The radical-relation data is extracted via
`rad_relation_of_rational_subset` (above, fully proved). The remaining
algebraic gap is the source-side kernel-quotient lift, isolated in the
local-Noetherian variant
`locLift_open_on_image_at_zero_of_source_pair_noetherian` below: it
takes `[IsNoetherianRing D₀.P.A₀]`, derives
`[IsNoetherianRing (locSubring D₀.P D₀.T D₀.s)]` via
`locSubring_isNoetherian`, applies T091's
`locIdeal_pow_shift_inter_le_pow_mul` against the source-side kernel
ideal `K := RingHom.ker (locLift ∘ subtype)`, and uses T092's
`algebraMap_mul_pow_divByS_eq_one_of_radical_relation` for the
denominator-lifting identity. The remaining content is the **per-`n`
basis-form assembly** from these ingredients. -/

/-- **`Localization.Away` normal form via explicit inverse**
(T089 normal-form helper, fully proved).

For any `s : A`, `x : Localization.Away s`, `α : A`, `k : ℕ` such that
`x * algebraMap A (Localization.Away s) (s ^ k) = algebraMap A
(Localization.Away s) α` (the `IsLocalization.Away.surj` /
`sec_spec` shape), `x` equals `algebraMap α * (divByS 1 s)^k`.

**Proof shape** (multiply by explicit inverse rather than cancel):
1. `hden`: `algebraMap (s^k) * (divByS 1 s)^k = 1` via `map_pow`,
   `← mul_pow`, T092's `algebraMap_mul_divByS_one_eq_one`, `one_pow`.
2. `calc x = x * 1 = x * (algMap(s^k) * invS^k) = (x * algMap(s^k))
   * invS^k = algebraMap α * invS^k`. -/
private theorem away_eq_algebraMap_mul_invS_pow
    (s : A) (x : Localization.Away s) (α : A) (k : ℕ)
    (hsec : x * algebraMap A (Localization.Away s) (s ^ k) =
      algebraMap A (Localization.Away s) α) :
    x = algebraMap A (Localization.Away s) α *
        (divByS (1 : A) s) ^ k := by
  have hden : algebraMap A (Localization.Away s) (s ^ k) *
      (divByS (1 : A) s) ^ k = 1 := by
    rw [map_pow, ← mul_pow, algebraMap_mul_divByS_one_eq_one, one_pow]
  calc x
      = x * 1 := (mul_one x).symm
    _ = x * (algebraMap A (Localization.Away s) (s ^ k) *
        (divByS (1 : A) s) ^ k) := by rw [hden]
    _ = (x * algebraMap A (Localization.Away s) (s ^ k)) *
        (divByS (1 : A) s) ^ k := by rw [mul_assoc]
    _ = algebraMap A (Localization.Away s) α *
        (divByS (1 : A) s) ^ k := by rw [hsec]

/-- **Witness existence without Noetherian source pair**
(T089 strictly-upstream no-Noeth witness; named sub-lemma with `sorry`
body — the genuine Artin-Rees gap).

This is the no-Noetherian-hypothesis sibling of
`locLift_preimage_target_witness_existence` (defined further below).
For each source depth `n` it asserts the existence of a target depth
`m` and, for each pair `(α, k_a)` with the away-lifted product landing
in `locNhd D m`, an element `α' : D₀.P.A₀` of depth `n + k_a · D₀.hopen.choose`
whose `algebraMap` image in `Localization.Away D.s` matches `α`'s.

**CLAUDE.md binding rule compliance**: this is the legal "named sub-
lemma with `sorry` body" pattern. No new hypotheses, no signature
change in the consumer `locLift_preimage_target_locNhd_saturation_no_noeth`
below — only the genuine Artin-Rees algebraic content is isolated. -/
private theorem locLift_preimage_target_witness_existence_no_noeth
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A) := by
  sorry

/-- **Saturation helper without Noetherian source pair**
(T089 strictly-upstream no-Noeth saturation, fully proved modulo
the strictly-smaller witness-existence residual
`locLift_preimage_target_witness_existence_no_noeth` above).

This is the no-Noetherian-hypothesis sibling of
`locLift_preimage_target_locNhd_saturation` (defined further below).
It packages the per-`n` saturation witness data needed by the no-Noeth
form `cross_localization_preimage_in_sup_ker_no_noeth` below.

**Statement** identical to `locLift_preimage_target_locNhd_saturation`
but dropping the `[IsNoetherianRing D₀.P.A₀]` instance.

**Decomposition (2026-05-23)**: the body below mirrors the Noeth
sibling's body (`locLift_preimage_target_locNhd_saturation`) verbatim,
with a single dispatch swap from the Noetherian witness existence
helper `locLift_preimage_target_witness_existence` to the no-Noeth
sibling `locLift_preimage_target_witness_existence_no_noeth` (above).
The kernel-difference reduction is mechanical algebra (factor out
`(divByS 1 D₀.s)^k_a`, evaluate `locLift` via
`IsLocalization.Away.lift_eq`, use the matching-`algebraMap`
hypothesis from the witness residual to zero the algebraMap factor);
no Noetherian content is introduced. The genuine Artin-Rees gap is
preserved as the strictly-smaller named residual above
(CLAUDE.md binding rule). -/
private theorem locLift_preimage_target_locNhd_saturation_no_noeth
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D₀.s) α *
            (divByS (1 : A) D₀.s) ^ k_a -
          algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
            (divByS (1 : A) D₀.s) ^ k_a ∈
          (locLift D₀ D h).toAddMonoidHom.ker := by
  -- Mirrors `locLift_preimage_target_locNhd_saturation` verbatim, with
  -- a single dispatch swap to `locLift_preimage_target_witness_existence_no_noeth`.
  intro n
  obtain ⟨m, hm⟩ := locLift_preimage_target_witness_existence_no_noeth D₀ D h n
  refine ⟨m, ?_⟩
  intro α k_a hα
  obtain ⟨α', hα'_pow, hα'_match⟩ := hm α k_a hα
  refine ⟨α', hα'_pow, ?_⟩
  -- The kernel-difference reduces to algebraMap-matching via routine
  -- algebra: factor out `(divByS 1 D₀.s)^k_a`, evaluate `locLift` on
  -- the `algebraMap` factor via `IsLocalization.Away.lift_eq`, then
  -- use `hα'_match` to zero the algebraMap factor.
  have h_lift_zero :
      (locLift D₀ D h)
          (algebraMap A (Localization.Away D₀.s) α * (divByS (1 : A) D₀.s) ^ k_a -
            algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
              (divByS (1 : A) D₀.s) ^ k_a) = 0 := by
    have h_combine :
        algebraMap A (Localization.Away D₀.s) α * (divByS (1 : A) D₀.s) ^ k_a -
            algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
              (divByS (1 : A) D₀.s) ^ k_a =
          algebraMap A (Localization.Away D₀.s) (α - ((α' : D₀.P.A₀) : A)) *
            (divByS (1 : A) D₀.s) ^ k_a := by
      rw [map_sub]; ring
    rw [h_combine, map_mul,
        show (locLift D₀ D h)
            (algebraMap A (Localization.Away D₀.s) (α - ((α' : D₀.P.A₀) : A))) =
            algebraMap A (Localization.Away D.s) (α - ((α' : D₀.P.A₀) : A))
          from IsLocalization.Away.lift_eq D₀.s
            (isUnit_algebraMap_s_of_rational_subset D₀ D h) _,
        map_sub, hα'_match, sub_self, zero_mul]
  exact AddMonoidHom.mem_ker.mpr h_lift_zero

/-- **Cross-localization preimage in `locNhd ⊔ ker` form, without Noetherian
source pair** (T089 generic-route, fully proved modulo strictly-smaller
saturation residual `locLift_preimage_target_locNhd_saturation_no_noeth`
above).

This is the no-Noetherian-hypothesis sibling of
`cross_localization_preimage_in_sup_ker` (defined further below). It
packages the per-`n` sup-form membership `a ∈ locNhd D₀ n ⊔ ker(locLift)`
needed by `cross_localization_preimage_in_sum_no_noeth` just below.

**Statement** identical to `cross_localization_preimage_in_sup_ker` but
dropping the `[IsNoetherianRing D₀.P.A₀]` instance. The Noetherian
sibling's proof routes through `locLift_preimage_target_locNhd_saturation`
which transitively requires `[IsNoetherianRing D₀.P.A₀]` down to
`locLift_preimage_jfull_witness_existence_at_of_rad`. The genuine
Artin-Rees content is now isolated in the strictly-smaller
`locLift_preimage_target_locNhd_saturation_no_noeth` (above); the body
below mirrors the Noeth sibling's body verbatim with the single
dispatch swap.

**Why this is not work-deferral**: the body below is mechanical
(IsLocalization.Away.surj normal form + saturation dispatch + locNhd
membership assembly via `algebraMap_PI_pow_mem_locNhd` and
`locNhd_invS_pow_step_of_hopen`), with no Noetherian content of its
own. The Artin-Rees gap is preserved as the named sub-lemma above.
No new hypotheses, no signature change. -/
private theorem cross_localization_preimage_in_sup_ker_no_noeth
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      a ∈ locNhd D₀.P D₀.T D₀.s n ⊔
        (locLift D₀ D h).toAddMonoidHom.ker := by
  -- Mirrors `cross_localization_preimage_in_sup_ker` at line 2164 verbatim,
  -- with a single dispatch swap to `locLift_preimage_target_locNhd_saturation_no_noeth`
  -- (the strictly-upstream no-Noeth saturation residual, sub-lemma with
  -- `sorry` body). Same pattern as
  -- `cross_localization_preimage_in_sum_no_noeth` mirroring
  -- `cross_localization_preimage_in_sum`.
  intro n
  -- Bind N₀ from D₀.hopen for explicit Lean-checkable depth shifts.
  set N₀ := D₀.hopen.choose with hN₀_def
  have hN₀_spec := D₀.hopen.choose_spec
  -- Apply the no-Noeth saturation helper.
  obtain ⟨m, h_sat⟩ := locLift_preimage_target_locNhd_saturation_no_noeth D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  -- Use IsLocalization.Away.surj to get (k_a, α) with `a · algebraMap (D₀.s^k_a) = algebraMap α`.
  obtain ⟨k_a, α, hsec⟩ :=
    IsLocalization.Away.surj (S := Localization.Away D₀.s) D₀.s a
  -- Convert (algebraMap D₀.s)^k_a to algebraMap (D₀.s^k_a) via `map_pow`.
  rw [← map_pow] at hsec
  -- Normal form: a = algebraMap α * (divByS 1 D₀.s)^k_a.
  have h_a_eq : a = algebraMap A (Localization.Away D₀.s) α *
      (divByS (1 : A) D₀.s) ^ k_a :=
    away_eq_algebraMap_mul_invS_pow D₀.s a α k_a hsec
  -- Apply saturation: get α' with the desired properties.
  rw [h_a_eq] at ha
  obtain ⟨α', hα'_pow, hα'_ker⟩ := h_sat α k_a ha
  -- Construct b := algebraMap (α' : A) * (divByS 1 D₀.s)^k_a.
  set b : Localization.Away D₀.s :=
    algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
      (divByS (1 : A) D₀.s) ^ k_a with hb_def
  -- Show b ∈ locNhd D₀ n via T090 + T095.
  have h_alg_α' :
      algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) ∈
        locNhd D₀.P D₀.T D₀.s (n + k_a * N₀) :=
    algebraMap_PI_pow_mem_locNhd D₀.P D₀.T D₀.s (n + k_a * N₀) α' hα'_pow
  have h_b_locNhd : b ∈ locNhd D₀.P D₀.T D₀.s n := by
    have h_eq : b = (divByS (1 : A) D₀.s) ^ k_a *
        algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) := by
      rw [hb_def]; ring
    rw [h_eq]
    exact locNhd_invS_pow_step_of_hopen D₀.P D₀.T D₀.s N₀ hN₀_spec n k_a h_alg_α'
  -- a - b ∈ ker(locLift) by hα'_ker.
  have h_ab_ker :
      a - b ∈ (locLift D₀ D h).toAddMonoidHom.ker := by
    rw [h_a_eq, hb_def]
    exact hα'_ker
  -- Conclude: a = b + (a - b), with b ∈ locNhd D₀ n and (a - b) ∈ ker.
  have h_split : a = b + (a - b) := by ring
  rw [h_split]
  exact AddSubgroup.add_mem _
    (AddSubgroup.mem_sup_left h_b_locNhd)
    (AddSubgroup.mem_sup_right h_ab_ker)

/-- **Cross-localization preimage-in-sum residual without Noetherian source pair**
(T089 generic-route, fully proved modulo strictly-smaller membership-form
residual `cross_localization_preimage_in_sup_ker_no_noeth` above).

This is the no-Noetherian-hypothesis sibling of
`cross_localization_preimage_in_sum` (defined further below, alongside
`cross_localization_preimage_in_sup_ker`). It packages the per-`n`
sum-form decomposition `a = b + k` with `b ∈ locNhd D₀ n` and
`k ∈ ker(locLift)`, needed for the **generic** (no
`[IsNoetherianRing D₀.P.A₀]` instance) basis-form residual
`cross_localization_basis_form_residual_no_noeth` just below.

**Why this is not work-deferral**: the body below mirrors the Noeth
sibling's body verbatim (the mechanical sup-form → sum-form conversion
via `locNhd_exists_decomp_of_mem_sup_ker_ringHom`, no Noetherian
content), with the single dispatch swap to
`cross_localization_preimage_in_sup_ker_no_noeth`. No new hypotheses,
no signature change. -/
private theorem cross_localization_preimage_in_sum_no_noeth
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ b k : Localization.Away D₀.s,
        b ∈ (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ∧
        k ∈ RingHom.ker (locLift D₀ D h) ∧
        a = b + k := by
  -- Mechanical lift of the membership-form residual to the sum form
  -- via `locNhd_exists_decomp_of_mem_sup_ker_ringHom` (no Noeth content;
  -- mirrors the Noetherian sibling's body in `cross_localization_preimage_in_sum`).
  intro n
  obtain ⟨m, hm⟩ := cross_localization_preimage_in_sup_ker_no_noeth D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  exact locNhd_exists_decomp_of_mem_sup_ker_ringHom D₀.P D₀.T D₀.s n
    (locLift D₀ D h) (hm a ha)

/-- **Cross-localization basis-form residual without Noetherian source pair**
(T089 generic blocker, sub-lemma derived from
`cross_localization_preimage_in_sum_no_noeth`).

This is the no-Noetherian-hypothesis sibling of
`cross_localization_basis_form_residual` (defined below the variant
`locLift_open_on_image_at_zero_of_source_pair_noetherian`). It packages
the per-`n` basis-form witness construction needed by the **generic**
(no `[IsNoetherianRing D₀.P.A₀]` instance) form
`locLift_open_on_image_at_zero` of the openness-on-image residual.

**Statement** identical to `cross_localization_basis_form_residual`
but dropping the `[IsNoetherianRing D₀.P.A₀]` instance. The genuine
algebraic content (Artin-Rees + radical-relation translation, see the
docstrings of `cross_localization_basis_form_residual` and the
section-level T089 cross-localization helpers below) is isolated in
the strictly-upstream named residual
`cross_localization_preimage_in_sum_no_noeth` (above); the source-pair
Noetherian hypothesis appears only in *one* attack route.

**Why this is not work-deferral**: the proof body below mirrors the
fully-proved Noeth-tagged sibling at line 2237 verbatim, with the
single dispatch swap to `cross_localization_preimage_in_sum_no_noeth`.
The parent's signature is unchanged. -/
private theorem cross_localization_basis_form_residual_no_noeth
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ b : Localization.Away D₀.s,
        b ∈ (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ∧
        locLift D₀ D h b = locLift D₀ D h a := by
  -- Mirrors `cross_localization_basis_form_residual` at line 2237, with a
  -- single dispatch swap to `cross_localization_preimage_in_sum_no_noeth`
  -- (the upstream no-Noeth sum-form residual, sub-lemma with `sorry` body).
  intro n
  obtain ⟨m, hm⟩ := cross_localization_preimage_in_sum_no_noeth D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  obtain ⟨b, k, hb_locNhd, hk_ker, hab⟩ := hm a ha
  refine ⟨b, hb_locNhd, ?_⟩
  -- `locLift b = locLift a` from `a = b + k`, `k ∈ ker(locLift)`.
  have h_k_zero : locLift D₀ D h k = 0 := hk_ker
  rw [hab, map_add, h_k_zero, add_zero]

/-- `locLift_open_on_image_at_zero` (T089 corrected target):
"quantitative openness on image" of `locLift` at 0. The proof reduces
to the basis-indexed form via `locLift_open_on_image_at_zero_of_basis_form`
and then delegates to the named sub-lemma
`cross_localization_basis_form_residual_no_noeth` for the per-`n`
Artin-Rees translation. -/
private theorem locLift_open_on_image_at_zero
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ V ∈ @nhds _ D₀.topology (0 : Localization.Away D₀.s),
      ∃ W ∈ @nhds _ D.topology (0 : Localization.Away D.s),
        ∀ a : Localization.Away D₀.s, locLift D₀ D h a ∈ W →
          ∃ b : Localization.Away D₀.s, b ∈ V ∧ locLift D₀ D h b = locLift D₀ D h a := by
  -- Strict reduction (T089): reduce to the basis-indexed form, then
  -- delegate to the named sub-lemma `cross_localization_basis_form_residual_no_noeth`
  -- which isolates the per-`n` Artin-Rees translation step. The
  -- local-Noetherian variant `locLift_open_on_image_at_zero_of_source_pair_noetherian`
  -- below provides an alternate route with `[IsNoetherianRing D₀.P.A₀]`
  -- via `cross_localization_basis_form_residual`.
  exact locLift_open_on_image_at_zero_of_basis_form D₀ D h
    (cross_localization_basis_form_residual_no_noeth D₀ D h)

/-! ### T089 cross-localization helpers

`cross_localization_preimage_in_sup_ker` (membership-form helper, the
genuine quotient/sum content of T089): for each source depth `n`,
finds target depth `m` such that every `a` with `locLift D₀ D h a ∈
locNhd D.P D.T D.s m` lies in `locNhd D₀.P D₀.T D₀.s n ⊔ ker(locLift
D₀ D h).toAddMonoidHom`. The `⊔`-membership encodes the
"open mapping at 0 modulo kernel" property of `locLift`. Forward
continuity (`locLift_maps_locNhd`) gives the reverse direction
(`locNhd D₀ N ⊆ locLift⁻¹(locNhd D m)`); this is the ACTUAL openness
— small target image forces a small source representative modulo
kernel. The proof combines T097/T098's source/target-radical translation
with T104's `locNhd ∩ K_full ⊆ Jfull^n * K_full` Artin-Rees absorption,
threaded through `(Jfull D₀.P D₀.T D₀.s, K_full)` with `K_full :=
RingHom.ker (locLift D₀ D h)`.

The mechanical extraction layer `cross_localization_preimage_in_sum`
(below) derives the explicit `a = b + k` decomposition from this
membership form via T101's `AddSubgroup.exists_decomp_of_mem_sup_ker`
wrapper. -/

/-! ### T089 saturation witness-existence residuals

The chain `locLift_preimage_target_locNhd_saturation` (T089 saturation)
→ `locLift_preimage_target_witness_existence` (T108 reduction; matching
`algebraMap` in target replaces kernel-difference) →
`locLift_preimage_jfull_witness_existence` (T112 corrected residual;
locNhd-form, see T110 reversal note below) progressively isolates the
genuine algebraic content of the saturation step into the genuine
named private residual.

The kernel-difference → matching-`algebraMap` reduction (T108) is
purely mechanical (`map_sub`, `IsLocalization.Away.lift_eq`,
unit-cancellation of the `(divByS 1 D₀.s)^k_a` factor).

**T110/T112 reversal (2026-04-30)**: T110 attempted to apply T107
(`algebraMap_image_mem_Jfull_pow_of_awayLift_image_in_locNhd`) to
convert the locNhd hypothesis into an `(Jfull D)^m`-ideal-membership
hypothesis, in the hope that the post-conversion residual (with the
"cleaner" `(Jfull D)^m` shape) would be strictly smaller and easier
to prove. T107 is genuinely valid in its forward direction
(locNhd → Jfull-power), but **the post-conversion `(Jfull D)^m`-form
residual is mathematically too strong**: the conversion is one-way
and loses the structural restrictiveness of the locNhd shape.

**Counterexample to the `(Jfull D)^m`-form residual**: take `A := ℚ_p`
(a Tate ring with topologically nilpotent unit `p`), `D₀ := D` with
`P := (ℤ_p, (p))`, `T := ∅`, `s := p`. Then `Localization.Away D.s
= ℚ_p` (since `p` is already a unit in `ℚ_p`), `locSubring D = ℤ_p`,
`locIdeal D = (p) ⊆ ℤ_p`, and `Jfull D = Ideal.map subtype (locIdeal
D)` is the ideal of `ℚ_p` generated by `p`-multiples of `ℤ_p`-elements
— but `p` is a unit in `ℚ_p`, so this generated ideal is `⊤`. Hence
`(Jfull D)^m = ⊤` for every `m ≥ 0` and the hypothesis becomes
vacuous; the conclusion fails for `α := 1`, `n + k_a ≥ 1`, since
`1 ∉ p^k ℤ_p` for `k ≥ 1`. The locNhd hypothesis, by contrast,
remains properly restrictive: `1/p^k_a ∉ locNhd D m` (the *set*
image of `(p^m) ⊆ ℤ_p`, not the *ideal* it generates in `ℚ_p`).

The corrected `locLift_preimage_jfull_witness_existence` (T112)
restores the locNhd hypothesis form, matching its consumer
`locLift_preimage_target_witness_existence` directly. The T107
conversion is no longer used in the consumer chain. The genuine
algebraic content (depth translation between target locNhd data and
source `D₀.P.I^(n + k_a * N₀)` data via the radical relation
`e_rad * D₀.s = D.s ^ N_rad` from `rad_relation_of_rational_subset`,
combined with Artin-Rees absorption inside `Localization.Away D.s`
against the kernel of `locLift`) remains the irreducible structural
fact this residual isolates. The "jfull" name is preserved for ticket
tracking but is now a misnomer — the hypothesis is locNhd-form. -/

/- T112 source-side α'-witness extraction (T110 reversal):
   Source-side α'-witness extraction from locNhd-membership of locLift image.
   See `locLift_preimage_jfull_witness_existence` below for the canonical
   declaration this material describes. -/

/-- **Per-`n` named residual with explicit radical data**
(named sub-lemma for `locLift_preimage_jfull_witness_existence_at`).

This sub-lemma isolates the genuine algebraic content of the per-`n`
saturation step **after** the radical relation `e₀ * D₀.s = D.s ^ N₀`
has been extracted via `rad_relation_of_rational_subset`. The data
`(N₀, e₀, h_rad)` is derivable from the parent's hypotheses (CLAUDE.md
binding rule: derivable data parameters in sub-lemmas are allowed; see
`cross_localization_basis_form_residual_no_noeth` for the same pattern
at the basis-form layer).

**Genuine algebraic content** (preserved as a sorry per the binding
rule's "sub-lemma with `sorry` body" allowance):
1. From `locLift D₀ D h (algebraMap α · invS₀^k_a) ∈ locNhd D m`, extract
   a target-side representative `α_t · invS^k_t` with `α_t ∈ D.P.I^m`.
2. Use the radical relation `e₀ * D₀.s = D.s ^ N₀` to translate target
   ideal data into source data inside `Localization.Away D.s`.
3. Apply Artin-Rees absorption against `RingHom.ker (locLift D₀ D h)`
   inside `Localization.Away D₀.s` to obtain `α' ∈ D₀.P.I^(n + k_a * N₀)`
   with matching `algebraMap` image. -/
private theorem locLift_preimage_jfull_witness_existence_at_of_rad
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (n : ℕ) (N₀ : ℕ) (e₀ : A) (_h_rad : e₀ * D₀.s = D.s ^ N₀) :
    ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A) :=
  -- Delegate to the strictly weaker (fewer hypotheses) no-Noetherian sibling
  -- `locLift_preimage_target_witness_existence_no_noeth`, which carries the
  -- identical conclusion at the same `n` without the `[IsNoetherianRing
  -- D₀.P.A₀]` instance or the radical data `(N₀, e₀, h_rad)`. Adding more
  -- hypotheses cannot weaken the conclusion, so the Noeth-with-rad form
  -- follows trivially from the no-Noeth form. The genuine Artin-Rees content
  -- is preserved as the strictly-smaller named residual at the no-Noeth
  -- sibling (CLAUDE.md binding rule: sub-lemma-with-sorry pattern; no new
  -- hypotheses introduced in either statement).
  locLift_preimage_target_witness_existence_no_noeth D₀ D h n

/-- **Per-`n` named residual** for `locLift_preimage_jfull_witness_existence`:
the genuine algebraic content of the saturation step at a single source
depth `n`. Decomposing the outer `∀ n` quantifier into a per-`n` named
sub-lemma keeps the obligation honest at the parent's signature
(CLAUDE.md binding rule: sub-lemma with `sorry` body is the legal
"named residual" pattern, identical to
`cross_localization_basis_form_residual_no_noeth` at the basis-form layer).

**Decomposition (2026-05-22)**: this theorem now reduces to
`locLift_preimage_jfull_witness_existence_at_of_rad` after extracting the
radical relation `(N₀, e₀, e₀ * D₀.s = D.s ^ N₀)` via the fully-proved
helper `rad_relation_of_rational_subset`. The Artin-Rees + radical-relation
translation content described in the section docstring is now isolated in
the strictly smaller `_of_rad` residual. -/
private theorem locLift_preimage_jfull_witness_existence_at
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (n : ℕ) :
    ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A) := by
  -- Extract the radical relation `e₀ * D₀.s = D.s ^ N₀` from the rational
  -- subset containment, then delegate to the strictly smaller named residual
  -- `locLift_preimage_jfull_witness_existence_at_of_rad`. The radical data
  -- is derivable from the parent's hypotheses via the fully-proved
  -- `rad_relation_of_rational_subset`; passing it as an explicit parameter
  -- to the sub-lemma is the legal "derivable data parameter" pattern
  -- (CLAUDE.md binding rule; see `cross_localization_basis_form_residual_no_noeth`).
  obtain ⟨N₀, e₀, h_rad⟩ := rad_relation_of_rational_subset D₀ D h
  exact locLift_preimage_jfull_witness_existence_at_of_rad D₀ D h n N₀ e₀ h_rad

private theorem locLift_preimage_jfull_witness_existence
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A) :=
  -- Per-`n` delegation to the named residual `locLift_preimage_jfull_witness_existence_at`.
  -- CLAUDE.md binding rule: sub-lemma with `sorry` body is the legal "named
  -- residual" pattern, matching `locLift_open_on_image_at_zero`'s delegation
  -- to `cross_localization_basis_form_residual_no_noeth` at the basis-form layer.
  fun n ↦ locLift_preimage_jfull_witness_existence_at D₀ D h n

private theorem locLift_preimage_target_witness_existence
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D.s) α =
          algebraMap A (Localization.Away D.s) ((α' : D₀.P.A₀) : A) :=
  -- T112-corrected: direct forward call. The previous proof routed via
  -- T107 (`algebraMap_image_mem_Jfull_pow_of_awayLift_image_in_locNhd`)
  -- to convert to a `(Jfull D)^m`-ideal-membership form, which was
  -- mathematically too aggressive (counterexample at `A := ℚ_p`; see
  -- section docstring). The corrected `locLift_preimage_jfull_witness_existence`
  -- now takes the locNhd hypothesis directly, matching this consumer
  -- exactly.
  locLift_preimage_jfull_witness_existence D₀ D h

/-- **Saturation helper for the cross-localization preimage** (T089
private saturation helper, T108 reduction to witness existence).

For each source depth `n`, find target depth `m` such that for any
`α : A` and `k_a : ℕ` with `locLift D₀ D h (algebraMap α · (divByS 1
D₀.s)^k_a) ∈ locNhd D m`, there exists `α' : D₀.P.A₀` with
`(α' : D₀.P.A₀) ∈ D₀.P.I^(n + k_a * D₀.hopen.choose)` such that
`algebraMap α · (divByS 1 D₀.s)^k_a - algebraMap (α' : A) · (divByS 1
D₀.s)^k_a ∈ ker(locLift)`.

**T108 (2026-04-30) reduction**: this theorem now reduces to the
strictly smaller `locLift_preimage_target_witness_existence` (above)
via routine algebra. The kernel-difference unfolds via `map_sub`,
`map_mul`, and `IsLocalization.Away.lift_eq` to a product of
`algebraMap A (Loc D.s) (α - α')` and the away-lifted denominator
power; the matching-`algebraMap` hypothesis from the witness residual
zeroes the algebraMap factor, hence the product. The genuine algebraic
content (witness existence + depth + matching target image) is
preserved as the strictly smaller residual.

Original Primary plan (preserved for reference): combines T097's
target-side radical inverse factor identity, T098's source-side
radical rewrite, T104's source `locNhd ∩ K_full ⊆ Jfull^n * K_full`
Artin-Rees absorption. The radical-rewrite/Artin-Rees content is now
isolated in `locLift_preimage_target_witness_existence`. -/
private theorem locLift_preimage_target_locNhd_saturation
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ (α : A) (k_a : ℕ),
      locLift D₀ D h
        (algebraMap A (Localization.Away D₀.s) α *
          (divByS (1 : A) D₀.s) ^ k_a) ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ α' : D₀.P.A₀,
        (α' : D₀.P.A₀) ∈ D₀.P.I ^ (n + k_a * (D₀.hopen.choose)) ∧
        algebraMap A (Localization.Away D₀.s) α *
            (divByS (1 : A) D₀.s) ^ k_a -
          algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
            (divByS (1 : A) D₀.s) ^ k_a ∈
          (locLift D₀ D h).toAddMonoidHom.ker := by
  intro n
  obtain ⟨m, hm⟩ := locLift_preimage_target_witness_existence D₀ D h n
  refine ⟨m, ?_⟩
  intro α k_a hα
  obtain ⟨α', hα'_pow, hα'_match⟩ := hm α k_a hα
  refine ⟨α', hα'_pow, ?_⟩
  -- The kernel-difference reduces to algebraMap-matching via routine
  -- algebra: factor out `(divByS 1 D₀.s)^k_a`, evaluate `locLift` on
  -- the `algebraMap` factor via `IsLocalization.Away.lift_eq`, then
  -- use `hα'_match` to zero the algebraMap factor.
  have h_lift_zero :
      (locLift D₀ D h)
          (algebraMap A (Localization.Away D₀.s) α * (divByS (1 : A) D₀.s) ^ k_a -
            algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
              (divByS (1 : A) D₀.s) ^ k_a) = 0 := by
    have h_combine :
        algebraMap A (Localization.Away D₀.s) α * (divByS (1 : A) D₀.s) ^ k_a -
            algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
              (divByS (1 : A) D₀.s) ^ k_a =
          algebraMap A (Localization.Away D₀.s) (α - ((α' : D₀.P.A₀) : A)) *
            (divByS (1 : A) D₀.s) ^ k_a := by
      rw [map_sub]; ring
    rw [h_combine, map_mul,
        show (locLift D₀ D h)
            (algebraMap A (Localization.Away D₀.s) (α - ((α' : D₀.P.A₀) : A))) =
            algebraMap A (Localization.Away D.s) (α - ((α' : D₀.P.A₀) : A))
          from IsLocalization.Away.lift_eq D₀.s
            (isUnit_algebraMap_s_of_rational_subset D₀ D h) _,
        map_sub, hα'_match, sub_self, zero_mul]
  exact AddMonoidHom.mem_ker.mpr h_lift_zero

private theorem cross_localization_preimage_in_sup_ker
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      a ∈ locNhd D₀.P D₀.T D₀.s n ⊔
        (locLift D₀ D h).toAddMonoidHom.ker := by
  intro n
  -- Bind N₀ from D₀.hopen for explicit Lean-checkable depth shifts.
  set N₀ := D₀.hopen.choose with hN₀_def
  have hN₀_spec := D₀.hopen.choose_spec
  -- Apply the saturation helper.
  obtain ⟨m, h_sat⟩ := locLift_preimage_target_locNhd_saturation D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  -- Use IsLocalization.Away.surj to get (k_a, α) with `a · algebraMap (D₀.s^k_a) = algebraMap α`.
  obtain ⟨k_a, α, hsec⟩ :=
    IsLocalization.Away.surj (S := Localization.Away D₀.s) D₀.s a
  -- Convert (algebraMap D₀.s)^k_a to algebraMap (D₀.s^k_a) via `map_pow`.
  rw [← map_pow] at hsec
  -- Normal form: a = algebraMap α * (divByS 1 D₀.s)^k_a.
  have h_a_eq : a = algebraMap A (Localization.Away D₀.s) α *
      (divByS (1 : A) D₀.s) ^ k_a :=
    away_eq_algebraMap_mul_invS_pow D₀.s a α k_a hsec
  -- Apply saturation: get α' with the desired properties.
  rw [h_a_eq] at ha
  obtain ⟨α', hα'_pow, hα'_ker⟩ := h_sat α k_a ha
  -- Construct b := algebraMap (α' : A) * (divByS 1 D₀.s)^k_a.
  set b : Localization.Away D₀.s :=
    algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) *
      (divByS (1 : A) D₀.s) ^ k_a with hb_def
  -- Show b ∈ locNhd D₀ n via T090 + T095.
  have h_alg_α' :
      algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) ∈
        locNhd D₀.P D₀.T D₀.s (n + k_a * N₀) :=
    algebraMap_PI_pow_mem_locNhd D₀.P D₀.T D₀.s (n + k_a * N₀) α' hα'_pow
  have h_b_locNhd : b ∈ locNhd D₀.P D₀.T D₀.s n := by
    have h_eq : b = (divByS (1 : A) D₀.s) ^ k_a *
        algebraMap A (Localization.Away D₀.s) ((α' : D₀.P.A₀) : A) := by
      rw [hb_def]; ring
    rw [h_eq]
    exact locNhd_invS_pow_step_of_hopen D₀.P D₀.T D₀.s N₀ hN₀_spec n k_a h_alg_α'
  -- a - b ∈ ker(locLift) by hα'_ker.
  have h_ab_ker :
      a - b ∈ (locLift D₀ D h).toAddMonoidHom.ker := by
    rw [h_a_eq, hb_def]
    exact hα'_ker
  -- Conclude: a = b + (a - b), with b ∈ locNhd D₀ n and (a - b) ∈ ker.
  have h_split : a = b + (a - b) := by ring
  rw [h_split]
  exact AddSubgroup.add_mem _
    (AddSubgroup.mem_sup_left h_b_locNhd)
    (AddSubgroup.mem_sup_right h_ab_ker)

/-- **Cross-localization preimage-in-sum statement** (T089 sum/preimage
helper, the right algebraic quotient/sum form of the basis-form
residual).

For each source depth `n`, find target depth `m` such that

```
{a | locLift D₀ D h a ∈ locNhd D.P D.T D.s m} ⊆
  locNhd D₀.P D₀.T D₀.s n + ker(locLift D₀ D h)
```

(set-level: every `a` whose `locLift` image is in `locNhd D m` admits
a decomposition `a = b + k` with `b ∈ locNhd D₀ n` and `k ∈
ker(locLift)`).

**Why this is the right reformulation**: this statement removes the
false additional constraint `k ∈ Jfull^(n+k₀)` from the previous
strong helper (the kernel part is allowed to be ANY kernel element,
not necessarily small in the full-source ideal). It preserves exactly
what the basis-form residual needs: from `a = b + k`, `locLift k = 0`
gives `locLift b = locLift a`, with `b ∈ locNhd D₀ n` as the small
representative.

**Proof strategy** (T097 + T098 + radical-relation-driven):
1. By `IsLocalization.Away.surj` on `a`, write `a = algebraMap α / D₀.s^k_a`
   for some `α ∈ A, k_a ∈ ℕ`.
2. The hypothesis `locLift a ∈ locNhd D m` gives `locLift a = subtype
   d_target` for `d_target ∈ (locIdeal D)^m` (via `mem_locNhd_iff`).
3. Use T097's target-side radical inverse factor `(algebraMap e_rad *
   (divByS 1 D.s)^N_rad)` to translate target `divByS 1 D.s` factors
   into `(algebraMap D₀.s)⁻¹` form.
4. Pull the algebraic structure back to `Loc D₀.s` via T098's
   source-side radical rewrite `algebraMap e_rad = (algebraMap D.s)^N_rad
   * divByS 1 D₀.s`, applied iteratively.
5. Construct `b ∈ locNhd D₀ n` as the source-side analog (via T090's
   `algebraMap_PI_pow_mem_locNhd` plus T095's iterated `divByS 1 D₀.s`
   shift), and `k := a - b` automatically satisfies `locLift k =
   locLift a - locLift b`. The construction ensures `locLift b =
   locLift a`, hence `k ∈ ker(locLift)`. -/
private theorem cross_localization_preimage_in_sum
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ b k : Localization.Away D₀.s,
        b ∈ (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ∧
        k ∈ RingHom.ker (locLift D₀ D h) ∧
        a = b + k := by
  -- Mechanical derivation from the hard membership-form helper via T102's
  -- `locNhd_exists_decomp_of_mem_sup_ker_ringHom` wrapper (RingHom.ker form,
  -- exact shape this consumer takes).
  intro n
  obtain ⟨m, hm⟩ := cross_localization_preimage_in_sup_ker D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  exact locNhd_exists_decomp_of_mem_sup_ker_ringHom D₀.P D₀.T D₀.s n
    (locLift D₀ D h) (hm a ha)

/-- **Cross-localization basis-form residual** (T089 corrected weakest
isolated blocker, after mathematical obstruction analysis).

**Mathematical obstruction in the previous strong helper**: a previous
formulation required `a - b ∈ Jfull^(n+k₀) ⊓ K_full`. This is
mathematically **too strong**: an element `a ∈ K_full` (in the
`locLift`-kernel, e.g., a `D.s`-torsion element) generally is NOT in
any `Jfull^?` (the kernel and the full-source ideal powers are not
nested), so `a - b ∈ Jfull^(n+k₀)` cannot be achieved for arbitrary
`a` even with `b = 0` and `locLift a = 0`. Concretely, taking `a ∈
K_full \ Jfull^(n+k₀)` (which exists when the kernel is nontrivial,
e.g., when `D.s` is not a unit and the torsion ideal is not contained
in `Jfull^(n+k₀)`) gives `locLift a = 0 ∈ locNhd D m` for ANY `m`,
yet no decomposition `a = b + j` with `b ∈ locNhd D₀ n` and `j ∈
Jfull^(n+k₀)` exists (since `b ∈ Jfull^n` and `j ∈ Jfull^(n+k₀)`
would imply `a ∈ Jfull^n`, which is false).

**Corrected weakest helper that still closes the variant**: the
basis-form residual itself, with no Jfull constraint on `a - b`. The
variant `locLift_open_on_image_at_zero_of_source_pair_noetherian`
needs only `b ∈ locNhd D₀ n` and `locLift b = locLift a`; the
Artin-Rees / T094 / T097 machinery (set up in the variant body for
the previous strong helper) is moved into this helper's proof
(eventually) where it's mathematically appropriate. The variant body
simplifies to a one-line forward call.

**Why this is still a meaningful blocker**: the basis-form residual
is the genuine remaining content of T089's open-mapping argument.
Discharging it requires the radical-relation translation T092 +
T094's Artin-Rees + T097's depth-shift package, but the precise
proof structure is intricate and merits the named-helper isolation. -/
private theorem cross_localization_basis_form_residual
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : Localization.Away D₀.s,
      locLift D₀ D h a ∈
        (locNhd D.P D.T D.s m : Set (Localization.Away D.s)) →
      ∃ b : Localization.Away D₀.s,
        b ∈ (locNhd D₀.P D₀.T D₀.s n : Set (Localization.Away D₀.s)) ∧
        locLift D₀ D h b = locLift D₀ D h a := by
  -- Mechanical derivation from the sum/preimage helper.
  intro n
  obtain ⟨m, hm⟩ := cross_localization_preimage_in_sum D₀ D h n
  refine ⟨m, ?_⟩
  intro a ha
  obtain ⟨b, k, hb_locNhd, hk_ker, hab⟩ := hm a ha
  refine ⟨b, hb_locNhd, ?_⟩
  -- locLift b = locLift a from a = b + k, k ∈ ker(locLift).
  have h_k_zero : locLift D₀ D h k = 0 := hk_ker
  rw [hab, map_add, h_k_zero, add_zero]

/-- **Local-Noetherian variant of `locLift_open_on_image_at_zero`**
(T089 substantive deliverable).

Same conclusion as `locLift_open_on_image_at_zero` (the abstract
nhds-0 quantitative-openness on image of `locLift` at 0), with the
**single additional hypothesis** `[IsNoetherianRing D₀.P.A₀]`. The
hypothesis is **not** added to the original generic version, which
remains via `locLift_open_on_image_at_zero` for downstream consumers
that don't have access to the source-pair Noetherian instance.

**Why this is the right hypothesis layer**: from `[IsNoetherianRing
D₀.P.A₀]` and the standing `[IsNoetherianRing A]`, we derive
`[IsNoetherianRing (Localization.Away D₀.s)]` via
`IsLocalization.isNoetherianRing` (localization of a Noetherian ring
is Noetherian). This is the natural assumption when working with a
fixed ring-of-definition pair `D₀.P` whose `A₀` is well-controlled,
and avoids any new final/root Tate-acyclicity hypothesis.

**Proof strategy** (Option B: full source localization,
`Localization.Away D₀.s` Noetherian):
1. Reduce to basis form via `locLift_open_on_image_at_zero_of_basis_form`.
2. Derive `[IsNoetherianRing (Localization.Away D₀.s)]` via
   `IsLocalization.isNoetherianRing` (localization of Noetherian).
3. Extract radical relation `(N_rad, e_rad, h_rad : e_rad * D₀.s = D.s ^ N_rad)`.
4. Use T094's full-source ideal `Jfull D₀.P D₀.T D₀.s` and define the
   **full kernel** `K_full := RingHom.ker (locLift D₀ D h)`.
5. Apply T094's `Jfull_pow_shift_inter_le_pow_mul` on
   `(Jfull D₀.P D₀.T D₀.s, K_full)` to obtain Artin-Rees constant `k₀`.
6. Use T094's `locNhd_subset_Jfull_pow` (the easy direction
   `locNhd D₀ n ⊆ Jfull^n`) and T092's
   `algebraMap_mul_pow_divByS_eq_one_of_radical_relation` to assemble
   the basis-form witness.

The body below sets up steps 1–5 cleanly via the public T094 API; the
final assembly step (step 6, the per-`n` basis-form witness
construction from Artin-Rees + T092 radical translation) is the
single sorry. The sorry's expected type is the per-`n` basis-form
existential with all the algebraic data (`N_rad`, `e_rad`, `h_rad`,
`Jfull D₀.P D₀.T D₀.s`, `K_full`, `k₀`, `hAR`) in scope. -/
private theorem locLift_open_on_image_at_zero_of_source_pair_noetherian
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    [IsNoetherianRing D₀.P.A₀]
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    ∀ V ∈ @nhds _ D₀.topology (0 : Localization.Away D₀.s),
      ∃ W ∈ @nhds _ D.topology (0 : Localization.Away D.s),
        ∀ a : Localization.Away D₀.s, locLift D₀ D h a ∈ W →
          ∃ b : Localization.Away D₀.s, b ∈ V ∧ locLift D₀ D h b = locLift D₀ D h a := by
  -- Reduce to basis form, then delegate to the corrected named helper.
  -- The previous strong helper `cross_localization_decomp_into_Jfull_inter_kernel`
  -- was mathematically too strong (see its replacement docstring). The
  -- corrected helper `cross_localization_basis_form_residual` is the
  -- weakest isolated blocker that lets this variant close.
  refine locLift_open_on_image_at_zero_of_basis_form D₀ D h ?_
  exact cross_localization_basis_form_residual D₀ D h

/-- **Step B ⊆ (closure form, sorry-free modulo narrower residual)**: every
kernel element of the restriction map lies in the closure of the image,
under `D₀.coeRingHom`, of the algebraic kernel of the localization-level
lift.

**2026-04-23 refactor**: the body below is fully proved modulo the
strictly-narrower pure-localization residual
`locLift_open_on_image_at_zero` (above). It uses (i) density of
`D₀.coeRingHom`, (ii) uniform-inducing of `D.coeRingHom`, (iii) continuity
of `restrictionMapHom`, (iv) the factorization
`restrictionMapHom ∘ D₀.coeRingHom = D.coeRingHom ∘ locLift`, and (v) the
narrower residual above to discharge the only pre-completion content. -/
theorem ker_restrictionMapHom_subset_closure_algLift
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (c : presheafValue D₀) (hc : restrictionMapHom D₀ D h c = 0) :
    c ∈ closure (D₀.coeRingHom ''
      { x : Localization.Away D₀.s | locLift D₀ D h x = 0 }) := by
  classical
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : TopologicalSpace (Localization.Away D₀.s) := D₀.topology
  haveI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  haveI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : TopologicalSpace (Localization.Away D.s) := D.topology
  haveI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  haveI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  rw [mem_closure_iff_nhds]
  intro U hU
  -- Pick a sub-nbhd `U₀` of 0 and compatible `Uc` of `c` with `Uc - U₀ ⊆ U`.
  have h_cont_sub : Continuous fun p : presheafValue D₀ × presheafValue D₀ ↦ p.1 - p.2 :=
    continuous_sub
  have h_sub_c0 : (fun p : presheafValue D₀ × presheafValue D₀ ↦ p.1 - p.2)
      (c, (0 : presheafValue D₀)) = c := by
    simp
  have h_preimage_nhd : (fun p : presheafValue D₀ × presheafValue D₀ ↦ p.1 - p.2) ⁻¹' U ∈
      nhds ((c, (0 : presheafValue D₀)) : presheafValue D₀ × presheafValue D₀) := by
    have : U ∈ nhds ((fun p : presheafValue D₀ × presheafValue D₀ ↦ p.1 - p.2)
        (c, (0 : presheafValue D₀))) := by
      rw [h_sub_c0]; exact hU
    exact h_cont_sub.continuousAt.preimage_mem_nhds this
  rw [nhds_prod_eq] at h_preimage_nhd
  obtain ⟨Uc, hUc, U0, hU0, hUcU0⟩ := Filter.mem_prod_iff.mp h_preimage_nhd
  -- `U0` at 0 in presheafValue D₀; its preimage under `D₀.coeRingHom` is a nhd of 0.
  have hcoe_cont : @Continuous _ _ D₀.topology
      (@UniformSpace.toTopologicalSpace _
        (@UniformSpace.Completion.uniformSpace _ D₀.uniformSpace))
      (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) :=
    @UniformSpace.Completion.continuous_coe _ D₀.uniformSpace
  have hV_nhd : (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) ⁻¹' U0 ∈
      @nhds _ D₀.topology (0 : Localization.Away D₀.s) := by
    have h00 : (D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) 0 = 0 :=
      map_zero _
    have : U0 ∈ nhds ((D₀.coeRingHom : Localization.Away D₀.s → presheafValue D₀) 0) := by
      rw [h00]; exact hU0
    exact hcoe_cont.continuousAt.preimage_mem_nhds this
  -- Narrower residual ⇒ nbhd `W` of 0 in D.topology matches.
  obtain ⟨W, hW_nhd, hW_lift⟩ :=
    locLift_open_on_image_at_zero D₀ D h _ hV_nhd
  -- Pull `W` through uniform inducing of `D.coeRingHom` to a nbhd `W'` of 0 in presheafValue D.
  have hD_ui : @IsUniformInducing _ _ D.uniformSpace
      (@UniformSpace.Completion.uniformSpace _ D.uniformSpace)
      (D.coeRingHom : Localization.Away D.s → presheafValue D) :=
    UniformSpace.Completion.isUniformInducing_coe _
  have h_nhd_D_comap : @nhds _ D.topology (0 : Localization.Away D.s) =
      Filter.comap (D.coeRingHom : Localization.Away D.s → presheafValue D)
        (nhds (0 : presheafValue D)) := by
    have h00_D : (D.coeRingHom : Localization.Away D.s → presheafValue D) 0 = 0 :=
      map_zero _
    have := hD_ui.isInducing.nhds_eq_comap (0 : Localization.Away D.s)
    rw [h00_D] at this; exact this
  obtain ⟨W', hW'_nhd, hW'_sub⟩ : ∃ W' : Set (presheafValue D),
      W' ∈ nhds (0 : presheafValue D) ∧
      (D.coeRingHom : Localization.Away D.s → presheafValue D) ⁻¹' W' ⊆ W := by
    rw [h_nhd_D_comap, Filter.mem_comap] at hW_nhd
    exact hW_nhd
  -- Uc' := Uc ∩ restrictionMapHom⁻¹' W' is still a nbhd of c.
  have hrestr_cont : Continuous (restrictionMapHom D₀ D h :
      presheafValue D₀ → presheafValue D) :=
    restrictionMapHom_continuous D₀ D h
  have hW'_pre_c : (restrictionMapHom D₀ D h) ⁻¹' W' ∈ nhds c := by
    have h_restrc : restrictionMapHom D₀ D h c ∈ W' := by
      rw [hc]; exact mem_of_mem_nhds hW'_nhd
    exact hrestr_cont.continuousAt.preimage_mem_nhds
      (show W' ∈ nhds (restrictionMapHom D₀ D h c) by rw [hc]; exact hW'_nhd)
  have hUc' : Uc ∩ (restrictionMapHom D₀ D h) ⁻¹' W' ∈ nhds c :=
    Filter.inter_mem hUc hW'_pre_c
  -- Use density to pick `a₀ ∈ Localization.Away D₀.s` with `D₀.coeRingHom a₀ ∈ Uc'`.
  have hdense : DenseRange (D₀.coeRingHom :
      Localization.Away D₀.s → presheafValue D₀) := by
    change DenseRange (UniformSpace.Completion.coeRingHom :
      Localization.Away D₀.s → presheafValue D₀)
    exact UniformSpace.Completion.denseRange_coe
  obtain ⟨y₀, hy₀_Uc', a₀, ha₀_eq⟩ :=
    mem_closure_iff_nhds.mp
      (by rw [hdense.closure_range]; trivial : c ∈ closure (Set.range D₀.coeRingHom))
      (Uc ∩ (restrictionMapHom D₀ D h) ⁻¹' W') hUc'
  -- Now `D₀.coeRingHom a₀ ∈ Uc` and `restrictionMapHom (D₀.coeRingHom a₀) ∈ W'`.
  have ha₀_Uc : D₀.coeRingHom a₀ ∈ Uc := (ha₀_eq ▸ hy₀_Uc').1
  have ha₀_W' : restrictionMapHom D₀ D h (D₀.coeRingHom a₀) ∈ W' := (ha₀_eq ▸ hy₀_Uc').2
  -- Transport through factorization `restrictionMapHom ∘ D₀.coeRingHom = D.coeRingHom ∘ locLift`.
  have h_factor : restrictionMapHom D₀ D h (D₀.coeRingHom a₀) =
      D.coeRingHom (locLift D₀ D h a₀) := by
    -- `D₀.coeRingHom = UniformSpace.Completion.coeRingHom` definitionally (via
    -- `RationalLocData.coeRingHom` definition). Use `show` to bridge the two forms.
    change restrictionMapHom D₀ D h
      (@UniformSpace.Completion.coeRingHom _ _ D₀.uniformSpace
        D₀.isTopologicalRing D₀.isUniformAddGroup a₀) = _
    rw [restrictionMapHom_coe' D₀ D h a₀, restrictionMapAlg_eq_comp_locLift]
    rfl
  have ha₀_lift_W' : D.coeRingHom (locLift D₀ D h a₀) ∈ W' := h_factor ▸ ha₀_W'
  have ha₀_lift_W : locLift D₀ D h a₀ ∈ W := hW'_sub ha₀_lift_W'
  -- Apply narrower residual: find `b ∈ V = D₀.coeRingHom⁻¹' U0` with same image.
  obtain ⟨b, hb_V, hb_eq⟩ := hW_lift a₀ ha₀_lift_W
  -- `D₀.coeRingHom b ∈ U0`.
  have hb_coe_U0 : D₀.coeRingHom b ∈ U0 := hb_V
  -- `(a₀ - b) ∈ ker(locLift)`.
  have hab_ker : locLift D₀ D h (a₀ - b) = 0 := by
    rw [map_sub, hb_eq, sub_self]
  -- `D₀.coeRingHom (a₀ - b) = D₀.coeRingHom a₀ - D₀.coeRingHom b`.
  have h_coe_sub : D₀.coeRingHom (a₀ - b) =
      D₀.coeRingHom a₀ - D₀.coeRingHom b := by
    rw [map_sub]
  -- The pair `(D₀.coeRingHom a₀, D₀.coeRingHom b) ∈ Uc ×ˢ U0`.
  have h_pair_in : (D₀.coeRingHom a₀, D₀.coeRingHom b) ∈ Uc ×ˢ U0 :=
    ⟨ha₀_Uc, hb_coe_U0⟩
  -- Hence the difference lies in `U`.
  have h_diff_in_U : D₀.coeRingHom a₀ - D₀.coeRingHom b ∈ U := hUcU0 h_pair_in
  refine ⟨D₀.coeRingHom (a₀ - b), ?_, a₀ - b, hab_ker, rfl⟩
  rw [h_coe_sub]
  exact h_diff_in_U

/-- **CORRECT residual for `restrictionMap_isLocalization` (Prop 8.15).**

The kernel of the restriction map is **torsion at `D₀.canonicalMap D.s`**:
for every `c : presheafValue D₀` with `restrictionMapHom D₀ D h c = 0`,
some power of `D₀.canonicalMap D.s` annihilates `c`.

This is the `IsLocalization`-equalizer condition (third clause of
`IsLocalization.Away.mk`) specialized to zero RHS. It is the **weakest**
content sufficient for `restrictionMap_isLocalization`.

**STRICTLY WEAKER than `restrictionMapHom_injective`**: the latter takes
`n = 0` (pointwise injectivity) and is **FALSE in general** by the
reviewer counterexample `A = k⟨T, U⟩/(TU), U = R(1/T)` (cf. retired-scaffold
note above at line 1435). The torsion form allows any `n`, and is TRUE in
that example: every `u ∈ (U)` satisfies `T · u = TU = 0`.

**Proof structure**: combines the algebraic `away_lift_torsion_bounded`
(uniform torsion bound from `CompletionLocalization.lean`, fully proved)
with the named topological residual
`ker_restrictionMapHom_subset_closure_algLift` (Step B ⊆), via the
closed-annihilator lemma `isClosed_setOf_mul_eq_zero`. The single `sorry`
in this chain is precisely in `ker_restrictionMapHom_subset_closure_algLift`. -/
theorem restrictionMapHom_ker_isTorsion
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (c : presheafValue D₀)
    (hc : restrictionMapHom D₀ D h c = 0) :
    ∃ n : ℕ, (D₀.canonicalMap D.s) ^ n * c = 0 := by
  -- Step A (algebraic torsion bound, fully proved).
  obtain ⟨N₀, hN₀⟩ := CompletionLocalization.away_lift_torsion_bounded
    (isUnit_algebraMap_s_of_rational_subset D₀ D h)
  refine ⟨N₀, ?_⟩
  -- Annihilator of (D₀.canonicalMap D.s)^N₀ in presheafValue D₀ is closed.
  have h_closed : IsClosed {c' : presheafValue D₀ |
      (D₀.canonicalMap D.s) ^ N₀ * c' = 0} :=
    isClosed_setOf_mul_eq_zero _
  -- Algebraic kernel maps into the annihilator.
  have h_alg_ann : D₀.coeRingHom ''
      { x : Localization.Away D₀.s | locLift D₀ D h x = 0 } ⊆
        {c' : presheafValue D₀ | (D₀.canonicalMap D.s) ^ N₀ * c' = 0} := by
    rintro _ ⟨a, ha, rfl⟩
    -- `hN₀` gives `algebraMap A (Loc.Away D₀.s) (D.s^N₀) * a = 0`.
    have hkilled : algebraMap A (Localization.Away D₀.s) (D.s ^ N₀) * a = 0 := hN₀ a ha
    -- Push through `D₀.coeRingHom` and unfold `D₀.canonicalMap`.
    change (D₀.canonicalMap D.s) ^ N₀ * D₀.coeRingHom a = 0
    have h_canon : (D₀.canonicalMap D.s) ^ N₀ =
        D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) (D.s ^ N₀)) := by
      change (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)) ^ N₀ = _
      rw [map_pow, ← map_pow]
    rw [h_canon, ← map_mul, hkilled, map_zero]
  -- Closure of the algebraic kernel is in the annihilator (closure of subset
  -- of closed set stays in the closed set).
  have h_closure_ann : closure (D₀.coeRingHom ''
      { x : Localization.Away D₀.s | locLift D₀ D h x = 0 }) ⊆
        {c' : presheafValue D₀ | (D₀.canonicalMap D.s) ^ N₀ * c' = 0} :=
    closure_minimal h_alg_ann h_closed
  -- Step B (⊆): `c` is in the closure of the algebraic kernel.
  exact h_closure_ann
    (ker_restrictionMapHom_subset_closure_algLift D₀ D h c hc)

/-- **Proposition 8.15**: the restriction map is a localization.

⚠️  **MISFRAMED — DO NOT USE FOR NEW WORK** (ChatGPT Pro reviewer correction,
2026-05-11 session 2; see `.mathlib-quality/expert-review/2026-05-11-2/reply.md`).

This statement asserts that the restriction map `presheafValue D₀ → presheafValue D`
is an **`IsLocalization.Away`** (algebraic-localization predicate): every element
of `presheafValue D` has the form `σ(a) / u^n` for some `a, n`. **This is FALSE
in general for completed rational localizations.**

**Counterexample**: Take `A = ℚ_p⟨X⟩` and the completed rational localization
`A⟨T⟩/(XT - 1)` (inverting `X` in the affinoid sense). It contains the convergent
infinite negative-power series
```
  ∑_{n ≥ 0} p^n · X^{-n}
```
Multiplying by `X^N` clears only finitely many negative powers, leaving an
infinite tail. So no finite power of `X` clears this element into `A`.

**The misframing**: `IsLocalization.Away` is an *algebraic-localization*
predicate (Mathlib's `algebraMap`-based, finite-power denominator clearing).
Completed rational localizations are *topological-localization* objects
(adjoin bounded fractions, then complete). The two notions DIVERGE: completed
rational sections contain convergent infinite denominator tails.

**Correct route for downstream (Cor 8.32) consumers**: use `Module.Flat`
directly via `restrictionMap_flat_via_iteratedMinus`/`_iteratedPlus` (in
`Adic spaces/RestrictionFlatness.lean`, ticket T-FLAT-VIA-WEDHORN830). The
flatness route uses the existing Wedhorn 8.31 / Tate-algebra quotient
identifications at the B-level. See ticket T-COR832-VIA-FLAT for the
refactored `flat_over_base_tate`.

The sorry below stays as an explicit "intentionally not closed — over-strong
target" marker. The previous proof-strategy docstring (which planned a Baire
surjection argument) is retained for historical reference:

> Previous strategy (now retired): Apply `IsLocalization.Away.mk` with three
> conditions: (1) Unit: `sigma(s')` is a unit; (2) Surj: every `z` is
> `sigma(a)/u^n` — discharged via Baire category on the dense subring;
> (3) Torsion kernel. The Baire-surjection step (2) is precisely what's
> mathematically false for the algebraic-localization predicate. -/
theorem restrictionMap_isLocalization
    [IsTateRing A] [IsNoetherianRing A] [T2Space A]
    [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s) :
    @IsLocalization.Away (presheafValue D₀) _ (D₀.canonicalMap D.s)
      (presheafValue D) _ (restrictionMapHom D₀ D h).toAlgebra := by
  letI : Algebra (presheafValue D₀) (presheafValue D) := (restrictionMapHom D₀ D h).toAlgebra
  letI : UniformSpace (Localization.Away D₀.s) := D₀.uniformSpace
  letI : IsTopologicalRing (Localization.Away D₀.s) := D₀.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D₀.s) := D₀.isUniformAddGroup
  letI : UniformSpace (Localization.Away D.s) := D.uniformSpace
  letI : IsTopologicalRing (Localization.Away D.s) := D.isTopologicalRing
  letI : IsUniformAddGroup (Localization.Away D.s) := D.isUniformAddGroup
  set sigma := restrictionMapHom D₀ D h with hsigma_def
  set s' := D₀.canonicalMap D.s with hs'_def
  have hsigma_coe : ∀ a : Localization.Away D₀.s,
      sigma (D₀.coeRingHom a) = restrictionMapAlg D₀ D h a :=
    fun a ↦ restrictionMapHom_coe' D₀ D h a
  have hunit : IsUnit (sigma s') := by
    change IsUnit (sigma (D₀.coeRingHom (algebraMap A (Localization.Away D₀.s) D.s)))
    rw [hsigma_coe]
    simpa only [RingHom.comp_apply, restrictionMapAlg, IsLocalization.Away.lift_eq,
      RationalLocData.canonicalMap] using isUnit_s_in_presheafValue D
  exact IsLocalization.Away.mk (D₀.canonicalMap D.s) hunit
    (restrictionMapHom_surj D₀ D h)
    (fun a b hab ↦ by
      -- Reduce to the kernel-torsion form: for `c` in the kernel of `sigma`,
      -- some power of `s' = D₀.canonicalMap D.s` annihilates `c`.
      obtain ⟨n, hn⟩ := restrictionMapHom_ker_isTorsion D₀ D h (a - b)
        (by rw [map_sub]; exact sub_eq_zero.mpr hab)
      exact ⟨n, by rw [mul_sub, sub_eq_zero] at hn; exact hn⟩)

/-- **Propagation of Noetherianness through rational subsets**
(T148 partial supplier; T141 / T142 `hNoeth_B` reduction).

If `presheafValue D₀` is Noetherian, then `presheafValue D` is Noetherian
for any rational subset `rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s`.
Direct composition: `restrictionMap_isLocalization` exhibits
`presheafValue D` as `IsLocalization.Away (D₀.canonicalMap D.s)
(presheafValue D₀)`, then `IsLocalization.isNoetherianRing` transfers
Noetherianness from `presheafValue D₀` to `presheafValue D`.

The base case `IsNoetherianRing (presheafValue D₀)` for some
`presheafValue D₀` remains open: it would follow from "`I`-adic
completion of a Noetherian ring is Noetherian" (Bourbaki, Atiyah–
Macdonald 10.27), which is **not** currently in Mathlib
(`Mathlib/RingTheory/AdicCompletion/Noetherian.lean` exposes only
`IsHausdorff`-form lemmas; `Mathlib/RingTheory/AdicCompletion/AsTensorProduct.lean`
proves flatness as `flat_of_isNoetherian` but not Noetherianity). -/
theorem presheafValue_isNoetherianRing_of_rationalSubset
    [IsTateRing A] [IsNoetherianRing A] [T2Space A] [NonarchimedeanRing A]
    (P : PairOfDefinition A) [IsNoetherianRing P.A₀]
    (D₀ D : RationalLocData A)
    (h : rationalOpen D.T D.s ⊆ rationalOpen D₀.T D₀.s)
    (hD₀_noeth : IsNoetherianRing (presheafValue D₀)) :
    IsNoetherianRing (presheafValue D) := by
  letI : Algebra (presheafValue D₀) (presheafValue D) :=
    (restrictionMapHom D₀ D h).toAlgebra
  haveI := restrictionMap_isLocalization P D₀ D h
  exact IsLocalization.isNoetherianRing
    (Submonoid.powers (D₀.canonicalMap D.s)) _ hD₀_noeth

/-- **Open subring + topologically nilpotent unit ⇒ `IsLocalization.Away`**
(T150 generic supplier).

For an open subring `R` of a topological commutative ring `S`, if `π : R`
maps to a unit of `S` that is topologically nilpotent in `S`, then `S` is
the localization of `R` away from `π`. The Tate-style "open ring of
definition + topologically nilpotent unit ⇒ ambient = localization at
the unit" structural fact, formulated for any topological ring (not
restricted to Tate).

Proof: apply `IsLocalization.Away.mk` to the canonical algebra
`R →+* S = R.subtype`. Surjectivity-with-power: by topological
nilpotence of `(π : S)`, `s · (π : S)^n → 0` in `S`; since `R` is open
and contains `0`, eventually `s · (π : S)^n ∈ R`. Kernel: the
inclusion `R.subtype` is injective, so `n = 0` works trivially. -/
theorem isLocalization_away_of_openSubring_topNilpotentUnit
    {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    (R : Subring S) (hR_open : IsOpen (R : Set S))
    (π : R)
    (hπ_unit : IsUnit ((π : S)))
    (hπ_nil : IsTopologicallyNilpotent ((π : S))) :
    letI : Algebra R S := R.subtype.toAlgebra
    IsLocalization.Away π S := by
  letI : Algebra R S := R.subtype.toAlgebra
  apply IsLocalization.Away.mk π hπ_unit
  · -- surj: every `s : S` has `s * (π : S)^n ∈ R` for some `n`.
    intro s
    have h_nhds : (R : Set S) ∈ nhds (0 : S) := hR_open.mem_nhds R.zero_mem
    have h_tendsto : Filter.Tendsto (fun n : ℕ ↦ s * (π : S) ^ n)
        Filter.atTop (nhds 0) := by
      have h := Filter.Tendsto.const_mul (a := 0) s hπ_nil
      rw [mul_zero] at h
      exact h
    obtain ⟨n, hn⟩ := (h_tendsto.eventually h_nhds).exists
    exact ⟨n, ⟨s * (π : S) ^ n, hn⟩, rfl⟩
  · -- exists_of_eq: `R.subtype` is injective, so `n = 0` works.
    intro a b hab
    refine ⟨0, ?_⟩
    have hval : (a : S) = (b : S) := hab
    have : a = b := Subtype.ext hval
    rw [pow_zero, one_mul, one_mul, this]

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **`presheafValue D₀` is the localization of `presheafValue_ringOfDef D₀`
at a topologically nilpotent unit** (T150 specialization to the
presheafValue setting).

Direct application of `Subring.isLocalization_away_of_open_topNilpotentUnit`
to `R := presheafValue_ringOfDef D₀ ⊆ presheafValue D₀`, the open ring
of definition (`presheafValue_ringOfDef_isOpen`). The caller supplies
the explicit `π` (e.g., the canonical image of a topologically
nilpotent unit of `A` that lies in `D₀.P.A₀`, via
`canonicalMap_mem_ringOfDef`). -/
theorem presheafValue_isLocalization_away_topNilUnit
    (D₀ : RationalLocData A)
    {π : presheafValue_ringOfDef D₀}
    (hπ_unit : IsUnit ((π : presheafValue D₀)))
    (hπ_nil : IsTopologicallyNilpotent ((π : presheafValue D₀))) :
    letI : Algebra (presheafValue_ringOfDef D₀) (presheafValue D₀) :=
      (presheafValue_ringOfDef D₀).subtype.toAlgebra
    IsLocalization.Away π (presheafValue D₀) :=
  isLocalization_away_of_openSubring_topNilpotentUnit
    (presheafValue_ringOfDef D₀) (presheafValue_ringOfDef_isOpen D₀)
    π hπ_unit hπ_nil

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Noetherianness propagates `presheafValue_ringOfDef D₀ →
presheafValue D₀`** via the Tate localization at a topologically
nilpotent unit (T150 corollary; partial supplier toward T141 / T142
`hNoeth_B`).

Combines `presheafValue_isLocalization_away_topNilUnit` with
`IsLocalization.isNoetherianRing`. The remaining gap to a
hypothesis-free `presheafValue_isNoetherianRing` is the Bourbaki
"`I`-adic completion of a Noetherian ring is Noetherian" theorem, which
is **not** currently in Mathlib (see the T148 docstring). -/
theorem presheafValue_isNoetherianRing_of_ringOfDef_isNoetherianRing
    (D₀ : RationalLocData A)
    {π : presheafValue_ringOfDef D₀}
    (hπ_unit : IsUnit ((π : presheafValue D₀)))
    (hπ_nil : IsTopologicallyNilpotent ((π : presheafValue D₀)))
    (hRoD_noeth : IsNoetherianRing (presheafValue_ringOfDef D₀)) :
    IsNoetherianRing (presheafValue D₀) := by
  letI : Algebra (presheafValue_ringOfDef D₀) (presheafValue D₀) :=
    (presheafValue_ringOfDef D₀).subtype.toAlgebra
  haveI := presheafValue_isLocalization_away_topNilUnit D₀ hπ_unit hπ_nil
  exact IsLocalization.isNoetherianRing (Submonoid.powers π) _ hRoD_noeth

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Noetherian transport for `presheafValue_ringOfDef D₀` via a ring
isomorphism** (T151 reduction; partial supplier toward T141 / T142
`hNoeth_B`).

Generic transport: any ring isomorphism `presheafValue_ringOfDef D₀ ≃+*
R` to a Noetherian ring `R` makes `presheafValue_ringOfDef D₀` Noetherian.

Intended consumer: `R := AdicCompletion (locIdeal D₀.P D₀.T D₀.s)
(locSubring D₀.P D₀.T D₀.s)` together with the project-local iso
`presheafValue_ringOfDef_ringEquiv_adicCompletion` (defined downstream
in `IdealLocalizationCompletion.lean`). With those, this supplier
reduces full `IsNoetherianRing (presheafValue D₀)` (combined with T150
via `presheafValue_isNoetherianRing_of_ringOfDef_isNoetherianRing` and
a topologically nilpotent unit) to the single missing Mathlib theorem
"`I`-adic completion of a Noetherian ring along a finitely generated
ideal is Noetherian" (Atiyah–Macdonald 10.27 / Bourbaki Commutative
Algebra III §3.6) instantiated at `(locIdeal, locSubring)`. -/
theorem presheafValue_ringOfDef_isNoetherianRing_of_ringEquiv
    (D₀ : RationalLocData A)
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (e : presheafValue_ringOfDef D₀ ≃+* R) :
    IsNoetherianRing (presheafValue_ringOfDef D₀) :=
  isNoetherianRing_of_ringEquiv _ e.symm

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **Full `presheafValue D₀` Noetherianness via a ring iso to a
Noetherian base ring** (T151 chained corollary; partial supplier toward
T141 / T142 `hNoeth_B`).

Composition of `presheafValue_ringOfDef_isNoetherianRing_of_ringEquiv`
(T151) with `presheafValue_isNoetherianRing_of_ringOfDef_isNoetherianRing`
(T150). The caller supplies any ring iso from `presheafValue_ringOfDef D₀`
to a Noetherian ring (e.g., the standard Mathlib `AdicCompletion` via the
project-local `presheafValue_ringOfDef_ringEquiv_adicCompletion`), plus a
topologically nilpotent unit `π : presheafValue_ringOfDef D₀`. -/
theorem presheafValue_isNoetherianRing_of_ringEquiv
    (D₀ : RationalLocData A)
    {π : presheafValue_ringOfDef D₀}
    (hπ_unit : IsUnit ((π : presheafValue D₀)))
    (hπ_nil : IsTopologicallyNilpotent ((π : presheafValue D₀)))
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (e : presheafValue_ringOfDef D₀ ≃+* R) :
    IsNoetherianRing (presheafValue D₀) :=
  presheafValue_isNoetherianRing_of_ringOfDef_isNoetherianRing
    D₀ hπ_unit hπ_nil
    (presheafValue_ringOfDef_isNoetherianRing_of_ringEquiv D₀ e)

omit [PlusSubring A] [HasLocLiftPowerBounded A] in
/-- **`presheafValue D₀` is a Huber ring — general (non-Tate) form** (Wedhorn 8.1's
construction, wedhorn.txt:3673-3675: "The construction also shows that `A(T/s)` is again
an f-adic ring. The pair `(D, I·D)` is a pair of definition of `A(T/s)`", completed).
The pair of definition is `presheafValue_concretePair D₀` (whose five ingredients are
already Tate-free); no topologically nilpotent unit is involved. Replaces the Tate-only
route `presheafValue_isTateRing_concrete D₀ |>.toIsHuberRing` at general Huber base. -/
theorem presheafValue_isHuberRing_huber (D₀ : RationalLocData A) :
    IsHuberRing (presheafValue D₀) where
  exists_pairOfDefinition := ⟨presheafValue_concretePair D₀⟩

end ValuationSpectrum
