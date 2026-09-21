/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyPair

/-!
# The public structure presheaf, bundled (Wedhorn §8.1–§8.2, Kedlaya Def 1.2.3)

This file makes the genuine all-open projective-limit presheaf (`limitSections`,
`StructurePresheafLimit.lean`) the **public structure presheaf** of `Spa (A, A⁺)`:

* `structurePresheaf A : Presheaf CompleteTopCommRingCat (SpaTop A)` — the functor
  `V ↦ 𝒪_X(V) = lim_{R(T/s) ⊆ V} A⟨T/s⟩` with the projective-limit topology
  (Kedlaya Definition 1.2.3; Wedhorn §8.1), values in the *coherent* category of
  complete separated topological commutative rings, restriction = `limitRestrict`.
  Identity and composition laws hold definitionally (reindexing).
* `IsSheafOfTopologicalRings A` — **Wedhorn's definition of "sheaf of topological
  rings"** (Remark 8.20, first form): for **every** topological commutative ring `T`
  (no completeness, separation, or discreteness assumed), the presheaf
  `V ↦ Hom_cont(T, 𝒪_X(V))` is a sheaf of sets.
* `isSheafOfTopologicalRings_iff_isLimitSheaf` — **Wedhorn Remark 8.20**: the
  representable condition is equivalent to `IsLimitSheaf` (ring-sheaf axioms + the
  topological-embedding condition for every open cover). The interesting direction
  tests against `T := 𝒪_X(V)` re-topologized with the topology induced from
  `∏ᵢ 𝒪_X(Uᵢ)`, and against discrete polynomial rings `ULift ℤ[X]` (element probes).
* `structurePresheaf_isSheaf` — under `IsLimitSheaf A`, the bundled presheaf
  satisfies mathlib's categorical sheaf condition (which for a non-`Type`-valued
  presheaf *is* the `Hom(E, −)`-by-`E` condition, [Stacks 00VR] — the same shape as
  Remark 8.20, tested along the category's objects).
* `structureSheaf A : Sheaf CompleteTopCommRingCat (SpaTop A)` (for `[IsSheafy A]`)
  and the rewired `AffinoidAdicPresentation.sheaf` — **sorry-free**; the discrete
  locally-fraction placeholder is no longer referenced by any public name.
* Universe reduction (`IsLimitSheaf.injective'`, `.glue'`, `.isEmbedding'`): the
  `ι : Type u` cover index of `IsLimitSheaf` extends to covers indexed by any
  `ι : Type v`, by factoring through the range family
  `{W : Opens ↥(Spa A A⁺) // ∃ i, U i = W}` — so the universe restriction in the
  structure does not weaken the sheaf property.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §8.1, Remark 8.20, Definition 8.21.
* [K. Kedlaya, *Sheaves, stacks, and shtukas* (AWS 2017)], Definition 1.2.3,
  Definition 1.2.8.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology Filter

universe v u

namespace ValuationSpectrum

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A] [HasLocLiftPowerBounded A]

/-! ### Uniform coherence of the limit values

`↥(limitSections V)` carries the subspace uniformity of the product of completions;
its topology is (definitionally) the topology of that uniformity, so the bundled
objects below are coherent by construction. -/

instance limitSections.isUniformAddGroup (V : Opens ↥(Spa A A⁺)) :
    IsUniformAddGroup ↥(limitSections V) :=
  IsUniformInducing.isUniformAddGroup (limitSections V).subtype
    isUniformEmbedding_subtype_val.isUniformInducing

instance limitSections.t0Space (V : Opens ↥(Spa A A⁺)) :
    T0Space ↥(limitSections V) :=
  inferInstance

/-! `SpaTop A` is an opaque `def` of `TopCat.of ↥(Spa A A⁺)`, so instance goals
arising from `Opens ↥(SpaTop A)`-typed opens do not unify with the
`Opens ↥(Spa A A⁺)`-form instances at reducible transparency. The following
aliases re-key the (proof-irrelevant) facts at the `SpaTop` form. -/

instance limitSections.isUniformAddGroup' (V : Opens ↥(SpaTop A)) :
    IsUniformAddGroup ↥(limitSections V) :=
  limitSections.isUniformAddGroup V

instance limitSections.completeSpace' (V : Opens ↥(SpaTop A)) :
    CompleteSpace ↥(limitSections V) :=
  limitSections.completeSpace V

instance limitSections.t0Space' (V : Opens ↥(SpaTop A)) :
    T0Space ↥(limitSections V) :=
  limitSections.t0Space V

/-! ### The bundled public structure presheaf -/

variable (A) in
/-- **The public structure presheaf** of `Spa (A, A⁺)` (Wedhorn §8.1; Kedlaya
Definition 1.2.3): the functor sending an open `V` to the projective-limit value
`𝒪_X(V) = lim_{R(T/s) ⊆ V} A⟨T/s⟩` (`limitSections V`, a complete separated
topological ring with the projective-limit topology) and an inclusion `W ≤ V` to the
continuous reindexing restriction `limitRestrict`. Functoriality is definitional.

This **replaces** the earlier discrete locally-fraction placeholder (now
`locallyFractionPresheaf`, quarantined in `StructureSheaf.lean`): the values on
rational opens are canonically the completed rational localizations
(`limitEval : limitSections (spaOpens D) ≃+* presheafValue D`, a homeomorphism), and
no discrete topology appears anywhere. -/
def structurePresheaf : TopCat.Presheaf CompleteTopCommRingCat.{u} (SpaTop A) where
  obj V := CompleteTopCommRingCat.of ↥(limitSections (A := A) V.unop)
  map {V W} i := ⟨limitRestrict (leOfHom i.unop), limitRestrict_continuous _⟩
  map_id V := by
    refine Subtype.ext (RingHom.ext fun x => Subtype.ext (funext fun i => ?_))
    rfl
  map_comp {U V W} i j := by
    refine Subtype.ext (RingHom.ext fun x => Subtype.ext (funext fun i => ?_))
    rfl

@[simp] theorem structurePresheaf_obj (V : (Opens ↥(SpaTop A))ᵒᵖ) :
    (structurePresheaf A).obj V = CompleteTopCommRingCat.of ↥(limitSections V.unop) :=
  rfl

theorem structurePresheaf_map {V W : (Opens ↥(SpaTop A))ᵒᵖ} (i : V ⟶ W)
    (x : ↥(limitSections V.unop)) :
    ((structurePresheaf A).map i).1 x = limitRestrict (leOfHom i.unop) x :=
  rfl

/-- On a rational open, the public structure presheaf takes the value `A⟨T/s⟩`
(Wedhorn (8.1.1); the comparison `limitEval` is a ring isomorphism and a
homeomorphism — `limitEval_continuous`, `limitEval_symm_continuous`). -/
theorem structurePresheaf_rational_value {D : RationalLocData A} (hD : D.IsRational) :
    ∃ e : ((structurePresheaf A).obj (Opposite.op (spaOpens D)) : Type u) ≃+*
        presheafValue D, Continuous e ∧ Continuous e.symm :=
  ⟨limitEval hD, limitEval_continuous hD, limitEval_symm_continuous hD⟩

/-! ### Composition collapse for `limitRestrict` (definitional reindexing) -/

theorem limitRestrict_limitRestrict {U V W : Opens ↥(Spa A A⁺)} (h₁ : W ≤ V)
    (h₂ : V ≤ U) (x : ↥(limitSections U)) :
    limitRestrict h₁ (limitRestrict h₂ x) = limitRestrict (h₁.trans h₂) x :=
  rfl

theorem limitRestrict_self {V : Opens ↥(Spa A A⁺)} (h : V ≤ V)
    (x : ↥(limitSections V)) : limitRestrict h x = x :=
  rfl

/-! ### Universe reduction for covers (WO1 task 8)

The `IsLimitSheaf` fields quantify covers over `ι : Type u`. Arbitrary index types
factor through the **range family** `{W : Opens ↥(Spa A A⁺) // ∃ i, U i = W}` (which
lives in `Type u`), with the tautological index `⟨U i, ⟨i, rfl⟩⟩` giving cast-free
transport. Hence the universe restriction does not weaken the sheaf property. -/

namespace IsLimitSheaf

variable {ι : Type v} {V : Opens ↥(Spa A A⁺)} {U : ι → Opens ↥(Spa A A⁺)}

/-- The range family of a cover: its members, as a `Type u` index. -/
private def RangeIndex (U : ι → Opens ↥(Spa A A⁺)) : Type u :=
  {W : Opens ↥(Spa A A⁺) // ∃ i, U i = W}

/-- Separation for covers indexed in an arbitrary universe. -/
theorem injective' (h : IsLimitSheaf A) (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    {x y : ↥(limitSections V)}
    (hxy : ∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) : x = y := by
  have hle' : ∀ W : RangeIndex U, W.1 ≤ V := by
    rintro ⟨W, i, rfl⟩; exact hle i
  have hcov' : (V : Set ↥(Spa A A⁺)) ⊆
      ⋃ W : RangeIndex U, ((W.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) := by
    intro v hv
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcov hv)
    exact Set.mem_iUnion.mpr ⟨⟨U i, i, rfl⟩, hvi⟩
  refine h.injective (U := fun W : RangeIndex U => W.1) hle' hcov' ?_
  rintro ⟨W, i, rfl⟩
  exact hxy i

/-- **Well-definedness core for gluing**: on two cover members that refine each
other, the section at one restricts to the section at the other. -/
private theorem limitRestrict_eq_of_le
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j))
    (i j : ι) (hUij : U i ≤ U j) :
    limitRestrict hUij (s j) = s i := by
  have h₁ : U i ≤ U i ⊓ U j := le_inf le_rfl hUij
  calc limitRestrict hUij (s j)
      = limitRestrict h₁ (limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) :=
        (limitRestrict_limitRestrict h₁ inf_le_right (s j)).symm
    _ = limitRestrict h₁ (limitRestrict (inf_le_left (a := U i) (b := U j)) (s i)) := by
        rw [hs i j]
    _ = limitRestrict (h₁.trans inf_le_left) (s i) :=
        limitRestrict_limitRestrict h₁ inf_le_left (s i)
    _ = s i := limitRestrict_self _ (s i)

/-- Gluing for covers indexed in an arbitrary universe. -/
theorem glue' (h : IsLimitSheaf A) (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (s : ∀ i, ↥(limitSections (U i)))
    (hs : ∀ i j, limitRestrict (inf_le_left (a := U i) (b := U j)) (s i) =
                 limitRestrict (inf_le_right (a := U i) (b := U j)) (s j)) :
    ∃ x : ↥(limitSections V), ∀ i, limitRestrict (hle i) x = s i := by
  classical
  -- the well-definedness core: sections at equal cover members agree after
  -- restriction along the equality
  have hkey : ∀ (i j : ι) (hUij : U i ≤ U j), U j ≤ U i →
      limitRestrict hUij (s j) = s i :=
    fun i j hUij _ => limitRestrict_eq_of_le s hs i j hUij
  have hle' : ∀ W : RangeIndex U, W.1 ≤ V := by
    rintro ⟨W, i, rfl⟩; exact hle i
  have hcov' : (V : Set ↥(Spa A A⁺)) ⊆
      ⋃ W : RangeIndex U, ((W.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) := by
    intro v hv
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcov hv)
    exact Set.mem_iUnion.mpr ⟨⟨U i, i, rfl⟩, hvi⟩
  -- transported family on the range: restrict the section at a chosen preimage
  -- along the (propositional) equality, cast-free
  set s' : ∀ W : RangeIndex U, ↥(limitSections W.1) := fun W =>
    limitRestrict W.2.choose_spec.ge (s W.2.choose) with hs'def
  have hs'val : ∀ (W : RangeIndex U) (i : ι), U i = W.1 →
      ∀ h : W.1 ≤ U i, limitRestrict h (s i) = s' W := by
    intro W i h hWi
    have hji : U W.2.choose ≤ U i := (W.2.choose_spec.trans h.symm).le
    have hij : U i ≤ U W.2.choose := (h.trans W.2.choose_spec.symm).le
    rw [hs'def]
    have hcollapse : limitRestrict hij (s W.2.choose) = s i :=
      hkey i W.2.choose hij hji
    rw [← hcollapse, limitRestrict_limitRestrict]
  have hs' : ∀ W₁ W₂ : RangeIndex U,
      limitRestrict (inf_le_left (a := W₁.1) (b := W₂.1)) (s' W₁) =
      limitRestrict (inf_le_right (a := W₁.1) (b := W₂.1)) (s' W₂) := by
    intro W₁ W₂
    obtain ⟨i₁, hi₁⟩ := W₁.2
    obtain ⟨i₂, hi₂⟩ := W₂.2
    rw [← hs'val W₁ i₁ hi₁ hi₁.ge, ← hs'val W₂ i₂ hi₂ hi₂.ge,
      limitRestrict_limitRestrict, limitRestrict_limitRestrict]
    have h₁ : W₁.1 ⊓ W₂.1 ≤ U i₁ ⊓ U i₂ := by rw [hi₁, hi₂]
    calc limitRestrict ((inf_le_left (a := W₁.1) (b := W₂.1)).trans hi₁.ge) (s i₁)
        = limitRestrict h₁
            (limitRestrict (inf_le_left (a := U i₁) (b := U i₂)) (s i₁)) :=
          (limitRestrict_limitRestrict h₁ inf_le_left (s i₁)).symm
      _ = limitRestrict h₁
            (limitRestrict (inf_le_right (a := U i₁) (b := U i₂)) (s i₂)) := by
          rw [hs i₁ i₂]
      _ = limitRestrict ((inf_le_right (a := W₁.1) (b := W₂.1)).trans hi₂.ge) (s i₂) :=
          limitRestrict_limitRestrict h₁ inf_le_right (s i₂)
  obtain ⟨x, hx⟩ := h.glue (U := fun W : RangeIndex U => W.1) hle' hcov' s' hs'
  refine ⟨x, fun i => ?_⟩
  have hxi := hx ⟨U i, ⟨i, rfl⟩⟩
  rw [← hs'val ⟨U i, ⟨i, rfl⟩⟩ i rfl le_rfl] at hxi
  exact hxi

/-- The topological-embedding condition for covers indexed in an arbitrary
universe. -/
theorem isEmbedding' (h : IsLimitSheaf A) (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺))) :
    Topology.IsEmbedding (limitRestrictProd hle) := by
  have hle' : ∀ W : RangeIndex U, W.1 ≤ V := by
    rintro ⟨W, i, rfl⟩; exact hle i
  have hcov' : (V : Set ↥(Spa A A⁺)) ⊆
      ⋃ W : RangeIndex U, ((W.1 : Opens ↥(Spa A A⁺)) : Set ↥(Spa A A⁺)) := by
    intro v hv
    obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcov hv)
    exact Set.mem_iUnion.mpr ⟨⟨U i, i, rfl⟩, hvi⟩
  have hemb' := h.isEmbedding (U := fun W : RangeIndex U => W.1) hle' hcov'
  -- reindex the target product along the surjection ι → RangeIndex U
  set π : ι → RangeIndex U := fun i => ⟨U i, ⟨i, rfl⟩⟩ with hπdef
  have hπ : Function.Surjective π := by
    rintro ⟨W, i, rfl⟩; exact ⟨i, rfl⟩
  set φ : (∀ W : RangeIndex U, ↥(limitSections W.1)) →
      (∀ i, ↥(limitSections (U i))) := fun y i => y (π i) with hφdef
  have hfac : limitRestrictProd hle = φ ∘ limitRestrictProd hle' := rfl
  have hφinj : Function.Injective φ := by
    intro y₁ y₂ h12
    funext W
    obtain ⟨i, rfl⟩ := hπ W
    exact congr_fun h12 i
  have hφind : Topology.IsInducing φ := by
    refine Topology.isInducing_iff_nhds.mpr fun y => ?_
    rw [nhds_pi, nhds_pi, Filter.pi, Filter.pi, Filter.comap_iInf]
    simp only [Filter.comap_comap]
    exact (hπ.iInf_congr _ fun i => rfl).symm
  rw [hfac]
  exact ⟨hφind.comp hemb'.isInducing, hφinj.comp hemb'.injective⟩

end IsLimitSheaf

/-! ### Wedhorn Remark 8.20: the representable sheaf condition -/

variable (A) in
/-- **"`𝒪_X` is a sheaf of topological rings"** in Wedhorn's sense (Remark 8.20,
first form): for **every** topological commutative ring `T` — with no completeness,
separation, or discreteness restriction — the presheaf `V ↦ Hom_cont(T, 𝒪_X(V))` of
continuous ring homomorphisms is a sheaf of sets: every family of continuous ring
homomorphisms into the members of an open cover that is compatible on pairwise
intersections arises from a **unique** continuous ring homomorphism into `𝒪_X(V)`.

**DEPRECATION NOTE (P0.4, 2026-07-20)**: this Spa-specific formulation is
superseded by the generic `TopCat.Presheaf.IsSheafOfTopologicalRings` at
`structurePresheaf A` — the two are equivalent by
`structurePresheaf_isSheafOfTopologicalRings_iff` +
`isSheafOfTopologicalRings_iff_isLimitSheaf`. New statements should use the
generic predicate; this one remains for the equivalence theorems and existing
consumers. -/
def IsSheafOfTopologicalRings : Prop :=
  ∀ (T : Type u) [CommRing T] [TopologicalSpace T] [IsTopologicalRing T],
    ∀ {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
      (hle : ∀ i, U i ≤ V)
      (_ : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
      (f : ∀ i, T →+* ↥(limitSections (U i))), (∀ i, Continuous (f i)) →
      (∀ i j, (limitRestrict (inf_le_left (a := U i) (b := U j))).comp (f i) =
              (limitRestrict (inf_le_right (a := U i) (b := U j))).comp (f j)) →
      ∃! g : {g : T →+* ↥(limitSections V) // Continuous g},
        ∀ i, (limitRestrict (hle i)).comp g.1 = f i

section HomSheafCore

variable {T : Type u} [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]

omit [IsTopologicalRing T] in
/-- **The `Hom`-gluing core** (the substantive half of Wedhorn Remark 8.20's "⟸"):
under `IsLimitSheaf A`, compatible families of continuous ring homomorphisms glue
uniquely. Pointwise gluing gives the function; separation gives additivity,
multiplicativity, and uniqueness; the arbitrary-cover embedding condition gives
continuity (`IsInducing.continuous_iff` along `limitRestrictProd`). -/
theorem IsLimitSheaf.homGlue (h : IsLimitSheaf A)
    {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    (f : ∀ i, T →+* ↥(limitSections (U i))) (hfc : ∀ i, Continuous (f i))
    (hcompat : ∀ i j, (limitRestrict (inf_le_left (a := U i) (b := U j))).comp (f i) =
        (limitRestrict (inf_le_right (a := U i) (b := U j))).comp (f j)) :
    ∃! g : {g : T →+* ↥(limitSections V) // Continuous g},
      ∀ i, (limitRestrict (hle i)).comp g.1 = f i := by
  classical
  -- pointwise gluing
  have hglue : ∀ t : T, ∃ x : ↥(limitSections V),
      ∀ i, limitRestrict (hle i) x = f i t := by
    intro t
    exact h.glue hle hcov (fun i => f i t)
      (fun i j => DFunLike.congr_fun (hcompat i j) t)
  choose g₀ hg₀ using hglue
  -- separation-driven ring-hom structure
  have huniq : ∀ (x y : ↥(limitSections V)),
      (∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) → x = y :=
    fun x y hxy => h.injective hle hcov hxy
  have hg_add : ∀ t₁ t₂, g₀ (t₁ + t₂) = g₀ t₁ + g₀ t₂ := by
    intro t₁ t₂
    refine huniq _ _ fun i => ?_
    rw [hg₀ (t₁ + t₂) i, map_add, map_add, hg₀ t₁ i, hg₀ t₂ i]
  have hg_mul : ∀ t₁ t₂, g₀ (t₁ * t₂) = g₀ t₁ * g₀ t₂ := by
    intro t₁ t₂
    refine huniq _ _ fun i => ?_
    rw [hg₀ (t₁ * t₂) i, map_mul, map_mul, hg₀ t₁ i, hg₀ t₂ i]
  have hg_one : g₀ 1 = 1 := by
    refine huniq _ _ fun i => ?_
    rw [hg₀ 1 i, map_one, map_one]
  have hg_zero : g₀ 0 = 0 := by
    refine huniq _ _ fun i => ?_
    rw [hg₀ 0 i, map_zero, map_zero]
  set g : T →+* ↥(limitSections V) :=
    { toFun := g₀, map_one' := hg_one, map_mul' := hg_mul,
      map_zero' := hg_zero, map_add' := hg_add } with hgdef
  -- continuity through the arbitrary-cover embedding
  have hgc : Continuous g := by
    rw [(h.isEmbedding hle hcov).isInducing.continuous_iff]
    have : limitRestrictProd hle ∘ g = fun t i => f i t := by
      funext t i
      exact hg₀ t i
    rw [this]
    exact continuous_pi fun i => (hfc i)
  refine ⟨⟨g, hgc⟩, fun i => RingHom.ext fun t => hg₀ t i, ?_⟩
  rintro ⟨g', hg'c⟩ hg'
  refine Subtype.ext (RingHom.ext fun t => ?_)
  refine huniq _ _ fun i => ?_
  exact (DFunLike.congr_fun (hg' i) t).trans (hg₀ t i).symm

/-! #### Discrete polynomial probes (elements as homomorphisms)

An element `x` of a topological ring `R` is the image of `X` under the evaluation
homomorphism from the **discrete** polynomial ring `ULift ℤ[X]`; homomorphisms from
a discrete ring are automatically continuous, and two such homomorphisms agree iff
they agree at `X`. This encodes the element-level (ring-presheaf) sheaf axioms into
the representable condition. -/

/-- The discrete polynomial test ring, in the working universe. -/
private abbrev PolyProbe : Type u := ULift.{u} (Polynomial ℤ)

private instance : TopologicalSpace PolyProbe := ⊥
private instance : DiscreteTopology PolyProbe := ⟨rfl⟩
private instance : IsTopologicalRing PolyProbe where
  continuous_add := continuous_of_discreteTopology
  continuous_mul := continuous_of_discreteTopology
  continuous_neg := continuous_of_discreteTopology

/-- The lift `ℤ[X] →+* ULift ℤ[X]`, pinned at the working universe. -/
private def polyProbeUp : Polynomial ℤ →+* PolyProbe :=
  ((ULift.ringEquiv (R := Polynomial ℤ)).symm :
    Polynomial ℤ ≃+* ULift.{u} (Polynomial ℤ)).toRingHom

@[simp] private theorem polyProbeUp_apply (p : Polynomial ℤ) :
    polyProbeUp p = ULift.up p := rfl

/-- Evaluation at an element, as a homomorphism from the discrete polynomial ring. -/
private def polyProbeEval {R : Type u} [CommRing R] (x : R) : PolyProbe →+* R :=
  (Polynomial.eval₂RingHom (Int.castRingHom R) x).comp
    ((ULift.ringEquiv (R := Polynomial ℤ)) :
      ULift.{u} (Polynomial ℤ) ≃+* Polynomial ℤ).toRingHom

@[simp] private theorem polyProbeEval_X {R : Type u} [CommRing R] (x : R) :
    polyProbeEval x (ULift.up Polynomial.X) = x := by
  simp [polyProbeEval, ULift.ringEquiv]

private theorem polyProbe_hom_ext {R : Type u} [CommRing R]
    {f g : PolyProbe →+* R} (h : f (ULift.up Polynomial.X) = g (ULift.up Polynomial.X)) :
    f = g := by
  have hfg : f.comp polyProbeUp = g.comp polyProbeUp := by
    refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
    rw [RingHom.comp_apply, RingHom.comp_apply, polyProbeUp_apply]
    exact h
  refine DFunLike.ext f g fun p => ?_
  have hp : p = polyProbeUp p.down := rfl
  rw [hp]
  exact DFunLike.congr_fun hfg p.down

private theorem polyProbeEval_comp {R S : Type u} [CommRing R] [CommRing S]
    (φ : R →+* S) (x : R) :
    φ.comp (polyProbeEval x) = polyProbeEval (φ x) := by
  refine polyProbe_hom_ext ?_
  rw [RingHom.comp_apply, polyProbeEval_X, polyProbeEval_X]

end HomSheafCore

/-- The topology on `𝒪_X(V)` induced from the cover product — the test topology of
Wedhorn Remark 8.20's embedding direction. A plain definition (deliberately **not** a
local hypothesis or instance, so it never shadows the projective-limit instance
during elaboration). -/
private def inducedLimitTopology {V : Opens ↥(Spa A A⁺)} {ι : Type u}
    {U : ι → Opens ↥(Spa A A⁺)} (hle : ∀ i, U i ≤ V) :
    TopologicalSpace ↥(limitSections V) :=
  TopologicalSpace.induced (limitRestrictProd hle) inferInstance

/-- **Element-level separation from the bundled sheaf condition**: two sections that
agree on a cover are equal, obtained by probing with the discrete polynomial test
object and reading off the coefficient of `X`. -/
private theorem isLimitSheaf_separation_of_sheaf (hsheaf : IsSheafOfTopologicalRings A)
    {V : Opens ↥(Spa A A⁺)} {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)}
    (hle : ∀ i, U i ≤ V)
    (hcov : (V : Set ↥(Spa A A⁺)) ⊆ ⋃ i, (U i : Set ↥(Spa A A⁺)))
    {x y : ↥(limitSections V)}
    (hxy : ∀ i, limitRestrict (hle i) x = limitRestrict (hle i) y) : x = y := by
  -- both element probes glue the same compatible family
  obtain ⟨g, -, hguniq⟩ := hsheaf PolyProbe hle hcov
    (fun i => polyProbeEval (limitRestrict (hle i) x))
    (fun i => continuous_of_discreteTopology)
    (fun i j => by
      rw [polyProbeEval_comp, polyProbeEval_comp, limitRestrict_limitRestrict,
        limitRestrict_limitRestrict])
  have hx := hguniq ⟨polyProbeEval x, continuous_of_discreteTopology⟩
    (fun i => polyProbeEval_comp (limitRestrict (hle i)) x)
  have hy := hguniq ⟨polyProbeEval y, continuous_of_discreteTopology⟩
    (fun i => by rw [polyProbeEval_comp, hxy i])
  have hkey : polyProbeEval (R := ↥(limitSections V)) x = polyProbeEval y := by
    have := hx.trans hy.symm
    exact congrArg Subtype.val this
  calc x = polyProbeEval (R := ↥(limitSections V)) x (ULift.up Polynomial.X) :=
        (polyProbeEval_X x).symm
    _ = polyProbeEval (R := ↥(limitSections V)) y (ULift.up Polynomial.X) := by
        rw [hkey]
    _ = y := polyProbeEval_X y

/-- The topology induced on `limitSections V` by the restriction maps to a cover is a
ring topology: the inducing map is a ring homomorphism in each component, so `+`, `*`
and `-` all factor through it. No sheaf hypothesis is involved. -/
private theorem isTopologicalRing_inducedLimitTopology {V : Opens ↥(Spa A A⁺)}
    {ι : Type u} {U : ι → Opens ↥(Spa A A⁺)} (hle : ∀ i, U i ≤ V) :
    @IsTopologicalRing ↥(limitSections V) (inducedLimitTopology hle) _ := by
  have hcontProd : Continuous[inducedLimitTopology hle, _] (limitRestrictProd hle) :=
    continuous_induced_dom
  letI := inducedLimitTopology hle
  have hadd : (limitRestrictProd hle) ∘
      (fun p : ↥(limitSections V) × ↥(limitSections V) => p.1 + p.2) =
      fun p => limitRestrictProd hle p.1 + limitRestrictProd hle p.2 := by
    funext p
    funext i
    exact map_add (limitRestrict (hle i)) p.1 p.2
  have hmul : (limitRestrictProd hle) ∘
      (fun p : ↥(limitSections V) × ↥(limitSections V) => p.1 * p.2) =
      fun p => limitRestrictProd hle p.1 * limitRestrictProd hle p.2 := by
    funext p
    funext i
    exact map_mul (limitRestrict (hle i)) p.1 p.2
  have hneg : (limitRestrictProd hle) ∘
      (fun z : ↥(limitSections V) => -z) =
      fun z => -(limitRestrictProd hle z) := by
    funext z
    funext i
    exact map_neg (limitRestrict (hle i)) z
  refine { continuous_add := ?_, continuous_mul := ?_, continuous_neg := ?_ }
  · refine continuous_induced_rng.mpr ?_
    rw [hadd]
    exact (hcontProd.comp continuous_fst).add (hcontProd.comp continuous_snd)
  · refine continuous_induced_rng.mpr ?_
    rw [hmul]
    exact (hcontProd.comp continuous_fst).mul (hcontProd.comp continuous_snd)
  · refine continuous_induced_rng.mpr ?_
    rw [hneg]
    exact hcontProd.neg


/-- **Wedhorn Remark 8.20** for the all-open structure presheaf: the representable
condition ("for every topological ring `T`, `Hom(T, 𝒪_X(−))` is a sheaf of sets") is
equivalent to the concrete pair (ring-sheaf axioms) + (topological embedding into the
cover product), i.e. to `IsLimitSheaf`.

`⟸` is `IsLimitSheaf.homGlue`. For `⟹`: the element-level axioms are recovered by
testing along the discrete polynomial ring `ULift ℤ[X]` (an element is the image of
`X`; homomorphisms from a discrete ring are continuous); the embedding condition is
recovered by testing along `𝒪_X(V)` itself re-topologized with the topology induced
from `∏ᵢ 𝒪_X(Uᵢ)` — the glued homomorphism against the identity's restriction family
is the identity (by uniqueness), which is exactly continuity of
`(𝒪_X(V), induced) → (𝒪_X(V), projective)`. -/
theorem isSheafOfTopologicalRings_iff_isLimitSheaf :
    IsSheafOfTopologicalRings A ↔ IsLimitSheaf A := by
  constructor
  · intro hsheaf
    -- element-level separation, via the discrete polynomial probe
    refine ⟨fun hle hcov => isLimitSheaf_separation_of_sheaf hsheaf hle hcov, ?_, ?_⟩
    · -- element-level gluing, via the discrete polynomial probe
      intro V ι U hle hcov s hs
      obtain ⟨g, hg, -⟩ := hsheaf PolyProbe hle hcov
        (fun i => polyProbeEval (s i))
        (fun i => continuous_of_discreteTopology)
        (fun i j => by rw [polyProbeEval_comp, polyProbeEval_comp, hs i j])
      refine ⟨g.1 (ULift.up Polynomial.X), fun i => ?_⟩
      calc limitRestrict (hle i) (g.1 (ULift.up Polynomial.X))
          = ((limitRestrict (hle i)).comp g.1) (ULift.up Polynomial.X) := rfl
        _ = polyProbeEval (s i) (ULift.up Polynomial.X) := by rw [hg i]
        _ = s i := polyProbeEval_X (s i)
    · -- the embedding condition, via the induced-topology test object
      intro V ι U hle hcov
      have hcontProd : Continuous[inducedLimitTopology hle, _] (limitRestrictProd hle) :=
        continuous_induced_dom
      -- the induced topology is a ring topology (the target is a topological ring
      -- and the inducing map is a ring homomorphism component-wise)
      have σring := isTopologicalRing_inducedLimitTopology hle
      -- restriction homomorphisms are continuous from the induced topology
      have hfc : ∀ i, Continuous[inducedLimitTopology hle, _] (limitRestrict (hle i)) :=
        fun i => @Continuous.comp ↥(limitSections V) (∀ j, ↥(limitSections (U j)))
          ↥(limitSections (U i)) (inducedLimitTopology hle) _ _ _ _
          (continuous_apply i) hcontProd
      -- glue the identity restriction family against the induced-topology test object
      obtain ⟨g, hg, -⟩ := @hsheaf ↥(limitSections V) _ (inducedLimitTopology hle)
        σring V ι U hle hcov (fun i => limitRestrict (hle i)) hfc
        (fun i j => by rw [limitRestrict_comp, limitRestrict_comp])
      -- the glued homomorphism is the identity, by element-level separation
      have hgid : ∀ z, g.1 z = z := by
        intro z
        refine isLimitSheaf_separation_of_sheaf hsheaf hle hcov fun i => ?_
        exact DFunLike.congr_fun (hg i) z
      -- hence the identity is continuous from the induced topology to the
      -- projective-limit topology, which forces the two to agree
      have hστ : inducedLimitTopology hle ≤
          (instTopologicalSpaceSubtype : TopologicalSpace ↥(limitSections V)) := by
        have hgeq : (g.1 : ↥(limitSections V) → ↥(limitSections V)) = id := funext hgid
        have hcont := g.2
        rw [hgeq] at hcont
        exact continuous_id_iff_le.mp hcont
      have hind : Topology.IsInducing (limitRestrictProd hle) := by
        refine ⟨le_antisymm ?_ hστ⟩
        exact continuous_iff_le_induced.mp
          (continuous_pi fun i => limitRestrict_continuous (hle i))
      exact ⟨hind, fun x y hxy =>
        isLimitSheaf_separation_of_sheaf hsheaf hle hcov fun i => congr_fun hxy i⟩
  · intro hlimit T _ _ _ V ι U hle hcov f hfc hcompat
    exact hlimit.homGlue hle hcov f hfc hcompat

/-! ### The categorical sheaf condition and the public sheaf object

Mathlib's sheaf condition for a presheaf valued in a general category
([Stacks 00VR]) is: for every object `E`, the type-valued presheaf
`V ↦ Hom(E, F(V))` is a sheaf of sets — the same shape as Wedhorn Remark 8.20,
tested along the objects of `CompleteTopCommRingCat`. Since
`IsSheafOfTopologicalRings` quantifies over **all** topological commutative rings,
it implies the categorical condition (restriction of the test class); we derive the
categorical sheaf property from `IsLimitSheaf` directly through `homGlue`. -/

variable (A) in
/-- Under pair-level sheafiness (`IsLimitSheaf`), the bundled public structure
presheaf satisfies mathlib's categorical sheaf condition. -/
theorem structurePresheaf_isSheaf (h : IsLimitSheaf A) :
    (structurePresheaf A).IsSheaf := by
  intro E
  rw [← CategoryTheory.isSheaf_iff_isSheaf_of_type]
  refine (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing_types _).mpr ?_
  intro ι U sf hsf
  have hle : ∀ i, U i ≤ iSup U := fun i => le_iSup U i
  have hcov : ((iSup U : Opens ↥(SpaTop A)) : Set ↥(SpaTop A)) ⊆
      ⋃ i, ((U i : Opens ↥(SpaTop A)) : Set ↥(SpaTop A)) := by
    intro v hv
    obtain ⟨i, hvi⟩ := Opens.mem_iSup.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hvi⟩
  obtain ⟨g, hg, hguniq⟩ := h.homGlue (T := E.α) hle hcov
    (fun i => (sf i).1) (fun i => (sf i).2)
    (fun i j => congrArg Subtype.val (hsf i j))
  refine ⟨g, fun i => Subtype.ext (hg i), fun s' hs' => ?_⟩
  exact hguniq s' fun i => congrArg Subtype.val (hs' i)

variable (A) in
/-- **The public structure sheaf** of `Spa (A, A⁺)` for a sheafy complete Tate pair:
the bundled projective-limit presheaf together with its categorical sheaf property
(from the finite rational criterion via `isLimitSheaf_of_isSheafy`). -/
def structureSheaf [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] [IsSheafy A] :
    TopCat.Sheaf CompleteTopCommRingCat.{u} (SpaTop A) :=
  ⟨structurePresheaf A, structurePresheaf_isSheaf A isLimitSheaf_of_isSheafy⟩


variable (A) in
/-- **The generic Hom-sheaf predicate specializes to the public structure
presheaf**: under pair-level sheafiness, `structurePresheaf A` satisfies the
arbitrary-presheaf sheaf-of-topological-rings condition of
`HomSheafPredicate.lean` (hence in particular the categorical conditions for both
the bundled and the underlying ring presheaf). -/
theorem structurePresheaf_isSheafOfTopologicalRings (h : IsLimitSheaf A) :
    TopCat.Presheaf.IsSheafOfTopologicalRings (structurePresheaf A) := by
  intro T _ _ _ ι U f hcompat
  have hle : ∀ i, U i ≤ iSup U := fun i => le_iSup U i
  have hcov : ((iSup U : Opens ↥(SpaTop A)) : Set ↥(SpaTop A)) ⊆
      ⋃ i, ((U i : Opens ↥(SpaTop A)) : Set ↥(SpaTop A)) := by
    intro v hv
    obtain ⟨i, hvi⟩ := Opens.mem_iSup.mp hv
    exact Set.mem_iUnion.mpr ⟨i, hvi⟩
  obtain ⟨g, hg, hguniq⟩ := h.homGlue (T := T) hle hcov
    (fun i => (f i).1) (fun i => (f i).2) hcompat
  exact ⟨g, hg, fun g' hg' => hguniq g' hg'⟩


variable (A) in
/-- **The generic predicate specializes exactly** (P0.4): the bundled public
structure presheaf satisfies the arbitrary-presheaf sheaf-of-topological-rings
condition iff the pair is sheafy (`IsLimitSheaf`). The forward direction
transports a general-`V` cover to the `iSup`-form through the open-equality
reindexing (`limitRestrict` along `V = iSup U`, mutually inverse by
reindexing-`rfl`), then runs the Spa-specific Remark-8.20 argument. -/
theorem structurePresheaf_isSheafOfTopologicalRings_iff :
    TopCat.Presheaf.IsSheafOfTopologicalRings (structurePresheaf A) ↔
      IsLimitSheaf A := by
  constructor
  · intro hgen
    refine (isSheafOfTopologicalRings_iff_isLimitSheaf).mp ?_
    intro T instC instTop instRing V ι U hle hcov f hfc hcompat
    -- the cover forces `V = iSup U`
    have hVeq : V = iSup U := by
      refine le_antisymm ?_ (iSup_le hle)
      intro v hv
      obtain ⟨i, hvi⟩ := Set.mem_iUnion.mp (hcov hv)
      exact Opens.mem_iSup.mpr ⟨i, hvi⟩
    -- run the generic condition at the `iSup` cover, then reinterpret the
    -- entire unique-gluing datum on the concrete (subring) side in ONE defeq step
    obtain ⟨gPair, hgPair, hgPairUniq⟩ :
        ∃! g : {g : T →+* ↥(limitSections (iSup U)) // Continuous g},
          ∀ i, (limitRestrict (le_iSup U i)).comp g.1 = f i :=
      hgen T instC instTop instRing U
        (fun i => ⟨f i, hfc i⟩) (fun i j => hcompat i j)
    obtain ⟨g₀, hg₀c⟩ := gPair
    -- transport the glued hom along the open equality (note `limitRestrict` is
    -- contravariant: `limitRestrict (V ≤ iSup U)` maps `iSup`-sections to `V`-sections)
    refine ⟨⟨(limitRestrict hVeq.le).comp g₀, ?_⟩, fun i => ?_, ?_⟩
    · exact (limitRestrict_continuous hVeq.le).comp hg₀c
    · -- restriction check: collapse the reindexings
      refine RingHom.ext fun t => ?_
      show limitRestrict (hle i) (limitRestrict hVeq.le (g₀ t)) = f i t
      rw [limitRestrict_limitRestrict]
      exact DFunLike.congr_fun (hgPair i) t
    · rintro ⟨g', hg'c⟩ hg'
      -- the reverse transport of `g'` also glues at `iSup U`, hence equals `g₀`
      have huniq := hgPairUniq ⟨(limitRestrict hVeq.ge).comp g',
        (limitRestrict_continuous hVeq.ge).comp hg'c⟩ (fun i => by
          refine RingHom.ext fun t => ?_
          show limitRestrict (le_iSup U i) (limitRestrict hVeq.ge (g' t)) = f i t
          rw [limitRestrict_limitRestrict]
          exact DFunLike.congr_fun (hg' i) t)
      refine Subtype.ext (RingHom.ext fun t => ?_)
      have hval := congrArg Subtype.val huniq
      have hstep := congr_fun (congrArg (fun z : T →+* ↥(limitSections (iSup U)) =>
        (fun t => limitRestrict hVeq.le (z t))) hval) t
      show g' t = limitRestrict hVeq.le (g₀ t)
      calc g' t = limitRestrict hVeq.le (limitRestrict hVeq.ge (g' t)) := rfl
        _ = limitRestrict hVeq.le (g₀ t) := hstep
  · exact structurePresheaf_isSheafOfTopologicalRings A

variable (A) in
/-- **The standard formulation, over `TopCommRingCat`**: the public structure
presheaf, pushed along the forgetful functor into the category of plain topological
commutative rings, satisfies mathlib's categorical sheaf condition **iff** the pair
is sheafy. The categorical condition tests `Hom(E, −)`-gluing along the objects of
the value category; over `TopCommRingCat` those are exactly Wedhorn's arbitrary
topological test rings (Remark 8.20), so — unlike the `CompleteTopCommRingCat`-valued
condition, where only the forward implication `structurePresheaf_isSheaf` is
available — this is an equivalence. -/
theorem structurePresheaf_forgetToTopCommRingCat_isSheaf_iff :
    TopCat.Presheaf.IsSheaf
        (structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToTopCommRingCat) ↔
      IsLimitSheaf A :=
  (TopCat.Presheaf.isSheafOfTopologicalRings_iff_forgetToTopCommRingCat_isSheaf
        (structurePresheaf A)).symm.trans
    (structurePresheaf_isSheafOfTopologicalRings_iff A)

variable (A) in
/-- **The finite rational-cover criterion is exactly mathlib's sheaf condition over
`TopCommRingCat`** — the full chain endpoint
`IsSheafy ↔ IsLimitSheaf ↔ IsSheafOfTopologicalRings ↔ categorical IsSheaf`:
the project's rational-basis criterion `IsSheafy A` holds iff the bundled public
structure presheaf, viewed in `TopCommRingCat` through the forgetful functor,
satisfies mathlib's `IsSheaf`. -/
theorem isSheafy_iff_structurePresheaf_forgetToTopCommRingCat_isSheaf
    [DecidableEq A] [DecidableEq (RationalLocData A)] [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] [T2Space A] [NonarchimedeanRing A]
    [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A;
      CompleteSpace A] :
    IsSheafy A ↔
      TopCat.Presheaf.IsSheaf
        (structurePresheaf A ⋙ CompleteTopCommRingCat.forgetToTopCommRingCat) :=
  isSheafy_iff_isLimitSheaf.trans
    (structurePresheaf_forgetToTopCommRingCat_isSheaf_iff A).symm

/-! ### Affinoid and adic presentations (towards Definitions 8.21/8.22) -/

/-- **A presentation of an affinoid adic space** (honest naming, P5 repair
2026-07-20): a complete affinoid pair `(A, A⁺)` whose genuine all-open structure
presheaf is a sheaf of topological rings (the sheafiness field is Definition 8.26's
condition in the concrete `IsLimitSheaf` form, equivalent to the `Hom(T, 𝒪_X(−))`
form by `isSheafOfTopologicalRings_iff_isLimitSheaf`). Restriction maps are
constructed from the ring data (Proposition 8.2), not assumed separately.

**This is the ring/pair *presentation* only — it does not itself implement Wedhorn
Definition 8.21** (an affinoid adic space is an object of `𝒱` isomorphic *in `𝒱`*
to a `Spa`-object with its stalk valuations); constructing the canonical `𝒱`-object
of a presentation requires the stalk-valuation layer (Wedhorn Prop 8.6 for the
projective-limit presheaf), which is recorded as the open P5 leaf. -/
structure AffinoidAdicPresentation where
  /-- The underlying affinoid ring. -/
  Ring : Type u
  [instCommRing : CommRing Ring]
  [instTopologicalSpace : TopologicalSpace Ring]
  [instIsTopologicalRing : IsTopologicalRing Ring]
  [instPlusSubring : PlusSubring Ring]
  [instIsHuberRing : IsHuberRing Ring]
  [instT2Space : T2Space Ring]
  [instNonarchimedeanRing : NonarchimedeanRing Ring]
  [instCompleteSpace :
    letI : UniformSpace Ring := IsTopologicalAddGroup.rightUniformSpace Ring
    CompleteSpace Ring]
  [instIsRingOfIntegralElements : IsRingOfIntegralElements (Ring⁺)]
  /-- The structure presheaf is a sheaf of topological rings (Definition 8.26's
  condition for the pair, in the concrete all-open form). -/
  sheafy : IsLimitSheaf Ring

attribute [instance] AffinoidAdicPresentation.instCommRing
  AffinoidAdicPresentation.instTopologicalSpace AffinoidAdicPresentation.instIsTopologicalRing
  AffinoidAdicPresentation.instPlusSubring AffinoidAdicPresentation.instIsHuberRing
  AffinoidAdicPresentation.instT2Space AffinoidAdicPresentation.instNonarchimedeanRing
  AffinoidAdicPresentation.instCompleteSpace AffinoidAdicPresentation.instIsRingOfIntegralElements

namespace AffinoidAdicPresentation

variable (X : AffinoidAdicPresentation.{u})

/-- The underlying topological space of an affinoid adic space. -/
def toTopCat : TopCat.{u} := SpaTop X.Ring

/-- **The structure sheaf of an affinoid adic presentation** (Remark 8.20 of
Wedhorn): the genuine all-open projective-limit presheaf, a sheaf by the
presentation's own sheafiness field. Sorry-free; the former discrete
locally-fraction placeholder is not referenced. -/
noncomputable def sheaf : TopCat.Sheaf CompleteTopCommRingCat.{u} X.toTopCat :=
  ⟨structurePresheaf X.Ring, structurePresheaf_isSheaf X.Ring X.sheafy⟩

/-- Build an affinoid adic presentation from the finite rational-cover criterion
(`IsSheafy`, complete Tate scope), through the C5 equivalence
`isLimitSheaf_of_isSheafy`. -/
noncomputable def ofIsSheafy (R : Type u) [CommRing R] [TopologicalSpace R]
    [PlusSubring R] [IsTateRing R]
    [T2Space R] [NonarchimedeanRing R]
    [letI : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R;
      CompleteSpace R]
    [IsRingOfIntegralElements (R⁺ : Subring R)] [IsSheafy R] :
    AffinoidAdicPresentation.{u} :=
  letI : DecidableEq R := Classical.decEq R
  letI : DecidableEq (RationalLocData R) := Classical.decEq _
  { Ring := R
    sheafy := isLimitSheaf_of_isSheafy }

end AffinoidAdicPresentation

/-- **A carrier-level presentation of an adic space** (honest naming, P5 repair
2026-07-20): a topological space locally *homeomorphic* to the spectra of affinoid
adic presentations. **This does not itself implement Wedhorn Definition 8.22** —
an adic space is an object of `𝒱` locally `𝒱`-isomorphic to affinoid ones (the
local identifications must carry the structure sheaves and stalk valuations, not
only the topology); the `𝒱`-level definition awaits the canonical `Spa` object of
`𝒱` (the open P5 leaf). -/
structure AdicSpacePresentation where
  /-- The underlying topological space. -/
  carrier : Type u
  [instTopologicalSpace : TopologicalSpace carrier]
  /-- Every point has an open neighborhood homeomorphic to the spectrum of an
  affinoid adic presentation (a *topological* chart only). -/
  isLocallyAffinoid : ∀ x : carrier, ∃ (U : Opens carrier) (_ : x ∈ U)
    (X : AffinoidAdicPresentation.{u}), Nonempty (↥U ≃ₜ X.toTopCat)

attribute [instance] AdicSpacePresentation.instTopologicalSpace

end ValuationSpectrum
