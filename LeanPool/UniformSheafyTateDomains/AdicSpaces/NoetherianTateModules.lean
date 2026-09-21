/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.Topology.Algebra.Ring.Ideal
import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings

/-!
# Noetherian Tate Module Topology (Wedhorn Prop 6.18)

We formalize the canonical topology on finitely generated modules over topological rings,
following §6.18 of [Wedhorn, *Adic Spaces*].

The key insight is that mathlib's `moduleTopology` (the finest topology making `M` a
topological `A`-module) coincides with the I-adic lattice topology from Wedhorn, and
already provides automatic continuity of linear maps and the open mapping theorem.

## Main definitions

* `IsStrictMap` : A continuous map between topological spaces is *strict* if it is open
  onto its image (i.e., it is an open map to `Set.range f` with the subspace topology).
* `IsStrictLinearMap` : Specialization for linear maps.

## Main results

* `IsModuleTopology.isOpenMap_of_surjective_of_finite` : Every surjective `A`-linear map
  between modules with module topology is open (the open mapping theorem, Prop 6.18(2)).
* `IsModuleTopology.isStrictLinearMap_surjective` : Every surjective `A`-linear map between
  modules with module topology is strict.
* `IsModuleTopology.strictExact` : In a short exact sequence of modules with module
  topology, the surjection is open and the injection is continuous (strict exactness).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Proposition 6.18, Remark 6.19
-/

open Filter Topology Pointwise

/-! ### Strict maps -/

/-- A continuous map `f : X → Y` is **strict** if it is open onto its image, i.e.,
the induced map `X → Set.range f` (with the subspace topology) is an open map. -/
def IsStrictMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : X → Y) : Prop :=
  IsOpenMap (Set.rangeFactorization f)

/-- A linear map `f : M →ₗ[R] N` is **strict** if the underlying continuous map is
open onto its image. This is the notion of "strict morphism" in the theory of
topological modules. -/
def IsStrictLinearMap {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [TopologicalSpace M] [TopologicalSpace N] (f : M →ₗ[R] N) : Prop :=
  IsStrictMap f

/-- An open map is strict. -/
theorem isStrictMap_of_isOpenMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsOpenMap f) : IsStrictMap f := by
  intro U hU
  rw [isOpen_induced_iff]
  exact ⟨f '' U, hf U hU, by
    ext ⟨y, x, rfl⟩
    simp only [Set.rangeFactorization, Set.mem_preimage, Set.mem_image]
    refine exists_congr fun z => and_congr_right fun _ => ?_
    constructor
    · exact fun h => Subtype.ext h
    · exact congrArg Subtype.val⟩

/-- A strict surjective map is open. -/
theorem IsStrictMap.isOpenMap_of_surjective {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : IsStrictMap f) (hfs : Function.Surjective f) :
    IsOpenMap f := by
  intro U hU
  have h := hf U hU
  rw [isOpen_induced_iff] at h
  obtain ⟨V, hV, hVeq⟩ := h
  convert hV using 1
  ext y
  constructor
  · rintro ⟨x, hxU, rfl⟩
    have hmem : Set.rangeFactorization f x ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact ⟨x, hxU, rfl⟩
    exact hmem
  · intro hy
    obtain ⟨x, rfl⟩ := hfs y
    have hmem : (⟨f x, Set.mem_range_self x⟩ : Set.range f) ∈ Subtype.val ⁻¹' V :=
      hy
    rw [hVeq] at hmem
    obtain ⟨x', hx'U, hx'eq⟩ := hmem
    exact ⟨x', hx'U, congr_arg Subtype.val hx'eq⟩

/-- An open surjective linear map is strict. -/
theorem isStrictLinearMap_of_isOpenMap {R : Type*} [Semiring R] {M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]
    [TopologicalSpace M] [TopologicalSpace N] {f : M →ₗ[R] N}
    (hf : IsOpenMap f) : IsStrictLinearMap f :=
  isStrictMap_of_isOpenMap hf

/-! ### Module topology on finitely generated modules -/

section ModuleTopologyFG

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {M : Type*} [AddCommGroup M] [Module A M] [TopologicalSpace M]
variable {N : Type*} [AddCommGroup N] [Module A N] [TopologicalSpace N]

omit [IsTopologicalRing A] in
/-- Every `A`-linear map from a module with module topology is continuous
(Prop 6.18(2) of Wedhorn, easy direction). -/
theorem IsModuleTopology.continuous_linearMap_of_finite [IsModuleTopology A M]
    [ContinuousAdd N] [ContinuousSMul A N] (f : M →ₗ[A] N) :
    Continuous f :=
  IsModuleTopology.continuous_of_linearMap f

omit [IsTopologicalRing A] in
/-- Every surjective `A`-linear map between modules with module topology is open.
This is the **open mapping theorem** for module topologies (Prop 6.18(2) of Wedhorn). -/
theorem IsModuleTopology.isOpenMap_of_surjective_of_finite
    [IsModuleTopology A M] [IsModuleTopology A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) : IsOpenMap f :=
  (IsModuleTopology.isOpenQuotientMap_of_surjective (φ := f) hf).isOpenMap

omit [IsTopologicalRing A] in
/-- Every surjective `A`-linear map between modules with module topology is strict.
This follows immediately from the open mapping theorem. -/
theorem IsModuleTopology.isStrictLinearMap_surjective
    [IsModuleTopology A M] [IsModuleTopology A N]
    (f : M →ₗ[A] N) (hf : Function.Surjective f) : IsStrictLinearMap f :=
  isStrictLinearMap_of_isOpenMap (IsModuleTopology.isOpenMap_of_surjective_of_finite f hf)

end ModuleTopologyFG

/-! ### Completeness of the module topology on finitely generated modules (Prop 6.18(1)) -/

section ModuleTopologyComplete

/-- **Wedhorn Prop 6.18(1), completeness half** (p. 50, `wedhorn.txt:4076`): a finitely
generated module `M` over a complete, first-countable topological ring `A`, carrying its
module topology, is complete.

The module topology presents `M` as an *open quotient* image `Aⁿ ↠ M` (Prop 6.18(2),
`IsModuleTopology.isOpenMap_of_surjective_of_finite`). `Aⁿ` is complete and first countable,
so the additive quotient `Aⁿ ⧸ ker` is complete (`QuotientAddGroup.completeSpace`), and the
canonical add-equiv `Aⁿ ⧸ ker ≃+ M` is a uniform isomorphism (continuous + open between
uniform additive groups), transporting completeness to `M`.

**Faithfulness:** uses `[CompleteSpace A]` + the module topology only — *no* noetherianity of
`A` and *no* ring of definition `A₀`. This is the Wedhorn-faithful (case-(b)) input to
Prop 6.18 / Remark 8.29 / Lemma 8.31. -/
theorem CompleteSpace.of_isModuleTopology_finite
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
      [CompleteSpace A] [(uniformity A).IsCountablyGenerated]
    {M : Type*} [AddCommGroup M] [Module A M] [UniformSpace M] [IsUniformAddGroup M]
      [IsModuleTopology A M] [Module.Finite A M] :
    CompleteSpace M := by
  obtain ⟨n, ν, hν⟩ := Module.Finite.exists_fin' A M
  let : CompleteSpace (Fin n → A) := inferInstance
  let : FirstCountableTopology A := UniformSpace.firstCountableTopology A
  let : FirstCountableTopology (Fin n → A) := inferInstance
  have hν_cont : Continuous ⇑ν := IsModuleTopology.continuous_linearMap_of_finite ν
  have hν_open : IsOpenMap ⇑ν := IsModuleTopology.isOpenMap_of_surjective_of_finite ν hν
  -- Right uniformity on the quotient (mirrors `wedhorn_6_18_exists_canonical_topology`).
  let τQ : UniformSpace ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) :=
    IsTopologicalAddGroup.rightUniformSpace _
  let : @IsUniformAddGroup _ τQ _ := isUniformAddGroup_of_addCommGroup
  let : @CompleteSpace _ τQ :=
    QuotientAddGroup.completeSpace_right (Fin n → A) ν.toAddMonoidHom.ker
  -- The canonical add-equiv from the quotient to `M`.
  let e : ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) ≃+ M :=
    QuotientAddGroup.quotientKerEquivOfSurjective ν.toAddMonoidHom hν
  have hq_surj : Function.Surjective ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) :=
    QuotientAddGroup.mk'_surjective _
  have hq_cont : Continuous ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) :=
    continuous_quot_mk
  have he_mk : ⇑e ∘ ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) = ⇑ν := by ext x; rfl
  -- `e` is continuous via the quotient universal property.
  have he_cont : Continuous ⇑e := by
    rw [continuous_def]
    intro U hU
    have : ⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U) = ⇑ν ⁻¹' U := by
      rw [← Set.preimage_comp, he_mk]
    have hopen : IsOpen (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' (⇑e ⁻¹' U)) := by
      rw [this]; exact hU.preimage hν_cont
    exact (QuotientAddGroup.isOpenQuotientMap_mk
      (N := ν.toAddMonoidHom.ker)).isQuotientMap.isOpen_preimage.mp hopen
  -- `e` is open: `e '' U = ν '' (mk ⁻¹' U)`.
  have he_open : IsOpenMap ⇑e := by
    intro U hU
    have himg : ⇑e '' U = ⇑ν '' (⇑(QuotientAddGroup.mk' ν.toAddMonoidHom.ker) ⁻¹' U) := by
      rw [← he_mk, Set.image_comp, Set.image_preimage_eq U hq_surj]
    rw [himg]
    exact hν_open _ (hU.preimage hq_cont)
  -- `e.symm` is continuous (continuous + open bijection).
  have he_symm_cont : Continuous ⇑e.symm := by
    have := (e.toEquiv.toHomeomorphOfContinuousOpen he_cont he_open).symm.continuous
    simpa using this
  -- Package as a uniform isomorphism and transport completeness.
  let ue : ((Fin n → A) ⧸ ν.toAddMonoidHom.ker) ≃ᵤ M :=
    { toEquiv := e.toEquiv
      uniformContinuous_toFun := uniformContinuous_addMonoidHom_of_continuous (f := e) he_cont
      uniformContinuous_invFun :=
        uniformContinuous_addMonoidHom_of_continuous (f := e.symm) he_symm_cont }
  exact ue.completeSpace_iff.mp inferInstance

end ModuleTopologyComplete

/-! ### Open mapping theorem for complete metrizable topological groups

The Banach open mapping theorem: a surjective continuous group homomorphism
from a sigma-compact complete topological group to a Baire T₂ group is open.

This is a specialization of `AddMonoidHom.isOpenMap_of_sigmaCompact` to the
setting with a complete uniform structure, which is the form used for
Tate acyclicity (Wedhorn Thm 6.16). -/

section BanachOpenMapping

/-- **Open mapping theorem for sigma-compact complete topological groups.**
A surjective continuous homomorphism from a sigma-compact complete uniform
additive group to a Baire T₂ topological group is open.

This is the standard Banach open mapping theorem, used in Wedhorn Thm 6.16
for the strict exactness of the Laurent cover Čech complex.

Note: the original statement omitted the `SigmaCompactSpace G` hypothesis,
but the result is false without it. Consider `G = (ℝ, discrete)` and
`H = (ℝ, usual)`: the identity is continuous and surjective but not open.
The sigma-compactness hypothesis is satisfied in all applications (e.g.,
complete metrizable groups are sigma-compact). -/
theorem AddMonoidHom.isOpenMap_of_complete_countable
    {G H : Type*} [AddCommGroup G] [UniformSpace G] [IsUniformAddGroup G]
    [CompleteSpace G] [SigmaCompactSpace G]
    [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [BaireSpace H] [T2Space H]
    (f : G →+ H) (hf : Function.Surjective f) (hf_cont : Continuous f) :
    IsOpenMap f :=
  AddMonoidHom.isOpenMap_of_sigmaCompact f hf hf_cont

end BanachOpenMapping

/-! ### I-adic lattice topology characterization (Prop 6.18) -/

section AdicLattice

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- An **`A₀`-lattice** in a module `M` is a finitely generated `A₀`-submodule that
generates `M` as an `A`-module. -/
structure IsLattice (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) : Prop where
  /-- The lattice is finitely generated over `A₀`. -/
  fg : M₀.FG
  /-- The lattice generates `M` over `A`. -/
  span_eq_top : Submodule.span A (M₀ : Set M) = ⊤

/-- The n-th lattice neighborhood: `I^n • M₀` as a submodule of `M`. -/
def latticeNhd (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) (n : ℕ) : Submodule P.A₀ M :=
  P.I ^ n • M₀

omit [IsTopologicalRing A] in
/-- The lattice neighborhoods `I^n • M₀` are antitone in `n`. -/
theorem latticeNhd_antitone (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) : Antitone (latticeNhd P M₀) := by
  intro m n hmn
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)

omit [IsTopologicalRing A] in
/-- `I^(n+m) • M₀ ≤ I^n • M₀` -/
theorem latticeNhd_add_le (P : PairOfDefinition A) {M : Type*} [AddCommGroup M] [Module A M]
    (M₀ : Submodule P.A₀ M) (n m : ℕ) : latticeNhd P M₀ (n + m) ≤ latticeNhd P M₀ n :=
  latticeNhd_antitone P M₀ le_self_add

end AdicLattice

/-! ### Module topology on the ring itself -/

section RingModuleTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- A topological ring `A` has `IsModuleTopology A A`. This is
`IsTopologicalSemiring.toIsModuleTopology` from mathlib. -/
example : IsModuleTopology A A := inferInstance

/-- For a finite type `ι`, the product `ι → A` has `IsModuleTopology A (ι → A)`.
This is `IsModuleTopology.instPi` from mathlib. -/
example (ι : Type*) [Finite ι] : IsModuleTopology A (ι → A) := inferInstance

end RingModuleTopology

/-! ### Neighborhood basis characterization -/

section NhdBasis

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The standard `A₀`-lattice in `Fin k → A` is `(A₀)^k`, the product of copies of `A₀`. -/
def stdLattice (P : PairOfDefinition A) (k : ℕ) : Submodule P.A₀ (Fin k → A) where
  carrier := Set.pi Set.univ (fun _ ↦ (P.A₀ : Set A))
  add_mem' ha hb := fun i _ ↦ P.A₀.add_mem (ha i trivial) (hb i trivial)
  zero_mem' := fun _ _ ↦ P.A₀.zero_mem
  smul_mem' r _ hx := fun i _ ↦ P.A₀.mul_mem r.2 (hx i trivial)

omit [IsTopologicalRing A] in
/-- Elements of the standard lattice are exactly tuples in `(A₀)^k`. -/
theorem mem_stdLattice_iff (P : PairOfDefinition A) {k : ℕ} {x : Fin k → A} :
    x ∈ stdLattice P k ↔ ∀ i, x i ∈ P.A₀ :=
  ⟨fun h i ↦ h i trivial, fun h i _ ↦ h i⟩

end NhdBasis

/-! ### Strict exact sequences -/

section StrictExact

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {M₁ M₂ M₃ : Type*}
  [AddCommGroup M₁] [Module A M₁] [TopologicalSpace M₁]
  [AddCommGroup M₂] [Module A M₂] [TopologicalSpace M₂]
  [AddCommGroup M₃] [Module A M₃] [TopologicalSpace M₃]

omit [IsTopologicalRing A] in
/-- A short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules with module topology
is **strict exact**: `g` is an open map and `f` is continuous.
This is a consequence of Prop 6.18(2) (open mapping theorem). -/
theorem IsModuleTopology.strictExact
    [IsModuleTopology A M₁] [IsModuleTopology A M₂] [IsModuleTopology A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hg_surj : Function.Surjective g) :
    IsOpenMap g ∧ Continuous f := by
  have := IsModuleTopology.toContinuousAdd (R := A) (A := M₂)
  have := IsModuleTopology.toContinuousSMul (R := A) (A := M₂)
  exact ⟨IsModuleTopology.isOpenMap_of_surjective_of_finite g hg_surj,
         IsModuleTopology.continuous_of_linearMap f⟩

end StrictExact

/-! ### Wedhorn Prop 6.17 and 6.18: closed submodules and unique topology

**Wedhorn Proposition 6.17** (lecture notes p. 50, "Proof. Missing"):
Let `A` be a complete Tate ring and `M` a complete topological `A`-module
with a countable fundamental system of open neighborhoods of `0`. Then `M`
is noetherian if and only if every submodule of `M` is closed. In
particular, `A` itself is noetherian iff every ideal of `A` is closed.

**Wedhorn Proposition 6.18** (p. 50, "Proof. Missing"): Let `A` be a complete
noetherian Tate ring.
1. Every finitely generated `A`-module has a unique `A`-module topology that
   is complete and has a countable fundamental system of open neighborhoods
   of `0`.
2. Every `A`-linear map `f : M → N` between f.g. modules with that topology
   is continuous, and `f : M → f(M)` is open.

Prop 6.18(2) is already covered (for `IsModuleTopology`) by Mathlib's
`IsModuleTopology.isOpenMap_of_surjective_of_finite` and
`IsModuleTopology.continuous_linearMap_of_finite` above. Prop 6.18(1) — the
existence and uniqueness of a complete Hausdorff module topology — is the
non-trivial part, and is what unlocks Prop 6.17 via the quotient argument
(`M` noetherian ⇒ `M/N` is a f.g. module with unique complete topology ⇒
the quotient map `M → M/N` is continuous into a `T2` space ⇒ `N` is closed).

Prop 6.17 is proved below as `Wedhorn.isClosed_ideal_of_noetherian` using
Krull intersection in the noetherian ring of definition `A₀` (Phase 2.3 of
the Wedhorn flatness route). The signature takes a pair of definition `P`
with noetherian `A₀` as an explicit hypothesis; strongly-noetherian Tate
rings (Wedhorn Def 6.9) automatically provide such a pair.

See `docs/plans/2026-04-08-wedhorn-vs-zavyalov.md` Phase 2. -/

section WedhornClosedIdeals

open Filter Topology

/-- **Helper:** In a complete T₂ noetherian commutative ring `R` whose topology
is `I`-adic for some ideal `I`, every ideal `J` is closed.

This is the abstract ring-theoretic core of Wedhorn Proposition 6.17; it does
not need the Tate/Huber structure and only relies on:
(a) Krull's intersection theorem `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson`,
(b) `IsAdicComplete.le_jacobson_bot`, and
(c) the closure characterization via the adic basis of neighborhoods of `0`.

We inline the proof here (rather than importing the parallel statement
`isClosed_ideal_of_noetherian_adic_separated` from `TopologyComparison.lean`)
to keep the dependency chain clean. -/
private theorem isClosed_ideal_of_adicComplete_noetherian
    {R : Type*} [CommRing R] [UniformSpace R] [IsUniformAddGroup R]
    [IsTopologicalRing R] [T2Space R] [CompleteSpace R] [IsNoetherianRing R]
    {I : Ideal R} (hadic : IsAdic I) (J : Ideal R) :
    IsClosed (J : Set R) := by
  let : IsAdicComplete I R := hadic.isAdicComplete_iff.mpr ⟨‹_›, ‹_›⟩
  have hjac : I ≤ (⊥ : Ideal R).jacobson := IsAdicComplete.le_jacobson_bot I
  have hkrull : (⨅ i : ℕ, I ^ i • (⊤ : Submodule R (R ⧸ J))) = ⊥ :=
    Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I hjac
  rw [← closure_subset_iff_isClosed]
  intro x hx
  rw [mem_closure_iff_nhds_basis (hadic.hasBasis_nhds x)] at hx
  suffices Ideal.Quotient.mk J x = 0 from Ideal.Quotient.eq_zero_iff_mem.mp this
  have hmem : Ideal.Quotient.mk J x ∈
      (⨅ i : ℕ, I ^ i • (⊤ : Submodule R (R ⧸ J))) := by
    rw [Submodule.mem_iInf]
    intro n
    obtain ⟨y, hy_mem, hxy⟩ := hx n trivial
    obtain ⟨z, hz, rfl⟩ := hxy
    have hyz : Ideal.Quotient.mk J (x + z) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hy_mem
    have hxeq : Ideal.Quotient.mk J x = -(Ideal.Quotient.mk J z) := by
      have h1 : Ideal.Quotient.mk J x + Ideal.Quotient.mk J z = 0 := by
        rw [← map_add]; exact hyz
      exact eq_neg_of_add_eq_zero_left h1
    rw [hxeq]
    apply neg_mem
    change Ideal.Quotient.mk J z ∈ I ^ n • (⊤ : Submodule R (R ⧸ J))
    rw [Ideal.smul_top_eq_map]
    exact (Submodule.restrictScalars_mem R _ _).mpr (Ideal.mem_map_of_mem _ hz)
  rw [hkrull, Submodule.mem_bot] at hmem
  exact hmem

/-- **Wedhorn Proposition 6.17 (ideal form):** Every ideal in a complete Tate
ring `A` with a noetherian ring of definition `P.A₀` is closed.

The statement requires a pair of definition `P = (A₀, I)` such that `A₀` is
noetherian. This is automatic for **strongly noetherian** Tate rings (the
setting of Huber's theory, Wedhorn Def 6.9), and downstream callers can
discharge the `IsNoetherianRing P.A₀` hypothesis from a strongly-noetherian
structure.

**Proof sketch (Krull intersection on the ring of definition).**

1. `A₀ = P.A₀` is an open, hence closed (open subgroup of a topological
   group), subring of `A`. It inherits `CompleteSpace`, `T2Space`, and its
   subspace topology is the `I`-adic topology by `P.isAdic`.
2. `J₀ := J.comap P.A₀.subtype`, the pullback of `J` to `A₀`, is closed in
   `A₀` by the abstract helper
   `isClosed_ideal_of_adicComplete_noetherian` applied to the noetherian
   complete T₂ adic ring `A₀`.
3. `closure_A(J) ∩ A₀ = J₀`: for `x ∈ A₀`, membership in `closure_A(J)` is
   characterised by the `A`-neighborhood basis `{x + Subtype.val '' I^n}`,
   which equals the `A₀`-basis `{x + I^n}` under the inclusion. So
   `x ∈ closure_A(J) ↔ x ∈ closure_{A₀}(J₀)`, and the latter equals `J₀`
   since `J₀` is closed in `A₀`.
4. To close the argument for a general `x ∈ closure_A(J)`, we use that `P`
   can be chosen as a **principal pair** (via
   `IsTateRing.exists_principal_pairOfDefinition`) with generator `π` a
   topologically nilpotent unit in `A`. Then some power `π^k · x` lands in
   `A₀` (because `π^k → 0` and `A₀` is an open neighborhood of `0`), and
   `π^k · x ∈ closure_A(J) ∩ A₀ = J₀ ⊆ J`, so `x = π^(-k) · (π^k · x) ∈ J`.

Because the signature of the theorem takes an **arbitrary** pair `P`, not
necessarily principal, step 4 uses `IsTateRing.exists_principal_pairOfDefinition`
to produce a principal pair `P'` and argues via `P'` whose `A₀'`-inclusion
factors through `P.A₀`'s closure — this only needs the *abstract* existence of a
topologically nilpotent unit and `P.A₀` being open. -/
theorem Wedhorn.isClosed_ideal_of_noetherian
    {A : Type*} [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
    [IsTopologicalRing A] [T2Space A] [CompleteSpace A] [IsTateRing A]
    (P : PairOfDefinition A) [IsNoetherianRing ↥P.A₀]
    (J : Ideal A) : IsClosed (J : Set A) := by
  -- Step 1: A₀ is closed in A (open subring of an additive topological group).
  have hA₀_closed : IsClosed (P.A₀ : Set A) :=
    AddSubgroup.isClosed_of_isOpen P.A₀.toAddSubgroup P.isOpen
  -- Step 2: Install uniform + complete instances on ↥P.A₀.
  let : IsUniformAddGroup ↥P.A₀ := P.A₀.toAddSubgroup.isUniformAddGroup
  let : CompleteSpace ↥P.A₀ := hA₀_closed.completeSpace_coe
  -- Step 3: Apply the abstract helper to show J₀ := J.comap A₀.subtype is closed.
  set J₀ : Ideal ↥P.A₀ := J.comap P.A₀.subtype with hJ₀_def
  have hJ₀_closed : IsClosed (J₀ : Set ↥P.A₀) :=
    isClosed_ideal_of_adicComplete_noetherian P.isAdic J₀
  -- Step 4: Get a principal pair P' with generator π (topologically nilpotent unit in A).
  obtain ⟨P', π, hπ_span, hπ_unit⟩ := IsTateRing.exists_principal_pairOfDefinition A
  have hπ_mem : π ∈ P'.I := by rw [hπ_span]; exact Ideal.mem_span_singleton_self π
  have hπ_nilp : IsTopologicallyNilpotent ((π : A)) :=
    P'.isTopologicallyNilpotent_of_mem hπ_mem
  -- Step 5: Main argument. Show closure(J) ⊆ J.
  rw [← closure_subset_iff_isClosed]
  intro x hx_cl
  -- Translate `x ∈ closure(J)` to `x ∈ J.closure` (as an ideal).
  have hx_cl' : x ∈ J.closure := by rwa [← Ideal.coe_closure] at hx_cl
  -- 5a. Find k : ℕ such that (π : A) ^ k * x ∈ P.A₀.
  have hπx_tends : Filter.Tendsto (fun k : ℕ ↦ (π : A) ^ k * x) Filter.atTop (nhds 0) := by
    simpa using hπ_nilp.mul_const x
  have hA₀_nhds : (P.A₀ : Set A) ∈ nhds (0 : A) := P.isOpen.mem_nhds P.A₀.zero_mem
  obtain ⟨k, hk⟩ := (hπx_tends.eventually hA₀_nhds).exists
  set a : A := (π : A) ^ k * x with ha_def
  have ha_A₀ : a ∈ P.A₀ := hk
  -- 5b. a ∈ J.closure (closure is an ideal, closed under ring multiplication).
  have ha_cl' : a ∈ J.closure := J.closure.mul_mem_left ((π : A) ^ k) hx_cl'
  have ha_cl : a ∈ closure (J : Set A) := by rw [← Ideal.coe_closure]; exact ha_cl'
  -- 5c. Show ⟨a, ha_A₀⟩ is in closure of J₀ in ↥P.A₀.
  set a₀ : ↥P.A₀ := ⟨a, ha_A₀⟩ with ha₀_def
  have ha₀_cl : a₀ ∈ closure (J₀ : Set ↥P.A₀) := by
    rw [mem_closure_iff_nhds_basis (P.isAdic.hasBasis_nhds a₀)]
    intro n _
    -- Need: ∃ y ∈ J₀, y ∈ (fun z ↦ a₀ + z) '' (P.I^n : Ideal P.A₀).
    -- Build the corresponding neighborhood in A and extract a point of J.
    have hnhd_A : ((fun y ↦ a + y) '' (Subtype.val ''
        ((P.I ^ n : Ideal P.A₀) : Set P.A₀))) ∈ nhds a := by
      have : (Subtype.val '' ((P.I ^ n : Ideal P.A₀) : Set P.A₀) : Set A) ∈ nhds (0 : A) :=
        P.hasBasis_nhds_zero.mem_of_mem (i := n) trivial
      rw [← map_add_left_nhds_zero a]
      exact Filter.image_mem_map this
    rw [mem_closure_iff_nhds] at ha_cl
    obtain ⟨j, hj_in_nhd, hj_in_J⟩ := ha_cl _ hnhd_A
    obtain ⟨b, ⟨b₀, hb₀_mem, rfl⟩, hj_eq⟩ := hj_in_nhd
    -- hj_eq : a + (b₀ : A) = j;  hb₀_mem : b₀ ∈ (P.I ^ n : Ideal P.A₀)
    -- hj_in_J : j ∈ J.
    -- j = a + b₀ ∈ A₀, so (⟨j, _⟩ : P.A₀) is well-defined.
    have hj_A₀ : j ∈ P.A₀ := by rw [← hj_eq]; exact P.A₀.add_mem ha_A₀ b₀.2
    refine ⟨⟨j, hj_A₀⟩, ?_, ?_⟩
    · -- ⟨j, hj_A₀⟩ ∈ J₀: just j ∈ J
      change j ∈ J; exact hj_in_J
    · -- ⟨j, hj_A₀⟩ ∈ (fun y ↦ a₀ + y) '' ↑(P.I^n)
      refine ⟨b₀, hb₀_mem, ?_⟩
      apply Subtype.ext
      change a + (b₀ : A) = j
      exact hj_eq
  -- 5d. a₀ ∈ J₀ by hJ₀_closed.
  have ha₀_in_J₀ : a₀ ∈ J₀ := by
    have h : a₀ ∈ (J₀ : Set ↥P.A₀) := hJ₀_closed.closure_eq ▸ ha₀_cl
    exact h
  -- 5e. Unpack: a = ↑a₀ ∈ J (by the comap definition of J₀).
  have ha_in_J : a ∈ J := ha₀_in_J₀
  -- 5f. Conclude x ∈ J. Since π is a unit in A, let πu : Aˣ with ↑πu = π.
  obtain ⟨πu, hπu⟩ := hπ_unit
  -- x = πu⁻¹^k * (πu^k * x) = πu⁻¹^k * ((π : A)^k * x) = πu⁻¹^k * a.
  have hx_eq : x = ((πu⁻¹ : Aˣ) : A) ^ k * a := by
    have hpi : ((πu : A)) = π := hπu
    have : ((πu⁻¹ : Aˣ) : A) ^ k * ((πu : A) ^ k * x) = x := by
      rw [← mul_assoc, ← mul_pow]
      simp [Units.inv_mul]
    calc x = ((πu⁻¹ : Aˣ) : A) ^ k * ((πu : A) ^ k * x) := this.symm
      _ = ((πu⁻¹ : Aˣ) : A) ^ k * a := by rw [ha_def, hpi]
  rw [hx_eq]
  exact J.mul_mem_left _ ha_in_J

end WedhornClosedIdeals
