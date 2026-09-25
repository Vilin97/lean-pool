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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyFoundations
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Presheaf
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets

/-!
# The genuine structure presheaf on all opens (projective-limit model)

Wedhorn §8.1: on a rational open `R(T/s)` the structure presheaf takes the value
`𝒪_X(R(T/s)) = A⟨T/s⟩` (the completed rational localization, `presheafValue`); on an
**arbitrary** open `V ⊆ Spa (A, A⁺)`,

    𝒪_X(V) = lim_{R(T/s) ⊆ V} 𝒪_X(R(T/s)),

with the **projective-limit topology**. This file constructs that object as the
compatible-family subring

    limitSections V ⊆ ∏_{D : RationalIndex V} presheafValue D

with the subspace topology of the product — which *is* the initial topology for the
rational evaluations, i.e. the projective-limit topology (`Topology.IsInducing.subtypeVal`
composed with the product's universal property).

## Main definitions

* `spaOpen D` / `spaOpens D` : the rational subset `R(D.T/D.s)` as a subset/open of the
  subtype `↥(Spa A A⁺)`.
* `RationalIndex V` : valid (`IsRational`) rational data whose rational open is
  contained in `V` — the index of the limit.
* `limitSections V` : the compatible families, as a `Subring` of the product.
* `limitRestrict h : limitSections V →+* limitSections W` for `W ≤ V` — reindexing;
  continuous, and functorial (`limitRestrict_id`, `limitRestrict_comp`).
* `limitEval hD : limitSections (spaOpens D) ≃+* presheafValue D` — the rational-open
  comparison (Wedhorn 8.1.1 for the extended presheaf): evaluation at the tautological
  index, with inverse "restrict everywhere"; a homeomorphism
  (`limitEval_continuous`, `limitEval_symm_continuous`).

## Main results

* `isClosed_limitSections` : the compatibility locus is closed in the product
  (equalizers of continuous maps into the separated completions) — hence
  `limitSections.completeSpace` : each value is a **complete** topological ring, and
  `instT2Space` : separated. No discrete topology appears anywhere on this path.
* `limitSections_topology_isInducing` : the topology is initial for the rational
  evaluation maps (the projective-limit topology).
* `spaOpens_globalLocData` : `R({1}/1) = ⊤`, so `limitSections ⊤` is identified by
  `limitEval` with `presheafValue (globalLocData P) = Â` (Wedhorn Remark 8.3; the
  topological `Â`-comparison for complete Tate rings is assembled downstream with the
  8.28 machinery).

The presheaf is bundled functorially downstream (`SheafyPair.lean`); this file keeps to
the concrete objects so the topology stays visibly coherent (one `TopologicalSpace`
instance per value, its `UniformSpace` the subspace uniformity of the product —
the handover's F2 requirement).
-/

@[expose] public section

noncomputable section

open Topology

namespace ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]
  [PlusSubring A] [IsHuberRing A]

/-! ### Rational opens inside the subtype `↥(Spa A A⁺)` -/

/-- The rational subset `R(D.T/D.s)` as a subset of the subtype `↥(Spa A A⁺)`. -/
def spaOpen (D : RationalLocData A) : Set ↥(Spa A A⁺) :=
  Subtype.val ⁻¹' rationalOpen D.T D.s

theorem isOpen_spaOpen (D : RationalLocData A) : IsOpen (spaOpen D) :=
  rationalOpen_isOpen D.T D.s

/-- The rational subset `R(D.T/D.s)` as an open of `↥(Spa A A⁺)` (Wedhorn Thm 7.35(2)). -/
def spaOpens (D : RationalLocData A) : TopologicalSpace.Opens ↥(Spa A A⁺) :=
  ⟨spaOpen D, isOpen_spaOpen D⟩

@[simp] theorem coe_spaOpens (D : RationalLocData A) :
    (spaOpens D : Set ↥(Spa A A⁺)) = spaOpen D := rfl

theorem mem_spaOpen {D : RationalLocData A} {v : ↥(Spa A A⁺)} :
    v ∈ spaOpen D ↔ (v : Spv A) ∈ rationalOpen D.T D.s := Iff.rfl

/-- Containment of rational opens can be checked in the subtype: since
`rationalOpen ⊆ Spa A A⁺` always, `spaOpen`-containment is equivalent to
`rationalOpen`-containment in `Spv A`. -/
theorem spaOpen_subset_iff {D E : RationalLocData A} :
    spaOpen D ⊆ spaOpen E ↔ rationalOpen D.T D.s ⊆ rationalOpen E.T E.s := by
  constructor
  · intro h v hv
    exact h (show (⟨v, rationalOpen_subset_spa hv⟩ : ↥(Spa A A⁺)) ∈ spaOpen D from hv)
  · intro h v hv
    exact h hv

theorem spaOpen_subset_of_rationalOpen_subset {D E : RationalLocData A}
    (h : rationalOpen D.T D.s ⊆ rationalOpen E.T E.s) : spaOpen D ⊆ spaOpen E :=
  spaOpen_subset_iff.mpr h

/-! ### The index of the projective limit -/

/-- The index of the projective limit at an open `V`: **valid** rational data
(`IsRational`, Wedhorn Definition 7.29) whose rational open is contained in `V`.
Raw (non-rational) data do not index the literature-facing presheaf. -/
structure RationalIndex (V : TopologicalSpace.Opens ↥(Spa A A⁺)) where
  /-- The underlying rational localization datum. -/
  D : RationalLocData A
  /-- The datum presents a rational subset (Wedhorn Definition 7.29). -/
  isRational : D.IsRational
  /-- Its rational open is contained in `V`. -/
  subset : spaOpen D ⊆ (V : Set ↥(Spa A A⁺))

/-- Reindexing along `W ≤ V`. -/
def RationalIndex.mono {V W : TopologicalSpace.Opens ↥(Spa A A⁺)} (h : W ≤ V)
    (i : RationalIndex W) : RationalIndex V :=
  ⟨i.D, i.isRational, i.subset.trans h⟩

@[simp] theorem RationalIndex.mono_D {V W : TopologicalSpace.Opens ↥(Spa A A⁺)}
    (h : W ≤ V) (i : RationalIndex W) : (i.mono h).D = i.D := rfl

variable [HasLocLiftPowerBounded A]

/-! ### The compatible-family subring -/

/-- The **compatible families**: elements of the product of the completed rational
localizations over `RationalIndex V` whose coordinates are intertwined by the canonical
restriction maps. This is Wedhorn's projective limit
`𝒪_X(V) = lim_{R(T/s) ⊆ V} A⟨T/s⟩` in its concrete model. -/
def limitSections (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    Subring (∀ i : RationalIndex V, presheafValue i.D) where
  carrier := {x | ∀ (i j : RationalIndex V)
    (h : rationalOpen j.D.T j.D.s ⊆ rationalOpen i.D.T i.D.s),
    restrictionMap i.D j.D h (x i) = x j}
  one_mem' := fun i j h => by
    show restrictionMapHom i.D j.D h 1 = 1
    exact map_one _
  mul_mem' := fun {x y} hx hy i j h => by
    show restrictionMapHom i.D j.D h (x i * y i) = x j * y j
    rw [map_mul]
    exact congrArg₂ (· * ·) (hx i j h) (hy i j h)
  zero_mem' := fun i j h => by
    show restrictionMapHom i.D j.D h 0 = 0
    exact map_zero _
  add_mem' := fun {x y} hx hy i j h => by
    show restrictionMapHom i.D j.D h (x i + y i) = x j + y j
    rw [map_add]
    exact congrArg₂ (· + ·) (hx i j h) (hy i j h)
  neg_mem' := fun {x} hx i j h => by
    show restrictionMapHom i.D j.D h (-x i) = -x j
    rw [map_neg]
    exact congrArg Neg.neg (hx i j h)

theorem mem_limitSections {V : TopologicalSpace.Opens ↥(Spa A A⁺)}
    {x : ∀ i : RationalIndex V, presheafValue i.D} :
    x ∈ limitSections V ↔ ∀ (i j : RationalIndex V)
      (h : rationalOpen j.D.T j.D.s ⊆ rationalOpen i.D.T i.D.s),
      restrictionMap i.D j.D h (x i) = x j := Iff.rfl

/-- **The compatibility locus is closed** in the product: it is the intersection of the
equalizers of the continuous maps `x ↦ res (x i)` and `x ↦ x j` into the separated
(complete Hausdorff) values `𝒪_X(D_j)`. This is the topological input for completeness
of the limit values (no discrete uniformity anywhere). -/
theorem isClosed_limitSections (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    IsClosed (limitSections V : Set (∀ i : RationalIndex V, presheafValue i.D)) := by
  have : (limitSections V : Set (∀ i : RationalIndex V, presheafValue i.D)) =
      ⋂ (i : RationalIndex V) (j : RationalIndex V)
        (h : rationalOpen j.D.T j.D.s ⊆ rationalOpen i.D.T i.D.s),
        {x | restrictionMap i.D j.D h (x i) = x j} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact Iff.rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun h => ?_
  exact isClosed_eq
    ((restrictionMapHom_continuous i.D j.D h).comp (continuous_apply i))
    (continuous_apply j)

/-- The limit value is a **complete** topological ring: a closed subring of the product
of the complete values (Wedhorn §8.1: the projective limit of complete topological rings
is complete). -/
instance limitSections.completeSpace (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    CompleteSpace ↥(limitSections V) :=
  (isClosed_limitSections V).completeSpace_coe

instance limitSections.t2Space (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    T2Space ↥(limitSections V) :=
  inferInstance

/-- The subspace topology on the limit is **initial for the rational evaluations**
(the projective-limit topology): the inclusion into the product is inducing, and the
product topology is initial for its projections. -/
theorem limitSections_topology_isInducing (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    Topology.IsInducing
      (fun x : ↥(limitSections V) => (x : ∀ i : RationalIndex V, presheafValue i.D)) :=
  Topology.IsInducing.subtypeVal

/-- The rational evaluation maps out of the limit, as ring homomorphisms. -/
def limitEvalHom {V : TopologicalSpace.Opens ↥(Spa A A⁺)} (i : RationalIndex V) :
    ↥(limitSections V) →+* presheafValue i.D :=
  (Pi.evalRingHom (fun j : RationalIndex V => presheafValue j.D) i).comp
    (limitSections V).subtype

@[simp] theorem limitEvalHom_apply {V : TopologicalSpace.Opens ↥(Spa A A⁺)}
    (i : RationalIndex V) (x : ↥(limitSections V)) :
    limitEvalHom i x = (x : ∀ j : RationalIndex V, presheafValue j.D) i := rfl

theorem limitEvalHom_continuous {V : TopologicalSpace.Opens ↥(Spa A A⁺)}
    (i : RationalIndex V) : Continuous (limitEvalHom i) :=
  (continuous_apply i).comp continuous_subtype_val

/-! ### Restriction to a smaller open -/

/-- Restriction `𝒪_X(V) → 𝒪_X(W)` for `W ≤ V`: reindex the compatible family along
`RationalIndex.mono`. -/
def limitRestrict {V W : TopologicalSpace.Opens ↥(Spa A A⁺)} (h : W ≤ V) :
    ↥(limitSections V) →+* ↥(limitSections W) where
  toFun x := ⟨fun i => (x : ∀ j : RationalIndex V, presheafValue j.D) (i.mono h),
    fun i j hij => x.2 (i.mono h) (j.mono h) hij⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem limitRestrict_apply {V W : TopologicalSpace.Opens ↥(Spa A A⁺)}
    (h : W ≤ V) (x : ↥(limitSections V)) (i : RationalIndex W) :
    (limitRestrict h x : ∀ j : RationalIndex W, presheafValue j.D) i =
      (x : ∀ j : RationalIndex V, presheafValue j.D) (i.mono h) := rfl

theorem limitRestrict_continuous {V W : TopologicalSpace.Opens ↥(Spa A A⁺)} (h : W ≤ V) :
    Continuous (limitRestrict h) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact (continuous_apply (i.mono h)).comp continuous_subtype_val

@[simp] theorem limitRestrict_id (V : TopologicalSpace.Opens ↥(Spa A A⁺)) :
    limitRestrict (le_refl V) = RingHom.id ↥(limitSections V) := by
  refine RingHom.ext fun x => Subtype.ext (funext fun i => ?_)
  rfl

theorem limitRestrict_comp {U V W : TopologicalSpace.Opens ↥(Spa A A⁺)}
    (hWV : W ≤ V) (hVU : V ≤ U) :
    (limitRestrict hWV).comp (limitRestrict hVU) = limitRestrict (hWV.trans hVU) := by
  refine RingHom.ext fun x => Subtype.ext (funext fun i => ?_)
  rfl

/-! ### The rational-open comparison (Wedhorn 8.1.1 for the extended presheaf) -/

section RationalComparison

variable {D₀ : RationalLocData A}

/-- The tautological index: a valid rational datum indexes its own rational open. -/
def RationalIndex.self (D₀ : RationalLocData A) (hD₀ : D₀.IsRational) :
    RationalIndex (spaOpens D₀) :=
  ⟨D₀, hD₀, subset_rfl⟩

omit [HasLocLiftPowerBounded A] in
/-- Every index of `spaOpens D₀` has rational open contained in `R(D₀.T/D₀.s)`
(in `Spv A` terms). -/
theorem RationalIndex.rationalOpen_subset {D₀ : RationalLocData A}
    (i : RationalIndex (spaOpens D₀)) :
    rationalOpen i.D.T i.D.s ⊆ rationalOpen D₀.T D₀.s :=
  spaOpen_subset_iff.mp i.subset

/-- "Restrict everywhere": the canonical map `A⟨T₀/s₀⟩ → lim_{R(D) ⊆ R(D₀)} A⟨T/s⟩`,
sending a value to the family of all its restrictions. Compatibility is restriction
functoriality (`restrictionMap_comp`). -/
def limitOfValue (D₀ : RationalLocData A) :
    presheafValue D₀ →+* ↥(limitSections (spaOpens D₀)) where
  toFun x := ⟨fun i => restrictionMap D₀ i.D i.rationalOpen_subset x, by
    intro i j hij
    have h := congr_fun (restrictionMap_comp D₀ i.D j.D i.rationalOpen_subset hij) x
    simp only [Function.comp_apply] at h
    exact h⟩
  map_one' := Subtype.ext (funext fun i => map_one (restrictionMapHom D₀ i.D _))
  map_mul' x y := Subtype.ext (funext fun i => map_mul (restrictionMapHom D₀ i.D _) x y)
  map_zero' := Subtype.ext (funext fun i => map_zero (restrictionMapHom D₀ i.D _))
  map_add' x y := Subtype.ext (funext fun i => map_add (restrictionMapHom D₀ i.D _) x y)

@[simp] theorem limitOfValue_apply (D₀ : RationalLocData A) (x : presheafValue D₀)
    (i : RationalIndex (spaOpens D₀)) :
    (limitOfValue D₀ x : ∀ j : RationalIndex (spaOpens D₀), presheafValue j.D) i =
      restrictionMap D₀ i.D i.rationalOpen_subset x := rfl

theorem limitOfValue_continuous (D₀ : RationalLocData A) :
    Continuous (limitOfValue D₀) := by
  refine Continuous.subtype_mk (continuous_pi fun i => ?_) _
  exact restrictionMapHom_continuous D₀ i.D i.rationalOpen_subset

/-- **The rational-open comparison** (Wedhorn 8.1.1 for the all-open presheaf): on the
rational open `R(D₀.T/D₀.s)`, the projective-limit value is canonically the completed
rational localization `A⟨T₀/s₀⟩`. Forward: evaluate at the tautological index; inverse:
restrict everywhere. Both are continuous ring homomorphisms (`limitEval_continuous`,
`limitOfValue_continuous`), so this is an isomorphism of topological rings. -/
def limitEval (hD₀ : D₀.IsRational) :
    ↥(limitSections (spaOpens D₀)) ≃+* presheafValue D₀ where
  toFun := limitEvalHom (RationalIndex.self D₀ hD₀)
  invFun := limitOfValue D₀
  left_inv x := by
    refine Subtype.ext (funext fun i => ?_)
    exact x.2 (RationalIndex.self D₀ hD₀) i i.rationalOpen_subset
  right_inv x := by
    -- `(RationalIndex.self D₀ hD₀).D` reduces to `D₀` and the containment proofs are
    -- irrelevant, so `restrictionMap_id` closes the evaluation of the restriction family.
    exact congr_fun (restrictionMap_id D₀) x
  map_mul' x y := map_mul (limitEvalHom _) x y
  map_add' x y := map_add (limitEvalHom _) x y

theorem limitEval_continuous (hD₀ : D₀.IsRational) :
    Continuous (limitEval hD₀) :=
  limitEvalHom_continuous (RationalIndex.self D₀ hD₀)

theorem limitEval_symm_continuous (hD₀ : D₀.IsRational) :
    Continuous (limitEval hD₀).symm :=
  limitOfValue_continuous D₀

/-- The rational comparison as evaluation: tracking lemma. -/
@[simp] theorem limitEval_apply (hD₀ : D₀.IsRational) (x : ↥(limitSections (spaOpens D₀))) :
    limitEval hD₀ x =
      (x : ∀ j : RationalIndex (spaOpens D₀), presheafValue j.D)
        (RationalIndex.self D₀ hD₀) := rfl

end RationalComparison

/-! ### The whole space (Wedhorn Remark 8.3, presheaf level) -/

omit [HasLocLiftPowerBounded A] in
/-- The whole space is the rational open of the `{1}/1`-datum: `R({1}/1) = Spa (A, A⁺)`.
Combined with `limitEval`, this identifies `𝒪_X(X)` with
`presheafValue (globalLocData P)`; the further identification with `Â` (for complete
`A`) is Remark 8.3 and is assembled with the completion machinery downstream. -/
theorem spaOpens_globalLocData (P : PairOfDefinition A) :
    spaOpens (globalLocData P) = ⊤ := by
  refine le_antisymm le_top ?_
  intro v _
  refine ⟨v.2, fun t ht => ?_, ?_⟩
  · rw [show (globalLocData P).T = {1} from rfl] at ht
    rw [Finset.mem_singleton.mp ht]
    exact (v.1.vle_total 1 1).elim id id
  · exact v.1.not_vle_one_zero

end ValuationSpectrum
