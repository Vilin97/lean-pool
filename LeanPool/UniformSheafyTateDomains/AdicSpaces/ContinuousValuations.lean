/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.WithZeroTopology
import Mathlib.Topology.Algebra.OpenSubgroup
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ValuationSpectrum

/-!
# Continuous Valuations and Cont(A)

We define continuous valuations on a topological ring and the subspace `Cont(A)` of the
valuation spectrum `Spv(A)`, following Definition 7.7 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `Valuation.IsContinuous v` : A valuation `v` on a topological ring `A` is continuous if
  `{ a ∈ A | v(a) < γ }` is open for all `γ` in the value group.
* `ValuationSpectrum.IsContinuous v` : A point `v` of `Spv A` is continuous.
* `Cont A` : The set of continuous valuations in `Spv A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.7, Remark 7.8, Remark 7.9
-/

namespace Valuation

variable {A : Type*} [CommRing A] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- A valuation `v` on a topological ring `A` is *continuous* if `{ a | v(a) < γ }` is open
for all `γ` (Definition 7.7 of Wedhorn). -/
def IsContinuous [TopologicalSpace A] (v : Valuation A Γ₀) : Prop :=
  ∀ (γ : Γ₀), IsOpen { a : A | v a < γ }

variable (v : Valuation A Γ₀) [TopologicalSpace A]

/-- A valuation is continuous iff `{ a | v(a) < γ }` is open for all units `γ`. -/
lemma isContinuous_iff_units :
    v.IsContinuous ↔ ∀ (γ : Γ₀ˣ), IsOpen { a : A | v a < γ } := by
  refine ⟨fun h γ ↦ h γ, fun h γ ↦ ?_⟩
  by_cases hγ : γ = 0
  · subst hγ; simp
  · exact h (Units.mk0 γ hγ)

/-- If `v` is continuous, then `v.ltAddSubgroup γ` is open for every unit `γ`. -/
lemma IsContinuous.isOpen_ltAddSubgroup (hv : v.IsContinuous) (γ : Γ₀ˣ) :
    IsOpen (v.ltAddSubgroup γ : Set A) :=
  Valuation.coe_ltAddSubgroup v γ ▸ hv γ

/-- A `Valuation.IsContinuous` valuation (Wedhorn 7.7) on a topological ring is
continuous at any nonzero-value point `a` (in mathlib's topological sense):
the strict-triangle inequality forces `v ≡ v a` on the open neighborhood
`a + {b : v b < v a}` of `a`. -/
lemma IsContinuous.continuousAt_of_ne_zero [IsTopologicalRing A]
    [TopologicalSpace Γ₀] (hv : v.IsContinuous) {a : A} (ha : v a ≠ 0) :
    ContinuousAt v a := by
  rw [ContinuousAt]
  set B : Set A := {b | v b < v a}
  have hB_open : IsOpen B := hv (v a)
  have hB_zero : (0 : A) ∈ B := by
    change v 0 < v a
    rw [v.map_zero]; exact zero_lt_iff.mpr ha
  set T : Set A := (· + a) '' B
  have hT_open : IsOpen T := (Homeomorph.addRight a).isOpenMap _ hB_open
  have hT_a : a ∈ T := ⟨0, hB_zero, zero_add a⟩
  have heq : v =ᶠ[nhds a] fun _ ↦ v a := by
    refine Filter.eventually_of_mem (hT_open.mem_nhds hT_a) ?_
    rintro x ⟨b, hb, rfl⟩
    change v (b + a) = v a
    rw [add_comm b a, v.map_add_of_distinct_val (ne_of_gt hb)]
    exact max_eq_left hb.le
  exact heq.tendsto

/-- A `Valuation.IsContinuous` valuation (Wedhorn 7.7) on a topological ring is
continuous at `1`. Specialization of `IsContinuous.continuousAt_of_ne_zero` with
`a = 1` and `v 1 = 1 ≠ 0`. -/
lemma IsContinuous.continuousAt_one [IsTopologicalRing A]
    [TopologicalSpace Γ₀] (hv : v.IsContinuous) :
    ContinuousAt v 1 := by
  apply hv.continuousAt_of_ne_zero (a := 1)
  rw [v.map_one]
  exact one_ne_zero

open scoped WithZeroTopology in
/-- A `Valuation.IsContinuous` valuation (Wedhorn 7.7) on a topological ring is
continuous at any zero-value point `a` (with the `WithZeroTopology` instance on
`Γ₀`): the open `{b : v b < γ}` (Wedhorn 7.7) is a neighborhood of `a` since
`v a = 0 < γ`. -/
lemma IsContinuous.continuousAt_of_eq_zero [IsTopologicalRing A]
    (hv : v.IsContinuous) {a : A} (ha : v a = 0) :
    ContinuousAt v a := by
  rw [ContinuousAt, ha, WithZeroTopology.hasBasis_nhds_zero.tendsto_right_iff]
  intro γ hγ
  have hmem : a ∈ {b : A | v b < γ} := by
    change v a < γ
    rw [ha]
    exact zero_lt_iff.mpr hγ
  exact Filter.eventually_of_mem ((hv γ).mem_nhds hmem) fun _ hx ↦ hx

open scoped WithZeroTopology in
/-- A `Valuation.IsContinuous` valuation (Wedhorn 7.7) on a topological ring is
fully topologically continuous (with the `WithZeroTopology` instance on `Γ₀`).
Combines `continuousAt_of_ne_zero` (strict-triangle near nonzero values) and
`continuousAt_of_eq_zero` (Wedhorn 7.7 open neighborhood at zero values). -/
lemma IsContinuous.continuous [IsTopologicalRing A] (hv : v.IsContinuous) :
    Continuous v := by
  rw [continuous_iff_continuousAt]
  intro a
  by_cases ha : v a = 0
  · exact IsContinuous.continuousAt_of_eq_zero v hv ha
  · exact IsContinuous.continuousAt_of_ne_zero v hv ha

end Valuation

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-- A point `v` of `Spv A` is *continuous* if the canonical valuation is continuous
(Definition 7.7 of Wedhorn). -/
def IsContinuous [TopologicalSpace A] (v : Spv A) : Prop :=
  letI : ValuativeRel A := v.toValuativeRel
  (ValuativeRel.valuation A).IsContinuous

/-- The set `Cont(A)` of continuous valuations in `Spv(A)` (Definition 7.7 of Wedhorn). -/
def Cont (A : Type*) [CommRing A] [TopologicalSpace A] : Set (Spv A) :=
  { v : Spv A | v.IsContinuous }

variable [TopologicalSpace A]

/-- Membership in `Cont A` is equivalent to `IsContinuous`. -/
@[simp]
lemma mem_cont_iff (v : Spv A) : v ∈ Cont A ↔ v.IsContinuous := Iff.rfl

omit [TopologicalSpace A] in
private lemma embed_comp_valuation_eq {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀) (a : A) :
    letI := ValuativeRel.ofValuation v
    haveI := Valuation.Compatible.ofValuation v
    MonoidWithZeroHom.ValueGroup₀.embedding
      ((ValuativeRel.ValueGroupWithZero.embed v)
        ((ValuativeRel.valuation A) a)) = v a := by
  letI := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  change MonoidWithZeroHom.ValueGroup₀.embedding
    (ValuativeRel.ValueGroupWithZero.embed v
      (ValuativeRel.ValueGroupWithZero.mk a
        ⟨1, (ValuativeRel.posSubmonoid A).one_mem⟩)) = v a
  simp [ValuativeRel.ValueGroupWithZero.embed_mk, MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]

/-- If `v : Valuation A Γ₀` is continuous, then `ofValuation v` is continuous. -/
lemma isContinuous_ofValuation_of {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation A Γ₀)
    (hv : v.IsContinuous) : (ofValuation v).IsContinuous := by
  letI : ValuativeRel A := ValuativeRel.ofValuation v
  haveI := Valuation.Compatible.ofValuation v
  have h_sm := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
    (f := MonoidWithZeroHom.ofClass v)
  intro δ
  have heq : { a : A | (ValuativeRel.valuation A) a < δ } =
      { a : A | v a < MonoidWithZeroHom.ValueGroup₀.embedding
        ((ValuativeRel.ValueGroupWithZero.embed v) δ) } := by
    ext a; simp only [Set.mem_setOf_eq, ← embed_comp_valuation_eq v a]
    exact ⟨fun h ↦ h_sm ((ValuativeRel.ValueGroupWithZero.embed_strictMono v) h),
      fun h ↦ (ValuativeRel.ValueGroupWithZero.embed_strictMono v).lt_iff_lt.mp
        (h_sm.lt_iff_lt.mp h)⟩
  exact heq ▸ hv _

/-- Every valuation on a discrete ring is continuous (Remark 7.8(2) of Wedhorn). -/
theorem cont_eq_univ_of_discreteTopology [DiscreteTopology A] :
    Cont A = Set.univ :=
  Set.eq_univ_of_forall fun _ _ ↦ isOpen_discrete _

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B]

/-- `Spv(φ)` preserves continuity for continuous `φ` (Remark 7.9 of Wedhorn). -/
theorem comap_isContinuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : v.IsContinuous) :
    (comap φ v).IsContinuous := by
  letI : ValuativeRel B := v.toValuativeRel
  have hkey : comap φ v =
      ofValuation ((ValuativeRel.valuation B).comap φ) := by
    conv_lhs => rw [show v = ofValuation (ValuativeRel.valuation B)
      from (ofValuation_valuation v).symm]
    exact comap_ofValuation φ (ValuativeRel.valuation B)
  exact hkey ▸ isContinuous_ofValuation_of _ fun γ ↦ hφ.isOpen_preimage _ (hv γ)

/-- `Spv(φ)` maps `Cont B` into `Cont A` when `φ` is continuous (Remark 7.9). -/
theorem cont_comap_mapsTo {φ : A →+* B} (hφ : Continuous φ) :
    Set.MapsTo (comap φ) (Cont B) (Cont A) :=
  fun _ hv ↦ comap_isContinuous hφ hv

end Functoriality

end ValuationSpectrum

namespace Valuation

variable {A : Type*} [CommRing A] [TopologicalSpace A]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

/-- **Forward direction of Wedhorn 7.8(3)** (under topological additive
group): if `v` is continuous (Definition 7.7), then the half-space
`{a | γ ≤ v a}` (complement of the open ball `{v a < γ}`) is open for every
`γ`. -/
lemma IsContinuous.isOpen_setOf_ge [ContinuousAdd A] {v : Valuation A Γ₀}
    (hv : v.IsContinuous) (γ : Γ₀) :
    IsOpen { a : A | γ ≤ v a } := by
  by_cases hγ : γ = 0
  · subst hγ
    have hEq : { a : A | (0 : Γ₀) ≤ v a } = Set.univ :=
      Set.eq_univ_of_forall fun _ ↦ zero_le
    rw [hEq]
    exact isOpen_univ
  · have hClosed : IsClosed ((v.ltAddSubgroup (Units.mk0 γ hγ)) : Set A) :=
      AddSubgroup.isClosed_of_isOpen _
        (Valuation.IsContinuous.isOpen_ltAddSubgroup (v := v) hv (Units.mk0 γ hγ))
    have hcompl : { a : A | γ ≤ v a } =
        ((v.ltAddSubgroup (Units.mk0 γ hγ)) : Set A)ᶜ := by
      ext a
      simp only [v.coe_ltAddSubgroup, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt,
        Units.val_mk0]
    rw [hcompl]
    exact hClosed.isOpen_compl

/-- **Wedhorn 7.8(3) — claimed equivalence (CURRENTLY UNRESOLVED).**

*Claim:* `v` is continuous iff `{a | γ ≤ v a}` is open for every `γ`.

**Status (2026-05-18 audit):** the forward direction is captured by
`IsContinuous.isOpen_setOf_ge` under `[ContinuousAdd A]`. The reverse
direction, as stated for all `γ : Γ₀`, **is mathematically false** in this
project's hypothesis profile (only `[TopologicalSpace A]` / `[CommRing A]`).

**Counterexample (reverse direction).** Take `A = ℝ` with the standard
topology and the trivial valuation `v : ℝ → WithZero (Multiplicative ℤ)`
with `v 0 = 0`, `v a = 1` for `a ≠ 0`. Then:
* For every `γ : Γ₀`, `{a | γ ≤ v a}` is either `ℝ`, `ℝ \ {0}`, or `∅` —
  all open. So the hypothesis of the reverse direction holds.
* But `v.IsContinuous` fails: at `γ = 1`, `{a | v a < 1} = {0}`, which is
  not open in `ℝ`.

The original "transposition" docstring claimed `v(a) ≥ γ ↔ v(a)⁻¹ ≤ γ⁻¹`,
but this conflates `v(a)⁻¹` (value-group inverse) with `v(a⁻¹)` (value of
inverse in `A`), which only coincide when `a` is a unit. The set-level
equivalence breaks down on the support of `v`.

This statement is preserved as a named sorry so consumers calling it can
be located via the type system; **no working downstream consumer should
rely on the reverse direction as stated.** -/
theorem isContinuous_iff_setOf_ge_isOpen (v : Valuation A Γ₀) :
    v.IsContinuous ↔ ∀ γ : Γ₀, IsOpen { a : A | γ ≤ v a } :=
  sorry

end Valuation

/-! ## Determination of a continuous valuation by a dense subring

The injectivity content of Wedhorn Proposition 7.48 (= Huber [Hu2] Prop. 3.9): a continuous
valuation on a topological ring is determined by its restriction to a dense subring. This is
the elementary "uniqueness" half of the Spa–completion comparison, provable directly from
density, valuation continuity (Wedhorn 7.7), and the nonarchimedean strict-triangle rule —
without the full Huber §3 apparatus.
-/

namespace Valuation

variable {S : Type*} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- A continuous valuation is locally constant at a point of nonzero value: the strict
triangle inequality makes `{z | v z = v x}` a neighbourhood of `x` when `v x ≠ 0`. -/
lemma IsContinuous.setOf_value_eq_mem_nhds {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation S Γ₀} (hv : v.IsContinuous) {x : S} (hx : v x ≠ 0) :
    {z | v z = v x} ∈ nhds x := by
  have hB_zero : (0 : S) ∈ {b : S | v b < v x} := by
    change v 0 < v x
    rw [v.map_zero]; exact zero_lt_iff.mpr hx
  have hT_open : IsOpen ((· + x) '' {b | v b < v x}) :=
    (Homeomorph.addRight x).isOpenMap _ (hv (v x))
  have hT_x : x ∈ (· + x) '' {b | v b < v x} := ⟨0, hB_zero, zero_add x⟩
  refine Filter.mem_of_superset (hT_open.mem_nhds hT_x) ?_
  rintro _ ⟨b, hb, rfl⟩
  change v (b + x) = v x
  rw [add_comm b x, v.map_add_of_distinct_val (ne_of_gt hb)]
  exact max_eq_left hb.le

variable {R : Type*} [CommRing R]

private lemma le_of_isContinuous_of_denseRange_of_le {Γv Γw : Type*}
    [LinearOrderedCommGroupWithZero Γv] [LinearOrderedCommGroupWithZero Γw]
    {φ : R →+* S} (hdense : DenseRange φ)
    {v : Valuation S Γv} {w : Valuation S Γw}
    (hv : v.IsContinuous) (hw : w.IsContinuous)
    (h : ∀ a b : R, v (φ a) ≤ v (φ b) ↔ w (φ a) ≤ w (φ b))
    {x y : S} (hxy : v x ≤ v y) : w x ≤ w y := by
  have hex : ∀ (p : S) (N : Set S), N ∈ nhds p → ∃ a : R, φ a ∈ N := by
    intro p N hN
    obtain ⟨z, hzN, a, rfl⟩ := mem_closure_iff_nhds.mp (hdense p) N hN
    exact ⟨a, hzN⟩
  by_contra hwxy
  rw [not_le] at hwxy
  have hwx : w x ≠ 0 := by
    intro h0; rw [h0] at hwxy; exact absurd hwxy (not_lt.mpr zero_le)
  by_cases hvx : v x = 0
  · have hmem1 : x ∈ {z : S | v z < 1} := by change v x < 1; rw [hvx]; exact zero_lt_one
    have hN1 : {z | w z = w x} ∩ {z : S | v z < 1} ∈ nhds x :=
      Filter.inter_mem (hw.setOf_value_eq_mem_nhds hwx) ((hv 1).mem_nhds hmem1)
    obtain ⟨a₁, ha₁⟩ := hex x _ hN1
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ha₁
    obtain ⟨ha₁w, ha₁v⟩ := ha₁
    have hδ : v (φ a₁) ≠ 0 := by
      intro h0
      apply hwx
      have hiff := h a₁ 0
      simp only [map_zero, le_zero_iff] at hiff
      rw [← ha₁w]; exact hiff.mp h0
    have hmem2 : x ∈ {z : S | v z < v (φ a₁)} := by
      change v x < v (φ a₁); rw [hvx]; exact zero_lt_iff.mpr hδ
    have hN2 : {z | w z = w x} ∩ {z : S | v z < v (φ a₁)} ∈ nhds x :=
      Filter.inter_mem (hw.setOf_value_eq_mem_nhds hwx) ((hv (v (φ a₁))).mem_nhds hmem2)
    obtain ⟨a₂, ha₂⟩ := hex x _ hN2
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ha₂
    obtain ⟨ha₂w, ha₂v⟩ := ha₂
    have hww : w (φ a₁) ≤ w (φ a₂) := by rw [ha₁w, ha₂w]
    exact absurd ha₂v (not_lt.mpr ((h a₁ a₂).mpr hww))
  · have hN_a : {z | v z = v x} ∩ {z | w z = w x} ∈ nhds x :=
      Filter.inter_mem (hv.setOf_value_eq_mem_nhds hvx) (hw.setOf_value_eq_mem_nhds hwx)
    obtain ⟨a, ha⟩ := hex x _ hN_a
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at ha
    obtain ⟨ha_v, ha_w⟩ := ha
    have hvy : v y ≠ 0 := fun h0 ↦ hvx (le_antisymm (h0 ▸ hxy) zero_le)
    by_cases hwy : w y = 0
    · have hmemb : y ∈ {z : S | w z < w x} := hwxy
      have hN_b : {z | v z = v y} ∩ {z : S | w z < w x} ∈ nhds y :=
        Filter.inter_mem (hv.setOf_value_eq_mem_nhds hvy) ((hw (w x)).mem_nhds hmemb)
      obtain ⟨b, hb⟩ := hex y _ hN_b
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hb
      obtain ⟨hb_v, hb_w⟩ := hb
      have hvab : v (φ a) ≤ v (φ b) := by rw [ha_v, hb_v]; exact hxy
      have hwab : w (φ a) ≤ w (φ b) := (h a b).mp hvab
      rw [ha_w] at hwab
      exact absurd hwab (not_le.mpr hb_w)
    · have hN_b : {z | v z = v y} ∩ {z | w z = w y} ∈ nhds y :=
        Filter.inter_mem (hv.setOf_value_eq_mem_nhds hvy) (hw.setOf_value_eq_mem_nhds hwy)
      obtain ⟨b, hb⟩ := hex y _ hN_b
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hb
      obtain ⟨hb_v, hb_w⟩ := hb
      have hvab : v (φ a) ≤ v (φ b) := by rw [ha_v, hb_v]; exact hxy
      have hwab : w (φ a) ≤ w (φ b) := (h a b).mp hvab
      rw [ha_w, hb_w] at hwab
      exact absurd hwab (not_le.mpr hwxy)

/-- **Continuous valuations are determined by a dense subring** (the injectivity content of
Wedhorn Proposition 7.48 = Huber [Hu2] Prop. 3.9). If `φ : R →+* S` has dense image and two
continuous valuations `v`, `w` on `S` induce the same preorder on `φ(R)`, then `v` and `w`
are equivalent. -/
theorem isEquiv_of_isContinuous_of_denseRange {Γv Γw : Type*}
    [LinearOrderedCommGroupWithZero Γv] [LinearOrderedCommGroupWithZero Γw]
    {φ : R →+* S} (hdense : DenseRange φ)
    {v : Valuation S Γv} {w : Valuation S Γw}
    (hv : v.IsContinuous) (hw : w.IsContinuous)
    (h : ∀ a b : R, v (φ a) ≤ v (φ b) ↔ w (φ a) ≤ w (φ b)) :
    v.IsEquiv w := by
  intro x y
  exact ⟨fun hxy ↦ le_of_isContinuous_of_denseRange_of_le hdense hv hw h hxy,
         fun hxy ↦ le_of_isContinuous_of_denseRange_of_le hdense hw hv
           (fun a b ↦ (h a b).symm) hxy⟩

end Valuation

namespace ValuationSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

/-- **The point of `Spv S` is determined by a dense subring** (the injectivity content of
Wedhorn Proposition 7.48 = Huber [Hu2] Prop. 3.9). If `φ : R →+* S` has dense image and two
continuous points `v, w ∈ Spv S` have the same pullback `comap φ v = comap φ w`, then `v = w`.
This is the elementary uniqueness half of the Spa–completion comparison; it is the keystone
the completion Spa-injectivity (`comap_coeRingHom_injOn_spa`) reduces to. -/
theorem eq_of_isContinuous_of_comap_eq_of_denseRange {φ : R →+* S} (hdense : DenseRange φ)
    {v w : Spv S} (hv : v.IsContinuous) (hw : w.IsContinuous)
    (h : comap φ v = comap φ w) : v = w := by
  have bridgeV : ∀ s t : S, v.vle s t ↔
      (@ValuativeRel.valuation S _ v.toValuativeRel) s ≤
        (@ValuativeRel.valuation S _ v.toValuativeRel) t := by
    intro s t
    letI : ValuativeRel S := v.toValuativeRel
    exact (ValuativeRel.valuation S).vle_iff_le
  have bridgeW : ∀ s t : S, w.vle s t ↔
      (@ValuativeRel.valuation S _ w.toValuativeRel) s ≤
        (@ValuativeRel.valuation S _ w.toValuativeRel) t := by
    intro s t
    letI : ValuativeRel S := w.toValuativeRel
    exact (ValuativeRel.valuation S).vle_iff_le
  have hrel : ∀ a b : R, v.vle (φ a) (φ b) ↔ w.vle (φ a) (φ b) := by
    intro a b
    refine Iff.of_eq ?_
    rw [← comap_vle, ← comap_vle]; exact congrArg (fun u : Spv R ↦ u.vle a b) h
  have key : (@ValuativeRel.valuation S _ v.toValuativeRel).IsEquiv
      (@ValuativeRel.valuation S _ w.toValuativeRel) :=
    Valuation.isEquiv_of_isContinuous_of_denseRange hdense hv hw
      (fun a b ↦ by rw [← bridgeV, ← bridgeW]; exact hrel a b)
  calc v = ofValuation (@ValuativeRel.valuation S _ v.toValuativeRel) :=
            (ofValuation_valuation v).symm
    _ = ofValuation (@ValuativeRel.valuation S _ w.toValuativeRel) :=
            ofValuation_eq_of_isEquiv key
    _ = w := ofValuation_valuation w

end ValuationSpectrum
