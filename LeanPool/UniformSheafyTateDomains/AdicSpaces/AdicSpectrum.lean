/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.ContinuousValuations
import LeanPool.UniformSheafyTateDomains.AdicSpaces.GeometricSeries
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The Adic Spectrum

We define the adic spectrum `Spa(A, A⁺)` of a topological ring `A` with a subring `A⁺`,
following Definition 7.23 of [Wedhorn, *Adic Spaces*].

## Main definitions

* `PlusSubring A` : Typeclass equipping `A` with a designated subring `A⁺`.
* `Spa A Aplus` : The adic spectrum `Spa(A, A⁺)`, the set of continuous valuations on `A`
  that are bounded by `1` on `A⁺`.
* `rationalOpen T s` : A rational subset `R(T/s)` of `Spa(A, A⁺)`
  (Definition 7.29 of Wedhorn).

## Main results

* `isClosed_of_isMaximal_of_isOpen_units` : Maximal ideals are closed when the unit group
  is open.
* `isOpen_units_of_isOpen_topologicallyNilpotent` : The unit group is open when the set of
  topologically nilpotent elements is open (Prop 5.38 consequence).
* `IsTopologicallyNilpotent.mem_of_isMaximal` : Topologically nilpotent elements lie in
  every maximal ideal (Jacobson radical containment).
* `isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent` : Every maximal ideal is open when
  `A°°` is open.
* `exists_mem_spa_supp_eq` : Prop 7.51 (for open maximal ideals via trivial valuation).

## Notation

* `A⁺` (scoped in `ValuationSpectrum`) : The subring of integral elements, via `PlusSubring A`.

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], Definition 7.23, Example 7.26,
  Remark 7.28, Definition 7.29, Proposition 5.38, Proposition 7.51, Proposition 7.52
-/

open Topology Pointwise WithZero

section MaximalIdealClosed

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Every maximal ideal is closed when the unit group is open. -/
theorem isClosed_of_isMaximal_of_isOpen_units
    (hU : IsOpen {a : A | IsUnit a}) (𝔪 : Ideal A) [𝔪.IsMaximal] :
    IsClosed (𝔪 : Set A) := by
  rw [← closure_eq_iff_isClosed, ← Ideal.coe_closure]
  congr 1
  have hne : 𝔪.closure ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one]
    exact fun h1 ↦ (closure_minimal (fun x hx ↦ mt (Ideal.eq_top_of_isUnit_mem 𝔪 hx)
      (Ideal.IsMaximal.ne_top ‹_›)) hU.isClosed_compl h1) isUnit_one
  exact (Ideal.IsMaximal.eq_of_le ‹_› hne (fun x hx ↦ subset_closure hx)).symm

end MaximalIdealClosed

section OpenUnits

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A]

/-- The unit group is open when `A°°` is open (Prop 5.38). -/
theorem isOpen_units_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a}) :
    IsOpen {a : A | IsUnit a} := by
  rw [isOpen_iff_forall_mem_open]
  intro u hu
  refine ⟨(u + ·) '' {a | IsTopologicallyNilpotent a}, ?_, ?_, ?_⟩
  · rintro x ⟨a, ha, rfl⟩
    change IsUnit (_ + a)
    obtain ⟨u', rfl⟩ := (hu : IsUnit u)
    rw [show (↑u' : A) + a = ↑u' * (1 + ↑u'⁻¹ * a) by
      rw [mul_add, mul_one, ← mul_assoc, mul_comm (↑u' : A) (↑u'⁻¹ : A),
        Units.inv_mul, one_mul]]
    exact u'.isUnit.mul (ha.mul_left ↑u'⁻¹).isUnit_one_add
  · exact isOpenMap_add_left u _ hopen
  · exact ⟨0, IsTopologicallyNilpotent.zero, by simp⟩

end OpenUnits

namespace ValuationSpectrum

/-- A commutative ring equipped with a designated subring `A⁺`. -/
class PlusSubring (A : Type*) [CommRing A] where
  /-- The subring of integral elements `A⁺`. -/
  toSubring : Subring A

/-- The subring `A⁺` of integral elements. -/
def ringPlus (A : Type*) [CommRing A] [PlusSubring A] : Subring A :=
  PlusSubring.toSubring

@[inherit_doc ringPlus]
scoped postfix:max "⁺" => ringPlus

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- The *adic spectrum* `Spa(A, A⁺)` (Definition 7.23 of Wedhorn). -/
def Spa (A : Type*) [CommRing A] [TopologicalSpace A] (Aplus : Subring A) : Set (Spv A) :=
  { v ∈ Cont A | ∀ f ∈ Aplus, v.vle f 1 }

/-- `Spa` is antitone in the subring. -/
lemma spa_antitone {Aplus Aplus' : Subring A} (h : Aplus ≤ Aplus') :
    Spa A Aplus' ⊆ Spa A Aplus :=
  fun _ hv ↦ ⟨hv.1, fun f hf ↦ hv.2 f (h hf)⟩

variable [PlusSubring A]

/-- Characterization of membership in `Spa(A, A⁺)`. -/
@[simp]
lemma mem_spa_iff (v : Spv A) :
    v ∈ Spa A A⁺ ↔ v.IsContinuous ∧ ∀ f ∈ A⁺, v.vle f 1 :=
  Iff.rfl

/-- `Spa(A, A⁺)` is contained in `Cont(A)`. -/
lemma spa_subset_cont : Spa A A⁺ ⊆ Cont A :=
  fun _ hv ↦ hv.1

/-- Elements of `A⁺` satisfy `v(f) ≤ v(1)` for `v ∈ Spa(A, A⁺)`. -/
lemma vle_one_of_mem_spa {v : Spv A} (hv : v ∈ Spa A A⁺)
    {f : A} (hf : f ∈ A⁺) : v.vle f 1 :=
  hv.2 f hf

/-- `Spa(A, A⁺)` as an intersection of `Cont(A)` with valuation conditions. -/
lemma spa_eq_cont_inter :
    Spa A A⁺ = Cont A ∩ ⋂ f ∈ (A⁺ : Set A), { v : Spv A | v.vle f 1 } := by
  ext v
  simp only [Spa, Set.mem_inter_iff, mem_cont_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rfl

/-- For discrete `A`, every valuation is continuous (Example 7.26). -/
theorem spa_eq_of_discreteTopology [DiscreteTopology A] :
    Spa A A⁺ = { v : Spv A | ∀ f ∈ A⁺, v.vle f 1 } := by
  ext v
  simp only [mem_spa_iff, Set.mem_setOf_eq]
  exact ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨fun γ ↦ isOpen_discrete _, h⟩⟩

section Prop752

/-- The trivial valuation on `A/𝔪` gives a point of `Spa(A, A⁺)`
with support `𝔪` (Prop 7.51). -/
lemma exists_mem_spa_supp_eq (𝔪 : Ideal A) [𝔪.IsMaximal]
    (h𝔪 : IsOpen (𝔪 : Set A)) :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔪 := by
  classical
  haveI := Ideal.Quotient.field 𝔪
  let w : Valuation A (ℤᵐ⁰) := (1 : Valuation (A ⧸ 𝔪) _).comap (Ideal.Quotient.mk 𝔪)
  refine ⟨ofValuation w, ⟨?_, ?_⟩, ?_⟩
  · apply isContinuous_ofValuation_of
    intro γ
    by_cases hγ : γ = 0
    · subst hγ
      convert isOpen_empty
      ext a
      simp
    · by_cases h1 : (1 : ℤᵐ⁰) < γ
      · convert isOpen_univ
        ext a
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, w, Valuation.comap_apply]
        exact lt_of_le_of_lt (Valuation.one_apply_le_one _) h1
      · push Not at h1
        suffices {a : A | w a < γ} = (𝔪 : Set A) by rwa [this]
        ext a
        simp only [Set.mem_setOf_eq, w, Valuation.comap_apply]
        constructor
        · intro h
          exact Ideal.Quotient.eq_zero_iff_mem.mp
            (Valuation.one_apply_lt_one_iff.mp (lt_of_lt_of_le h h1))
        · intro ha
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
          exact zero_lt_iff.mpr hγ
  · intro f _
    change w f ≤ w 1
    simpa only [w, Valuation.comap_apply, map_one] using Valuation.one_apply_le_one _
  · rw [supp_ofValuation]
    ext a
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply,
      Valuation.one_apply_eq_zero_iff]
    exact Ideal.Quotient.eq_zero_iff_mem

/-- If `v(f) ≠ 0` for all `v ∈ Spa(A, A⁺)`, then `f` is a unit (Prop 7.52(2)). -/
lemma isUnit_of_forall_not_vle_zero
    (hmax : ∀ (𝔪 : Ideal A), 𝔪.IsMaximal → IsOpen (𝔪 : Set A))
    {f : A} (h : ∀ v ∈ Spa A A⁺, ¬ v.vle f 0) : IsUnit f := by
  by_contra hf
  obtain ⟨𝔪, h𝔪, hf𝔪⟩ :=
    Ideal.exists_le_maximal (Ideal.span {f}) (Ideal.span_singleton_ne_top hf)
  haveI := h𝔪
  obtain ⟨v, hv, hsv⟩ := exists_mem_spa_supp_eq 𝔪 (hmax 𝔪 h𝔪)
  exact h v hv ((v.mem_supp_iff f).mp (hsv ▸ hf𝔪 (Ideal.mem_span_singleton_self f)))

/-- The trivial valuation on `Frac(A/p)` gives a point of `Spa(A, A⁺)` (discrete case). -/
lemma exists_mem_spa_supp_eq_of_prime [DiscreteTopology A]
    (p : Ideal A) [p.IsPrime] :
    ∃ v ∈ Spa A A⁺, v.supp = p := by
  classical
  haveI : IsDomain (A ⧸ p) := Ideal.Quotient.isDomain p
  let φ : A →+* FractionRing (A ⧸ p) :=
    (algebraMap (A ⧸ p) (FractionRing (A ⧸ p))).comp (Ideal.Quotient.mk p)
  let w : Valuation A ℤᵐ⁰ := (1 : Valuation (FractionRing (A ⧸ p)) _).comap φ
  refine ⟨ofValuation w, ⟨?_, ?_⟩, ?_⟩
  · exact isContinuous_ofValuation_of _ (fun _ ↦ isOpen_discrete _)
  · intro f _
    change w f ≤ w 1
    simpa only [w, Valuation.comap_apply, map_one] using Valuation.one_apply_le_one _
  · rw [supp_ofValuation]
    ext a
    simp only [Valuation.mem_supp_iff, w, Valuation.comap_apply, φ, RingHom.comp_apply,
      Valuation.one_apply_eq_zero_iff]
    exact ⟨fun h ↦ Ideal.Quotient.eq_zero_iff_mem.mp
      ((IsFractionRing.injective (A ⧸ p) (FractionRing (A ⧸ p))).eq_iff.mp
        (by rwa [map_zero])),
      fun ha ↦ by rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]⟩

end Prop752

/-- A rational subset `R(T/s)` of `Spa(A, A⁺)` (Definition 7.29). -/
def rationalOpen (T : Finset A) (s : A) : Set (Spv A) :=
  { v ∈ Spa A A⁺ | (∀ t ∈ T, v.vle t s) ∧ ¬ v.vle s 0 }

/-- A rational subset is contained in `Spa(A, A⁺)`. -/
lemma rationalOpen_subset_spa {T : Finset A} {s : A} :
    rationalOpen T s ⊆ Spa A A⁺ :=
  fun _ hv ↦ hv.1

/-- A rational subset as an intersection of basic opens with `Spa`. -/
lemma rationalOpen_eq_spa_inter {T : Finset A} (hT : T.Nonempty) (s : A) :
    rationalOpen T s = Spa A A⁺ ∩ ⋂ t ∈ (T : Set A), basicOpen t s := by
  ext v
  simp only [rationalOpen, Set.mem_inter_iff, Set.mem_iInter,
    basicOpen, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hv, hvT, hvs⟩
    exact ⟨hv, fun t ht ↦ ⟨hvT t ht, hvs⟩⟩
  · rintro ⟨hv, hvT⟩
    obtain ⟨t₀, ht₀⟩ := hT
    exact ⟨hv, fun t ht ↦ (hvT t ht).1, (hvT t₀ ht₀).2⟩

section Functoriality

variable {B : Type*} [CommRing B] [TopologicalSpace B] [PlusSubring B]

/-- `Spa(φ)` via `comap` (Remark 7.28). -/
theorem comap_mem_spa {φ : A →+* B} (hφ : Continuous φ)
    (hAB : A⁺ ≤ (B⁺).comap φ)
    {v : Spv B} (hv : v ∈ Spa B B⁺) :
    comap φ v ∈ Spa A A⁺ := by
  refine ⟨comap_isContinuous hφ hv.1, fun f hf ↦ ?_⟩
  simpa only [comap_vle, map_one] using hv.2 (φ f) (hAB hf)

/-- `comap φ` maps `Spa(B, B⁺)` into `Spa(A, A⁺)` (Remark 7.28). -/
theorem spa_comap_mapsTo {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ) :
    Set.MapsTo (comap φ) (Spa B B⁺) (Spa A A⁺) :=
  fun _ hv ↦ comap_mem_spa hφ hAB hv

/-- The continuous map `Spa(φ)` (Remark 7.28). -/
def spaComap {φ : A →+* B} (hφ : Continuous φ) (hAB : A⁺ ≤ (B⁺).comap φ) :
    C(↥(Spa B B⁺), ↥(Spa A A⁺)) where
  toFun := (spa_comap_mapsTo hφ hAB).restrict _ _ _
  continuous_toFun :=
    (comap_continuous φ).restrict (spa_comap_mapsTo hφ hAB)

end Functoriality

section SubspaceTopology

variable {A : Type*} [CommRing A] [TopologicalSpace A] [PlusSubring A]

omit [PlusSubring A] in
/-- `↥(Cont A) ↪ Spv A` is a topological embedding. -/
theorem cont_subtypeVal_isEmbedding :
    Topology.IsEmbedding (Subtype.val : ↥(Cont A) → Spv A) :=
  Topology.IsEmbedding.subtypeVal

/-- `↥(Spa A A⁺) ↪ Spv A` is a topological embedding. -/
theorem spa_subtypeVal_isEmbedding :
    Topology.IsEmbedding (Subtype.val : ↥(Spa A A⁺) → Spv A) :=
  Topology.IsEmbedding.subtypeVal

/-- `↥(Spa A A⁺) → ↥(Cont A)` is continuous. -/
theorem continuous_spa_inclusion :
    Continuous (Set.inclusion spa_subset_cont : ↥(Spa A A⁺) → ↥(Cont A)) :=
  continuous_inclusion spa_subset_cont

/-- `↥(Spa A A⁺) ↪ ↥(Cont A)` is a topological embedding. -/
theorem spa_inclusion_isEmbedding :
    Topology.IsEmbedding (Set.inclusion spa_subset_cont : ↥(Spa A A⁺) → ↥(Cont A)) :=
  Topology.IsEmbedding.mk
    (Topology.IsInducing.of_comp (continuous_inclusion spa_subset_cont)
      continuous_subtype_val Topology.IsInducing.subtypeVal)
    (Set.inclusion_injective spa_subset_cont)

end SubspaceTopology

end ValuationSpectrum

section TopNilMaximal

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A]

/-- Topologically nilpotent elements lie in every maximal ideal. -/
theorem IsTopologicallyNilpotent.mem_of_isMaximal {a : A}
    (ha : IsTopologicallyNilpotent a) (𝔪 : Ideal A) [𝔪.IsMaximal] : a ∈ 𝔪 := by
  by_contra ha𝔪
  have htop : 𝔪 ⊔ Ideal.span {a} = ⊤ := by
    by_contra h
    exact ha𝔪 ((Ideal.IsMaximal.eq_of_le ‹_› h le_sup_left).ge
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)))
  rw [Ideal.eq_top_iff_one] at htop
  obtain ⟨m, hm, n, hn, hmn⟩ := Submodule.mem_sup.mp htop
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hn
  exact Ideal.IsMaximal.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem 𝔪 hm
    (eq_sub_of_add_eq hmn ▸ (ha.mul_left r).isUnit_one_sub))

/-- Every maximal ideal is open when `A°°` is open. -/
theorem isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    (𝔪 : Ideal A) [𝔪.IsMaximal] : IsOpen (𝔪 : Set A) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨(x + ·) '' {a | IsTopologicallyNilpotent a}, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact 𝔪.add_mem hx (ha.mem_of_isMaximal 𝔪)
  · exact isOpenMap_add_left x _ hopen
  · exact ⟨0, IsTopologicallyNilpotent.zero, by simp⟩

end TopNilMaximal

section Prop752Full

variable {A : Type*} [CommRing A]
  [UniformSpace A] [T2Space A] [CompleteSpace A]
  [IsTopologicalRing A] [IsUniformAddGroup A] [NonarchimedeanAddGroup A]
  [IsLinearTopology A A] [ValuationSpectrum.PlusSubring A]

open ValuationSpectrum

/-- Prop 7.51 with f-adic hypotheses. -/
theorem ValuationSpectrum.exists_mem_spa_supp_eq_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    (𝔪 : Ideal A) [𝔪.IsMaximal] :
    ∃ v ∈ Spa A A⁺, v.supp = 𝔪 :=
  exists_mem_spa_supp_eq 𝔪
    (isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent hopen 𝔪)

/-- Prop 7.52(2) with f-adic hypotheses. -/
theorem ValuationSpectrum.isUnit_of_forall_not_vle_zero_of_isOpen_topologicallyNilpotent
    (hopen : IsOpen {a : A | IsTopologicallyNilpotent a})
    {f : A} (h : ∀ v ∈ Spa A A⁺, ¬ v.vle f 0) : IsUnit f :=
  isUnit_of_forall_not_vle_zero
    (fun 𝔪 h𝔪 ↦ letI := h𝔪;
      isOpen_of_isMaximal_of_isOpen_topologicallyNilpotent hopen 𝔪)
    h

end Prop752Full
