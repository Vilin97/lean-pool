/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. The mapping degree, positivity/bounds, degree-1 ⇒ homeomorphism,
and the (statement-bank) multiplicativity of degree under composition.
-/
import LeanPool.JacobianDiffgeo.MappingDegree.Ramification
import LeanPool.JacobianDiffgeo.MappingDegree.LocalConstancy
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The mapping degree

* `RS.degree F : ℕ` — total multiplicity of `F` over an arbitrary basepoint of `Y`; well-defined
  (basepoint-independent) by `RS.fiberMultSum_eq_degree`; `0` for constant maps
  (`RS.degree_of_forall_eq`).
* Positivity/bounds: `RS.one_le_degree`, `RS.degree_pos_iff`, `RS.multiplicity_le_degree`.
* Regular-fiber cardinality: `RS.ncard_fiber_of_isRegularValue`, `RS.ncard_fiber_le_degree`.
* Degree-1 ⇒ bijective ⇒ homeomorphism (genus-zero-headline / Abel bank):
  `RS.bijective_of_degree_eq_one`, `RS.homeomorphOfDegreeEqOne`,
  `RS.coe_homeomorphOfDegreeEqOne`, `RS.isHomeomorph_of_degree_eq_one`.
* `RS.degree_comp` — degree of a composition is multiplicative (needs the extra instance
  `[CompactSpace Y]`, the only statement in the unit that does).
-/

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

section DegreeDef

variable [Nonempty Y]

/-- The mapping degree: total multiplicity of `F` over an arbitrary basepoint of `Y`.
Well-defined (basepoint-independent) by `fiberMultSum_eq_degree`; `0` for constant maps
(`degree_of_forall_eq`). -/
noncomputable def degree (F : X → Y) : ℕ := fiberMultSum F (Classical.arbitrary Y)

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω Y] in
theorem degree_def (F : X → Y) : degree F = fiberMultSum F (Classical.arbitrary Y) := rfl

omit [T2Space X] [CompactSpace X] [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X] [T2Space Y]
  [IsManifold 𝓘(ℂ) ω Y] in
/-- Junk convention: constant maps have `degree ≡ 0`. -/
theorem degree_of_forall_eq (c : Y) : degree (fun _ : X ↦ c) = 0 := by
  rw [degree_def, fiberMultSum_of_forall_eq]

end DegreeDef

variable [ConnectedSpace Y]

/-- THE well-definedness statement in `degree` form: the fiber-sum over any `y` is the degree. -/
theorem fiberMultSum_eq_degree (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : fiberMultSum F y = degree F :=
  fiberMultSum_const hF hne y (Classical.arbitrary Y)

theorem degree_eq_fiberMultSum (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : degree F = ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x :=
  (fiberMultSum_eq_degree hF hne y).symm

omit [T2Space X] in
theorem one_le_degree (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c) :
    1 ≤ degree F := by
  rw [degree_def]
  exact one_le_fiberMultSum hF hne _

omit [T2Space X] in
/-- `degree F` is positive exactly when `F` is nonconstant. -/
theorem degree_pos_iff (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) :
    0 < degree F ↔ ¬ ∃ c, ∀ x, F x = c := by
  constructor
  · rintro hpos ⟨c, hc⟩
    have hFeq : F = fun _ : X ↦ c := funext hc
    rw [hFeq, degree_of_forall_eq] at hpos
    exact lt_irrefl 0 hpos
  · intro hne
    exact one_le_degree hF hne

theorem multiplicity_le_degree (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (x : X) : multiplicity F x ≤ degree F := by
  rw [← fiberMultSum_eq_degree hF hne (F x)]
  exact multiplicity_le_fiberMultSum hF hne

/-- Fiber cardinality equals the degree over regular values (every fiber point has
multiplicity exactly `1`). -/
theorem ncard_fiber_of_isRegularValue (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) {y : Y} (hy : IsRegularValue F y) :
    (F ⁻¹' {y}).ncard = degree F := by
  have hfin := fiber_finite hF hne y
  have heq : ∀ x ∈ hfin.toFinset, multiplicity F x = 1 := fun x hx ↦
    multiplicity_eq_one_of_isRegularValue hF hne hy (hfin.mem_toFinset.mp hx)
  rw [Set.ncard_eq_toFinset_card _ hfin, ← fiberMultSum_eq_degree hF hne y,
    fiberMultSum_eq_finset_sum hfin, Finset.sum_congr rfl heq, Finset.sum_const, smul_eq_mul,
    mul_one]

/-- In general (branch values included), fiber cardinality is at most the degree. -/
theorem ncard_fiber_le_degree (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F) (hne : ¬ ∃ c, ∀ x, F x = c)
    (y : Y) : (F ⁻¹' {y}).ncard ≤ degree F := by
  have hfin := fiber_finite hF hne y
  rw [Set.ncard_eq_toFinset_card _ hfin, ← fiberMultSum_eq_degree hF hne y,
    fiberMultSum_eq_finset_sum hfin]
  calc hfin.toFinset.card = ∑ _x ∈ hfin.toFinset, 1 := by
        rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ x ∈ hfin.toFinset, multiplicity F x :=
        Finset.sum_le_sum (fun x _ ↦ one_le_multiplicity_of_not_const hF hne x)

/-! ### Degree `1` ⇒ bijective ⇒ homeomorphism (genus-zero-headline / Abel bank) -/

/-- Degree `1` forces bijectivity: surjectivity is automatic (nonconstant on connected `X`);
injectivity fails only if some fiber has `≥ 2` points, forcing `fiberMultSum ≥ 2 > 1`. -/
theorem bijective_of_degree_eq_one (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (h1 : degree F = 1) : Function.Bijective F := by
  classical
  refine ⟨?_, surjective_of_not_const' hF hne⟩
  intro x₁ x₂ hFx
  by_contra hxne
  set y := F x₁ with hy_def
  have hfin := fiber_finite hF hne y
  have hx1mem : x₁ ∈ hfin.toFinset := hfin.mem_toFinset.mpr rfl
  have hx2mem : x₂ ∈ hfin.toFinset := hfin.mem_toFinset.mpr hFx.symm
  have hsub : ({x₁, x₂} : Finset X) ⊆ hfin.toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hx1mem
    · exact hx2mem
  have hcard : ({x₁, x₂} : Finset X).card = 2 := Finset.card_pair hxne
  have hconst : (∑ _x ∈ ({x₁, x₂} : Finset X), (1 : ℕ)) = 2 := by
    rw [Finset.sum_const, hcard, smul_eq_mul, mul_one]
  have h2le : (2 : ℕ) ≤ ∑ x ∈ hfin.toFinset, multiplicity F x :=
    calc (2 : ℕ) = ∑ _x ∈ ({x₁, x₂} : Finset X), (1 : ℕ) := hconst.symm
      _ ≤ ∑ x ∈ ({x₁, x₂} : Finset X), multiplicity F x :=
          Finset.sum_le_sum (fun z _ ↦ one_le_multiplicity_of_not_const hF hne z)
      _ ≤ ∑ x ∈ hfin.toFinset, multiplicity F x := Finset.sum_le_sum_of_subset hsub
  rw [← fiberMultSum_eq_finset_sum hfin, fiberMultSum_eq_degree hF hne, h1] at h2le
  omega

/-- The homeomorphism witnessed by a degree-`1` map (compact source, T2 target,
continuous bijection). -/
noncomputable def homeomorphOfDegreeEqOne (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (h1 : degree F = 1) : X ≃ₜ Y :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective F (bijective_of_degree_eq_one hF hne h1)) hF.continuous

theorem coe_homeomorphOfDegreeEqOne (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (h1 : degree F = 1) :
    ⇑(homeomorphOfDegreeEqOne hF hne h1) = F := rfl

theorem isHomeomorph_of_degree_eq_one (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hne : ¬ ∃ c, ∀ x, F x = c) (h1 : degree F = 1) : IsHomeomorph F :=
  isHomeomorph_iff_exists_homeomorph.mpr
    ⟨homeomorphOfDegreeEqOne hF hne h1, coe_homeomorphOfDegreeEqOne hF hne h1⟩

/-! ### `degree_comp` (statement bank; no critical downstream consumer) -/

/-- Degree is multiplicative under composition. The only statement in the unit needing the
extra instance `[CompactSpace Y]` (finiteness of `G`'s fibers). -/
theorem degree_comp {Z : Type*} [TopologicalSpace Z] [T2Space Z] [ConnectedSpace Z]
    [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z] [CompactSpace Y]
    {G : Y → Z} (hG : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω G) (hF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F)
    (hneG : ¬ ∃ c, ∀ y, G y = c) (hneF : ¬ ∃ c, ∀ x, F x = c) :
    degree (G ∘ F) = degree G * degree F := by
  have hneGF : ¬ ∃ c, ∀ x, (G ∘ F) x = c := by
    rintro ⟨c, hc⟩
    apply hneG
    refine ⟨c, fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := surjective_of_not_const' hF hneF y
    have h := hc x
    simp only [Function.comp_apply, hx] at h
    exact h
  have hGF : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (G ∘ F) := hG.comp hF
  set z₀ : Z := Classical.arbitrary Z
  have hIfin : (G ⁻¹' {z₀}).Finite := fiber_finite hG hneG z₀
  have hunion : (G ∘ F) ⁻¹' {z₀} = ⋃ y ∈ G ⁻¹' {z₀}, F ⁻¹' {y} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact Set.mem_biUnion hx rfl
    · intro x hx
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp hx
      have hxy' : F x = y := hxy
      change G (F x) = z₀
      rw [hxy']
      exact hy
  have hdisj : (G ⁻¹' {z₀}).PairwiseDisjoint (fun y ↦ F ⁻¹' {y}) := by
    intro y₁ _ y₂ _ hy12
    change Disjoint (F ⁻¹' {y₁}) (F ⁻¹' {y₂})
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hy12 (hx1.symm.trans hx2)
  have hFfin : ∀ y ∈ G ⁻¹' {z₀}, (F ⁻¹' {y}).Finite := fun y _ ↦ fiber_finite hF hneF y
  rw [degree_eq_fiberMultSum hGF hneGF z₀, hunion, finsum_mem_biUnion hdisj hIfin hFfin]
  have hstep1 : ∀ y ∈ G ⁻¹' {z₀},
      (∑ᶠ x ∈ F ⁻¹' {y}, multiplicity (G ∘ F) x) = multiplicity G y * degree F := by
    intro y hy
    have hfinFy := fiber_finite hF hneF y
    rw [finsum_mem_eq_finite_toFinset_sum _ hfinFy]
    have hpt : ∀ x ∈ hfinFy.toFinset,
        multiplicity (G ∘ F) x = multiplicity G y * multiplicity F x := by
      intro x hx
      have hxy : F x = y := hfinFy.mem_toFinset.mp hx
      rw [← hxy]
      exact multiplicity_comp (hG (F x)) (hF x)
    rw [Finset.sum_congr rfl hpt, ← Finset.mul_sum, ← fiberMultSum_eq_finset_sum hfinFy,
      fiberMultSum_eq_degree hF hneF y]
  rw [finsum_mem_congr rfl hstep1, finsum_mem_eq_finite_toFinset_sum _ hIfin, ← Finset.sum_mul,
    ← fiberMultSum_eq_finset_sum hIfin, fiberMultSum_eq_degree hG hneG z₀]

end RS
