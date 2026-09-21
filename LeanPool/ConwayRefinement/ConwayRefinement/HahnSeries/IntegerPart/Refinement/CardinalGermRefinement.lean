/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Algebra.Order.ArchimedeanQuotient
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.IntegerPart.Refinement.CompleteGermRefinement
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEmbedding
public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.SmallClosedSubspace
public import Mathlib.RingTheory.HahnSeries.Cardinal
public import Mathlib.SetTheory.Cardinal.Regular

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint

/-!
# Cardinal-bounded germ refinement

Four cardinal-bounded generalised power series and a cardinal-bounded positive coinitial family
lie in one Cauchy-complete closed rational subspace. Germ refinement inside that subspace produces
factors with well-ordered support. Although the subspace itself may be large, density of the
original rational span bounds each such support by the prescribed cardinal.
-/

open Cardinal Set
open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries.Nonpositive

variable {C : Type u} {K : Type v}
variable [AddCommGroup C] [LinearOrder C] [IsOrderedAddMonoid C]
  [UniformSpace C] [IsUniformAddGroup C] [OrderTopology C] [Nontrivial C] [CompleteSpace C]
  [Field K] [CharZero K]

private theorem exists_mapDomain_germ_eq
    {D : Type u}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [UniformSpace D] [IsUniformAddGroup D] [OrderTopology D] [Nontrivial D] [CompleteSpace D]
    (inc : D →+ C) (hinc : Function.Injective inc)
    (hincOrder : ∀ x y : D, inc x ≤ inc y ↔ x ≤ y)
    (x y : Nonpositive D K)
    (hxy : ∃ r < (0 : D), ∀ q > r,
      (x : HahnSeries D K).coeff q = (y : HahnSeries D K).coeff q) :
    ∃ r < (0 : C), ∀ q > r,
      (mapDomain inc hinc hincOrder x : HahnSeries C K).coeff q =
        (mapDomain inc hinc hincOrder y : HahnSeries C K).coeff q := by
  let JD := (cantorBendixsonValuation (G := D) (R := K)).supp
  let JC := (cantorBendixsonValuation (G := C) (R := K)).supp
  have mapMemSupp (z : Nonpositive D K) (hz : z ∈ JD) :
      mapDomain inc hinc hincOrder z ∈ JC := by
    rw [mem_cantorBendixsonValuation_supp] at hz ⊢
    obtain ⟨r, hr, hzr⟩ := hz
    refine ⟨inc r, ?_, ?_⟩
    · have hle : inc r ≤ inc 0 := (hincOrder r 0).mpr hr.le
      rw [map_zero] at hle
      exact lt_of_le_of_ne hle (fun h ↦ hr.ne (hinc (by simpa using h)))
    rw [support_mapDomain]
    rintro _ ⟨q, hq, rfl⟩
    exact (hincOrder q r).mpr (hzr hq)
  apply cantorBendixson_germ_eq_iff _ _ |>.mp
  apply Ideal.Quotient.eq.mpr
  change mapDomain inc hinc hincOrder x - mapDomain inc hinc hincOrder y ∈ JC
  rw [← map_sub]
  exact mapMemSupp _
    (Ideal.Quotient.eq.mp (cantorBendixson_germ_eq_iff x y |>.mpr hxy))

private theorem mapDomain_refinement
    {D : Type u}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [UniformSpace D] [IsUniformAddGroup D] [OrderTopology D] [Nontrivial D] [CompleteSpace D]
    (inc : D →+ C) (hinc : Function.Injective inc)
    (hincOrder : ∀ x y : D, inc x ≤ inc y ↔ x ≤ y)
    (a b c d e f g h : Nonpositive D K)
    (hea : ∃ r < (0 : D), ∀ q > r,
      (a : HahnSeries D K).coeff q = (e * f : Nonpositive D K).1.coeff q)
    (heb : ∃ r < (0 : D), ∀ q > r,
      (b : HahnSeries D K).coeff q = (g * h : Nonpositive D K).1.coeff q)
    (hec : ∃ r < (0 : D), ∀ q > r,
      (c : HahnSeries D K).coeff q = (e * g : Nonpositive D K).1.coeff q)
    (hed : ∃ r < (0 : D), ∀ q > r,
      (d : HahnSeries D K).coeff q = (f * h : Nonpositive D K).1.coeff q) :
    (∃ r < (0 : C), ∀ q > r,
      (mapDomain inc hinc hincOrder a : HahnSeries C K).coeff q =
        (mapDomain inc hinc hincOrder (e * f) : HahnSeries C K).coeff q) ∧
    (∃ r < (0 : C), ∀ q > r,
      (mapDomain inc hinc hincOrder b : HahnSeries C K).coeff q =
        (mapDomain inc hinc hincOrder (g * h) : HahnSeries C K).coeff q) ∧
    (∃ r < (0 : C), ∀ q > r,
      (mapDomain inc hinc hincOrder c : HahnSeries C K).coeff q =
        (mapDomain inc hinc hincOrder (e * g) : HahnSeries C K).coeff q) ∧
    ∃ r < (0 : C), ∀ q > r,
      (mapDomain inc hinc hincOrder d : HahnSeries C K).coeff q =
        (mapDomain inc hinc hincOrder (f * h) : HahnSeries C K).coeff q :=
  ⟨exists_mapDomain_germ_eq inc hinc hincOrder a (e * f) hea,
    exists_mapDomain_germ_eq inc hinc hincOrder b (g * h) heb,
    exists_mapDomain_germ_eq inc hinc hincOrder c (e * g) hec,
    exists_mapDomain_germ_eq inc hinc hincOrder d (f * h) hed⟩

private theorem exists_cardinal_refinement_mapDomain
    {D : Type u} {κ : Cardinal.{u}}
    [AddCommGroup D] [LinearOrder D] [IsOrderedAddMonoid D]
    [UniformSpace D] [IsUniformAddGroup D] [OrderTopology D] [Nontrivial D] [CompleteSpace D]
    (inc : D →+ C) (hinc : Function.Injective inc)
    (hincOrder : ∀ x y : D, inc x ≤ inc y ↔ x ≤ y)
    (hDsupport : ∀ z : Nonpositive D K,
      (z : HahnSeries D K).cardSupp < κ)
    (a b c d : Nonpositive C K) (a₀ b₀ c₀ d₀ e₀ f₀ g₀ h₀ : Nonpositive D K)
    (ha₀ : mapDomain inc hinc hincOrder a₀ = a)
    (hb₀ : mapDomain inc hinc hincOrder b₀ = b)
    (hc₀ : mapDomain inc hinc hincOrder c₀ = c)
    (hd₀ : mapDomain inc hinc hincOrder d₀ = d)
    (hea : ∃ r < (0 : D), ∀ q > r,
      (a₀ : HahnSeries D K).coeff q = (e₀ * f₀ : Nonpositive D K).1.coeff q)
    (heb : ∃ r < (0 : D), ∀ q > r,
      (b₀ : HahnSeries D K).coeff q = (g₀ * h₀ : Nonpositive D K).1.coeff q)
    (hec : ∃ r < (0 : D), ∀ q > r,
      (c₀ : HahnSeries D K).coeff q = (e₀ * g₀ : Nonpositive D K).1.coeff q)
    (hed : ∃ r < (0 : D), ∀ q > r,
      (d₀ : HahnSeries D K).coeff q = (f₀ * h₀ : Nonpositive D K).1.coeff q) :
    ∃ e f g h : Nonpositive C K,
      (∃ r < (0 : C), ∀ q > r,
        (a : HahnSeries C K).coeff q = (e * f : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (b : HahnSeries C K).coeff q = (g * h : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (c : HahnSeries C K).coeff q = (e * g : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (d : HahnSeries C K).coeff q = (f * h : Nonpositive C K).1.coeff q) ∧
      (e : HahnSeries C K).cardSupp < κ ∧
      (f : HahnSeries C K).cardSupp < κ ∧
      (g : HahnSeries C K).cardSupp < κ ∧
      (h : HahnSeries C K).cardSupp < κ := by
  let e := mapDomain inc hinc hincOrder e₀
  let f := mapDomain inc hinc hincOrder f₀
  let g := mapDomain inc hinc hincOrder g₀
  let h := mapDomain inc hinc hincOrder h₀
  have cardMap (z : Nonpositive D K) :
      (mapDomain inc hinc hincOrder z : HahnSeries C K).cardSupp < κ := by
    rw [HahnSeries.cardSupp, support_mapDomain]
    exact Cardinal.mk_image_le.trans_lt (by
      simpa only [HahnSeries.cardSupp] using hDsupport z)
  obtain ⟨hea', heb', hec', hed'⟩ :=
    mapDomain_refinement inc hinc hincOrder a₀ b₀ c₀ d₀ e₀ f₀ g₀ h₀ hea heb hec hed
  refine ⟨e, f, g, h, ?_, ?_, ?_, ?_, cardMap e₀, cardMap f₀, cardMap g₀, cardMap h₀⟩
  · simpa only [ha₀, map_mul] using hea'
  · simpa only [hb₀, map_mul] using heb'
  · simpa only [hc₀, map_mul] using hec'
  · simpa only [hd₀, map_mul] using hed'

variable [Module ℚ C] [PosSMulMono ℚ C] [DenselyOrdered C]
  [NoMaxOrder (FiniteArchimedeanClass C)]

/-- Cauchy-complete germ refinement preserves a cardinal support bound. -/
@[blueprint "thm:cardinal-bounded-germ-refinement"
  (phase := "Refinement over Archimedean classes")
  (title := "Cardinal-bounded refinement modulo series bounded away from zero")
  (statement := /--
    Let $C$ be an ordered rational vector space that is Cauchy complete for its
    additive uniformity and whose nonzero Archimedean classes have no least
    element in the magnitude order.  Let $K$ be a field of characteristic zero
    and let $\kappa>\aleph_0$.  If $C$ has a positive coinitial subset of
    cardinality less than $\kappa$, then every equation $ab=cd$ among four
    $\kappa$-bounded series in $K((C^{\le 0}))$ admits a four-factor refinement
    modulo series bounded strictly below zero whose four factors are also
    $\kappa$-bounded.
  -/)
  (proof := /--
    Put the supports of $a,b,c,d$ and the chosen positive coinitial set into
    one closed rational subspace $C_0$.
    The coinitial set remains positive and coinitial in $C_0$; hence $C_0$ is
    nontrivial, has no endpoints, and its nonzero Archimedean classes have no
    least element in the magnitude order.  As a closed subspace of $C$, it is
    Cauchy complete for its additive uniformity, and its induced order topology
    and rational vector-space structure satisfy the remaining hypotheses of
    \ref{thm:complete-hahn-germ-refinement}.  Apply that theorem over $C_0$,
    and then map the four factors back to $C$.  Each factor has well-ordered
    support in $C_0$.  By
    \ref{lem:well-ordered-subset-closed-rational-span-cardinality}, such a
    support has cardinality less than $\kappa$.
  -/)]
theorem exists_cardinal_germ_refinement
    {κ : Cardinal.{u}} [Fact (ℵ₀ < κ)]
    (E : Set C) (hEcard : #E < κ)
    (hEcoinitial : ∀ y : C, 0 < y → ∃ x ∈ E, 0 < x ∧ x ≤ y)
    (a b c d : Nonpositive C K)
    (ha : (a : HahnSeries C K).cardSupp < κ)
    (hb : (b : HahnSeries C K).cardSupp < κ)
    (hc : (c : HahnSeries C K).cardSupp < κ)
    (hd : (d : HahnSeries C K).cardSupp < κ)
    (habcd : a * b = c * d) :
    ∃ e f g h : Nonpositive C K,
      (∃ r < (0 : C), ∀ q > r,
        (a : HahnSeries C K).coeff q = (e * f : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (b : HahnSeries C K).coeff q = (g * h : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (c : HahnSeries C K).coeff q = (e * g : Nonpositive C K).1.coeff q) ∧
      (∃ r < (0 : C), ∀ q > r,
        (d : HahnSeries C K).coeff q = (f * h : Nonpositive C K).1.coeff q) ∧
      (e : HahnSeries C K).cardSupp < κ ∧
      (f : HahnSeries C K).cardSupp < κ ∧
      (g : HahnSeries C K).cardSupp < κ ∧
      (h : HahnSeries C K).cardSupp < κ := by
  let S : Set C :=
    (a : HahnSeries C K).support ∪ (b : HahnSeries C K).support ∪
      (c : HahnSeries C K).support ∪ (d : HahnSeries C K).support ∪ E
  have hκ : ℵ₀ ≤ κ := (Fact.out : ℵ₀ < κ).le
  have hS : #S < κ := by
    have ha' : #(a : HahnSeries C K).support < κ := by
      simpa only [HahnSeries.cardSupp] using ha
    have hb' : #(b : HahnSeries C K).support < κ := by
      simpa only [HahnSeries.cardSupp] using hb
    have hc' : #(c : HahnSeries C K).support < κ := by
      simpa only [HahnSeries.cardSupp] using hc
    have hd' : #(d : HahnSeries C K).support < κ := by
      simpa only [HahnSeries.cardSupp] using hd
    exact (Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ
      ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ
        ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ
          ((Cardinal.mk_union_le _ _).trans_lt (Cardinal.add_lt_of_lt hκ ha' hb')) hc')) hd'))
      hEcard)
  let C₀ := (Submodule.span ℚ S).topologicalClosure
  let inc : C₀ →+ C := C₀.subtype
  have hinc : Function.Injective inc := Subtype.val_injective
  have hincOrder : ∀ x y : C₀, inc x ≤ inc y ↔ x ≤ y := fun _ _ ↦ Iff.rfl
  have hcoinitial : ∀ y : C, 0 < y → ∃ x : C₀, 0 < (x : C) ∧ (x : C) ≤ y := by
    intro y hy
    obtain ⟨x, hxE, hx, hxy⟩ := hEcoinitial y hy
    have hxS : x ∈ S := by
      exact Or.inr hxE
    exact ⟨⟨x, (Submodule.span ℚ S).le_topologicalClosure
      (Submodule.subset_span hxS)⟩, hx, hxy⟩
  let y : C := Classical.choose (exists_ne (0 : C))
  have hy : y ≠ 0 := Classical.choose_spec (exists_ne (0 : C))
  have habsy : 0 < |y| := abs_pos.mpr hy
  have hSne : S.Nonempty := by
    obtain ⟨x, hxE, -⟩ := hEcoinitial |y| habsy
    exact ⟨x, Or.inr hxE⟩
  letI : NoMaxOrder (FiniteArchimedeanClass C₀) :=
    AddSubgroup.finiteArchimedeanClass_noMax_of_pos_coinitial C₀.toAddSubgroup hcoinitial
  letI : NoMinOrder C₀ := ⟨fun x ↦ by
    obtain ⟨z, hz, -⟩ := hcoinitial |y| habsy
    exact ⟨x - z, sub_lt_self x hz⟩⟩
  letI : NoMaxOrder C₀ := ⟨fun x ↦ by
    obtain ⟨z, hz, -⟩ := hcoinitial |y| habsy
    exact ⟨x + z, lt_add_of_pos_right x hz⟩⟩
  letI : OrderTopology C₀ := by
    apply induced_orderTopology' (fun z : C₀ ↦ (z : C)) (fun {_ _} ↦ Iff.rfl)
    · intro x y hyx
      obtain ⟨z, hzpos, hzle⟩ := hcoinitial ((x : C) - y) (sub_pos.mpr hyx)
      refine ⟨x - z, sub_lt_self x hzpos, ?_⟩
      simpa [sub_le_iff_le_add] using sub_le_sub_left hzle (x : C)
    · intro x y hxy
      obtain ⟨z, hzpos, hzle⟩ := hcoinitial (y - (x : C)) (sub_pos.mpr hxy)
      refine ⟨x + z, lt_add_of_pos_right x hzpos, ?_⟩
      change (x : C) + (z : C) ≤ y
      rw [add_comm]
      exact le_sub_iff_add_le.mp hzle
  letI : PosSMulMono ℚ C₀ := {
    smul_le_smul_of_nonneg_left := fun {q} hq {_ _} hxy ↦
      smul_le_smul_of_nonneg_left (α := ℚ) (β := C) hxy hq }
  letI : PosSMulStrictMono ℚ C₀ :=
    PosSMulMono.toPosSMulStrictMono (α := ℚ) (β := C₀)
  letI : DenselyOrdered C₀ := by
    constructor
    intro x y hxy
    refine ⟨(2 : ℚ)⁻¹ • (x + y), ?_, ?_⟩
    · calc
        x = (2 : ℚ)⁻¹ • (x + x) := by rw [smul_add, ← add_smul]; norm_num
        _ < (2 : ℚ)⁻¹ • (x + y) := smul_lt_smul_of_pos_left
          (add_lt_add_left hxy x |>.trans_eq (add_comm _ _)) (by norm_num)
    · calc
        (2 : ℚ)⁻¹ • (x + y) < (2 : ℚ)⁻¹ • (y + y) :=
          smul_lt_smul_of_pos_left
            (by simpa [add_comm] using add_lt_add_left hxy y) (by norm_num)
        _ = y := by rw [smul_add, ← add_smul]; norm_num
  letI : IsUniformAddGroup C₀ := C₀.toAddSubgroup.isUniformAddGroup
  letI : Nontrivial C₀ := by
    obtain ⟨z, hz, -⟩ := hcoinitial |y| habsy
    exact ⟨⟨0, z, ne_of_lt hz⟩⟩
  have haRange : (a : HahnSeries C K).support ⊆ Set.range inc := by
    intro q hq
    exact ⟨⟨q, (Submodule.span ℚ S).le_topologicalClosure
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inl hq)))))⟩, rfl⟩
  have hbRange : (b : HahnSeries C K).support ⊆ Set.range inc := by
    intro q hq
    exact ⟨⟨q, (Submodule.span ℚ S).le_topologicalClosure
      (Submodule.subset_span (Or.inl (Or.inl (Or.inl (Or.inr hq)))))⟩, rfl⟩
  have hcRange : (c : HahnSeries C K).support ⊆ Set.range inc := by
    intro q hq
    exact ⟨⟨q, (Submodule.span ℚ S).le_topologicalClosure
      (Submodule.subset_span (Or.inl (Or.inl (Or.inr hq))))⟩, rfl⟩
  have hdRange : (d : HahnSeries C K).support ⊆ Set.range inc := by
    intro q hq
    exact ⟨⟨q, (Submodule.span ℚ S).le_topologicalClosure
      (Submodule.subset_span (Or.inl (Or.inr hq)))⟩, rfl⟩
  let a₀ := restrictDomain inc hinc hincOrder a
  let b₀ := restrictDomain inc hinc hincOrder b
  let c₀ := restrictDomain inc hinc hincOrder c
  let d₀ := restrictDomain inc hinc hincOrder d
  have habcd₀ : a₀ * b₀ = c₀ * d₀ := by
    apply mapDomain_injective inc hinc hincOrder
    rw [map_mul, map_mul, mapDomain_restrictDomain inc hinc hincOrder a haRange,
      mapDomain_restrictDomain inc hinc hincOrder b hbRange,
      mapDomain_restrictDomain inc hinc hincOrder c hcRange,
      mapDomain_restrictDomain inc hinc hincOrder d hdRange, habcd]
  obtain ⟨e₀, f₀, g₀, h₀, hea, heb, hec, hed⟩ :=
    exists_germ_refinement_of_complete_exponent_group a₀ b₀ c₀ d₀ habcd₀
  have ha₀ : mapDomain inc hinc hincOrder a₀ = a :=
    mapDomain_restrictDomain inc hinc hincOrder a haRange
  have hb₀ : mapDomain inc hinc hincOrder b₀ = b :=
    mapDomain_restrictDomain inc hinc hincOrder b hbRange
  have hc₀ : mapDomain inc hinc hincOrder c₀ = c :=
    mapDomain_restrictDomain inc hinc hincOrder c hcRange
  have hd₀ : mapDomain inc hinc hincOrder d₀ = d :=
    mapDomain_restrictDomain inc hinc hincOrder d hdRange
  have hC₀support (z : Nonpositive C₀ K) :
      (z : HahnSeries C₀ K).cardSupp < κ := by
    rw [HahnSeries.cardSupp]
    exact Submodule.mk_lt_of_isPWO_topologicalClosure_span S hS hSne
      (z : HahnSeries C₀ K).support (z : HahnSeries C₀ K).isPWO_support
  exact exists_cardinal_refinement_mapDomain inc hinc hincOrder hC₀support
    a b c d a₀ b₀ c₀ d₀ e₀ f₀ g₀ h₀ ha₀ hb₀ hc₀ hd₀ hea heb hec hed

end HahnSeries.Nonpositive
