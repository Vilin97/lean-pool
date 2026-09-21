/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Translation

/-!
# Exponent-primitive finite-support series

Gilmer and Parker call a semigroup-ring element exponent-primitive when the greatest common
divisor of its exponents is zero. In `G ^ (≤ 0)` divisibility is the reverse order, so that
greatest common divisor is the largest exponent, and an element is exponent-primitive exactly when
its support meets zero. That reading is taken as the definition here.

This is the reduction step of Gilmer and Parker, Theorem 6.4, specialized to a totally ordered
exponent group, where it replaces their Theorem 3.1 and their Propositions 4.6, 6.2 and 6.3. The
largest exponent is additive on products, so every nonzero element is a monomial times an
exponent-primitive element and divisibility splits along that decomposition.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- A series supported in the nonpositive exponents is exponent-primitive when its largest
exponent is zero. -/
def IsEPrimitive (x : K⟦G⟧) : Prop :=
  x.support ⊆ Set.Iic 0 ∧ x.coeff 0 ≠ 0

omit [IsOrderedAddMonoid G] in
theorem IsEPrimitive.support_subset {x : K⟦G⟧} (hx : IsEPrimitive x) :
    x.support ⊆ Set.Iic 0 := hx.1

omit [IsOrderedAddMonoid G] in
theorem IsEPrimitive.ne_zero {x : K⟦G⟧} (hx : IsEPrimitive x) : x ≠ 0 :=
  fun h ↦ hx.2 (by simp [h])

/-- At the sum of two exponents dominating the respective supports, the coefficient of a product
is the product of the coefficients: that decomposition of the sum is the only one available. -/
theorem coeff_add_of_forall_le {x y : K⟦G⟧} {a b : G}
    (ha : ∀ g ∈ x.support, g ≤ a) (hb : ∀ g ∈ y.support, g ≤ b) :
    (x * y).coeff (a + b) = x.coeff a * y.coeff b := by
  classical
  have hsplit : ∀ c ∈ Finset.addAntidiagonal x.isPWO_support y.isPWO_support (a + b),
      c = (a, b) := by
    intro c hc
    rw [Finset.mem_addAntidiagonal] at hc
    obtain ⟨hc1, hc2, hc0⟩ := hc
    have h1 : c.1 = a := by
      refine le_antisymm (ha _ hc1) ?_
      by_contra hlt
      rw [not_le] at hlt
      exact absurd hc0 (ne_of_lt (add_lt_add_of_lt_of_le hlt (hb _ hc2)))
    refine Prod.ext h1 ?_
    have h2 := hc0
    rw [h1] at h2
    exact add_left_cancel h2
  rw [HahnSeries.coeff_mul]
  by_cases hx0 : x.coeff a = 0
  · rw [hx0, zero_mul]
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [hsplit c hc, hx0, zero_mul]
  by_cases hy0 : y.coeff b = 0
  · rw [hy0, mul_zero]
    refine Finset.sum_eq_zero fun c hc ↦ ?_
    rw [hsplit c hc, hy0, mul_zero]
  refine Finset.sum_eq_single_of_mem (a, b) ?_ (fun c hc hne ↦ absurd (hsplit c hc) hne)
  refine Finset.mem_addAntidiagonal.mpr ⟨?_, ?_, rfl⟩
  · exact (HahnSeries.mem_support x a).mpr hx0
  · exact (HahnSeries.mem_support y b).mpr hy0

/-- Zero has a unique decomposition into nonpositive exponents, so the coefficient there is
multiplicative on series supported in the nonpositive exponents. -/
theorem coeff_zero_mul_of_support_subset {x y : K⟦G⟧} (hx : x.support ⊆ Set.Iic 0)
    (hy : y.support ⊆ Set.Iic 0) : (x * y).coeff 0 = x.coeff 0 * y.coeff 0 := by
  have h := coeff_add_of_forall_le (x := x) (y := y) (a := 0) (b := 0) hx hy
  rwa [add_zero] at h

theorem IsEPrimitive.mul {x y : K⟦G⟧} (hx : IsEPrimitive x) (hy : IsEPrimitive y) :
    IsEPrimitive (x * y) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hg
    exact add_nonpos (hx.1 hi) (hy.1 hj)
  · rw [coeff_zero_mul_of_support_subset hx.1 hy.1]
    exact mul_ne_zero hx.2 hy.2

omit [AddCommGroup G] [IsOrderedAddMonoid G] in
/-- A nonzero finite-support series has a largest exponent. -/
theorem exists_max_mem_support {x : K⟦G⟧} (hfin : x.support.Finite) (hx : x ≠ 0) :
    ∃ a ∈ x.support, ∀ g ∈ x.support, g ≤ a := by
  classical
  have hne : hfin.toFinset.Nonempty := by
    rw [Set.Finite.toFinset_nonempty]
    exact HahnSeries.support_nonempty_iff.mpr hx
  obtain ⟨a, ha, hmax⟩ := hfin.toFinset.exists_max_image id hne
  exact ⟨a, (Set.Finite.mem_toFinset hfin).mp ha,
    fun g hg ↦ hmax g ((Set.Finite.mem_toFinset hfin).mpr hg)⟩

/-- The largest exponent is additive on products. -/
theorem isMax_support_mul {x y : K⟦G⟧} {a b : G}
    (ha : a ∈ x.support) (hamax : ∀ g ∈ x.support, g ≤ a)
    (hb : b ∈ y.support) (hbmax : ∀ g ∈ y.support, g ≤ b) :
    a + b ∈ (x * y).support ∧ ∀ g ∈ (x * y).support, g ≤ a + b := by
  refine ⟨?_, fun g hg ↦ ?_⟩
  · rw [HahnSeries.mem_support, coeff_add_of_forall_le hamax hbmax]
    exact mul_ne_zero ((HahnSeries.mem_support _ _).mp ha) ((HahnSeries.mem_support _ _).mp hb)
  · obtain ⟨i, hi, j, hj, rfl⟩ := HahnSeries.support_mul_subset hg
    exact add_le_add (hamax i hi) (hbmax j hj)

/-- Every nonzero finite-support series is a monomial times an exponent-primitive one, the
monomial exponent being the largest exponent of its support. -/
theorem exists_eprimitive_decomposition' {x : K⟦G⟧} (hfin : x.support.Finite) (hx : x ≠ 0) :
    ∃ m : G, ∃ y : K⟦G⟧,
      m ∈ x.support ∧ y.support.Finite ∧ IsEPrimitive y ∧ x = translate m y := by
  classical
  obtain ⟨m, hm, hmax⟩ := exists_max_mem_support hfin hx
  refine ⟨m, translate (-m) x, hm, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [HahnSeries.support_translate]
    exact hfin.image _
  · intro g hg
    rw [HahnSeries.support_translate] at hg
    obtain ⟨a, ha, rfl⟩ := hg
    simpa using hmax a ha
  · rw [HahnSeries.coeff_translate]
    simpa using (HahnSeries.mem_support _ _).mp hm
  · rw [HahnSeries.translate_add_apply]
    simp

/-- The same decomposition in the nonpositive exponents, where the monomial exponent is
nonpositive. -/
theorem exists_eprimitive_decomposition {x : K⟦G⟧} (hfin : x.support.Finite)
    (hsub : x.support ⊆ Set.Iic 0) (hx : x ≠ 0) :
    ∃ m : G, ∃ y : K⟦G⟧,
      m ≤ 0 ∧ y.support.Finite ∧ IsEPrimitive y ∧ x = translate m y := by
  obtain ⟨m, y, hm, hyf, hy, hxy⟩ := exists_eprimitive_decomposition' hfin hx
  exact ⟨m, y, hsub hm, hyf, hy, hxy⟩

/-- Divisibility among finite-support series in the nonpositive exponents, with the divisor
exponent-primitive: the quotient may be taken exponent-primitive as well. -/
theorem eprimitive_of_mul_eq {x y w : K⟦G⟧} (hx : IsEPrimitive x) (hy : IsEPrimitive y)
    (hw : w.support ⊆ Set.Iic 0) (hmul : y = x * w) : IsEPrimitive w := by
  refine ⟨hw, ?_⟩
  intro h0
  apply hy.2
  rw [hmul, coeff_zero_mul_of_support_subset hx.1 hw, h0, mul_zero]

/-- Two exponent-primitive series differing by a translation are equal: the translation must be
trivial, since it moves both the largest exponent and the exponent carrying a nonzero
coefficient. -/
theorem eq_zero_of_isEPrimitive_translate {d : G} {u v : K⟦G⟧} (hu : IsEPrimitive u)
    (hv : IsEPrimitive v) (h : u = translate d v) : d = 0 := by
  have hmem : d ∈ u.support := by
    refine (HahnSeries.mem_support _ _).mpr ?_
    rw [h, HahnSeries.coeff_translate]
    simpa using hv.2
  have hneg : -d ∈ v.support := by
    refine (HahnSeries.mem_support _ _).mpr ?_
    have h0 := hu.2
    rw [h, HahnSeries.coeff_translate] at h0
    simpa [sub_eq_add_neg] using h0
  exact le_antisymm (hu.1 hmem) (neg_nonpos.mp (hv.1 hneg))

/-- Divisibility in the finite-support ring on the nonpositive exponents. -/
def DvdNP (x z : K⟦G⟧) : Prop :=
  ∃ w : K⟦G⟧, w.support.Finite ∧ w.support ⊆ Set.Iic 0 ∧ z = x * w

/-- Divisibility in the finite-support ring on the whole exponent group. -/
def DvdFS (x z : K⟦G⟧) : Prop :=
  ∃ w : K⟦G⟧, w.support.Finite ∧ z = x * w

theorem dvdNP_iff {x z : K⟦G⟧} :
    DvdNP x z ↔
      ∃ w : K⟦G⟧, w.support.Finite ∧ w.support ⊆ Set.Iic 0 ∧ z = x * w := (Iff.rfl)

theorem dvdFS_iff {x z : K⟦G⟧} :
    DvdFS x z ↔ ∃ w : K⟦G⟧, w.support.Finite ∧ z = x * w := (Iff.rfl)

theorem DvdNP.dvdFS {x z : K⟦G⟧} (h : DvdNP x z) : DvdFS x z := by
  obtain ⟨w, hwf, -, hw⟩ := h
  exact ⟨w, hwf, hw⟩

/-- On exponent-primitive elements the two divisibilities agree: a quotient with a positive
exponent would push the largest exponent of the product above zero. -/
theorem dvdNP_iff_dvdFS {x z : K⟦G⟧} (hx : IsEPrimitive x) (hz : IsEPrimitive z) :
    DvdNP x z ↔ DvdFS x z := by
  refine ⟨DvdNP.dvdFS, ?_⟩
  rintro ⟨w, hwf, rfl⟩
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hz.ne_zero (by simp)
  obtain ⟨m, hm, hmmax⟩ := exists_max_mem_support hwf hw0
  obtain ⟨hmem, hmax⟩ :=
    isMax_support_mul ((HahnSeries.mem_support x 0).mpr hx.2) hx.1 hm hmmax
  rw [zero_add] at hmem hmax
  have hm0 : m = 0 :=
    le_antisymm (hz.1 hmem) (hmax 0 ((HahnSeries.mem_support _ _).mpr hz.2))
  exact ⟨w, hwf, fun g hg ↦ hm0 ▸ hmmax g hg, rfl⟩

/-- Divisibility splits along the monomial decomposition: the monomial exponents compare and the
exponent-primitive parts divide. -/
theorem dvdNP_translate_iff {a c : G} {x₀ z₀ : K⟦G⟧}
    (hx₀ : IsEPrimitive x₀) (hz₀ : IsEPrimitive z₀) :
    DvdNP (translate a x₀) (translate c z₀) ↔ c ≤ a ∧ DvdNP x₀ z₀ := by
  constructor
  · rintro ⟨w, hwf, hws, hw⟩
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hw
      exact hz₀.ne_zero ((translate c).injective (by simpa using hw))
    obtain ⟨e, y, hele, hyf, hy, rfl⟩ := exists_eprimitive_decomposition hwf hws hw0
    have hprod : translate c z₀ = translate (a + e) (x₀ * y) := by
      rw [hw, HahnSeries.translate_mul_translate]
    have hshift : x₀ * y = translate (c - (a + e)) z₀ := by
      have h2 := congrArg (translate (-(a + e))) hprod
      rw [HahnSeries.translate_add_apply, HahnSeries.translate_add_apply] at h2
      simp only [neg_add_cancel, HahnSeries.translate_zero_apply] at h2
      rw [← h2]
      congr 1
      abel_nf
    have hzero : c - (a + e) = 0 :=
      eq_zero_of_isEPrimitive_translate (hx₀.mul hy) hz₀ hshift
    have hce : c = a + e := by
      have := hzero
      rwa [sub_eq_zero] at this
    refine ⟨?_, y, hyf, hy.1, ?_⟩
    · rw [hce]
      simpa using add_le_add_left hele a
    · rw [hshift, hzero]
      simp
  · rintro ⟨hca, w, hwf, hws, rfl⟩
    refine ⟨translate (c - a) w, ?_, ?_, ?_⟩
    · rw [HahnSeries.support_translate]
      exact hwf.image _
    · rw [HahnSeries.support_translate]
      rintro _ ⟨g, hg, rfl⟩
      exact add_nonpos (by simpa using sub_nonpos.mpr hca) (hws hg)
    · rw [HahnSeries.translate_mul_translate]
      congr 1
      abel_nf

theorem dvdNP_zero (e : K⟦G⟧) : DvdNP e 0 := ⟨0, by simp, by simp, by simp⟩

theorem translate_mul_left (a : G) (x y : K⟦G⟧) : translate a (x * y) = x * translate a y := by
  have h := HahnSeries.translate_mul_translate (0 : G) a x y
  rw [HahnSeries.translate_zero_apply, zero_add] at h
  exact h.symm

/-- Divisibility in the whole group ring is unchanged by translating the dividend, since a
translation is multiplication by a unit. -/
theorem dvdFS_translate_iff {b : G} {e w : K⟦G⟧} : DvdFS e (translate b w) ↔ DvdFS e w := by
  constructor
  · rintro ⟨v, hvf, hv⟩
    refine ⟨translate (-b) v, ?_, ?_⟩
    · rw [HahnSeries.support_translate]
      exact hvf.image _
    · have h2 := congrArg (translate (-b)) hv
      rw [HahnSeries.translate_add_apply] at h2
      simp only [neg_add_cancel, HahnSeries.translate_zero_apply] at h2
      rw [h2]
      exact translate_mul_left _ _ _
  · rintro ⟨v, hvf, hv⟩
    refine ⟨translate b v, ?_, ?_⟩
    · rw [HahnSeries.support_translate]
      exact hvf.image _
    · rw [hv]
      exact translate_mul_left _ _ _

/-- Gilmer and Parker, Theorem 6.4 for a totally ordered exponent group: greatest common divisors
in the whole group ring produce greatest common divisors in the nonpositive ring. -/
theorem exists_gcd_nonpositive_of_exists_gcd
    (Hgcd : ∀ x z : K⟦G⟧, x.support.Finite → z.support.Finite →
      ∃ d : K⟦G⟧, d.support.Finite ∧
        ∀ e : K⟦G⟧, e.support.Finite → (DvdFS e x ∧ DvdFS e z ↔ DvdFS e d))
    {x z : K⟦G⟧} (hxf : x.support.Finite) (hxs : x.support ⊆ Set.Iic 0)
    (hzf : z.support.Finite) (hzs : z.support ⊆ Set.Iic 0) :
    ∃ d : K⟦G⟧, d.support.Finite ∧ d.support ⊆ Set.Iic 0 ∧
      ∀ e : K⟦G⟧, e.support.Finite → e.support ⊆ Set.Iic 0 →
        (DvdNP e x ∧ DvdNP e z ↔ DvdNP e d) := by
  classical
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨z, hzf, hzs, fun e _ _ ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨dvdNP_zero e, h⟩⟩⟩
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ⟨x, hxf, hxs, fun e _ _ ↦ ⟨fun h ↦ h.1, fun h ↦ ⟨h, dvdNP_zero e⟩⟩⟩
  obtain ⟨a, x₀, hale, hx₀f, hx₀, rfl⟩ := exists_eprimitive_decomposition hxf hxs hx0
  obtain ⟨c, z₀, hcle, hz₀f, hz₀, rfl⟩ := exists_eprimitive_decomposition hzf hzs hz0
  obtain ⟨d₀, hd₀f, hd₀⟩ := Hgcd x₀ z₀ hx₀f hz₀f
  have hd₀ne : d₀ ≠ 0 := by
    rintro rfl
    obtain ⟨hdx, -⟩ := (hd₀ 0 (by simp)).mpr ⟨1, by simp, by simp⟩
    obtain ⟨w, -, hw⟩ := hdx
    exact hx₀.ne_zero (by simpa using hw)
  obtain ⟨b, d₁, -, hd₁f, hd₁, hd₀eq⟩ := exists_eprimitive_decomposition' hd₀f hd₀ne
  have hd₁gcd : ∀ e : K⟦G⟧, e.support.Finite →
      (DvdFS e x₀ ∧ DvdFS e z₀ ↔ DvdFS e d₁) := by
    intro e hef
    rw [hd₀ e hef, hd₀eq, dvdFS_translate_iff]
  refine ⟨translate (max a c) d₁, ?_, ?_, ?_⟩
  · rw [HahnSeries.support_translate]
    exact hd₁f.image _
  · rw [HahnSeries.support_translate]
    rintro _ ⟨g, hg, rfl⟩
    exact add_nonpos (max_le hale hcle) (hd₁.1 hg)
  · intro e hef hes
    rcases eq_or_ne e 0 with rfl | he0
    · constructor
      · rintro ⟨⟨w, -, -, hw⟩, -⟩
        refine absurd ?_ hx₀.ne_zero
        have hz : translate a x₀ = 0 := by simpa using hw
        exact (translate a).injective (by simpa using hz)
      · rintro ⟨w, -, -, hw⟩
        refine absurd ?_ hd₁.ne_zero
        have hz : translate (max a c) d₁ = 0 := by simpa using hw
        exact (translate (max a c)).injective (by simpa using hz)
    obtain ⟨f, e₀, -, he₀f, he₀, rfl⟩ := exists_eprimitive_decomposition hef hes he0
    rw [dvdNP_translate_iff he₀ hx₀, dvdNP_translate_iff he₀ hz₀,
      dvdNP_translate_iff he₀ hd₁, dvdNP_iff_dvdFS he₀ hx₀, dvdNP_iff_dvdFS he₀ hz₀,
      dvdNP_iff_dvdFS he₀ hd₁, ← hd₁gcd e₀ he₀f, max_le_iff]
    tauto

end HahnSeries
