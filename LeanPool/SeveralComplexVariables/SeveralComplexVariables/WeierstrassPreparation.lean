/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.WeierstrassDivision

/-!
# Analytic Weierstrass preparation

A function regular of order `d` in the distinguished coordinate factors locally as a
nonvanishing holomorphic function times a monic polynomial of degree `d`. The lower coefficients
are holomorphic in the parameters and vanish at the parameter origin.

Reference: [Jakóbczak–Jarnicki][JakobczakJarnicki2021], Theorem 1.7.2. Preparation and its
uniqueness are derived from the analytic division theorem. The proof includes degree zero, and
empty parameter types recover one-variable theory.

## Main definitions

* `weierstrassPolynomial`: The monic polynomial in the distinguished coordinate with prescribed
  lower coefficients.
* `IsWeierstrassPreparationAt`: Local preparation consists of a unit and a monic polynomial whose
  lower coefficients vanish at the parameter origin.

## Main results

* `exists_isWeierstrassPreparationAt`: **Weierstrass preparation for analytic germs.** Divide `w^d`
  by `f`, identify the central coefficients using one-variable order factorization and division
  uniqueness, and invert the resulting quotient.
* `exists_eqOn_mul_weierstrassPolynomial`: **Weierstrass preparation
  ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.2).** On a sufficiently small polydisc, a regular
  holomorphic function is a nonvanishing holomorphic factor times a monic polynomial with
  holomorphic lower coefficients vanishing at the origin.
* `exists_isWeierstrassPreparationAt_of_finiteDimensional`: **Weierstrass preparation for analytic
  germs on any finite-dimensional parameter space.** Obtained by transporting the coordinate version
  along a basis; no choice of coordinates occurs in the statement.

## References

* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
-/

public noncomputable section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The monic polynomial in the distinguished coordinate with prescribed lower coefficients. -/
@[expose] def weierstrassPolynomial {d : ℕ} (a : Fin d → E → ℂ) (z : E × ℂ) : ℂ :=
  z.2 ^ d + weierstrassRemainder a z

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- Negating the coefficient functions negates the remainder polynomial. -/
@[simp] theorem weierstrassRemainder_neg {d : ℕ} (a : Fin d → E → ℂ) (z : E × ℂ) :
    weierstrassRemainder (fun j x => -a j x) z = -weierstrassRemainder a z := by
  simp [weierstrassRemainder, Finset.sum_neg_distrib]

omit [NormedAddCommGroup E] [NormedSpace ℂ E] in
/-- A monic polynomial of degree zero is the constant one. -/
@[simp] theorem weierstrassPolynomial_zero (a : Fin 0 → E → ℂ) :
    weierstrassPolynomial a = 1 := by
  funext z
  simp [weierstrassPolynomial]

/-- Analytic coefficients give a jointly analytic monic polynomial. -/
theorem analyticAt_weierstrassPolynomial {d : ℕ} {a : Fin d → E → ℂ} {z : E × ℂ}
    (ha : ∀ j, AnalyticAt ℂ (a j) z.1) : AnalyticAt ℂ (weierstrassPolynomial a) z :=
  (analyticAt_snd.pow d).add (analyticAt_weierstrassRemainder ha)

omit [NormedSpace ℂ E] in
/-- Vanishing of the lower coefficients gives the central monomial. -/
theorem weierstrassPolynomial_central {d : ℕ} {a : Fin d → E → ℂ}
    (ha : ∀ j, a j 0 = 0) (w : ℂ) : weierstrassPolynomial a (0, w) = w ^ d := by
  simp [weierstrassPolynomial, weierstrassRemainder, ha]

/-- Local preparation consists of a unit and a monic polynomial whose lower coefficients vanish at
the parameter origin. Equality is equality of germs at the origin. -/
structure IsWeierstrassPreparationAt {d : ℕ} (f u : E × ℂ → ℂ)
    (a : Fin d → E → ℂ) : Prop where
  /-- The unit factor is analytic at the origin. -/
  analyticAt_unit : AnalyticAt ℂ u 0
  /-- The unit factor does not vanish at the origin. -/
  unit_ne_zero : u 0 ≠ 0
  /-- Each polynomial coefficient is analytic at the parameter origin. -/
  analyticAt_coeff : ∀ j, AnalyticAt ℂ (a j) 0
  /-- All lower polynomial coefficients vanish at the parameter origin. -/
  coeff_zero : ∀ j, a j 0 = 0
  /-- As germs, the function equals the unit times the distinguished polynomial. -/
  eq : f =ᶠ[𝓝 0] fun z => u z * weierstrassPolynomial a z

/-- A nonvanishing analytic function is already prepared in degree zero. -/
theorem isWeierstrassPreparationAt_zero {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (h0 : f 0 ≠ 0) :
    IsWeierstrassPreparationAt f f (fun j : Fin 0 => Fin.elim0 j) := by
  refine ⟨hf, h0, fun j => Fin.elim0 j, fun j => Fin.elim0 j, ?_⟩
  exact .of_forall fun z => by simp

/-- A preparation gives a division of the monomial by the original function. -/
theorem IsWeierstrassPreparationAt.division {d : ℕ} {f u : E × ℂ → ℂ}
    {a : Fin d → E → ℂ} (h : IsWeierstrassPreparationAt f u a) :
    IsWeierstrassDivisionAt f (fun z => z.2 ^ d) (fun z => (u z)⁻¹)
      (fun j x => -a j x) := by
  refine ⟨h.analyticAt_unit.inv h.unit_ne_zero, fun j => (h.analyticAt_coeff j).neg, ?_⟩
  filter_upwards [h.eq, h.analyticAt_unit.continuousAt.eventually_ne h.unit_ne_zero] with z hz hne
  rw [hz, weierstrassRemainder_neg]
  simp [weierstrassPolynomial, hne]

variable {ι : Type*} [Fintype ι]

/-- Uniqueness of preparation follows from uniqueness of analytic division. Thus it rests on the
division theorem. -/
theorem IsWeierstrassPreparationAt.unique {d : ℕ} {f u v : (ι → ℂ) × ℂ → ℂ}
    {a b : Fin d → (ι → ℂ) → ℂ}
    (h : IsWeierstrassPreparationAt f u a) (h' : IsWeierstrassPreparationAt f v b)
    (hf : AnalyticAt ℂ f 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    u =ᶠ[𝓝 0] v ∧ ∀ j, a j =ᶠ[𝓝 0] b j := by
  obtain ⟨hu, ha⟩ := h.division.unique h'.division hf (analyticAt_snd.pow d) horder
  refine ⟨hu.mono (fun z hz => inv_injective hz), fun j => ?_⟩
  exact (ha j).mono (fun z hz => neg_injective hz)

/-- Uniqueness of the factors and coefficients on a whole product domain follows from germ
uniqueness and the identity theorem. This applies to the polydisc of preparation. -/
theorem IsWeierstrassPreparationAt.unique_on {d : ℕ} {f u v : (ι → ℂ) × ℂ → ℂ}
    {a b : Fin d → (ι → ℂ) → ℂ} {V : Set (ι → ℂ)} {R : ℝ}
    (h : IsWeierstrassPreparationAt f u a) (h' : IsWeierstrassPreparationAt f v b)
    (hf : AnalyticAt ℂ f 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d)
    (hV : IsOpen V) (hconn : IsPreconnected V) (h0 : 0 ∈ V) (hR : 0 < R)
    (hu : DifferentiableOn ℂ u (V ×ˢ ball 0 R))
    (hv : DifferentiableOn ℂ v (V ×ˢ ball 0 R))
    (ha : ∀ j, DifferentiableOn ℂ (a j) V) (hb : ∀ j, DifferentiableOn ℂ (b j) V) :
    EqOn u v (V ×ˢ ball 0 R) ∧ ∀ j, EqOn (a j) (b j) V := by
  obtain ⟨he, he'⟩ := h.unique h' hf horder
  exact ⟨DifferentiableOn.eqOn_of_preconnected_of_eventuallyEq
      (show IsOpen (V ×ˢ ball (0 : ℂ) R) from hV.prod isOpen_ball)
      (hconn.prod (convex_ball (0 : ℂ) R).isPreconnected)
      hu hv ⟨h0, mem_ball_self hR⟩ he,
    fun j => (ha j).eqOn_of_preconnected_of_eventuallyEq hV hconn (hb j) h0 (he' j)⟩

/-- **Weierstrass preparation for analytic germs.** Divide `w^d` by `f`, identify the
central coefficients using one-variable order factorization and division uniqueness,
and invert the resulting quotient. This proof depends on analytic division. -/
theorem exists_isWeierstrassPreparationAt {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (u : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
      IsWeierstrassPreparationAt f u a ∧
      ∀ v b, IsWeierstrassPreparationAt f v b →
        u =ᶠ[𝓝 0] v ∧ ∀ j, a j =ᶠ[𝓝 0] b j := by
  have hp : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ => z.2 ^ d) 0 := analyticAt_snd.pow d
  obtain ⟨q, a, hD, _⟩ := exists_isWeierstrassDivisionAt hf hp horder
  have hs : AnalyticAt ℂ (fun w : ℂ => f (0, w)) 0 :=
    hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
  obtain ⟨v, hv, hv0, hfv⟩ := hs.analyticOrderAt_eq_natCast.mp horder
  have hc : AnalyticAt ℂ (fun z : (ι → ℂ) × ℂ => ((0 : ι → ℂ), z.2)) 0 :=
    analyticAt_const.prod analyticAt_snd
  have hDc : IsWeierstrassDivisionAt (fun z : (ι → ℂ) × ℂ => f (0, z.2))
      (fun z => z.2 ^ d) (fun z => q (0, z.2)) (fun j _ => a j 0) := by
    refine ⟨hD.analyticAt_quotient.comp_of_eq hc rfl, fun _ => analyticAt_const, ?_⟩
    exact hD.eq.comp_tendsto hc.continuousAt
  have hDv : IsWeierstrassDivisionAt (fun z : (ι → ℂ) × ℂ => f (0, z.2))
      (fun z => z.2 ^ d) (fun z => (v z.2)⁻¹) (fun _ _ => 0 : Fin d → (ι → ℂ) → ℂ) := by
    refine ⟨(hv.comp_of_eq (analyticAt_snd (𝕜 := ℂ)
      (p := (0 : (ι → ℂ) × ℂ))) rfl).inv hv0, fun _ => analyticAt_const, ?_⟩
    have ht : Tendsto (Prod.snd : (ι → ℂ) × ℂ → ℂ) (𝓝 0) (𝓝 0) :=
      continuous_snd.tendsto 0
    filter_upwards [ht.eventually hfv, ht.eventually (hv.continuousAt.eventually_ne hv0)]
      with z hz hne
    simp only [sub_zero, smul_eq_mul] at hz
    simp [weierstrassRemainder, hz, hne, mul_comm]
  obtain ⟨hq, ha⟩ := hDc.unique hDv (hf.comp_of_eq hc rfl) hp horder
  have hq0 : q 0 ≠ 0 := by
    have he : q 0 = (v 0)⁻¹ := hq.eq_of_nhds
    rw [he]
    exact inv_ne_zero hv0
  have ha0 : ∀ j, a j 0 = 0 := fun j => (ha j).eq_of_nhds
  have H : IsWeierstrassPreparationAt f (fun z => (q z)⁻¹) (fun j x => -a j x) := by
    refine ⟨hD.analyticAt_quotient.inv hq0, inv_ne_zero hq0,
      fun j => (hD.analyticAt_coeff j).neg, fun j => by simp [ha0], ?_⟩
    filter_upwards [hD.eq, hD.analyticAt_quotient.continuousAt.eventually_ne hq0] with z hz hne
    simp only [weierstrassPolynomial, weierstrassRemainder_neg]
    apply (mul_left_cancel₀ hne)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
    linear_combination -hz
  exact ⟨_, _, H, fun v b hb => H.unique hb hf horder⟩

/-- **Weierstrass preparation ([Jakóbczak–Jarnicki][JakobczakJarnicki2021] 1.7.2).** On a
sufficiently small
polydisc, a regular holomorphic function is a nonvanishing holomorphic factor times a
monic polynomial with holomorphic lower coefficients vanishing at the origin.
The factorization is unique as a germ. The proof depends on analytic division. -/
theorem exists_eqOn_mul_weierstrassPolynomial {d : ℕ} {f : (ι → ℂ) × ℂ → ℂ}
    {U : Set ((ι → ℂ) × ℂ)} (hU : IsOpen U) (h0 : 0 ∈ U)
    (hf : DifferentiableOn ℂ f U)
    (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (r : ι → ℝ) (R : ℝ) (u : (ι → ℂ) × ℂ → ℂ) (a : Fin d → (ι → ℂ) → ℂ),
      (∀ i, 0 < r i) ∧ 0 < R ∧ polydisc 0 r ×ˢ ball 0 R ⊆ U ∧
      DifferentiableOn ℂ u (polydisc 0 r ×ˢ ball 0 R) ∧
      (∀ z ∈ polydisc 0 r ×ˢ ball 0 R, u z ≠ 0) ∧
      (∀ j, DifferentiableOn ℂ (a j) (polydisc 0 r)) ∧
      (∀ j, a j 0 = 0) ∧
      EqOn f (fun z => u z * weierstrassPolynomial a z) (polydisc 0 r ×ˢ ball 0 R) ∧
      ∀ v b, IsWeierstrassPreparationAt f v b →
        u =ᶠ[𝓝 0] v ∧ ∀ j, a j =ᶠ[𝓝 0] b j := by
  obtain ⟨u, a, H, hu⟩ := exists_isWeierstrassPreparationAt
    ((hf.analyticOnNhd_of_finiteDimensional hU) _ h0) horder
  have ha' : ∀ᶠ x in 𝓝 (0 : ι → ℂ), ∀ j, AnalyticAt ℂ (a j) x :=
    Filter.eventually_all.mpr (fun j => (H.analyticAt_coeff j).eventually_analyticAt)
  have ha : ∀ᶠ z : (ι → ℂ) × ℂ in 𝓝 0, ∀ j, AnalyticAt ℂ (a j) z.1 :=
    by
      have ht : Tendsto (Prod.fst : (ι → ℂ) × ℂ → (ι → ℂ)) (𝓝 0) (𝓝 0) :=
        continuous_fst.tendsto 0
      exact ht.eventually ha'
  have hU' : ∀ᶠ z in 𝓝 (0 : (ι → ℂ) × ℂ), z ∈ U := hU.mem_nhds h0
  have hn := hU'.and (H.analyticAt_unit.eventually_analyticAt.and
    ((H.analyticAt_unit.continuousAt.eventually_ne H.unit_ne_zero).and (ha.and H.eq)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hn
  have hP : polydisc (0 : ι → ℂ) (fun _ => ε) ×ˢ ball (0 : ℂ) ε =
      ball (0 : (ι → ℂ) × ℂ) ε := by
    rw [polydisc_const_eq_ball _ hε, ball_prod_same]
    rfl
  have hprop := fun z (hz : z ∈ polydisc (0 : ι → ℂ) (fun _ => ε) ×ˢ ball (0 : ℂ) ε) =>
    hball (hP ▸ hz)
  refine ⟨fun _ => ε, ε, u, a, fun _ => hε, hε, fun z hz => (hprop z hz).1,
    fun z hz => (hprop z hz).2.1.differentiableAt.differentiableWithinAt,
    fun z hz => (hprop z hz).2.2.1, ?_, H.coeff_zero,
    fun z hz => (hprop z hz).2.2.2.2, hu⟩
  intro j z hz
  exact ((hprop (z, 0) ⟨hz, mem_ball_self hε⟩).2.2.2.1 j).differentiableAt.differentiableWithinAt

/-- Preparation transports along a continuous linear equivalence of the parameter space. -/
theorem IsWeierstrassPreparationAt.comp_equiv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (φ : F ≃L[ℂ] E) {d : ℕ} {f u : E × ℂ → ℂ} {a : Fin d → E → ℂ}
    (h : IsWeierstrassPreparationAt f u a) :
    IsWeierstrassPreparationAt (fun z : F × ℂ => f (φ z.1, z.2))
      (fun z : F × ℂ => u (φ z.1, z.2)) (fun j x => a j (φ x)) := by
  have hφ : AnalyticAt ℂ φ (0 : F) := φ.toContinuousLinearMap.analyticAt 0
  have hφmap : φ (0 : F) = 0 := φ.map_zero
  have hpair : AnalyticAt ℂ (fun z : F × ℂ => (φ z.1, z.2)) (0 : F × ℂ) :=
    (hφ.comp_of_eq analyticAt_fst rfl).prod analyticAt_snd
  have h0 : (fun z : F × ℂ => (φ z.1, z.2)) 0 = (0 : E × ℂ) := by simp [hφmap]
  have ht : Tendsto (fun z : F × ℂ => (φ z.1, z.2)) (𝓝 0) (𝓝 (0 : E × ℂ)) := by
    rw [← h0]; exact hpair.continuousAt.tendsto
  refine ⟨h.analyticAt_unit.comp_of_eq hpair h0,
    by show u (φ 0, (0 : ℂ)) ≠ 0; rw [hφmap]; exact h.unit_ne_zero,
    fun j => (h.analyticAt_coeff j).comp_of_eq hφ hφmap,
    fun j => by show a j (φ (0 : F)) = 0; rw [hφmap]; exact h.coeff_zero j,
    (h.eq.comp_tendsto ht).mono fun z hz => by
      simpa [weierstrassPolynomial, weierstrassRemainder] using hz⟩

/-- **Weierstrass preparation for analytic germs on any finite-dimensional parameter space.**
Obtained by transporting the coordinate version along a basis; no choice of coordinates
occurs in the statement. -/
theorem exists_isWeierstrassPreparationAt_of_finiteDimensional [FiniteDimensional ℂ E] {d : ℕ}
    {f : E × ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : analyticOrderAt (fun w : ℂ => f (0, w)) 0 = d) :
    ∃ (u : E × ℂ → ℂ) (a : Fin d → E → ℂ),
      IsWeierstrassPreparationAt f u a ∧
      ∀ v b, IsWeierstrassPreparationAt f v b →
        u =ᶠ[𝓝 0] v ∧ ∀ j, a j =ᶠ[𝓝 0] b j := by
  set e := (Module.finBasis ℂ E).equivFunL with he_def
  set g : (Fin (Module.finrank ℂ E) → ℂ) × ℂ → ℂ := fun z => f (e.symm z.1, z.2) with hg_def
  have hg0 : (fun w : ℂ => g (0, w)) = fun w : ℂ => f (0, w) := by funext w; simp [hg_def]
  have hgan : AnalyticAt ℂ g 0 :=
    hf.comp_of_eq (((e.symm.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd) (by simp)
  have hgorder : analyticOrderAt (fun w : ℂ => g (0, w)) 0 = d := by rw [hg0]; exact horder
  obtain ⟨v, b, Hg, huniqg⟩ := exists_isWeierstrassPreparationAt hgan hgorder
  have hf_eq : f = fun z : E × ℂ => g (e z.1, z.2) := by funext z; simp [hg_def]
  have Hf : IsWeierstrassPreparationAt f (fun z : E × ℂ => v (e z.1, z.2))
      (fun j x => b j (e x)) := by
    rw [hf_eq]; exact Hg.comp_equiv e
  refine ⟨_, _, Hf, fun v' a' Hv' => ?_⟩
  have Hv'' : IsWeierstrassPreparationAt g (fun z => v' (e.symm z.1, z.2))
      (fun j x => a' j (e.symm x)) := by
    rw [hg_def]; exact Hv'.comp_equiv e.symm
  obtain ⟨huv, hab⟩ := huniqg _ _ Hv''
  have ht : Tendsto (fun z : E × ℂ => (e z.1, z.2)) (𝓝 0)
      (𝓝 (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ)) := by
    have h0 : (fun z : E × ℂ => (e z.1, z.2)) 0 = (0 : (Fin (Module.finrank ℂ E) → ℂ) × ℂ) := by
      simp
    rw [← h0]
    exact (((e.toContinuousLinearMap.analyticAt 0).comp_of_eq analyticAt_fst rfl).prod
      analyticAt_snd).continuousAt.tendsto
  refine ⟨(huv.comp_tendsto ht).mono fun z hz => ?_, fun j => ?_⟩
  · simpa using hz
  · have htj : Tendsto e (𝓝 (0 : E)) (𝓝 (0 : Fin (Module.finrank ℂ E) → ℂ)) := by
      simpa using (e.toContinuousLinearMap.analyticAt 0).continuousAt.tendsto
    exact ((hab j).comp_tendsto htj).mono fun x hx => by simpa using hx

/-- Preparation gives a factorization in the analytic germ ring with an invertible factor. -/
theorem IsWeierstrassPreparationAt.germ_factorization {d : ℕ} {f u : E × ℂ → ℂ}
    {a : Fin d → E → ℂ} (h : IsWeierstrassPreparationAt f u a)
    (hf : AnalyticAt ℂ f 0) :
    IsUnit (AnalyticGerm.ofAnalyticAt u h.analyticAt_unit) ∧
    AnalyticGerm.ofAnalyticAt f hf = AnalyticGerm.ofAnalyticAt u h.analyticAt_unit *
      AnalyticGerm.ofAnalyticAt (weierstrassPolynomial a)
        (analyticAt_weierstrassPolynomial h.analyticAt_coeff) := by
  refine ⟨(AnalyticGerm.isUnit_iff _).mpr h.unit_ne_zero, ?_⟩
  apply Subtype.ext
  exact Germ.coe_eq.mpr h.eq

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
