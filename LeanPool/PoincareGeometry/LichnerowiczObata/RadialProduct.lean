/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.SmoothRadialFlow

/-! # Product coordinates supplied by radial transport -/

@[expose] public noncomputable section
open Set
open scoped Topology

namespace LichnerowiczObata

/-- A level contained in an open region is the same topological space whether
it is formed in the ambient space or inside that region. -/
def wholeLevelHomeomorph {X : Type*} [TopologicalSpace X]
    (U : Set X) (ρ : X → ℝ) (r : ℝ)
    (hU : ∀ x, ρ x = r → x ∈ U) :
    {x : U // ρ x = r} ≃ₜ {x : X // ρ x = r} where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨⟨x.1, hU x x.2⟩, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- A radial family with its proved coordinate and reset identities gives
an actual bijective product parameterization, not merely a surjective map. -/
def radialProductEquiv {X : Type*} (U : Set X) (J : Set ℝ) (ρ : X → ℝ)
    (η : X × ℝ → X) (r₀ : ℝ) (hr₀ : r₀ ∈ J)
    (hρ : ∀ x ∈ U, ρ x ∈ J)
    (hη : ∀ x ∈ U, ∀ r ∈ J, η (x, r) ∈ U)
    (hlevel : ∀ x ∈ U, ∀ r ∈ J, ρ (η (x, r)) = r)
    (hinit : ∀ x ∈ U, η (x, ρ x) = x)
    (hreset : ∀ x ∈ U, ∀ r ∈ J, ∀ s ∈ J, η (η (x, r), s) = η (x, s)) :
    U ≃ {x : U // ρ x = r₀} × J where
  toFun x := (⟨⟨η (x, r₀), hη x x.property r₀ hr₀⟩, hlevel x x.property r₀ hr₀⟩,
    ⟨ρ x, hρ x x.property⟩)
  invFun z := ⟨η (z.1.1, z.2), hη z.1.1 z.1.1.property z.2 z.2.property⟩
  left_inv x := by
    apply Subtype.ext
    exact (hreset x x.property r₀ hr₀ (ρ x) (hρ x x.property)).trans (hinit x x.property)
  right_inv z := by
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change η (η (z.1.1, z.2), r₀) = z.1.1
      rw [hreset z.1.1 z.1.1.property z.2 z.2.property r₀ hr₀]
      simpa only [z.1.property] using hinit z.1.1 z.1.1.property
    · apply Subtype.ext
      exact hlevel z.1.1 z.1.1.property z.2 z.2.property

/-- Continuous radial transport identifies the regular region
homeomorphically with any one radial level times the radial interval. -/
def radialProductHomeomorph {X : Type*} [TopologicalSpace X]
    (U : Set X) (J : Set ℝ) (ρ : X → ℝ) (η : X × ℝ → X) (r₀ : ℝ) (hr₀ : r₀ ∈ J)
    (hρ : ∀ x ∈ U, ρ x ∈ J)
    (hη : ∀ x ∈ U, ∀ r ∈ J, η (x, r) ∈ U)
    (hlevel : ∀ x ∈ U, ∀ r ∈ J, ρ (η (x, r)) = r)
    (hinit : ∀ x ∈ U, η (x, ρ x) = x)
    (hreset : ∀ x ∈ U, ∀ r ∈ J, ∀ s ∈ J, η (η (x, r), s) = η (x, s))
    (hcρ : ContinuousOn ρ U) (hcη : ContinuousOn η (U ×ˢ J)) :
    U ≃ₜ {x : U // ρ x = r₀} × J where
  toEquiv := radialProductEquiv U J ρ η r₀ hr₀ hρ hη hlevel hinit hreset
  continuous_toFun := by
    have hleft : Continuous (fun x : U => η (x, r₀)) :=
      hcη.comp_continuous (continuous_subtype_val.prodMk continuous_const)
        (fun x => ⟨x.property, hr₀⟩)
    have hright : Continuous (fun x : U => ρ x) :=
      hcρ.comp_continuous continuous_subtype_val (fun x => x.property)
    exact (hleft.subtype_mk _ |>.subtype_mk _).prodMk (hright.subtype_mk _)
  continuous_invFun := by
    have hmap : Continuous (fun z : {x : U // ρ x = r₀} × J =>
        ((z.1.1 : X), (z.2 : ℝ))) :=
      ((continuous_subtype_val.comp (continuous_subtype_val.comp continuous_fst)).prodMk
        (continuous_subtype_val.comp continuous_snd))
    exact (hcη.comp_continuous hmap (fun z => ⟨z.1.1.property, z.2.property⟩)).subtype_mk _

open AlmostSchur Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
  [CompactSpace M] [T2Space M] [Nonempty M] [PreconnectedSpace M]
/-- The regular region of an actual Obata function is homeomorphic to any
one of its radial levels times the full open radial interval. -/
theorem exists_obata_radial_product_with_energy {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      (∀ y, ‖gradient (I := I) f y‖ ^ 2 = K * (a ^ 2 - f y ^ 2)) ∧
      ∀ r₀ ∈ Ioo 0 (Real.pi / Real.sqrt K),
        Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
          {x : {x : M // -a < f x ∧ f x < a} // obataRadial K a f x = r₀} ×
            Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨a, ha, hb, hn, η, hηs, hp⟩ := exists_smooth_obata_radial_family hK hf hnon hH
  let U := {x : M | -a < f x ∧ f x < a}
  let J := Ioo 0 (Real.pi / Real.sqrt K)
  let ρ := obataRadial K a f
  have hρ : ∀ x ∈ U, ρ x ∈ J := by
    intro x hx
    have hm : -1 < f x / a := (lt_div_iff₀ ha).mpr (by nlinarith [hx.1])
    have hlt : f x / a < 1 := (div_lt_iff₀ ha).mpr (by simpa using hx.2)
    exact ⟨div_pos (Real.arccos_pos.mpr hlt) (Real.sqrt_pos.mpr hK),
      (div_lt_div_iff_of_pos_right (Real.sqrt_pos.mpr hK)).mpr (Real.arccos_lt_pi.mpr hm)⟩
  have hr : ∀ x ∈ U, ∀ r ∈ J, ρ (η (x, r)) = r :=
    fun x hx r hr => ((hp x hx).2.2.2.1 r hr).1
  have hη : ∀ x ∈ U, ∀ r ∈ J, η (x, r) ∈ U := by
    intro x hx r hrt
    have he := obataRadial_cos hK ha (η (x, r)) (hb (η (x, r)))
    change a * Real.cos (Real.sqrt K * ρ (η (x, r))) = f (η (x, r)) at he
    rw [hr x hx r hrt] at he
    change -a < f (η (x, r)) ∧ f (η (x, r)) < a
    rw [← he]
    exact obata_cos_level_mem hK ha hrt
  have hfc := hf.continuous
  have hcρ : Continuous ρ := by unfold ρ obataRadial; fun_prop
  refine ⟨a, ha, hb, hn, ?_⟩
  intro r₀ hr₀
  exact ⟨radialProductHomeomorph U J ρ η r₀ hr₀ hρ hη hr
    (fun x hx => (hp x hx).1) (fun x hx r hrt s _ => (hp x hx).2.1 r hrt s)
    hcρ.continuousOn hηs.continuousOn⟩

/-- Product coordinates without retaining the energy identity. -/
theorem exists_obata_radial_product {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ r₀ ∈ Ioo 0 (Real.pi / Real.sqrt K),
        Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
          {x : {x : M // -a < f x ∧ f x < a} // obataRadial K a f x = r₀} ×
            Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨a, ha, hb, _, hp⟩ := exists_obata_radial_product_with_energy hK hf hnon hH
  exact ⟨a, ha, hb, hp⟩
/-- The angular factor can be taken to be a whole ambient radial level.
This is the form that composes directly with the normal-sphere chart. -/
theorem exists_obata_whole_level_product {K : ℝ} (hK : 0 < K) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w) :
    ∃ a : ℝ, 0 < a ∧ (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ r₀ ∈ Ioo 0 (Real.pi / Real.sqrt K),
        Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
          {x : M // obataRadial K a f x = r₀} ×
            Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨a, ha, hb, hp⟩ := exists_obata_radial_product hK hf hnon hH
  refine ⟨a, ha, hb, ?_⟩
  intro r hr
  obtain ⟨e⟩ := hp r hr
  have hregular : ∀ x, obataRadial K a f x = r → -a < f x ∧ f x < a := by
    intro x hx
    have he := obataRadial_cos hK ha x (hb x)
    rw [hx] at he
    rw [← he]
    exact obata_cos_level_mem hK ha hr
  exact ⟨e.trans ((wholeLevelHomeomorph _ _ r hregular).prodCongr (Homeomorph.refl _))⟩
/-- A positive critical value fixes the amplitude of the constructed radial
product. No independent choice of normalization remains. -/
theorem obata_whole_level_product_at_positive_critical_value
    {K a : ℝ} (hK : 0 < K) (ha : 0 < a) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hnon : ∃ x y, f x ≠ f y)
    (hH : ∀ (x : M) (v w : TangentSpace I x),
      hessian (leviCivitaConnection (I := I)) f x v w = -K * f x * inner ℝ v w)
    (p : M) (hp : f p = a) (hcrit : gradient (I := I) f p = 0) :
    (∀ x, -a ≤ f x ∧ f x ≤ a) ∧
      ∀ r ∈ Ioo 0 (Real.pi / Real.sqrt K),
        Nonempty ({x : M // -a < f x ∧ f x < a} ≃ₜ
          {x : M // obataRadial K a f x = r} × Ioo 0 (Real.pi / Real.sqrt K)) := by
  obtain ⟨b, hb, hbound, hn, hprod⟩ :=
    exists_obata_radial_product_with_energy hK hf hnon hH
  have he := hn p
  rw [hcrit, hp, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  have hba : b = a := by
    have hs : b ^ 2 - a ^ 2 = 0 := (mul_eq_zero.mp he.symm).resolve_left hK.ne'
    nlinarith
  subst b
  refine ⟨hbound, ?_⟩
  intro r hr
  obtain ⟨e⟩ := hprod r hr
  have hregular : ∀ x, obataRadial K a f x = r → -a < f x ∧ f x < a := by
    intro x hx
    have he := obataRadial_cos hK ha x (hbound x)
    rw [hx] at he
    rw [← he]
    exact obata_cos_level_mem hK ha hr
  exact ⟨e.trans ((wholeLevelHomeomorph _ _ r hregular).prodCongr (Homeomorph.refl _))⟩

end LichnerowiczObata
