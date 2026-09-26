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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpvAITopology
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaCompact
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalSubsets

/-!
# Quasi-compactness of `Spa A A⁺` via `Spv(A, I)` (Wedhorn 7.5 / 7.12 / 7.35)

The faithful route to the quasi-compactness of the adic spectrum and of its rational
subsets, mirroring Wedhorn's own assembly (re-based 2026-07-03; supersedes the
`(A × A → Bool)`-cube closedness keystone of `SpaCompactNoHArch`, which encodes the
STRICTLY STRONGER "`Spa` pro-constructible in `Spv A`" — a B2 candidate given
Remark 7.6):

* **`rhoR`** — the continuous map between Boolean cubes sending the `basicOpen`-profile
  of `v` to its `W(T/s)`-profile (`W(T/s) = { w ∈ Spv A ; ∀ t ∈ T, w(t) ≤ w(s) ≠ 0 }`).
* **Wedhorn 7.5(iii)** (`wedhorn.txt:2862-2872`): for `T` finite with `I ⊆ √(T·A)`,
  `W(T/s) = r⁻¹(Spv(A,I)(T/s))` where `r` is the 7.1.2 retraction. Hence
  `rhoR '' (range ιSpvBool) = ιSpvR '' SpvAI A I`: the `R`-profile image of `Spv A`
  IS the `R`-profile image of `Spv(A, I)` — quasi-compactness of the latter as a
  continuous image of the (proven) compact `range ιSpvBool` (7.5(iv),
  `wedhorn.txt:2873-2884`).
* **Theorem 7.10** (`wedhorn.txt:2908-2926`): `Cont A = { v ∈ Spv(A,I) ; v(a) < 1 ∀ a ∈ I }`
  — inside the profile cube these are clopen coordinate conditions.
* **Theorem 7.35** (`wedhorn.txt:3186-3207`): `Spa A = Cont A ∩ ⋂_{f ∈ A⁺} {v(f) ≤ 1}` —
  again clopen coordinate conditions; hence the `Spa`-profile image is compact, and the
  profile map is inducing and injective on `Spa` (rational subsets form a basis, 7.35(2)),
  so `Spa A A⁺` is a compact space and each rational subset is quasi-compact.

The principal case (`I = (π)`, Tate) uses the FAITHFUL `restrictIdealSingle` machinery
(T-SPVAI, 2026-06-22); the general-`I` `cGammaIdeal` is the known-unfaithful B2 and is
not used here.
-/

@[expose] public section

open ValuationSpectrum

namespace ValuationSpectrum

variable {A : Type*} [CommRing A]

/-! ### R0 — the `W(T/s)`-profile cube and the connecting map `rhoR` -/

/-- The index of the profile cube: rational data `(T, s)` satisfying Wedhorn 7.5's side
condition `I ⊆ √(T·A)`. Only these coordinates are transported by the retraction
(7.5(iii)), and they suffice: they generate the topology of `Spv(A, I)` (7.5(ii)) and
encode the `Cont`/`Spa` conditions (`({1}, a)` and `({f}, 1)` both satisfy the side
condition trivially). -/
def RCoord (A : Type*) [CommRing A] (I : Ideal A) : Type _ :=
  {p : Finset A × A // I ≤ (Ideal.span (p.1 : Set A)).radical}

/-- The profile map between Boolean cubes: from the `basicOpen`-profile
`x = ιSpvBool v` to the `W(T/s)`-profile. The `(T, s)`-coordinate is the finite
Boolean formula `(∀ t ∈ T, x (t, s)) ∧ x (s, s)`; note `x (t, s)` already encodes
`v(t) ≤ v(s) ≠ 0` and `x (s, s)` encodes `v(s) ≠ 0` (covering `T = ∅`). -/
noncomputable def rhoR (I : Ideal A) (x : A × A → Bool) : RCoord A I → Bool :=
  fun p => (p.1.1.toList.all fun t => x (t, p.1.2)) && x (p.1.2, p.1.2)

/-- Each `rhoR`-coordinate depends on finitely many input coordinates, so `rhoR` is
continuous for the product-of-discrete topologies. -/
theorem continuous_rhoR (I : Ideal A) : Continuous (rhoR (A := A) I) := by
  refine continuous_pi fun p => ?_
  have hall : ∀ l : List A, Continuous fun x : A × A → Bool => l.all fun t => x (t, p.1.2) := by
    intro l
    induction l with
    | nil => simpa using continuous_const
    | cons t l ih =>
      simp only [List.all_cons]
      exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
        ((continuous_apply (t, p.1.2)).prodMk ih)
  exact (continuous_of_discreteTopology (f := fun q : Bool × Bool => q.1 && q.2)).comp
    ((hall p.1.1.toList).prodMk (continuous_apply (p.1.2, p.1.2)))

/-- The `W(T/s)`-profile of a point of `Spv A`. -/
noncomputable def ιSpvR (I : Ideal A) (v : Spv A) : RCoord A I → Bool :=
  rhoR I (ιSpvBool v)

@[simp]
theorem rhoR_ιSpv_bool (I : Ideal A) (v : Spv A) : rhoR I (ιSpvBool v) = ιSpvR I v := rfl

/-- Coordinate semantics of the `W(T/s)`-profile. -/
theorem ιSpvR_eq_true_iff (I : Ideal A) (v : Spv A) (p : RCoord A I) :
    ιSpvR I v p = true ↔ (∀ t ∈ p.1.1, v.vle t p.1.2) ∧ ¬ v.vle p.1.2 0 := by
  unfold ιSpvR rhoR ιSpvBool
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨hT, -, hs0⟩
    exact ⟨fun t ht => (hT t (Finset.mem_toList.mpr ht)).1, hs0⟩
  · rintro ⟨hT, hs0⟩
    exact ⟨fun t ht => ⟨hT t (Finset.mem_toList.mp ht), hs0⟩,
      (v.vle_total p.1.2 p.1.2).elim id id, hs0⟩

/-! ### R1 — Wedhorn 7.5(iii): the profile image of `Spv A` is the profile image of
`Spv(A, I)`

The two order-transfer lemmas for the convex-window restriction: the `≤`-side is
preserved unconditionally (values outside the window truncate to `0`, and convexity
forces an in-window sandwich), and the order is reflected wherever the restricted upper
value is nonzero (same sandwich). -/

/-- Order transfer UP: `w g ≤ w h` implies the restricted values are ordered. -/
theorem restrictToConvexBounded_le_of_le
    {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : w a ≠ 0, 1 ≤ w a → Units.mk0 (w a) ha ∈ H)
    {g h : R} (hle : w g ≤ w h) :
    w.restrictToConvexBounded H hH_ge g ≤ w.restrictToConvexBounded H hH_ge h := by
  by_cases hg0 : w g = 0
  · rw [Valuation.restrictToConvexBounded_apply_zero w H hH_ge hg0]
    exact zero_le'
  by_cases hgm : Units.mk0 (w g) hg0 ∈ H
  · -- `g` in the window; then `h` is too (else `w g ≤ w h < 1` sandwiches `w h` in `H`).
    have hh0 : w h ≠ 0 := fun h0 => hg0 (le_antisymm (h0 ▸ hle) zero_le')
    have hhm : Units.mk0 (w h) hh0 ∈ H := by
      by_contra hhm
      have hh_lt : w h < 1 := by
        by_contra hge
        push_neg at hge
        exact hhm (hH_ge h hh0 hge)
      exact hhm (H.convex hgm (one_mem H)
        (Units.val_le_val.mp (by simpa using hle))
        (Units.val_le_val.mp (by simpa using hh_lt.le)))
    rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hg0 hgm,
      Valuation.restrictToConvexBounded_apply_mem w H hH_ge hh0 hhm]
    exact WithZero.coe_le_coe.mpr (Subtype.mk_le_mk.mpr (Units.val_le_val.mp
      (by simpa using hle)))
  · rw [Valuation.restrictToConvexBounded_apply_not_mem w H hH_ge hg0 hgm]
    exact zero_le'

/-- Order transfer DOWN (specialization): ordered restricted values with nonzero upper
value give back `w g ≤ w h ≠ 0`. -/
theorem restrictToConvexBounded_le_reflect
    {R : Type*} [CommRing R] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : w a ≠ 0, 1 ≤ w a → Units.mk0 (w a) ha ∈ H)
    {g h : R}
    (hle : w.restrictToConvexBounded H hH_ge g ≤ w.restrictToConvexBounded H hH_ge h)
    (hne : w.restrictToConvexBounded H hH_ge h ≠ 0) :
    w g ≤ w h ∧ w h ≠ 0 := by
  by_cases hh0 : w h = 0
  · exact absurd (Valuation.restrictToConvexBounded_apply_zero w H hH_ge hh0) hne
  by_cases hhm : Units.mk0 (w h) hh0 ∈ H
  swap
  · exact absurd (Valuation.restrictToConvexBounded_apply_not_mem w H hH_ge hh0 hhm) hne
  refine ⟨?_, hh0⟩
  by_cases hg0 : w g = 0
  · rw [hg0]
    exact zero_le'
  by_cases hgm : Units.mk0 (w g) hg0 ∈ H
  · rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hg0 hgm,
      Valuation.restrictToConvexBounded_apply_mem w H hH_ge hh0 hhm] at hle
    have h1 := Subtype.mk_le_mk.mp (WithZero.coe_le_coe.mp hle)
    simpa using Units.val_le_val.mpr h1
  · -- `g` outside the window with `w h < w g < 1` would sandwich `w g` in `H`.
    by_contra hlt
    push_neg at hlt
    have hg_lt : w g < 1 := by
      by_contra hge
      push_neg at hge
      exact hgm (hH_ge g hg0 hge)
    exact hgm (H.convex hhm (one_mem H)
      (Units.val_le_val.mp (by simpa using hlt.le))
      (Units.val_le_val.mp (by simpa using hg_lt.le)))

variable [TopologicalSpace A]

/-- `vle`-bridge for `v` via its canonical valuation. -/
theorem vle_iff_canonical (v : Spv A) (g h : A) :
    v.vle g h ↔
      (letI : ValuativeRel A := v.toValuativeRel
       ValuativeRel.valuation A g ≤ ValuativeRel.valuation A h) := by
  letI : ValuativeRel A := v.toValuativeRel
  exact Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation A) g h

/-- `v(a) = 0` in canonical-valuation form. -/
theorem vle_zero_iff_canonical (v : Spv A) (a : A) :
    v.vle a 0 ↔
      (letI : ValuativeRel A := v.toValuativeRel
       ValuativeRel.valuation A a = 0) := by
  letI : ValuativeRel A := v.toValuativeRel
  rw [vle_iff_canonical]
  simp

/-- Transitivity of `vle` (through the canonical valuation). -/
theorem vle_trans' {v : Spv A} {a b c : A} (h1 : v.vle a b) (h2 : v.vle b c) :
    v.vle a c := by
  rw [vle_iff_canonical] at h1 h2 ⊢
  exact le_trans h1 h2

/-- `v(I) = 0` puts `v` in `Spv(A, I)` (the cofinality disjunct holds vacuously on zero
values). -/
theorem isInSpvAI_of_forall_vle_zero {v : Spv A} {I : Ideal A}
    (h : ∀ a ∈ I, v.vle a 0) : v ∈ SpvAI A I := by
  letI : ValuativeRel A := v.toValuativeRel
  refine Or.inl fun a ha => ?_
  have h0 : ValuativeRel.valuation A a = 0 := by
    have h1 := (vle_iff_canonical v a 0).mp (h a ha)
    simpa using h1
  intro γ hγ
  exact ⟨1, by simpa [h0] using hγ⟩

/-! ### R1' — the faithful PRINCIPAL retraction (Wedhorn 7.1.2 for `I = (g)`)

The general `restrictIdeal`-retraction's `SpvAI`-membership rests on the unfaithful
`cGammaIdeal` (B2, 2026-06-22). The principal case — the only one the Tate-ring
application needs (`IsTateRing.exists_principal_pairOfDefinition`) — is faithful:
`ofValuation_restrictIdealSingle_isInSpvAI` is proven. We build the `Spv`-level
retraction on `restrictIdealSingle` and prove Wedhorn 7.5(iii) for it. -/

/-- **Wedhorn 7.4(iii), principal case.** For `v ∈ Spv(A, (g))` (with `v(g) ≠ 0`) the
window `cΓ_v((g))` contains every nonzero value-unit — i.e. it is all of `Γ_v`.

* Cofinal disjunct: `v(g)` is cofinal, so any `v(a) < 1` is sandwiched
  `v(g)^n < v(a) < 1` with both ends in the window (`v(g)⁻¹` is a generator).
* Microbial disjunct: the microbial witness `b` puts `v(a)` directly in the
  characteristic generators `cGammaUnits`. -/
theorem cGammaSingle_univ_of_isInSpvAI {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {w : Valuation A Γ₀} {g : A} (hg : w g ≠ 0)
    (h : (∀ a ∈ Ideal.span {g}, Valuation.CofinalValue w a) ∨ Valuation.IsMicrobial w) :
    ∀ (a : A) (ha : w a ≠ 0), Units.mk0 (w a) ha ∈ Valuation.cGammaSingle w g hg := by
  intro a ha
  by_cases h_ge : 1 ≤ w a
  · exact Valuation.vUnit_mem_cGammaSingle hg h_ge ha
  · push_neg at h_ge
    rcases h with h_cof | h_micr
    · -- cofinality of `v(g)` sandwiches `v(a)` between `(mk0 v(g))^n` and `1`.
      obtain ⟨n, hn⟩ :=
        h_cof g (Ideal.mem_span_singleton_self g) (w a) (zero_lt_iff.mpr ha)
      have hg_mem : Units.mk0 (w g) hg ∈ Valuation.cGammaSingle w g hg := by
        have := Valuation.invGen_mem_cGammaSingle w g hg
        simpa using inv_mem this
      have hpow_mem : (Units.mk0 (w g) hg) ^ n ∈ Valuation.cGammaSingle w g hg :=
        pow_mem hg_mem n
      refine (Valuation.cGammaSingle w g hg).convex hpow_mem
        (one_mem (Valuation.cGammaSingle w g hg)) ?_ ?_
      · exact Units.val_le_val.mp (by simpa using hn.le)
      · exact Units.val_le_val.mp (by simpa using h_ge.le)
    · obtain ⟨b, hb_ge_one, hb_inv_le, hb_ge⟩ := h_micr (w a) (zero_lt_iff.mpr ha)
      have hvb_ne : w b ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hb_ge_one)
      refine ConvexSubgroup.subset_minContain _ (Set.mem_insert_of_mem _ ?_)
      refine ⟨b, hb_ge_one, hvb_ne, ?_, ?_⟩
      · rw [← Units.val_le_val]; exact hb_inv_le
      · rw [← Units.val_le_val]; exact hb_ge

/-- **Full-window restriction is a value-equivalence** (generic form of
`restrictIdeal_isEquiv_of_cGammaIdeal_univ` for an arbitrary convex window). -/
theorem restrictToConvexBounded_isEquiv_of_univ {R : Type*} [CommRing R] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] (w : Valuation R Γ₀) (H : ConvexSubgroup Γ₀ˣ)
    (hH_ge : ∀ a : R, ∀ ha : w a ≠ 0, 1 ≤ w a → Units.mk0 (w a) ha ∈ H)
    (huniv : ∀ (a : R) (ha : w a ≠ 0), Units.mk0 (w a) ha ∈ H) :
    (w.restrictToConvexBounded H hH_ge).IsEquiv w := by
  intro r s
  by_cases hr : w r = 0
  · rw [Valuation.restrictToConvexBounded_apply_zero w H hH_ge hr, hr]
    simp only [zero_le']
  · rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hr (huniv r hr)]
    by_cases hs : w s = 0
    · rw [Valuation.restrictToConvexBounded_apply_zero w H hH_ge hs, hs]
      constructor
      · intro h
        exact absurd (le_zero_iff.mp h) WithZero.coe_ne_zero
      · intro h
        rw [le_zero_iff] at h
        exact absurd h hr
    · rw [Valuation.restrictToConvexBounded_apply_mem w H hH_ge hs (huniv s hs)]
      rw [show ((⟨Units.mk0 (w r) hr, huniv r hr⟩ : H.toSubgroup) :
          WithZero H.toSubgroup) ≤ _ ↔ _ from WithZero.coe_le_coe]
      exact Units.val_le_val.symm

open Classical in
/-- **The faithful principal `Spv`-level retraction**: restrict to the window
`cΓ_v((g))` when `v(g) ≠ 0`; fix `v` when `v(g) = 0` (there `v ∈ Spv(A, (g))` holds
vacuously through the cofinality disjunct). -/
noncomputable def restrictIdealSingleSpv (v : Spv A) (g : A) : Spv A :=
  letI : ValuativeRel A := v.toValuativeRel
  if hg : (ValuativeRel.valuation A) g = 0 then v
  else ofValuation ((ValuativeRel.valuation A).restrictIdealSingle g hg)

theorem restrictIdealSingleSpv_of_zero {v : Spv A} {g : A} (hg : v.vle g 0) :
    restrictIdealSingleSpv v g = v := by
  letI : ValuativeRel A := v.toValuativeRel
  have h0 : (ValuativeRel.valuation A) g = 0 := (vle_zero_iff_canonical v g).mp hg
  simp only [restrictIdealSingleSpv, dif_pos h0]

theorem restrictIdealSingleSpv_of_ne {v : Spv A} {g : A} (hg : ¬ v.vle g 0) :
    restrictIdealSingleSpv v g =
      (letI : ValuativeRel A := v.toValuativeRel
       ofValuation ((ValuativeRel.valuation A).restrictIdealSingle g
         (fun h0 => hg ((vle_zero_iff_canonical v g).mpr h0)))) := by
  letI : ValuativeRel A := v.toValuativeRel
  have h0 : (ValuativeRel.valuation A) g ≠ 0 :=
    fun h => hg ((vle_zero_iff_canonical v g).mpr h)
  simp only [restrictIdealSingleSpv, dif_neg h0]

/-- The principal retraction lands in `Spv(A, (g))` — faithfully
(`ofValuation_restrictIdealSingle_isInSpvAI`), no `cGammaIdeal` sorry. -/
theorem restrictIdealSingleSpv_mem_SpvAI (v : Spv A) (g : A) :
    restrictIdealSingleSpv v g ∈ SpvAI A (Ideal.span {g}) := by
  by_cases hg : v.vle g 0
  · rw [restrictIdealSingleSpv_of_zero hg]
    refine isInSpvAI_of_forall_vle_zero fun a ha => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [vle_zero_iff_canonical] at hg ⊢
    letI : ValuativeRel A := v.toValuativeRel
    rw [map_mul, hg, mul_zero]
  · rw [restrictIdealSingleSpv_of_ne hg]
    letI : ValuativeRel A := v.toValuativeRel
    exact ofValuation_restrictIdealSingle_isInSpvAI (ValuativeRel.valuation A) g _

/-- **Wedhorn 7.5(2), principal case (fixed points).** `r(v) = v` for
`v ∈ Spv(A, (g))`. -/
theorem restrictIdealSingleSpv_eq_self_of_mem {v : Spv A} {g : A}
    (hv : v ∈ SpvAI A (Ideal.span {g})) : restrictIdealSingleSpv v g = v := by
  by_cases hg : v.vle g 0
  · exact restrictIdealSingleSpv_of_zero hg
  · rw [restrictIdealSingleSpv_of_ne hg]
    letI : ValuativeRel A := v.toValuativeRel
    exact (ofValuation_eq_of_isEquiv
      (restrictToConvexBounded_isEquiv_of_univ _ _ _
        (cGammaSingle_univ_of_isInSpvAI _ hv))).trans (ofValuation_valuation v)

/-- **Wedhorn 7.5(iii), principal profile form** (`wedhorn.txt:2862-2872`): for every
side-condition coordinate `p` and every `v : Spv A`, the `p`-profile coordinate of `v`
agrees with that of the principal retraction. -/
theorem ιSpvR_retractionSingle_eq (g : A) (I : Ideal A) (hIg : I = Ideal.span {g})
    (v : Spv A) (p : RCoord A I) :
    ιSpvR I (restrictIdealSingleSpv v g) p = ιSpvR I v p := by
  by_cases hg0 : v.vle g 0
  · rw [restrictIdealSingleSpv_of_zero hg0]
  · rw [restrictIdealSingleSpv_of_ne hg0]
    letI : ValuativeRel A := v.toValuativeRel
    set w := ValuativeRel.valuation A with hw_def
    have hg : w g ≠ 0 := fun h0 => hg0 ((vle_zero_iff_canonical v g).mpr h0)
    set w' := w.restrictIdealSingle g
      (fun h0 => hg0 ((vle_zero_iff_canonical v g).mpr h0)) with hw'_def
    -- vle on the retraction IS ≤ of `w'` (ofValuation's rel is definitionally ≤).
    have hbr : ∀ a b : A, (ofValuation w').vle a b ↔ w' a ≤ w' b := fun a b => Iff.rfl
    -- `w'(g) ≠ 0`: the generator's value-unit lies in its own window.
    have hg'_ne : w' g ≠ 0 := by
      have hg_mem : Units.mk0 (w g) hg ∈ Valuation.cGammaSingle w g hg := by
        have := Valuation.invGen_mem_cGammaSingle w g hg
        simpa using inv_mem this
      rw [hw'_def, Valuation.restrictIdealSingle,
        Valuation.restrictToConvexBounded_apply_mem w _ _ hg hg_mem]
      exact WithZero.coe_ne_zero
    rw [Bool.eq_iff_iff, ιSpvR_eq_true_iff, ιSpvR_eq_true_iff]
    -- destructure the coordinate only AFTER the profile rewrites (v4.33 literal-leak)
    obtain ⟨⟨T, s⟩, hTI⟩ := p
    constructor
    · rintro ⟨hT, hs⟩
      have hs_ne : w' s ≠ 0 := by
        intro h0
        exact hs ((hbr s 0).mpr (by rw [h0, map_zero]))
      constructor
      · intro t ht
        have hle := (hbr t s).mp (hT t ht)
        rw [hw'_def, Valuation.restrictIdealSingle] at hle hs_ne
        rw [vle_iff_canonical]
        exact (restrictToConvexBounded_le_reflect w _ _ hle hs_ne).1
      · intro hcon
        have h0 : w s = 0 := (vle_zero_iff_canonical v s).mp hcon
        refine hs_ne ?_
        rw [hw'_def, Valuation.restrictIdealSingle]
        exact Valuation.restrictToConvexBounded_apply_zero w _ _ h0
    · rintro ⟨hT, hs0⟩
      -- Nonvanishing of `w'(s)`: else all of `T` dies, so `span T ≤ supp w'`; the side
      -- condition then kills `g` in `w'`, contradicting `w'(g) ≠ 0`.
      have hs'_ne : w' s ≠ 0 := by
        intro h0
        have hTz : ∀ t ∈ (T : Finset A), t ∈ w'.supp := by
          intro t ht
          have hle : w t ≤ w s := (vle_iff_canonical v t s).mp (hT t ht)
          have hle' : w' t ≤ w' s := by
            rw [hw'_def, Valuation.restrictIdealSingle]
            exact restrictToConvexBounded_le_of_le w _ _ hle
          rw [h0, le_zero_iff] at hle'
          exact (Valuation.mem_supp_iff w' t).mpr hle'
        have hspan : Ideal.span (T : Set A) ≤ w'.supp :=
          Ideal.span_le.mpr fun t ht => hTz t ht
        have hg_rad : g ∈ (Ideal.span (T : Set A)).radical :=
          hTI (hIg ▸ Ideal.mem_span_singleton_self g)
        obtain ⟨n, hn⟩ := hg_rad
        have hprime : (w'.supp).IsPrime := inferInstance
        have hg_supp : g ∈ w'.supp := hprime.mem_of_pow_mem n (hspan hn)
        exact hg'_ne ((Valuation.mem_supp_iff w' g).mp hg_supp)
      refine ⟨fun t ht => ?_, fun hcon => ?_⟩
      · rw [hbr, hw'_def, Valuation.restrictIdealSingle]
        exact restrictToConvexBounded_le_of_le w _ _
          ((vle_iff_canonical v t s).mp (hT t ht))
      · have h0 := (hbr s 0).mp hcon
        rw [map_zero, le_zero_iff] at h0
        exact hs'_ne h0

/-! ### R2 — the compact profile set

To avoid quantifying images over non-side-condition coordinates, define the compact
carrier as the FULL `rhoR`-image of the (proven compact) `basicOpen`-profile range. -/

/-- The `W`-profile carrier: image of the compact `range ιSpvBool` under the continuous
`rhoR`. Compact by construction; equals the profile image of `Spv(A, I)` by 7.5(iii). -/
noncomputable def profileCarrier (A : Type*) [CommRing A] (I : Ideal A) :
    Set (RCoord A I → Bool) :=
  rhoR I '' Set.range (ιSpvBool : Spv A → A × A → Bool)

theorem isCompact_profileCarrier (I : Ideal A) : IsCompact (profileCarrier A I) :=
  (isCompact_range_ιSpv_bool).image (continuous_rhoR I)

/-! ### R3 — Wedhorn 7.10 / 7.35 as clopen coordinate conditions -/

variable [PlusSubring A]

/-- The `({1}, a)`-coordinate satisfies the side condition trivially
(`span {1} = ⊤`). -/
def RCoord.oneOver (I : Ideal A) (a : A) : RCoord A I :=
  ⟨(({1} : Finset A), a), by
    have h : Ideal.span (({1} : Finset A) : Set A) = ⊤ := by
      simp [Ideal.span_singleton_one]
    rw [h, Ideal.radical_top]
    exact le_top⟩

open Classical in
/-- The `({f, 1}, 1)`-coordinate (encoding `v(f) ≤ 1`) satisfies the side condition
trivially (`1 ∈ T` gives `span T = ⊤`). -/
noncomputable def RCoord.leOne (I : Ideal A) (f : A) : RCoord A I :=
  ⟨((({f, 1} : Finset A)), (1 : A)), by
    have h : Ideal.span ((({f, 1} : Finset A)) : Set A) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span (by simp)) isUnit_one
    rw [h, Ideal.radical_top]
    exact le_top⟩

/-- The `Spa`-profile conditions inside the profile cube, for a PRINCIPAL generator `g`
(the image in `A` of the principal Tate pair's `π`): the coordinate `({1}, g)` is `false`
(encoding `v(g) < 1`, as `W({1}/g) = {v(g) ≥ 1}`), and for `f ∈ A⁺` the coordinate
`({f,1}, 1)` is `true` (encoding `v(f) ≤ 1`). Theorem 7.10's hypothesis `v(a) < 1` on
all of `P.I = (π)` follows from the single `g`-condition by coefficient absorption:
`a = c·π` with `c ∈ A₀` and `v(c) ≤ 1`. -/
def spaProfileConditions (I : Ideal A) (g : A) : Set (RCoord A I → Bool) :=
  { y | y (RCoord.oneOver I g) = false ∧
        ∀ f ∈ (A⁺ : Subring A), y (RCoord.leOne I f) = true }

/-- The conditions cut out a closed subset (coordinate cylinders in a product of
discrete spaces). -/
theorem isClosed_spaProfileConditions (I : Ideal A) (g : A) :
    IsClosed (spaProfileConditions (A := A) I g) := by
  have hrw : spaProfileConditions (A := A) I g =
      {y : RCoord A I → Bool | y (RCoord.oneOver I g) = false} ∩
      ⋂ f ∈ (A⁺ : Subring A), {y : RCoord A I → Bool | y (RCoord.leOne I f) = true} := by
    ext y
    simp [spaProfileConditions]
  rw [hrw]
  refine IsClosed.inter ?_ ?_
  · have h : {y : RCoord A I → Bool | y (RCoord.oneOver I g) = false} =
        (fun y : RCoord A I → Bool => y (RCoord.oneOver I g)) ⁻¹' {false} := rfl
    rw [h]
    exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)
  · refine isClosed_biInter fun f _ => ?_
    have h : {y : RCoord A I → Bool | y (RCoord.leOne I f) = true} =
        (fun y : RCoord A I → Bool => y (RCoord.leOne I f)) ⁻¹' {true} := rfl
    rw [h]
    exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)

/-- **Wedhorn 7.10 + 7.35, profile form (principal Tate pair).** Let `P` be a pair of
definition with `P.I = (π)` principal, `P.A₀ ≤ A⁺`, and `I = (↑π)` the generated ideal
of `A`. The `Spa`-profile image equals the compact carrier intersected with the clopen
conditions.

`⊆`: `Spa ⊆ Spv` gives carrier membership; a continuous `v` has `v(↑π) < 1`
(`not_vle_one_of_mem_spa_of_topologicallyNilpotent`) and `v(f) ≤ 1` for `f ∈ A⁺`.
`⊇`: given `y = ιSpvR I v`, Wedhorn 7.5(iii) (`ιSpvR_retractionSingle_eq`) rewrites
`y = ιSpvR I w` for the principal retraction `w ∈ Spv(A, I)`; the conditions transported
to `w` say `w(↑π) < 1` and `w ≤ 1` on `A⁺ ⊇ A₀`; Theorem 7.10's converse
(`Spv.isContinuous_of_isInSpvAI_of_lt_one`, with `w(a) < 1` on `P.I` by coefficient
absorption `a = c·π`) yields `w ∈ Cont A`, hence `w ∈ Spa A A⁺` and `y ∈ ιSpvR '' Spa`. -/
theorem image_ιSpvR_spa_eq [IsTopologicalRing A] (P : PairOfDefinition A) {π : P.A₀}
    (hπ : P.I = Ideal.span {π}) (hA₀le : ∀ x : P.A₀, (x : A) ∈ (A⁺ : Subring A))
    (I : Ideal A) (hIeq : I = Ideal.span {((π : A))}) :
    ιSpvR I '' (Spa A A⁺) = profileCarrier A I ∩ spaProfileConditions I (π : A) := by
  have hπ_tn : IsTopologicallyNilpotent ((π : A)) :=
    P.isTopologicallyNilpotent_of_mem (hπ ▸ Ideal.mem_span_singleton_self π)
  apply Set.Subset.antisymm
  · rintro y ⟨v, hv, rfl⟩
    refine ⟨⟨ιSpvBool v, ⟨v, rfl⟩, rfl⟩, ?_, ?_⟩
    · -- `v(π) < 1` for continuous `v` (forward 7.10, via topological nilpotence).
      rw [Bool.eq_false_iff]
      intro htrue
      rw [ιSpvR_eq_true_iff] at htrue
      have h1 : v.vle 1 ((π : A)) := htrue.1 1 (by simp [RCoord.oneOver])
      exact not_vle_one_of_mem_spa_of_topologicallyNilpotent hv hπ_tn h1
    · intro f hf
      rw [ιSpvR_eq_true_iff]
      refine ⟨fun t ht => ?_, v.not_vle_one_zero⟩
      simp only [RCoord.leOne, Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact hv.2 _ hf
      · exact (v.vle_total 1 1).elim id id
  · rintro y ⟨⟨x, ⟨v, rfl⟩, rfl⟩, hone, hplus⟩
    set w := restrictIdealSingleSpv v ((π : A)) with hw_def
    have hprofile : ιSpvR I w = ιSpvR I v :=
      funext fun p => ιSpvR_retractionSingle_eq ((π : A)) I hIeq v p
    have hw_mem : w ∈ SpvAI A I := by
      rw [hIeq]
      exact restrictIdealSingleSpv_mem_SpvAI v _
    have hone_w : ιSpvR I w (RCoord.oneOver I ((π : A))) = false := by
      rw [hprofile]; exact hone
    have hplus_w : ∀ f ∈ (A⁺ : Subring A), ιSpvR I w (RCoord.leOne I f) = true := by
      intro f hf
      rw [hprofile]; exact hplus f hf
    letI : ValuativeRel A := w.toValuativeRel
    set wv := ValuativeRel.valuation A with hwv_def
    have h_le_one : ∀ a : P.A₀, wv ((a : A)) ≤ 1 := by
      intro a
      have hcoord := hplus_w (a : A) (hA₀le a)
      rw [ιSpvR_eq_true_iff] at hcoord
      have hle : w.vle ((a : A)) 1 :=
        hcoord.1 (a : A) (by simp [RCoord.leOne])
      have h2 := (vle_iff_canonical w ((a : A)) 1).mp hle
      simpa using h2
    have h_lt_pi : wv ((π : A)) < 1 := by
      by_contra hge
      push_neg at hge
      have hge' : wv 1 ≤ wv ((π : A)) := by
        rw [map_one]
        exact hge
      have hne : wv ((π : A)) ≠ 0 := by
        intro h0
        rw [map_one, h0] at hge'
        simp at hge'
      have htrue : ιSpvR I w (RCoord.oneOver I ((π : A))) = true := by
        rw [ιSpvR_eq_true_iff]
        refine ⟨fun t ht => ?_, fun hcon => hne ((vle_zero_iff_canonical w _).mp hcon)⟩
        simp only [RCoord.oneOver, Finset.mem_singleton] at ht
        subst ht
        exact (vle_iff_canonical w 1 ((π : A))).mpr hge'
      rw [hone_w] at htrue
      exact Bool.false_ne_true htrue
    have h_lt_one : ∀ a ∈ P.I, wv ((P.A₀.subtype a)) < 1 := by
      intro a ha
      rw [hπ] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      have hmul : wv ((P.A₀.subtype (c * π))) = wv ((c : A)) * wv ((π : A)) := by
        rw [show (P.A₀.subtype (c * π) : A) = (c : A) * ((π : A)) from rfl, map_mul]
      rw [hmul]
      calc wv ((c : A)) * wv ((π : A)) ≤ 1 * wv ((π : A)) := by
            gcongr
            exact h_le_one c
        _ = wv ((π : A)) := one_mul _
        _ < 1 := h_lt_pi
    have hmap : Ideal.map P.A₀.subtype P.I = I := by
      rw [hπ, Ideal.map_span, Set.image_singleton, hIeq]
      rfl
    have h_in : Spv.IsInSpvAI w (Ideal.map P.A₀.subtype P.I) := by
      rw [hmap]
      exact hw_mem
    have hcont : w.IsContinuous :=
      Spv.isContinuous_of_isInSpvAI_of_lt_one P w h_in (fun a => h_le_one a) h_lt_one
    have hbdd : ∀ f ∈ (A⁺ : Subring A), w.vle f 1 := by
      intro f hf
      have hcoord := hplus_w f hf
      rw [ιSpvR_eq_true_iff] at hcoord
      exact hcoord.1 f (by simp [RCoord.leOne])
    exact ⟨w, ⟨hcont, hbdd⟩, hprofile⟩

/-- The `Spa`-profile image is compact. -/
theorem isCompact_image_ιSpvR_spa [IsTopologicalRing A] (P : PairOfDefinition A)
    {π : P.A₀} (hπ : P.I = Ideal.span {π})
    (hA₀le : ∀ x : P.A₀, (x : A) ∈ (A⁺ : Subring A))
    (I : Ideal A) (hIeq : I = Ideal.span {((π : A))}) :
    IsCompact (ιSpvR I '' (Spa A A⁺)) := by
  rw [image_ιSpvR_spa_eq P hπ hA₀le I hIeq]
  exact (isCompact_profileCarrier I).inter_right (isClosed_spaProfileConditions I (π : A))

/-! ### R4 — transfer back along the Sierpinski embedding

`ιSpv_isEmbedding` (proven) reduces compactness of a subset of `Spv A` to compactness
of its `ιSpv`-image in the Sierpinski cube. On `Spa` the subspace topology is generated
by the side-condition rational subsets (Wedhorn 7.5(ii)/7.35(2) basis argument), so the
`RCoord`-indexed Sierpinski profile is itself an embedding of `Spa`, and compactness of
the Bool-profile image (R3) transfers. -/

/-- **Wedhorn 7.35(2) basis substrate**: for `v ∈ Spa A A⁺` and a basic open
`basicOpen g h ∋ v`, there is a side-condition datum `(T, s)` with
`v ∈ rationalOpen T s ⊆ basicOpen g h`. Take `s := h`, `T := {g} ∪ Tₙ` where `Tₙ`
finitely generates (the image of) `P.I ^ n` and `n` is chosen by continuity of `v` so
that `v < v(h)` on `P.I ^ n`. -/
theorem exists_rational_between_of_mem_basicOpen [IsTopologicalRing A]
    (P : PairOfDefinition A) (I : Ideal A)
    (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)))
    {v : Spv A} (hv : v ∈ Spa A A⁺) {g h : A} (hgh : v ∈ basicOpen g h) :
    ∃ (T : Finset A) (_ : I ≤ (Ideal.span (T : Set A)).radical),
      v ∈ rationalOpen T h ∧ rationalOpen T h ⊆ basicOpen g h := by
  classical
  obtain ⟨hvle, hne⟩ := hgh
  letI : ValuativeRel A := v.toValuativeRel
  set wv := ValuativeRel.valuation A with hwv_def
  have hwh_ne : wv h ≠ 0 := fun h0 => hne ((vle_zero_iff_canonical v h).mpr h0)
  have hcont : v.IsContinuous := hv.1
  have h_open : IsOpen {x : A | wv x < wv h} := hcont (wv h)
  have h0mem : (0 : A) ∈ {x : A | wv x < wv h} := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_lt_iff.mpr hwh_ne
  obtain ⟨n, -, hsub⟩ := P.hasBasis_nhds_zero.mem_iff.mp (h_open.mem_nhds h0mem)
  obtain ⟨Gn, hGn⟩ := Ideal.FG.pow (n := n) P.fg
  refine ⟨insert g (Gn.image (fun b : P.A₀ => (b : A))), ?_, ⟨hv, fun t ht => ?_, hne⟩, ?_⟩
  · -- side condition: `I ≤ √(span T)` — every generator image has its `n`-th power in
    -- `span (image Gn) ⊆ span T`.
    rw [hIeq, Ideal.span_le]
    rintro x ⟨b, hbI, rfl⟩
    refine ⟨n, ?_⟩
    have hbn : b ^ n ∈ P.I ^ n := Ideal.pow_mem_pow hbI n
    rw [← hGn] at hbn
    have hcoe : (P.A₀.subtype b) ^ n = P.A₀.subtype (b ^ n) := by
      rw [map_pow]
    rw [hcoe]
    have hmem := Ideal.mem_map_of_mem (P.A₀.subtype) hbn
    rw [Ideal.map_span] at hmem
    refine Ideal.span_mono ?_ hmem
    rw [Finset.coe_insert, Finset.coe_image]
    intro y hy
    obtain ⟨c, hcG, rfl⟩ := hy
    exact Set.mem_insert_of_mem _ ⟨c, hcG, rfl⟩
  · -- membership: `v(t) ≤ v(h)` for each `t ∈ T` (for `g` by hypothesis, for the
    -- `Gn`-images because they lie in the continuity neighborhood).
    rcases Finset.mem_insert.mp ht with rfl | htG
    · exact hvle
    · obtain ⟨b, hbG, rfl⟩ := Finset.mem_image.mp htG
      have hb_pow : b ∈ ((P.I ^ n : Ideal P.A₀) : Set P.A₀) := by
        rw [← hGn]
        exact Ideal.subset_span hbG
      have hb_nbhd : ((b : A)) ∈ {x : A | wv x < wv h} :=
        hsub ⟨b, hb_pow, rfl⟩
      exact (vle_iff_canonical v _ h).mpr (le_of_lt hb_nbhd)
  · rintro u ⟨-, huT, hus⟩
    exact ⟨huT g (Finset.mem_insert_self g _), hus⟩

/-- The Sierpinski `R`-profile: coordinate `p` tests membership in the side-condition
rational subset `R(p)`. Factors as `(· = true) ∘ ιSpvR I`, so its `Spa`-image is a
continuous image of the (compact) Bool profile image. -/
noncomputable def ιSpvPropR (I : Ideal A) (v : Spv A) : RCoord A I → Prop :=
  fun p => ιSpvR I v p = true

/-- The Bool-to-Sierpinski comparison map on the `R`-cube is continuous. -/
theorem continuous_toProp_rcoord (I : Ideal A) :
    Continuous (fun (y : RCoord A I → Bool) (p : RCoord A I) => y p = true) :=
  continuous_pi fun p =>
    (continuous_of_discreteTopology (f := fun b : Bool => b = true)).comp
      (continuous_apply p)

/-- **The `R`-profile is inducing on `Spa A A⁺`** (Wedhorn 7.35(2): side-condition
rational subsets form a basis of the subspace topology; one direction is
`rationalOpen_isOpen`, the other is the basis lemma above). -/
theorem isInducing_ιSpvPropR_spa [IsTopologicalRing A] (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    Topology.IsInducing (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) := by
  classical
  refine ⟨?_⟩
  have hstep1 : TopologicalSpace.induced
      (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) Pi.topologicalSpace =
      TopologicalSpace.generateFrom
        {U | ∃ p : RCoord A I, U = Subtype.val ⁻¹' rationalOpen p.1.1 p.1.2} := by
    rw [show (Pi.topologicalSpace : TopologicalSpace (RCoord A I → Prop)) =
        ⨅ p, TopologicalSpace.induced (fun r : RCoord A I → Prop => r p) sierpinskiSpace
        from rfl]
    rw [induced_iInf]
    have hcoord : ∀ p : RCoord A I,
        TopologicalSpace.induced ((fun r : RCoord A I → Prop => r p) ∘
          (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A))) sierpinskiSpace =
          TopologicalSpace.generateFrom {Subtype.val ⁻¹' rationalOpen p.1.1 p.1.2} := by
      intro p
      rw [show sierpinskiSpace = TopologicalSpace.generateFrom {{True}} from rfl,
          induced_generateFrom_eq]
      congr 1
      ext U
      simp only [Set.image_singleton, Set.mem_singleton_iff]
      constructor
      · rintro rfl
        ext v
        simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
          eq_iff_iff, iff_true, ιSpvPropR, ιSpvR_eq_true_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨v.2, h1, h2⟩
        · rintro ⟨-, h1, h2⟩
          exact ⟨h1, h2⟩
      · rintro rfl
        ext v
        simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
          eq_iff_iff, iff_true, ιSpvPropR, ιSpvR_eq_true_iff]
        constructor
        · rintro ⟨-, h1, h2⟩
          exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨v.2, h1, h2⟩
    simp_rw [induced_compose, hcoord]
    rw [show (⨅ p : RCoord A I, TopologicalSpace.generateFrom
          {Subtype.val ⁻¹' rationalOpen p.1.1 p.1.2}) =
        TopologicalSpace.generateFrom
          (⋃ p : RCoord A I, {Subtype.val ⁻¹' rationalOpen p.1.1 p.1.2}) from
        generateFrom_iUnion.symm]
    congr 1
    ext U
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
  have hstep2 : (instTopologicalSpaceSubtype : TopologicalSpace ↥(Spa A A⁺)) =
      TopologicalSpace.generateFrom
        ((Set.preimage (Subtype.val : ↥(Spa A A⁺) → Spv A)) ''
          {U | ∃ f s : A, U = basicOpen f s}) := by
    rw [show (instTopologicalSpaceSubtype : TopologicalSpace ↥(Spa A A⁺)) =
        TopologicalSpace.induced (Subtype.val : ↥(Spa A A⁺) → Spv A)
          ValuationSpectrum.instTopologicalSpace from rfl]
    rw [show (ValuationSpectrum.instTopologicalSpace : TopologicalSpace (Spv A)) =
        TopologicalSpace.generateFrom {U | ∃ f s : A, U = basicOpen f s} from rfl]
    exact induced_generateFrom_eq
  rw [hstep1, hstep2]
  apply le_antisymm
  · -- side-condition rational traces are open in the subspace topology
    refine le_generateFrom fun U hU => ?_
    obtain ⟨p, rfl⟩ := hU
    rw [← hstep2]
    exact rationalOpen_isOpen _ _
  · -- basic-open traces are open in the rational-trace topology (basis lemma)
    refine le_generateFrom fun U hU => ?_
    obtain ⟨V, ⟨f, t, rfl⟩, rfl⟩ := hU
    have hcover : (Subtype.val ⁻¹' basicOpen f t : Set ↥(Spa A A⁺)) =
        ⋃₀ {W | (∃ p : RCoord A I, W = Subtype.val ⁻¹' rationalOpen p.1.1 p.1.2) ∧
          W ⊆ Subtype.val ⁻¹' basicOpen f t} := by
      ext v
      constructor
      · intro hv
        obtain ⟨T, hside, hmem, hsub⟩ :=
          exists_rational_between_of_mem_basicOpen P I hIeq v.2 hv
        exact ⟨Subtype.val ⁻¹' rationalOpen T t,
          ⟨⟨⟨(T, t), hside⟩, rfl⟩, Set.preimage_mono hsub⟩, hmem⟩
      · rintro ⟨W, ⟨-, hWsub⟩, hvW⟩
        exact hWsub hvW
    rw [hcover]
    exact TopologicalSpace.GenerateOpen.sUnion _ fun W hW =>
      TopologicalSpace.GenerateOpen.basic _ hW.1

/-- **The `R`-profile is injective on `Spa A A⁺`** (side-condition rational subsets
separate points, via the basis lemma + injectivity of the full Huber embedding). -/
theorem injective_ιSpvPropR_spa [IsTopologicalRing A] (P : PairOfDefinition A)
    (I : Ideal A) (hIeq : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀))) :
    Function.Injective (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) := by
  intro v₁ v₂ hEq
  have key : ∀ f t : A, (v₁ : Spv A) ∈ basicOpen f t ↔ (v₂ : Spv A) ∈ basicOpen f t := by
    have main : ∀ (w₁ w₂ : ↥(Spa A A⁺)),
        ιSpvPropR I (w₁ : Spv A) = ιSpvPropR I (w₂ : Spv A) →
        ∀ f t : A, (w₁ : Spv A) ∈ basicOpen f t → (w₂ : Spv A) ∈ basicOpen f t := by
      intro w₁ w₂ hE f t hmem
      obtain ⟨T, hside, hm, hsub⟩ :=
        exists_rational_between_of_mem_basicOpen P I hIeq w₁.2 hmem
      obtain ⟨-, hm1, hm2⟩ := hm
      have hco : ιSpvR I (w₁ : Spv A) ⟨(T, t), hside⟩ = true :=
        (ιSpvR_eq_true_iff I _ _).mpr ⟨hm1, hm2⟩
      have hco2 : ιSpvR I (w₂ : Spv A) ⟨(T, t), hside⟩ = true := by
        have := congrFun hE ⟨(T, t), hside⟩
        simp only [ιSpvPropR, eq_iff_iff] at this
        exact this.mp hco
      obtain ⟨h1, h2⟩ := (ιSpvR_eq_true_iff I _ _).mp hco2
      exact hsub ⟨w₂.2, h1, h2⟩
    intro f t
    exact ⟨main v₁ v₂ hEq f t, main v₂ v₁ hEq.symm f t⟩
  have hιSpv : ιSpv (v₁ : Spv A) = ιSpv (v₂ : Spv A) := by
    funext q
    exact propext ((ιSpv_iff_mem_basicOpen _ q.1 q.2).trans
      ((key q.1 q.2).trans (ιSpv_iff_mem_basicOpen _ q.1 q.2).symm))
  exact Subtype.ext (ιSpv_injective hιSpv)

/-- **`Spa A A⁺` is quasi-compact in `Spv A`** (Wedhorn 7.35(1), no `hArch`): the
`R`-profile embeds `Spa` into the Sierpinski `R`-cube, and its image is the continuous
image of the compact Bool-profile image (R3). -/
theorem isCompact_spa_noHArch [IsTopologicalRing A] (P : PairOfDefinition A)
    {π : P.A₀} (hπ : P.I = Ideal.span {π})
    (hA₀le : ∀ x : P.A₀, (x : A) ∈ (A⁺ : Subring A))
    (I : Ideal A) (hIeq : I = Ideal.span {((π : A))}) :
    IsCompact ((Spa A A⁺) : Set (Spv A)) := by
  have hIeq' : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)) := by
    rw [show Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)) =
        Ideal.map P.A₀.subtype P.I from rfl, hπ, Ideal.map_span, Set.image_singleton, hIeq]
    rfl
  have hEmb : Topology.IsEmbedding (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) :=
    ⟨isInducing_ιSpvPropR_spa P I hIeq', injective_ιSpvPropR_spa P I hIeq'⟩
  have himg : IsCompact ((fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) ''
      Set.univ) := by
    have h1 : ((fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) '' Set.univ) =
        (fun (y : RCoord A I → Bool) (p : RCoord A I) => y p = true) ''
          (ιSpvR I '' (Spa A A⁺)) := by
      rw [Set.image_univ]
      ext r
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨ιSpvR I (v : Spv A), ⟨(v : Spv A), v.2, rfl⟩, rfl⟩
      · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
        exact ⟨⟨v, hv⟩, rfl⟩
    rw [h1]
    exact (isCompact_image_ιSpvR_spa P hπ hA₀le I hIeq).image (continuous_toProp_rcoord I)
  have huniv : IsCompact (Set.univ : Set ↥(Spa A A⁺)) :=
    (hEmb.isCompact_iff (s := Set.univ)).mpr himg
  exact isCompact_iff_compactSpace.mpr (isCompact_univ_iff.mp huniv)

/-- **`Spa A A⁺` is a compact topological space** (instance form). -/
theorem compactSpace_spa_noHArch [IsTopologicalRing A] (P : PairOfDefinition A)
    {π : P.A₀} (hπ : P.I = Ideal.span {π})
    (hA₀le : ∀ x : P.A₀, (x : A) ∈ (A⁺ : Subring A))
    (I : Ideal A) (hIeq : I = Ideal.span {((π : A))}) :
    CompactSpace ↥(Spa A A⁺) :=
  isCompact_iff_compactSpace.mp (isCompact_spa_noHArch P hπ hA₀le I hIeq)

/-- **Rational subsets are quasi-compact** (Wedhorn 7.35(2)): the trace of
`rationalOpen T s` on `Spa A A⁺` is compact whenever the datum satisfies the openness
side condition. -/
theorem isCompact_subtype_rationalOpen [IsTopologicalRing A] (P : PairOfDefinition A)
    {π : P.A₀} (hπ : P.I = Ideal.span {π})
    (hA₀le : ∀ x : P.A₀, (x : A) ∈ (A⁺ : Subring A))
    (I : Ideal A) (hIeq : I = Ideal.span {((π : A))})
    (T : Finset A) (s : A)
    (hTI : I ≤ (Ideal.span (T : Set A)).radical) :
    IsCompact (Subtype.val ⁻¹' (rationalOpen T s) : Set ↥(Spa A A⁺)) := by
  have hIeq' : I = Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)) := by
    rw [show Ideal.span (P.A₀.subtype '' (P.I : Set P.A₀)) =
        Ideal.map P.A₀.subtype P.I from rfl, hπ, Ideal.map_span, Set.image_singleton, hIeq]
    rfl
  have hEmb : Topology.IsEmbedding (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) :=
    ⟨isInducing_ιSpvPropR_spa P I hIeq', injective_ιSpvPropR_spa P I hIeq'⟩
  refine (hEmb.isCompact_iff (s := Subtype.val ⁻¹' rationalOpen T s)).mpr ?_
  have h1 : (fun v : ↥(Spa A A⁺) => ιSpvPropR I (v : Spv A)) ''
      (Subtype.val ⁻¹' rationalOpen T s) =
      (fun (y : RCoord A I → Bool) (p : RCoord A I) => y p = true) ''
        ((ιSpvR I '' (Spa A A⁺)) ∩
          {y : RCoord A I → Bool | y ⟨(T, s), hTI⟩ = true}) := by
    ext r
    constructor
    · rintro ⟨v, hv, rfl⟩
      rw [Set.mem_preimage] at hv
      obtain ⟨hvSpa, h1, h2⟩ := hv
      exact ⟨ιSpvR I (v : Spv A), ⟨⟨(v : Spv A), v.2, rfl⟩,
        (ιSpvR_eq_true_iff I _ _).mpr ⟨h1, h2⟩⟩, rfl⟩
    · rintro ⟨y, ⟨⟨v, hvSpa, rfl⟩, hq⟩, rfl⟩
      obtain ⟨h1, h2⟩ := (ιSpvR_eq_true_iff I _ _).mp hq
      exact ⟨⟨v, hvSpa⟩, Set.mem_preimage.mpr ⟨hvSpa, h1, h2⟩, rfl⟩
  rw [h1]
  refine IsCompact.image ?_ (continuous_toProp_rcoord I)
  refine (isCompact_image_ιSpvR_spa P hπ hA₀le I hIeq).inter_right ?_
  have hcl : {y : RCoord A I → Bool | y ⟨(T, s), hTI⟩ = true} =
      (fun y : RCoord A I → Bool => y ⟨(T, s), hTI⟩) ⁻¹' {true} := rfl
  rw [hcl]
  exact IsClosed.preimage (continuous_apply _) (isClosed_discrete _)

end ValuationSpectrum
