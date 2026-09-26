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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.JetRings
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFNoetherian
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetGraphKoszul
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetNoetherianVertices

/-!
# Strict localization of the finite-jet Milnor square over a CDVF base ([FJP] §4)

Source: [FJP] §4 (Lemmas 4.1, 4.3, 4.4, Prop 4.5), ported to the generic base stack of the
CDVF campaign (crosswalk D9): `K` a complete nonarchimedean nontrivially normed field, with
the layer-1 uniformizer data `(ϖ : Uniformizer K)` and the unit-ball noetherianity input
`hK₀ : IsNoetherianRing (unitBall K)` wherever the graph–Koszul engine consumes a scaling
bundle or a noetherian pod. The Laurent original is `FiniteJetStrictLocalization.lean`; the
statements and proofs are identical except for the noetherianity sourcing, which now runs
through the K2 chain of `CDVFNoetherian.lean` instead of the `K = F((t))`-specific
transposition `isNoetherianRing_unitBall_gaussK`.

For an indexed open rational datum `(g, f₁, …, f_m)` on 𝓐 (`span ({g} ∪ range f) = ⊤` — in a
Tate ring openness of the ideal is generation of the unit ideal), write
`P_E = E⟨T₁,…,T_m⟩` for `E ∈ {𝓐, 𝓑, 𝓒, 𝓓}` and `I_E = (r₁, …, r_m)` with `r_i = gT_i − f_i`.

* **Lemma 4.1** (Tate extension of a strict pullback): the extended row
  `0 → P_𝓐 → P_𝓑 ⊕ P_𝓒 → P_𝓓 → 0` is strict exact with the same constants (here all 1),
  coefficientwise.
* **Lemma 4.3** (controlled graph-ideal pullback): `I_𝓐 ≅ I_𝓑 ×_{I_𝓓} I_𝓒` boundedly, and
  `I_𝓐` is closed in `P_𝓐` (the `d₂`-correction argument, constants (4.11)–(4.16)).
* **Lemma 4.4** (strict quotient lemma): the normed-group 3×3 lemma.
* **Prop 4.5** (strict Milnor localization): the quotient row
  `0 → 𝓐_α → 𝓑_α ⊕ 𝓒_α → 𝓓_α → 0` of graph quotients `E_α := P_E ⧸ I_E` (complete, since
  the ideals are closed) is exact, the induced map `𝓐_α → 𝓑_α × 𝓒_α` is a topological
  embedding, and `𝓒_α → 𝓓_α` is a continuous open surjection.
-/

@[expose] public section

open Filter Topology

namespace FiniteJetOver

open FiniteJet
open FiniteJet.RestrictedLaurent
open FiniteJet.GraphKoszul

namespace StrictLoc

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- `P_𝓐 = 𝓐⟨T₁,…,T_m⟩` and its three companions. -/
abbrev PA (m : ℕ) : Type _ := GraphKoszul.P (JetA K) m
abbrev PB (m : ℕ) : Type _ := GraphKoszul.P (JetB K) m
abbrev PC (m : ℕ) : Type _ := GraphKoszul.P (JetC K) m
abbrev PD (m : ℕ) : Type _ := GraphKoszul.P (JetD K) m

variable (m : ℕ)

/-- Coefficientwise `jB : P_𝓐 → P_𝓑`. -/
noncomputable def extJB : PA K m →+* PB K m :=
  mapRestricted (jB K) (norm_jB_le K) _

/-- Coefficientwise `ιC : P_𝓐 → P_𝓒`. -/
noncomputable def extIotaC : PA K m →+* PC K m :=
  mapRestricted (iotaC K) (fun a => le_of_eq (norm_iotaC K a)) _

/-- Coefficientwise `ρB : P_𝓑 → P_𝓓`. -/
noncomputable def extRhoB : PB K m →+* PD K m :=
  mapRestricted (rhoB K) (fun b => le_of_eq (norm_rhoB K b)) _

/-- Coefficientwise `ρC : P_𝓒 → P_𝓓`. -/
noncomputable def extRhoC : PC K m →+* PD K m :=
  mapRestricted (rhoC K) (norm_rhoC_le K) _

/-! ### Lemma 4.1 — the extended strict row, constants 1

[FJP] Lemma 4.1 (verbatim): "For every `n ≥ 0`, restricted Tate extension in `n` variables
carries a strict Milnor square to a strict Milnor square. With Gauss norms, the constants κ
and ρ above continue to work." (For the finite-jet square both may be taken equal to one,
[FJP] §4 after (4.2).) -/

theorem ext_square_commutes (p : PA K m) :
    extRhoB K m (extJB K m p) = extRhoC K m (extIotaC K m p) := by
  refine Subtype.ext ?_
  show MvPowerSeries.map (rhoB K) (MvPowerSeries.map (jB K) p.1) =
    MvPowerSeries.map (rhoC K) (MvPowerSeries.map (iotaC K) p.1)
  refine MvPowerSeries.ext fun s => ?_
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map, MvPowerSeries.coeff_map,
    MvPowerSeries.coeff_map]
  exact square_commutes K _

-- v4.33: the goal carries `↑d` at the (defeq-only) `PD`-def type plus raw
-- `MvPowerSeries`-lambdas; restore pre-v4.33 defeq behaviour for this declaration
-- (established bump-repair pattern; reconfirmed necessary at the abstract base `K`).
/-- Coefficientwise sectioning: the extended `ρC` is strictly surjective with constant 1. -/
theorem extRhoC_strict_surjective (d : PD K m) :
    ∃ c : PC K m, extRhoC K m c = d ∧ ‖c‖ = ‖d‖ := by
  classical
  have hmem : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => sectionD K (MvPowerSeries.coeff s d.1)) := by
    have hd : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) d.1 := d.2
    unfold MvPowerSeries.IsRestrictedGauss at hd ⊢
    refine hd.congr fun s => ?_
    show ‖MvPowerSeries.coeff s d.1‖ * _ =
      ‖MvPowerSeries.coeff s (fun s => sectionD K (MvPowerSeries.coeff s d.1))‖ * _
    rw [show MvPowerSeries.coeff s (fun s => sectionD K (MvPowerSeries.coeff s d.1)) =
      sectionD K (MvPowerSeries.coeff s d.1) from rfl, norm_sectionD]
  refine ⟨⟨fun s => sectionD K (MvPowerSeries.coeff s d.1), hmem⟩, ?_, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map (rhoC K) (fun s => sectionD K (MvPowerSeries.coeff s d.1)) = d.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    show rhoC K (sectionD K (MvPowerSeries.coeff s d.1)) = MvPowerSeries.coeff s d.1
    rw [rhoC_sectionD]
  · rw [MvRestricted.norm_eq, MvRestricted.norm_eq, MvPowerSeries.gaussNorm,
      MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    show ‖MvPowerSeries.coeff s (fun s => sectionD K (MvPowerSeries.coeff s d.1))‖ * _ = _
    rw [show MvPowerSeries.coeff s (fun s => sectionD K (MvPowerSeries.coeff s d.1)) =
      sectionD K (MvPowerSeries.coeff s d.1) from rfl, norm_sectionD]

-- v4.33: goals carry `↑b`/`↑c` at the (defeq-only) `PB`/`PC`-def types plus raw
-- subtype-valued `MvPowerSeries`-lambdas; restore pre-v4.33 defeq behaviour.
/-- The extended square is cartesian: a compatible pair comes from a unique element of
`P_𝓐` ([FJP] Lemma 4.1: "If `b = ∑ b_ν T^ν` and `c = ∑ c_ν T^ν` have the same image, each
coefficient pair comes from a unique `a_ν ∈ R`"). -/
theorem ext_milnorRow_exact (b : PB K m) (c : PC K m)
    (h : extRhoB K m b = extRhoC K m c) :
    ∃! p : PA K m, extJB K m p = b ∧ extIotaC K m p = c := by
  classical
  have hcoeff : ∀ s : Fin m →₀ ℕ, rhoB K (MvPowerSeries.coeff s b.1) =
      rhoC K (MvPowerSeries.coeff s c.1) := fun s => by
    have h0 := congrArg (fun x : PD K m => MvPowerSeries.coeff s x.1) h
    show rhoB K (MvPowerSeries.coeff s b.1) = rhoC K (MvPowerSeries.coeff s c.1)
    have h1 : MvPowerSeries.coeff s (MvPowerSeries.map (rhoB K) b.1) =
        MvPowerSeries.coeff s (MvPowerSeries.map (rhoC K) c.1) := h0
    rwa [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at h1
  have hmem : ∀ s, MvPowerSeries.coeff s c.1 ∈ jetSupport K := fun s =>
    (mem_jetSupport_iff_jet_in_range K _).mpr ⟨MvPowerSeries.coeff s b.1, hcoeff s⟩
  have hres : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ))
      (fun s => (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K)) := by
    have hc : MvPowerSeries.IsRestrictedGauss (fun _ : Fin m => (1 : ℝ)) c.1 := c.2
    unfold MvPowerSeries.IsRestrictedGauss at hc ⊢
    exact hc.congr fun s => rfl
  refine ⟨⟨fun s => (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K), hres⟩, ⟨?_, ?_⟩, ?_⟩
  · refine Subtype.ext ?_
    show MvPowerSeries.map (jB K)
      (fun s => (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K)) = b.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    obtain ⟨a, ⟨hab, hac⟩, -⟩ := milnorRow_exact K (MvPowerSeries.coeff s b.1)
      (MvPowerSeries.coeff s c.1) (hcoeff s)
    have hpa : (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K) = a :=
      Subtype.ext (show MvPowerSeries.coeff s c.1 = (a : JetC K) from hac.symm)
    show jB K (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K) = _
    rw [hpa, hab]
  · refine Subtype.ext ?_
    show MvPowerSeries.map (iotaC K)
      (fun s => (⟨MvPowerSeries.coeff s c.1, hmem s⟩ : JetA K)) = c.1
    refine MvPowerSeries.ext fun s => ?_
    rw [MvPowerSeries.coeff_map]
    rfl
  · rintro q ⟨-, hqc⟩
    refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
    have h1 := congrArg (fun x : PC K m => MvPowerSeries.coeff s x.1) hqc
    have h2 : MvPowerSeries.coeff s (MvPowerSeries.map (iotaC K) q.1) =
        MvPowerSeries.coeff s c.1 := h1
    rw [MvPowerSeries.coeff_map] at h2
    show MvPowerSeries.coeff s q.1 = _
    exact Subtype.ext h2

/-- Pullback-norm identity for the extended square (constants 1). -/
theorem ext_max_norm_eq (p : PA K m) :
    max ‖extJB K m p‖ ‖extIotaC K m p‖ = ‖p‖ := by
  have h1 : ‖extIotaC K m p‖ = ‖p‖ := by
    rw [MvRestricted.norm_eq, MvRestricted.norm_eq]
    show MvPowerSeries.gaussNorm _ _ (MvPowerSeries.map (iotaC K) p.1) = _
    rw [MvPowerSeries.gaussNorm, MvPowerSeries.gaussNorm]
    refine iSup_congr fun s => ?_
    rw [MvPowerSeries.coeff_map, norm_iotaC]
  have h2 : ‖extJB K m p‖ ≤ ‖p‖ := norm_mapRestricted_le _ _ _ p
  rw [h1]
  exact max_eq_right h2

/-- `P_𝓐 → P_𝓑 ⊕ P_𝓒` is injective (left exactness of the extended row). -/
theorem ext_pair_injective :
    Function.Injective (fun p : PA K m => (extJB K m p, extIotaC K m p)) := by
  intro p q h
  have h2 : extIotaC K m p = extIotaC K m q := congrArg Prod.snd h
  have hinj : Function.Injective (iotaC K) := fun a b hab => Subtype.ext hab
  exact Subtype.ext (MvPowerSeries.map_injective hinj (congrArg Subtype.val h2))

/-! ### The graph data -/

variable (g : JetA K) (f : Fin m → JetA K)

/-- The graph relations `r_i = gT_i − f_i` in `P_𝓐` ([FJP] (4.6)). -/
noncomputable def rA : Fin m → PA K m := fun i =>
  polyToP (MvPolynomial.C g * MvPolynomial.X i - MvPolynomial.C (f i))

/-- The pushed relations at the vertices. -/
noncomputable def rB : Fin m → PB K m := fun i => extJB K m (rA K m g f i)
noncomputable def rC : Fin m → PC K m := fun i => extIotaC K m (rA K m g f i)
noncomputable def rD : Fin m → PD K m := fun i => extRhoC K m (rC K m g f i)

/-- Graph ideals `I_E = im(d₁) = (r₁, …, r_m)` ([FJP] (4.6)). -/
noncomputable def IA : Ideal (PA K m) := Ideal.span (Set.range (rA K m g f))
noncomputable def IB : Ideal (PB K m) := Ideal.span (Set.range (rB K m g f))
noncomputable def IC : Ideal (PC K m) := Ideal.span (Set.range (rC K m g f))
noncomputable def ID : Ideal (PD K m) := Ideal.span (Set.range (rD K m g f))

/-- The pushed data generate the unit ideal at each vertex ([FJP] §4 after (4.6): "Because
the rational datum is open, its defining ideal contains a power of ϖ. After mapping to each
of the k-algebras B, C, D, the tuple therefore generates the unit ideal"). -/
theorem span_pushed_B (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({jB K g} ∪ Set.range (fun i => jB K (f i))) = ⊤ := by
  have h := congrArg (Ideal.map (jB K)) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

theorem span_pushed_C (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({iotaC K g} ∪ Set.range (fun i => iotaC K (f i))) = ⊤ := by
  have h := congrArg (Ideal.map (iotaC K)) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

theorem span_pushed_D (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Ideal.span ({rhoC K (iotaC K g)} ∪
      Set.range (fun i => rhoC K (iotaC K (f i)))) = ⊤ := by
  have h := congrArg (Ideal.map ((rhoC K).comp (iotaC K))) hspan
  rw [Ideal.map_span, Ideal.map_top] at h
  rw [← h]
  congr 1
  rw [Set.image_union, Set.image_singleton, ← Set.range_comp]
  rfl

/-- Coefficientwise maps carry `polyToP`-images to `polyToP`-images. -/
theorem mapRestricted_polyToP {E E' : Type*} [NormedCommRing E] [IsUltrametricDist E]
    [NormOneClass E] [CompleteSpace E] [NormedCommRing E'] [IsUltrametricDist E']
    [NormOneClass E'] [CompleteSpace E']
    (φ : E →+* E') (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) (q : MvPolynomial (Fin m) E) :
    mapRestricted φ hφ (fun _ : Fin m => (1 : ℝ)) (polyToP q) =
      polyToP (MvPolynomial.map φ q) := by
  refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
  show MvPowerSeries.coeff s (MvPowerSeries.map φ ((polyToP (E := E) (m := m) q)).1) = _
  rw [MvPowerSeries.coeff_map, coeff_polyToP, coeff_polyToP, MvPolynomial.coeff_map]

theorem rB_eq (i : Fin m) : rB K m g f i =
    polyToP (MvPolynomial.C (jB K g) * MvPolynomial.X i -
      MvPolynomial.C (jB K (f i))) := by
  show mapRestricted (jB K) (norm_jB_le K) _ (polyToP _) = _
  rw [mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

theorem rC_eq (i : Fin m) : rC K m g f i =
    polyToP (MvPolynomial.C (iotaC K g) * MvPolynomial.X i -
      MvPolynomial.C (iotaC K (f i))) := by
  show mapRestricted (iotaC K) (fun a => le_of_eq (norm_iotaC K a)) _ (polyToP _) = _
  rw [mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

theorem rD_eq (i : Fin m) : rD K m g f i =
    polyToP (MvPolynomial.C (rhoC K (iotaC K g)) * MvPolynomial.X i -
      MvPolynomial.C (rhoC K (iotaC K (f i)))) := by
  show mapRestricted (rhoC K) (norm_rhoC_le K) _ (rC K m g f i) = _
  rw [rC_eq, mapRestricted_polyToP]
  congr 1
  rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

/-- The pushed generators are compatible across the square. -/
theorem extRhoB_rB (i : Fin m) : extRhoB K m (rB K m g f i) = rD K m g f i :=
  ext_square_commutes K m (rA K m g f i)

/-! ### Noetherianity of the vertex Tate extensions (re-sourced from the CDVF chain)

Where the Laurent template consumed the `K = F((t))`-specific transposition
`FiniteJet.isNoetherianRing_unitBall_gaussK`, the generic development sources every pod
from the K2 chain of `CDVFNoetherian.lean` — `Uniformizer.isNoetherianRing_unitBall_P` and
`Uniformizer.isStronglyNoetherian` at the base field — transported to the vertices by the
base-agnostic flattening/section lemmas of `FiniteJetNoetherianVertices.lean`. All
statements are layer-1: they take an explicit uniformizer `ϖ` and
`hK₀ : IsNoetherianRing (unitBall K)`, never a noetherian class on `K` (crosswalk ground
rule; the layer-2 `[IsDiscreteValuationRing 𝒪[K]]` chooser stays upstream in
`CDVFNoetherian.lean`). -/

/-- Restricted extensions of the Laurent ring are noetherian: `L⟨Z₁,…,Z_k⟩` is a quotient
of the noetherian `K⟨W,V,Z₁,…,Z_k⟩` ([FJP] Prop 2.1; the presentation `L = k⟨W,V⟩/(WV−1)`).
Generic port of `FiniteJet.isNoetherianRing_restricted_L`. -/
theorem isNoetherianRing_restricted_L (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (k : ℕ) :
    IsNoetherianRing (restrictedMvPowerSeriesSubring k (L K)) := by
  classical
  haveI := ϖ.isStronglyNoetherian hK₀
  -- flattening: `(K⟨W⟩)⟨V⟩ ≅ K⟨W,V⟩`
  obtain ⟨e1, he1⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 1
  -- flattening: `K⟨W,V⟩⟨Z₁,…,Z_k⟩ ≅ (K⟨W⟩)⟨Z₀,…,Z_k⟩`
  obtain ⟨e2, -⟩ := UnitDiscExample.exists_flatten'
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ)))
    (MvPowerSeries.Restricted K (fun _ : Fin 2 => (1 : ℝ)))
    e1.symm
    (fun x => by
      have h := he1 (e1.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) k
  -- flattening: `(K⟨W⟩)⟨Z₀,…,Z_k⟩ ≅ K⟨(k+2) variables⟩`
  obtain ⟨e3, -⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) (k + 1)
  haveI hK : IsNoetherianRing (restrictedMvPowerSeriesSubring (k + 2) K) :=
    IsStronglyNoetherian.isNoetherianRing_restricted (k + 2)
  refine isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring (k + 2) K) _
    (((UnitDiscExample.restrictedGaussEquiv (L K) k).toRingHom).comp
      ((mapRestrictedGauss k (evalHom (R := K)) (evalHom_norm_le (R := K))).comp
        (((UnitDiscExample.restrictedGaussEquiv K (k + 2)).symm.trans
          (e3.symm.trans e2.symm)).toRingHom))) ?_
  rw [RingHom.coe_comp, RingHom.coe_comp]
  exact (RingEquiv.surjective _).comp
    ((mapRestrictedGauss_surjective k (evalHom (R := K)) (evalHom_norm_le (R := K))
      (evalHom_exists_norm_le (R := K))).comp (RingEquiv.surjective _))

/-- `L = K⟨W,W⁻¹⟩` is strongly noetherian (layer-1 form). -/
theorem isStronglyNoetherian_L (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsStronglyNoetherian (L K) :=
  ⟨isNoetherianRing_restricted_L K ϖ hK₀⟩

/-- `𝓑 = K⟨W⟩[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1, layer-1 form). -/
theorem isStronglyNoetherian_JetB (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsStronglyNoetherian (JetB K) := by
  haveI := ϖ.isStronglyNoetherian hK₀
  exact ⟨fun k => isNoetherianRing_restricted_dualNumber (PowerSeries.Restricted K (1 : ℝ))
    (fun j => isNoetherianRing_restricted_univariate K j) k⟩

/-- `𝒞 = L⟨Q⟩` is strongly noetherian ([FJP] Prop 2.1, layer-1 form). -/
theorem isStronglyNoetherian_JetC (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsStronglyNoetherian (JetC K) := by
  haveI := isStronglyNoetherian_L K ϖ hK₀
  exact ⟨fun k => isNoetherianRing_restricted_univariate (L K) k⟩

/-- `𝓓 = L[Q]/(Q²)` is strongly noetherian ([FJP] Prop 2.1, layer-1 form). -/
theorem isStronglyNoetherian_JetD (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsStronglyNoetherian (JetD K) :=
  ⟨fun k => isNoetherianRing_restricted_dualNumber (L K)
    (isNoetherianRing_restricted_L K ϖ hK₀) k⟩

/-- The vertex Tate extensions are noetherian (transfer of strong noetherianity to the
Gauss form). -/
theorem isNoetherianRing_PB (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (PB K m) := by
  haveI := isStronglyNoetherian_JetB K ϖ hK₀
  haveI hsub := IsStronglyNoetherian.isNoetherianRing_restricted (A := JetB K) m
  exact isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring m (JetB K)) _
    (UnitDiscExample.restrictedGaussEquiv (JetB K) m).symm.toRingHom (RingEquiv.surjective _)

theorem isNoetherianRing_PC (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (PC K m) := by
  haveI := isStronglyNoetherian_JetC K ϖ hK₀
  haveI hsub := IsStronglyNoetherian.isNoetherianRing_restricted (A := JetC K) m
  exact isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring m (JetC K)) _
    (UnitDiscExample.restrictedGaussEquiv (JetC K) m).symm.toRingHom (RingEquiv.surjective _)

theorem isNoetherianRing_PD (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (PD K m) := by
  haveI := isStronglyNoetherian_JetD K ϖ hK₀
  haveI hsub := IsStronglyNoetherian.isNoetherianRing_restricted (A := JetD K) m
  exact isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring m (JetD K)) _
    (UnitDiscExample.restrictedGaussEquiv (JetD K) m).symm.toRingHom (RingEquiv.surjective _)

/-- The unit ball of `L⟨T₁,…,T_k⟩` is noetherian (the transfer chain at arity `k`, with the
base pod supplied by `Uniformizer.isNoetherianRing_unitBall_P`). Generic port of
`FiniteJet.isNoetherianRing_unitBall_restricted_L`. -/
theorem isNoetherianRing_unitBall_restricted_L (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) (k : ℕ) :
    IsNoetherianRing (unitBall
      (MvPowerSeries.Restricted (L K) (fun _ : Fin k => (1 : ℝ)))) := by
  obtain ⟨e1, he1⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) 1
  obtain ⟨e2, he2⟩ := UnitDiscExample.exists_flatten'
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ)))
    (MvPowerSeries.Restricted K (fun _ : Fin 2 => (1 : ℝ)))
    e1.symm
    (fun x => by
      have h := he1 (e1.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) k
  obtain ⟨e3, he3⟩ := UnitDiscExample.exists_flatten' K
    (MvPowerSeries.Restricted K (fun _ : Fin 1 => (1 : ℝ))) (RingEquiv.refl _)
    (fun _ => rfl) (k + 1)
  have h23 := isNoetherianRing_unitBall_of_isometry e3.symm
    (fun x => by
      have h := he3 (e3.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) (ϖ.isNoetherianRing_unitBall_P hK₀ (k + 2))
  have h3 := isNoetherianRing_unitBall_of_isometry e2.symm
    (fun x => by
      have h := he2 (e2.symm x)
      rw [RingEquiv.apply_symm_apply] at h
      exact h.symm) h23
  exact isNoetherianRing_unitBall_of_section
    (mapRestrictedGauss k (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (norm_mapRestrictedGauss_le k (evalHom (R := K)) (evalHom_norm_le (R := K)))
    (mapRestrictedGauss_exists_norm_le k (evalHom (R := K)) (evalHom_norm_le (R := K))
      (evalHom_exists_norm_le (R := K))) h3

/-- `L° = 𝒪_K⟨W,W⁻¹⟩` is noetherian ([FJP] Lemma 4.2 for the annulus vertex; the
`evalHom`-image of the unit ball of `K⟨W,V⟩ = P K 2`). -/
theorem isNoetherianRing_unitBall_L (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (unitBall (L K)) :=
  isNoetherianRing_unitBall_of_section (evalHom (R := K)) (evalHom_norm_le (R := K))
    (evalHom_exists_norm_le (R := K)) (ϖ.isNoetherianRing_unitBall_P hK₀ 2)

/-- `𝓓° = DualNumber L°` is noetherian ([FJP] Lemma 4.2: noetherian rings of
definition). -/
theorem isNoetherianRing_unitBall_JetD (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (unitBall (JetD K)) :=
  isNoetherianRing_unitBall_dualNumber (L K) (isNoetherianRing_unitBall_L K ϖ hK₀)

/-- The vertex Tate-extension unit balls are noetherian. -/
theorem isNoetherianRing_unitBall_PB (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (unitBall (PB K m)) :=
  isNoetherianRing_unitBall_restricted_dualNumber
    (PowerSeries.Restricted K (1 : ℝ)) m
    (isNoetherianRing_unitBall_restricted_univariate K m
      (ϖ.isNoetherianRing_unitBall_P hK₀ (m + 1)))

theorem isNoetherianRing_unitBall_PC (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (unitBall (PC K m)) :=
  isNoetherianRing_unitBall_restricted_univariate (L K) m
    (isNoetherianRing_unitBall_restricted_L K ϖ hK₀ (m + 1))

theorem isNoetherianRing_unitBall_PD (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (unitBall K)) : IsNoetherianRing (unitBall (PD K m)) :=
  isNoetherianRing_unitBall_restricted_dualNumber (L K) m
    (isNoetherianRing_unitBall_restricted_L K ϖ hK₀ m)

/-! ### Lemma 4.3 — controlled graph-ideal pullback

[FJP] Lemma 4.3 (verbatim): "The canonical algebraic map `I_R → I_B ×_{I_D} I_C` is a
bounded bijection with bounded inverse for the subspace norms. Consequently `I_R` is closed
in `P_R`, the map in (4.9) is a strict isomorphism of Banach spaces, and the difference
sequence `0 → I_R → I_B ⊕ I_C → I_D → 0` is strict exact."  Constants: (4.11)–(4.16). -/

/-- Right strict surjectivity of the ideal row ([FJP] (4.11)). -/
theorem ideal_row_surjective (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧ ∀ y ∈ ID K m g f,
      ∃ xc ∈ IC K m g f, extRhoC K m xc = y ∧ ‖xc‖ ≤ Cs * ‖y‖ := by
  classical
  haveI hPD : IsNoetherianRing (PD K m) := isNoetherianRing_PD K m ϖ hK₀
  have hE₀P : IsNoetherianRing (unitBall (PD K m)) := isNoetherianRing_unitBall_PD K m ϖ hK₀
  obtain ⟨h, hh1, hlift⟩ := exists_d1_lift (E := JetD K) (piD ϖ) (isUnit_piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos) (norm_piD_mul ϖ) hE₀P (rD K m g f)
  set Cr : ℝ := 1 + ∑ i, ‖rC K m g f i‖ with hCr
  have hCr1 : 1 ≤ Cr := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  refine ⟨h * Cr, ?_, fun y hy => ?_⟩
  · calc (1 : ℝ) ≤ h := hh1
      _ = h * 1 := (mul_one h).symm
      _ ≤ h * Cr := mul_le_mul_of_nonneg_left hCr1 (zero_le_one.trans hh1)
  · obtain ⟨u, hu, hun⟩ := hlift y hy
    have hsec : ∀ i, ∃ c : PC K m, extRhoC K m c = u i ∧ ‖c‖ = ‖u i‖ := fun i =>
      extRhoC_strict_surjective K m (u i)
    choose cc hcc hccn using hsec
    refine ⟨d1 (rC K m g f) cc, ?_, ?_, ?_⟩
    · show d1 (rC K m g f) cc ∈ Ideal.span (Set.range (rC K m g f))
      unfold d1
      exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    · rw [show extRhoC K m (d1 (rC K m g f) cc) =
        d1 (fun i => extRhoC K m (rC K m g f i)) (fun i => extRhoC K m (cc i)) from
          d1_map (extRhoC K m) _ cc,
        show (fun i => extRhoC K m (rC K m g f i)) = rD K m g f from rfl,
        show (fun i => extRhoC K m (cc i)) = u from funext hcc]
      exact hu
    · have hterm : ∀ i : Fin m, ‖cc i * rC K m g f i‖ ≤ ‖u‖ * Cr := fun i => by
        calc ‖cc i * rC K m g f i‖ ≤ ‖cc i‖ * ‖rC K m g f i‖ := norm_mul_le _ _
          _ = ‖u i‖ * ‖rC K m g f i‖ := by rw [hccn i]
          _ ≤ ‖u‖ * Cr := by
              refine mul_le_mul (norm_le_pi_norm u i) ?_ (norm_nonneg _) (norm_nonneg u)
              rw [hCr]
              refine le_add_of_nonneg_of_le zero_le_one ?_
              exact Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ i)
      have hpartial : ∀ s : Finset (Fin m),
          ‖∑ i ∈ s, cc i * rC K m g f i‖ ≤ ‖u‖ * Cr := by
        intro s
        induction s using Finset.induction_on with
        | empty =>
          rw [Finset.sum_empty, norm_zero]
          exact mul_nonneg (norm_nonneg u) (zero_le_one.trans hCr1)
        | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hterm a) ih)
      show ‖d1 (rC K m g f) cc‖ ≤ h * Cr * ‖y‖
      unfold d1
      refine (hpartial Finset.univ).trans ?_
      calc ‖u‖ * Cr ≤ h * ‖y‖ * Cr :=
            mul_le_mul_of_nonneg_right hun (zero_le_one.trans hCr1)
        _ = h * Cr * ‖y‖ := by ring

/-- The controlled pullback ([FJP] (4.12)–(4.16)): a matching pair of graph-ideal elements
comes from an element of `I_𝓐` with a uniformly bounded representative. This is where the
`d₂`-syzygy correction (`exists_d2_lift` at the 𝓓-vertex) enters. -/
theorem ideal_pullback_controlled (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    ∃ Cs : ℝ, 1 ≤ Cs ∧
      ∀ xb ∈ IB K m g f, ∀ xc ∈ IC K m g f,
        extRhoB K m xb = extRhoC K m xc →
        ∃ xa ∈ IA K m g f,
          extJB K m xa = xb ∧ extIotaC K m xa = xc ∧ ‖xa‖ ≤ Cs * max ‖xb‖ ‖xc‖ := by
  classical
  haveI hPB := isNoetherianRing_PB K m ϖ hK₀
  haveI hPC := isNoetherianRing_PC K m ϖ hK₀
  haveI hPD := isNoetherianRing_PD K m ϖ hK₀
  obtain ⟨hB, hB1, hliftB⟩ := exists_d1_lift (E := JetB K) (piB ϖ) (isUnit_piB ϖ)
    (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piB]; exact ϖ.norm_val_pos)
    (norm_piB_mul ϖ) (isNoetherianRing_unitBall_PB K m ϖ hK₀) (rB K m g f)
  obtain ⟨hC, hC1, hliftC⟩ := exists_d1_lift (E := JetC K) (piC ϖ) (isUnit_piC ϖ)
    (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piC]; exact ϖ.norm_val_pos)
    (norm_piC_mul ϖ) (isNoetherianRing_unitBall_PC K m ϖ hK₀) (rC K m g f)
  obtain ⟨z, hz1, hliftD⟩ := exists_d2_lift (E := JetD K)
    (isNoetherianRing_unitBall_JetD K ϖ hK₀) (piD ϖ) (isUnit_piD ϖ)
    (by rw [norm_piD]; exact ϖ.norm_val_lt_one)
    (by rw [norm_piD]; exact ϖ.norm_val_pos)
    (norm_piD_mul ϖ) (rhoC K (iotaC K g)) (fun i => rhoC K (iotaC K (f i)))
    (span_pushed_D K m g f hspan) (rD K m g f) (rD_eq K m g f)
  set CrC : ℝ := 1 + ∑ i, ‖rC K m g f i‖ with hCrC
  set CrA : ℝ := 1 + ∑ i, ‖rA K m g f i‖ with hCrA
  have hCrC1 : 1 ≤ CrC := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hCrA1 : 1 ≤ CrA := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hB0 : 0 ≤ hB := zero_le_one.trans hB1
  have hC0 : 0 ≤ hC := zero_le_one.trans hC1
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  set Bs : ℝ := hB + hC + z * (hB + hC) * CrC with hBs
  have hBs0 : 0 ≤ Bs := add_nonneg (add_nonneg hB0 hC0)
    (mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) (zero_le_one.trans hCrC1))
  have hprod0 : 0 ≤ z * (hB + hC) * CrC :=
    mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) (zero_le_one.trans hCrC1)
  have hBsB : hB ≤ Bs := by
    rw [hBs]
    linarith
  have hBsC : hC ≤ Bs := by
    rw [hBs]
    linarith
  have hBszC : z * (hB + hC) * CrC ≤ Bs := by
    rw [hBs]
    linarith
  refine ⟨1 + Bs * CrA, le_add_of_nonneg_right (mul_nonneg hBs0
    (zero_le_one.trans hCrA1)), fun xb hxb xc hxc hcompat => ?_⟩
  set M : ℝ := max ‖xb‖ ‖xc‖ with hM
  have hM0 : (0 : ℝ) ≤ M := le_max_of_le_left (norm_nonneg xb)
  obtain ⟨u, hu, hun⟩ := hliftB xb hxb
  obtain ⟨v, hv, hvn⟩ := hliftC xc hxc
  have hun' : ‖u‖ ≤ hB * M :=
    hun.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hB0)
  have hvn' : ‖v‖ ≤ hC * M :=
    hvn.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) hC0)
  set w : Fin m → PD K m := fun i => extRhoB K m (u i) - extRhoC K m (v i) with hw
  have hd1sub : ∀ {S : Type _} [inst : CommRing S] (r a b : Fin m → S),
      d1 r (fun i => a i - b i) = d1 r a - d1 r b := by
    intro S _ r a b
    unfold d1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hwd1 : d1 (rD K m g f) w = 0 := by
    have h1 : d1 (rD K m g f) (fun i => extRhoB K m (u i)) = extRhoB K m xb := by
      rw [← hu, d1_map (extRhoB K m)]
      congr 1
      exact (funext fun i => (extRhoB_rB K m g f i)).symm
    have h2 : d1 (rD K m g f) (fun i => extRhoC K m (v i)) = extRhoC K m xc := by
      rw [← hv, d1_map (extRhoC K m)]
      rfl
    rw [hw, hd1sub, h1, h2, hcompat, sub_self]
  obtain ⟨sD, hsD, hsDn⟩ := hliftD w hwd1
  have hwn : ‖w‖ ≤ (hB + hC) * M := by
    refine pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg hB0 hC0) hM0) |>.mpr fun i => ?_
    show ‖extRhoB K m (u i) - extRhoC K m (v i)‖ ≤ _
    have hsub : ‖extRhoB K m (u i) - extRhoC K m (v i)‖ ≤
        max ‖extRhoB K m (u i)‖ ‖extRhoC K m (v i)‖ := by
      have h := IsUltrametricDist.norm_add_le_max (extRhoB K m (u i))
        (-(extRhoC K m (v i)))
      rwa [← sub_eq_add_neg, norm_neg] at h
    refine hsub.trans (max_le ?_ ?_)
    · calc ‖extRhoB K m (u i)‖ ≤ ‖u i‖ := norm_mapRestricted_le _ _ _ _
        _ ≤ ‖u‖ := norm_le_pi_norm u i
        _ ≤ hB * M := hun'
        _ ≤ (hB + hC) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    · calc ‖extRhoC K m (v i)‖ ≤ ‖v i‖ := norm_mapRestricted_le _ _ _ _
        _ ≤ ‖v‖ := norm_le_pi_norm v i
        _ ≤ hC * M := hvn'
        _ ≤ (hB + hC) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
  have hzM0 : 0 ≤ z * (hB + hC) * M :=
    mul_nonneg (mul_nonneg hz0 (add_nonneg hB0 hC0)) hM0
  have hsDn' : ‖sD‖ ≤ z * (hB + hC) * M := by
    refine hsDn.trans ?_
    calc z * ‖w‖ ≤ z * ((hB + hC) * M) := mul_le_mul_of_nonneg_left hwn hz0
      _ = z * (hB + hC) * M := by ring
  have hsec : ∀ p : Pairs m, ∃ c : PC K m, extRhoC K m c = sD p ∧ ‖c‖ = ‖sD p‖ := fun p =>
    extRhoC_strict_surjective K m (sD p)
  choose sC hsC hsCn using hsec
  have hsCn' : ∀ p, ‖sC p‖ ≤ z * (hB + hC) * M := fun p => by
    rw [hsCn p]
    exact (norm_le_pi_norm sD p).trans hsDn'
  set v' : Fin m → PC K m := fun i => v i + d2 (rC K m g f) sC i with hv'def
  have hd1add : ∀ {S : Type _} [inst : CommRing S] (r a b : Fin m → S),
      d1 r (fun i => a i + b i) = d1 r a + d1 r b := by
    intro S _ r a b
    unfold d1
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hv'd1 : d1 (rC K m g f) v' = xc := by
    rw [hv'def, hd1add, hv,
      show d1 (rC K m g f) (fun i => d2 (rC K m g f) sC i) = 0 from d1_d2 _ sC, add_zero]
  have hv'compat : ∀ i, extRhoB K m (u i) = extRhoC K m (v' i) := fun i => by
    rw [hv'def]
    show _ = extRhoC K m (v i + d2 (rC K m g f) sC i)
    rw [map_add, d2_map (extRhoC K m)]
    have heq : d2 (fun j => extRhoC K m (rC K m g f j)) (fun p => extRhoC K m (sC p)) i =
        d2 (rD K m g f) sD i := by
      congr 1
      exact funext hsC
    rw [heq, congrFun hsD i, hw]
    show extRhoB K m (u i) =
      extRhoC K m (v i) + (extRhoB K m (u i) - extRhoC K m (v i))
    ring
  have hpull := fun i => (ext_milnorRow_exact K m (u i) (v' i) (hv'compat i)).exists
  choose a ha using hpull
  refine ⟨d1 (rA K m g f) a, ?_, ?_, ?_, ?_⟩
  · show d1 (rA K m g f) a ∈ Ideal.span (Set.range (rA K m g f))
    unfold d1
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [show extJB K m (d1 (rA K m g f) a) =
      d1 (fun i => extJB K m (rA K m g f i)) (fun i => extJB K m (a i)) from
        d1_map (extJB K m) _ a,
      show (fun i => extJB K m (rA K m g f i)) = rB K m g f from rfl,
      show (fun i => extJB K m (a i)) = u from funext fun i => (ha i).1]
    exact hu
  · rw [show extIotaC K m (d1 (rA K m g f) a) =
      d1 (fun i => extIotaC K m (rA K m g f i)) (fun i => extIotaC K m (a i)) from
        d1_map (extIotaC K m) _ a,
      show (fun i => extIotaC K m (rA K m g f i)) = rC K m g f from rfl,
      show (fun i => extIotaC K m (a i)) = v' from funext fun i => (ha i).2]
    exact hv'd1
  · have hsum : ∀ (C0 : ℝ), 0 ≤ C0 → ∀ (T : Finset (Fin m)) (G : Fin m → PC K m),
        (∀ j ∈ T, ‖G j‖ ≤ C0) → ‖∑ j ∈ T, G j‖ ≤ C0 := by
      intro C0 hC00 T G hG
      induction T using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, norm_zero]
        exact hC00
      | insert b T hb ih =>
        rw [Finset.sum_insert hb]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans
          (max_le (hG b (Finset.mem_insert_self _ _))
            (ih fun j hj => hG j (Finset.mem_insert_of_mem hj)))
    have hd2bound : ∀ i, ‖d2 (rC K m g f) sC i‖ ≤ z * (hB + hC) * M * CrC := fun i => by
      have hterm : ∀ (p : Pairs m) (j : Fin m), ‖sC p * rC K m g f j‖ ≤
          z * (hB + hC) * M * CrC := fun p j => by
        calc ‖sC p * rC K m g f j‖ ≤ ‖sC p‖ * ‖rC K m g f j‖ := norm_mul_le _ _
          _ ≤ (z * (hB + hC) * M) * CrC := by
              refine mul_le_mul (hsCn' p) ?_ (norm_nonneg _) hzM0
              rw [hCrC]
              exact le_add_of_nonneg_of_le zero_le_one
                (Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ j))
      have hCrCM0 : 0 ≤ z * (hB + hC) * M * CrC :=
        mul_nonneg hzM0 (zero_le_one.trans hCrC1)
      show ‖d2 (rC K m g f) sC i‖ ≤ _
      unfold d2
      have h1 : ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * rC K m g f j else 0)‖ ≤
          z * (hB + hC) * M * CrC := by
        refine hsum _ hCrCM0 Finset.univ _ fun j _ => ?_
        by_cases hji : j < i
        · rw [dif_pos hji]
          exact hterm _ _
        · rw [dif_neg hji, norm_zero]
          exact hCrCM0
      have h2 : ‖(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * rC K m g f j else 0)‖ ≤
          z * (hB + hC) * M * CrC := by
        refine hsum _ hCrCM0 Finset.univ _ fun j _ => ?_
        by_cases hji : i < j
        · rw [dif_pos hji]
          exact hterm _ _
        · rw [dif_neg hji, norm_zero]
          exact hCrCM0
      have hd : ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * rC K m g f j else 0) -
          (∑ j, if h : i < j then sC ⟨(i, j), h⟩ * rC K m g f j else 0)‖ ≤
          max ‖(∑ j, if h : j < i then sC ⟨(j, i), h⟩ * rC K m g f j else 0)‖
            ‖(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * rC K m g f j else 0)‖ := by
        have h := IsUltrametricDist.norm_add_le_max
          (∑ j, if h : j < i then sC ⟨(j, i), h⟩ * rC K m g f j else 0)
          (-(∑ j, if h : i < j then sC ⟨(i, j), h⟩ * rC K m g f j else 0))
        rwa [← sub_eq_add_neg, norm_neg] at h
      exact hd.trans (max_le h1 h2)
    have hv'n : ‖v'‖ ≤ Bs * M := by
      refine pi_norm_le_iff_of_nonneg (mul_nonneg hBs0 hM0) |>.mpr fun i => ?_
      show ‖v i + d2 (rC K m g f) sC i‖ ≤ _
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · calc ‖v i‖ ≤ ‖v‖ := norm_le_pi_norm v i
          _ ≤ hC * M := hvn'
          _ ≤ Bs * M := mul_le_mul_of_nonneg_right hBsC hM0
      · refine (hd2bound i).trans ?_
        calc z * (hB + hC) * M * CrC = (z * (hB + hC) * CrC) * M := by ring
          _ ≤ Bs * M := mul_le_mul_of_nonneg_right hBszC hM0
    have han : ‖a‖ ≤ Bs * M := by
      refine pi_norm_le_iff_of_nonneg (mul_nonneg hBs0 hM0) |>.mpr fun i => ?_
      have hmax := ext_max_norm_eq K m (a i)
      rw [(ha i).1, (ha i).2] at hmax
      rw [← hmax]
      refine max_le ?_ ?_
      · exact (norm_le_pi_norm u i).trans (hun'.trans
          (mul_le_mul_of_nonneg_right hBsB hM0))
      · exact (norm_le_pi_norm v' i).trans hv'n
    have hfinal : ∀ (T : Finset (Fin m)), ‖∑ j ∈ T, a j * rA K m g f j‖ ≤ Bs * M * CrA := by
      have hBMC0 : 0 ≤ Bs * M * CrA :=
        mul_nonneg (mul_nonneg hBs0 hM0) (zero_le_one.trans hCrA1)
      intro T
      induction T using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty, norm_zero]
        exact hBMC0
      | insert b T hb ih =>
        rw [Finset.sum_insert hb]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
        calc ‖a b * rA K m g f b‖ ≤ ‖a b‖ * ‖rA K m g f b‖ := norm_mul_le _ _
          _ ≤ (Bs * M) * CrA := by
              refine mul_le_mul ((norm_le_pi_norm a b).trans han) ?_ (norm_nonneg _)
                (mul_nonneg hBs0 hM0)
              rw [hCrA]
              exact le_add_of_nonneg_of_le zero_le_one
                (Finset.single_le_sum (fun k _ => norm_nonneg _) (Finset.mem_univ b))
    show ‖d1 (rA K m g f) a‖ ≤ (1 + Bs * CrA) * M
    unfold d1
    refine (hfinal Finset.univ).trans ?_
    calc Bs * M * CrA = Bs * CrA * M := by ring
      _ ≤ (1 + Bs * CrA) * M := by
          refine mul_le_mul_of_nonneg_right ?_ hM0
          linarith [mul_nonneg hBs0 (zero_le_one.trans hCrA1)]

/-- `I_𝓐` is closed in `P_𝓐` ([FJP] Lemma 4.3: "Consequently `I_R` is closed in `P_R`"). -/
theorem isClosed_IA (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    IsClosed ((IA K m g f : Set (PA K m))) := by
  classical
  haveI hPB := isNoetherianRing_PB K m ϖ hK₀
  haveI hPC := isNoetherianRing_PC K m ϖ hK₀
  have hIBclosed : IsClosed ((IB K m g f : Set (PB K m))) :=
    isClosed_graphIdeal (piB ϖ) (isUnit_piB ϖ)
      (by rw [norm_piB]; exact ϖ.norm_val_lt_one)
      (by rw [norm_piB]; exact ϖ.norm_val_pos)
      (norm_piB_mul ϖ) (isNoetherianRing_unitBall_PB K m ϖ hK₀) (rB K m g f)
  have hICclosed : IsClosed ((IC K m g f : Set (PC K m))) :=
    isClosed_graphIdeal (piC ϖ) (isUnit_piC ϖ)
      (by rw [norm_piC]; exact ϖ.norm_val_lt_one)
      (by rw [norm_piC]; exact ϖ.norm_val_pos)
      (norm_piC_mul ϖ) (isNoetherianRing_unitBall_PC K m ϖ hK₀) (rC K m g f)
  obtain ⟨Cs, hCs1, hpull⟩ := ideal_pullback_controlled K m g f ϖ hK₀ hspan
  refine isClosed_of_closure_subset fun x hx => ?_
  have hcontB : Continuous (extJB K m) := by
    have hlip : LipschitzWith 1 (extJB K m) := LipschitzWith.of_dist_le_mul fun a b => by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_mapRestricted_le _ _ _ _
    exact hlip.continuous
  have hcontC : Continuous (extIotaC K m) := by
    have hlip : LipschitzWith 1 (extIotaC K m) := LipschitzWith.of_dist_le_mul fun a b => by
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
      exact norm_mapRestricted_le _ _ _ _
    exact hlip.continuous
  have hsubB : extJB K m '' (IA K m g f : Set (PA K m)) ⊆ (IB K m g f : Set (PB K m)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmap : Ideal.map (extJB K m) (IA K m g f) ≤ IB K m g f := by
      rw [show IA K m g f = Ideal.span (Set.range (rA K m g f)) from rfl, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, rfl⟩
    exact hmap (Ideal.mem_map_of_mem _ hy)
  have hsubC : extIotaC K m '' (IA K m g f : Set (PA K m)) ⊆ (IC K m g f : Set (PC K m)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmap : Ideal.map (extIotaC K m) (IA K m g f) ≤ IC K m g f := by
      rw [show IA K m g f = Ideal.span (Set.range (rA K m g f)) from rfl, Ideal.map_span]
      refine Ideal.span_le.mpr ?_
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact Ideal.subset_span ⟨i, rfl⟩
    exact hmap (Ideal.mem_map_of_mem _ hy)
  have hxB : extJB K m x ∈ (IB K m g f : Set (PB K m)) := by
    have h1 : extJB K m x ∈ closure (extJB K m '' (IA K m g f : Set (PA K m))) :=
      image_closure_subset_closure_image hcontB ⟨x, hx, rfl⟩
    exact hIBclosed.closure_eq ▸ closure_mono hsubB h1
  have hxC : extIotaC K m x ∈ (IC K m g f : Set (PC K m)) := by
    have h1 : extIotaC K m x ∈ closure (extIotaC K m '' (IA K m g f : Set (PA K m))) :=
      image_closure_subset_closure_image hcontC ⟨x, hx, rfl⟩
    exact hICclosed.closure_eq ▸ closure_mono hsubC h1
  obtain ⟨xa, hxa, hJ, hI, -⟩ := hpull (extJB K m x) hxB (extIotaC K m x) hxC
    (ext_square_commutes K m x)
  have heq : xa = x := ext_pair_injective K m (Prod.ext hJ hI)
  rw [← heq]
  exact hxa

/-! ### Proposition 4.5 — strict Milnor localization

[FJP] Prop 4.5 (verbatim): "Let (4.5) be a strict Milnor square and assume B, C, D are
affinoid k-algebras. For every open rational datum α in R, the canonical square of completed
rational localizations is again a strict Milnor square. Equivalently,
`0 → R_α → B_α ⊕ C_α → D_α → 0` is strict exact, `R_α ≅ B_α ×_{D_α} C_α` is a strict
isomorphism, and `C_α → D_α` is a strict surjection."

Since all four graph ideals are closed ([FJP] (4.21): "the completed graph quotient is
already the Banach quotient `E_α = P_E/I_E`"), we take the plain ring quotients with their
quotient topologies. The strict quotient lemma ([FJP] Lemma 4.4) is consumed inside the
proofs of the statements below; its normed-group bookkeeping is recorded in the campaign
decomposition. -/

/-- `𝓐_α = P_𝓐 ⧸ I_𝓐` and companions, as topological rings with the quotient topology. -/
abbrev locA : Type _ := PA K m ⧸ IA K m g f
abbrev locB : Type _ := PB K m ⧸ IB K m g f
abbrev locC : Type _ := PC K m ⧸ IC K m g f
abbrev locD : Type _ := PD K m ⧸ ID K m g f

/-- Graph ideals push forward along the square's maps. -/
theorem extJB_mem_IB {y : PA K m} (hy : y ∈ IA K m g f) : extJB K m y ∈ IB K m g f := by
  have hmap : Ideal.map (extJB K m) (IA K m g f) ≤ IB K m g f := by
    rw [show IA K m g f = Ideal.span (Set.range (rA K m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

theorem extIotaC_mem_IC {y : PA K m} (hy : y ∈ IA K m g f) :
    extIotaC K m y ∈ IC K m g f := by
  have hmap : Ideal.map (extIotaC K m) (IA K m g f) ≤ IC K m g f := by
    rw [show IA K m g f = Ideal.span (Set.range (rA K m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

theorem extRhoB_mem_ID {y : PB K m} (hy : y ∈ IB K m g f) :
    extRhoB K m y ∈ ID K m g f := by
  have hmap : Ideal.map (extRhoB K m) (IB K m g f) ≤ ID K m g f := by
    rw [show IB K m g f = Ideal.span (Set.range (rB K m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, (extRhoB_rB K m g f i).symm⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

theorem extRhoC_mem_ID {y : PC K m} (hy : y ∈ IC K m g f) :
    extRhoC K m y ∈ ID K m g f := by
  have hmap : Ideal.map (extRhoC K m) (IC K m g f) ≤ ID K m g f := by
    rw [show IC K m g f = Ideal.span (Set.range (rC K m g f)) from rfl, Ideal.map_span]
    refine Ideal.span_le.mpr ?_
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact Ideal.subset_span ⟨i, rfl⟩
  exact hmap (Ideal.mem_map_of_mem _ hy)

/-- The induced maps of the localized square ([FJP] (4.19)). -/
noncomputable def locJB : locA K m g f →+* locB K m g f :=
  Ideal.Quotient.lift (IA K m g f)
    ((Ideal.Quotient.mk (IB K m g f)).comp (extJB K m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact extJB_mem_IB K m g f ha)

noncomputable def locIotaC : locA K m g f →+* locC K m g f :=
  Ideal.Quotient.lift (IA K m g f)
    ((Ideal.Quotient.mk (IC K m g f)).comp (extIotaC K m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact extIotaC_mem_IC K m g f ha)

noncomputable def locRhoB : locB K m g f →+* locD K m g f :=
  Ideal.Quotient.lift (IB K m g f)
    ((Ideal.Quotient.mk (ID K m g f)).comp (extRhoB K m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact extRhoB_mem_ID K m g f ha)

noncomputable def locRhoC : locC K m g f →+* locD K m g f :=
  Ideal.Quotient.lift (IC K m g f)
    ((Ideal.Quotient.mk (ID K m g f)).comp (extRhoC K m)) (fun a ha => by
      rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact extRhoC_mem_ID K m g f ha)

theorem locJB_mk (p : PA K m) :
    locJB K m g f (Ideal.Quotient.mk (IA K m g f) p) =
      Ideal.Quotient.mk (IB K m g f) (extJB K m p) := rfl

theorem locIotaC_mk (p : PA K m) :
    locIotaC K m g f (Ideal.Quotient.mk (IA K m g f) p) =
      Ideal.Quotient.mk (IC K m g f) (extIotaC K m p) := rfl

theorem locRhoB_mk (p : PB K m) :
    locRhoB K m g f (Ideal.Quotient.mk (IB K m g f) p) =
      Ideal.Quotient.mk (ID K m g f) (extRhoB K m p) := rfl

theorem locRhoC_mk (p : PC K m) :
    locRhoC K m g f (Ideal.Quotient.mk (IC K m g f) p) =
      Ideal.Quotient.mk (ID K m g f) (extRhoC K m p) := rfl

theorem loc_square_commutes (x : locA K m g f) :
    locRhoB K m g f (locJB K m g f x) = locRhoC K m g f (locIotaC K m g f x) := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [locJB_mk, locIotaC_mk, locRhoB_mk, locRhoC_mk, ext_square_commutes]

/-- Algebraic exactness of the localized row: the pullback description of `𝓐_α`
([FJP] (4.20)). -/
theorem loc_pair_injective (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Function.Injective
      (fun x : locA K m g f => (locJB K m g f x, locIotaC K m g f x)) := by
  obtain ⟨Cs, hCs1, hpull⟩ := ideal_pullback_controlled K m g f ϖ hK₀ hspan
  have hker : ∀ y : locA K m g f, locJB K m g f y = 0 → locIotaC K m g f y = 0 → y = 0 := by
    intro y hyB hyC
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [locJB_mk, Ideal.Quotient.eq_zero_iff_mem] at hyB
    rw [locIotaC_mk, Ideal.Quotient.eq_zero_iff_mem] at hyC
    obtain ⟨qa, hqa, hJ, hI, -⟩ := hpull (extJB K m q) hyB (extIotaC K m q) hyC
      (ext_square_commutes K m q)
    have heq : qa = q := ext_pair_injective K m (Prod.ext hJ hI)
    rw [Ideal.Quotient.eq_zero_iff_mem, ← heq]
    exact hqa
  intro x y hxy
  have hxy' : (locJB K m g f x, locIotaC K m g f x) =
      (locJB K m g f y, locIotaC K m g f y) := hxy
  rw [Prod.mk.injEq] at hxy'
  have hpair := hxy'
  have h1 : locJB K m g f (x - y) = 0 := by
    rw [map_sub, hpair.1, sub_self]
  have h2 : locIotaC K m g f (x - y) = 0 := by
    rw [map_sub, hpair.2, sub_self]
  have := hker (x - y) h1 h2
  rwa [sub_eq_zero] at this

/-- Algebraic exactness of the localized row: the pullback description of `𝓐_α`
([FJP] (4.20)). -/
theorem loc_row_exact (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤)
    (b : locB K m g f) (c : locC K m g f)
    (h : locRhoB K m g f b = locRhoC K m g f c) :
    ∃! x : locA K m g f, locJB K m g f x = b ∧ locIotaC K m g f x = c := by
  obtain ⟨pb, rfl⟩ := Ideal.Quotient.mk_surjective b
  obtain ⟨pc, rfl⟩ := Ideal.Quotient.mk_surjective c
  rw [locRhoB_mk, locRhoC_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h
  obtain ⟨Cs, hCs1, hrow⟩ := ideal_row_surjective K m g f ϖ hK₀ hspan
  obtain ⟨xc, hxc, hxcρ, -⟩ := hrow (extRhoB K m pb - extRhoC K m pc) h
  set pc' : PC K m := pc + xc with hpc'
  have hcompat : extRhoB K m pb = extRhoC K m pc' := by
    rw [hpc', map_add, hxcρ]
    ring
  obtain ⟨p, hpb, hpc⟩ := (ext_milnorRow_exact K m pb pc' hcompat).exists
  refine ⟨Ideal.Quotient.mk _ p, ⟨?_, ?_⟩, ?_⟩
  · rw [locJB_mk, hpb]
  · rw [locIotaC_mk, hpc, hpc', Ideal.Quotient.mk_eq_mk_iff_sub_mem, add_sub_cancel_left]
    exact hxc
  · rintro x' ⟨hx'B, hx'C⟩
    refine loc_pair_injective K m g f ϖ hK₀ hspan ?_
    rw [Prod.ext_iff]
    constructor
    · show locJB K m g f x' = locJB K m g f (Ideal.Quotient.mk _ p)
      rw [hx'B, locJB_mk, hpb]
    · show locIotaC K m g f x' = locIotaC K m g f (Ideal.Quotient.mk _ p)
      rw [hx'C, locIotaC_mk, hpc, hpc', Ideal.Quotient.mk_eq_mk_iff_sub_mem,
        sub_add_cancel_left]
      exact (IC K m g f).neg_mem hxc

/-- The quotient projections are 1-Lipschitz for the quotient seminorms. -/
theorem locJB_lipschitz : LipschitzWith 1 (locJB K m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locJB_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt (Ideal.Quotient.mk (IA K m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (IB K m g f) (extJB K m p) =
        Ideal.Quotient.mk (IB K m g f) (extJB K m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact extJB_mem_IB K m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (IB K m g f) (extJB K m q)‖
        ≤ ‖extJB K m q‖ := Ideal.Quotient.norm_mk_le _ (extJB K m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (IA K m g f) p‖ + ε := hqn.le

theorem locIotaC_lipschitz : LipschitzWith 1 (locIotaC K m g f) :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (a - b)
    rw [← hp, locIotaC_mk]
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨q, hq, hqn⟩ := Ideal.Quotient.norm_mk_lt (Ideal.Quotient.mk (IA K m g f) p) hε
    have hmkeq : Ideal.Quotient.mk (IC K m g f) (extIotaC K m p) =
        Ideal.Quotient.mk (IC K m g f) (extIotaC K m q) := by
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
      exact extIotaC_mem_IC K m g f (by
        have h := hq.symm
        rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at h)
    rw [hmkeq]
    calc ‖Ideal.Quotient.mk (IC K m g f) (extIotaC K m q)‖
        ≤ ‖extIotaC K m q‖ := Ideal.Quotient.norm_mk_le _ (extIotaC K m q)
      _ ≤ ‖q‖ := norm_mapRestricted_le _ _ _ _
      _ ≤ ‖Ideal.Quotient.mk (IA K m g f) p‖ + ε := hqn.le

/-- The quantitative Lemma 4.4 estimate: the quotient pullback norm is controlled by the
component norms. -/
theorem loc_norm_le (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) (x : locA K m g f) :
    ‖x‖ ≤ (1 + Classical.choose (ideal_row_surjective K m g f ϖ hK₀ hspan)) *
      max ‖locJB K m g f x‖ ‖locIotaC K m g f x‖ := by
  classical
  obtain ⟨hC₁1, hrow⟩ := Classical.choose_spec (ideal_row_surjective K m g f ϖ hK₀ hspan)
  set C₁ := Classical.choose (ideal_row_surjective K m g f ϖ hK₀ hspan) with hC₁def
  have hC₁0 : (0 : ℝ) ≤ C₁ := zero_le_one.trans hC₁1
  set M : ℝ := max ‖locJB K m g f x‖ ‖locIotaC K m g f x‖ with hMdef
  have hM0 : 0 ≤ M := le_max_of_le_left (norm_nonneg _)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ : ℝ := ε / (2 * (1 + C₁)) with hδdef
  have hδ0 : 0 < δ := by positivity
  obtain ⟨pb, hpb, hpbn⟩ := Ideal.Quotient.norm_mk_lt (locJB K m g f x) hδ0
  obtain ⟨pc, hpc, hpcn⟩ := Ideal.Quotient.norm_mk_lt (locIotaC K m g f x) hδ0
  have hpbM : ‖pb‖ < M + δ := by
    refine hpbn.trans_le ?_
    have h := le_max_left ‖locJB K m g f x‖ ‖locIotaC K m g f x‖
    linarith
  have hpcM : ‖pc‖ < M + δ := by
    refine hpcn.trans_le ?_
    have h := le_max_right ‖locJB K m g f x‖ ‖locIotaC K m g f x‖
    linarith
  -- the defect lies in the graph ideal at 𝓓
  have hdefect : extRhoB K m pb - extRhoC K m pc ∈ ID K m g f := by
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← locRhoB_mk, ← locRhoC_mk, hpb, hpc]
    exact loc_square_commutes K m g f x
  obtain ⟨xc, hxcIC, hxcρ, hxcn⟩ := hrow _ hdefect
  have hdn : ‖extRhoB K m pb - extRhoC K m pc‖ < M + δ := by
    have hsub : ‖extRhoB K m pb - extRhoC K m pc‖ ≤
        max ‖extRhoB K m pb‖ ‖extRhoC K m pc‖ := by
      have h := IsUltrametricDist.norm_add_le_max (extRhoB K m pb) (-(extRhoC K m pc))
      rwa [← sub_eq_add_neg, norm_neg] at h
    refine lt_of_le_of_lt hsub (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (norm_mapRestricted_le _ _ _ _) hpbM
    · exact lt_of_le_of_lt (norm_mapRestricted_le _ _ _ _) hpcM
  have hxcn' : ‖xc‖ ≤ C₁ * (M + δ) :=
    hxcn.trans (mul_le_mul_of_nonneg_left hdn.le hC₁0)
  set pc' : PC K m := pc + xc with hpc'def
  have hcompat : extRhoB K m pb = extRhoC K m pc' := by
    rw [hpc'def, map_add, hxcρ]
    ring
  obtain ⟨p', hp'b, hp'c⟩ := (ext_milnorRow_exact K m pb pc' hcompat).exists
  have hmkp' : Ideal.Quotient.mk (IA K m g f) p' = x := by
    refine loc_pair_injective K m g f ϖ hK₀ hspan ?_
    show (locJB K m g f _, locIotaC K m g f _) = (locJB K m g f x, locIotaC K m g f x)
    rw [Prod.mk.injEq]
    constructor
    · rw [locJB_mk, hp'b, hpb]
    · rw [locIotaC_mk, hp'c, hpc'def, ← hpc]
      rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, add_sub_cancel_left]
      exact hxcIC
  have hnormp' : ‖p'‖ ≤ (1 + C₁) * (M + δ) := by
    have hmax := ext_max_norm_eq K m p'
    rw [hp'b, hp'c] at hmax
    rw [← hmax]
    refine max_le ?_ ?_
    · nlinarith [hpbM.le, hM0, hδ0.le, hC₁0]
    · show ‖pc'‖ ≤ _
      rw [hpc'def]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · nlinarith [hpcM.le, hM0, hδ0.le, hC₁0]
      · nlinarith [hxcn', hM0, hδ0.le, hC₁0]
  calc ‖x‖ = ‖Ideal.Quotient.mk (IA K m g f) p'‖ := by rw [hmkp']
    _ ≤ ‖p'‖ := Ideal.Quotient.norm_mk_le _ p'
    _ ≤ (1 + C₁) * (M + δ) := hnormp'
    _ = (1 + C₁) * M + (1 + C₁) * δ := by ring
    _ ≤ (1 + C₁) * M + ε := by
        have hδval : (1 + C₁) * δ ≤ ε := by
          have h2 : (0 : ℝ) < 2 * (1 + C₁) := by linarith
          calc (1 + C₁) * δ = (1 + C₁) * (ε / (2 * (1 + C₁))) := by rw [hδdef]
            _ = ε / 2 := by
                field_simp
            _ ≤ ε := by linarith
        linarith

-- v4.33: instance search no longer sees the quotient-norm chain through the
-- `PA`/`locA` defs; restore pre-v4.33 defeq behaviour for these declarations.
/-- Topological strictness on the left ([FJP] (4.19)/(4.20)): `𝓐_α` carries the subspace
topology of `𝓑_α × 𝓒_α`. -/
theorem loc_pair_isEmbedding (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Topology.IsEmbedding
      (fun x : locA K m g f => (locJB K m g f x, locIotaC K m g f x)) := by
  classical
  haveI hclA : IsClosed ((IA K m g f : Set (PA K m))) := isClosed_IA K m g f ϖ hK₀ hspan
  haveI : NormedAddCommGroup (PA K m ⧸ IA K m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  set C₁ := Classical.choose (ideal_row_surjective K m g f ϖ hK₀ hspan) with hC₁def
  have hC₁1 := (Classical.choose_spec (ideal_row_surjective K m g f ϖ hK₀ hspan)).1
  have hK0 : (0 : ℝ) ≤ 1 + C₁ := by linarith
  have hcont : Continuous (fun x : locA K m g f =>
      (locJB K m g f x, locIotaC K m g f x)) :=
    Continuous.prodMk (locJB_lipschitz K m g f).continuous
      (locIotaC_lipschitz K m g f).continuous
  have hanti : AntilipschitzWith ⟨1 + C₁, hK0⟩
      (fun x : locA K m g f => (locJB K m g f x, locIotaC K m g f x)) := by
    refine AntilipschitzWith.of_le_mul_dist fun x y => ?_
    have hest := loc_norm_le K m g f ϖ hK₀ hspan (x - y)
    rw [map_sub, map_sub] at hest
    rw [dist_eq_norm, Prod.dist_eq]
    dsimp only
    rw [dist_eq_norm, dist_eq_norm]
    exact hest
  exact hanti.isEmbedding hcont

/-- `𝓒_α → 𝓓_α` is a continuous open surjection ([FJP] Prop 4.5: "`C_α → D_α` is a strict
surjection"). -/
theorem locRhoC_surjective (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    Function.Surjective (locRhoC K m g f) := by
  intro d
  obtain ⟨pd, rfl⟩ := Ideal.Quotient.mk_surjective d
  obtain ⟨c, hc, -⟩ := extRhoC_strict_surjective K m pd
  exact ⟨Ideal.Quotient.mk _ c, by rw [locRhoC_mk, hc]⟩

/-- `extRhoC` is open (constant-1 sections). -/
theorem extRhoC_isOpenMap : IsOpenMap (extRhoC K m) := by
  intro U hU
  rw [Metric.isOpen_iff] at hU ⊢
  rintro _ ⟨x, hxU, rfl⟩
  obtain ⟨ε, hε, hball⟩ := hU x hxU
  refine ⟨ε, hε, fun d hd => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hd
  obtain ⟨c, hc, hcn⟩ := extRhoC_strict_surjective K m (d - extRhoC K m x)
  refine ⟨x + c, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, hcn]
    exact hd
  · rw [map_add, hc]
    ring

theorem locRhoC_isOpenMap (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    IsOpenMap (locRhoC K m g f) := by
  intro U hU
  have hmkC_cont : Continuous (Ideal.Quotient.mk (IC K m g f)) := by
    have hlip : LipschitzWith 1 (Ideal.Quotient.mk (IC K m g f)) :=
      LipschitzWith.of_dist_le_mul fun a b => by
        rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm, ← map_sub]
        exact Ideal.Quotient.norm_mk_le _ _
    exact hlip.continuous
  have hmkD_open : IsOpenMap (Ideal.Quotient.mk (ID K m g f)) := by
    intro V hV
    rw [Metric.isOpen_iff] at hV ⊢
    rintro _ ⟨v, hvV, rfl⟩
    obtain ⟨ε, hε, hball⟩ := hV v hvV
    refine ⟨ε, hε, fun d hd => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hd
    have hpos : 0 < ε - ‖d - Ideal.Quotient.mk (ID K m g f) v‖ := by linarith
    obtain ⟨y, hy, hyn⟩ := Ideal.Quotient.norm_mk_lt
      (d - Ideal.Quotient.mk (ID K m g f) v) hpos
    refine ⟨v + y, hball ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      linarith
    · have hadd := RingHom.map_add (Ideal.Quotient.mk (ID K m g f)) v y
      rw [hadd, hy]
      ring
  have himg : locRhoC K m g f '' U =
      Ideal.Quotient.mk (ID K m g f) ''
        (extRhoC K m '' (Ideal.Quotient.mk (IC K m g f) ⁻¹' U)) := by
    ext d
    constructor
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective u
      exact ⟨extRhoC K m p, ⟨p, hu, rfl⟩, (locRhoC_mk K m g f p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Ideal.Quotient.mk _ p, hp, locRhoC_mk K m g f p⟩
  rw [himg]
  exact hmkD_open _ (extRhoC_isOpenMap K m _ (hU.preimage hmkC_cont))

/-- `𝓐_α` is Hausdorff (quotient by a closed ideal; [FJP] (4.21)). -/
theorem locA_t2 (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    T2Space (locA K m g f) := by
  haveI hclA : IsClosed ((IA K m g f : Set (PA K m))) := isClosed_IA K m g f ϖ hK₀ hspan
  haveI : NormedAddCommGroup (PA K m ⧸ IA K m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  infer_instance

/-- `𝓐_α` is complete (Banach quotient; [FJP] (4.21): "the completed graph quotient is
already the Banach quotient"). -/
theorem locA_completeSpace (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (unitBall K))
    (hspan : Ideal.span ({g} ∪ Set.range f) = ⊤) :
    @CompleteSpace (locA K m g f)
      (IsTopologicalAddGroup.rightUniformSpace (locA K m g f)) := by
  haveI hclA : IsClosed ((IA K m g f : Set (PA K m))) := isClosed_IA K m g f ϖ hK₀ hspan
  haveI : NormedAddCommGroup (PA K m ⧸ IA K m g f) :=
    Submodule.Quotient.normedAddCommGroup _
  haveI : IsUniformAddGroup (locA K m g f) := SeminormedAddCommGroup.to_isUniformAddGroup
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

end StrictLoc

end FiniteJetOver
