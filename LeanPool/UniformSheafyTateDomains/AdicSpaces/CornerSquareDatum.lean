/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativePieceKeystone

/-!
# Corner-square datum layer: generic pushed and intersection rational data (T624)

The ring-generic datum constructions consumed by Milnor-square instantiations
(`MilnorSheafTransfer.isSheafy_of_milnorSquare`): pushing a rational datum along a
continuous ring hom (`pushDatumOfHom`, [FJP] Lemma 5.1 made generic), the comap
characterization of the pushed rational open (`mem_rationalOpen_pushDatumOfHom_iff`,
[FJP] Lemma 5.2's pointwise coverage transfer), the intersection datum of two
rational data over one ring (`interDatumOfRational`, [FJP] Lemma 5.2's
`U_{ij} = U_i ∩ U_j`), and the push-of-intersection formula
(`pushDatumOfHom_interOpen`).

These generalize the Jet-concrete constructions of
`FJP/FiniteJetFunctoriality.lean` (`pushDatumB` :93, `mem_rationalOpen_pushDatumB_iff`
:2146, `interDatum` :2326) and `FJP/FiniteJetSheafTransfer.lean`
(`pushDatumB_interOpen` :147); the proofs are the same valuation-inequality chases,
with the power-bounded transport abstracted into the single subring hypothesis
`hAB : A⁺ ≤ (B⁺).comap φ` (exactly `comap_mem_spa`'s input).
-/

@[expose] public section

noncomputable section

namespace ValuationSpectrum

/-! ### Span transport along a ring hom -/

theorem span_finset_image_eq_top {A B : Type*} [CommRing A] [CommRing B] [DecidableEq B]
    (φ : A →+* B)
    {T : Finset A} (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((T.image φ : Finset B) : Set B) = ⊤ := by
  have hmap := congrArg (Ideal.map φ) h
  rw [Ideal.map_span, Ideal.map_top] at hmap
  rw [Finset.coe_image, ← hmap]

/-! ### The pushed datum along a continuous ring hom -/

section PushDatum

variable {A B : Type*}
  [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DecidableEq B]

/-- Push a rational datum along a ring hom (image datum, [FJP] Lemma 5.1 generically):
`s ↦ φ s`, `T ↦ φ '' T`, target pair of definition supplied. Rationality of `D` is
required to discharge `hopen` via the generic span-⊤ computation `genPiece_hopen`. -/
def pushDatumOfHom (φ : A →+* B) (PB : PairOfDefinition B)
    (D : RationalLocData A) (hD : D.IsRational) : RationalLocData B where
  P := PB
  T := D.T.image φ
  s := φ D.s
  hopen := genPiece_hopen PB (D.T.image φ) (φ D.s)
    (span_finset_image_eq_top φ hD.span_eq_top)

theorem pushDatumOfHom_isRational (φ : A →+* B) (PB : PairOfDefinition B)
    {D : RationalLocData A} (hD : D.IsRational) :
    (pushDatumOfHom φ PB D hD).IsRational :=
  RationalLocData.isRational_of_span_eq_top (span_finset_image_eq_top φ hD.span_eq_top)

/-- The comap characterization of the pushed rational open ([FJP] Lemma 5.2:
"inverse images preserve the defining valuation inequalities"). The power-bounded
transport hypothesis `hAB` is exactly `comap_mem_spa`'s input. -/
theorem mem_rationalOpen_pushDatumOfHom_iff [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (hAB : (A⁺ : Subring A) ≤ (B⁺ : Subring B).comap φ)
    (PB : PairOfDefinition B) (D : RationalLocData A) (hD : D.IsRational)
    (v : Spv B) (hv : v ∈ Spa B B⁺) :
    v ∈ rationalOpen (pushDatumOfHom φ PB D hD).T (pushDatumOfHom φ PB D hD).s ↔
      comap φ v ∈ rationalOpen D.T D.s := by
  have hcomap : comap φ v ∈ Spa A A⁺ := comap_mem_spa hφ hAB hv
  constructor
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hcomap, fun t ht => ?_, fun h0 => hs0 ?_⟩
    · rw [comap_vle]
      exact hvle (φ t) (Finset.mem_image_of_mem _ ht)
    · have := comap_vle φ v D.s 0
      rw [map_zero] at this
      rw [show (pushDatumOfHom φ PB D hD).s = φ D.s from rfl, ← this]
      exact h0
  · rintro ⟨-, hvle, hs0⟩
    refine ⟨hv, fun t' ht' => ?_, fun h0 => hs0 ?_⟩
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht'
      have := hvle t ht
      rwa [comap_vle] at this
    · have := comap_vle φ v D.s 0
      rw [map_zero] at this
      rw [this]
      exact h0

end PushDatum

/-! ### The intersection datum over one ring -/

section InterDatum

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTateRing A]

open scoped Pointwise in
/-- Spans of pointwise-product finsets of two spanning sets span (`⊤ * ⊤ = ⊤`).
The `DecidableEq` binder is deliberate: it makes the use site instantiate
`Finset.image` with the ambient instance (cf. the Jet-concrete original). -/
theorem span_mul_image_eq_top' {A : Type*} [CommRing A] [DecidableEq A]
    {T₁ T₂ : Finset A}
    (h₁ : Ideal.span (T₁ : Set A) = ⊤) (h₂ : Ideal.span (T₂ : Set A) = ⊤) :
    Ideal.span ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A) = ⊤ := by
  have hcoe : ((((T₁ ×ˢ T₂).image fun p => p.1 * p.2 : Finset A)) : Set A)
      = (T₁ : Set A) * (T₂ : Set A) := by
    rw [Finset.coe_image, Finset.coe_product]
    exact Set.image_mul_prod
  rw [hcoe, ← Ideal.span_mul_span', h₁, h₂, Ideal.top_mul]

/-- Spans of `insert`-enlarged spanning sets span. -/
theorem span_insert_eq_top' {A : Type*} [CommRing A] [DecidableEq A] {T : Finset A}
    (a : A) (h : Ideal.span (T : Set A) = ⊤) :
    Ideal.span ((insert a T : Finset A) : Set A) = ⊤ := by
  rw [← top_le_iff, ← h]
  exact Ideal.span_mono (by rw [Finset.coe_insert]; exact Set.subset_insert a _)

theorem interDatumOfRational_span_eq_top [DecidableEq A] (D₁ D₂ : RationalLocData A)
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    Ideal.span ((((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image
      fun p => p.1 * p.2 : Finset A)) : Set A) = ⊤ :=
  span_mul_image_eq_top' (span_insert_eq_top' D₁.s h₁.span_eq_top)
    (span_insert_eq_top' D₂.s h₂.span_eq_top)

/-- The product (intersection) datum of two rational data over one ring
([FJP] Lemma 5.2's `U_{ij} = U_i ∩ U_j`, generically). The factors are
`s`-normalized (`insert sᵢ Tᵢ`) so that the pointwise intersection formula
`rationalOpen_interDatumOfRational` holds; the pair of definition is inherited
from the first datum. -/
def interDatumOfRational [DecidableEq A] (D₁ D₂ : RationalLocData A)
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) : RationalLocData A where
  P := D₁.P
  T := (insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2
  s := D₁.s * D₂.s
  hopen := genPiece_hopen D₁.P
    ((insert D₁.s D₁.T ×ˢ insert D₂.s D₂.T).image fun p => p.1 * p.2)
    (D₁.s * D₂.s) (interDatumOfRational_span_eq_top D₁ D₂ h₁ h₂)

theorem interDatumOfRational_isRational [DecidableEq A] {D₁ D₂ : RationalLocData A}
    (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    (interDatumOfRational D₁ D₂ h₁ h₂).IsRational :=
  RationalLocData.isRational_of_span_eq_top
    (interDatumOfRational_span_eq_top D₁ D₂ h₁ h₂)

theorem rationalOpen_interDatumOfRational [DecidableEq A] [PlusSubring A]
    (D₁ D₂ : RationalLocData A) (h₁ : D₁.IsRational) (h₂ : D₂.IsRational) :
    rationalOpen (interDatumOfRational D₁ D₂ h₁ h₂).T
        (interDatumOfRational D₁ D₂ h₁ h₂).s =
      rationalOpen D₁.T D₁.s ∩ rationalOpen D₂.T D₂.s := by
  ext v
  constructor
  · rintro ⟨hspa, hvle, hs0⟩
    have hs₁0 : ¬ v.vle D₁.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 D₂.s
      rwa [zero_mul] at this)
    have hs₂0 : ¬ v.vle D₂.s 0 := fun h0 => hs0 (by
      have := v.mul_vle_mul_left h0 D₁.s
      rw [zero_mul, mul_comm D₂.s D₁.s] at this
      exact this)
    refine ⟨⟨hspa, fun t ht => ?_, hs₁0⟩, ⟨hspa, fun t ht => ?_, hs₂0⟩⟩
    · have hpair : t * D₂.s ∈ (interDatumOfRational D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(t, D₂.s), Finset.mem_product.mpr
          ⟨Finset.mem_insert_of_mem ht, Finset.mem_insert_self _ _⟩, rfl⟩
      exact v.vle_mul_cancel hs₂0 (hvle _ hpair)
    · have hpair : D₁.s * t ∈ (interDatumOfRational D₁ D₂ h₁ h₂).T :=
        Finset.mem_image.mpr ⟨(D₁.s, t), Finset.mem_product.mpr
          ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ht⟩, rfl⟩
      have h' := hvle _ hpair
      rw [show D₁.s * t = t * D₁.s from mul_comm _ _,
        show (interDatumOfRational D₁ D₂ h₁ h₂).s = D₂.s * D₁.s from mul_comm _ _] at h'
      exact v.vle_mul_cancel hs₁0 h'
  · rintro ⟨⟨hspa, hvle₁, hs₁0⟩, ⟨-, hvle₂, hs₂0⟩⟩
    have hvle₁' : ∀ t₁ ∈ insert D₁.s D₁.T, v.vle t₁ D₁.s := by
      intro t₁ ht₁
      rcases Finset.mem_insert.mp ht₁ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₁ t₁ h
    have hvle₂' : ∀ t₂ ∈ insert D₂.s D₂.T, v.vle t₂ D₂.s := by
      intro t₂ ht₂
      rcases Finset.mem_insert.mp ht₂ with h | h
      · subst h; exact (v.vle_total _ _).elim id id
      · exact hvle₂ t₂ h
    refine ⟨hspa, fun t' ht' => ?_, fun h0 => ?_⟩
    · obtain ⟨⟨t₁, t₂⟩, hmem, rfl⟩ := Finset.mem_image.mp ht'
      obtain ⟨ht₁, ht₂⟩ := Finset.mem_product.mp hmem
      have ha := v.mul_vle_mul_left (hvle₁' t₁ ht₁) t₂
      have hb := v.mul_vle_mul_left (hvle₂' t₂ ht₂) D₁.s
      rw [mul_comm t₂ D₁.s, mul_comm D₂.s D₁.s] at hb
      exact v.vle_trans ha hb
    · rw [show (interDatumOfRational D₁ D₂ h₁ h₂).s = D₁.s * D₂.s from rfl,
        show (0 : A) = 0 * D₂.s from (zero_mul _).symm] at h0
      exact hs₁0 (v.vle_mul_cancel hs₂0 h0)

end InterDatum

/-! ### Push of an intersection is the intersection of pushes -/

section PushInter

variable {A B : Type*}
  [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DecidableEq B]
  [PlusSubring A] [PlusSubring B]

/-- `(U₁ ∩ U₂)_B = (U₁)_B ∩ (U₂)_B` on rational opens ([FJP] Lemma 5.2, the
pushed-intersection formula, generically; pattern of `pushDatumB_interOpen`). -/
theorem pushDatumOfHom_interOpen [DecidableEq A] {φ : A →+* B} (hφ : Continuous φ)
    (hAB : (A⁺ : Subring A) ≤ (B⁺ : Subring B).comap φ) (PB : PairOfDefinition B)
    (d₁ d₂ : RationalLocData A) (h₁ : d₁.IsRational) (h₂ : d₂.IsRational) :
    rationalOpen (pushDatumOfHom φ PB (interDatumOfRational d₁ d₂ h₁ h₂)
        (interDatumOfRational_isRational h₁ h₂)).T
      (pushDatumOfHom φ PB (interDatumOfRational d₁ d₂ h₁ h₂)
        (interDatumOfRational_isRational h₁ h₂)).s =
    rationalOpen (pushDatumOfHom φ PB d₁ h₁).T (pushDatumOfHom φ PB d₁ h₁).s ∩
      rationalOpen (pushDatumOfHom φ PB d₂ h₂).T (pushDatumOfHom φ PB d₂ h₂).s := by
  ext v
  constructor
  · intro hv
    have hvspa : v ∈ Spa B B⁺ := hv.1
    have hmem := (mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB
      (interDatumOfRational d₁ d₂ h₁ h₂) (interDatumOfRational_isRational h₁ h₂)
      v hvspa).mp hv
    rw [rationalOpen_interDatumOfRational d₁ d₂ h₁ h₂] at hmem
    exact ⟨(mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB d₁ h₁ v hvspa).mpr hmem.1,
      (mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB d₂ h₂ v hvspa).mpr hmem.2⟩
  · rintro ⟨hv₁, hv₂⟩
    have hvspa : v ∈ Spa B B⁺ := hv₁.1
    refine (mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB
      (interDatumOfRational d₁ d₂ h₁ h₂) (interDatumOfRational_isRational h₁ h₂)
      v hvspa).mpr ?_
    rw [rationalOpen_interDatumOfRational d₁ d₂ h₁ h₂]
    exact ⟨(mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB d₁ h₁ v hvspa).mp hv₁,
      (mem_rationalOpen_pushDatumOfHom_iff hφ hAB PB d₂ h₂ v hvspa).mp hv₂⟩

end PushInter

/-! ### Iterated intersections (the Čech multi-intersection data, T631) -/

section InterList

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [DecidableEq A]

/-- Iterated intersection datum with its rationality, by folding
`interDatumOfRational` ([Wedhorn] Appendix A's `U_{i₀…i_q}`). -/
noncomputable def interListAux :
    ∀ {q : ℕ} (D : Fin (q + 1) → RationalLocData A),
      (∀ i, (D i).IsRational) → {E : RationalLocData A // E.IsRational}
  | 0, D, h => ⟨D 0, h 0⟩
  | (_ + 1), D, h =>
    let rest := interListAux (fun i => D i.succ) (fun i => h i.succ)
    ⟨interDatumOfRational (D 0) rest.1 (h 0) rest.2,
      interDatumOfRational_isRational (h 0) rest.2⟩

/-- The iterated intersection datum. -/
noncomputable def interList {q : ℕ} (D : Fin (q + 1) → RationalLocData A)
    (h : ∀ i, (D i).IsRational) : RationalLocData A :=
  (interListAux D h).1

theorem interList_isRational {q : ℕ} (D : Fin (q + 1) → RationalLocData A)
    (h : ∀ i, (D i).IsRational) : (interList D h).IsRational :=
  (interListAux D h).2

theorem interList_zero (D : Fin 1 → RationalLocData A)
    (h : ∀ i, (D i).IsRational) : interList D h = D 0 := rfl

theorem interList_succ {q : ℕ} (D : Fin (q + 2) → RationalLocData A)
    (h : ∀ i, (D i).IsRational) :
    interList D h = interDatumOfRational (D 0)
      (interList (fun i => D i.succ) (fun i => h i.succ)) (h 0)
      (interList_isRational _ _) := rfl

/-- The iterated intersection cuts out the intersection of the rational opens. -/
theorem rationalOpen_interList [PlusSubring A] {q : ℕ}
    (D : Fin (q + 1) → RationalLocData A) (h : ∀ i, (D i).IsRational) :
    rationalOpen (interList D h).T (interList D h).s =
      ⋂ i, rationalOpen (D i).T (D i).s := by
  induction q with
  | zero =>
    rw [interList_zero]
    ext v
    simp only [Set.mem_iInter]
    exact ⟨fun hv i => by rw [Fin.fin_one_eq_zero i]; exact hv, fun hv => hv 0⟩
  | succ q ih =>
    rw [interList_succ, rationalOpen_interDatumOfRational,
      ih (fun i => D i.succ) (fun i => h i.succ)]
    ext v
    simp only [Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨h0, hs⟩ i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · exact h0
      · exact hs j
    · intro hall
      exact ⟨hall 0, fun j => hall j.succ⟩

end InterList

end ValuationSpectrum
