/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaRationalOpenComparison
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaParameterPerturbation
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RelativeDescent

/-!
# Wedhorn Proposition 8.2(2): the `Spa` comparison is a homeomorphism

The openness half of Wedhorn 8.2(2): the canonical bijection
`spaPresheafValueEquivRationalOpen D` (forward map `comap D.canonicalMap`) is a
**homeomorphism** `Spa (presheafValue D) ((presheafValue D)⁺) ≃ₜ R(T/s) ∩ Spa (A, A⁺)`.

Wedhorn's proof shape is followed faithfully:

1. **rational basis** (`exists_spanning_presentation_of_mem_basicOpens`): every
   finite intersection of basic opens containing a Spa-point contains a rational
   presentation with *spanning* parameters (throw a `ϖ^k` into the numerators —
   Wedhorn Remark 7.30-adjacent);
2. **approximation** (Wedhorn 7.48 / Kedlaya Ex. 1.2.2, from
   `SpaParameterPerturbation.lean`): perturb the parameters into the dense image
   of the uncompleted localization without changing the subset;
3. **denominator clearing** (Wedhorn 8.2: "multiplying with a suitable power of
   `s`"): scale by the unit `canonicalMap (s^N)` to land the parameters in the
   image of `A`;
4. the resulting presentation is the `comap`-preimage of a *finite intersection
   of basic opens of `Spv A`* (by `comap_vle`), so the forward map is open onto
   its image.

Main results:
* `exists_A_level_open_presentation` — the composite of 1–4.
* `spaPresheafValueEquivRationalOpen_isOpenMap` — openness.
* `spaPresheafValueHomeomorphRationalOpen` — the **comparison homeomorphism** in
  Tate scope, with exact image the rational open (Wedhorn Proposition 8.2(2),
  *homeomorphism part*).

**Scope note.** This is the homeomorphism onto `R(T/s) ∩ Spa (A,A⁺)` with
forward map `comap D.canonicalMap`. The remaining assertion of Proposition
8.2(2) — that this homeomorphism induces a *bijection between the valid rational
subsets* of the two spectra — is delivered in
`SpaRationalSubsetCorrespondence.lean`
(`spaPresheafValueRationalSubsetEquiv`, the complete-Tate specialization).
-/

noncomputable section

open Filter Topology

namespace ValuationSpectrum

universe u v

/-! ### Generic ingredients over a topological ring -/

section Generic

variable {B : Type u} [CommRing B] [TopologicalSpace B]

/-- A continuous valuation eventually satisfies `v(ϖ^k) ≤ v(g)` for any `g` with
`v(g) ≠ 0`. -/
theorem exists_pow_vle_of_isContinuous {v : Spv B} (hv : v.IsContinuous)
    {ϖ : B} (hϖ : IsTopologicallyNilpotent ϖ) {g : B} (hg : ¬ v.vle g 0) :
    ∃ k : ℕ, v.vle (ϖ ^ k) g := by
  letI : ValuativeRel B := v.toValuativeRel
  have hbridge : ∀ x y : B, v.vle x y ↔
      ValuativeRel.valuation B x ≤ ValuativeRel.valuation B y := fun x y =>
    Valuation.Compatible.vle_iff_le (v := ValuativeRel.valuation B) x y
  have hg0 : ValuativeRel.valuation B g ≠ 0 := by
    intro hc
    exact hg ((hbridge g 0).mpr (by rw [map_zero, hc]))
  have hopen : IsOpen {a : B | ValuativeRel.valuation B a <
      ValuativeRel.valuation B g} := hv _
  have h0 : (0 : B) ∈ {a : B | ValuativeRel.valuation B a <
      ValuativeRel.valuation B g} := by
    simp only [Set.mem_setOf_eq, map_zero]
    exact zero_lt_iff.mpr hg0
  obtain ⟨k, hk⟩ := (hϖ.eventually_mem (hopen.mem_nhds h0)).exists
  simp only [Set.mem_setOf_eq] at hk
  exact ⟨k, (hbridge _ _).mpr hk.le⟩

variable [IsTopologicalRing B] [PlusSubring B]

/-- Scaling all parameters of an indexed rational set by a unit does not change
it. -/
theorem indexedRationalSet_unit_mul_eq {ι : Type v} {u : B} (hu : IsUnit u)
    (s : Finset ι) (f : ι → B) (g : B) :
    indexedRationalSet B s (fun i => u * f i) (u * g) =
      indexedRationalSet B s f g := by
  ext v
  simp only [indexedRationalSet, Set.mem_setOf_eq]
  refine and_congr_right fun hv => ?_
  have hu_ne : ¬ v.vle u 0 := not_vle_zero_of_isUnit hu v
  constructor
  · rintro ⟨hT, hg⟩
    refine ⟨fun i hi => ?_, fun hc => ?_⟩
    · have := hT i hi
      rw [show u * f i = f i * u from mul_comm _ _,
        show u * g = g * u from mul_comm _ _] at this
      exact v.vle_mul_cancel hu_ne this
    · refine hg ?_
      have := v.mul_vle_mul_left hc u
      rwa [zero_mul, show g * u = u * g from mul_comm _ _] at this
  · rintro ⟨hT, hg⟩
    refine ⟨fun i hi => ?_, fun hc => ?_⟩
    · have := v.mul_vle_mul_left (hT i hi) u
      rwa [show f i * u = u * f i from mul_comm _ _,
        show g * u = u * g from mul_comm _ _] at this
    · refine hg ?_
      rw [show u * g = g * u from mul_comm _ _,
        show (0 : B) = 0 * u from (zero_mul u).symm] at hc
      exact v.vle_mul_cancel hu_ne hc

/-- Uniform spanning bound, indexed form producing the hypothesis shape of
`indexedRationalSet_perturb_eq`. -/
theorem exists_uniform_bound_insert [IsRingOfIntegralElements (B⁺ : Subring B)]
    {ϖ : B} (hϖ : IsTopologicallyNilpotent ϖ) {ι : Type v} [DecidableEq B]
    {s : Finset ι} {f : ι → B} {g : B}
    (hspan : Ideal.span ((insert g (s.image f) : Finset B) : Set B) = ⊤) :
    ∃ M : ℕ, ∀ v : Spv B, v ∈ Spa B B⁺ →
      v.vle (ϖ ^ M) g ∨ ∃ i ∈ s, v.vle (ϖ ^ M) (f i) := by
  obtain ⟨M, hM⟩ := exists_uniform_spanning_bound hϖ hspan
  refine ⟨M, fun v hv => ?_⟩
  obtain ⟨t, ht, hvle⟩ := hM v hv
  rcases Finset.mem_insert.mp ht with rfl | ht'
  · exact Or.inl hvle
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ht'
    exact Or.inr ⟨i, hi, hvle⟩

/-- **The rational-basis trick** (Wedhorn Remark 7.30-adjacent): a Spa-point in a
finite intersection of basic opens lies in an indexed rational set with
*spanning* parameters contained in that intersection. The numerators are
`ϖ^k` (making the parameters span) and the cross terms
`(∏_{j ≠ i} G j) · F i`; the denominator is `∏ G i`. -/
theorem exists_spanning_presentation_of_mem_basicOpens [DecidableEq B]
    {ϖ : B} (hϖ_unit : IsUnit ϖ) (hϖ : IsTopologicallyNilpotent ϖ)
    {w : Spv B} (hw : w ∈ Spa B B⁺) {ι : Type v} [DecidableEq ι]
    {fam : Finset ι} {F G : ι → B}
    (hmem : ∀ i ∈ fam, w ∈ basicOpen (F i) (G i)) :
    ∃ (f : Option ι → B) (g : B),
      Ideal.span ((insert g ((insert none (fam.image some)).image f) :
        Finset B) : Set B) = ⊤ ∧
      w ∈ indexedRationalSet B (insert none (fam.image some)) f g ∧
      indexedRationalSet B (insert none (fam.image some)) f g ⊆
        ⋂ i ∈ fam, basicOpen (F i) (G i) := by
  classical
  set g : B := ∏ i ∈ fam, G i with hg_def
  -- `v(g) ≠ 0` at `w` (the support is prime)
  have hGw : ∀ i ∈ fam, ¬ w.vle (G i) 0 := fun i hi => (hmem i hi).2
  have hgw : ¬ w.vle g 0 := by
    rw [show ∀ x, w.vle x 0 ↔ x ∈ w.supp from fun x => (mem_supp_iff w x).symm]
    intro hc
    obtain ⟨i, hi, hGi⟩ := (Ideal.IsPrime.prod_mem_iff).mp hc
    exact hGw i hi ((mem_supp_iff w _).mp hGi)
  -- pick `k` with `w(ϖ^k) ≤ w(g)` (continuity)
  obtain ⟨k, hk⟩ := exists_pow_vle_of_isContinuous hw.1 hϖ hgw
  refine ⟨fun o => o.elim (ϖ ^ k) (fun i => (∏ j ∈ fam.erase i, G j) * F i), g,
    ?_, ?_, ?_⟩
  · -- spanning: `ϖ^k` is a unit in the parameter set
    refine Ideal.eq_top_of_isUnit_mem _ ?_ (hϖ_unit.pow k)
    refine Ideal.subset_span (Finset.mem_coe.mpr ?_)
    exact Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨none, Finset.mem_insert_self _ _, rfl⟩)
  · -- membership of `w`
    refine ⟨hw, fun o ho => ?_, hgw⟩
    match o with
    | none => exact hk
    | some i =>
      have hi : i ∈ fam := by
        rcases Finset.mem_insert.mp ho with h | h
        · exact absurd h (by simp)
        · obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp h
          exact Option.some_injective _ hji ▸ hj
      show w.vle ((∏ j ∈ fam.erase i, G j) * F i) g
      have hmul := w.mul_vle_mul_left (hmem i hi).1 (∏ j ∈ fam.erase i, G j)
      rw [show F i * ∏ j ∈ fam.erase i, G j =
          (∏ j ∈ fam.erase i, G j) * F i from mul_comm _ _,
        show G i * ∏ j ∈ fam.erase i, G j = g from Finset.mul_prod_erase fam G hi]
        at hmul
      exact hmul
  · -- inclusion into each basic open
    rintro v ⟨hv, hT, hg_ne⟩
    simp only [Set.mem_iInter]
    intro i hi
    have hGprod_ne : ¬ v.vle (∏ j ∈ fam.erase i, G j) 0 := by
      intro hc
      refine hg_ne ?_
      rw [← mem_supp_iff] at hc ⊢
      rw [show g = (∏ j ∈ fam.erase i, G j) * G i from
        (Finset.prod_erase_mul fam G hi).symm]
      exact Ideal.mul_mem_right _ _ hc
    have hGi_ne : ¬ v.vle (G i) 0 := by
      intro hc
      refine hg_ne ?_
      rw [← mem_supp_iff] at hc ⊢
      rw [show g = (∏ j ∈ fam.erase i, G j) * G i from
        (Finset.prod_erase_mul fam G hi).symm]
      exact Ideal.mul_mem_left _ _ hc
    have hvle := hT (some i) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem some hi))
    show v.vle (F i) (G i) ∧ ¬ v.vle (G i) 0
    refine ⟨?_, hGi_ne⟩
    have : v.vle (F i * (∏ j ∈ fam.erase i, G j))
        (G i * (∏ j ∈ fam.erase i, G j)) := by
      rw [show F i * (∏ j ∈ fam.erase i, G j) =
          (∏ j ∈ fam.erase i, G j) * F i from mul_comm _ _,
        show G i * (∏ j ∈ fam.erase i, G j) = g from Finset.mul_prod_erase fam G hi]
      exact hvle
    exact v.vle_mul_cancel hGprod_ne this

end Generic

/-! ### The `presheafValue` chain: approximation + clearing + openness -/

section PresheafValue

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [PlusSubring A] [IsHuberRing A]

/-- **The A-level open presentation** (Wedhorn 8.2(2), steps 1–4 of the file
docstring): every finite intersection of basic opens of `Spv (presheafValue D)`
around a Spa-point contains, relatively to `Spa`, the `comap`-preimage of a
finite intersection of basic opens of `Spv A`. -/
theorem exists_A_level_open_presentation [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A)
    {w : Spv (presheafValue D)}
    (hw : w ∈ Spa (presheafValue D) (presheafValue D)⁺)
    {ι : Type v} [DecidableEq ι] {fam : Finset ι} {F G : ι → presheafValue D}
    (hmem : ∀ i ∈ fam, w ∈ basicOpen (F i) (G i)) :
    ∃ W : Set (Spv A), IsOpen W ∧ comap D.canonicalMap w ∈ W ∧
      ∀ w' : Spv (presheafValue D),
        w' ∈ Spa (presheafValue D) (presheafValue D)⁺ →
        comap D.canonicalMap w' ∈ W →
        ∀ i ∈ fam, w' ∈ basicOpen (F i) (G i) := by
  classical
  -- the topologically nilpotent unit of the completion
  obtain ⟨u, hu⟩ := presheafValue_topNilUnit D
  have hϖ_unit : IsUnit ((u : (presheafValue D)ˣ) : presheafValue D) := u.isUnit
  -- Step 1: spanning presentation inside the intersection
  obtain ⟨f, g, hspan, hw_mem, hsubset⟩ :=
    exists_spanning_presentation_of_mem_basicOpens hϖ_unit hu hw hmem
  set idx : Finset (Option ι) := insert none (fam.image some) with hidx_def
  -- Step 2: uniform bound + density approximation into the localization image
  obtain ⟨M, hM⟩ :=
    exists_uniform_bound_insert hu (s := idx) (f := f) (g := g) hspan
  have hdense : DenseRange (⇑(D.coeRingHom)) := fun y =>
    @UniformSpace.Completion.denseRange_coe _ D.uniformSpace y
  have hcoset : ∀ x : presheafValue D, ∃ l : Localization.Away D.s,
      ∃ b ∈ ((presheafValue D)⁺ : Subring (presheafValue D)),
        D.coeRingHom l = x + (u : presheafValue D) ^ (M + 1) * b := by
    intro x
    obtain ⟨u', hu'⟩ := (hϖ_unit.pow (M + 1)).exists_left_inv
    have hplus : IsOpen (((presheafValue D)⁺ :
        Subring (presheafValue D)) : Set (presheafValue D)) :=
      (inferInstance : IsRingOfIntegralElements
        ((presheafValue D)⁺ : Subring (presheafValue D))).isOpen
    have hO_open : IsOpen ((fun y => u' * (y - x)) ⁻¹'
        (((presheafValue D)⁺ : Subring (presheafValue D)) :
          Set (presheafValue D))) :=
      hplus.preimage (continuous_const.mul (continuous_id.sub continuous_const))
    have hxO : x ∈ (fun y => u' * (y - x)) ⁻¹'
        (((presheafValue D)⁺ : Subring (presheafValue D)) :
          Set (presheafValue D)) := by
      simp only [Set.mem_preimage, sub_self, mul_zero, SetLike.mem_coe]
      exact Subring.zero_mem _
    obtain ⟨l, hl⟩ := hdense.exists_mem_open hO_open ⟨x, hxO⟩
    refine ⟨l, u' * (D.coeRingHom l - x), hl, ?_⟩
    have hcalc : (u : presheafValue D) ^ (M + 1) * (u' * (D.coeRingHom l - x)) =
        D.coeRingHom l - x := by
      rw [← mul_assoc, mul_comm ((u : presheafValue D) ^ (M + 1)) u', hu', one_mul]
    rw [hcalc]
    ring
  choose lf bf hbf hlf using fun o => hcoset (f o)
  obtain ⟨lg, bg, hbg, hlg⟩ := hcoset g
  have hpert : indexedRationalSet (presheafValue D) idx f g =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.coeRingHom (lf o)) (D.coeRingHom lg) :=
    indexedRationalSet_perturb_eq hϖ_unit hu hM
      (fun o _ => ⟨bf o, hbf o, hlf o⟩) ⟨bg, hbg, hlg⟩
  -- Step 3: clear denominators — scale by the unit `canonicalMap b`
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers D.s) (insert none (idx.image some))
    (fun o : Option (Option ι) => o.elim lg lf)
  have hbg' : IsLocalization.IsInteger A ((b : A) • lg) :=
    hb none (Finset.mem_insert_self _ _)
  have hbf' : ∀ o : Option ι, ∃ a : A, o ∈ idx →
      algebraMap A (Localization.Away D.s) a = (b : A) • lf o := by
    intro o
    by_cases ho : o ∈ idx
    · obtain ⟨a, ha⟩ := hb (some o)
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem some ho))
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun hc => absurd hc ho⟩
  choose hA hhA using hbf'
  obtain ⟨q, hq⟩ := hbg'
  set U : presheafValue D :=
    D.coeRingHom (algebraMap A (Localization.Away D.s) (b : A)) with hU_def
  have hU_unit : IsUnit U :=
    (IsLocalization.map_units (Localization.Away D.s) b).map D.coeRingHom
  have hqparam : D.canonicalMap q = U * D.coeRingHom lg := by
    have hstep := congrArg D.coeRingHom hq
    rw [Algebra.smul_def, map_mul] at hstep
    exact hstep
  have hparam : ∀ o ∈ idx, D.canonicalMap (hA o) = U * D.coeRingHom (lf o) := by
    intro o ho
    have hstep := congrArg D.coeRingHom (hhA o ho)
    rw [Algebra.smul_def, map_mul] at hstep
    exact hstep
  have hset' : indexedRationalSet (presheafValue D) idx
      (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.coeRingHom (lf o)) (D.coeRingHom lg) := by
    have hstep : indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) =
        indexedRationalSet (presheafValue D) idx
          (fun o => U * D.coeRingHom (lf o)) (U * D.coeRingHom lg) := by
      ext v
      simp only [indexedRationalSet, Set.mem_setOf_eq]
      refine and_congr_right fun hv => ?_
      rw [hqparam]
      constructor
      · rintro ⟨hT, h0⟩
        exact ⟨fun o ho => by rw [← hparam o ho]; exact hT o ho, h0⟩
      · rintro ⟨hT, h0⟩
        exact ⟨fun o ho => by rw [hparam o ho]; exact hT o ho, h0⟩
    rw [hstep, indexedRationalSet_unit_mul_eq hU_unit]
  have hchain : indexedRationalSet (presheafValue D) idx f g =
      indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) :=
    hpert.trans hset'.symm
  -- Step 4: the downstairs open and the transfer
  refine ⟨⋂ o ∈ idx, basicOpen (hA o) q, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset fun o _ =>
      TopologicalSpace.isOpen_generateFrom_of_mem ⟨hA o, q, rfl⟩
  · have hw_mem' : w ∈ indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) := hchain ▸ hw_mem
    obtain ⟨-, hT, h0⟩ := hw_mem'
    simp only [Set.mem_iInter]
    intro o ho
    exact ⟨hT o ho, by rwa [comap_vle, map_zero]⟩
  · intro w' hw' hWmem
    simp only [Set.mem_iInter] at hWmem
    have hmem' : w' ∈ indexedRationalSet (presheafValue D) idx
        (fun o => D.canonicalMap (hA o)) (D.canonicalMap q) := by
      refine ⟨hw', fun o ho => (hWmem o ho).1, ?_⟩
      have := (hWmem none (Finset.mem_insert_self _ _)).2
      rwa [comap_vle, map_zero] at this
    rw [← hchain] at hmem'
    have hfinal := hsubset hmem'
    simp only [Set.mem_iInter] at hfinal
    exact hfinal

/-- **Openness of the Wedhorn 8.2 comparison map**: the forward map of
`spaPresheafValueEquivRationalOpen` is an open map. -/
theorem spaPresheafValueEquivRationalOpen_isOpenMap [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A) :
    IsOpenMap (spaPresheafValueEquivRationalOpen D) := by
  classical
  intro Uopen hUopen
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨w, hwU, rfl⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.mp hUopen
  have hbasis := TopologicalSpace.isTopologicalBasis_of_subbasis
    (t := (instTopologicalSpace : TopologicalSpace (Spv (presheafValue D))))
    (s := {U : Set (Spv (presheafValue D)) | ∃ f s, U = basicOpen f s}) rfl
  have hwV : (w : Spv (presheafValue D)) ∈ V := hwU
  obtain ⟨t, ht, hwt, htV⟩ := hbasis.exists_subset_of_mem_open hwV hV
  obtain ⟨fam₀, ⟨hfam₀_fin, hfam₀_sub⟩, rfl⟩ := ht
  -- choose parameters for each member of the finite family
  have hFG : ∀ e : Set (Spv (presheafValue D)),
      ∃ p : presheafValue D × presheafValue D, e ∈ fam₀ →
        e = basicOpen p.1 p.2 := by
    intro e
    by_cases he : e ∈ fam₀
    · obtain ⟨f, s, rfl⟩ := hfam₀_sub he
      exact ⟨(f, s), fun _ => rfl⟩
    · exact ⟨(0, 0), fun hc => absurd hc he⟩
  choose P hP using hFG
  have hmem : ∀ e ∈ hfam₀_fin.toFinset,
      (w : Spv (presheafValue D)) ∈ basicOpen (P e).1 (P e).2 := by
    intro e he
    rw [← hP e ((Set.Finite.mem_toFinset _).mp he)]
    exact hwt _ ((Set.Finite.mem_toFinset _).mp he)
  obtain ⟨W, hW_open, hW_mem, hW_capture⟩ := exists_A_level_open_presentation D w.2
    (fam := hfam₀_fin.toFinset) (F := fun e => (P e).1) (G := fun e => (P e).2) hmem
  refine ⟨Subtype.val ⁻¹' W, ?_, hW_open.preimage continuous_subtype_val, hW_mem⟩
  intro z hz
  refine ⟨(spaPresheafValueEquivRationalOpen D).symm z, ?_,
    Equiv.apply_symm_apply _ z⟩
  have hspa := ((spaPresheafValueEquivRationalOpen D).symm z).2
  have hcm : comap D.canonicalMap
      (((spaPresheafValueEquivRationalOpen D).symm z :
        ↥(Spa (presheafValue D) (presheafValue D)⁺)) : Spv (presheafValue D)) =
      (z : Spv A) :=
    congrArg Subtype.val
      (Equiv.apply_symm_apply (spaPresheafValueEquivRationalOpen D) z)
  have hin := hW_capture _ hspa (by rw [hcm]; exact hz)
  show (((spaPresheafValueEquivRationalOpen D).symm z : _) : Spv (presheafValue D)) ∈ V
  refine htV ?_
  rw [Set.mem_sInter]
  intro e he
  rw [hP e he]
  exact hin e ((Set.Finite.mem_toFinset _).mpr he)

/-- **Wedhorn Proposition 8.2(2), the homeomorphism**:
`Spa (presheafValue D) ((presheafValue D)⁺) ≃ₜ R(T/s) ∩ Spa (A, A⁺)`, with
forward map the valuation pull-back along `D.canonicalMap`
(`spaPresheafValueHomeomorphRationalOpen_apply_coe`). Bijectivity is
`spaPresheafValueEquivRationalOpen`; forward continuity is the restriction of
`comap_continuous`; openness is Huber's approximation argument
(`spaPresheafValueEquivRationalOpen_isOpenMap`). -/
def spaPresheafValueHomeomorphRationalOpen [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A) :
    ↥(Spa (presheafValue D) (presheafValue D)⁺) ≃ₜ
      ↥(rationalOpen D.T D.s ∩ Spa A A⁺ : Set (Spv A)) :=
  (spaPresheafValueEquivRationalOpen D).toHomeomorphOfContinuousOpen
    (spaPresheafValueEquivRationalOpen_continuous D)
    (spaPresheafValueEquivRationalOpen_isOpenMap D)

@[simp] theorem spaPresheafValueHomeomorphRationalOpen_apply_coe [IsTateRing A]
    [IsRingOfIntegralElements (A⁺ : Subring A)] (D : RationalLocData A)
    (w : ↥(Spa (presheafValue D) (presheafValue D)⁺)) :
    ((spaPresheafValueHomeomorphRationalOpen D w :
      ↥(rationalOpen D.T D.s ∩ Spa A A⁺)) : Spv A) =
      comap D.canonicalMap (w : Spv (presheafValue D)) := rfl

end PresheafValue

end ValuationSpectrum
