/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaRationalOpenHomeomorph
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalIntersection
import LeanPool.UniformSheafyTateDomains.AdicSpaces.RationalBasis
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SpaCompactNoHArch
import LeanPool.UniformSheafyTateDomains.AdicSpaces.PresheafTateStructure

/-!
# Wedhorn Proposition 8.2(2): the bijection of valid rational subsets

The **complete-Tate specialization** of the rational-subset half of Wedhorn
Proposition 8.2(2): the homeomorphism `Spa (A⟨T/s⟩, A⟨T/s⟩⁺) ≅ R(T/s)`
(`spaPresheafValueHomeomorphRationalOpen`) induces a bijection between the
valid rational subsets of `Spa A⟨T/s⟩` and the valid rational subsets of
`Spa (A, A⁺)` contained in `R(T/s)`:

* `imgDatum_mem_rationalOpen_iff` — clean membership for the image datum: an
  upstairs valuation lies in `R(imgDatum D W)` iff it is a Spa-point whose
  canonical-map pull-back lies in the downstairs `R(W)`. No noetherian,
  strong-noetherian, `CompatiblePlusSubring`, or explicit
  `HasLocLiftPowerBounded` hypotheses.
* `exists_downstairs_rationalDatum` — **the hard direction**: every valid
  rational datum upstairs presents the same subset as the image of a valid
  downstairs datum. Route: approximate the parameters into the dense
  localization image (`indexedRationalSet_perturb_eq` with the uniform
  spanning bound), clear denominators by a unit of the localization, then pad
  the downstairs numerator family with a power `π^N` of a topologically
  nilpotent unit dominated by the denominator on the *compact* upstairs
  subset (`isCompact_spaOpen` + `exists_uniform_pow_vle_on_compact`) — the
  padding makes the downstairs family span `⊤` without changing the upstairs
  subset. (The independent perturbation theorem
  `exists_parameterPerturbation_span_top` is deliberately not used: the direct
  Tate proof enforces span-top by the unit padding.)
* `spaPresheafValueRationalSubsetEquiv` — the packaged equivalence. Following
  Wedhorn, the forward image of an upstairs rational subset is
  `R(D) ∩ R(W)` — the intersection with the base rational subset, realized by
  `interRational`; it is **not** merely `R(W)`.

**Scope honesty**: stated for a complete Tate ring `A` — the complete-Tate
specialization of Proposition 8.2(2), not the full arbitrary-affinoid theorem.
-/

noncomputable section

open Filter Topology

open scoped Classical

namespace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTateRing A]
  [T2Space A] [NonarchimedeanRing A]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A]
  [PlusSubring A] [IsRingOfIntegralElements (A⁺ : Subring A)]

/-! ### Generalities: open spans in Tate rings, valid data present rational subsets -/

/-- In a Tate ring, a finite family generating an open ideal generates the unit
ideal (Wedhorn Remark 7.30(1) for Definition 7.29's condition). -/
theorem span_eq_top_of_isOpen_span {B : Type*} [CommRing B] [TopologicalSpace B]
    [IsTateRing B] {T : Finset B}
    (h : IsOpen (((Ideal.span (T : Set B) : Ideal B) : Set B))) :
    Ideal.span (T : Set B) = ⊤ := by
  obtain ⟨u, hu⟩ := ‹IsTateRing B›.exists_topologicallyNilpotent_unit
  obtain ⟨n, hn⟩ :=
    (hu.eventually_mem (h.mem_nhds (Ideal.span (T : Set B)).zero_mem)).exists
  exact Ideal.eq_top_of_isUnit_mem _ hn (u.isUnit.pow n)

/-- A valid rational localization datum presents a rational subset (in the
honest `IsRationalSubset` sense: the presentation's span is open). -/
theorem RationalLocData.isRationalSubset_rationalOpen {B : Type*} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [PlusSubring B]
    {D : RationalLocData B} (hD : D.IsRational) :
    IsRationalSubset (rationalOpen D.T D.s) :=
  ⟨D.T, D.s, hD, rfl⟩

/-! ### The clean membership theorem for the image datum -/

omit [T2Space A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
/-- **Membership in an image-datum rational open** (Wedhorn Prop 8.2 + Remark
8.4, clean form): an upstairs valuation lies in `R(imgDatum D E)` iff it is a
Spa-point of the completed localization whose canonical-map pull-back lies in
the downstairs `R(E)`. The conditions transport verbatim through `comap_vle`. -/
theorem imgDatum_mem_rationalOpen_iff (D E : RationalLocData A)
    (hspanE : Ideal.span (E.T : Set A) = ⊤) (w : Spv (presheafValue D)) :
    w ∈ rationalOpen (imgDatum D E hspanE).T (imgDatum D E hspanE).s ↔
      w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
        comap D.canonicalMap w ∈ rationalOpen E.T E.s := by
  constructor
  · rintro ⟨hspa, hcond, hnz⟩
    refine ⟨hspa, comap_mem_spa (canonicalMap_continuous D)
      D.canonicalMap_integral hspa, fun t ht => ?_, fun h0 => ?_⟩
    · rw [comap_vle]
      have := hcond (D.canonicalMap t) (by
        rw [imgDatum_T]; exact Finset.mem_image_of_mem _ ht)
      rwa [imgDatum_s] at this
    · rw [comap_vle, map_zero] at h0
      rw [imgDatum_s] at hnz
      exact hnz h0
  · rintro ⟨hspa, -, hcond, hnz⟩
    refine ⟨hspa, fun x hx => ?_, fun h0 => ?_⟩
    · rw [imgDatum_T, Finset.mem_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      rw [imgDatum_s]
      have := hcond t ht
      rwa [comap_vle] at this
    · rw [imgDatum_s] at h0
      exact hnz (by rw [comap_vle, map_zero]; exact h0)

/-! ### The hard direction: every upstairs rational subset descends -/

omit [T2Space A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- **The reverse-image construction** (Wedhorn Proposition 8.2(2), hard
direction, complete-Tate specialization): every valid rational datum `E` over
the completed localization `A⟨T/s⟩` presents the same rational open as the
image of some valid datum `W` over `A`.

Proof route: approximate `E`'s parameters into the dense localization image
without changing the subset (uniform spanning bound + perturbation), clear
denominators with a unit of the localization, then pad the resulting
`A`-level numerator family with `π^N` — a topologically nilpotent unit power
uniformly dominated by the denominator on the *compact* upstairs subset — so
that the downstairs family spans `⊤` (the unit is in it) while the upstairs
subset is unchanged (the added condition holds throughout). -/
theorem exists_downstairs_rationalDatum
    (D : RationalLocData A) (_hD : D.IsRational)
    (E : RationalLocData (presheafValue D)) (hE : E.IsRational) :
    ∃ (W : RationalLocData A) (hW : W.IsRational),
      rationalOpen E.T E.s =
        rationalOpen (imgDatum D W hW.span_eq_top).T
          (imgDatum D W hW.span_eq_top).s := by
  classical
  haveI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  haveI : IsHuberRing (presheafValue D) := hTateB.toIsHuberRing
  -- Step 1: the topologically nilpotent unit upstairs
  obtain ⟨u, hu⟩ := presheafValue_topNilUnit D
  have hu_unit : IsUnit ((u : (presheafValue D)ˣ) : presheafValue D) := u.isUnit
  -- Step 2: the uniform perturbation bound for `E`'s parameters
  have hspanE : Ideal.span (E.T : Set (presheafValue D)) = ⊤ := hE.span_eq_top
  have hins : Ideal.span ((insert E.s (E.T.attach.image Subtype.val) :
      Finset (presheafValue D)) : Set (presheafValue D)) = ⊤ := by
    rw [Finset.attach_image_val]
    refine top_unique (le_trans (le_of_eq hspanE.symm) (Ideal.span_mono ?_))
    exact fun x hx => Finset.mem_insert_of_mem hx
  obtain ⟨M, hM⟩ := exists_uniform_bound_insert hu
    (s := E.T.attach) (f := Subtype.val) (g := E.s) hins
  -- Step 3: approximate every parameter into the dense localization image
  have hdense : DenseRange (⇑(D.coeRingHom)) := fun y =>
    @UniformSpace.Completion.denseRange_coe _ D.uniformSpace y
  have hcoset : ∀ x : presheafValue D, ∃ l : Localization.Away D.s,
      ∃ b ∈ ((presheafValue D)⁺ : Subring (presheafValue D)),
        D.coeRingHom l = x + (u : presheafValue D) ^ (M + 1) * b := by
    intro x
    obtain ⟨u', hu'⟩ := (hu_unit.pow (M + 1)).exists_left_inv
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
  choose lf bf hbf hlf using fun i : ↥E.T => hcoset i.val
  obtain ⟨lg, bg, hbg, hlg⟩ := hcoset E.s
  -- Step 4: perturbation does not change the subset
  have hpert : indexedRationalSet (presheafValue D) E.T.attach Subtype.val E.s =
      indexedRationalSet (presheafValue D) E.T.attach
        (fun i => D.coeRingHom (lf i)) (D.coeRingHom lg) :=
    indexedRationalSet_perturb_eq hu_unit hu hM
      (fun i _ => ⟨bf i, hbf i, hlf i⟩) ⟨bg, hbg, hlg⟩
  have hbase : rationalOpen E.T E.s =
      indexedRationalSet (presheafValue D) E.T.attach Subtype.val E.s := by
    rw [indexedRationalSet_eq_rationalOpen, Finset.attach_image_val]
    exact (Set.inter_eq_left.mpr rationalOpen_subset_spa).symm
  -- Step 5: clear localization denominators
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples
    (Submonoid.powers D.s) (insert none (E.T.attach.image some))
    (fun o : Option ↥E.T => o.elim lg lf)
  have hbg' : IsLocalization.IsInteger A ((b : A) • lg) :=
    hb none (Finset.mem_insert_self _ _)
  have hbf' : ∀ i : ↥E.T, ∃ a : A,
      algebraMap A (Localization.Away D.s) a = (b : A) • lf i := fun i =>
    hb (some i) (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem some (Finset.mem_attach _ i)))
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
  have hparam : ∀ i : ↥E.T, D.canonicalMap (hA i) = U * D.coeRingHom (lf i) := by
    intro i
    have hstep := congrArg D.coeRingHom (hhA i)
    rw [Algebra.smul_def, map_mul] at hstep
    exact hstep
  have hset' : indexedRationalSet (presheafValue D) E.T.attach
      (fun i => D.canonicalMap (hA i)) (D.canonicalMap q) =
      indexedRationalSet (presheafValue D) E.T.attach
        (fun i => D.coeRingHom (lf i)) (D.coeRingHom lg) := by
    have hstep : indexedRationalSet (presheafValue D) E.T.attach
        (fun i => D.canonicalMap (hA i)) (D.canonicalMap q) =
        indexedRationalSet (presheafValue D) E.T.attach
          (fun i => U * D.coeRingHom (lf i)) (U * D.coeRingHom lg) := by
      ext v
      simp only [indexedRationalSet, Set.mem_setOf_eq]
      refine and_congr_right fun hv => ?_
      rw [hqparam]
      constructor
      · rintro ⟨hT, h0⟩
        exact ⟨fun i hi => by rw [← hparam i]; exact hT i hi, h0⟩
      · rintro ⟨hT, h0⟩
        exact ⟨fun i hi => by rw [hparam i]; exact hT i hi, h0⟩
    rw [hstep, indexedRationalSet_unit_mul_eq hU_unit]
  have hchain : rationalOpen E.T E.s =
      indexedRationalSet (presheafValue D) E.T.attach
        (fun i => D.canonicalMap (hA i)) (D.canonicalMap q) :=
    (hbase.trans hpert).trans hset'.symm
  -- Steps 6–8: a topologically nilpotent unit power dominated by the
  -- denominator on the compact upstairs subset
  obtain ⟨π, hπ⟩ := IsTateRing.exists_topologicallyNilpotent_unit (A := A)
  have hK : IsCompact (spaOpen E) := isCompact_spaOpen E hE
  have hq0 : ∀ w ∈ spaOpen E,
      ¬ (w.1 : Spv (presheafValue D)).vle (D.canonicalMap q) 0 := by
    intro w hw
    have hwE : (w.1 : Spv (presheafValue D)) ∈ rationalOpen E.T E.s := hw
    rw [hchain] at hwE
    exact hwE.2.2
  have hπtn : IsTopologicallyNilpotent (D.canonicalMap (π : A)) :=
    hπ.map (canonicalMap_continuous D)
  obtain ⟨N, hN⟩ := exists_uniform_pow_vle_on_compact hK hπtn hq0
  -- Steps 9–11: pad the downstairs family with the unit power
  have hspanW : Ideal.span ((insert ((π : A) ^ N) (E.T.attach.image hA) :
      Finset A) : Set A) = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _
      (Ideal.subset_span (Finset.mem_insert_self _ _)) (π.isUnit.pow N)
  refine ⟨genPieceDatum D.P (insert ((π : A) ^ N) (E.T.attach.image hA)) q hspanW,
    RationalLocData.isRational_of_span_eq_top hspanW, ?_⟩
  ext w
  constructor
  · intro hw
    have hw' := hw
    rw [hchain] at hw'
    obtain ⟨hspa, hT, h0⟩ := hw'
    refine ⟨hspa, fun t' ht' => ?_, ?_⟩
    · have ht'' : t' ∈ (insert ((π : A) ^ N) (E.T.attach.image hA)).image
          D.canonicalMap := ht'
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp ht''
      show (w.vle (D.canonicalMap t) (D.canonicalMap q))
      rcases Finset.mem_insert.mp ht with rfl | ht₀
      · -- the padded unit power: uniform domination on the compact subset
        have hwK : (⟨w, hspa⟩ : ↥(Spa (presheafValue D) (presheafValue D)⁺)) ∈
            spaOpen E := hw
        have := hN _ hwK
        rwa [← map_pow] at this
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht₀
        exact hT i (Finset.mem_attach _ i)
    · exact h0
  · intro hw
    obtain ⟨hspa, hT, h0⟩ := hw
    rw [hchain]
    refine ⟨hspa, fun i _ => ?_, ?_⟩
    · exact hT (D.canonicalMap (hA i))
        (show D.canonicalMap (hA i) ∈ (imgDatum D (genPieceDatum D.P
            (insert ((π : A) ^ N) (E.T.attach.image hA)) q hspanW) hspanW).T from
          Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem
            (Finset.mem_image_of_mem hA (Finset.mem_attach _ i))))
    · exact h0

/-! ### The comap image of an image-datum open -/

omit [T2Space A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- The `comap`-image of an image-datum rational open is the **intersection with
the base**: `R(D) ∩ R(W)` (Wedhorn 8.2(2): the image is `U ∩ W`, not `W`). -/
theorem comap_image_imgDatum_rationalOpen (D : RationalLocData A)
    (W : RationalLocData A) (hspanW : Ideal.span (W.T : Set A) = ⊤) :
    comap D.canonicalMap ''
        rationalOpen (imgDatum D W hspanW).T (imgDatum D W hspanW).s =
      rationalOpen D.T D.s ∩ rationalOpen W.T W.s := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hspa, hcomap⟩ := (imgDatum_mem_rationalOpen_iff D W hspanW w).mp hw
    exact ⟨(comap_canonicalMap_mem_rationalOpen_inter_spa D ⟨w, hspa⟩).1, hcomap⟩
  · rintro ⟨hvD, hvW⟩
    obtain ⟨w, hwspa, hwcomap⟩ := exists_spa_presheafValue_of_rationalOpen D hvD
    exact ⟨w, (imgDatum_mem_rationalOpen_iff D W hspanW w).mpr
      ⟨hwspa, by rw [hwcomap]; exact hvW⟩, hwcomap⟩

omit [T2Space A] [IsRingOfIntegralElements (A⁺ : Subring A)]
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] in
/-- The backward carrier, presentation-free: the set of upstairs Spa-points
whose pull-back lies in a downstairs set `V`, at `V = R(W)`, is exactly the
image-datum rational open. -/
theorem setOf_comap_mem_eq_imgDatum_rationalOpen (D : RationalLocData A)
    (W : RationalLocData A) (hspanW : Ideal.span (W.T : Set A) = ⊤) :
    {w : Spv (presheafValue D) |
        w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
          comap D.canonicalMap w ∈ rationalOpen W.T W.s} =
      rationalOpen (imgDatum D W hspanW).T (imgDatum D W hspanW).s :=
  Set.ext fun w => (imgDatum_mem_rationalOpen_iff D W hspanW w).symm

/-! ### The rational-subset correspondence -/

section Correspondence

variable (D : RationalLocData A) (hD : D.IsRational)

omit [T2Space A] [NonarchimedeanRing A] 
  [letI : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A; CompleteSpace A] [IsRingOfIntegralElements (A⁺ : Subring A)] in
/-- Forward carrier lands inside the base rational subset. -/
private theorem forward_subset (V : RationalSubset (presheafValue D)) :
    comap D.canonicalMap '' V.1 ⊆ rationalOpen D.T D.s := by
  rintro _ ⟨w, hw, rfl⟩
  have hspa : w ∈ Spa (presheafValue D) (presheafValue D)⁺ :=
    V.2.hasRationalPresentation.subset_spa hw
  exact (comap_canonicalMap_mem_rationalOpen_inter_spa D ⟨w, hspa⟩).1

include hD in
/-- The forward carrier is a rational subset of `A` — packaged as
`R(D) ∩ R(W) = R(interRational D W)` via the hard direction. -/
private theorem forward_rational (V : RationalSubset (presheafValue D)) :
    IsRationalSubset (comap D.canonicalMap '' V.1) := by
  haveI hTateB : IsTateRing (presheafValue D) := presheafValue_isTateRing_concrete D
  obtain ⟨T, s, hopen, hpres⟩ := V.2
  have hspanT : Ideal.span (T : Set (presheafValue D)) = ⊤ :=
    span_eq_top_of_isOpen_span hopen
  have hEup : (genPieceDatum (presheafValue_concretePair D) T s hspanT).IsRational :=
    RationalLocData.isRational_of_span_eq_top hspanT
  obtain ⟨W, hW, hWeq⟩ := exists_downstairs_rationalDatum D hD
    (genPieceDatum (presheafValue_concretePair D) T s hspanT) hEup
  have hV1 : V.1 = rationalOpen (imgDatum D W hW.span_eq_top).T
      (imgDatum D W hW.span_eq_top).s := by
    rw [hpres]
    exact hWeq
  rw [hV1, comap_image_imgDatum_rationalOpen D W hW.span_eq_top,
    ← RationalLocData.interRational_rationalOpen D W hD hW]
  exact RationalLocData.isRationalSubset_rationalOpen
    (RationalLocData.interRational_isRational D W hD hW)

/-- The backward carrier is a rational subset of the completed localization —
realized by the image datum. -/
private theorem backward_rational
    (V : {V : RationalSubset A // V.1 ⊆ rationalOpen D.T D.s}) :
    IsRationalSubset {w : Spv (presheafValue D) |
      w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
        comap D.canonicalMap w ∈ (V : RationalSubset A).1} := by
  obtain ⟨T, s, hopen, hpres⟩ := (V : RationalSubset A).2
  have hspanT : Ideal.span (T : Set A) = ⊤ := span_eq_top_of_isOpen_span hopen
  have hcarrier : {w : Spv (presheafValue D) |
      w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
        comap D.canonicalMap w ∈ (V : RationalSubset A).1} =
      rationalOpen (imgDatum D (genPieceDatum D.P T s hspanT) hspanT).T
        (imgDatum D (genPieceDatum D.P T s hspanT) hspanT).s := by
    rw [hpres]
    exact setOf_comap_mem_eq_imgDatum_rationalOpen D
      (genPieceDatum D.P T s hspanT) hspanT
  rw [hcarrier]
  exact RationalLocData.isRationalSubset_rationalOpen
    (imgDatum_isRational D (genPieceDatum D.P T s hspanT) hspanT)

/-- **Wedhorn Proposition 8.2(2), rational-subset bijection (complete-Tate
specialization)**: the valid rational subsets of `Spa A⟨T/s⟩` correspond
bijectively to the valid rational subsets of `Spa (A, A⁺)` contained in
`R(T/s)`. The forward carrier is the `comap`-image (Wedhorn's `U ∩ W`,
realized by `interRational`); the backward carrier is the homeomorphic
preimage, realized by the image datum. -/
def spaPresheafValueRationalSubsetEquiv :
    RationalSubset (presheafValue D) ≃
      {V : RationalSubset A // V.1 ⊆ rationalOpen D.T D.s} where
  toFun V := ⟨⟨comap D.canonicalMap '' V.1, forward_rational D hD V⟩,
    forward_subset D V⟩
  invFun V := ⟨{w : Spv (presheafValue D) |
      w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
        comap D.canonicalMap w ∈ (V : RationalSubset A).1},
    backward_rational D V⟩
  left_inv V := by
    refine Subtype.ext ?_
    show {w : Spv (presheafValue D) |
        w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
          comap D.canonicalMap w ∈ comap D.canonicalMap '' V.1} = V.1
    ext w
    constructor
    · rintro ⟨hspa, w', hw', hcomap⟩
      have hw'spa : w' ∈ Spa (presheafValue D) (presheafValue D)⁺ :=
        V.2.hasRationalPresentation.subset_spa hw'
      have hww' : w' = w :=
        comap_canonicalMap_injOn_spa D hw'spa hspa hcomap
      rwa [← hww']
    · intro hw
      exact ⟨V.2.hasRationalPresentation.subset_spa hw, ⟨w, hw, rfl⟩⟩
  right_inv V := by
    refine Subtype.ext (Subtype.ext ?_)
    show comap D.canonicalMap '' {w : Spv (presheafValue D) |
        w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
          comap D.canonicalMap w ∈ (V : RationalSubset A).1} =
      (V : RationalSubset A).1
    ext v
    constructor
    · rintro ⟨w, ⟨hspa, hcomap⟩, rfl⟩
      exact hcomap
    · intro hv
      obtain ⟨w, hwspa, hwcomap⟩ := exists_spa_presheafValue_of_rationalOpen D
        (V.2 hv)
      exact ⟨w, ⟨hwspa, by rw [hwcomap]; exact hv⟩, hwcomap⟩

/-- The forward carrier of the correspondence (simp interface). -/
@[simp] theorem spaPresheafValueRationalSubsetEquiv_apply_coe
    (V : RationalSubset (presheafValue D)) :
    ((spaPresheafValueRationalSubsetEquiv D hD V).1).1 =
      comap D.canonicalMap '' V.1 := rfl

/-- The backward carrier of the correspondence (simp interface). -/
@[simp] theorem spaPresheafValueRationalSubsetEquiv_symm_apply_coe
    (V : {V : RationalSubset A // V.1 ⊆ rationalOpen D.T D.s}) :
    ((spaPresheafValueRationalSubsetEquiv D hD).symm V).1 =
      {w : Spv (presheafValue D) |
        w ∈ Spa (presheafValue D) (presheafValue D)⁺ ∧
          comap D.canonicalMap w ∈ (V : RationalSubset A).1} := rfl

end Correspondence

end ValuationSpectrum
