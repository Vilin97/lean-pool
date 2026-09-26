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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AnalyticPoints
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicSpectrum
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.Lemma745
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.StructureSheaf

/-!
# Adic Morphisms

We prove Lemma 7.46 and develop the theory of adic morphisms,
following §7.5 and §8.4 of [Wedhorn, *Adic Spaces*].

## Main results

* `ValuationSpectrum.supp_comap` : `supp(comap φ v) = φ⁻¹(supp v)`.
* `ValuationSpectrum.nonAnalytic_comap_of_continuous` : Continuous maps preserve non-analytic
  points (Lemma 7.46(1), first part).
* `ValuationSpectrum.analytic_comap_of_isAdicHom` : Adic homomorphisms preserve analytic
  points (Lemma 7.46(1), second part).
* `ValuationSpectrum.isAdicHom_of_complete_and_analytic_preserved` : If `B` is complete and
  `Spa(φ)` preserves analytic points, then `φ` is adic (Lemma 7.46(2)).
* `ValuationSpectrum.PresentationIsAdicMorphism` (in `AdicSpaceMorphisms.lean`) :
  PROVISIONAL predicate on carrier *presentations* — NOT Definition 8.38 (see its
  docstring; presentations are not objects of Wedhorn's `𝒱`, and the public name
  `IsAdicMorphism` stays reserved for the eventual `𝒱`-level predicate).
* `ValuationSpectrum.isAdicHom_iff_preserves_analytic` : A ring hom is adic iff it
  preserves analytic points on Spa (Proposition 8.39(1), affinoid iff version).
* `ValuationSpectrum.morphism_preserves_nonAnalytic_affinoid` : Any continuous ring hom
  preserves non-analytic points (Proposition 8.39(2), affinoid case).

## References

* [T. Wedhorn, *Adic Spaces*][wedhorn2019adic], §7.5, §8.4
-/

@[expose] public section

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` equals the preimage ideal `φ⁻¹(supp v)`. -/
theorem supp_comap (φ : A →+* B) (v : Spv B) :
    (comap φ v).supp = Ideal.comap φ v.supp := by
  simpa using congr_arg PrimeSpectrum.asIdeal (suppFun_comap φ v)

omit [TopologicalSpace A] [TopologicalSpace B] in
/-- The support of `comap φ v` as a set equals `φ ⁻¹' (supp v : Set B)`. -/
theorem supp_comap_coe (φ : A →+* B) (v : Spv B) :
    ((comap φ v).supp : Set A) = φ ⁻¹' (v.supp : Set B) := by
  ext x; simp only [Set.mem_preimage, SetLike.mem_coe, Ideal.mem_comap, supp_comap]

/-- **Lemma 7.46(1), first part.** Continuous ring homomorphisms preserve non-analytic points. -/
theorem nonAnalytic_comap_of_continuous {φ : A →+* B} (hφ : Continuous φ)
    {v : Spv B} (hv : ¬IsAnalytic v) : ¬IsAnalytic (comap φ v) := by
  simp only [IsAnalytic, not_not] at hv ⊢
  rw [supp_comap_coe]
  exact hφ.isOpen_preimage _ hv

section AdicPreservesAnalytic

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

omit [IsHuberRing B] in
/-- If `supp(v)` contains the ideal of definition, then `supp(v)` is open. -/
private theorem supp_isOpen_of_idealOfDefinition_le (PB : PairOfDefinition B) (v : Spv B)
    (h : PB.idealOfDefinition ≤ v.supp) : IsOpen (v.supp : Set B) := by
  change IsOpen (v.supp.toAddSubgroup : Set B)
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset
      ((PB.pow_image_isOpen 1).mem_nhds
        (Set.mem_image_of_mem _ (PB.I ^ 1).zero_mem))
      (fun b hb ↦ by
        rw [Submodule.coe_toAddSubgroup]
        obtain ⟨y, hy, rfl⟩ := hb
        exact h (Ideal.mem_map_of_mem _ (pow_one PB.I ▸ hy))))

omit [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B] in
/-- If `I` maps into `supp(comap φ v)` and `φ` is adic, then `PB.idealOfDefinition ≤ supp v`. -/
private theorem idealOfDefinition_le_supp_of_adic (PA : PairOfDefinition A)
    (PB : PairOfDefinition B) (φ : A →+* B) (hAB : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (hrad : (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical = PB.I.radical)
    (v : Spv B) (hI : PA.idealOfDefinition ≤ (comap φ v).supp) :
    PB.idealOfDefinition ≤ v.supp := by
  have hI_comap : PA.I ≤ Ideal.comap PA.A₀.subtype (comap φ v).supp := by
    rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap] at hI
  have hmap_le : Ideal.map (PA.restrictRingHom PB φ hAB) PA.I ≤
      Ideal.comap PB.A₀.subtype v.supp := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have ha' : (PA.A₀.subtype a : A) ∈ (comap φ v).supp := hI_comap ha
    rw [supp_comap] at ha'
    exact ha'
  have hJ_le : PB.I ≤ Ideal.comap PB.A₀.subtype v.supp := by
    calc PB.I ≤ PB.I.radical := Ideal.le_radical
    _ = (Ideal.map (PA.restrictRingHom PB φ hAB) PA.I).radical := hrad.symm
    _ ≤ (Ideal.comap PB.A₀.subtype v.supp).radical := Ideal.radical_mono hmap_le
    _ = Ideal.comap PB.A₀.subtype v.supp :=
        (Ideal.IsPrime.comap PB.A₀.subtype).radical
  rwa [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]

omit [IsTopologicalRing A] in
/-- **Lemma 7.46(1), second part.** Adic homomorphisms preserve analytic points. -/
theorem analytic_comap_of_isAdicHom {φ : A →+* B} (hφ : IsAdicHom φ) {v : Spv B}
    (hv : IsAnalytic v) : IsAnalytic (comap φ v) := by
  intro hna
  apply hv; clear hv
  obtain ⟨PA, PB, hAB, hrad⟩ := hφ
  have hI_le : PA.idealOfDefinition ≤ (comap φ v).supp := by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ (instIsPrimeSupp (comap φ v)).radical.le
      ((PA.isTopologicallyNilpotent_of_mem ha).mem_ideal_radical hna)
  exact supp_isOpen_of_idealOfDefinition_le PB v
    (idealOfDefinition_le_supp_of_adic PA PB φ hAB hrad v hI_le)

end AdicPreservesAnalytic

section TateSpecialization

variable [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

omit [IsTopologicalRing A] in
/-- In a Tate source ring, adic homomorphisms produce analytic comap points. -/
theorem analytic_comap_of_isAdicHom_tate [IsTateRing B] {φ : A →+* B} (hφ : IsAdicHom φ)
    (v : Spv B) : IsAnalytic (comap φ v) :=
  analytic_comap_of_isAdicHom hφ (IsTateRing.isAnalytic v)

end TateSpecialization

section Lemma746Converse

variable {A B : Type*} [CommRing A] [CommRing B]
  [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B]

omit [IsTopologicalRing A] [IsHuberRing A] in
/-- The closure of `I^(2m)` under `PA.A₀.subtype` lies in `Subring.closure S`
where `S` is the image of `I^m`. Used to show `A₀'` is open. -/
private theorem pow_2m_image_sub_closure (PA : PairOfDefinition A) {m : ℕ} {S : Set A}
    (hS : S = PA.A₀.subtype '' ((PA.I ^ m : Ideal PA.A₀) : Set PA.A₀)) :
    PA.A₀.subtype '' ((PA.I ^ (2 * m) : Ideal PA.A₀) : Set PA.A₀) ⊆
        (Subring.closure S : Set A) := by
  set A₀' := Subring.closure S
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ PA.I ^ m * PA.I ^ m := by
    rwa [← pow_add, ← two_mul]
  refine Submodule.mul_induction_on hx'
    (fun a ha b hb ↦ ?_) (fun _ _ h1 h2 ↦ A₀'.add_mem h1 h2)
  change PA.A₀.subtype (a * b) ∈ A₀'
  rw [map_mul]
  exact A₀'.mul_mem
    (Subring.subset_closure (hS ▸ ⟨a, ha, rfl⟩))
    (Subring.subset_closure (hS ▸ ⟨b, hb, rfl⟩))

omit [IsHuberRing A] in
/-- Each I' power is open in A₀', using `comap_le_pow`. -/
private theorem isAdic_pow_open (PA : PairOfDefinition A) {m : ℕ} {A₀' : Subring A}
    (hA₀'_le_PA : A₀' ≤ PA.A₀) {I' : Ideal A₀'}
    (comap_le_pow : ∀ n, Ideal.comap (Subring.inclusion hA₀'_le_PA)
      (PA.I ^ ((n + 2) * m)) ≤ I' ^ n)
    (n : ℕ) : IsOpen ((I' ^ n).toAddSubgroup : Set A₀') := by
  set ι := Subring.inclusion hA₀'_le_PA
  set k := (n + 2) * m
  have hW_open : IsOpen ((fun x : A₀' ↦ (x : A)) ⁻¹'
      (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀))) :=
    (PA.pow_image_isOpen k).preimage continuous_subtype_val
  have hW_zero : (0 : A₀') ∈ (fun x : A₀' ↦ (x : A)) ⁻¹'
      (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀)) :=
    ⟨0, (PA.I ^ k).zero_mem,
      by simp only [ZeroMemClass.coe_zero, map_zero]⟩
  have hW_sub : (fun x : A₀' ↦ (x : A)) ⁻¹'
      (PA.A₀.subtype '' ((PA.I ^ k : Ideal PA.A₀) : Set PA.A₀)) ⊆
      ((I' ^ n : Ideal A₀') : Set A₀') := by
    intro x ⟨y, hy, hval⟩
    apply comap_le_pow n
    change ι x ∈ PA.I ^ ((n + 2) * m)
    exact (Subtype.ext
      (by simp only [ι, Subring.inclusion]; exact hval.symm) :
        ι x = y) ▸ hy
  exact AddSubgroup.isOpen_of_mem_nhds _
    (Filter.mem_of_superset (hW_open.mem_nhds hW_zero)
      (Submodule.coe_toAddSubgroup (I' ^ n) ▸ hW_sub))

omit [IsHuberRing A] in
/-- The I'-adic topology on A₀' is finer than the subspace topology. -/
private theorem isAdic_topology_finer (PA : PairOfDefinition A) {m : ℕ} (hm_pos : m > 0)
    {A₀' : Subring A} (hA₀'_le_PA : A₀' ≤ PA.A₀) {I' : Ideal A₀'}
    (hI'_le_comap : I' ≤ Ideal.comap (Subring.inclusion hA₀'_le_PA) (PA.I ^ m))
    (s : Set A₀') (hs : s ∈ nhds (0 : A₀')) : ∃ n, ∀ x ∈ I' ^ n, x ∈ s := by
  set ι := Subring.inclusion hA₀'_le_PA
  have hI'_pow_le :
      ∀ n, I' ^ n ≤ Ideal.comap ι (PA.I ^ (m * n)) := by
    intro n
    calc I' ^ n
        ≤ (Ideal.comap ι (PA.I ^ m)) ^ n := pow_le_pow_left' hI'_le_comap n
      _ ≤ Ideal.comap ι ((PA.I ^ m) ^ n) := Ideal.le_comap_pow ι n
      _ = Ideal.comap ι (PA.I ^ (m * n)) := by rw [← pow_mul]
  rw [nhds_induced, Filter.mem_comap] at hs
  obtain ⟨V, hV, hV_sub⟩ := hs
  obtain ⟨j, -, hj⟩ := PA.hasBasis_nhds_zero.mem_iff.mp hV
  refine ⟨j, fun x hx ↦ hV_sub (show (x : A) ∈ V from hj ?_)⟩
  have hιx : ι x ∈ PA.I ^ (m * j) := hI'_pow_le j hx
  have hmj_le : PA.I ^ (m * j) ≤ PA.I ^ j :=
    Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left j hm_pos)
  exact ⟨ι x, hmj_le hιx, rfl⟩

omit [IsHuberRing A] in
/-- **Every open subring contains a ring of definition** (Wedhorn Rem 6.2-style): given
any pair of definition and an open subring `U`, some pair of definition has `A₀ ≤ U`
(take the subring closure of the image of a high power `I^m ⊆ U`). -/
theorem exists_pairOfDefinition_le_subring (PA : PairOfDefinition A) {U : Subring A}
    (hU : IsOpen (U : Set A)) :
    ∃ (PA' : PairOfDefinition A), PA'.A₀ ≤ U := by
  obtain ⟨m, -, hm⟩ := PA.hasBasis_nhds_zero.mem_iff.mp (hU.mem_nhds (U.zero_mem))
  rcases Nat.eq_zero_or_pos m with rfl | hm_pos
  · have : PA.A₀ ≤ U := by
      intro a ha
      exact hm (Set.mem_image_of_mem PA.A₀.subtype
        (by simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top] :
          (⟨a, ha⟩ : PA.A₀) ∈ (PA.I ^ 0 : Ideal PA.A₀)))
    exact ⟨PA, this⟩
  set S := PA.A₀.subtype '' ((PA.I ^ m : Ideal PA.A₀) : Set PA.A₀) with S_def
  set A₀' := Subring.closure S with A₀'_def
  have hA₀'_le_U : A₀' ≤ U := Subring.closure_le.mpr hm
  have hA₀'_le_PA : A₀' ≤ PA.A₀ :=
    Subring.closure_le.mpr
      (Set.image_subset_iff.mpr fun _ _ ↦ Subtype.coe_prop _)
  have hA₀'_open : IsOpen (A₀' : Set A) := by
    change IsOpen (A₀'.toAddSubgroup : Set A)
    exact AddSubgroup.isOpen_of_mem_nhds _
      (Filter.mem_of_superset
        ((PA.pow_image_isOpen (2 * m)).mem_nhds
          (Set.mem_image_of_mem _ (PA.I ^ (2 * m)).zero_mem))
        (pow_2m_image_sub_closure PA S_def))
  set ι := Subring.inclusion hA₀'_le_PA with ι_def
  have hlift : ∀ x ∈ PA.I ^ m, (PA.A₀.subtype x : A) ∈ A₀' :=
    fun x hx ↦ Subring.subset_closure ⟨x, hx, rfl⟩
  obtain ⟨F, hF⟩ := PA.fg.pow (n := m)
  have hF_sub : ∀ g ∈ F, (PA.A₀.subtype g : A) ∈ A₀' :=
    fun g hg ↦
      hlift g (hF ▸ Ideal.subset_span (Finset.mem_coe.mpr hg))
  classical
  set F' : Finset A₀' :=
    F.attach.image (fun g ↦ ⟨PA.A₀.subtype g.1, hF_sub g.1 g.2⟩)
  set I' := Ideal.span (F' : Set A₀') with I'_def
  have hι_gen : ∀ g' ∈ F', ι g' ∈ PA.I ^ m := by
    intro g' hg'
    simp only [F', Finset.mem_image, Finset.mem_attach,
      true_and] at hg'
    obtain ⟨⟨g, hg_mem⟩, rfl⟩ := hg'
    have : ι ⟨PA.A₀.subtype g, hF_sub g hg_mem⟩ = g :=
      Subtype.ext rfl
    rw [this]
    exact hF ▸ Ideal.subset_span (Finset.mem_coe.mpr hg_mem)
  have hI'_le_comap : I' ≤ Ideal.comap ι (PA.I ^ m) :=
    Ideal.span_le.mpr hι_gen
  have comap_le_pow :
      ∀ n, Ideal.comap ι (PA.I ^ ((n + 2) * m)) ≤ I' ^ n := by
    intro n
    induction n with
    | zero =>
      intro x _
      change x ∈ (I' ^ 0 : Ideal ↥A₀')
      simp only [pow_zero, Ideal.one_eq_top, Submodule.mem_top]
    | succ n ih =>
      intro x hx
      change x ∈ I' ^ (n + 1)
      have hιx : ι x ∈ PA.I ^ m * PA.I ^ ((n + 2) * m) := by
        rw [← pow_add, show m + (n + 2) * m = (n + 3) * m by ring]
        exact hx
      suffices h_suff :
          ∀ z ∈ PA.I ^ m * PA.I ^ ((n + 2) * m),
          (PA.A₀.subtype z : A) ∈ A₀' ∧
          ∀ (h' : (PA.A₀.subtype z : A) ∈ A₀'),
          (⟨PA.A₀.subtype z, h'⟩ : A₀') ∈
            (I' ^ (n + 1) : Ideal A₀') by
        have hx_eq :
            x = ⟨PA.A₀.subtype (ι x), x.2⟩ := by
          ext; rfl
        rw [hx_eq]; exact (h_suff (ι x) hιx).2 x.2
      intro z hz
      refine Submodule.mul_induction_on hz
        (fun g hg w hw ↦ ?_) (fun u v hu hv ↦ ?_)
      · suffices h_span :
            ∀ (g' : PA.A₀),
            g' ∈ Ideal.span (F : Set PA.A₀) →
            ∀ (w' : PA.A₀),
            w' ∈ PA.I ^ ((n + 2) * m) →
            (PA.A₀.subtype (g' * w') : A) ∈ A₀' ∧
            ∀ (h' : (PA.A₀.subtype (g' * w') : A) ∈ A₀'),
            (⟨PA.A₀.subtype (g' * w'), h'⟩ : A₀') ∈
              (I' ^ (n + 1) : Ideal A₀') by
          exact h_span g (hF ▸ hg) w hw
        intro g' hg'
        induction hg' using Submodule.span_induction with
        | mem f hf =>
          intro w' hw'
          have hf'_mem :
              (⟨PA.A₀.subtype f, hF_sub f hf⟩ : A₀') ∈ I' :=
            Ideal.subset_span (Finset.mem_image.mpr
              ⟨⟨f, hf⟩, Finset.mem_attach _ _, rfl⟩)
          have hw'_A₀' : (PA.A₀.subtype w' : A) ∈ A₀' :=
            hlift w' (Ideal.pow_le_pow_right
              (Nat.le_mul_of_pos_left m (by omega)) hw')
          have hfw'_A₀' :
              (PA.A₀.subtype (f * w') : A) ∈ A₀' := by
            rw [map_mul]
            exact A₀'.mul_mem (hF_sub f hf) hw'_A₀'
          refine ⟨hfw'_A₀', fun h' ↦ ?_⟩
          have hw'_In :
              (⟨PA.A₀.subtype w', hw'_A₀'⟩ : A₀') ∈
                (I' ^ n : Ideal A₀') := by
            apply ih
            change ι ⟨_, hw'_A₀'⟩ ∈ PA.I ^ ((n + 2) * m)
            rw [show (ι ⟨PA.A₀.subtype w', hw'_A₀'⟩ :
                PA.A₀) = w' from Subtype.ext rfl]
            exact hw'
          have : (⟨PA.A₀.subtype (f * w'), h'⟩ : A₀') =
              ⟨PA.A₀.subtype f, hF_sub f hf⟩ *
              ⟨PA.A₀.subtype w', hw'_A₀'⟩ :=
            Subtype.ext (map_mul PA.A₀.subtype f w')
          rw [this, pow_succ']
          exact Ideal.mul_mem_mul hf'_mem hw'_In
        | zero =>
          intro w' _
          exact ⟨by simp only [zero_mul, map_zero]; exact A₀'.zero_mem,
            fun h' ↦ by
              have : (⟨PA.A₀.subtype (0 * w'), h'⟩ : A₀') = 0 :=
                Subtype.ext (by simp only [zero_mul, map_zero,
                  ZeroMemClass.coe_zero])
              rw [this]; exact (I' ^ (n + 1)).zero_mem⟩
        | add x' y' _ _ hx'_ih hy'_ih =>
          intro w' hw'
          obtain ⟨hx'w'_A₀', hx'_res⟩ := hx'_ih w' hw'
          obtain ⟨hy'w'_A₀', hy'_res⟩ := hy'_ih w' hw'
          have hadd :
              (PA.A₀.subtype ((x' + y') * w') : A) ∈
                A₀' := by
            rw [add_mul, map_add]
            exact A₀'.add_mem hx'w'_A₀' hy'w'_A₀'
          refine ⟨hadd, fun h' ↦ ?_⟩
          have : (⟨PA.A₀.subtype ((x' + y') * w'),
              h'⟩ : A₀') =
              ⟨PA.A₀.subtype (x' * w'), hx'w'_A₀'⟩ +
              ⟨PA.A₀.subtype (y' * w'), hy'w'_A₀'⟩ :=
            Subtype.ext (by
              simp only [add_mul, map_add,
                AddMemClass.coe_add])
          rw [this]
          exact (I' ^ (n + 1)).add_mem
            (hx'_res hx'w'_A₀') (hy'_res hy'w'_A₀')
        | smul c x' _ hx'_ih =>
          intro w' hw'
          have hcw'_mem :
              c * w' ∈ PA.I ^ ((n + 2) * m) :=
            Ideal.mul_mem_left _ c hw'
          obtain ⟨hx'cw'_A₀', hx'_res⟩ :=
            hx'_ih (c * w') hcw'_mem
          constructor
          · change (PA.A₀.subtype (c • x' * w') :
                A) ∈ A₀'
            rw [show (c • x' * w' : PA.A₀) =
                x' * (c * w') from Subtype.ext (by
              simp only [smul_eq_mul, Subring.coe_mul]
              ring)]
            exact hx'cw'_A₀'
          · intro h'
            have : (⟨PA.A₀.subtype (c • x' * w'),
                h'⟩ : A₀') =
                ⟨PA.A₀.subtype (x' * (c * w')),
                  hx'cw'_A₀'⟩ :=
              Subtype.ext (by
                simp only [smul_eq_mul, map_mul]
                ring)
            rw [this]; exact hx'_res hx'cw'_A₀'
      · obtain ⟨hu_A₀', hu_res⟩ := hu
        obtain ⟨hv_A₀', hv_res⟩ := hv
        refine ⟨by rw [map_add]; exact A₀'.add_mem hu_A₀' hv_A₀',
          fun h' ↦ ?_⟩
        have : (⟨PA.A₀.subtype (u + v), h'⟩ : A₀') =
            ⟨PA.A₀.subtype u, hu_A₀'⟩ +
            ⟨PA.A₀.subtype v, hv_A₀'⟩ :=
          Subtype.ext (map_add PA.A₀.subtype u v)
        rw [this]
        exact (I' ^ (n + 1)).add_mem
          (hu_res hu_A₀') (hv_res hv_A₀')
  have hI'_isAdic : IsAdic I' := by
    rw [isAdic_iff]
    exact ⟨fun n ↦ isAdic_pow_open PA hA₀'_le_PA comap_le_pow n,
      fun s hs ↦ isAdic_topology_finer PA hm_pos hA₀'_le_PA
        hI'_le_comap s hs⟩
  exact ⟨⟨A₀', I', hA₀'_open, ⟨F', rfl⟩, hI'_isAdic⟩, hA₀'_le_U⟩


omit [IsTopologicalRing A] [IsHuberRing A] in
/-- **Principal pair inside an open subring** (Tate case): combine
`exists_pairOfDefinition_le_subring` with `PairOfDefinition.exists_principal_same_A₀`.
Discharges the `A₀ ≤ A⁺` hypothesis of the Spa quasi-compactness route whenever `A⁺`
is open (e.g. a ring of integral elements / `CompatiblePlusSubring`). -/
theorem IsTateRing.exists_principal_pairOfDefinition_le_subring
    [IsTateRing A] {U : Subring A} (hU : IsOpen (U : Set A)) :
    ∃ (P : PairOfDefinition A) (π : P.A₀),
      P.A₀ ≤ U ∧ P.I = Ideal.span {π} ∧ IsUnit ((π : A)) := by
  obtain ⟨P₀⟩ := (‹IsTateRing A›.toIsHuberRing).exists_pairOfDefinition
  obtain ⟨P₁, hP₁le⟩ := exists_pairOfDefinition_le_subring P₀ hU
  obtain ⟨P, π, hA₀eq, hπ, hunit⟩ := P₁.exists_principal_same_A₀
  refine ⟨P, π, ?_, hπ, hunit⟩
  rw [hA₀eq]
  exact hP₁le

omit [IsTopologicalRing B] [IsHuberRing B] in
private theorem exists_compatible_pair
    {φ : A →+* B} (hφ : Continuous φ) (PB : PairOfDefinition B) :
    ∃ (PA : PairOfDefinition A), ∀ a ∈ PA.A₀, φ a ∈ PB.A₀ := by
  obtain ⟨PA'⟩ := ‹IsHuberRing A›.exists_pairOfDefinition
  have hpreimg_open : IsOpen (φ ⁻¹' (PB.A₀ : Set B)) := PB.isOpen.preimage hφ
  set U : Subring A := PA'.A₀ ⊓ (PB.A₀.comap φ) with U_def
  have hU_open : IsOpen (U : Set A) := PA'.isOpen.inter hpreimg_open
  have hU_le : U ≤ PA'.A₀ := inf_le_left
  obtain ⟨PA, hPA_le⟩ := exists_pairOfDefinition_le_subring PA' hU_open
  exact ⟨PA, fun a ha ↦ (hPA_le ha).2⟩

omit [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B] in
private theorem exists_separating_prime_of_B₀ {φ : A →+* B} (PA : PairOfDefinition A)
    (PB : PairOfDefinition B) (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical) :
    ∃ (𝔭₀ : Ideal PB.A₀), 𝔭₀.IsPrime ∧
      Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀ ∧ ¬PB.I ≤ 𝔭₀ := by
  obtain ⟨j, hj_radJ, hj_not_radI⟩ :=
    Set.exists_of_ssubset
      (show (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical <
        PB.I.radical from lt_of_le_of_ne h_le h_not_eq)
  set img := Ideal.map (PA.restrictRingHom PB φ h_map) PA.I
  have hj_not_all :
      ¬(∀ (𝔭 : Ideal PB.A₀), (img ≤ 𝔭 ∧ 𝔭.IsPrime) → j ∈ 𝔭) := by
    intro hall
    exact hj_not_radI (Ideal.radical_eq_sInf img ▸ Ideal.mem_sInf.mpr hall)
  push Not at hj_not_all
  obtain ⟨𝔭₀, ⟨h_image_le, h𝔭₀_prime⟩, hj_not_p⟩ := hj_not_all
  refine ⟨𝔭₀, h𝔭₀_prime, h_image_le, fun hJ_le ↦ hj_not_p ?_⟩
  exact h𝔭₀_prime.radical.symm ▸ Ideal.radical_mono hJ_le hj_radJ

omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
/-- Span induction for the prime extension argument: for each element
`b` in `span(subtype '' 𝔭₀)`, there exist `n` and `c ∈ 𝔭₀` with
`subtype c = (subtype j)^n * b`. -/
private theorem span_pow_mul_eq_of_prime (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    {𝔭₀ : Ideal PB.A₀} {j : PB.A₀}
    (hj_nil : IsTopologicallyNilpotent (PB.A₀.subtype j : B))
    (b : B) (hb : b ∈ Ideal.span (PB.A₀.subtype '' (𝔭₀ : Set PB.A₀))) :
    ∃ (n : ℕ) (c : PB.A₀), c ∈ 𝔭₀ ∧
      PB.A₀.subtype c = (PB.A₀.subtype j) ^ n * b := by
  induction hb using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨a, ha_mem, ha_eq⟩ := hb
    exact ⟨0, a, ha_mem, by rw [pow_zero, one_mul, ha_eq]⟩
  | zero =>
    exact ⟨0, 0, 𝔭₀.zero_mem,
      by simp only [map_zero, pow_zero, one_mul]⟩
  | add b₁ b₂ _ _ ih₁ ih₂ =>
    obtain ⟨n₁, c₁, hc₁_mem, hc₁_eq⟩ := ih₁
    obtain ⟨n₂, c₂, hc₂_mem, hc₂_eq⟩ := ih₂
    refine ⟨n₁ ⊔ n₂,
      j ^ (n₁ ⊔ n₂ - n₁) * c₁ + j ^ (n₁ ⊔ n₂ - n₂) * c₂,
      𝔭₀.add_mem (𝔭₀.mul_mem_left _ hc₁_mem)
        (𝔭₀.mul_mem_left _ hc₂_mem), ?_⟩
    simp only [map_add, map_mul, map_pow, mul_add]
    congr 1
    · calc (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁) * (PB.A₀.subtype c₁)
          = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁) *
              ((PB.A₀.subtype j) ^ n₁ * b₁) := by rw [hc₁_eq]
        _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₁ + n₁) * b₁ := by
            rw [pow_add, mul_assoc]
        _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₁ := by
            rw [Nat.sub_add_cancel (Nat.le_max_left n₁ n₂)]
    · calc (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂) * (PB.A₀.subtype c₂)
          = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂) *
              ((PB.A₀.subtype j) ^ n₂ * b₂) := by rw [hc₂_eq]
        _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂ - n₂ + n₂) * b₂ := by
            rw [pow_add, mul_assoc]
        _ = (PB.A₀.subtype j) ^ (n₁ ⊔ n₂) * b₂ := by
            rw [Nat.sub_add_cancel (Nat.le_max_right n₁ n₂)]
  | smul r b _ ih =>
    obtain ⟨n₀, c₀, hc₀_mem, hc₀_eq⟩ := ih
    obtain ⟨m, hm⟩ := PB.exists_pow_mul_mem_A₀ hj_nil r
    set r' : PB.A₀ := ⟨(PB.A₀.subtype j) ^ m * r, hm⟩
    refine ⟨m + n₀, r' * c₀, 𝔭₀.mul_mem_left _ hc₀_mem, ?_⟩
    have h_lhs : PB.A₀.subtype (r' * c₀) =
        ((PB.A₀.subtype j) ^ m * r) *
          ((PB.A₀.subtype j) ^ n₀ * b) := by
      rw [map_mul, hc₀_eq]; rfl
    rw [h_lhs, smul_eq_mul, pow_add, mul_assoc, mul_assoc,
      mul_left_comm r ((PB.A₀.subtype j) ^ n₀) b]

omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
/-- The comap of the mapped prime ideal is contained in the original
prime, using the span induction and primality. -/
private theorem comap_map_subtype_le_of_prime (PB : PairOfDefinition B)
    [IsAdicComplete PB.I PB.A₀] {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime] {j : PB.A₀}
    (hj_mem : j ∈ PB.I) (hj_not : j ∉ 𝔭₀) :
    (Ideal.map PB.A₀.subtype 𝔭₀).comap PB.A₀.subtype ≤ 𝔭₀ := by
  have hj_nil : IsTopologicallyNilpotent (PB.A₀.subtype j : B) :=
    PB.isTopologicallyNilpotent_of_mem hj_mem
  intro x hx
  simp only [Ideal.mem_comap] at hx
  obtain ⟨n, c, hc_mem, hc_eq⟩ :=
    span_pow_mul_eq_of_prime PB hj_nil (PB.A₀.subtype x) hx
  have hc_eq' : c = j ^ n * x := Subtype.val_injective (by
    simp only [Subring.coe_mul, SubmonoidClass.coe_pow]
    exact hc_eq)
  rw [hc_eq'] at hc_mem
  rcases (‹𝔭₀.IsPrime›).mem_or_mem hc_mem with hjn | hx_in
  · exact absurd (‹𝔭₀.IsPrime›.mem_of_pow_mem n hjn) hj_not
  · exact hx_in

omit [TopologicalSpace A] [TopologicalSpace B]
  [IsTopologicalRing A] [IsTopologicalRing B]
  [IsHuberRing A] [IsHuberRing B] in
/-- Powers of `j` outside `𝔭₀` map to the prime complement image. -/
private theorem powers_sub_primeCompl_map {B₀ : Subring B} {𝔭₀ : Ideal B₀}
    [𝔭₀.IsPrime] {j : B₀} (hj_not : j ∉ 𝔭₀) :
    (Submonoid.powers (B₀.subtype j) : Set B) ⊆
    (𝔭₀.primeCompl.map B₀.subtype : Set B) := by
  rintro _ ⟨n, rfl⟩
  refine ⟨j ^ n, ?_, map_pow B₀.subtype j n⟩
  change j ^ n ∉ 𝔭₀
  intro h
  rcases n.eq_zero_or_pos with rfl | hn
  · exact (Ideal.IsPrime.ne_top ‹_›)
      ((Ideal.eq_top_iff_one 𝔭₀).mpr (pow_zero j ▸ h))
  · exact hj_not
      ((_root_.Ideal.IsPrime.pow_mem_iff_mem ‹_› n hn).mp h)

omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
private theorem exists_nonOpen_prime_of_B_from_B₀_prime (PB : PairOfDefinition B)
    [IsAdicComplete PB.I PB.A₀] {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime]
    (hJ_not_le : ¬PB.I ≤ 𝔭₀) :
    ∃ (𝔭 : Ideal B), 𝔭.IsPrime ∧ ¬IsOpen (𝔭 : Set B) ∧
      𝔭₀ ≤ Ideal.comap PB.A₀.subtype 𝔭 := by
  obtain ⟨j, hj_mem, hj_not⟩ := SetLike.not_le_iff_exists.mp hJ_not_le
  have h_disj : Disjoint (Ideal.map PB.A₀.subtype 𝔭₀ : Set B)
      (Submonoid.powers (PB.A₀.subtype j)) :=
    (Ideal.disjoint_map_primeCompl_iff_comap_le.mpr
      (comap_map_subtype_le_of_prime PB hj_mem hj_not)).mono_right
      (powers_sub_primeCompl_map hj_not)
  obtain ⟨𝔭, h𝔭_prime, h𝔭_le, h𝔭_disj⟩ :=
    (Ideal.map PB.A₀.subtype 𝔭₀).exists_le_prime_disjoint
      (Submonoid.powers (PB.A₀.subtype j)) h_disj
  refine ⟨𝔭, h𝔭_prime, ?_, ?_⟩
  · intro h_open
    have hj_in_𝔭 : (PB.A₀.subtype j : B) ∈ 𝔭 := by
      have h𝔭_mem_nhds : (𝔭 : Set B) ∈ nhds 0 :=
        h_open.mem_nhds 𝔭.zero_mem
      obtain ⟨n, hn⟩ :=
        (Filter.Tendsto.eventually
          (PB.isTopologicallyNilpotent_of_mem hj_mem)
          h𝔭_mem_nhds).exists
      exact h𝔭_prime.mem_of_pow_mem n hn
    exact Set.disjoint_left.mp h𝔭_disj hj_in_𝔭
      (Submonoid.mem_powers _)
  · exact Ideal.le_comap_of_map_le h𝔭_le

omit [IsTopologicalRing A] [IsHuberRing A] [IsHuberRing B] in
private theorem spa_point_from_nonOpen_prime [PlusSubring B] (PB : PairOfDefinition B)
    [IsAdicComplete PB.I PB.A₀] {𝔭 : Ideal B} [𝔭.IsPrime]
    (h𝔭 : ¬IsOpen (𝔭 : Set B)) (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ 𝔭 ≤ v.supp := by
  obtain ⟨v, hv_spa, hv_supp, hv_idealOfDef⟩ :=
    PB.exists_mem_spa_supp_ge_of_nonOpen_prime h𝔭 hBplus_le_B₀
  refine ⟨v, hv_spa, ?_, hv_supp⟩
  intro h_open
  exact hv_idealOfDef (by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap]
    exact fun a ha ↦ (instIsPrimeSupp v).radical.le
      ((PB.isTopologicallyNilpotent_of_mem ha).mem_ideal_radical h_open))

omit [IsHuberRing A] [IsHuberRing B] in
private theorem exists_analytic_spa_point_from_B₀_prime [PlusSubring B] {φ : A →+* B}
    (PA : PairOfDefinition A) (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀) {𝔭₀ : Ideal PB.A₀} [𝔭₀.IsPrime]
    (h_image_le : Ideal.map (PA.restrictRingHom PB φ h_map) PA.I ≤ 𝔭₀)
    (hJ_not_le : ¬PB.I ≤ 𝔭₀) (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  obtain ⟨𝔭, h𝔭_prime, h𝔭_notopen, h𝔭₀_le⟩ :=
    exists_nonOpen_prime_of_B_from_B₀_prime PB hJ_not_le
  have := h𝔭_prime
  obtain ⟨v, hv_spa, hv_an, hv_supp⟩ :=
    spa_point_from_nonOpen_prime PB h𝔭_notopen hBplus_le_B₀
  refine ⟨v, hv_spa, hv_an, ?_⟩
  have h_idealOfDef_le : PA.idealOfDefinition ≤ (comap φ v).supp := by
    rw [PairOfDefinition.idealOfDefinition, Ideal.map_le_iff_le_comap, supp_comap]
    intro a ha
    have h1 : PA.restrictRingHom PB φ h_map a ∈ 𝔭₀ :=
      h_image_le (Ideal.mem_map_of_mem _ ha)
    have h2 : (PB.A₀.subtype (PA.restrictRingHom PB φ h_map a) : B) ∈ 𝔭 :=
      h𝔭₀_le h1
    have h3 : PB.A₀.subtype (PA.restrictRingHom PB φ h_map a) =
        φ (PA.A₀.subtype a) := rfl
    exact hv_supp (h3 ▸ h2)
  exact PA.isOpen_of_idealOfDefinition_le h_idealOfDef_le

omit [IsHuberRing A] [IsHuberRing B] in
private theorem exists_analytic_spa_point_with_open_comap_supp [PlusSubring B]
    {φ : A →+* B} (_hφ : Continuous φ) (PA : PairOfDefinition A) (PB : PairOfDefinition B)
    [IsAdicComplete PB.I PB.A₀] (h_map : ∀ a ∈ PA.A₀, φ a ∈ PB.A₀)
    (h_not_eq : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠ PB.I.radical)
    (h_le : (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤ PB.I.radical)
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) :
    ∃ v ∈ Spa B B⁺, IsAnalytic v ∧ IsOpen ((comap φ v).supp : Set A) := by
  obtain ⟨𝔭₀, h𝔭₀_prime, h_image_le, hJ_not_le⟩ :=
    exists_separating_prime_of_B₀ PA PB h_map h_not_eq h_le
  have := h𝔭₀_prime
  exact exists_analytic_spa_point_from_B₀_prime
    PA PB h_map h_image_le hJ_not_le hBplus_le_B₀

/-- **Lemma 7.46(2) of Wedhorn.** If `Spa(φ)` preserves analytic points and `B` is
complete, then `φ` is adic. -/
theorem isAdicHom_of_complete_and_analytic_preserved [PlusSubring A] [PlusSubring B]
    {φ : A →+* B} (hφ : Continuous φ) (_hAB : A⁺ ≤ (B⁺).comap φ)
    (h_analytic : ∀ v ∈ Spa B B⁺, IsAnalytic v → IsAnalytic (comap φ v))
    (PB : PairOfDefinition B) [IsAdicComplete PB.I PB.A₀]
    (hBplus_le_B₀ : (B⁺ : Set B) ⊆ PB.A₀) : IsAdicHom φ := by
  obtain ⟨PA, h_map⟩ := exists_compatible_pair hφ PB
  by_contra h_not_adic
  have h_ne :
      (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≠
        PB.I.radical :=
    fun h_eq ↦ h_not_adic ⟨PA, PB, h_map, h_eq⟩
  have h_le :
      (Ideal.map (PA.restrictRingHom PB φ h_map) PA.I).radical ≤
        PB.I.radical := by
    rw [Ideal.radical_le_radical_iff, Ideal.map_le_iff_le_comap]
    intro a ha
    have h_nil : IsTopologicallyNilpotent (φ (PA.A₀.subtype a)) :=
      (PA.isTopologicallyNilpotent_of_mem ha).map hφ
    have h_mem : φ (PA.A₀.subtype a) ∈ PB.A₀ := h_map _ a.2
    obtain ⟨N, hN⟩ := PB.exists_pow_mem_I h_mem h_nil
    change PA.restrictRingHom PB φ h_map a ∈ PB.I.radical
    exact Ideal.mem_radical_iff.mpr ⟨N, hN⟩
  obtain ⟨v, hv_spa, hv_an, hv_open⟩ :=
    exists_analytic_spa_point_with_open_comap_supp
      hφ PA PB h_map h_ne h_le hBplus_le_B₀
  exact (h_analytic v hv_spa hv_an) hv_open

end Lemma746Converse


-- Space-level adic morphisms (Definition 8.38, Prop 8.39, Cor 8.40) live in
-- `AdicSpaceMorphisms.lean`; the module `AdicMorphisms` is the AGGREGATOR importing
-- both, so `import «Adic spaces».AdicMorphisms` exposes the full API (P6, 2026-07-20).


end ValuationSpectrum
