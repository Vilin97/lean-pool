/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.Symmetrization
import LeanPool.FormalLearningTheory.Complexity.Generalization
import LeanPool.FormalLearningTheory.PureMath.FiniteVCApprox
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Map

/-!
# Finite-Support VC Approximation via Symmetrization

For finite `H`, we embed into `H ⊕ ℕ` (which is Infinite) and push the FinitePMF
forward along `Sum.inl`. This forces the growth-function path in the symmetrization
proof, giving a sample bound depending only on d and ε, not on |H| or |A|.
-/

open Finset MeasureTheory
noncomputable section
universe u

/-! ## PMF Bridge -/

private noncomputable def FinitePMF.toPMF {H : Type*} [Fintype H] (μ : FinitePMF H) : PMF H :=
  PMF.ofFintype (fun h => ENNReal.ofReal (μ.prob h)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun h _ => μ.prob_nonneg h)]
    simpa using congrArg ENNReal.ofReal μ.prob_sum_one)

/-! ## Infinite Envelope: H ⊕ ℕ -/

private def extendBool {H : Type*} (a : H → Bool) : H ⊕ ℕ → Bool
  | Sum.inl h => a h
  | Sum.inr _ => false

private def liftClass {H : Type*} (A : Finset (H → Bool)) :
    ConceptClass (H ⊕ ℕ) Bool :=
  { h | ∃ a ∈ A, h = extendBool a }

/-! ## Boolean Expectation Bridges -/
private lemma trueErrorReal_extend_false
    {H : Type*} [Fintype H]
    [MeasurableSpace H] [MeasurableSingletonClass H]
    (μ : FinitePMF H) (a : H → Bool) :
    @TrueErrorReal (H ⊕ ℕ) ⊤ (extendBool a) (fun _ => false)
      (@PMF.toMeasure (H ⊕ ℕ) ⊤ (μ.toPMF.map Sum.inl))
      = boolTestExpectation μ a := by
  unfold TrueErrorReal TrueError
  let S := {x : H ⊕ ℕ | extendBool a x ≠ false}
  -- Key: under ⊤, toMeasure = toOuterMeasure for any PMF
  have hto : @PMF.toMeasure (H ⊕ ℕ) ⊤ (μ.toPMF.map Sum.inl) S =
      (μ.toPMF.map Sum.inl).toOuterMeasure S := by
    letI : MeasurableSpace (H ⊕ ℕ) := ⊤
    exact @PMF.toMeasure_apply_eq_toOuterMeasure (H ⊕ ℕ) ⊤ (μ.toPMF.map Sum.inl)
      ⟨fun _ => trivial⟩ S
  change (@PMF.toMeasure (H ⊕ ℕ) ⊤ (μ.toPMF.map Sum.inl) S).toReal = _
  rw [hto, PMF.toOuterMeasure_map_apply]
  -- Preimage computation
  have hpre : Sum.inl ⁻¹' S = {h : H | a h ≠ false} := by
    ext h; simp [S, extendBool]
  rw [hpre]
  -- Back to toMeasure on H, then expand via fintype
  rw [show μ.toPMF.toOuterMeasure {h : H | a h ≠ false} =
    μ.toPMF.toMeasure {h : H | a h ≠ false} from
      (PMF.toMeasure_apply_eq_toOuterMeasure _ _).symm]
  rw [PMF.toMeasure_apply_fintype]
  -- Convert ENNReal sum to Real sum
  have hne_top : ∀ h ∈ Finset.univ, Set.indicator {h : H | a h ≠ false} (⇑μ.toPMF) h ≠ ⊤ := by
    intro h _; simp only [Set.indicator_apply, Set.mem_setOf_eq]
    split_ifs
    · show μ.toPMF h ≠ ⊤
      simp [FinitePMF.toPMF, PMF.ofFintype_apply, ENNReal.ofReal_ne_top]
    · exact ENNReal.zero_ne_top
  rw [ENNReal.toReal_sum hne_top]
  -- Simplify each term and match boolTestExpectation
  simp only [boolTestExpectation, trueExpectation]
  congr 1; ext h
  simp only [Set.indicator_apply, Set.mem_setOf_eq, FinitePMF.toPMF, PMF.ofFintype_apply]
  by_cases hah : a h = true
  · simp [hah, ENNReal.toReal_ofReal (μ.prob_nonneg h)]
  · have haf : a h = false := Bool.eq_false_iff.mpr fun htrue => hah htrue
    simp [haf]

private theorem liftClass_growth_bound
    {H : Type*} [Fintype H] [DecidableEq H] [Nonempty H] (A : Finset (H → Bool))
    {d v : ℕ} (hv : v = d + 1) (hvc : A.boolVCDim ≤ d) :
    ∀ n : ℕ, v ≤ n →
      GrowthFunction (H ⊕ ℕ) (liftClass A) n ≤
        ∑ i ∈ Finset.range (v + 1), Nat.choose n i := by
  classical
  intro n hn
  let X := H ⊕ ℕ
  let C : ConceptClass X Bool := liftClass A
  change GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), n.choose i
  have hvcdim_le : VCDim X C ≤ (d : WithTop ℕ) := by
    apply iSup₂_le; intro S hS
    have hno_inr : ∀ x ∈ S, ∃ h : H, x = Sum.inl h := by
      intro x hx; cases x with
      | inl h => exact ⟨h, rfl⟩
      | inr k =>
        obtain ⟨c, hcC, hcf⟩ := hS (fun _ => true)
        have := hcf ⟨Sum.inr k, hx⟩
        obtain ⟨a, _, rfl⟩ := hcC; simp [extendBool] at this
    let getH : (x : H ⊕ ℕ) → x ∈ S → H := fun x hx => (hno_inr x hx).choose
    let SH : Finset H := S.image (fun x => if hx : x ∈ S then getH x hx
      else Classical.arbitrary H)
    have hSH_card : SH.card = S.card := by
      apply Finset.card_image_of_injOn
      intro x₁ hx₁ x₂ hx₂ heq
      simp only [show (x₁ ∈ S) = True from propext ⟨fun _ => trivial, fun _ => hx₁⟩,
        show (x₂ ∈ S) = True from propext ⟨fun _ => trivial, fun _ => hx₂⟩,
        dite_true] at heq
      calc x₁ = Sum.inl (getH x₁ hx₁) := (hno_inr x₁ hx₁).choose_spec
        _ = Sum.inl (getH x₂ hx₂) := congrArg Sum.inl heq
        _ = x₂ := ((hno_inr x₂ hx₂).choose_spec).symm
    have hSH_shat : (boolFamilyToFinsetFamily A).Shatters SH := by
      intro t ht
      let f : ↥S → Bool := fun ⟨x, hx⟩ => decide (getH x hx ∈ t)
      obtain ⟨c, hcC, hcf⟩ := hS f
      obtain ⟨a, haA, rfl⟩ := hcC
      refine ⟨Finset.univ.filter (fun h => a h = true),
        Finset.mem_image.mpr ⟨a, haA, rfl⟩, ?_⟩
      ext h; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro ⟨hh_SH, hah⟩
        obtain ⟨x, hxS, hxH⟩ := Finset.mem_image.mp hh_SH
        simp only [dif_pos hxS] at hxH
        have hx_eq := (hno_inr x hxS).choose_spec
        have hab : a (getH x hxS) = decide (getH x hxS ∈ t) := by
          have h1 := hcf ⟨x, hxS⟩
          have h2 : extendBool a x = a (getH x hxS) := by
            conv_lhs => rw [hx_eq]; simp only [extendBool]
          rw [h2] at h1; exact h1
        rw [hxH] at hab
        rw [hab, decide_eq_true_eq] at hah; exact hah
      · intro hht
        refine ⟨ht hht, ?_⟩
        obtain ⟨x, hxS, hxH⟩ := Finset.mem_image.mp (ht hht)
        simp only [dif_pos hxS] at hxH
        have hx_eq := (hno_inr x hxS).choose_spec
        have hab : a (getH x hxS) = decide (getH x hxS ∈ t) := by
          have h1 := hcf ⟨x, hxS⟩
          have h2 : extendBool a x = a (getH x hxS) := by
            conv_lhs => rw [hx_eq]; simp only [extendBool]
          rw [h2] at h1; exact h1
        rw [hxH] at hab
        rw [hab]; exact decide_eq_true hht
    calc (S.card : WithTop ℕ) = ↑SH.card := by rw [hSH_card]
      _ ≤ ↑(A.boolVCDim) := WithTop.coe_le_coe.mpr hSH_shat.card_le_vcDim
      _ ≤ ↑d := by exact_mod_cast hvc
  unfold GrowthFunction
  apply csSup_le'
  rintro k ⟨⟨S, hSn⟩, rfl⟩
  change { f : ↥S → Bool | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }.ncard ≤
    ∑ i ∈ Finset.range (v + 1), n.choose i
  haveI : DecidableEq X := Classical.decEq X
  set RS : Set (↥S → Bool) := { f | ∃ c ∈ C, ∀ x : ↥S, c ↑x = f x }
  have hRS_fin : Set.Finite RS := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  set RS_fs := hRS_fin.toFinset
  rw [Set.ncard_eq_toFinset_card RS hRS_fin]
  haveI : DecidableEq ↥S := Classical.typeDecidableEq _
  haveI : DecidableEq (Finset ↥S) := Classical.typeDecidableEq _
  let toSub : (↥S → Bool) → Finset ↥S :=
    fun f => Finset.univ.filter (fun x => f x = true)
  have h_inj : Function.Injective toSub := by
    intro f g hfg; funext x
    have := Finset.ext_iff.mp hfg x
    simp only [toSub, Finset.mem_filter, Finset.mem_univ, true_and] at this
    cases hf : f x <;> cases hg : g x <;> simp_all
  set 𝒜 := RS_fs.image toSub
  have h1 : RS_fs.card = 𝒜.card := (Finset.card_image_of_injective _ h_inj).symm
  have h_vcdim_le : 𝒜.vcDim ≤ d := by
    simp only [Finset.vcDim]
    apply Finset.sup_le; intro T hT_mem
    have hT_shat : 𝒜.Shatters T := Finset.mem_shatterer.mp hT_mem
    suffices hT_lift : Shatters X C (T.map ⟨Subtype.val, Subtype.val_injective⟩) by
      have : ((T.map ⟨Subtype.val, Subtype.val_injective⟩).card : WithTop ℕ) ≤ ↑d :=
        le_trans (le_iSup₂_of_le _ hT_lift le_rfl) hvcdim_le
      rw [Finset.card_map] at this; exact_mod_cast this
    intro f
    let fb : ↥S → Bool := fun y =>
      if hy : y ∈ T then f ⟨↑y, Finset.mem_map.mpr ⟨y, hy, rfl⟩⟩ else false
    let t : Finset ↥S := T.filter (fun y => fb y = true)
    have ht_sub : t ⊆ T := Finset.filter_subset _ _
    obtain ⟨A_set, hA_mem, hTA⟩ := hT_shat ht_sub
    obtain ⟨g, hg_fs, hg_eq⟩ := Finset.mem_image.mp hA_mem
    obtain ⟨c, hcC, hcg⟩ := hRS_fin.mem_toFinset.mp hg_fs
    refine ⟨c, hcC, fun ⟨x, hx_mem⟩ => ?_⟩
    obtain ⟨y, hyT, rfl⟩ := Finset.mem_map.mp hx_mem
    have hcgy : c ↑y = g y := hcg y
    have hy_in_A : y ∈ A_set ↔ g y = true := by subst hg_eq; simp [toSub, Finset.mem_filter]
    have hy_in_t : y ∈ t ↔ fb y = true := by
      simp [t, Finset.mem_filter, hyT]
    have key : g y = fb y := by
      have hy_inter : y ∈ T ∩ A_set ↔ y ∈ t :=
        ⟨fun h => (Finset.ext_iff.mp hTA y).mp h, fun h => (Finset.ext_iff.mp hTA y).mpr h⟩
      cases hgy : g y <;> cases hfby : fb y
      · rfl
      · exact absurd (hy_in_A.mp (Finset.mem_inter.mp (hy_inter.mpr (hy_in_t.mpr hfby))).2)
          (by simp [hgy])
      · exact absurd (hy_in_t.mp (hy_inter.mp (Finset.mem_inter.mpr ⟨hyT, hy_in_A.mpr hgy⟩)))
          (by simp [hfby])
      · rfl
    change c ↑y = f ⟨↑y, hx_mem⟩
    rw [hcgy, key]; simp only [fb, dif_pos hyT]
  calc RS_fs.card
      = 𝒜.card := h1
    _ ≤ 𝒜.shatterer.card := Finset.card_le_card_shatterer 𝒜
    _ ≤ ∑ k ∈ Finset.Iic 𝒜.vcDim, (Fintype.card ↥S).choose k :=
        Finset.card_shatterer_le_sum_vcDim
    _ = ∑ k ∈ Finset.Iic 𝒜.vcDim, S.card.choose k := by rw [Fintype.card_coe]
    _ ≤ ∑ k ∈ Finset.Iic d, S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Iic_subset_Iic.mpr h_vcdim_le
    _ ≤ ∑ k ∈ Finset.range (v + 1), S.card.choose k := by
        apply Finset.sum_le_sum_of_subset
        intro x; simp [Finset.mem_Iic, Finset.mem_range, hv]; omega
    _ = ∑ k ∈ Finset.range (v + 1), n.choose k := by rw [hSn]

/-! ## Main Theorem -/
/-- Finite-support distributions uniformly approximate any distribution on a VC class.
For a class of VC dimension at most `d` and any `ε > 0`, there exists
`T = T(d, ε)` such that every finitely supported distribution `μ` is within `ε`
(uniformly over the class) of some empirical distribution on `T` points. A
density-style reduction that lets the approximate minimax / MWU machinery, which lives
in finite support, apply to general distributions. -/
theorem finite_support_vc_approx
    (d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (T : ℕ) (hT : 0 < T),
      ∀ {H : Type*} [Fintype H] [DecidableEq H]
        (A : Finset (H → Bool)),
        A.boolVCDim ≤ d →
        ∀ μ : FinitePMF H, ∃ hs : Fin T → H,
          ∀ a ∈ A,
            |boolTestExpectation μ a -
              boolTestExpectation (empiricalPMF hT hs) a| ≤ ε := by
  classical
  by_cases hbig : 1 ≤ ε
  · refine ⟨1, Nat.one_pos, ?_⟩
    intro H _ _ A hvc μ
    haveI : Nonempty H := by
      by_contra hemp; rw [not_nonempty_iff] at hemp
      have := μ.prob_sum_one; simp [Finset.eq_empty_of_isEmpty] at this
    refine ⟨fun _ => Classical.arbitrary H, ?_⟩
    intro a ha
    have h1 := boolTestExpectation_le_one μ a
    have h0 := boolTestExpectation_nonneg μ a
    have h3 := boolTestExpectation_le_one
      (empiricalPMF Nat.one_pos (fun _ => Classical.arbitrary H)) a
    have h4 := boolTestExpectation_nonneg
      (empiricalPMF Nat.one_pos (fun _ => Classical.arbitrary H)) a
    rw [abs_le]; constructor <;> linarith
  · push Not at hbig
    let v : ℕ := d + 1
    let δ : ℝ := 1 / 2
    let Tnat : ℕ := max 1 (Nat.ceil ((16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ))
    have hTpos : 0 < Tnat := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left 1 _)
    refine ⟨Tnat, hTpos, ?_⟩
    intro H _ _ A hvc μ
    haveI : Nonempty H := by
      by_contra hemp; rw [not_nonempty_iff] at hemp
      have := μ.prob_sum_one; simp [Finset.eq_empty_of_isEmpty] at this
    letI : MeasurableSpace (H ⊕ ℕ) := ⊤
    haveI : MeasurableSingletonClass (H ⊕ ℕ) := ⟨fun _ => trivial⟩
    haveI : Infinite (H ⊕ ℕ) := Sum.infinite_of_right
    letI : MeasurableSpace H := ⊤
    haveI : MeasurableSingletonClass H := ⟨fun _ => trivial⟩
    let X := H ⊕ ℕ
    let C : ConceptClass X Bool := liftClass A
    let D : Measure X := @PMF.toMeasure X ⊤ (μ.toPMF.map Sum.inl)
    haveI : IsProbabilityMeasure D := PMF.toMeasure.isProbabilityMeasure _
    have hgrowth : ∀ n : ℕ, v ≤ n →
        GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i :=
      liftClass_growth_bound (A := A) (v := v) rfl hvc
    -- Under ⊤ MeasurableSpace on X, every function from X is measurable
    have hmeas_C : ∀ f ∈ C, @Measurable X Bool ⊤ _ f :=
      fun _ _ _ _ => @MeasurableSpace.measurableSet_top X _
    have hc_meas : @Measurable X Bool ⊤ _ (fun _ => false) :=
      fun _ _ => @MeasurableSpace.measurableSet_top X _
    -- NullMeasurableSet: under ⊤, discrete measurability gives all sets measurable
    haveI : Countable X := inferInstance
    haveI : DiscreteMeasurableSpace X :=
      MeasurableSingletonClass.toDiscreteMeasurableSpace
    have hnull : NullMeasurableSet
        {p : (Fin Tnat → X) × (Fin Tnat → X) | ∃ f ∈ C,
          EmpiricalError X Bool f (fun i => (p.2 i, (fun _ => false) (p.2 i)))
            (zeroOneLoss Bool) -
          EmpiricalError X Bool f (fun i => (p.1 i, (fun _ => false) (p.1 i)))
            (zeroOneLoss Bool) ≥ ε / 2}
        ((Measure.pi (fun _ : Fin Tnat => D)).prod (Measure.pi (fun _ : Fin Tnat => D))) :=
      MeasurableSet.nullMeasurableSet (DiscreteMeasurableSpace.forall_measurableSet _)
    have hTlarge : (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ ≤ (Tnat : ℝ) := by
      calc (16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ
          ≤ ↑(Nat.ceil ((16 * Real.exp 1 * (↑v + 1) / ε ^ 2) ^ (v + 1) / δ)) :=
            Nat.le_ceil _
        _ ≤ (Tnat : ℝ) := by
            apply Nat.cast_le.mpr
            exact Nat.le_max_right 1 _
    have hbound := growth_exp_le_delta C v (by omega : 0 < v) Tnat hTpos ε δ
      hε (by norm_num : (0 : ℝ) < δ) (by norm_num : δ < 1) hgrowth hTlarge
    obtain ⟨hGF, hLarge⟩ := hbound
    have hsym := symmetrization_uc_bound D C (fun _ => false)
      hmeas_C hc_meas Tnat hTpos ε hε hLarge hnull
    let bad : Set (Fin Tnat → X) :=
      { xs | ∃ f ∈ C,
          |TrueErrorReal X f (fun _ => false) D -
            EmpiricalError X Bool f (fun i => (xs i, (fun _ => false) (xs i)))
              (zeroOneLoss Bool)| ≥ ε }
    have hbad_le : Measure.pi (fun _ : Fin Tnat => D) bad ≤ ENNReal.ofReal δ := by
      calc Measure.pi (fun _ => D) bad
          ≤ ENNReal.ofReal (4 * ↑(GrowthFunction X C (2 * Tnat)) *
              Real.exp (-(↑Tnat * ε ^ 2 / 8))) := hsym
        _ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal hGF
    -- Sub-step 1: Complement positivity
    -- μ_pi(bad) ≤ ofReal(1 / 2) < 1 = μ_pi(univ), so badᶜ has positive measure.
    have hbad_lt_one : Measure.pi (fun _ : Fin Tnat => D) bad < 1 := by
      calc Measure.pi (fun _ => D) bad ≤ ENNReal.ofReal δ := hbad_le
        _ < 1 := by simp only [δ]; rw [ENNReal.ofReal_lt_one]; norm_num
    have hcompl_pos : 0 < Measure.pi (fun _ : Fin Tnat => D) badᶜ := by
      have hfin : Measure.pi (fun _ : Fin Tnat => D) bad ≠ ⊤ :=
        ne_top_of_le_ne_top (by simp [measure_univ]) (measure_mono (Set.subset_univ _))
      have h1 := MeasureTheory.measure_compl
        (DiscreteMeasurableSpace.forall_measurableSet _) hfin
      rw [measure_univ] at h1; rw [h1]
      exact tsub_pos_of_lt hbad_lt_one
    -- Sub-step 2: Witness extraction with all-Sum.inl guarantee
    -- D = PMF.toMeasure (μ.toPMF.map Sum.inl) is supported on range Sum.inl.
    -- So the product measure is supported on {xs | ∀ i, xs i ∈ range Sum.inl}.
    let allInl : Set (Fin Tnat → X) := {xs | ∀ i, xs i ∈ Set.range Sum.inl}
    let p : PMF X := μ.toPMF.map Sum.inl
    have hD_eq : D = @PMF.toMeasure X ⊤ p := rfl
    have hp_supp : p.support ⊆ Set.range Sum.inl := by
      intro x hx; rw [PMF.mem_support_iff] at hx
      change x ∈ Set.range Sum.inl
      by_contra habs
      apply hx
      change (μ.toPMF.map Sum.inl) x = 0
      rw [PMF.map_apply]
      apply ENNReal.tsum_eq_zero.mpr; intro h
      -- goal: (if x = Sum.inl h then μ.toPMF h else 0) = 0
      split_ifs with heq
      · exact absurd ⟨h, heq.symm⟩ habs
      · rfl
    have hD_inl : D (Set.range Sum.inl)ᶜ = 0 := by
      rw [hD_eq, @PMF.toMeasure_apply_eq_toOuterMeasure X ⊤ p ⟨fun _ => trivial⟩]
      rw [PMF.toOuterMeasure_apply]
      apply ENNReal.tsum_eq_zero.mpr; intro x
      by_cases hx : x ∈ (Set.range (Sum.inl : H → X))ᶜ
      · -- x ∉ range Sum.inl, so x ∉ p.support, so p x = 0
        simp only [Set.indicator_apply, hx, ↓reduceIte]
        have : x ∉ p.support := fun h => hx (hp_supp h)
        rwa [PMF.mem_support_iff, not_not] at this
      · simp only [Set.indicator_apply, hx, ↓reduceIte]
    have hallInl_compl_zero : Measure.pi (fun _ : Fin Tnat => D) allInlᶜ = 0 := by
      have hsub : allInlᶜ ⊆ ⋃ i : Fin Tnat, {xs | xs i ∉ Set.range Sum.inl} := by
        intro xs hxs
        simp only [allInl, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hxs
        obtain ⟨i, hi⟩ := hxs
        exact Set.mem_iUnion.mpr ⟨i, hi⟩
      have hzero : ∀ i : Fin Tnat,
          Measure.pi (fun _ => D) {xs | xs i ∉ Set.range Sum.inl} = 0 := by
        intro i
        have heq : {xs : Fin Tnat → X | xs i ∉ Set.range Sum.inl} =
            Function.eval i ⁻¹' (Set.range Sum.inl)ᶜ := by ext; simp [Function.eval]
        rw [heq, ← Set.univ_pi_update_univ, MeasureTheory.Measure.pi_pi]
        apply Finset.prod_eq_zero (Finset.mem_univ i)
        simp [hD_inl]
      have hle : Measure.pi (fun _ => D) allInlᶜ ≤ 0 :=
        calc Measure.pi (fun _ => D) allInlᶜ
            ≤ Measure.pi (fun _ => D) (⋃ i, {xs | xs i ∉ Set.range Sum.inl}) :=
              MeasureTheory.measure_mono hsub
          _ ≤ ∑' i, Measure.pi (fun _ => D) {xs | xs i ∉ Set.range Sum.inl} :=
              MeasureTheory.measure_iUnion_le _
          _ = 0 := ENNReal.tsum_eq_zero.mpr hzero
      exact le_antisymm hle (zero_le _)
    have hinter_pos : 0 < Measure.pi (fun _ => D) (badᶜ ∩ allInl) := by
      by_contra h; push Not at h
      have h0 := le_antisymm h (zero_le _)
      have : Measure.pi (fun _ => D) badᶜ
          ≤ Measure.pi (fun _ => D) (badᶜ ∩ allInl) +
            Measure.pi (fun _ => D) allInlᶜ := by
        calc Measure.pi (fun _ => D) badᶜ
            ≤ Measure.pi (fun _ => D) (badᶜ ∩ allInl ∪ allInlᶜ) :=
              MeasureTheory.measure_mono (fun x hx => by
                by_cases hxA : x ∈ allInl
                · exact Or.inl ⟨hx, hxA⟩
                · exact Or.inr hxA)
          _ ≤ Measure.pi (fun _ => D) (badᶜ ∩ allInl) +
              Measure.pi (fun _ => D) allInlᶜ :=
              MeasureTheory.measure_union_le _ _
      rw [h0, hallInl_compl_zero, zero_add] at this
      exact not_lt.mpr this hcompl_pos
    -- Extract witness from badᶜ ∩ allInl
    have hne : (badᶜ ∩ allInl).Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty] at h
      rw [h] at hinter_pos
      simp at hinter_pos
    obtain ⟨xs, hxs_good, hxs_inl⟩ := hne
    -- hxs_good : xs ∈ badᶜ, i.e., xs ∉ bad
    have hxs_not_bad : xs ∉ bad := hxs_good
    -- Define hs by inverting Sum.inl
    let hs : Fin Tnat → H := fun i => (hxs_inl i).choose
    have hhs_eq : ∀ i, xs i = Sum.inl (hs i) := fun i => ((hxs_inl i).choose_spec).symm
    refine ⟨hs, fun a ha => ?_⟩
    -- Sub-step 3: Bridge to boolTestExpectation
    -- From hxs_not_bad: for all f ∈ C, |TrueErrorReal - EmpiricalError| < ε
    have hdev : |TrueErrorReal X (extendBool a) (fun _ => false) D -
        EmpiricalError X Bool (extendBool a)
          (fun i => (xs i, (fun (_ : X) => false) (xs i)))
          (zeroOneLoss Bool)| < ε := by
      by_contra hge; push Not at hge
      exact hxs_not_bad ⟨extendBool a, ⟨a, ha, rfl⟩, hge⟩
    -- True error side: trueErrorReal_extend_false gives the bridge
    have htrue_eq := trueErrorReal_extend_false μ a
    -- Empirical error side: since xs i = Sum.inl (hs i), extendBool a (xs i) = a (hs i)
    have hemp_eq : EmpiricalError X Bool (extendBool a)
        (fun i => (xs i, (fun (_ : X) => false) (xs i))) (zeroOneLoss Bool) =
        (∑ t : Fin Tnat, if a (hs t) then (1 : ℝ) else 0) / Tnat := by
      simp only [EmpiricalError, Nat.pos_iff_ne_zero.mp hTpos, ↓reduceIte]
      congr 1
      apply Finset.sum_congr rfl; intro i _
      simp only [zeroOneLoss, hhs_eq i, extendBool]
      split_ifs <;> simp_all
    rw [htrue_eq] at hdev
    rw [hemp_eq] at hdev
    rw [← boolTestExpectation_empirical_eq_avg hTpos hs a] at hdev
    exact le_of_lt hdev

end -- noncomputable section
