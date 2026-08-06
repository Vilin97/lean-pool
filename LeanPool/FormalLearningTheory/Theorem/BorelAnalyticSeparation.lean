/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import LeanPool.FormalLearningTheory.Complexity.BorelAnalyticBridge
import LeanPool.FormalLearningTheory.Complexity.Generalization

/-!
# Borel-Analytic Separation: Counterexample Chain

The singleton class over an analytic non-Borel set A ⊆ ℝ witnesses that
WellBehavedVCMeasTarget (NullMeasurableSet) is strictly weaker than
KrappWirthWellBehaved (MeasurableSet/Borel).

## Main results

- `singletonClassOn_measurable`: every hypothesis in the singleton class is measurable
- `singleton_badEvent_eq_preimage_planar`: bad event = preimage of planar witness
- `planarWitnessEvent_analytic`: the planar witness is analytic
- `planarWitnessEvent_not_measurable`: the planar witness is NOT Borel
- `singleton_badEvent_not_measurable`: the sample-space bad event is NOT Borel
-/

open MeasureTheory

/-! ## Definitions -/

/-- The constantly false concept. The base hypothesis of the singleton class, serving
both as the target concept and as the `zeroConcept` disjunct of `singletonClassOn`. -/
noncomputable def zeroConcept : Concept ℝ Bool := fun _ => false

/-- The point indicator `singletonConcept a x = (x = a)`. Each `singletonConcept a` is
itself Borel measurable; non-Borelness in the singleton-class witness comes from
quantifying over `a ∈ A` for `A` analytic non-Borel, not from any individual concept. -/
noncomputable def singletonConcept (a : ℝ) : Concept ℝ Bool :=
  fun x => if x = a then true else false

/-- The singleton class over `A ⊆ ℝ`: `{zeroConcept} ∪ {singletonConcept a | a ∈ A}`.
The `zeroConcept` disjunct is the target concept against which the symmetrization bad
event is measured. For `A` analytic non-Borel, this is the witness used to separate
`WellBehavedVCMeasTarget` from the Krapp-Wirth Borel condition. -/
def singletonClassOn (A : Set ℝ) : ConceptClass ℝ Bool :=
  {h | h = zeroConcept ∨ ∃ a ∈ A, h = singletonConcept a}

/-- The planar witness `{(x, y) ∈ ℝ × ℝ | y ∈ A ∧ x ≠ y}`. For `A` analytic non-Borel,
this set is itself analytic non-Borel. The geometric core of the separation: the
learning-theoretic bad event below is a measurable preimage of this planar set. -/
def planarWitnessEvent (A : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ A ∧ q.1 ≠ q.2}

/-- The ghost sample space at sample size `m = 1`: `(Fin 1 → ℝ) × (Fin 1 → ℝ)`. The
smallest sample size at which the singleton-class obstruction is already visible. -/
abbrev GhostPairs1 := (Fin 1 → ℝ) × (Fin 1 → ℝ)

/-- The projection `GhostPairs1 → ℝ × ℝ`, `p ↦ (p.1 0, p.2 0)`. Surjective and
measurable; non-Borelness of a target set transfers to non-Borelness of its preimage
under a measurable surjection. -/
def samplePair1ToPlane : GhostPairs1 → ℝ × ℝ :=
  fun p => (p.1 0, p.2 0)

/-- The symmetrization bad event for the singleton class at sample size `m = 1`, target
concept `zeroConcept`, and threshold `1 / 2`. Equals the preimage of `planarWitnessEvent`
under `samplePair1ToPlane` (see `singleton_badEvent_eq_preimage_planar`), and inherits
both analyticity and non-Borelness from the planar set when `A` is analytic non-Borel. -/
def singletonBadEvent (A : Set ℝ) : Set GhostPairs1 :=
  {p | ∃ h ∈ singletonClassOn A,
    EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
    EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool) ≥
      (1 : ℝ) / 2}

/-! ## Theorem G -/

/-- Every hypothesis in `singletonClassOn A` is Borel measurable: `zeroConcept` is
constant, and each `singletonConcept a` factors through `measurableSet_singleton`. The
class is regular at the level of individual hypotheses; non-measurability enters only
through the existential over `A`. -/
theorem singletonClassOn_measurable
    (A : Set ℝ) :
    ∀ h ∈ singletonClassOn A, Measurable h := by
  intro h hh
  rcases hh with rfl | ⟨a, _, rfl⟩
  · exact measurable_const
  · show Measurable (singletonConcept a)
    unfold singletonConcept
    exact Measurable.piecewise (measurableSet_singleton a) measurable_const measurable_const

/-! ## Theorem H -/

/-- The singleton bad event equals `samplePair1ToPlane ⁻¹' planarWitnessEvent`. The set
equality that transports both analyticity and non-Borelness from the planar witness to
the learning-theoretic bad event. -/
theorem singleton_badEvent_eq_preimage_planar
    (A : Set ℝ) :
    singletonBadEvent A = samplePair1ToPlane ⁻¹' planarWitnessEvent A := by
  ext p
  simp only [singletonBadEvent, singletonClassOn, planarWitnessEvent, samplePair1ToPlane,
    Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨h, hh, hgap⟩
    rcases hh with rfl | ⟨a, haA, rfl⟩
    · -- zeroConcept case: gap must be 0
      exfalso
      unfold EmpiricalError zeroOneLoss zeroConcept at hgap
      simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
        Nat.cast_one, div_one, sub_self] at hgap
      linarith
    · -- singletonConcept a case
      unfold EmpiricalError at hgap
      simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
        Nat.cast_one, div_one] at hgap
      refine ⟨?_, ?_⟩
      · -- p.2 0 ∈ A
        by_contra h_not
        have hne : p.2 0 ≠ a := fun heq => h_not (heq ▸ haA)
        have hz : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 0 := by
          unfold zeroOneLoss zeroConcept singletonConcept; simp [hne]
        have hnn : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) ≥ 0 := by
          unfold zeroOneLoss; split <;> norm_num
        rw [hz] at hgap; linarith
      · -- p.1 0 ≠ p.2 0
        intro heq
        by_cases ha2 : p.2 0 = a
        · have ha1 : p.1 0 = a := heq ▸ ha2
          have e1 : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 1 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha2]
          have e2 : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) = 1 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha1]
          rw [e1, e2] at hgap; linarith
        · have e1 : zeroOneLoss Bool (singletonConcept a (p.2 0)) (zeroConcept (p.2 0)) = 0 := by
            unfold zeroOneLoss zeroConcept singletonConcept; simp [ha2]
          have hnn : zeroOneLoss Bool (singletonConcept a (p.1 0)) (zeroConcept (p.1 0)) ≥ 0 := by
            unfold zeroOneLoss; split <;> norm_num
          rw [e1] at hgap; linarith
  · rintro ⟨hmem, hne⟩
    refine ⟨singletonConcept (p.2 0), Or.inr ⟨p.2 0, hmem, rfl⟩, ?_⟩
    unfold EmpiricalError
    simp only [show (1 : ℕ) ≠ 0 from one_ne_zero, ↓reduceIte, Fin.sum_univ_one,
      Nat.cast_one, div_one]
    unfold zeroOneLoss zeroConcept singletonConcept
    simp only [↓reduceIte]
    have h1 : p.1 0 ≠ p.2 0 := hne
    simp only [h1, ↓reduceIte]
    norm_num

/-! ## Theorem I -/

/-- For `A` analytic, `planarWitnessEvent A` is analytic. The proof presents it as the
intersection of `Prod.snd ⁻¹' A` (analytic, by preimage of analytic under a continuous
map) with the Borel set `{(x, y) | x ≠ y}` (the complement of the diagonal). Analytic
sets are closed under intersection with Borel sets. -/
theorem planarWitnessEvent_analytic
    (A : Set ℝ) (hA : AnalyticSet A) :
    AnalyticSet (planarWitnessEvent A) := by
  have h1 : AnalyticSet (Prod.snd ⁻¹' A : Set (ℝ × ℝ)) :=
    hA.preimage continuous_snd
  have h2 : AnalyticSet ({q : ℝ × ℝ | q.1 ≠ q.2}) := by
    have : MeasurableSet ({q : ℝ × ℝ | q.1 = q.2}) :=
      (isClosed_eq continuous_fst continuous_snd).measurableSet
    exact this.compl.analyticSet
  have hinter : planarWitnessEvent A = (Prod.snd ⁻¹' A) ∩ {q | q.1 ≠ q.2} := by
    ext q; simp [planarWitnessEvent, and_comm]
  rw [hinter]
  rw [Set.inter_eq_iInter]
  exact AnalyticSet.iInter (fun b => by cases b <;> simpa using by assumption)

/-! ## Theorem J -/

/-- For `A` non-Borel, `planarWitnessEvent A` is non-Borel. The proof picks some
`a ∉ A` and shows the vertical section `y ↦ (a, y)` pulls the planar event back to `A`
itself: if the planar event were Borel, its preimage under this measurable map would be
Borel too, contradicting the hypothesis on `A`. -/
theorem planarWitnessEvent_not_measurable
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (planarWitnessEvent A) := by
  intro hplanar
  apply hA_non
  have hA_ne_univ : A ≠ Set.univ := fun h => hA_non (h ▸ MeasurableSet.univ)
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem A).mp hA_ne_univ
  have hv : Measurable (fun y : ℝ => (a, y)) :=
    Measurable.prod (by exact measurable_const) (by exact measurable_id)
  have hpre : (fun y : ℝ => (a, y)) ⁻¹' planarWitnessEvent A = A := by
    ext y
    simp only [Set.mem_preimage, planarWitnessEvent, Set.mem_ofPred_eq]
    constructor
    · exact fun ⟨hy, _⟩ => hy
    · exact fun hy => ⟨hy, fun hay => ha (hay ▸ hy)⟩
  exact hpre ▸ hv hplanar

/-! ## Theorem K -/

/-- For `A` non-Borel, the singleton bad event is non-Borel. Combine
`singleton_badEvent_eq_preimage_planar` with `planarWitnessEvent_not_measurable`: the
preimage of a non-Borel set under a measurable *surjection* cannot itself be Borel. -/
theorem singleton_badEvent_not_measurable
    (A : Set ℝ) (hA_non : ¬ MeasurableSet A) :
    ¬ MeasurableSet (singletonBadEvent A) := by
  intro hbad
  rw [singleton_badEvent_eq_preimage_planar A] at hbad
  have hmeas : Measurable samplePair1ToPlane :=
    Measurable.prod ((measurable_pi_apply 0).comp measurable_fst)
      ((measurable_pi_apply 0).comp measurable_snd)
  have hsurj : Function.Surjective samplePair1ToPlane := by
    intro ⟨x, y⟩
    exact ⟨(fun _ => x, fun _ => y), by simp [samplePair1ToPlane]⟩
  have hplanar := (hmeas.measurableSet_preimage_iff_of_surjective hsurj).mp hbad
  exact planarWitnessEvent_not_measurable A hA_non hplanar

/-! ## Theorem L: Relative separation theorem -/

/-- **Main separation theorem.** Given any analytic non-Borel set `A ⊆ ℝ`, the
concept class obtained by parameterising `singletonConcept` (plus `zeroConcept`) over
`A` is a concrete witness that `WellBehavedVCMeasTarget` is strictly weaker than the
Krapp-Wirth Borel condition. The class is constructed as `Set.range e` for an
evaluation map `e : Bool × β → Concept ℝ Bool` built from a Polish parameterisation of
`A`; post-construction, `Set.range e` equals `singletonClassOn (Set.range g)` where `g`
realises `A`.

The class satisfies:

* `MeasurableHypotheses`: every individual hypothesis is Borel
  (`singletonClassOn_measurable`).
* `WellBehavedVCMeasTarget`: the bad event is analytic
  (`planarWitnessEvent_analytic` lifted via `singleton_badEvent_eq_preimage_planar`),
  hence `NullMeasurableSet` by the Choquet bridge.
* NOT `KrappWirthWellBehaved`: the bad event is not Borel
  (`singleton_badEvent_not_measurable`).

The separation is realised by passing through the standard Borel space ℝ as the
parameter space; the construction reuses no problem-specific fact beyond the existence
of an analytic non-Borel subset of ℝ (Souslin's classical result), supplied in
`exists_measTarget_separation`. The witness shows that the measurable-target variant
proved in this kernel is a genuine improvement over the existing literature, not a
restatement. -/
theorem analytic_nonborel_set_gives_measTarget_separation
    (A : Set ℝ)
    (hA_an : MeasureTheory.AnalyticSet A)
    (hA_non : ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  -- Step 1: Get Polish β and g : β → ℝ with range g = A
  rcases MeasureTheory.analyticSet_iff_exists_polishSpace_range.mp hA_an with
    ⟨β, hτ, hP, g, hg_cont, hg_range⟩
  -- Equip β with Borel σ-algebra to get MeasurableSpace and StandardBorelSpace
  let : MeasurableSpace β := @borel β hτ
  have : @BorelSpace β hτ (@borel β hτ) := ⟨rfl⟩
  have : @StandardBorelSpace β (@borel β hτ) := ⟨⟨hτ, ⟨rfl⟩, hP⟩⟩
  have hg_meas : Measurable g := hg_cont.measurable
  -- Step 2: A is nonempty
  have hA_ne : A.Nonempty := by
    by_contra h; exact hA_non (Set.not_nonempty_iff_eq_empty.mp h ▸ MeasurableSet.empty)
  obtain ⟨a0, ha0⟩ := hA_ne
  obtain ⟨θ0, hθ0⟩ : ∃ θ0, g θ0 = a0 := by
    have : a0 ∈ Set.range g := hg_range ▸ ha0; exact this
  -- Step 3: Define e : Bool × β → Concept ℝ Bool
  let e : Bool × β → Concept ℝ Bool := fun t x =>
    if t.1 then singletonConcept (g t.2) x else zeroConcept x
  -- Step 4: Joint measurability of e
  have he : Measurable (fun p : (Bool × β) × ℝ => e p.1 p.2) := by
    simp only [e, singletonConcept, zeroConcept]
    have hbool : MeasurableSet {p : (Bool × β) × ℝ | p.1.1 = true} :=
      (measurable_fst.comp measurable_fst) (measurableSet_singleton true)
    have htrue : Measurable (fun p : (Bool × β) × ℝ =>
        if p.2 = g p.1.2 then true else false) := by
      have hc1 : Continuous (fun p : (Bool × β) × ℝ => p.2) := continuous_snd
      have hc2 : Continuous (fun p : (Bool × β) × ℝ => g p.1.2) :=
        hg_cont.comp (continuous_snd.comp continuous_fst)
      have hset : MeasurableSet {p : (Bool × β) × ℝ | p.2 = g p.1.2} :=
        (isClosed_eq hc1 hc2).measurableSet
      exact Measurable.piecewise hset measurable_const measurable_const
    -- Goal: Measurable (fun p => if p.1.1 then (if p.2 = g p.1.2 then true else false) else false)
    exact Measurable.piecewise hbool htrue measurable_const
  -- Step 5: C = range e, MeasurableHypotheses
  let C : ConceptClass ℝ Bool := Set.range e
  have hC_meas : MeasurableHypotheses ℝ C := by
    refine ⟨fun h hh => ?_⟩
    obtain ⟨t, rfl⟩ := hh
    simp only [e]
    by_cases hb : t.1
    · simp only [hb, ↓reduceIte, singletonConcept]
      exact Measurable.piecewise (measurableSet_singleton _) measurable_const measurable_const
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, zeroConcept]; exact measurable_const
  -- Step 6: WellBehavedVCMeasTarget
  have hWB : WellBehavedVCMeasTarget ℝ C :=
    borel_param_wellBehavedVCMeasTarget e he
  -- Step 7: C = singletonClassOn (range g)
  have hC_eq : C = singletonClassOn (Set.range g) := by
    ext h; constructor
    · rintro ⟨⟨b, θ⟩, rfl⟩
      by_cases hb : b
      · exact Or.inr ⟨g θ, ⟨θ, rfl⟩, by funext x; simp [e, hb, singletonConcept]⟩
      · exact Or.inl (by funext x; simp [e, hb, zeroConcept])
    · rintro (rfl | ⟨a, ⟨θ, rfl⟩, rfl⟩)
      · exact ⟨(false, θ0), by funext x; simp [e, zeroConcept]⟩
      · exact ⟨(true, θ), by funext x; simp [e, singletonConcept]⟩
  -- Step 8: Separation - construct the witness
  refine ⟨C, hC_meas, hWB, ?_⟩
  intro hKW
  have hA_non' : ¬ MeasurableSet (Set.range g) := hg_range ▸ hA_non
  have hbad_non := singleton_badEvent_not_measurable (Set.range g) hA_non'
  apply hbad_non
  -- Show singletonBadEvent (range g) is MeasurableSet
  -- From KrappWirth V: ghostGapSup C zeroConcept 1 is Measurable
  have hV := hKW.V_measurable (zeroConcept) 1
  have hpre : MeasurableSet (ghostGapSup C zeroConcept 1 ⁻¹' Set.Ici ((1 : ℝ) / 2)) :=
    hV measurableSet_Ici
  -- singletonBadEvent = ghostGapSup preimage
  suffices hsuff : singletonBadEvent (Set.range g) =
      ghostGapSup C zeroConcept 1 ⁻¹' Set.Ici ((1 : ℝ) / 2) by
    rw [hsuff]; exact hpre
  -- Prove the set equality
  ext p
  simp only [singletonBadEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_Ici,
    ghostGapSup, ghostGapVals, oneSidedGhostGap]
  -- C is nonempty (contains zeroConcept)
  have hC_ne : C.Nonempty := ⟨e (false, θ0), ⟨(false, θ0), rfl⟩⟩
  -- The value set is a subset of the finite grid, hence finite (used by both directions).
  have hfin : {r | ∃ h ∈ C, r =
      EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
        (zeroOneLoss Bool) -
      EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
        (zeroOneLoss Bool)}.Finite := by
    apply Set.Finite.subset (Finset.finite_toSet (ghostGapGrid 1))
    intro r ⟨h, _, hr⟩
    rw [hr]; exact oneSidedGhostGap_mem_grid h zeroConcept 1 p
  constructor
  · -- Forward: witness in singletonClassOn → sSup ≥ 1 / 2
    rintro ⟨h_wit, hh_wit, hge⟩
    have hmem : (EmpiricalError ℝ Bool h_wit
        (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h_wit (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool)) ∈
      {r | ∃ h ∈ C, r =
        EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i))) (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i))) (zeroOneLoss Bool)} :=
      ⟨h_wit, hC_eq ▸ hh_wit, rfl⟩
    calc (1 : ℝ) / 2 ≤ _ := hge
      _ ≤ sSup _ := le_csSup hfin.bddAbove hmem
  · -- Backward: sSup ≥ 1 / 2 → witness in singletonClassOn
    intro hp
    have hne : {r | ∃ h ∈ C, r =
        EmpiricalError ℝ Bool h (fun i => (p.2 i, zeroConcept (p.2 i)))
          (zeroOneLoss Bool) -
        EmpiricalError ℝ Bool h (fun i => (p.1 i, zeroConcept (p.1 i)))
          (zeroOneLoss Bool)}.Nonempty := by
      obtain ⟨h0, hh0⟩ := hC_ne
      exact ⟨_, h0, hh0, rfl⟩
    obtain ⟨h_star, hh_star, h_eq⟩ := hne.csSup_mem hfin
    exact ⟨h_star, hC_eq ▸ hh_star, by rw [← h_eq]; exact hp⟩

/-- Existence form: provided an analytic non-Borel set in ℝ is available, the
separation in `analytic_nonborel_set_gives_measTarget_separation` is realised. The
unconditional form (with no hypothesis) requires supplying Souslin's classical
analytic non-Borel set; this theorem packages the reduction. -/
theorem exists_measTarget_separation
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  obtain ⟨A, hA_an, hA_non⟩ := hex
  exact analytic_nonborel_set_gives_measTarget_separation A hA_an hA_non
