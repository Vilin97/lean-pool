/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex.SumIntegral

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.LinearAlgebra.Finsupp.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import LeanPool.CarlsonFunctions.StdSimplexMeasure.ProdSlices

/-! # Aggregation of solid-simplex volume -/

open MeasureTheory

@[expose] public noncomputable section

/-! ## Aggregation of a solid simplex -/

open scoped Classical in
/-- Tonelli disintegration of a positive simplex after splitting along a decidable predicate. -/
theorem lintegral_posSimplex_split_pred {α : Type*} [Fintype α]
    (p : α → Prop) [DecidablePred p] (r : ℝ)
    (G : ({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ) → ENNReal) (hG : Measurable G) :
    ∫⁻ x in posSimplex α r, G (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p x) =
      ∫⁻ u in posSimplex {a : α // p a} r,
        ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p
  have hmp := volume_preserving_piEquivPiSubtypeProd (fun _ : α ↦ ℝ) p
  let T : Set (({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ)) :=
    {q | (∀ i, 0 ≤ q.1 i) ∧ (∀ i, 0 ≤ q.2 i) ∧ ∑ i, q.1 i + ∑ i, q.2 i ≤ r}
  have himage : e '' posSimplex α r = T := by
    ext q
    constructor
    · rintro ⟨x, ⟨hx0, hxs⟩, rfl⟩
      refine ⟨fun i ↦ hx0 i.1, fun i ↦ hx0 i.1, ?_⟩
      have hsum := Fintype.sum_subtype_add_sum_subtype p x
      simpa [e] using (hsum ▸ hxs)
    · intro hq
      refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
      rcases hq with ⟨hu0, hv0, hsum⟩
      refine ⟨?_, ?_⟩
      · intro a
        by_cases ha : p a
        · simpa [e, ha] using hu0 ⟨a, ha⟩
        · simpa [e, ha] using hv0 ⟨a, ha⟩
      · have h1 : (fun i : {a : α // p a} ↦ e.symm q i) = q.1 := by
          funext i
          change (if h : p i.1 then q.1 ⟨i.1, h⟩ else q.2 ⟨i.1, h⟩) = q.1 i
          simp [i.property]
        have h2 : (fun i : {a : α // ¬p a} ↦ e.symm q i) = q.2 := by
          funext i
          change (if h : p i.1 then q.1 ⟨i.1, h⟩ else q.2 ⟨i.1, h⟩) = q.2 i
          simp [i.property]
        calc
          ∑ a, e.symm q a
              = (∑ i : {a : α // p a}, e.symm q i) +
                  ∑ i : {a : α // ¬p a}, e.symm q i :=
                (Fintype.sum_subtype_add_sum_subtype p (e.symm q)).symm
          _ = ∑ i, q.1 i + ∑ i, q.2 i := by rw [h1, h2]
          _ ≤ r := hsum
  have hT : MeasurableSet T := by
    rw [← himage]
    exact e.measurableEmbedding.measurableSet_image.2 (measurableSet_posSimplex α r)
  have hsection (u : {a : α // p a} → ℝ) :
      Prod.mk u ⁻¹' T =
        if u ∈ posSimplex {a : α // p a} r then
          posSimplex {a : α // ¬p a} (r - ∑ i, u i)
        else (∅ : Set ({a : α // ¬p a} → ℝ)) := by
    ext v
    by_cases hu : u ∈ posSimplex {a : α // p a} r
    · simp only [hu, ↓reduceIte]
      simp only [T, posSimplex, Set.mem_preimage, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hu0, hv0, hs⟩
        exact ⟨hv0, by linarith⟩
      · rintro ⟨hv0, hvs⟩
        exact ⟨hu.1, hv0, by linarith⟩
    · simp only [hu, ↓reduceIte, Set.mem_empty_iff_false, iff_false]
      intro hv
      simp only [T, Set.mem_preimage, Set.mem_ofPred_eq] at hv
      rcases hv with ⟨hu0, hv0, hs⟩
      exact hu ⟨hu0, by
        have : 0 ≤ ∑ i, v i := Finset.sum_nonneg fun i _ ↦ hv0 i
        linarith⟩
  calc
    ∫⁻ x in posSimplex α r, G (e x) =
        ∫⁻ q in T, G q ∂volume.prod volume := by
      rw [← himage]
      exact (hmp.restrict_image_emb e.measurableEmbedding
        (posSimplex α r)).lintegral_comp_emb e.measurableEmbedding G
    _ = ∫⁻ u, ∫⁻ v in Prod.mk u ⁻¹' T, G (u, v) :=
      setLIntegral_prod_slices T hT G hG.aemeasurable
    _ = ∫⁻ u in posSimplex {a : α // p a} r,
        ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
      rw [← lintegral_indicator (measurableSet_posSimplex _ r)]
      apply lintegral_congr
      intro u
      rw [hsection]
      by_cases hu : u ∈ posSimplex {a : α // p a} r
      · simp [hu]
      · simp [hu]

open scoped Classical in
/-- A parameter-dependent nonnegative integral over a positive simplex whose radius decreases
with the parameter is measurable. -/
private theorem measurable_lintegral_posSimplex_sub
    {δ : Type*} [Fintype δ] (r : ℝ)
    (F : ℝ → (δ → ℝ) → ENNReal) (hF : Measurable (Function.uncurry F)) :
    Measurable fun s => ∫⁻ z in posSimplex δ (r - s), F s z := by
  let T : Set (ℝ × (δ → ℝ)) := {q | q.2 ∈ posSimplex δ (r - q.1)}
  have hT : MeasurableSet T := by
    have hsum : Measurable (fun q : ℝ × (δ → ℝ) => q.1 + ∑ i, q.2 i) := by fun_prop
    have hraw := (MeasurableSet.iInter fun i => measurableSet_le
      (measurable_const : Measurable fun _ : ℝ × (δ → ℝ) => (0 : ℝ))
      ((measurable_pi_apply i).comp measurable_snd)).inter
        (measurableSet_le hsum
          (measurable_const : Measurable fun _ : ℝ × (δ → ℝ) => r))
    have h : MeasurableSet ({q : ℝ × (δ → ℝ) | ∀ i, 0 ≤ q.2 i} ∩
        {q | q.1 + ∑ i, q.2 i ≤ r}) := by
      convert hraw using 1
      ext q
      simp
    convert h using 1
    ext q
    simp only [T, posSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor <;> rintro ⟨h0, hs⟩ <;> exact ⟨h0, by linarith⟩
  have hI : Measurable (T.indicator (Function.uncurry F)) := hF.indicator hT
  change Measurable (Function.uncurry
    (fun s z => T.indicator (Function.uncurry F) (s, z))) at hI
  have heq : (fun s => ∫⁻ z in posSimplex δ (r - s), F s z) =
      fun s => ∫⁻ z, T.indicator (Function.uncurry F) (s, z) := by
    funext s
    rw [← lintegral_indicator (measurableSet_posSimplex δ (r - s))]
    apply lintegral_congr
    intro z
    simp only [T, Set.indicator_apply, Set.mem_ofPred_eq, Function.uncurry_apply_pair]
  rw [heq]
  exact hI.lintegral_prod_right

open scoped Classical in
/-- Fibrewise density for the push-forward of Lebesgue measure on a solid simplex under
coordinate aggregation. For a vector `z` this is the product of the solid-simplex volumes
of the fibres of `f`. -/
def posSimplexAggregateDensity {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (z : β → ℝ) : ENNReal :=
  ∏ k, ENNReal.ofReal (z k) ^ (Fintype.card {i : α // f i = k} - 1) /
    (Nat.factorial (Fintype.card {i : α // f i = k} - 1) : ENNReal)

open scoped Classical in
/-- After splitting the source at one fibre, coordinate aggregation consists of summing that
fibre and aggregating the complementary coordinates. -/
private theorem linearMap_piEquivPiSubtypeProd_eq
    {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (k : β) :
    let p : α → Prop := fun a => f a = k
    let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ) p
    let β' := {j : β // j ≠ k}
    let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
    let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
      if h : j = k then s else z ⟨j, h⟩
    ∀ q, FunOnFinite.linearMap ℝ ℝ f (e.symm q) =
      assemble (∑ i, q.1 i) (FunOnFinite.linearMap ℝ ℝ f' q.2) := by
  classical
  dsimp only
  intro q
  let _ : Fintype {a : α // f a = k} := Fintype.ofFinite _
  let _ : Fintype {a : α // ¬f a = k} := Fintype.ofFinite _
  funext j
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hj : j = k
  · subst j
    rw [dite_eq_left rfl]
    rw [Finset.sum_subtype (p := fun a => f a = k)
      (Finset.univ.filter fun a => f a = k) (by simp)]
    apply Finset.sum_congr rfl
    intro a _
    simp [a.property]
  · simp only [dite_eq_right hj]
    rw [FunOnFinite.linearMap_apply_apply]
    rw [Finset.sum_subtype (p := fun a => f a = j)
      (Finset.univ.filter fun a => f a = j) (by simp)]
    change (∑ a : {a : α // f a = j},
      (if h : f a = k then q.1 ⟨a, h⟩ else q.2 ⟨a, h⟩)) = _
    simp only [Subtype.ext_iff] at ⊢
    rw [Finset.sum_subtype (p := fun a : {a : α // ¬f a = k} => f a = j)
      (Finset.univ.filter fun a : {a : α // ¬f a = k} => f a = j) (by simp)]
    apply Fintype.sum_equiv
      { toFun := fun a => ⟨⟨a, fun h => hj (a.property.symm.trans h)⟩, a.property⟩
        invFun := fun a => ⟨a.1.1, a.property⟩
        left_inv := fun a => by ext; rfl
        right_inv := fun a => by ext; rfl }
    intro a
    have hne : ¬f a = k := fun h => hj (a.property.symm.trans h)
    rw [dite_eq_right hne]
    congr 1

open scoped Classical in
/-- The aggregation density factors when one target coordinate and its source fibre are
split off. -/
private theorem posSimplexAggregateDensity_split
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (k : β) (s : ℝ) (z : {j : β // j ≠ k} → ℝ) :
    let p : α → Prop := fun a => f a = k
    let β' := {j : β // j ≠ k}
    let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
    let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
      if h : j = k then s else z ⟨j, h⟩
    posSimplexAggregateDensity f (assemble s z) =
      (ENNReal.ofReal s ^ (Fintype.card {a : α // p a} - 1) /
        (Nat.factorial (Fintype.card {a : α // p a} - 1) : ENNReal)) *
        posSimplexAggregateDensity f' z := by
  classical
  dsimp only
  unfold posSimplexAggregateDensity
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun j : β =>
    ENNReal.ofReal (if h : j = k then s else z ⟨j, h⟩) ^
      (Fintype.card {i : α // f i = j} - 1) /
        (Nat.factorial (Fintype.card {i : α // f i = j} - 1) : ENNReal)) k]
  rw [dite_eq_left rfl]
  congr 1
  apply Fintype.prod_congr
  intro j
  let e : {i : α // f i = (j : β)} ≃
      {i : {a : α // ¬f a = k} //
        (⟨f i, i.property⟩ : {j : β // j ≠ k}) = j} :=
    { toFun := fun a => ⟨⟨a, fun h => j.property (a.property.symm.trans h)⟩,
        Subtype.ext a.property⟩
      invFun := fun a => ⟨a.1.1, congrArg Subtype.val a.property⟩
      left_inv := fun a => by ext; rfl
      right_inv := fun a => by ext; rfl }
  rw [dite_eq_right j.property]
  have hj : (⟨(j : β), j.property⟩ : {j : β // j ≠ k}) = j := Subtype.ext rfl
  rw [hj]
  apply congrArg (fun n : ℕ => ENNReal.ofReal (z j) ^ (n - 1) /
    (Nat.factorial (n - 1) : ENNReal))
  convert Fintype.card_congr e using 1
  congr 1
  apply Subsingleton.elim

/-- The solid-simplex aggregation formula when the target index type is empty. -/
theorem lintegral_posSimplex_comp_aggregate_of_isEmpty
    {α β : Type*} [Fintype α] [Fintype β] [IsEmpty β]
    (f : α → β) (_hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (_hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  let _ : IsEmpty α := ⟨fun a => isEmptyElim (f a)⟩
  have hα : posSimplex α r = Set.univ := by
    ext x
    simp [posSimplex, hr]
  have hβ : posSimplex β r = Set.univ := by
    ext z
    simp [posSimplex, hr]
  rw [hα, hβ, Measure.restrict_univ, Measure.volume_pi_eq_dirac,
    Measure.volume_pi_eq_dirac, lintegral_dirac]
  simp [Measure.restrict_univ, posSimplexAggregateDensity]
  congr 1
  funext b
  exact isEmptyElim b

open scoped Classical in
/-- The solid-simplex aggregation formula when the target has a unique coordinate. -/
theorem lintegral_posSimplex_comp_aggregate_of_unique
    {α β : Type*} [Fintype α] [Fintype β] [Unique β]
    (f : α → β) (hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  let _ : Nonempty α := ⟨Classical.choose (hf default)⟩
  let e := MeasurableEquiv.piUnique (fun _ : β => ℝ)
  have hmp := volume_preserving_piUnique (fun _ : β => ℝ)
  have he_symm (s : ℝ) : e.symm s = fun _ : β => s := by
    funext j
    exact congrArg (e.symm s) (Subsingleton.elim j default)
  have hsimplex : e ⁻¹' Set.Icc (0 : ℝ) r = posSimplex β r := by
    ext z
    simp only [Set.mem_preimage, Set.mem_Icc]
    change (0 ≤ z default ∧ z default ≤ r) ↔
      (∀ j, 0 ≤ z j) ∧ ∑ j, z j ≤ r
    constructor
    · rintro ⟨h0, hr⟩
      exact ⟨fun j => by simpa [Subsingleton.elim j default] using h0, by simpa using hr⟩
    · rintro ⟨h0, hr⟩
      exact ⟨h0 default, by simpa using hr⟩
  have hagg (x : α → ℝ) :
      FunOnFinite.linearMap ℝ ℝ f x = fun _ : β => ∑ i, x i := by
    funext k
    rw [FunOnFinite.linearMap_apply_apply]
    congr 1
    ext i
    simp [Subsingleton.elim (f i) k]
  rw [show (fun x => g (FunOnFinite.linearMap ℝ ℝ f x)) =
      (fun x => g (fun _ : β => ∑ i, x i)) by funext x; rw [hagg]]
  have hg' : Measurable (fun s : ℝ => g (fun _ : β => s)) := by
    exact hg.comp (by fun_prop)
  rw [lintegral_posSimplex_comp_sum r hr (fun s => g (fun _ : β => s)) hg']
  have hfiber : Fintype.card {i : α // f i = default} = Fintype.card α := by
    apply Fintype.card_congr
    exact
      { toFun := Subtype.val
        invFun := fun i => ⟨i, Subsingleton.elim (f i) default⟩
        left_inv := fun i => by ext; rfl
        right_inv := fun _ => rfl }
  calc
    (∫⁻ s in Set.Icc (0 : ℝ) r,
        (g fun _ : β => s) *
          (ENNReal.ofReal s ^ (Fintype.card α - 1) /
            Nat.factorial (Fintype.card α - 1))) =
        ∫⁻ s in Set.Icc (0 : ℝ) r,
          g (e.symm s) * posSimplexAggregateDensity f (e.symm s) := by
      apply setLIntegral_congr_fun measurableSet_Icc
      intro s _
      change (g fun _ : β => s) * _ = g (e.symm s) * _
      rw [he_symm]
      congr 1
      simp only [posSimplexAggregateDensity]
      rw [Fintype.prod_unique, hfiber]
    _ = ∫⁻ z in e ⁻¹' Set.Icc (0 : ℝ) r,
        g z * posSimplexAggregateDensity f z := by
      have hchange := (hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding
        (fun s => g (e.symm s) * posSimplexAggregateDensity f (e.symm s))
        (Set.Icc (0 : ℝ) r)).symm
      calc
        _ = ∫⁻ z in e ⁻¹' Set.Icc (0 : ℝ) r,
              g (e.symm (e z)) * posSimplexAggregateDensity f (e.symm (e z)) := hchange
        _ = _ := by
          apply setLIntegral_congr_fun (measurableSet_Icc.preimage e.measurable)
          intro z _
          change g (e.symm (e z)) * posSimplexAggregateDensity f (e.symm (e z)) = _
          rw [e.symm_apply_apply]
    _ = ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by rw [hsimplex]

open scoped Classical in
/-- Pushing Lebesgue measure on a solid simplex forward under coordinate aggregation
(`FunOnFinite.linearMap`) weights the target solid simplex by the product of fibre volumes.

This is the solid-simplex form of the aggregation identity used for `stdSimplexMeasure`.
The unique-target case is `lintegral_posSimplex_comp_sum`. -/
theorem lintegral_posSimplex_comp_aggregate
    {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (hf : Function.Surjective f) (r : ℝ) (hr : 0 ≤ r)
    (g : (β → ℝ) → ENNReal) (hg : Measurable g) :
    ∫⁻ x in posSimplex α r, g (FunOnFinite.linearMap ℝ ℝ f x) =
      ∫⁻ z in posSimplex β r, g z * posSimplexAggregateDensity f z := by
  induction hcard : Fintype.card β using Nat.strong_induction_on generalizing α β r with
  | h n ih =>
      cases isEmpty_or_nonempty β with
      | inl _ => exact lintegral_posSimplex_comp_aggregate_of_isEmpty f hf r hr g hg
      | inr _ =>
          cases subsingleton_or_nontrivial β with
          | inl _ =>
              let _ : Unique β :=
                { default := Classical.choice inferInstance
                  uniq := fun _ => Subsingleton.elim _ _ }
              exact lintegral_posSimplex_comp_aggregate_of_unique f hf r hr g hg
          | inr _ =>
              classical
              let k : β := Classical.choice inferInstance
              let β' := {j : β // j ≠ k}
              let p : α → Prop := fun a => f a = k
              let f' : {a : α // ¬p a} → β' := fun a => ⟨f a, a.property⟩
              have hf' : Function.Surjective f' := by
                intro j
                obtain ⟨a, ha⟩ := hf j
                exact ⟨⟨a, fun hak => j.property (ha.symm.trans hak)⟩, Subtype.ext ha⟩
              have hcard' : Fintype.card β' < n := by
                rw [← hcard]
                rw [Fintype.card_subtype_compl (fun j : β => j = k),
                  Fintype.card_subtype_eq k]
                exact Nat.sub_lt (Fintype.card_pos) zero_lt_one
              let eα := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : α => ℝ) p
              let assemble : ℝ → (β' → ℝ) → (β → ℝ) := fun s z j =>
                if h : j = k then s else z ⟨j, h⟩
              let G : ({a : α // p a} → ℝ) × ({a : α // ¬p a} → ℝ) → ENNReal :=
                fun q => g (assemble (∑ i, q.1 i)
                  (FunOnFinite.linearMap ℝ ℝ f' q.2))
              have hG : Measurable G := by
                apply hg.comp
                apply Measurable.of_eval _
                intro j
                by_cases hj : j = k
                · subst j
                  simp only [assemble, dite_eq_left rfl]
                  fun_prop
                · simp only [assemble, dite_eq_right hj]
                  fun_prop
              have hsource :
                  (∫⁻ x in posSimplex α r,
                    g (FunOnFinite.linearMap ℝ ℝ f x)) =
                    ∫⁻ u in posSimplex {a : α // p a} r,
                      ∫⁻ v in posSimplex {a : α // ¬p a} (r - ∑ i, u i), G (u, v) := by
                calc
                  _ = ∫⁻ x in posSimplex α r, G (eα x) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex α r)
                    intro x _
                    have ha := linearMap_piEquivPiSubtypeProd_eq f k (eα x)
                    dsimp only [G]
                    apply congrArg g
                    simpa only [p, eα, β', f', assemble, eα.symm_apply_apply] using ha
                  _ = _ := lintegral_posSimplex_split_pred p r G hG
              let H : ℝ → ENNReal := fun s =>
                ∫⁻ z in posSimplex β' (r - s),
                  g (assemble s z) * posSimplexAggregateDensity f' z
              have hpair : Measurable (Function.uncurry (fun (s : ℝ) (z : β' → ℝ) =>
                  g (assemble s z) * posSimplexAggregateDensity f' z)) := by
                apply Measurable.mul
                · apply hg.comp
                  apply Measurable.of_eval _
                  intro j
                  by_cases hj : j = k
                  · subst j
                    simp only [assemble, dite_eq_left rfl]
                    fun_prop
                  · simp only [assemble, dite_eq_right hj]
                    fun_prop
                · unfold posSimplexAggregateDensity
                  fun_prop
              have hH : Measurable H := by
                exact measurable_lintegral_posSimplex_sub r _ hpair
              let A := {a : α // p a}
              let _ : Nonempty A := ⟨⟨Classical.choose (hf k), Classical.choose_spec (hf k)⟩⟩
              have hscalar :
                  (∫⁻ x in posSimplex α r,
                    g (FunOnFinite.linearMap ℝ ℝ f x)) =
                    ∫⁻ s in Set.Icc (0 : ℝ) r,
                      H s * (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                        Nat.factorial (Fintype.card A - 1)) := by
                rw [hsource]
                calc
                  _ = ∫⁻ u in posSimplex A r, H (∑ i, u i) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex A r)
                    intro u hu
                    have hrs : 0 ≤ r - ∑ i, u i := sub_nonneg.mpr hu.2
                    have hrec := ih (Fintype.card β') hcard' f' hf'
                      (r - ∑ i, u i) hrs (fun z => g (assemble (∑ i, u i) z))
                      (by
                        apply hg.comp
                        apply Measurable.of_eval _
                        intro j
                        by_cases hj : j = k
                        · subst j
                          simp only [assemble, dite_eq_left rfl]
                          fun_prop
                        · simp only [assemble, dite_eq_right hj]
                          fun_prop)
                      rfl
                    simpa only [G, H] using hrec
                  _ = _ := lintegral_posSimplex_comp_sum r hr H hH
              let pβ : β → Prop := fun j => j = k
              let eβ := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : β => ℝ) pβ
              let Aβ := {j : β // pβ j}
              let _ : Fintype Aβ := Subtype.fintype pβ
              let _ : Unique Aβ :=
                { default := ⟨k, rfl⟩
                  uniq := fun a => Subtype.ext a.property }
              have heβ (q : (Aβ → ℝ) × (β' → ℝ)) :
                  eβ.symm q = assemble (∑ i, q.1 i) q.2 := by
                funext j
                by_cases hj : j = k
                · subst j
                  change (if h : k = k then q.1 ⟨k, h⟩ else q.2 ⟨k, h⟩) = _
                  simp only [dite_eq_left rfl, assemble]
                  rw [Fintype.sum_unique]
                  congr 2
                · change (if h : j = k then q.1 ⟨j, h⟩ else q.2 ⟨j, h⟩) = _
                  simp only [dite_eq_right hj, assemble]
              let Gβ : (Aβ → ℝ) × (β' → ℝ) → ENNReal := fun q =>
                g (eβ.symm q) * posSimplexAggregateDensity f (eβ.symm q)
              have hGβ : Measurable Gβ := by
                apply Measurable.mul
                · exact hg.comp eβ.symm.measurable
                · unfold posSimplexAggregateDensity
                  fun_prop
              have htarget :
                  (∫⁻ z in posSimplex β r,
                    g z * posSimplexAggregateDensity f z) =
                    ∫⁻ s in Set.Icc (0 : ℝ) r,
                      H s * (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                        Nat.factorial (Fintype.card A - 1)) := by
                calc
                  _ = ∫⁻ z in posSimplex β r, Gβ (eβ z) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex β r)
                    intro z _
                    simp only [Gβ, eβ.symm_apply_apply]
                  _ = ∫⁻ u in posSimplex Aβ r,
                      ∫⁻ z in posSimplex β' (r - ∑ i, u i), Gβ (u, z) :=
                    lintegral_posSimplex_split_pred pβ r Gβ hGβ
                  _ = ∫⁻ u in posSimplex Aβ r,
                      H (∑ i, u i) *
                        (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                          Nat.factorial (Fintype.card A - 1)) := by
                    apply setLIntegral_congr_fun (measurableSet_posSimplex Aβ r)
                    intro u _
                    change (∫⁻ z in posSimplex β' (r - ∑ i, u i), Gβ (u, z)) = _
                    calc
                      _ = ∫⁻ z in posSimplex β' (r - ∑ i, u i),
                          (g (assemble (∑ i, u i) z) *
                            posSimplexAggregateDensity f' z) *
                            (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                              Nat.factorial (Fintype.card A - 1)) := by
                        apply setLIntegral_congr_fun (measurableSet_posSimplex β' _)
                        intro z _
                        change Gβ (u, z) = _
                        rw [show Gβ (u, z) = g (assemble (∑ i, u i) z) *
                            posSimplexAggregateDensity f (assemble (∑ i, u i) z) by
                          simp only [Gβ, heβ]]
                        rw [posSimplexAggregateDensity_split f k]
                        simp only [A]
                        ac_rfl
                      _ = H (∑ i, u i) *
                          (ENNReal.ofReal (∑ i, u i) ^ (Fintype.card A - 1) /
                            Nat.factorial (Fintype.card A - 1)) := by
                        apply lintegral_mul_const'
                        exact ENNReal.div_ne_top (by simp) (by positivity)
                  _ = _ := by
                    have hm : Measurable (fun s => H s *
                        (ENNReal.ofReal s ^ (Fintype.card A - 1) /
                          Nat.factorial (Fintype.card A - 1))) := by fun_prop
                    rw [lintegral_posSimplex_comp_sum r hr _ hm]
                    simp [Aβ, pβ]
              exact hscalar.trans htarget.symm
