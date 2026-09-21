/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Jankov-von Neumann Uniformization — Full Proof

  Reference: Kechris, Classical Descriptive Set Theory, §2 + Theorem 18.1.

  The infrastructure is generic: domain X (Polish), codomain ℕ → ℕ.
  The leftmost branch operates only on the codomain.
-/
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.AnalyticSigmaAlgebra

/-! ## Part I: Fibers (generic domain X, codomain ℕᴺ) -/

open Set Topology MeasureTheory

noncomputable section

variable {X : Type*} [TopologicalSpace X]



/-- The fiber of a subset of the product with Baire space over the given point. -/
def closedFiberG (F : Set (X × (ℕ → ℕ))) (x : X) : Set (ℕ → ℕ) :=
  { y | (x, y) ∈ F }

omit [TopologicalSpace X] in
theorem closedFiberG_nonempty_iff (F : Set (X × (ℕ → ℕ))) (x : X) :
    (closedFiberG F x).Nonempty ↔ x ∈ Prod.fst '' F := by
  constructor
  · rintro ⟨y, hy⟩; exact ⟨(x, y), hy, rfl⟩
  · rintro ⟨⟨x', y⟩, hm, rfl⟩; exact ⟨y, hm⟩

theorem isClosed_closedFiberG {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X) :
    IsClosed (closedFiberG F x) :=
  hF.preimage (Continuous.prodMk continuous_const continuous_id)

/-! ## Part II: Leftmost branch (generic domain) -/

/-- The fiber restricted to sequences agreeing with a prescribed prefix. -/
def fiberRestNG (F : Set (X × (ℕ → ℕ))) (x : X) (f : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  { y | (x, y) ∈ F ∧ ∀ i < n, y i = f i }

omit [TopologicalSpace X] in
theorem fiberRestNG_zero (F : Set (X × (ℕ → ℕ))) (x : X) (f : ℕ → ℕ) :
    fiberRestNG F x f 0 = closedFiberG F x := by
  ext y; simp [fiberRestNG, closedFiberG]

omit [TopologicalSpace X] in
theorem exists_extNG {F : Set (X × (ℕ → ℕ))} {x : X} {f : ℕ → ℕ} {n : ℕ}
    (hne : (fiberRestNG F x f n).Nonempty) :
    ∃ k, (fiberRestNG F x (Function.update f n k) (n + 1)).Nonempty := by
  obtain ⟨y, hy_mem, hy_ext⟩ := hne
  refine ⟨y n, y, hy_mem, fun i hi => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [Function.update_of_ne (by omega)]; exact hy_ext i h
  · subst h; simp [Function.update_self]

open scoped Classical in
/-- Recursively choose the smallest extendible next coordinate in each nonempty fiber. -/
def leftmostAuxG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    (n : ℕ) → { f : ℕ → ℕ // (fiberRestNG F x f n).Nonempty }
  | 0 => ⟨fun _ => 0, fiberRestNG_zero F x _ ▸ h₀⟩
  | n + 1 =>
    let ⟨f, hf⟩ := leftmostAuxG F x h₀ n
    ⟨Function.update f n (Nat.find (exists_extNG hf)),
     Nat.find_spec (exists_extNG hf)⟩

open scoped Classical in
/-- The sequence obtained by choosing the smallest extendible coordinate at every step. -/
def leftmostBranchG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n : ℕ) : ℕ :=
  Nat.find (exists_extNG (leftmostAuxG F x h₀ n).2)

omit [TopologicalSpace X] in
theorem leftmostAuxG_eq (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    ∀ n i, i < n → (leftmostAuxG F x h₀ n).val i = leftmostBranchG F x h₀ i := by
  intro n; induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    simp only [leftmostAuxG, leftmostBranchG]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [Function.update_of_ne (by omega)]; exact ih i h
    · subst h; simp [Function.update_self]

/-- Choose a fiber element extending the specified finite prefix of the leftmost branch. -/
def leftmostWitnessG (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n : ℕ) : ℕ → ℕ :=
  (leftmostAuxG F x h₀ n).2.some

omit [TopologicalSpace X] in
theorem leftmostWitnessG_mem (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n) :
    leftmostWitnessG F x h₀ n ∈ closedFiberG F x :=
  ((leftmostAuxG F x h₀ n).2.some_mem).1

omit [TopologicalSpace X] in
theorem leftmostWitnessG_agrees (F : Set (X × (ℕ → ℕ))) (x : X) (h₀ n i) (hi : i < n) :
    leftmostWitnessG F x h₀ n i = leftmostBranchG F x h₀ i := by
  have := ((leftmostAuxG F x h₀ n).2.some_mem).2 i hi
  rw [leftmostAuxG_eq F x h₀ n i hi] at this; exact this

theorem leftmostBranchG_mem
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) :
    (x, leftmostBranchG F x h₀) ∈ F :=
  (isClosed_closedFiberG hF x).mem_of_tendsto
    (tendsto_pi_nhds.mpr fun i => by
      rw [congr_fun (nhds_discrete ℕ) _]
      exact Filter.tendsto_pure.mpr (Filter.eventually_atTop.mpr
        ⟨i + 1, fun n hn => leftmostWitnessG_agrees F x h₀ n i (by omega)⟩))
    (Filter.Eventually.of_forall (leftmostWitnessG_mem F x h₀))

omit [TopologicalSpace X] in
open scoped Classical in
theorem leftmostBranchG_least (F : Set (X × (ℕ → ℕ))) (x : X)
    (h₀ : (closedFiberG F x).Nonempty) (n k : ℕ)
    (hk : k < leftmostBranchG F x h₀ n) :
    ¬(fiberRestNG F x (Function.update (leftmostAuxG F x h₀ n).val n k) (n + 1)).Nonempty :=
  Nat.find_min (exists_extNG (leftmostAuxG F x h₀ n).2) hk

/-! ## Part III: Fiber-cylinder projections (generic domain) -/

/-- The domain points whose fibers meet a prescribed finite cylinder. -/
def projFiberCylNG (F : Set (X × (ℕ → ℕ))) (f : ℕ → ℕ) (n : ℕ) : Set X :=
  { x | (fiberRestNG F x f n).Nonempty }

theorem analyticSet_projFiberCylNG [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (f : ℕ → ℕ) (n : ℕ) :
    AnalyticSet (projFiberCylNG F f n) := by
  have : projFiberCylNG F f n =
      Prod.fst '' (F ∩ (univ ×ˢ ⋂ (i : Fin n), { y : ℕ → ℕ | y i = f i })) := by
    ext x; simp only [projFiberCylNG, fiberRestNG, mem_ofPred_eq, mem_image, Prod.exists,
      mem_inter_iff, mem_prod, mem_univ, true_and, mem_iInter]
    constructor
    · rintro ⟨y, h1, h2⟩; exact ⟨x, y, ⟨h1, fun ⟨i, hi⟩ => h2 i hi⟩, rfl⟩
    · rintro ⟨_, y, ⟨h1, h2⟩, rfl⟩; exact ⟨y, h1, fun i hi => h2 ⟨i, hi⟩⟩
  rw [this]
  exact (hF.inter (IsClosed.prod isClosed_univ (isClosed_iInter fun (i : Fin n) =>
    isClosed_eq (continuous_apply (i : ℕ)) continuous_const))
    ).analyticSet.image_of_continuous continuous_fst

/-! ## Part IV: Closed uniformizer (generic domain) -/

open scoped Classical in
/-- Select the leftmost branch in a nonempty fiber, with a fixed fallback outside the projection. -/
def closedUniformizerG (F : Set (X × (ℕ → ℕ))) (_hF : IsClosed F)
    (hne : F.Nonempty) : X → (ℕ → ℕ) :=
  fun x => if h : (closedFiberG F x).Nonempty then leftmostBranchG F x h
            else hne.some.2

theorem closedUniformizerG_selection
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    {x : X} (hx : x ∈ Prod.fst '' F) :
    (x, closedUniformizerG F hF hne x) ∈ F := by
  simp only [closedUniformizerG, dite_eq_left ((closedFiberG_nonempty_iff F x).mpr hx)]
  exact leftmostBranchG_mem hF x _

open scoped Classical in
theorem closedUniformizerG_cylinder_eq
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } =
      (projFiberCylNG F f n ∩
        ⋂ (m : Fin n), ⋂ (j : Fin (f m)),
          (projFiberCylNG F (Function.update f m j) (↑m + 1))ᶜ) ∪
      ((Prod.fst '' F)ᶜ ∩ { _x | ∀ i < n, hne.some.2 i = f i }) := by
  ext x
  simp only [mem_ofPred_eq, mem_union, mem_inter_iff, mem_iInter, mem_compl_iff,
    projFiberCylNG, fiberRestNG, mem_ofPred_eq]
  constructor
  · intro hx
    by_cases hcf : (closedFiberG F x).Nonempty
    · left
      have hx' : ∀ i < n, leftmostBranchG F x hcf i = f i := by
        intro i hi; have := hx i hi
        simp only [closedUniformizerG, dite_eq_left hcf] at this; exact this
      constructor
      · have := (leftmostAuxG F x hcf n).2; rw [fiberRestNG] at this
        obtain ⟨y, hy_mem, hy_ext⟩ := this
        exact ⟨y, hy_mem, fun i hi =>
          (hy_ext i hi).trans ((leftmostAuxG_eq F x hcf n i hi).trans (hx' i hi))⟩
      · intro ⟨m, hm⟩ ⟨j, hj⟩ hmem
        apply leftmostBranchG_least F x hcf m j (by rw [hx' m hm]; exact hj)
        obtain ⟨y, hy_mem, hy_ext⟩ := hmem
        refine ⟨y, hy_mem, fun i hi => ?_⟩
        have hye := hy_ext i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
        · rw [Function.update_of_ne (show (i : ℕ) ≠ m from by omega)] at hye ⊢
          rwa [leftmostAuxG_eq F x hcf m i h, hx' i (by omega)]
        · subst h; rwa [Function.update_self] at hye ⊢
    · right
      refine ⟨fun h => hcf ((closedFiberG_nonempty_iff F x).mpr h), ?_⟩
      intro i hi
      have hvalue := hx i hi
      simpa only [closedUniformizerG, dite_eq_right hcf] using hvalue
  · rintro (⟨hproj, hmin⟩ | ⟨hnotproj, hdef⟩)
    · intro i hi
      simp only [closedUniformizerG]
      split
      · next hcf =>
        suffices key : ∀ j < n, leftmostBranchG F x hcf j = f j from key i hi
        intro j hj
        induction j using Nat.strongRecOn with
        | _ j IH =>
        apply le_antisymm
        · apply Nat.find_min'
          obtain ⟨y, hy_mem, hy_ext⟩ := hproj
          exact ⟨y, hy_mem, fun k hk => by
            rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt | heq
            · rw [Function.update_of_ne (by omega),
                   leftmostAuxG_eq F x hcf j k hlt, IH k hlt (by omega)]
              exact hy_ext k (by omega)
            · rw [heq, Function.update_self]; exact hy_ext _ (by omega)⟩
        · by_contra hlt; rw [not_le] at hlt
          have hspec := Nat.find_spec (exists_extNG (leftmostAuxG F x hcf j).2)
          obtain ⟨y', hy'_mem, hy'_ext⟩ := hspec
          have hmemN : x ∈ projFiberCylNG F
              (Function.update f j (leftmostBranchG F x hcf j)) (j + 1) :=
            ⟨y', hy'_mem, fun k hk => by
              have hye := hy'_ext k hk
              rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hlt' | heq
              · rw [Function.update_of_ne (by omega)] at hye ⊢
                rw [leftmostAuxG_eq F x hcf j k hlt', IH k hlt' (by omega)] at hye
                exact hye
              · rw [heq, Function.update_self] at hye ⊢; exact hye⟩
          exact absurd hmemN (hmin ⟨j, hj⟩ ⟨leftmostBranchG F x hcf j, hlt⟩)
      · next hncf =>
        exfalso; apply hncf
        obtain ⟨y, hy_mem, _⟩ := hproj; exact ⟨y, hy_mem⟩
    · intro i hi
      simp only [closedUniformizerG, dite_eq_right (by
        intro h; exact hnotproj ((closedFiberG_nonempty_iff F x).mp h))]
      exact hdef i hi

theorem closedUniformizerG_cylinder_measurable [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty)
    (f : ℕ → ℕ) (n : ℕ) :
    @MeasurableSet _ (analyticMeasurableSpace X)
      { x | ∀ i < n, closedUniformizerG F hF hne x i = f i } := by
  rw [closedUniformizerG_cylinder_eq hF hne f n]
  apply MeasurableSet.union
  · apply MeasurableSet.inter
    · exact (analyticSet_projFiberCylNG hF f n).mem_analyticMeasurableSpace
    · exact MeasurableSet.iInter fun m =>
        MeasurableSet.iInter fun j =>
          (analyticSet_projFiberCylNG hF _ _).compl_mem_analyticMeasurableSpace
  · apply MeasurableSet.inter
    · exact (hF.analyticSet.image_of_continuous continuous_fst).compl_mem_analyticMeasurableSpace
    · by_cases h : ∀ i < n, hne.some.2 i = f i
      · have : {x : X | ∀ i < n, hne.some.2 i = f i} = univ := by
          ext; simp only [mem_ofPred_eq, mem_univ, iff_true]; exact fun _ hh => h _ hh
        rw [this]; exact @MeasurableSet.univ _ (analyticMeasurableSpace X)
      · have : {x : X | ∀ i < n, hne.some.2 i = f i} = ∅ := by
          ext; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
          exact fun h' => h (fun i hi => h' i hi)
        rw [this]; exact @MeasurableSet.empty _ (analyticMeasurableSpace X)

/-! ## Part V: σ(Σ₁¹)-measurability (generic domain) -/

theorem closedUniformizerG_analyticallyMeasurable [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    AnalyticallyMeasurable (closedUniformizerG F hF hne) := by
  have hgen : borel (ℕ → ℕ) = MeasurableSpace.generateFrom
      { s | ∃ (x : ℕ → ℕ) (n : ℕ), s = PiNat.cylinder x n } :=
    (PiNat.isTopologicalBasis_cylinders (E := fun _ => ℕ)).borel_eq_generateFrom
  rw [AnalyticallyMeasurable, hgen]
  intro s hs
  induction hs with
  | basic s hs =>
    obtain ⟨f, n, rfl⟩ := hs
    have : closedUniformizerG F hF hne ⁻¹' PiNat.cylinder f n =
        {x | ∀ i < n, closedUniformizerG F hF hne x i = f i} := by
      ext x; simp only [mem_preimage, PiNat.mem_cylinder_iff, mem_ofPred_eq]
    rw [this]; exact closedUniformizerG_cylinder_measurable hF hne f n
  | empty => exact @MeasurableSet.empty _ (analyticMeasurableSpace X)
  | compl _ _ ih => exact ih.compl
  | iUnion _ _ ih => rw [preimage_iUnion]; exact .iUnion ih

/-! ## Part VI: JVN for closed sets (generic domain) -/

theorem jvn_closedG [PolishSpace X]
    {F : Set (X × (ℕ → ℕ))} (hF : IsClosed F) (hne : F.Nonempty) :
    ∃ (φ : X → (ℕ → ℕ)), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' F, (x, φ x) ∈ F :=
  ⟨closedUniformizerG F hF hne,
   closedUniformizerG_analyticallyMeasurable hF hne,
   fun _ hx => closedUniformizerG_selection hF hne hx⟩

/-! ## Part VII: JVN for analytic sets in general Polish spaces -/

/-- **Jankov–von Neumann Uniformization Theorem** (Kechris 18.1).

For P analytic in X × Y (Polish spaces), there exists a σ(Σ₁¹)-measurable
function φ : X → Y uniformizing P on its projection. -/
theorem jankov_von_neumann
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X]
    (P : Set (X × Y)) (hP : AnalyticSet P) (hne : P.Nonempty) :
    ∃ (φ : X → Y), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P := by
  rw [AnalyticSet] at hP
  rcases hP with rfl | ⟨π, hπ_cont, hπ_range⟩
  · exact absurd hne (by simp)
  -- F = {(x, z) ∈ X × ℕᴺ | fst(π(z)) = x} is closed
  let F : Set (X × (ℕ → ℕ)) := { p | Prod.fst (π p.2) = p.1 }
  have hF_closed : IsClosed F :=
    isClosed_eq (hπ_cont.fst.comp continuous_snd) continuous_fst
  have hF_ne : F.Nonempty := by
    obtain ⟨⟨x, y⟩, hxy⟩ := hne
    obtain ⟨z, hz⟩ := (hπ_range ▸ hxy : (x, y) ∈ range π)
    exact ⟨(x, z), show Prod.fst (π z) = x from congr_arg Prod.fst hz⟩
  -- Apply generalized jvn_closed: get ψ : X → ℕᴺ
  obtain ⟨ψ, hψ_meas, hψ_sel⟩ := jvn_closedG hF_closed hF_ne
  -- φ(x) = snd(π(ψ(x)))
  refine ⟨fun x => Prod.snd (π (ψ x)),
    hψ_meas.comp_continuous (hπ_cont.snd.comp continuous_id), fun x hx => ?_⟩
  have hx_projF : x ∈ Prod.fst '' F := by
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    obtain ⟨z, hz⟩ := (hπ_range ▸ hab : (a, b) ∈ range π)
    exact ⟨(a, z), show Prod.fst (π z) = a from congr_arg Prod.fst hz, rfl⟩
  have hfst : Prod.fst (π (ψ x)) = x := hψ_sel x hx_projF
  rw [show (x, Prod.snd (π (ψ x))) = π (ψ x) from Prod.ext hfst.symm rfl, ← hπ_range]
  exact mem_range_self _

end
