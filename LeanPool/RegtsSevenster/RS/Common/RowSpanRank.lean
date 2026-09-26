/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The row span of a matrix over arbitrary index types

A matrix whose rows and columns are indexed by arbitrary types has no
rank in the sense of linear algebra.  Two standard substitutes are the
dimension of the span of its rows and the supremum of the ranks of its
finite submatrices; this module proves them interchangeable in the
bounded form that a rank *hypothesis* uses, so that no cardinal
supremum is needed: the row span has dimension at most `n` exactly
when every finite submatrix has rank at most `n`
(`rank_span_rows_le_iff`).  The same criterion is restated for the row
span presented as the range of `Finsupp.lift`
(`rank_range_lift_le_iff`), which is how the connection matrices of
`RS/Novel/Skein/ConnectionRank.lean` present theirs.

The point of substance is that a finite-dimensional space of functions
on `κ` is separated by finitely many coordinates
(`exists_finset_separating`): that is what makes the row rank of an
infinite matrix visible on a single finite submatrix.
-/

@[expose] public section

namespace RS

variable {K : Type*}

/-! ## Separating a space of functions on finitely many coordinates -/

/-- Restriction of functions on `κ` to a finite set of coordinates. -/
private def restrictTo [Field K] {κ : Type*}
    (T : Finset κ) : (κ → K) →ₗ[K] (T → K) :=
  LinearMap.funLeft K K ((↑) : T → κ)

private theorem separating_aux [Field K] {κ : Type*}
    (n : ℕ) :
    ∀ U : Submodule K (κ → K), FiniteDimensional K U →
      Module.finrank K U ≤ n →
      ∃ T : Finset κ, ∀ w ∈ U, (∀ j ∈ T, w j = 0) → w = 0 := by
  classical
  induction n with
  | zero =>
    intro U _ hrank
    refine ⟨∅, fun w hw _ => ?_⟩
    by_contra hne
    have hbot : (⊥ : Submodule K (κ → K)) < U :=
      bot_lt_iff_ne_bot.2 fun h => hne (by simpa [h] using hw)
    have hlt := Submodule.finrank_lt_finrank_of_lt hbot
    rw [finrank_bot] at hlt
    omega
  | succ n ih =>
    intro U hU hrank
    by_cases hbot : U = ⊥
    · exact ⟨∅, fun w hw _ => by simpa [hbot] using hw⟩
    obtain ⟨w₀, hw₀U, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    obtain ⟨j, hj⟩ : ∃ j, w₀ j ≠ 0 := by
      by_contra h
      exact hw₀ (funext fun j => not_not.1 fun hne => h ⟨j, hne⟩)
    -- Cutting `U` down by one coordinate at which some vector of `U`
    -- is nonzero drops the dimension, so the recursion terminates.
    set U' : Submodule K (κ → K) := U ⊓ LinearMap.ker (LinearMap.proj j)
      with hU'def
    have hlt : U' < U := by
      refine lt_of_le_of_ne inf_le_left fun h => hj ?_
      have hmem : w₀ ∈ U' := by rw [h]; exact hw₀U
      exact LinearMap.mem_ker.1 (Submodule.mem_inf.1 hmem).2
    have : FiniteDimensional K U' :=
      FiniteDimensional.of_injective (Submodule.inclusion (le_of_lt hlt))
        (Submodule.inclusion_injective _)
    have hfr : Module.finrank K U' < Module.finrank K U :=
      Submodule.finrank_lt_finrank_of_lt hlt
    obtain ⟨T', hT'⟩ := ih U' inferInstance (by omega)
    refine ⟨insert j T', fun w hw hvan => hT' w ?_ ?_⟩
    · exact Submodule.mem_inf.2
        ⟨hw, LinearMap.mem_ker.2 (hvan j (Finset.mem_insert_self _ _))⟩
    · exact fun i hi => hvan i (Finset.mem_insert_of_mem hi)

/-- A finite-dimensional space of functions on `κ` is separated by
finitely many coordinates: some finite `T` is such that a vector of the
space vanishing throughout `T` is zero. -/
theorem exists_finset_separating [Field K] {κ : Type*}
    (U : Submodule K (κ → K))
    [FiniteDimensional K U] :
    ∃ T : Finset κ, ∀ w ∈ U, (∀ j ∈ T, w j = 0) → w = 0 :=
  separating_aux (Module.finrank K U) U inferInstance le_rfl

/-! ## Finite submatrices and the row span -/

/-- The submatrix of `M` on the rows `S` and the columns `T`. -/
def submatrixOn {ι : Type*} {κ : Type*}
    (M : ι → κ → K) (S : Finset ι) (T : Finset κ) :
    Matrix S T K :=
  (Matrix.of M).submatrix ((↑) : S → ι) ((↑) : T → κ)

/-- The span of the rows of `M` indexed by a finite set of rows. -/
private noncomputable def rowsOn
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) : Submodule K (κ → K) :=
  Submodule.span K (Set.range fun i : S => M (i : ι))

private theorem rowsOn_le [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) :
    rowsOn M S ≤ Submodule.span K (Set.range M) :=
  Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨(i : ι), rfl⟩)

private instance rowsOn_finiteDimensional
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) :
    FiniteDimensional K (rowsOn M S) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

private theorem span_rows_submatrixOn
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) (T : Finset κ) :
    Submodule.span K (Set.range (submatrixOn M S T).row)
      = Submodule.map (restrictTo T) (rowsOn M S) := by
  rw [rowsOn, ← Submodule.span_image]
  congr 1
  rw [← Set.range_comp]
  rfl

private instance span_rows_finiteDimensional
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) (T : Finset κ) :
    FiniteDimensional K (Submodule.map (restrictTo T) (rowsOn M S)) := by
  rw [← span_rows_submatrixOn]
  exact FiniteDimensional.span_of_finite K (Set.finite_range _)

private theorem rank_submatrixOn
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (S : Finset ι) (T : Finset κ) :
    (submatrixOn M S T).rank
      = Module.finrank K (Submodule.map (restrictTo T) (rowsOn M S)) := by
  rw [Matrix.rank_eq_finrank_span_row, span_rows_submatrixOn]

private theorem card_le_of_independent_in_span
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    {n : ℕ}
    (h : ∀ (S : Finset ι) (T : Finset κ), (submatrixOn M S T).rank ≤ n)
    {σ : Type*} [Fintype σ] (w : σ → (κ → K)) (hw : LinearIndependent K w)
    (hmem : ∀ i, w i ∈ Submodule.span K (Set.range M)) :
    Fintype.card σ ≤ n := by
  classical
  -- The family is written over finitely many rows.
  choose c hc using fun i =>
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hmem i)
  set S : Finset ι := Finset.univ.biUnion fun i => (c i).support with hSdef
  have hwS : ∀ i, w i ∈ rowsOn M S := by
    intro i
    rw [← hc i, Finsupp.sum]
    refine Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span
      ⟨⟨j, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩⟩, rfl⟩
  -- Finitely many columns already separate its span.
  set U := Submodule.span K (Set.range w) with hUdef
  have : FiniteDimensional K U :=
    FiniteDimensional.span_of_finite K (Set.finite_range _)
  have hUle : U ≤ rowsOn M S :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hwS i)
  obtain ⟨T, hT⟩ := exists_finset_separating U
  have hinj : Function.Injective (restrictTo T ∘ₗ U.subtype) := by
    intro x y hxy
    refine Subtype.ext (sub_eq_zero.1 (hT _ (U.sub_mem x.2 y.2) fun j hj => ?_))
    have hj' := congrFun hxy ⟨j, hj⟩
    simpa [restrictTo, sub_eq_zero] using hj'
  have hrange : LinearMap.range (restrictTo T ∘ₗ U.subtype)
      = Submodule.map (restrictTo T) U := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  -- Those rows and columns cut out a submatrix of at least this rank.
  calc Fintype.card σ
      = Module.finrank K U := by rw [hUdef, finrank_span_eq_card hw]
    _ = Module.finrank K (Submodule.map (restrictTo T) U) := by
        rw [← hrange, LinearMap.finrank_range_of_inj hinj]
    _ ≤ Module.finrank K (Submodule.map (restrictTo T) (rowsOn M S)) :=
        Submodule.finrank_mono (Submodule.map_mono hUle)
    _ = (submatrixOn M S T).rank := (rank_submatrixOn M S T).symm
    _ ≤ n := h S T

/-- **The row span and the finite submatrices agree in bounded form.**
The span of the rows of `M` has dimension at most `n` exactly when
every finite submatrix of `M` has rank at most `n`. -/
theorem rank_span_rows_le_iff [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (n : ℕ) :
    Module.rank K (Submodule.span K (Set.range M)) ≤ (n : Cardinal) ↔
      ∀ (S : Finset ι) (T : Finset κ), (submatrixOn M S T).rank ≤ n := by
  constructor
  · -- A finite submatrix's row space is the image of finitely many
    -- rows, so its dimension is at most the whole row span's.
    intro h S T
    rw [rank_submatrixOn]
    refine (Submodule.finrank_map_le _ _).trans ?_
    have hcast :
        (Module.finrank K (rowsOn M S) : Cardinal) ≤ (n : Cardinal) := by
      rw [Module.finrank_eq_rank]
      exact (Submodule.rank_mono (rowsOn_le M S)).trans h
    exact_mod_cast hcast
  · -- An independent finite family in the row span is bounded by
    -- `card_le_of_independent_in_span`.
    intro h
    refine rank_le fun s hs => ?_
    have hcard := card_le_of_independent_in_span M h
      (fun i : ↥s => ((i : ↥(Submodule.span K (Set.range M))) : κ → K))
      (by exact hs.map' _ (Submodule.ker_subtype _))
      (fun i => (i : ↥(Submodule.span K (Set.range M))).2)
    rwa [Fintype.card_coe] at hcard

/-- The range of `Finsupp.lift` at `M` is the span of the rows of
`M`. -/
theorem range_lift_eq_span_rows
    [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K) :
    LinearMap.range (Finsupp.lift (κ → K) K ι M)
      = Submodule.span K (Set.range M) := by
  have hlift : (Finsupp.lift (κ → K) K ι M) = Finsupp.linearCombination K M :=
    LinearMap.ext fun g => by
      rw [Finsupp.lift_apply, Finsupp.linearCombination_apply]
  rw [hlift, Finsupp.range_linearCombination]

/-- **The bounded row-rank criterion**, for the row span presented as
the range of `Finsupp.lift`. -/
theorem rank_range_lift_le_iff [Field K] {ι : Type*} {κ : Type*} (M : ι → κ → K)
    (n : ℕ) :
    Module.rank K (LinearMap.range (Finsupp.lift (κ → K) K ι M))
        ≤ (n : Cardinal) ↔
      ∀ (S : Finset ι) (T : Finset κ), (submatrixOn M S T).rank ≤ n := by
  rw [range_lift_eq_span_rows]
  exact rank_span_rows_le_iff M n

end RS
