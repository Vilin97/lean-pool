/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.PairedCertificate

/-! # Cluster Product -/

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

theorem prod_monomial
    {σ ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι → σ →₀ ℕ) (w : ι → ℝ) :
    ∏ i ∈ s, monomial (e i) (w i) =
      monomial (∑ i ∈ s, e i) (∏ i ∈ s, w i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih, monomial_mul]

/-- An independent injection of the rows of each cluster into the columns.
Choices belonging to different clusters are not required to have disjoint
images; the column selector enforces that condition later. -/
abbrev ClusterChoice {n : ℕ} (C : RowClustering n) :=
  (c : C.Cluster) → Fin (C.size c) ↪ Fin n

/-- Aggregate map from all row slots to columns. -/
def clusterChoiceMap
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) :
    (Σ c, Fin (C.size c)) → Fin n :=
  fun s ↦ f s.1 s.2

/-- A cluster choice compatible with the column selector uses every column
exactly once. -/
def IsGlobalClusterChoice
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) : Prop :=
  Function.Bijective (clusterChoiceMap C f)

abbrev GlobalClusterChoice {n : ℕ} (C : RowClustering n) :=
  {f : ClusterChoice C // IsGlobalClusterChoice C f}

/-- A permutation (columns to rows) induces the column choice of every row
slot by applying the inverse permutation to its row. -/
noncomputable def permutationClusterChoice
    {n : ℕ} (C : RowClustering n) (σ : Equiv.Perm (Fin n)) :
    ClusterChoice C :=
  fun c ↦
    { toFun := fun k ↦ σ.symm (C.rows ⟨c, k⟩)
      inj' := by
        intro k k' h
        have hs : (⟨c, k⟩ : Σ c, Fin (C.size c)) = ⟨c, k'⟩ :=
          C.rows.injective (σ.symm.injective h)
        simpa using hs }

@[simp]
theorem permutationClusterChoice_apply
    {n : ℕ} (C : RowClustering n) (σ : Equiv.Perm (Fin n))
    (c : C.Cluster) (k : Fin (C.size c)) :
    permutationClusterChoice C σ c k = σ.symm (C.rows ⟨c, k⟩) := rfl

theorem permutationClusterChoice_global
    {n : ℕ} (C : RowClustering n) (σ : Equiv.Perm (Fin n)) :
    IsGlobalClusterChoice C (permutationClusterChoice C σ) := by
  change Function.Bijective (fun s ↦ σ.symm (C.rows s))
  exact σ.symm.bijective.comp C.rows.bijective

/-- Global cluster choices are exactly permutations. -/
noncomputable def permutationGlobalClusterChoiceEquiv
    {n : ℕ} (C : RowClustering n) :
    Equiv.Perm (Fin n) ≃ GlobalClusterChoice C where
  toFun σ := ⟨permutationClusterChoice C σ,
    permutationClusterChoice_global C σ⟩
  invFun f :=
    (Equiv.ofBijective (clusterChoiceMap C f.1) f.2).symm.trans C.rows
  left_inv σ := by
    apply Equiv.ext
    intro j
    let e := Equiv.ofBijective
      (clusterChoiceMap C (permutationClusterChoice C σ))
      (permutationClusterChoice_global C σ)
    change C.rows (e.symm j) = σ j
    apply σ.symm.injective
    rw [σ.symm_apply_apply]
    have he := e.apply_symm_apply j
    change clusterChoiceMap C (permutationClusterChoice C σ) (e.symm j) = j at he
    exact he
  right_inv f := by
    apply Subtype.ext
    funext c
    apply Function.Embedding.ext
    intro k
    simp [clusterChoiceMap, permutationClusterChoice]

noncomputable instance globalClusterChoiceFintype
    {n : ℕ} (C : RowClustering n) : Fintype (GlobalClusterChoice C) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n))
    (permutationGlobalClusterChoiceEquiv C)

/-- Exponent vector contributed by a family of independent cluster choices. -/
noncomputable def clusterChoiceExponent
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) :
    C.Cluster × Fin n →₀ ℕ :=
  ∑ c, ∑ k, Finsupp.single (c, f c k) 1

@[simp]
theorem clusterChoiceExponent_apply
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C)
    (c : C.Cluster) (j : Fin n) :
    clusterChoiceExponent C f (c, j) =
      ((Finset.univ : Finset (Fin (C.size c))).filter
        (fun k ↦ f c k = j)).card := by
  classical
  simp [clusterChoiceExponent, Finsupp.single_apply]
  rw [Finset.sum_eq_single c]
  · congr 1
    ext k
    simp
  · intro b _ hbc
    simp [hbc]
  · simp

/-- A cluster-choice monomial lies in the selector support exactly when the
aggregate choice is a bijection from row slots to columns. -/
theorem exists_selectorExponent_eq_iff_global
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) :
    (∃ h : Fin n → C.Cluster,
        clusterChoiceExponent C f = selectorExponent h) ↔
      IsGlobalClusterChoice C f := by
  classical
  constructor
  · rintro ⟨h, he⟩
    constructor
    · rintro ⟨c, k⟩ ⟨d, l⟩ hsame
      have hcpos : 0 < clusterChoiceExponent C f (c, f c k) := by
        rw [clusterChoiceExponent_apply]
        exact Finset.card_pos.mpr ⟨k, by simp⟩
      have hdpos : 0 < clusterChoiceExponent C f (d, f d l) := by
        rw [clusterChoiceExponent_apply]
        exact Finset.card_pos.mpr ⟨l, by simp⟩
      rw [he, selectorExponent_apply] at hcpos hdpos
      have hc : c = h (f c k) := by
        by_contra hne
        simp [hne] at hcpos
      have hd : d = h (f d l) := by
        by_contra hne
        simp [hne] at hdpos
      have hcd : c = d := by
        change f c k = f d l at hsame
        rw [hc, hd, hsame]
      subst d
      have hkl : k = l := (f c).injective hsame
      subst l
      rfl
    · intro j
      have hone : clusterChoiceExponent C f (h j, j) = 1 := by
        rw [he, selectorExponent_apply]
        simp
      rw [clusterChoiceExponent_apply] at hone
      have hnonempty :
          ((Finset.univ : Finset (Fin (C.size (h j)))).filter
            (fun k ↦ f (h j) k = j)).Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro hempty
        rw [hempty] at hone
        simp at hone
      obtain ⟨k, hk⟩ := hnonempty
      exact ⟨⟨h j, k⟩, (Finset.mem_filter.mp hk).2⟩
  · intro hglobal
    let e := Equiv.ofBijective (clusterChoiceMap C f) hglobal
    refine ⟨fun j ↦ (e.symm j).1, ?_⟩
    ext v
    rcases v with ⟨c, j⟩
    rw [clusterChoiceExponent_apply, selectorExponent_apply]
    by_cases hc : c = (e.symm j).1
    · subst c
      have hs :
          ((Finset.univ : Finset (Fin (C.size (e.symm j).1))).filter
            (fun k ↦ f (e.symm j).1 k = j)) =
            {(e.symm j).2} := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        constructor
        · intro hk
          have hmaps : clusterChoiceMap C f ⟨(e.symm j).1, k⟩ =
              clusterChoiceMap C f (e.symm j) := by
            change f (e.symm j).1 k = clusterChoiceMap C f (e.symm j)
            rw [hk]
            exact (e.apply_symm_apply j).symm
          have hslots : (⟨(e.symm j).1, k⟩ : Σ c, Fin (C.size c)) = e.symm j :=
            e.injective hmaps
          have hslots' :
              (⟨(e.symm j).1, k⟩ : Σ c, Fin (C.size c)) =
                ⟨(e.symm j).1, (e.symm j).2⟩ :=
            hslots.trans (Sigma.eta (e.symm j)).symm
          exact eq_of_heq (Sigma.mk.inj_iff.mp hslots').2
        · intro hk
          subst k
          have he := e.apply_symm_apply j
          change f (e.symm j).1 (e.symm j).2 = j at he
          exact he
      rw [hs]
      simp
    · have hs :
          ((Finset.univ : Finset (Fin (C.size c))).filter
            (fun k ↦ f c k = j)) = ∅ := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro hk
          have hmaps : clusterChoiceMap C f ⟨c, k⟩ =
              clusterChoiceMap C f (e.symm j) := by
            change f c k = clusterChoiceMap C f (e.symm j)
            rw [hk]
            exact (e.apply_symm_apply j).symm
          have hslots : (⟨c, k⟩ : Σ c, Fin (C.size c)) = e.symm j :=
            e.injective hmaps
          exact (hc (congrArg Sigma.fst hslots)).elim
        · simp
      rw [hs]
      simp [hc]

theorem sum_selector_matches_choice_of_global
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) (w : ℝ)
    (hg : IsGlobalClusterChoice C f) :
    (∑ h : Fin n → C.Cluster,
        if clusterChoiceExponent C f = selectorExponent h then w else 0) = w := by
  classical
  obtain ⟨h, he⟩ := (exists_selectorExponent_eq_iff_global C f).mpr hg
  rw [Finset.sum_eq_single h]
  · simp [he]
  · intro h' _ hh'
    have hne : clusterChoiceExponent C f ≠ selectorExponent h' := by
      intro he'
      apply hh'
      exact (selectorExponent_injective (he.symm.trans he')).symm
    simp [hne]
  · simp

theorem sum_selector_matches_choice_of_not_global
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) (w : ℝ)
    (hg : ¬IsGlobalClusterChoice C f) :
    (∑ h : Fin n → C.Cluster,
        if clusterChoiceExponent C f = selectorExponent h then w else 0) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro h _
  have hne : clusterChoiceExponent C f ≠ selectorExponent h := by
    intro he
    exact hg ((exists_selectorExponent_eq_iff_global C f).mp ⟨h, he⟩)
  simp [hne]

/-- Matrix weight contributed by a family of independent cluster choices. -/
noncomputable def clusterChoiceWeight
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (f : ClusterChoice C) : ℝ :=
  ∏ c, ∏ k, A (C.rows ⟨c, k⟩) (f c k)

theorem sum_clusterSizes_eq
    {n : ℕ} (C : RowClustering n) :
    (∑ c, C.size c) = n := by
  calc
    (∑ c, C.size c) = ∑ c, Fintype.card (Fin (C.size c)) := by simp
    _ = Fintype.card (Σ c, Fin (C.size c)) := Fintype.card_sigma.symm
    _ = Fintype.card (Fin n) := Fintype.card_congr C.rows
    _ = n := Fintype.card_fin n

theorem clusterChoiceExponent_degree
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C) :
    Finsupp.degree (clusterChoiceExponent C f) = n := by
  rw [clusterChoiceExponent, map_sum]
  simp [map_sum, Finsupp.degree_single, sum_clusterSizes_eq C]

theorem clusterChoiceExponent_le_one
    {n : ℕ} (C : RowClustering n) (f : ClusterChoice C)
    (v : C.Cluster × Fin n) :
    clusterChoiceExponent C f v ≤ 1 := by
  rcases v with ⟨c, j⟩
  rw [clusterChoiceExponent_apply]
  apply Finset.card_le_one.mpr
  intro k hk l hl
  exact (f c).injective ((Finset.mem_filter.mp hk).2.trans
    (Finset.mem_filter.mp hl).2.symm)

theorem clusterChoiceWeight_permutation
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (σ : Equiv.Perm (Fin n)) :
    clusterChoiceWeight A C (permutationClusterChoice C σ) =
      ∏ j, A (σ j) j := by
  rw [clusterChoiceWeight]
  calc
    (∏ c, ∏ k, A (C.rows ⟨c, k⟩)
        (permutationClusterChoice C σ c k)) =
        ∏ s : Σ c, Fin (C.size c),
          A (C.rows s) (σ.symm (C.rows s)) := by
            rw [Fintype.prod_sigma]
            rfl
    _ = ∏ i, A i (σ.symm i) :=
      Equiv.prod_comp C.rows (fun i ↦ A i (σ.symm i))
    _ = ∏ j, A (σ j) j := by
      symm
      simpa using Equiv.prod_comp σ (fun i ↦ A i (σ.symm i))

theorem sum_globalClusterChoiceWeight_eq_permanent
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    (∑ f : GlobalClusterChoice C, clusterChoiceWeight A C f.1) =
      Matrix.permanent A := by
  rw [Matrix.permanent]
  symm
  calc
    (∑ σ : Equiv.Perm (Fin n), ∏ j, A (σ j) j) =
        ∑ σ : Equiv.Perm (Fin n),
          clusterChoiceWeight A C
            (permutationGlobalClusterChoiceEquiv C σ).1 := by
              apply Finset.sum_congr rfl
              intro σ _
              exact (clusterChoiceWeight_permutation A C σ).symm
    _ = ∑ f : GlobalClusterChoice C, clusterChoiceWeight A C f.1 :=
      Equiv.sum_comp (permutationGlobalClusterChoiceEquiv C)
        (fun f ↦ clusterChoiceWeight A C f.1)

/-- The polynomial for one row cluster.  Its monomials inject the rows in the
cluster into distinct columns.  For clusters of sizes one and two these are,
respectively, the singleton linear form and the pair polynomial of the paper. -/
noncomputable def rowClusterPolynomial
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) : MvPolynomial (C.Cluster × Fin n) ℝ :=
  ∑ f : Fin (C.size c) ↪ Fin n,
    monomial (∑ k, Finsupp.single (c, f k) 1)
      (∏ k, A (C.rows ⟨c, k⟩) (f k))

/-- The same injection polynomial before placing its variables in a named
cluster. -/
noncomputable def injectionPolynomial
    {m n : ℕ} (B : Fin m → Fin n → ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ f : Fin m ↪ Fin n,
    monomial (∑ k, Finsupp.single (f k) 1)
      (∏ k, B k (f k))

theorem injectionPolynomial_nonnegativeCoefficients
    {m n : ℕ} {B : Fin m → Fin n → ℝ}
    (hB : ∀ k j, 0 ≤ B k j) :
    HasNonnegativeCoefficients (injectionPolynomial B) := by
  intro d
  rw [injectionPolynomial, coeff_sum]
  apply Finset.sum_nonneg
  intro f _
  rw [coeff_monomial]
  split
  · exact Finset.prod_nonneg fun k _ ↦ hB k (f k)
  · exact le_rfl

theorem rowClusterPolynomial_eq_rename_injectionPolynomial
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) :
    rowClusterPolynomial A C c =
      MvPolynomial.rename (fun j : Fin n ↦ (c, j))
        (injectionPolynomial (fun k j ↦ A (C.rows ⟨c, k⟩) j)) := by
  rw [rowClusterPolynomial, injectionPolynomial, map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [rename_monomial]
  have hexp :
      Finsupp.mapDomain (fun j : Fin n ↦ (c, j))
          (∑ k, Finsupp.single (f k) 1) =
        ∑ k, Finsupp.single (c, f k) 1 := by
    simpa only [Finsupp.mapDomain_single,
      Finsupp.mapDomain.addMonoidHom_apply] using
      map_sum (Finsupp.mapDomain.addMonoidHom
        (fun j : Fin n ↦ (c, j)))
        (fun k ↦ Finsupp.single (f k) 1) Finset.univ
  rw [hexp]

/-- The full cluster product `p` in paper equation (10). -/
noncomputable def rowClusterProduct
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    MvPolynomial (C.Cluster × Fin n) ℝ :=
  ∏ c, rowClusterPolynomial A C c

/-- Expanding the product makes the independent choice made by every cluster
explicit.  Collisions between different clusters remain present here. -/
theorem rowClusterProduct_eq_sum_choices
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    rowClusterProduct A C =
      ∑ f : ClusterChoice C,
        monomial (clusterChoiceExponent C f) (clusterChoiceWeight A C f) := by
  simp only [rowClusterProduct, rowClusterPolynomial]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [clusterChoiceExponent, clusterChoiceWeight]
  simpa using prod_monomial (Finset.univ : Finset C.Cluster)
    (fun c ↦ ∑ k, Finsupp.single (c, f c k) 1)
    (fun c ↦ ∏ k, A (C.rows ⟨c, k⟩) (f c k))

theorem rowClusterPolynomial_isHomogeneous
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (c : C.Cluster) :
    (rowClusterPolynomial A C c).IsHomogeneous (C.size c) := by
  rw [rowClusterPolynomial]
  apply MvPolynomial.IsHomogeneous.sum
  intro f _
  apply isHomogeneous_monomial
  rw [map_sum]
  simp [Finsupp.degree_single]

theorem rowClusterProduct_isHomogeneous
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    (rowClusterProduct A C).IsHomogeneous n := by
  rw [rowClusterProduct]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (rowClusterPolynomial A C) C.size
    (fun c _ ↦ rowClusterPolynomial_isHomogeneous A C c)
  simpa only [sum_clusterSizes_eq C] using h

theorem rowClusterProduct_nonnegativeCoefficients
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    (hA : Matrix.Nonnegative A) :
    HasNonnegativeCoefficients (rowClusterProduct A C) := by
  intro d
  rw [rowClusterProduct_eq_sum_choices, coeff_sum]
  apply Finset.sum_nonneg
  intro f _
  rw [coeff_monomial]
  split
  · exact Finset.prod_nonneg fun c _ ↦
      Finset.prod_nonneg fun k _ ↦ hA (C.rows ⟨c, k⟩) (f c k)
  · exact le_rfl

theorem rowClusterProduct_isMultiaffine
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    IsMultiaffine (rowClusterProduct A C) := by
  intro v
  rw [rowClusterProduct_eq_sum_choices]
  refine (degreeOf_sum_le v _ _).trans (Finset.sup_le ?_)
  intro f _
  by_cases hw : clusterChoiceWeight A C f = 0
  · simp [hw]
  · rw [degreeOf_monomial_eq _ _ hw]
    exact clusterChoiceExponent_le_one C f v

theorem rowClusterProduct_isRealStable_of_factors
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n)
    (hstable : ∀ c, IsRealStable (rowClusterPolynomial A C c)) :
    IsRealStable (rowClusterProduct A C) := by
  intro z hz
  rw [rowClusterProduct, MvPolynomial.eval₂_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro c _
  exact hstable c z hz

/- Paper equation (12), now for the actual product of cluster factors rather
than for its selector-compatible truncation.  Independent cluster choices
that collide at a column disappear from the coefficient pairing; the
remaining choices are exactly permutations. -/
theorem coefficientInnerProduct_rowClusterProduct_eq_permanent
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : RowClustering n) :
    coefficientInnerProduct (rowClusterProduct A C)
      (columnSelector C.Cluster (Fin n)) = Matrix.permanent A := by
  classical
  rw [coefficientInnerProduct_columnSelector,
    rowClusterProduct_eq_sum_choices]
  simp_rw [coeff_sum, coeff_monomial]
  rw [Finset.sum_comm]
  calc
    (∑ f : ClusterChoice C, ∑ h : Fin n → C.Cluster,
        if clusterChoiceExponent C f = selectorExponent h then
          clusterChoiceWeight A C f else 0) =
        ∑ f ∈ (Finset.univ : Finset (ClusterChoice C)).filter
          (IsGlobalClusterChoice C), clusterChoiceWeight A C f := by
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro f _
            by_cases hg : IsGlobalClusterChoice C f
            · rw [if_pos hg,
                sum_selector_matches_choice_of_global C f _ hg]
            · rw [if_neg hg,
                sum_selector_matches_choice_of_not_global C f _ hg]
    _ = ∑ f : GlobalClusterChoice C, clusterChoiceWeight A C f.1 := by
          apply Finset.sum_subtype
          intro f
          simp
    _ = Matrix.permanent A := sum_globalClusterChoiceWeight_eq_permanent A C

/-- The stable-coefficient theorem applied to the actual cluster product and
column selector.  All polynomial hypotheses and the permanent coefficient
identity are discharged internally.  The coefficient inequality remains an
explicit argument here to keep this intermediate theorem modular; the final
theorem supplies its internal reconstruction from `SourceStableReindex`. -/
theorem rowClusterProduct_stableCoefficient_lower
    {n : ℕ} [Nonempty (Fin n)]
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {A : Matrix (Fin n) (Fin n) ℝ} (C : RowClustering n)
    [Nonempty C.Cluster]
    (hA : Matrix.Nonnegative A)
    (hfactorStable : ∀ c, IsRealStable (rowClusterPolynomial A C c))
    (α : C.Cluster × Fin n → ℝ)
    (hα : ∀ v, 0 ≤ α v ∧ α v ≤ 1)
    (hαsum : (∑ v, α v) = n) :
    stableBoundaryFactor α *
        polynomialCapacity α (rowClusterProduct A C) *
        polynomialCapacity α (columnSelector C.Cluster (Fin n)) ≤
      Matrix.permanent A := by
  have hselectorHomogeneous :
      (columnSelector C.Cluster (Fin n)).IsHomogeneous n := by
    simpa only [Fintype.card_fin] using
      columnSelector_isHomogeneous C.Cluster (Fin n)
  have hpair := stableCoefficient (σ := C.Cluster × Fin n)
    (rowClusterProduct A C) (columnSelector C.Cluster (Fin n)) n α
    (rowClusterProduct_nonnegativeCoefficients C hA)
    (columnSelector_nonnegativeCoefficients C.Cluster (Fin n))
    (rowClusterProduct_isMultiaffine A C)
    (columnSelector_isMultiaffine C.Cluster (Fin n))
    (rowClusterProduct_isRealStable_of_factors A C hfactorStable)
    (columnSelector_isRealStable C.Cluster (Fin n))
    (rowClusterProduct_isHomogeneous A C)
    hselectorHomogeneous
    hα hαsum
  rwa [coefficientInnerProduct_rowClusterProduct_eq_permanent] at hpair

end BeyondBethe
