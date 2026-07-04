import JL.NormPreservation
import JL.Projection

/-!
# The Johnson–Lindenstrauss embedding-existence theorem

The distributional norm-preservation bound (`JL.NormPreservation`) controls the
distortion of a *single* fixed vector. The JL lemma upgrades this to a *single*
realization of the random projection that simultaneously preserves **all** pairwise
distances of a finite point set, via the probabilistic method: a union bound over the
`< n²` pairs shows the total failure probability is `< 1`, so a good realization
exists.

`exists_avoiding` is the abstract probabilistic-method core; `johnson_lindenstrauss`
specializes it to pairwise-distance preservation. The per-pair concentration
hypothesis `hpair` is exactly the norm-preservation bound applied to each difference
vector `Q a - Q b` (Gaussian rotation invariance turns each into the chi-squared law),
and `hcard` is the union-bound counting condition implied by
`k ≥ ⌈8 · log n / (ε² − ε³)⌉`.
-/

open MeasureTheory ProbabilityTheory Real

namespace JL

/-- **Probabilistic method / union bound.** In a probability space, if the total
measure of a finite family of "bad" events is `< 1`, then some point avoids all of
them. -/
theorem exists_avoiding {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ι : Type*} (s : Finset ι) (B : ι → Set Ω)
    (hsum : ∑ i ∈ s, μ.real (B i) < 1) :
    ∃ ω, ∀ i ∈ s, ω ∉ B i := by
  by_contra hcon
  push Not at hcon
  have hcover : (Set.univ : Set Ω) ⊆ ⋃ i ∈ s, B i := by
    intro ω _
    obtain ⟨i, hi, hω⟩ := hcon ω
    exact Set.mem_biUnion hi hω
  have h1 : (1 : ℝ) ≤ μ.real (⋃ i ∈ s, B i) := by
    have hmono := measureReal_mono hcover (measure_ne_top μ _)
    have huniv : μ.real (Set.univ : Set Ω) = 1 := by simp [measureReal_def, measure_univ]
    rwa [huniv] at hmono
  have h2 := measureReal_biUnion_finset_le (μ := μ) s B
  linarith

/-- **Johnson–Lindenstrauss (existence form).** Given target squared distances
`D a b` and the realized squared projected distances `r a b ω`, if every pair's
distortion exceeds `ε · D a b` with probability at most `C`, and the union-bound
condition `n² · C < 1` holds, then there is a single realization `ω` that preserves
**all** pairwise (squared) distances within a factor `1 ± ε`. -/
theorem johnson_lindenstrauss {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {n : ℕ} {ε C : ℝ}
    (r : Fin n → Fin n → Ω → ℝ) (D : Fin n → Fin n → ℝ)
    (hpair : ∀ a b, a ≠ b →
      μ.real {ω | ε * D a b ≤ |r a b ω - D a b|} ≤ C)
    (hC : 0 ≤ C) (hcard : (n : ℝ) ^ 2 * C < 1) :
    ∃ ω, ∀ a b, a ≠ b → |r a b ω - D a b| < ε * D a b := by
  classical
  set s : Finset (Fin n × Fin n) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hs
  set B : Fin n × Fin n → Set Ω := fun p => {ω | ε * D p.1 p.2 ≤ |r p.1 p.2 ω - D p.1 p.2|}
    with hB
  have hsum : ∑ p ∈ s, μ.real (B p) < 1 := by
    calc ∑ p ∈ s, μ.real (B p)
        ≤ ∑ _p ∈ s, C :=
          Finset.sum_le_sum (fun p hp => hpair p.1 p.2 (Finset.mem_filter.mp hp).2)
      _ = (s.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (n : ℝ) ^ 2 * C := by
          apply mul_le_mul_of_nonneg_right _ hC
          have hcard_le : s.card ≤ n ^ 2 := by
            calc s.card ≤ (Finset.univ : Finset (Fin n × Fin n)).card := Finset.card_filter_le _ _
              _ = n ^ 2 := by simp [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
          exact_mod_cast hcard_le
      _ < 1 := hcard
  obtain ⟨ω, hω⟩ := exists_avoiding (μ := μ) s B hsum
  refine ⟨ω, fun a b hab => ?_⟩
  have hmem := hω (a, b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab⟩)
  simp only [hB, Set.mem_setOf_eq, not_le] at hmem
  exact hmem

end JL
