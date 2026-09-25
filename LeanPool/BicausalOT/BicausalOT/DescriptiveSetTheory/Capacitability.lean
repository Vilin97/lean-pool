/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Choquet Capacitability for Analytic Sets — Full Proof

  References:
  - Kechris, Classical Descriptive Set Theory, Theorem 30.13 (capacitability)
  - Bertsekas–Shreve, Prop 7.42 (analytic sets are universally measurable)

  Strategy (avoids König's lemma and metric-diameter bookkeeping):
  For A analytic, A = range π with π : ℕᴺ → Z continuous. The Souslin
  scheme is G_s := closure (π '' N_s) over cylinders N_s. For a bound
  β : ℕ → ℕ, the compact witness is K = π '' Σ(β) where
  Σ(β) = {σ | ∀ i, σ i ≤ β i} is compact. The core topological lemma is

      ⋂ n, ⋃ {s ≤ β, |s| = n} G_s  ⊆  π '' Σ(β),

  proved by a subsequence-extraction argument in Σ(β). The measure side
  is a recursion along increasing unions (continuity from below of outer
  measures), mirroring the `leftmostAuxG` pattern of Tree.lean.
-/
module

public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.PiNat
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.Probability.Kernel.MeasurableLIntegral
public import Mathlib.Tactic.Finiteness
public import LeanPool.BicausalOT.BicausalOT.DescriptiveSetTheory.AnalyticSet


/-! ## Part I: Bounded branch sets in Baire space -/

@[expose] public section

open Set Topology MeasureTheory Filter
open scoped ENNReal

noncomputable section



/-- Branches bounded by `β` everywhere: the compact set Σ(β). -/
def capBelow (β : ℕ → ℕ) : Set (ℕ → ℕ) := {σ | ∀ i, σ i ≤ β i}

/-- Branches bounded by `β` on the first `n` coordinates. -/
def capBelowN (β : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) := {σ | ∀ i < n, σ i ≤ β i}

theorem capBelowN_zero (β : ℕ → ℕ) : capBelowN β 0 = univ := by
  ext σ; simp [capBelowN]

theorem capBelowN_congr {β β' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, β i = β' i) :
    capBelowN β n = capBelowN β' n := by
  ext σ; constructor <;> intro hσ i hi
  · rw [← h i hi]; exact hσ i hi
  · rw [h i hi]; exact hσ i hi

theorem capBelowN_update_subset (β : ℕ → ℕ) (n k : ℕ) :
    capBelowN (Function.update β n k) (n + 1) ⊆ capBelowN β n := by
  intro σ hσ i hi
  have := hσ i (by omega)
  rwa [Function.update_of_ne (by omega)] at this

theorem capBelowN_eq_iUnion_update (β : ℕ → ℕ) (n : ℕ) :
    capBelowN β n = ⋃ k, capBelowN (Function.update β n k) (n + 1) := by
  ext σ
  simp only [mem_iUnion]
  constructor
  · intro hσ
    refine ⟨σ n, fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [Function.update_of_ne (by omega)]; exact hσ i h
    · subst h; simp [Function.update_self]
  · rintro ⟨k, hk⟩ i hi
    have := hk i (by omega)
    rwa [Function.update_of_ne (by omega)] at this

theorem monotone_capBelowN_update (β : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => capBelowN (Function.update β n k) (n + 1)) := by
  intro k k' hkk' σ hσ i hi
  rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
  · rw [Function.update_of_ne (by omega)]
    have := hσ i hi
    rwa [Function.update_of_ne (by omega)] at this
  · subst h
    have := hσ i (by omega)
    rw [Function.update_self] at this ⊢
    omega

theorem capBelow_eq_pi (β : ℕ → ℕ) :
    capBelow β = Set.pi univ (fun i => Iic (β i)) := by
  ext σ; simp [capBelow, Pi.le_def]

theorem isCompact_capBelow (β : ℕ → ℕ) : IsCompact (capBelow β) := by
  rw [capBelow_eq_pi]
  exact isCompact_univ_pi fun i => (Set.finite_Iic (β i)).isCompact

/-- Truncation: keep the first `n` values, zero out the rest. -/
def capTrunc (σ : ℕ → ℕ) (n : ℕ) : ℕ → ℕ := fun i => if i < n then σ i else 0

/-- Normalized representatives of prefixes bounded by `β`: finitely many. -/
def capSeqs (β : ℕ → ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {s | (∀ i < n, s i ≤ β i) ∧ ∀ i, n ≤ i → s i = 0}

theorem capTrunc_mem_capSeqs {β : ℕ → ℕ} {n : ℕ} {σ : ℕ → ℕ}
    (h : σ ∈ capBelowN β n) : capTrunc σ n ∈ capSeqs β n := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · simp only [capTrunc, ite_eq_left hi]; exact h i hi
  · have hn : ¬ i < n := by omega
    simp [capTrunc, hn]

theorem capSeqs_finite (β : ℕ → ℕ) (n : ℕ) : (capSeqs β n).Finite := by
  have hsub : capSeqs β n ⊆
      (fun g : Fin n → ℕ => fun i => if h : i < n then g ⟨i, h⟩ else 0) ''
        (Set.pi univ fun j : Fin n => Iic (β j)) := by
    rintro s ⟨h1, h2⟩
    refine ⟨fun j => s j, ?_, ?_⟩
    · intro j _; exact h1 j j.isLt
    · funext i
      by_cases h : i < n
      · simp [h]
      · simp [h, h2 i (by omega)]
  have hfin : (Set.pi univ fun j : Fin n => Iic (β (j : ℕ))).Finite :=
    Set.Finite.pi fun j => Set.finite_Iic (β (j : ℕ))
  exact (hfin.image _).subset hsub

theorem capSeqs_congr {β β' : ℕ → ℕ} {n : ℕ} (h : ∀ i < n, β i = β' i) :
    capSeqs β n = capSeqs β' n := by
  ext s
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨fun i hi => ?_, h2⟩
  · rw [← h i hi]; exact h1 i hi
  · rw [h i hi]; exact h1 i hi

/-! ## Part II: The Souslin scheme of a continuous map -/

variable {Z : Type*} [TopologicalSpace Z]

/-- The Souslin scheme piece: closure of the image of the cylinder `N_{f|n}`. -/
def capScheme (π : (ℕ → ℕ) → Z) (f : ℕ → ℕ) (n : ℕ) : Set Z :=
  closure (π '' PiNat.cylinder f n)

theorem capScheme_antitone (π : (ℕ → ℕ) → Z) (f : ℕ → ℕ) {m n : ℕ} (h : m ≤ n) :
    capScheme π f n ⊆ capScheme π f m :=
  closure_mono (Set.image_mono fun _ hσ i hi => hσ i (lt_of_lt_of_le hi h))

theorem capScheme_congr (π : (ℕ → ℕ) → Z) {f g : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, f i = g i) : capScheme π f n = capScheme π g n := by
  have hcyl : PiNat.cylinder f n = PiNat.cylinder g n := by
    ext σ
    simp only [PiNat.mem_cylinder_iff]
    constructor <;> intro hσ i hi
    · rw [← h i hi]; exact hσ i hi
    · rw [h i hi]; exact hσ i hi
  unfold capScheme
  rw [hcyl]

theorem capScheme_trunc (π : (ℕ → ℕ) → Z) (σ : ℕ → ℕ) (n : ℕ) :
    capScheme π (capTrunc σ n) n = capScheme π σ n :=
  capScheme_congr π fun i hi => by simp [capTrunc, ite_eq_left hi]

/-- The n-th bounded approximation: finite union of scheme pieces with
    prefix bounded by `β`. Closed. -/
def capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) : Set Z :=
  ⋃ s ∈ capSeqs β n, capScheme π s n

theorem isClosed_capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    IsClosed (capW π β n) :=
  (capSeqs_finite β n).isClosed_biUnion fun _ _ => isClosed_closure

theorem capW_antitone (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) : Antitone (capW π β) := by
  intro m n hmn z hz
  simp only [capW, mem_iUnion] at hz ⊢
  obtain ⟨s, hs, hzs⟩ := hz
  refine ⟨capTrunc s m, ?_, ?_⟩
  · exact capTrunc_mem_capSeqs fun i hi => hs.1 i (lt_of_lt_of_le hi hmn)
  · rw [capScheme_trunc]
    exact capScheme_antitone π s hmn hzs

theorem capW_congr (π : (ℕ → ℕ) → Z) {β β' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, β i = β' i) : capW π β n = capW π β' n := by
  unfold capW
  rw [capSeqs_congr h]

/-! ## Part III: The core topological lemma -/

/-- **Core lemma.** For continuous `π` and any bound `β`, the decreasing
    intersection of the bounded approximations is contained in the compact
    set `π '' Σ(β)`. Proved by subsequence extraction in `Σ(β)`. -/
theorem iInter_capW_subset {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) (β : ℕ → ℕ) :
    (⋂ n, capW π β n) ⊆ π '' capBelow β := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable Z
  intro y hy
  -- for each n, obtain a normalized bounded prefix sₙ with y ∈ closure (π '' N_{sₙ,n})
  have hsel : ∀ n : ℕ, ∃ s ∈ capSeqs β n, y ∈ capScheme π s n := by
    intro n
    have := mem_iInter.mp hy n
    simpa only [capW, mem_iUnion, exists_prop] using this
  choose s hs hys using hsel
  -- for each n, pick τₙ in the cylinder with π τₙ within 1/(n+1) of y
  have hτ : ∀ n : ℕ, ∃ τ ∈ PiNat.cylinder (s n) n, dist y (π τ) < 1 / (n + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (n + 1) := by positivity
    obtain ⟨z, hz_mem, hz_dist⟩ := Metric.mem_closure_iff.mp (hys n) _ hpos
    obtain ⟨τ, hτ_mem, rfl⟩ := hz_mem
    exact ⟨τ, hτ_mem, hz_dist⟩
  choose τ hτ_mem hτ_dist using hτ
  -- τₙ is bounded by β on the first n coordinates
  have hτ_bdd : ∀ n, ∀ i < n, τ n i ≤ β i := by
    intro n i hi
    have h1 : τ n i = s n i := hτ_mem n i hi
    rw [h1]
    exact (hs n).1 i hi
  -- clip to Σ(β) and extract a convergent subsequence
  set ρ : ℕ → (ℕ → ℕ) := fun n => fun i => min (τ n i) (β i) with hρ
  have hρ_mem : ∀ n, ρ n ∈ capBelow β := fun n i => min_le_right _ _
  obtain ⟨σ, hσ_mem, φ, hφ_mono, hφ_tendsto⟩ :=
    (isCompact_capBelow β).tendsto_subseq hρ_mem
  -- τ ∘ φ converges pointwise to σ (eventually agrees with ρ ∘ φ)
  have hτφ_tendsto : Tendsto (fun j => τ (φ j)) atTop (𝓝 σ) := by
    rw [tendsto_pi_nhds]
    intro i
    have hρi : Tendsto (fun j => ρ (φ j) i) atTop (𝓝 (σ i)) :=
      (tendsto_pi_nhds.mp hφ_tendsto) i
    apply hρi.congr'
    filter_upwards [Filter.eventually_ge_atTop (i + 1)] with j hj
    have hij : i < φ j := lt_of_lt_of_le (Nat.lt_succ_self i) (hj.trans (hφ_mono.le_apply))
    simp only [hρ]
    exact min_eq_left (hτ_bdd (φ j) i hij)
  -- π (τ (φ j)) → π σ, but also π (τ n) → y; conclude y = π σ
  have h1 : Tendsto (fun j => π (τ (φ j))) atTop (𝓝 (π σ)) :=
    (hπ.tendsto σ).comp hτφ_tendsto
  have h2 : Tendsto (fun n => π (τ n)) atTop (𝓝 y) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => dist_nonneg)
      (fun n => le_of_lt (by rw [dist_comm]; exact hτ_dist n))
  have h2φ : Tendsto (fun j => π (τ (φ j))) atTop (𝓝 y) :=
    h2.comp hφ_mono.tendsto_atTop
  exact ⟨σ, hσ_mem, tendsto_nhds_unique h1 h2φ⟩

/-! ## Part IV: Branches and the Souslin kernel -/

/-- The branch set along `σ`: decreasing intersection of scheme pieces. -/
def capBranch (π : (ℕ → ℕ) → Z) (σ : ℕ → ℕ) : Set Z := ⋂ n, capScheme π σ n

/-- The Souslin kernel `𝒜(G)` of the scheme. -/
def capKernel (π : (ℕ → ℕ) → Z) : Set Z := ⋃ σ, capBranch π σ

/-- Branches whose first `n` coordinates are bounded by `β`. -/
def capR (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) : Set Z :=
  ⋃ σ ∈ capBelowN β n, capBranch π σ

theorem capR_zero (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) : capR π β 0 = capKernel π := by
  unfold capR capKernel
  rw [capBelowN_zero]
  ext z; simp

theorem capR_congr (π : (ℕ → ℕ) → Z) {β β' : ℕ → ℕ} {n : ℕ}
    (h : ∀ i < n, β i = β' i) : capR π β n = capR π β' n := by
  unfold capR
  rw [capBelowN_congr h]

theorem capR_eq_iUnion_update (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    capR π β n = ⋃ k, capR π (Function.update β n k) (n + 1) := by
  unfold capR
  rw [capBelowN_eq_iUnion_update]
  exact biUnion_iUnion _ _

theorem monotone_capR_update (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    Monotone (fun k => capR π (Function.update β n k) (n + 1)) := fun _ _ hkk' =>
  biUnion_subset_biUnion_left (monotone_capBelowN_update β n hkk')

theorem capR_subset_capW (π : (ℕ → ℕ) → Z) (β : ℕ → ℕ) (n : ℕ) :
    capR π β n ⊆ capW π β n := by
  intro z hz
  simp only [capR, mem_iUnion, exists_prop] at hz
  obtain ⟨σ, hσ, hz⟩ := hz
  have h1 : z ∈ capScheme π σ n := mem_iInter.mp hz n
  exact mem_biUnion (capTrunc_mem_capSeqs hσ) (by rwa [capScheme_trunc])

theorem range_subset_capKernel (π : (ℕ → ℕ) → Z) : range π ⊆ capKernel π := by
  rintro _ ⟨σ, rfl⟩
  exact mem_iUnion.mpr ⟨σ, mem_iInter.mpr fun n =>
    subset_closure ⟨σ, fun i _ => rfl, rfl⟩⟩

/-- The Souslin kernel of the canonical scheme recovers exactly the range:
    the nontrivial inclusion is via the core lemma with `β := σ`. -/
theorem capKernel_eq_range {Z : Type*} [TopologicalSpace Z] [PolishSpace Z]
    {π : (ℕ → ℕ) → Z} (hπ : Continuous π) : capKernel π = range π := by
  refine subset_antisymm ?_ (range_subset_capKernel π)
  intro z hz
  obtain ⟨σ, hσ⟩ := mem_iUnion.mp hz
  have h1 : z ∈ ⋂ n, capW π σ n := by
    refine mem_iInter.mpr fun n => ?_
    have h2 := mem_iInter.mp hσ n
    exact mem_biUnion (capTrunc_mem_capSeqs fun i _ => le_refl (σ i))
      (by rwa [capScheme_trunc])
  obtain ⟨ρ, _, rfl⟩ := iInter_capW_subset hπ σ h1
  exact mem_range_self ρ

/-! ## Part V: The bounded recursion

Given a monotone set functional `m` continuous along increasing countable
unions (e.g. an outer measure, or `S ↦ κ x (Prod.mk x ⁻¹' S)`), if
`c < m (capKernel π)` then one can recursively choose a bound `β` with
`c < m (capW π β n)` for all `n`. Mirrors `leftmostAuxG` from Tree.lean. -/

theorem cap_exists_ext {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} {b : ℕ → ℕ} {n : ℕ} (hb : c < m (capR π b n)) :
    ∃ k, c < m (capR π (Function.update b n k) (n + 1)) := by
  have key : m (capR π b n) = ⨆ k, m (capR π (Function.update b n k) (n + 1)) := by
    rw [← hsup _ (monotone_capR_update π b n), ← capR_eq_iUnion_update]
  rw [key] at hb
  exact lt_iSup_iff.mp hb

/-- Recursive construction of the bound, one coordinate at a time. -/
def capAux {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    (n : ℕ) → {b : ℕ → ℕ // c < m (capR π b n)}
  | 0 => ⟨fun _ => 0, by rw [capR_zero]; exact h0⟩
  | n + 1 =>
    ⟨Function.update (capAux π m hsup h0 n).val n
        (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose,
     (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose_spec⟩

/-- The diagonal bound. -/
def capBound {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) (n : ℕ) : ℕ :=
  (capAux π m hsup h0 (n + 1)).val n

theorem capAux_eq {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∀ n i, i < n → (capAux π m hsup h0 n).val i = capBound π m hsup h0 i := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi
    have hval : (capAux π m hsup h0 (n + 1)).val
        = Function.update (capAux π m hsup h0 n).val n
            (cap_exists_ext π m hsup (capAux π m hsup h0 n).2).choose := rfl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [hval, Function.update_of_ne (by omega)]
      exact ih i h
    · subst h
      simp only [capBound]

/-- **Bounded recursion.** From `c < m (𝒜(G))` produce a bound `β` with
    `c < m (W(β, n))` for every `n`. -/
theorem cap_exists_bound {Z : Type*} [TopologicalSpace Z]
    (π : (ℕ → ℕ) → Z) (m : Set Z → ℝ≥0∞)
    (hmono : ∀ ⦃S T : Set Z⦄, S ⊆ T → m S ≤ m T)
    (hsup : ∀ s : ℕ → Set Z, Monotone s → m (⋃ k, s k) = ⨆ k, m (s k))
    {c : ℝ≥0∞} (h0 : c < m (capKernel π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < m (capW π β n) := by
  refine ⟨capBound π m hsup h0, fun n => ?_⟩
  have h1 : c < m (capR π (capAux π m hsup h0 n).val n) := (capAux π m hsup h0 n).2
  have h2 : capR π (capAux π m hsup h0 n).val n
      = capR π (capBound π m hsup h0) n :=
    capR_congr π fun i hi => capAux_eq π m hsup h0 n i hi
  rw [h2] at h1
  exact lt_of_lt_of_le h1 (hmono (capR_subset_capW π _ n))

/-! ## Part VI: Choquet capacitability for a single finite measure -/

/-- **Choquet capacitability** (Kechris 30.13, measure case; BS Prop 7.42):
    for a finite Borel measure on a Polish space, the (outer) measure of an
    analytic set is the supremum of the measures of its compact subsets. -/
theorem MeasureTheory.AnalyticSet.measure_eq_iSup_isCompact
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    μ A = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K := by
  refine le_antisymm ?_
    (iSup_le fun K => iSup_le fun _ => iSup_le fun hK => measure_mono hK)
  refine le_of_forall_lt fun c hc => ?_
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨π, hπ_cont, hπ_range⟩
  · simp at hc
  subst hπ_range
  obtain ⟨c', hcc', hc'A⟩ := exists_between hc
  have h0 : c' < μ (capKernel π) := by rwa [capKernel_eq_range hπ_cont]
  obtain ⟨β, hβ⟩ := cap_exists_bound π (fun S => μ S)
    (fun _ _ h => measure_mono h) (fun _ hs => hs.measure_iUnion) h0
  have h_iInter : μ (⋂ n, capW π β n) = ⨅ n, μ (capW π β n) :=
    Directed.measure_iInter
      (fun n => (isClosed_capW π β n).measurableSet.nullMeasurableSet)
      (fun i j => ⟨max i j, capW_antitone π β (le_max_left i j),
        capW_antitone π β (le_max_right i j)⟩)
      ⟨0, measure_ne_top μ _⟩
  have hKc : c' ≤ μ (π '' capBelow β) :=
    calc c' ≤ ⨅ n, μ (capW π β n) := le_iInf fun n => (hβ n).le
      _ = μ (⋂ n, capW π β n) := h_iInter.symm
      _ ≤ μ (π '' capBelow β) := measure_mono (iInter_capW_subset hπ_cont β)
  calc c < c' := hcc'
    _ ≤ μ (π '' capBelow β) := hKc
    _ ≤ ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ range π), μ K :=
        le_iSup_of_le (π '' capBelow β)
          (le_iSup_of_le ((isCompact_capBelow β).image hπ_cont)
            (le_iSup_of_le (image_subset_range π _) le_rfl))

/-- **Analytic sets are universally measurable** (Lusin; BS Prop 7.42):
    null-measurable with respect to every finite Borel measure. -/
theorem MeasureTheory.AnalyticSet.nullMeasurableSet
    {X : Type*} [TopologicalSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {A : Set X} (hA : AnalyticSet A)
    (μ : Measure X) [IsFiniteMeasure μ] :
    NullMeasurableSet A μ := by
  -- inner approximation by compacts, within 1/(k+1)
  have key : ∀ k : ℕ, ∃ K : Set X,
      IsCompact K ∧ K ⊆ A ∧ μ A ≤ μ K + ((k : ℝ≥0∞) + 1)⁻¹ := by
    intro k
    by_cases h0 : μ A = 0
    · exact ⟨∅, isCompact_empty, empty_subset A, by simp [h0]⟩
    have hε : ((k : ℝ≥0∞) + 1)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (by finiteness)
    have hlt : μ A - ((k : ℝ≥0∞) + 1)⁻¹
        < ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ A), μ K :=
      lt_of_lt_of_le (ENNReal.sub_lt_self (measure_ne_top μ A) h0 hε)
        (le_of_eq (hA.measure_eq_iSup_isCompact μ))
    obtain ⟨K, hK⟩ := lt_iSup_iff.mp hlt
    obtain ⟨hcpt, hK2⟩ := lt_iSup_iff.mp hK
    obtain ⟨hsub, hK3⟩ := lt_iSup_iff.mp hK2
    exact ⟨K, hcpt, hsub, tsub_le_iff_right.mp hK3.le⟩
  choose K hcpt hsub hge using key
  -- B = ⋃ K k is a Borel subset of A of full outer measure
  have hBmeas : MeasurableSet (⋃ k, K k) :=
    MeasurableSet.iUnion fun k => (hcpt k).isClosed.measurableSet
  have hBsub : (⋃ k, K k) ⊆ A := iUnion_subset hsub
  have hBeq : μ (⋃ k, K k) = μ A := by
    refine le_antisymm (measure_mono hBsub) ?_
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨k, hk⟩ := ENNReal.exists_inv_nat_lt
      (show (ε : ℝ≥0∞) ≠ 0 from by exact_mod_cast hε.ne')
    have hk1 : ((k : ℝ≥0∞) + 1)⁻¹ ≤ (ε : ℝ≥0∞) :=
      le_of_lt (lt_of_le_of_lt (ENNReal.inv_le_inv.mpr le_self_add) hk)
    calc μ A ≤ μ (K k) + ((k : ℝ≥0∞) + 1)⁻¹ := hge k
      _ ≤ μ (⋃ j, K j) + (ε : ℝ≥0∞) := by
          gcongr
          exact subset_iUnion K k
  -- measurable hull H ⊇ A; then A \ B ⊆ H \ B is null
  obtain ⟨H, hAH, hHmeas, hHeq⟩ := exists_measurable_superset μ A
  have hnull : μ (H \ ⋃ k, K k) = 0 := by
    rw [measure_sdiff (hBsub.trans hAH) hBmeas.nullMeasurableSet
      (measure_ne_top μ _), hHeq, hBeq]
    exact tsub_self _
  have hABnull : μ (A \ ⋃ k, K k) = 0 :=
    measure_mono_null (sdiff_subset_sdiff_left hAH) hnull
  rw [← union_sdiff_cancel hBsub]
  exact hBmeas.nullMeasurableSet.union (NullMeasurableSet.of_null hABnull)

/-! ## Part VII: Parametrized capacitability — the kernel key lemma -/

open ProbabilityTheory

section KernelLemma

variable {X Y : Type*}
  [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

omit [BorelSpace X] [BorelSpace Y] in
/-- (b) direction, pointwise: from `c < κ x (A_x)` produce a bound `β`
    controlling all bounded approximations. -/
theorem cap_kernel_exists_bound
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) {x : X} {c : ℝ≥0∞}
    (hc : c < κ x (Prod.mk x ⁻¹' range π)) :
    ∃ β : ℕ → ℕ, ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n) := by
  have h0 : c < κ x (Prod.mk x ⁻¹' capKernel π) := by
    rwa [capKernel_eq_range hπ]
  exact cap_exists_bound π (fun S => κ x (Prod.mk x ⁻¹' S))
    (fun _ _ hST => measure_mono (preimage_mono hST))
    (fun s hs => by
      show (κ x) (Prod.mk x ⁻¹' ⋃ k, s k) = ⨆ k, (κ x) (Prod.mk x ⁻¹' s k)
      rw [preimage_iUnion]
      exact Monotone.measure_iUnion fun i j hij => preimage_mono (hs hij))
    h0

omit [BorelSpace X] in
/-- (a) direction, pointwise: a bound `β` controlling all approximations
    forces `c ≤ κ x (A_x)` (via the core lemma and continuity from above). -/
theorem cap_kernel_le_of_bound
    {π : (ℕ → ℕ) → (X × Y)} (hπ : Continuous π)
    (κ : Kernel X Y) [IsFiniteKernel κ] {x : X} {c : ℝ≥0∞} {β : ℕ → ℕ}
    (h : ∀ n, c < κ x (Prod.mk x ⁻¹' capW π β n)) :
    c ≤ κ x (Prod.mk x ⁻¹' range π) := by
  have hmeas : ∀ n, NullMeasurableSet (Prod.mk x ⁻¹' capW π β n) (κ x) := fun n =>
    (((isClosed_capW π β n).preimage
      (Continuous.prodMk continuous_const continuous_id)).measurableSet).nullMeasurableSet
  have h_iInter : κ x (⋂ n, Prod.mk x ⁻¹' capW π β n)
      = ⨅ n, κ x (Prod.mk x ⁻¹' capW π β n) :=
    Directed.measure_iInter hmeas
      (fun i j => ⟨max i j,
        preimage_mono (capW_antitone π β (le_max_left i j)),
        preimage_mono (capW_antitone π β (le_max_right i j))⟩)
      ⟨0, measure_ne_top _ _⟩
  calc c ≤ ⨅ n, κ x (Prod.mk x ⁻¹' capW π β n) := le_iInf fun n => (h n).le
    _ = κ x (⋂ n, Prod.mk x ⁻¹' capW π β n) := h_iInter.symm
    _ ≤ κ x (Prod.mk x ⁻¹' (π '' capBelow β)) := by
        refine measure_mono ?_
        rw [← preimage_iInter]
        exact preimage_mono (iInter_capW_subset hπ β)
    _ ≤ κ x (Prod.mk x ⁻¹' range π) :=
        measure_mono (preimage_mono (image_subset_range π _))

/-- Padding a finite tuple into an `ℕ`-indexed bound. -/
def capPad (n : ℕ) (b : Fin n → ℕ) : ℕ → ℕ :=
  fun i => if h : i < n then b ⟨i, h⟩ else 0

omit [PolishSpace X] in
/-- Borel measurability of one layer of the parametrized construction:
    the bound `β` acts through finitely many coordinates, so the layer is a
    countable union of measurable rectangles. -/
theorem cap_measurable_layer
    (π : (ℕ → ℕ) → (X × Y)) (κ : Kernel X Y) [IsSFiniteKernel κ]
    (q : ℝ≥0∞) (n : ℕ) :
    MeasurableSet {p : X × (ℕ → ℕ) |
      q < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
  have hdecomp : {p : X × (ℕ → ℕ) | q < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)}
      = ⋃ b : Fin n → ℕ,
          ({x | q < κ x (Prod.mk x ⁻¹' capW π (capPad n b) n)} ×ˢ
           {β : ℕ → ℕ | ∀ i : Fin n, β i = b i}) := by
    ext ⟨x, β⟩
    simp only [mem_ofPred_eq, mem_iUnion, mem_prod]
    constructor
    · intro hq
      refine ⟨fun i => β i, ?_, fun i => rfl⟩
      have hW : capW π (capPad n (fun i : Fin n => β i)) n = capW π β n :=
        capW_congr π fun i hi => by simp [capPad, hi]
      rw [hW]; exact hq
    · rintro ⟨b, hq, hb⟩
      have hW : capW π β n = capW π (capPad n b) n :=
        capW_congr π fun i hi => by
          have := hb ⟨i, hi⟩
          simp [capPad, hi, this]
      rw [hW]; exact hq
  rw [hdecomp]
  refine MeasurableSet.iUnion fun b => MeasurableSet.prod ?_ ?_
  · exact measurableSet_lt measurable_const
      (Kernel.measurable_kernel_prodMk_left (isClosed_capW π _ n).measurableSet)
  · have : {β : ℕ → ℕ | ∀ i : Fin n, β i = b i}
        = ⋂ i : Fin n, (fun β : ℕ → ℕ => β i) ⁻¹' {b i} := by
      ext β; simp
    rw [this]
    exact MeasurableSet.iInter fun i =>
      (measurable_pi_apply (i : ℕ)) (measurableSet_singleton (b i))

/-- **Analytic superlevel sets for finite-kernel sections.**
    For `A` analytic in `X × Y` and a finite Borel kernel `κ`, the function
    `x ↦ κ x (A_x)` is upper semianalytic: its strict superlevel sets are
    analytic. This parametrized finite-kernel variant is proved below. For the
    related probability-measure statement, see Bertsekas–Shreve, *Stochastic
    Optimal Control: The Discrete-Time Case*, Corollary 7.43.1, p. 170. -/
theorem MeasureTheory.AnalyticSet.kernel_section_gt
    {A : Set (X × Y)} (hA : AnalyticSet A)
    (κ : Kernel X Y) [IsFiniteKernel κ] (c : ℝ≥0∞) :
    AnalyticSet {x | c < κ x (Prod.mk x ⁻¹' A)} := by
  rw [AnalyticSet] at hA
  rcases hA with rfl | ⟨π, hπ_cont, hπ_range⟩
  · have hempty : {x : X | c < κ x (Prod.mk x ⁻¹' (∅ : Set (X × Y)))} = ∅ := by
      ext x; simp
    rw [hempty]; exact analyticSet_empty
  subst hπ_range
  have main : {x | c < κ x (Prod.mk x ⁻¹' range π)}
      = ⋃ q : ℚ, Prod.fst ''
          {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
            ∀ n, (Real.toNNReal q : ℝ≥0∞)
              < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_image, Prod.exists]
    constructor
    · intro hc
      obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.mp hc
      obtain ⟨β, hβ⟩ := cap_kernel_exists_bound hπ_cont κ hq2
      exact ⟨q, x, β, ⟨hq1, hβ⟩, rfl⟩
    · rintro ⟨q, x', β, ⟨hq1, hβ⟩, rfl⟩
      exact lt_of_lt_of_le hq1 (cap_kernel_le_of_bound hπ_cont κ hβ)
  rw [main]
  refine AnalyticSet.iUnion fun q => ?_
  refine AnalyticSet.image_of_continuous ?_ continuous_fst
  refine MeasurableSet.analyticSet ?_
  by_cases hcq : c < (Real.toNNReal q : ℝ≥0∞)
  · have heq : {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
        ∀ n, (Real.toNNReal q : ℝ≥0∞)
          < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)}
        = ⋂ n, {p : X × (ℕ → ℕ) | (Real.toNNReal q : ℝ≥0∞)
            < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} := by
      ext p; simp [hcq]
    rw [heq]
    exact MeasurableSet.iInter fun n => cap_measurable_layer π κ _ n
  · have heq : {p : X × (ℕ → ℕ) | c < (Real.toNNReal q : ℝ≥0∞) ∧
        ∀ n, (Real.toNNReal q : ℝ≥0∞)
          < κ p.1 (Prod.mk p.1 ⁻¹' capW π p.2 n)} = ∅ := by
      ext p; simp [hcq]
    rw [heq]
    exact MeasurableSet.empty

end KernelLemma

end
