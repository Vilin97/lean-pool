/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Descriptive.GSGraph
import LeanPool.InfinitaryLogic.Descriptive.G0Dichotomy
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Fusion for the `G₀`-dichotomy: level objects and edge bookkeeping

Infrastructure for the fusion recursion of the classical `G₀`-dichotomy (2C-b sub-block 4;
see `docs/silver-phase2-route.md`), building on the positivity machinery of
`InfinitaryLogic/Descriptive/G0Dichotomy.lean`:

* **Finite-word API**: coercion-tame access lemmas for `Fin.snoc`
  (`snoc_apply_of_lt`/`snoc_apply_last`), level restrictions `restr n x` of branches with
  `restr_succ`, and canonical-word vertices `cvert m n`.
* **Edge bookkeeping**: `LvlEdgeAt m n u v` is the oriented level-`n` trace of the
  `GSGraph canonicalS` edge created by `canonicalWord m`. The three structural lemmas:
  `lvlEdgeAt_fresh` (the cross pair at the level just past the word), `lvlEdgeAt_succ_elim`
  (every level-`(n+1)` edge is the fresh cross pair or the `snoc` of a level-`n` edge),
  and `lvlEdgeAt_restr` (restrictions of a `GSGraph` edge pair are level edges), with
  `gsGraph_oriented` translating `GSGraph` edges into oriented prepended form.
* **Witness words**: `prepw c w` prepends a finite `ℕ`-word to a Baire-space point;
  `WitSet g u v c` is the (analytic) set of assignments whose `(u, v)`-value pair is
  `g`-witnessed through the cylinder of `c`, with `witSet_cover` feeding the positivity
  pigeonhole (`exists_not_smallFam_inter`) to extend witness words one coordinate at a
  time (`exists_extend_witnesses`, a fold over the finitely many tracked edges).
* **Vertex shrinking**: `exists_shrink` restricts a positive analytic family so that all
  members are uniformly `(1/2)^n`-close at every vertex, by the pigeonhole over a countable
  cover of `α` by small balls.

On top of these, the final section builds the fusion recursion itself: the `FusionStage`
tower (`exists_fusionStage_zero`, `exists_fusionStage_succ`, `fusionTower`) and the limit
extraction `exists_gsGraph_hom` — the classical `G₀`-dichotomy construction completing
Silver's theorem.
-/

open Set Function MeasureTheory

namespace G0Fusion

/-! ### Finite-word API -/

private theorem snoc_apply_mk_of_lt {n : ℕ} (u : Fin n → Bool) (i : Bool) {j : ℕ} (hj : j < n)
    (hj' : j < n + 1) : (Fin.snoc u i : Fin (n + 1) → Bool) ⟨j, hj'⟩ = u ⟨j, hj⟩ := by
  have h : (⟨j, hj'⟩ : Fin (n + 1)) = Fin.castSucc ⟨j, hj⟩ := by
    ext
    simp
  rw [h, Fin.snoc_castSucc]

/-- Coercion-tame access below the last position. -/
private theorem snoc_apply_lt {n : ℕ} (u : Fin n → Bool) (i : Bool) (j : Fin (n + 1))
    (hj : (j : ℕ) < n) : (Fin.snoc u i : Fin (n + 1) → Bool) j = u ⟨j, hj⟩ := by
  rcases j with ⟨j, hj'⟩
  exact snoc_apply_mk_of_lt u i hj hj'

/-- Coercion-tame access at the last position. -/
private theorem snoc_apply_eq {n : ℕ} (u : Fin n → Bool) (i : Bool) (j : Fin (n + 1))
    (hj : (j : ℕ) = n) : (Fin.snoc u i : Fin (n + 1) → Bool) j = i := by
  have h : j = Fin.last n := Fin.ext (by simpa using hj)
  rw [h, Fin.snoc_last]

/-- The level-`n` restriction of an infinite branch. -/
private def restr (n : ℕ) (x : ℕ → Bool) : Fin n → Bool := fun j => x j

private theorem restr_succ (n : ℕ) (x : ℕ → Bool) :
    restr (n + 1) x = Fin.snoc (restr n x) (x n) := by
  funext j
  rcases lt_or_ge (j : ℕ) n with hj | hj
  · rw [snoc_apply_lt _ _ j hj]
    rfl
  · have hjn : (j : ℕ) = n := by
      have := j.isLt
      omega
    rw [snoc_apply_eq _ _ j hjn]
    show x (j : ℕ) = x n
    rw [hjn]

private theorem restr_eq_restr_of_mem_cylinder {x y : ℕ → Bool} {N : ℕ}
    (h : y ∈ PiNat.cylinder x N) : restr N y = restr N x :=
  funext fun j => PiNat.mem_cylinder_iff.mp h j j.2

/-- The canonical word `m` as a level-`n` vertex (positions beyond the word read `false`). -/
private def cvert (m n : ℕ) : Fin n → Bool := fun j => (canonicalWord m).getD j false

/-! ### Edge bookkeeping -/

/-- The oriented level-`n` trace of the `GSGraph canonicalS` edge created by the canonical
word `m`: both vertices extend the word, the cross position carries `false` on the left and
`true` on the right, and the tails agree. -/
private def LvlEdgeAt (m n : ℕ) (u v : Fin n → Bool) : Prop :=
  canonicalLen m + 1 ≤ n ∧
  (∀ j : Fin n, (j : ℕ) < canonicalLen m →
    u j = (canonicalWord m).getD j false ∧ v j = (canonicalWord m).getD j false) ∧
  (∀ j : Fin n, (j : ℕ) = canonicalLen m → u j = false ∧ v j = true) ∧
  (∀ j : Fin n, canonicalLen m < (j : ℕ) → u j = v j)

/-- The fresh cross pair at the level just past the canonical word. -/
private theorem lvlEdgeAt_fresh (m n : ℕ) (h : canonicalLen m = n) :
    LvlEdgeAt m (n + 1) (Fin.snoc (cvert m n) false) (Fin.snoc (cvert m n) true) := by
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hjm
    have hjn : (j : ℕ) < n := by omega
    rw [snoc_apply_lt _ _ j hjn, snoc_apply_lt _ _ j hjn]
    exact ⟨rfl, rfl⟩
  · intro j hjm
    have hjn : (j : ℕ) = n := by omega
    rw [snoc_apply_eq _ _ j hjn, snoc_apply_eq _ _ j hjn]
    exact ⟨rfl, rfl⟩
  · intro j hjm
    have := j.isLt
    exact absurd hjm (by omega)

/-- Every level-`(n + 1)` edge is the fresh cross pair (when the word has length exactly
`n`) or the `snoc` of a level-`n` edge by a common last bit. -/
private theorem lvlEdgeAt_succ_elim {m n : ℕ} {u v : Fin (n + 1) → Bool}
    (h : LvlEdgeAt m (n + 1) u v) :
    (canonicalLen m = n ∧ u = Fin.snoc (cvert m n) false ∧ v = Fin.snoc (cvert m n) true) ∨
    (canonicalLen m + 1 ≤ n ∧ u (Fin.last n) = v (Fin.last n) ∧
      LvlEdgeAt m n (Fin.init u) (Fin.init v)) := by
  obtain ⟨hle, hword, hcross, htail⟩ := h
  have hLn : canonicalLen m ≤ n := by omega
  rcases eq_or_lt_of_le hLn with heq | hlt
  · left
    have hu : ∀ b : Bool, ∀ w : Fin (n + 1) → Bool,
        (∀ j : Fin (n + 1), (j : ℕ) < canonicalLen m →
          w j = (canonicalWord m).getD j false) →
        (∀ j : Fin (n + 1), (j : ℕ) = canonicalLen m → w j = b) →
        w = Fin.snoc (cvert m n) b := by
      intro b w hw hwc
      funext j
      rcases lt_or_ge (j : ℕ) n with hjn | hjn
      · rw [snoc_apply_lt _ _ j hjn]
        exact hw j (by omega)
      · have hjeq : (j : ℕ) = n := by
          have := j.isLt
          omega
        rw [snoc_apply_eq _ _ j hjeq]
        exact hwc j (by omega)
    exact ⟨heq, hu false u (fun j hj => (hword j hj).1) (fun j hj => (hcross j hj).1),
      hu true v (fun j hj => (hword j hj).2) (fun j hj => (hcross j hj).2)⟩
  · right
    refine ⟨by omega, htail (Fin.last n) (by simp [Fin.val_last]; omega), by omega, ?_, ?_, ?_⟩
    · intro j hjm
      exact hword (Fin.castSucc j) (by simpa using hjm)
    · intro j hjm
      exact hcross (Fin.castSucc j) (by simpa using hjm)
    · intro j hjm
      exact htail (Fin.castSucc j) (by simpa using hjm)

/-- The `snoc` of a level edge by a common last bit is a level edge. -/
private theorem lvlEdgeAt_snoc {m n : ℕ} {u v : Fin n → Bool} (h : LvlEdgeAt m n u v) (i : Bool) :
    LvlEdgeAt m (n + 1) (Fin.snoc u i) (Fin.snoc v i) := by
  obtain ⟨hle, hword, hcross, htail⟩ := h
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro j hjm
    have hjn : (j : ℕ) < n := by omega
    rw [snoc_apply_lt _ _ j hjn, snoc_apply_lt _ _ j hjn]
    exact hword ⟨j, hjn⟩ hjm
  · intro j hjm
    have hjn : (j : ℕ) < n := by omega
    rw [snoc_apply_lt _ _ j hjn, snoc_apply_lt _ _ j hjn]
    exact hcross ⟨j, hjn⟩ hjm
  · intro j hjm
    rcases lt_or_ge (j : ℕ) n with hjn | hjn
    · rw [snoc_apply_lt _ _ j hjn, snoc_apply_lt _ _ j hjn]
      exact htail ⟨j, hjn⟩ hjm
    · have hjeq : (j : ℕ) = n := by
        have := j.isLt
        omega
      rw [snoc_apply_eq _ _ j hjeq, snoc_apply_eq _ _ j hjeq]

/-- The level restrictions of an oriented `GSGraph` edge pair are level edges. -/
private theorem lvlEdgeAt_restr {m n : ℕ} (h : canonicalLen m + 1 ≤ n) (x : ℕ → Bool) :
    LvlEdgeAt m n
      (restr n (prependWord (canonicalWord m ++ [false]) x))
      (restr n (prependWord (canonicalWord m ++ [true]) x)) := by
  have hlen : ∀ b : Bool, (canonicalWord m ++ [b]).length = canonicalLen m + 1 := by
    intro b
    simp [length_canonicalWord]
  refine ⟨h, ?_, ?_, ?_⟩
  · intro j hjm
    constructor <;>
    · show prependWord _ x (j : ℕ) = _
      rw [prependWord_apply_of_lt (by rw [hlen]; omega),
        List.getD_append _ _ _ _ (by rw [length_canonicalWord]; exact hjm)]
  · intro j hjm
    constructor <;>
    · show prependWord _ x (j : ℕ) = _
      rw [prependWord_apply_of_lt (by rw [hlen]; omega), hjm,
        List.getD_append_right _ _ _ _ (by rw [length_canonicalWord])]
      simp [length_canonicalWord]
  · intro j hjm
    show prependWord _ x (j : ℕ) = prependWord _ x (j : ℕ)
    rw [prependWord_apply_of_le (by rw [hlen]; omega),
      prependWord_apply_of_le (by rw [hlen]; omega), hlen, hlen]

/-- Every `GSGraph canonicalS` edge comes from a canonical word in one of the two
orientations. -/
private theorem gsGraph_oriented {y z : ℕ → Bool} (h : GSGraph canonicalS y z) :
    ∃ m, ∃ x : ℕ → Bool,
      (y = prependWord (canonicalWord m ++ [false]) x ∧
        z = prependWord (canonicalWord m ++ [true]) x) ∨
      (y = prependWord (canonicalWord m ++ [true]) x ∧
        z = prependWord (canonicalWord m ++ [false]) x) := by
  obtain ⟨s, hs, i, x, hy, hz⟩ := h
  obtain ⟨m, rfl⟩ := hs
  cases i
  · exact ⟨m, x, Or.inl ⟨hy, by simpa using hz⟩⟩
  · exact ⟨m, x, Or.inr ⟨hy, by simpa using hz⟩⟩

/-! ### Witness words in Baire space -/

/-- Prepend a finite `ℕ`-word to a point of Baire space. -/
private def prepw (c : List ℕ) (w : ℕ → ℕ) : ℕ → ℕ := fun j =>
  if j < c.length then c.getD j 0 else w (j - c.length)

private theorem prepw_apply_of_lt {c : List ℕ} {j : ℕ} (h : j < c.length) (w : ℕ → ℕ) :
    prepw c w j = c.getD j 0 := ite_eq_left h

private theorem prepw_apply_of_le {c : List ℕ} {j : ℕ} (h : c.length ≤ j) (w : ℕ → ℕ) :
    prepw c w j = w (j - c.length) := ite_eq_right (not_lt.mpr h)

private theorem prepw_nil (w : ℕ → ℕ) : prepw [] w = w :=
  funext fun j => by simp [prepw]

private theorem continuous_prepw (c : List ℕ) : Continuous (prepw c) := by
  refine continuous_pi fun j => ?_
  rcases lt_or_ge j c.length with hj | hj
  · have h : (fun w : ℕ → ℕ => prepw c w j) = fun _ => c.getD j 0 :=
      funext fun w => prepw_apply_of_lt hj w
    rw [h]
    exact continuous_const
  · have h : (fun w : ℕ → ℕ => prepw c w j) = fun w => w (j - c.length) :=
      funext fun w => prepw_apply_of_le hj w
    rw [h]
    exact continuous_apply _

/-- Splitting off the head of the tail extends the word. -/
private theorem prepw_append_head (c : List ℕ) (w : ℕ → ℕ) :
    prepw (c ++ [w 0]) (fun j => w (j + 1)) = prepw c w := by
  funext j
  rcases lt_trichotomy j c.length with h | h | h
  · rw [prepw_apply_of_lt (by simp; omega), prepw_apply_of_lt h,
      List.getD_append _ _ _ _ h]
  · subst h
    rw [prepw_apply_of_lt (by simp), prepw_apply_of_le le_rfl,
      List.getD_append_right _ _ _ _ le_rfl]
    simp
  · rw [prepw_apply_of_le (by simp; omega), prepw_apply_of_le (by omega)]
    simp only [List.length_append, List.length_singleton]
    congr 1
    omega

private theorem getD_of_prefix {c d : List ℕ} (h : c <+: d) {j : ℕ} (hj : j < c.length) :
    d.getD j 0 = c.getD j 0 := by
  obtain ⟨t, rfl⟩ := h
  exact List.getD_append _ _ _ _ hj

/-! ### Witness-constraint sets -/

section WitSet

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]
variable {ι : Type*} [Countable ι]

/-- The set of assignments whose `(u, v)`-value pair is `g`-witnessed through the cylinder
of the word `c`. -/
private def WitSet (g : (ℕ → ℕ) → α × α) (u v : ι) (c : List ℕ) : Set (ι → α) :=
  {φ | ∃ w : ℕ → ℕ, g (prepw c w) = (φ u, φ v)}

private theorem analyticSet_witSet {g : (ℕ → ℕ) → α × α} (hg : Continuous g) (u v : ι)
    (c : List ℕ) : AnalyticSet (WitSet g u v c) := by
  have hclosed : IsClosed {p : (ι → α) × (ℕ → ℕ) | g (prepw c p.2) = (p.1 u, p.1 v)} :=
    isClosed_eq (hg.comp ((continuous_prepw c).comp continuous_snd))
      (((continuous_apply u).comp continuous_fst).prodMk
        ((continuous_apply v).comp continuous_fst))
  have h : WitSet g u v c =
      Prod.fst '' {p : (ι → α) × (ℕ → ℕ) | g (prepw c p.2) = (p.1 u, p.1 v)} := by
    ext φ
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨(φ, w), hw, rfl⟩
    · rintro ⟨⟨φ', w⟩, hw, rfl⟩
      exact ⟨w, hw⟩
  rw [h]
  exact hclosed.analyticSet.image_of_continuous continuous_fst

omit [TopologicalSpace α] [PolishSpace α] [Countable ι] in
/-- Witnessed families are covered by the one-step extensions of the witness word. -/
private theorem witSet_cover {g : (ℕ → ℕ) → α × α} {u v : ι} {c : List ℕ} {Φ : Set (ι → α)}
    (hwit : ∀ φ ∈ Φ, φ ∈ WitSet g u v c) :
    Φ ⊆ ⋃ k : ℕ, WitSet g u v (c ++ [k]) := by
  intro φ hφ
  obtain ⟨w, hw⟩ := hwit φ hφ
  refine mem_iUnion.mpr ⟨w 0, ⟨fun j => w (j + 1), ?_⟩⟩
  rw [prepw_append_head]
  exact hw

end WitSet

/-! ### Pigeonhole over countable index types -/

private theorem exists_not_smallFam_inter' {α : Type*} [MeasurableSpace α] {G : Set (α × α)}
    {ι : Type*} {Φ : Set (ι → α)} (hΦ : ¬ SmallFam G Φ)
    {κ : Type*} [Countable κ] [Nonempty κ] {Ψ : κ → Set (ι → α)}
    (hcov : Φ ⊆ ⋃ c : κ, Ψ c) :
    ∃ c : κ, ¬ SmallFam G (Φ ∩ Ψ c) := by
  obtain ⟨f, hf⟩ := exists_surjective_nat κ
  have hcov' : Φ ⊆ ⋃ n : ℕ, Ψ (f n) := by
    intro φ hφ
    obtain ⟨c, hc⟩ := mem_iUnion.mp (hcov hφ)
    obtain ⟨n, rfl⟩ := hf c
    exact mem_iUnion.mpr ⟨n, hc⟩
  obtain ⟨n, hn⟩ := exists_not_smallFam_inter hΦ hcov'
  exact ⟨f n, hn⟩

/-! ### Vertex shrinking -/

section Shrink

variable {α : Type*} [MetricSpace α] [SecondCountableTopology α] [CompleteSpace α]
  [MeasurableSpace α] [BorelSpace α]

omit [CompleteSpace α] in
/-- A countable cover of a separable metric space by measurable sets of diameter at most
`(1/2)^n`. -/
private theorem exists_smallOpens [Nonempty α] (n : ℕ) :
    ∃ O : ℕ → Set α, (∀ k, MeasurableSet (O k)) ∧ (∀ x : α, ∃ k, x ∈ O k) ∧
      ∀ k, ∀ a ∈ O k, ∀ b ∈ O k, dist a b ≤ (1 / 2) ^ n := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense α
  obtain ⟨e, he⟩ := hDc.exists_eq_range hDd.nonempty
  refine ⟨fun k => Metric.ball (e k) ((1 / 2) ^ (n + 2)), fun k =>
    Metric.isOpen_ball.measurableSet, ?_, ?_⟩
  · intro x
    obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.mp hDd x ((1 / 2) ^ (n + 2)) (by positivity)
    rw [he] at hdD
    obtain ⟨k, rfl⟩ := hdD
    refine ⟨k, Metric.mem_ball.mpr ?_⟩
    rw [dist_comm]
    exact Metric.mem_ball.mp hd
  · intro k a ha b hb
    rw [Metric.mem_ball] at ha hb
    calc dist a b ≤ dist a (e k) + dist (e k) b := dist_triangle _ _ _
      _ ≤ (1 / 2) ^ (n + 2) + (1 / 2) ^ (n + 2) := by
          rw [dist_comm (e k) b]
          exact add_le_add ha.le hb.le
      _ ≤ (1 / 2) ^ n := by
          rw [pow_succ, pow_succ]
          nlinarith [pow_pos (by norm_num : (0:ℝ) < 1/2) n]

/-- **Vertex shrinking**: a positive analytic family can be refined to a positive analytic
subfamily whose members are uniformly `(1/2)^n`-close at every vertex. -/
private theorem exists_shrink {G : Set (α × α)} {ι : Type*} [Finite ι] [Nonempty α]
    {Φ : Set (ι → α)} (hana : AnalyticSet Φ) (hpos : ¬ SmallFam G Φ) (n : ℕ) :
    ∃ Φ' : Set (ι → α), Φ' ⊆ Φ ∧ AnalyticSet Φ' ∧ ¬ SmallFam G Φ' ∧
      ∀ φ ∈ Φ', ∀ φ' ∈ Φ', ∀ u, dist (φ u) (φ' u) ≤ (1 / 2) ^ n := by
  classical
  obtain ⟨O, hOm, hOcov, hOdiam⟩ := exists_smallOpens (α := α) n
  set Ψ : (ι → ℕ) → Set (ι → α) := fun c => {φ | ∀ u, φ u ∈ O (c u)} with hΨ
  have hcov : Φ ⊆ ⋃ c : ι → ℕ, Ψ c := by
    intro φ hφ
    choose c hc using fun u => hOcov (φ u)
    exact mem_iUnion.mpr ⟨c, hc⟩
  obtain ⟨c, hc⟩ := exists_not_smallFam_inter' hpos hcov
  have hΨm : MeasurableSet (Ψ c) := by
    have h : Ψ c = ⋂ u, (fun φ : ι → α => φ u) ⁻¹' O (c u) := by
      ext φ
      simp [hΨ]
    rw [h]
    exact MeasurableSet.iInter fun u => measurable_pi_apply u (hOm (c u))
  refine ⟨Φ ∩ Ψ c, inter_subset_left, hana.inter_measurableSet hΨm, hc, ?_⟩
  rintro φ ⟨-, hφ⟩ φ' ⟨-, hφ'⟩ u
  exact hOdiam (c u) _ (hφ u) _ (hφ' u)

end Shrink

/-! ### Witness extension fold -/

section WitnessFold

variable {α : Type*} [TopologicalSpace α] [PolishSpace α]
  [MeasurableSpace α] [BorelSpace α]
variable {ι : Type*} [Countable ι] [DecidableEq ι]

omit [BorelSpace α] in
/-- **Witness extension**: given a positive analytic family whose tracked edge pairs are
all witnessed at their current words, the family can be refined to a positive analytic
subfamily with every tracked witness word properly extended. -/
private theorem exists_extend_witnesses {G : Set (α × α)}
    {g : (ℕ → ℕ) → α × α} (hg : Continuous g)
    (L : List (ι × ι)) (hnodup : L.Nodup)
    {Φ : Set (ι → α)} (hana : AnalyticSet Φ) (hpos : ¬ SmallFam G Φ)
    (c₀ : ι × ι → List ℕ)
    (hwit : ∀ p ∈ L, ∀ φ ∈ Φ, φ ∈ WitSet g p.1 p.2 (c₀ p)) :
    ∃ (Φ' : Set (ι → α)) (c' : ι × ι → List ℕ), Φ' ⊆ Φ ∧ AnalyticSet Φ' ∧
      ¬ SmallFam G Φ' ∧
      (∀ p ∈ L, c₀ p <+: c' p ∧ (c₀ p).length < (c' p).length ∧
        ∀ φ ∈ Φ', φ ∈ WitSet g p.1 p.2 (c' p)) ∧
      (∀ p ∉ L, c' p = c₀ p) := by
  classical
  induction L generalizing Φ with
  | nil => exact ⟨Φ, c₀, subset_rfl, hana, hpos, by simp, fun p _ => rfl⟩
  | cons p L IH =>
    obtain ⟨Φ₁, c₁, hsub₁, hana₁, hpos₁, hL₁, hout₁⟩ :=
      IH (List.Nodup.of_cons hnodup) hana hpos
        (fun q hq φ hφ => hwit q (List.mem_cons_of_mem p hq) φ hφ)
    have hpL : p ∉ L := (List.nodup_cons.mp hnodup).1
    have hwitp : ∀ φ ∈ Φ₁, φ ∈ WitSet g p.1 p.2 (c₀ p) :=
      fun φ hφ => hwit p List.mem_cons_self φ (hsub₁ hφ)
    obtain ⟨k, hk⟩ := exists_not_smallFam_inter hpos₁ (witSet_cover hwitp)
    refine ⟨Φ₁ ∩ WitSet g p.1 p.2 (c₀ p ++ [k]),
      Function.update c₁ p (c₀ p ++ [k]),
      inter_subset_left.trans hsub₁,
      hana₁.inter (analyticSet_witSet hg p.1 p.2 _), hk, ?_, ?_⟩
    · rintro q hq
      rcases List.mem_cons.mp hq with rfl | hqL
      · rw [Function.update_self]
        exact ⟨⟨[k], rfl⟩, by simp, fun φ hφ => hφ.2⟩
      · have hqp : q ≠ p := fun h => hpL (h ▸ hqL)
        rw [Function.update_of_ne hqp]
        obtain ⟨hpre, hlen, hwit'⟩ := hL₁ q hqL
        exact ⟨hpre, hlen, fun φ hφ => hwit' φ hφ.1⟩
    · intro q hq
      have hqp : q ≠ p := fun h => hq (h ▸ List.mem_cons_self)
      rw [Function.update_of_ne hqp]
      exact hout₁ q (fun h => hq (List.mem_cons_of_mem p h))

end WitnessFold

/-! ### The fusion recursion -/

section Fusion

variable {α : Type*} [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α]
  [MeasurableSpace α] [BorelSpace α]
variable {G : Set (α × α)} {g : (ℕ → ℕ) → α × α}

/-- The combination map: a pair of level-`n` assignments gives a level-`(n + 1)` assignment,
sending each vertex to the value of the parent under the assignment selected by the last
bit. -/
private def combFun (n : ℕ) (φ₀ φ₁ : (Fin n → Bool) → α) : (Fin (n + 1) → Bool) → α :=
  fun v => (if v (Fin.last n) then φ₁ else φ₀) (Fin.init v)

omit [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [BorelSpace α] in
private theorem combFun_vals (n : ℕ) (φ₀ φ₁ : (Fin n → Bool) → α) (v : Fin (n + 1) → Bool) :
    (∃ i, combFun n φ₀ φ₁ v = φ₀ i) ∨ (∃ i, combFun n φ₀ φ₁ v = φ₁ i) := by
  cases hv : v (Fin.last n)
  · exact Or.inl ⟨Fin.init v, by simp [combFun, hv]⟩
  · exact Or.inr ⟨Fin.init v, by simp [combFun, hv]⟩

omit [MetricSpace α] [CompleteSpace α] [SecondCountableTopology α] [MeasurableSpace α]
  [BorelSpace α] in
private theorem combFun_snoc (n : ℕ) (φ₀ φ₁ : (Fin n → Bool) → α) (u : Fin n → Bool) (i : Bool) :
    combFun n φ₀ φ₁ (Fin.snoc u i) = (if i then φ₁ else φ₀) u := by
  cases i <;> simp [combFun]

omit [CompleteSpace α] [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α] in
private theorem continuous_combFun (n : ℕ) :
    Continuous fun p : ((Fin n → Bool) → α) × ((Fin n → Bool) → α) =>
      combFun n p.1 p.2 := by
  refine continuous_pi fun v => ?_
  cases hv : v (Fin.last n)
  · have h : (fun p : ((Fin n → Bool) → α) × ((Fin n → Bool) → α) =>
        combFun n p.1 p.2 v) = fun p => p.1 (Fin.init v) := by
      funext p
      simp [combFun, hv]
    rw [h]
    exact (continuous_apply _).comp continuous_fst
  · have h : (fun p : ((Fin n → Bool) → α) × ((Fin n → Bool) → α) =>
        combFun n p.1 p.2 v) = fun p => p.2 (Fin.init v) := by
      funext p
      simp [combFun, hv]
    rw [h]
    exact (continuous_apply _).comp continuous_snd

/-- The inherited witness words: a level-`(n + 1)` pair with agreeing last bits inherits the
word of its parent pair; the fresh cross pair (differing last bits) starts at the empty
word. -/
private def precw (n : ℕ) (cw : (Fin n → Bool) × (Fin n → Bool) → List ℕ) :
    (Fin (n + 1) → Bool) × (Fin (n + 1) → Bool) → List ℕ :=
  fun p => if p.1 (Fin.last n) = p.2 (Fin.last n) then cw (Fin.init p.1, Fin.init p.2)
    else []

private theorem precw_of_last_eq {n : ℕ} {cw : (Fin n → Bool) × (Fin n → Bool) → List ℕ}
    {u v : Fin (n + 1) → Bool} (h : u (Fin.last n) = v (Fin.last n)) :
    precw n cw (u, v) = cw (Fin.init u, Fin.init v) := ite_eq_left h

private theorem precw_of_last_ne {n : ℕ} {cw : (Fin n → Bool) × (Fin n → Bool) → List ℕ}
    {u v : Fin (n + 1) → Bool} (h : ¬ u (Fin.last n) = v (Fin.last n)) :
    precw n cw (u, v) = [] := ite_eq_right h

private theorem precw_snoc {n : ℕ} (cw : (Fin n → Bool) × (Fin n → Bool) → List ℕ)
    (u v : Fin n → Bool) (i : Bool) :
    precw n cw (Fin.snoc u i, Fin.snoc v i) = cw (u, v) := by
  have h : (Fin.snoc u i : Fin (n + 1) → Bool) (Fin.last n) =
      (Fin.snoc v i : Fin (n + 1) → Bool) (Fin.last n) := by
    rw [Fin.snoc_last, Fin.snoc_last]
  rw [precw_of_last_eq h, Fin.init_snoc, Fin.init_snoc]

/-- A stage of the fusion construction: a positive analytic family of level-`n` assignments
whose members are uniformly close at every vertex and uniformly `g`-witnessed through the
tracked word at every level edge. -/
structure FusionStage (G : Set (α × α)) (g : (ℕ → ℕ) → α × α) (n : ℕ) where
  fam : Set ((Fin n → Bool) → α)
  cw : (Fin n → Bool) × (Fin n → Bool) → List ℕ
  analytic : AnalyticSet fam
  positive : ¬ SmallFam G fam
  close : ∀ φ ∈ fam, ∀ φ' ∈ fam, ∀ u, dist (φ u) (φ' u) ≤ (1 / 2) ^ n
  witness : ∀ m (u v : Fin n → Bool), LvlEdgeAt m n u v →
    ∀ φ ∈ fam, φ ∈ WitSet g u v (cw (u, v))
  wlen : ∀ m (u v : Fin n → Bool), LvlEdgeAt m n u v →
    n ≤ canonicalLen m + 1 + (cw (u, v)).length

/-- The base stage: the full family, shrunk once for the level-`0` closeness control. -/
private theorem exists_fusionStage_zero [Nonempty α]
    (hpos : ¬ SmallFam G (univ : Set ((Fin 0 → Bool) → α))) :
    Nonempty (FusionStage G g 0) := by
  have hana : AnalyticSet (univ : Set ((Fin 0 → Bool) → α)) := by
    rw [← Set.range_id]
    exact analyticSet_range_of_polishSpace continuous_id
  obtain ⟨Φ', hsub, hana', hpos', hclose'⟩ := exists_shrink hana hpos 0
  refine ⟨⟨Φ', fun _ => [], hana', hpos', hclose', ?_, ?_⟩⟩
  · intro m u v hedge
    exact absurd hedge.1 (by omega)
  · intro m u v hedge
    exact absurd hedge.1 (by omega)

/-- **The one-step extension lemma**: every fusion stage extends to the next level, with
children's values among the parents' values and inherited witness words extending the
parents' words. Combination (`not_smallFam_comb_cross` at fresh cross levels,
`not_smallFam_comb_pairs` otherwise), then the witness-extension fold, then vertex
shrinking. -/
private theorem exists_fusionStage_succ [Nonempty α] (hG : AnalyticSet G) (hg : Continuous g)
    (hrange : Set.range g = G) {n : ℕ} (S : FusionStage G g n) :
    ∃ T : FusionStage G g (n + 1),
      (∀ ψ ∈ T.fam, ∀ v : Fin (n + 1) → Bool, ∃ φ ∈ S.fam, ψ v = φ (Fin.init v)) ∧
      (∀ m (u v : Fin n → Bool) (i : Bool), LvlEdgeAt m n u v →
        S.cw (u, v) <+: T.cw (Fin.snoc u i, Fin.snoc v i)) := by
  classical
  -- The common tail: fold the witness extensions, shrink, and assemble.
  suffices hmain : ∀ Ψ : Set ((Fin (n + 1) → Bool) → α),
      AnalyticSet Ψ → ¬ SmallFam G Ψ →
      (∀ ψ ∈ Ψ, ∀ v : Fin (n + 1) → Bool, ∃ φ ∈ S.fam, ψ v = φ (Fin.init v)) →
      (∀ ψ ∈ Ψ, ∀ m (u v : Fin (n + 1) → Bool), LvlEdgeAt m (n + 1) u v →
        ψ ∈ WitSet g u v (precw n S.cw (u, v))) →
      ∃ T : FusionStage G g (n + 1),
        (∀ ψ ∈ T.fam, ∀ v : Fin (n + 1) → Bool, ∃ φ ∈ S.fam, ψ v = φ (Fin.init v)) ∧
        (∀ m (u v : Fin n → Bool) (i : Bool), LvlEdgeAt m n u v →
          S.cw (u, v) <+: T.cw (Fin.snoc u i, Fin.snoc v i)) by
    by_cases hcross : ∃ m, canonicalLen m = n
    · -- A fresh cross edge is born at this level
      obtain ⟨m₀, hm₀⟩ := hcross
      refine hmain
        {ψ | ∃ φ₀ ∈ S.fam, ∃ φ₁ ∈ S.fam,
          (φ₀ (cvert m₀ n), φ₁ (cvert m₀ n)) ∈ G ∧ ψ = combFun n φ₀ φ₁}
        (analyticSet_comb_cross hG S.analytic _ _ (continuous_combFun n))
        (not_smallFam_comb_cross hG S.analytic S.positive _ _ (combFun_vals n))
        ?_ ?_
      · rintro ψ ⟨φ₀, h₀, φ₁, h₁, -, rfl⟩ v
        cases hv : v (Fin.last n)
        · exact ⟨φ₀, h₀, by simp [combFun, hv]⟩
        · exact ⟨φ₁, h₁, by simp [combFun, hv]⟩
      · rintro ψ ⟨φ₀, h₀, φ₁, h₁, hcr, rfl⟩ m u v hedge
        rcases lvlEdgeAt_succ_elim hedge with ⟨heq, hu, hv⟩ | ⟨hle, hlast, hpar⟩
        · -- the fresh cross pair
          have hmm : m = m₀ := canonicalLen_strictMono.injective (heq.trans hm₀.symm)
          subst hmm
          have hne : (precw n S.cw (u, v)) = [] := by
            apply precw_of_last_ne
            rw [hu, hv, Fin.snoc_last, Fin.snoc_last]
            simp
          rw [hne]
          have hval : (combFun n φ₀ φ₁ u, combFun n φ₀ φ₁ v) =
              (φ₀ (cvert m n), φ₁ (cvert m n)) := by
            rw [hu, hv, combFun_snoc, combFun_snoc]
            simp
          obtain ⟨w, hw⟩ := hrange.symm ▸ hcr
          exact ⟨w, by rw [prepw_nil, hval]; exact hw⟩
        · -- an inherited pair
          rw [precw_of_last_eq hlast]
          obtain ⟨w, hw⟩ := S.witness m _ _ hpar (if u (Fin.last n) then φ₁ else φ₀)
            (by
              cases hu : u (Fin.last n)
              · simpa [hu] using h₀
              · simpa [hu] using h₁)
          refine ⟨w, hw.trans ?_⟩
          have hcv : combFun n φ₀ φ₁ v = (if u (Fin.last n) then φ₁ else φ₀) (Fin.init v) := by
            show (if v (Fin.last n) then φ₁ else φ₀) (Fin.init v) = _
            rw [hlast]
          rw [hcv]
          rfl
    · -- No fresh edge at this level
      refine hmain {ψ | ∃ φ₀ ∈ S.fam, ∃ φ₁ ∈ S.fam, ψ = combFun n φ₀ φ₁}
        (analyticSet_comb_pairs S.analytic _ (continuous_combFun n))
        (not_smallFam_comb_pairs S.positive _ (combFun_vals n)) ?_ ?_
      · rintro ψ ⟨φ₀, h₀, φ₁, h₁, rfl⟩ v
        cases hv : v (Fin.last n)
        · exact ⟨φ₀, h₀, by simp [combFun, hv]⟩
        · exact ⟨φ₁, h₁, by simp [combFun, hv]⟩
      · rintro ψ ⟨φ₀, h₀, φ₁, h₁, rfl⟩ m u v hedge
        rcases lvlEdgeAt_succ_elim hedge with ⟨heq, -, -⟩ | ⟨hle, hlast, hpar⟩
        · exact absurd ⟨m, heq⟩ hcross
        · rw [precw_of_last_eq hlast]
          obtain ⟨w, hw⟩ := S.witness m _ _ hpar (if u (Fin.last n) then φ₁ else φ₀)
            (by
              cases hu : u (Fin.last n)
              · simpa [hu] using h₀
              · simpa [hu] using h₁)
          refine ⟨w, hw.trans ?_⟩
          have hcv : combFun n φ₀ φ₁ v = (if u (Fin.last n) then φ₁ else φ₀) (Fin.init v) := by
            show (if v (Fin.last n) then φ₁ else φ₀) (Fin.init v) = _
            rw [hlast]
          rw [hcv]
          rfl
  -- The common tail
  intro Ψ hana hpos hchild hwit
  set L := (Finset.univ.filter
    fun p : ((Fin (n + 1) → Bool) × (Fin (n + 1) → Bool)) =>
      ∃ m, LvlEdgeAt m (n + 1) p.1 p.2).toList with hLdef
  obtain ⟨Φ₂, c', hsub₂, hana₂, hpos₂, hLspec, -⟩ :=
    exists_extend_witnesses hg L (Finset.nodup_toList _) hana hpos (precw n S.cw)
      (fun p hp ψ hψ => by
        obtain ⟨-, m, hedge⟩ := Finset.mem_filter.mp (Finset.mem_toList.mp hp)
        exact hwit ψ hψ m p.1 p.2 hedge)
  obtain ⟨Φ₃, hsub₃, hana₃, hpos₃, hclose₃⟩ := exists_shrink hana₂ hpos₂ (n + 1)
  have hmemL : ∀ {m} {u v : Fin (n + 1) → Bool}, LvlEdgeAt m (n + 1) u v → (u, v) ∈ L :=
    fun {m u v} hedge => Finset.mem_toList.mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, m, hedge⟩)
  refine ⟨⟨Φ₃, c', hana₃, hpos₃, hclose₃, ?_, ?_⟩, ?_, ?_⟩
  · -- witnesses at the extended words
    intro m u v hedge φ hφ
    exact (hLspec (u, v) (hmemL hedge)).2.2 φ (hsub₃ hφ)
  · -- word lengths
    intro m u v hedge
    obtain ⟨-, hlen, -⟩ := hLspec (u, v) (hmemL hedge)
    rcases lvlEdgeAt_succ_elim hedge with ⟨heq, -, -⟩ | ⟨hle, hlast, hpar⟩
    · omega
    · rw [precw_of_last_eq hlast] at hlen
      have hw := S.wlen m _ _ hpar
      omega
  · -- children's values come from the parents
    intro ψ hψ v
    exact hchild ψ (hsub₂ (hsub₃ hψ)) v
  · -- inherited words extend the parents' words
    intro m u v i hedge
    have hedge' := lvlEdgeAt_snoc hedge i
    obtain ⟨hpre, -, -⟩ := hLspec (Fin.snoc u i, Fin.snoc v i) (hmemL hedge')
    rw [precw_snoc] at hpre
    exact hpre

variable (G g) in
/-- The tower of fusion stages. -/
private noncomputable def fusionTower [Nonempty α] (hG : AnalyticSet G) (hg : Continuous g)
    (hrange : Set.range g = G)
    (hpos : ¬ SmallFam G (univ : Set ((Fin 0 → Bool) → α))) : ∀ n, FusionStage G g n
  | 0 => (exists_fusionStage_zero hpos).some
  | n + 1 => (exists_fusionStage_succ hG hg hrange
      (fusionTower hG hg hrange hpos n)).choose

private theorem fusionTower_spec [Nonempty α] (hG : AnalyticSet G) (hg : Continuous g)
    (hrange : Set.range g = G)
    (hpos : ¬ SmallFam G (univ : Set ((Fin 0 → Bool) → α))) (n : ℕ) :
    (∀ ψ ∈ (fusionTower G g hG hg hrange hpos (n + 1)).fam,
      ∀ v : Fin (n + 1) → Bool, ∃ φ ∈ (fusionTower G g hG hg hrange hpos n).fam,
        ψ v = φ (Fin.init v)) ∧
    (∀ m (u v : Fin n → Bool) (i : Bool), LvlEdgeAt m n u v →
      (fusionTower G g hG hg hrange hpos n).cw (u, v) <+:
        (fusionTower G g hG hg hrange hpos (n + 1)).cw (Fin.snoc u i, Fin.snoc v i)) :=
  (exists_fusionStage_succ hG hg hrange (fusionTower G g hG hg hrange hpos n)).choose_spec

/-- **The fusion limit**: a continuous map of Cantor space all of whose
`GSGraph canonicalS` edge pairs land in `G`. -/
theorem exists_gsGraph_hom [Nonempty α] (hG : AnalyticSet G) (hg : Continuous g)
    (hrange : Set.range g = G)
    (hpos : ¬ SmallFam G (univ : Set ((Fin 0 → Bool) → α)))
    (hsymm : ∀ a b : α, (a, b) ∈ G → (b, a) ∈ G) :
    ∃ φ : (ℕ → Bool) → α, Continuous φ ∧
      ∀ y z : ℕ → Bool, GSGraph canonicalS y z → (φ y, φ z) ∈ G := by
  classical
  set S : ∀ n, FusionStage G g n := fusionTower G g hG hg hrange hpos with hS
  have hspec := fusionTower_spec hG hg hrange hpos
  have hne : ∀ n, (S n).fam.Nonempty := fun n => nonempty_of_not_smallFam (S n).positive
  choose φseq hφseq using hne
  -- the approximating values along prefixes
  set a : (ℕ → Bool) → ℕ → α := fun x n => φseq n (restr n x) with ha
  have hinit : ∀ (x : ℕ → Bool) (n : ℕ), Fin.init (restr (n + 1) x) = restr n x := by
    intro x n
    funext j
    show x ↑(Fin.castSucc j) = x ↑j
    simp
  have hstep : ∀ x n, dist (a x n) (a x (n + 1)) ≤ (1 / 2) ^ n := by
    intro x n
    obtain ⟨φ, hφ, heq⟩ := (hspec n).1 (φseq (n + 1)) (hφseq (n + 1)) (restr (n + 1) x)
    show dist (φseq n (restr n x)) (φseq (n + 1) (restr (n + 1) x)) ≤ _
    rw [heq, hinit]
    exact (S n).close _ (hφseq n) _ hφ _
  have hcauchy : ∀ x, CauchySeq (a x) := fun x =>
    cauchySeq_of_le_geometric (1 / 2) 1 (by norm_num)
      (fun n => by simpa using hstep x n)
  choose φlim hφlim using fun x => cauchySeq_tendsto_of_complete (hcauchy x)
  have hdlim : ∀ x n, dist (a x n) (φlim x) ≤ (1 / 2) ^ n * 2 := by
    intro x n
    have h := dist_le_of_le_geometric_of_tendsto (1 / 2) 1 (by norm_num)
      (fun k => by simpa using hstep x k) (hφlim x) n
    calc dist (a x n) (φlim x) ≤ 1 * (1 / 2) ^ n / (1 - 1 / 2) := h
      _ = (1 / 2) ^ n * 2 := by ring
  refine ⟨φlim, ?_, ?_⟩
  · -- continuity: prefix agreement controls the limit values
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / 4 by linarith)
      (by norm_num : (1 : ℝ) / 2 < 1)
    refine Filter.eventually_of_mem
      ((PiNat.isOpen_cylinder _ x N).mem_nhds (PiNat.self_mem_cylinder x N)) ?_
    intro y hy
    have heqa : a y N = a x N := by
      show φseq N (restr N y) = φseq N (restr N x)
      rw [restr_eq_restr_of_mem_cylinder hy]
    have h1 : dist (φlim y) (φlim x) ≤ dist (a y N) (φlim y) + dist (a x N) (φlim x) :=
      calc dist (φlim y) (φlim x)
          ≤ dist (φlim y) (a y N) + dist (a y N) (φlim x) := dist_triangle _ _ _
        _ = dist (a y N) (φlim y) + dist (a x N) (φlim x) := by rw [dist_comm, heqa]
    have h2 := hdlim y N
    have h3 := hdlim x N
    calc dist (φlim y) (φlim x)
        ≤ (1 / 2) ^ N * 2 + (1 / 2) ^ N * 2 := by linarith
      _ < ε := by linarith
  · -- the homomorphism condition
    intro y z hyz
    obtain ⟨m, x, hor⟩ := gsGraph_oriented hyz
    have hkey : ∀ y' z' : ℕ → Bool,
        y' = prependWord (canonicalWord m ++ [false]) x →
        z' = prependWord (canonicalWord m ++ [true]) x →
        (φlim y', φlim z') ∈ G := by
      intro y' z' hy' hz'
      set L₀ := canonicalLen m + 1 with hL₀
      -- the finite edge traces
      have hedge : ∀ n, L₀ ≤ n → LvlEdgeAt m n (restr n y') (restr n z') := by
        intro n hn
        rw [hy', hz']
        exact lvlEdgeAt_restr hn x
      -- the tails agree beyond the cross position
      have htails : ∀ n, L₀ ≤ n → y' n = z' n := by
        intro n hn
        rw [hy', hz',
          prependWord_apply_of_le (by simp [length_canonicalWord]; omega),
          prependWord_apply_of_le (by simp [length_canonicalWord]; omega)]
        simp [length_canonicalWord]
      -- the witness-word chain
      set c : ℕ → List ℕ := fun n => (S n).cw (restr n y', restr n z') with hc
      have hchain : ∀ n, L₀ ≤ n → c n <+: c (n + 1) := by
        intro n hn
        have h2 := (hspec n).2 m (restr n y') (restr n z') (y' n) (hedge n hn)
        have hy2 : Fin.snoc (restr n y') (y' n) = restr (n + 1) y' := (restr_succ n y').symm
        have hz2 : Fin.snoc (restr n z') (y' n) = restr (n + 1) z' := by
          rw [htails n hn]
          exact (restr_succ n z').symm
        rw [hy2, hz2] at h2
        exact h2
      have hchain' : ∀ n N, L₀ ≤ n → n ≤ N → c n <+: c N := by
        intro n N hn hnN
        induction N with
        | zero => exact absurd hn (by omega)
        | succ N ih =>
          rcases eq_or_lt_of_le hnN with rfl | hlt
          · exact List.prefix_rfl
          · exact (ih (by omega)).trans (hchain N (by omega))
      have hlen : ∀ n, L₀ ≤ n → n ≤ L₀ + (c n).length := by
        intro n hn
        have := (S n).wlen m _ _ (hedge n hn)
        omega
      -- the limit witness word
      set wlim : ℕ → ℕ := fun j => (c (L₀ + j + 1)).getD j 0 with hwlim
      have hgetD : ∀ j n, L₀ + j + 1 ≤ n → (c n).getD j 0 = wlim j := by
        intro j n hn
        have hj1 : j < (c (L₀ + j + 1)).length := by
          have := hlen (L₀ + j + 1) (by omega)
          omega
        exact getD_of_prefix (hchain' (L₀ + j + 1) n (by omega) hn) hj1
      -- stage witnesses
      have hwitn : ∀ n, L₀ ≤ n → ∃ w, g (prepw (c n) w) = (a y' n, a z' n) := by
        intro n hn
        exact (S n).witness m _ _ (hedge n hn) (φseq n) (hφseq n)
      set W : ℕ → ℕ → ℕ := fun n =>
        if h : L₀ ≤ n then prepw (c n) ((hwitn n h).choose) else fun _ => 0 with hW
      have hgW : ∀ n, L₀ ≤ n → g (W n) = (a y' n, a z' n) := by
        intro n h
        rw [hW]
        simp only [dite_eq_left h]
        exact (hwitn n h).choose_spec
      -- the witness points converge to the limit word
      have hWlim : Filter.Tendsto W Filter.atTop (nhds wlim) := by
        rw [tendsto_pi_nhds]
        intro j
        refine tendsto_const_nhds.congr' ?_
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        refine ⟨L₀ + j + 1, fun n hn => ?_⟩
        have hL₀n : L₀ ≤ n := by omega
        have hjlen : j < (c n).length := by
          have := hlen n hL₀n
          omega
        rw [hW]
        simp only [dite_eq_left hL₀n]
        rw [prepw_apply_of_lt hjlen]
        exact (hgetD j n hn).symm
      -- identify the limits
      have hpair : Filter.Tendsto (fun n => g (W n)) Filter.atTop
          (nhds (φlim y', φlim z')) := by
        have h1 : Filter.Tendsto (fun n => (a y' n, a z' n)) Filter.atTop
            (nhds (φlim y', φlim z')) := (hφlim y').prodMk_nhds (hφlim z')
        refine h1.congr' ?_
        rw [Filter.EventuallyEq, Filter.eventually_atTop]
        exact ⟨L₀, fun n hn => (hgW n hn).symm⟩
      have hg2 : Filter.Tendsto (fun n => g (W n)) Filter.atTop (nhds (g wlim)) :=
        (hg.tendsto wlim).comp hWlim
      have hfinal : g wlim = (φlim y', φlim z') := tendsto_nhds_unique hg2 hpair
      rw [← hrange]
      exact hfinal ▸ mem_range_self wlim
    rcases hor with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · exact hkey y z hy hz
    · exact hsymm _ _ (hkey z y hz hy)

end Fusion

end G0Fusion
