/-
Copyright (c) 2026 Yann Pequignot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yann Pequignot
-/
import LeanPool.NashWilliams.Combinatorics.Front.Ray
import LeanPool.NashWilliams.Combinatorics.Front.Shrink
import LeanPool.NashWilliams.Data.Fintype.Pigeonhole

/-!
# The Nash-Williams theorem

The Nash-Williams theorem: a 2-coloring (equivalently, a subset `S`) of a front `F` on `M` admits
a monochromatic sub-front, i.e. an infinite `X ⊆ M` with `F | X ⊆ S` or `F | X ∩ S = ∅`. Here
`F | X` is `shrink F (M ∘ e)` for the increasing enumeration `M ∘ e` of `X`.

This file stages the development:

* `IsFront.nash_williams` — the base 2-color/subset theorem, by recursion on the rank of the
  front.
* `IsFront.nash_williams_fin` — the finite-color version, by induction on colors and
  color-blurring.
* `Front.ramsey_seq_of_nashWilliams` — the finite-arity infinite Ramsey theorem, obtained by
  instantiating the finite-color version at the uniform front `[M]^k` (`powK`).

Supporting lemmas:

* `Front.shrink_shrink` — restricting twice collapses to a single restriction.
* `Front.shrink_powK` — the restriction of a uniform front is the uniform front on the subset.

## Two proofs of infinite Ramsey

`Front.ramsey_seq_of_nashWilliams` re-derives `infinite_ramsey_seq` from the Nash-Williams
theorem. It is deliberately kept alongside the direct iterated-pigeonhole proof in
`NashWilliams.Combinatorics.Ramsey.Infinite`, and the two are *independent*: this file does not
import that one. The only lemmas the two developments share are the generic helpers in
`NashWilliams.Data`.
-/

open Set List

noncomputable section

namespace Front

variable {F : Set (List ℕ)} {M : ℕ → ℕ}

/-! ### Stage 1: the base 2-color / subset theorem -/

/-- Base case of the Nash-Williams recursion: the trivial front `F = {[]}` (`[] ∈ F`). Then
`shrink F M = {[]}`, monochromatic according to whether `[] ∈ S`. -/
private theorem nw_trivial (hF : IsFront F M) (h0 : [] ∈ F) (S : Set (List ℕ)) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
      (shrink F (M ∘ e) ⊆ S ∨ Disjoint (shrink F (M ∘ e)) S) := by
  refine ⟨id, strictMono_id, ?_⟩
  have hFeq : F = {[]} := by by_contra hne; exact (hF.nil_not_mem_iff.mpr hne) h0
  rw [Function.comp_id]
  have hsingle : ∀ s, s ∈ shrink F M → s = [] := by
    intro s hs; have := hs.1; rw [hFeq] at this; simpa using this
  by_cases hS : ([] : List ℕ) ∈ S
  · exact Or.inl fun s hs => (hsingle s hs) ▸ hS
  · refine Or.inr ?_
    rw [Set.disjoint_left]
    intro s hs hsS; rw [hsingle s hs] at hsS; exact hS hsS

/-- One step of the Nash-Williams ray recursion. Given a nontrivial front `F`, a tail `B` of `M`
with least element `B 0`, and the theorem as an oracle `ih` for all fronts of rank below `F`,
produce a sub-tail `T'` of `B`, all of whose elements exceed `B 0`, on which the ray front
`F after (B 0)` is monochromatic for `ray S (B 0)` (with the deciding colour recorded as `col`). -/
private theorem nw_step (hF : IsFront F M) (h0 : [] ∉ F) (S : Set (List ℕ))
    (ih : ∀ {M' : ℕ → ℕ} {F' : Set (List ℕ)} (hF' : IsFront F' M'), hF'.rank < hF.rank →
      ∀ S' : Set (List ℕ), ∃ e : ℕ → ℕ, StrictMono e ∧
        (shrink F' (M' ∘ e) ⊆ S' ∨ Disjoint (shrink F' (M' ∘ e)) S'))
    (T : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M}) :
    ∃ T' : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M},
      (∀ i, T'.1 i ∈ Set.range T.1) ∧ (∀ i, T.1 0 < T'.1 i) ∧
      ∃ col : Bool,
        (col = true → shrink (ray F (T.1 0)) T'.1 ⊆ ray S (T.1 0)) ∧
        (col = false → Disjoint (shrink (ray F (T.1 0)) T'.1) (ray S (T.1 0))) := by
  obtain ⟨B, hBmono, hBsub⟩ := T
  change ∃ T' : {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M},
      (∀ i, T'.1 i ∈ Set.range B) ∧ (∀ i, B 0 < T'.1 i) ∧
      ∃ col : Bool,
        (col = true → shrink (ray F (B 0)) T'.1 ⊆ ray S (B 0)) ∧
        (col = false → Disjoint (shrink (ray F (B 0)) T'.1) (ray S (B 0)))
  have hnM : B 0 ∈ Set.range M := hBsub 0
  have hRay : IsFront (ray F (B 0)) (rayEnum M (B 0)) := hF.ray_isFront_mem h0 hnM
  have hBtail_mono : StrictMono (fun i => B (i + 1)) := fun a b hab => hBmono (by omega)
  have hBtail_gt : ∀ i, B 0 < B (i + 1) := fun i => hBmono (by omega)
  have hBtail_ray : ∀ i, B (i + 1) ∈ Set.range (rayEnum M (B 0)) := fun i => by
    rw [mem_range_rayEnum_iff hF.mono]; exact ⟨hBsub (i + 1), hBtail_gt i⟩
  obtain ⟨E, hE, hEcomp⟩ :=
    exists_strictMono_comp (rayEnum_strictMono hF.mono (B 0)) hBtail_mono hBtail_ray
  have hG : IsFront (shrink (ray F (B 0)) (rayEnum M (B 0) ∘ E)) (rayEnum M (B 0) ∘ E) :=
    shrink_isFront hRay hE
  have hrank_lt : hG.rank < hF.rank :=
    lt_of_le_of_lt (hRay.shrink_rank_le hE) (hF.ray_rank_lt h0 hnM)
  obtain ⟨e, he, hdisj⟩ := ih hG hrank_lt (ray S (B 0))
  have hAeq : (rayEnum M (B 0) ∘ E) ∘ e = fun i => B (e i + 1) := by
    funext i; simp only [Function.comp_apply, hEcomp]
  have hA'mono : StrictMono (fun i => B (e i + 1)) :=
    fun a b hab => hBmono (by have := he hab; omega)
  have hA'M : ∀ i, B (e i + 1) ∈ Set.range M := fun i => hBsub (e i + 1)
  have hcollapse :
      shrink (shrink (ray F (B 0)) (rayEnum M (B 0) ∘ E)) ((rayEnum M (B 0) ∘ E) ∘ e)
        = shrink (ray F (B 0)) (fun i => B (e i + 1)) := by
    rw [shrink_shrink (Set.range_comp_subset_range e (rayEnum M (B 0) ∘ E)), hAeq]
  refine ⟨⟨fun i => B (e i + 1), hA'mono, hA'M⟩, fun i => ⟨e i + 1, rfl⟩,
    fun i => hBmono (by omega), ?_⟩
  rcases hdisj with hsub | hdis
  · exact ⟨true, fun _ => by rw [← hcollapse]; exact hsub, fun h => absurd h (by simp)⟩
  · exact ⟨false, fun h => absurd h (by simp), fun _ => by rw [← hcollapse]; exact hdis⟩

/-- Transfinite-recursion core of the Nash-Williams theorem, generalized over `M`, `F` and the
subset `S` and phrased with an explicit rank parameter so that `Ordinal.induction` applies. -/
private theorem nw_of_rank : ∀ (α : Ordinal) (M : ℕ → ℕ) (F : Set (List ℕ))
    (hF : IsFront F M) (S : Set (List ℕ)), hF.rank = α →
    ∃ e : ℕ → ℕ, StrictMono e ∧
      (shrink F (M ∘ e) ⊆ S ∨ Disjoint (shrink F (M ∘ e)) S) := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro M F hF S hrank
    by_cases h0 : [] ∈ F
    · exact nw_trivial hF h0 S
    · -- Nontrivial front `[] ∉ F`: the ray recursion.
      -- The induction hypothesis, packaged as a rank-bounded oracle for `nw_step`.
      have ih : ∀ {M' : ℕ → ℕ} {F' : Set (List ℕ)} (hF' : IsFront F' M'),
          hF'.rank < hF.rank → ∀ S' : Set (List ℕ), ∃ e : ℕ → ℕ, StrictMono e ∧
            (shrink F' (M' ∘ e) ⊆ S' ∨ Disjoint (shrink F' (M' ∘ e)) S') :=
        fun {M'} {F'} hF' hlt S' => IH hF'.rank (hrank ▸ hlt) M' F' hF' S' rfl
      -- Iterate the step by dependent choice.
      choose g hnest hgt gcol hcolT hcolF using nw_step hF h0 S ih
      let st : ℕ → {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M} :=
        fun k => Nat.rec
          (motive := fun _ => {B : ℕ → ℕ // StrictMono B ∧ ∀ i, B i ∈ Set.range M})
          ⟨M, hF.mono, fun i => ⟨i, rfl⟩⟩ (fun _ p => g p) k
      have hstep : ∀ k, st (k + 1) = g (st k) := fun _ => rfl
      let nn : ℕ → ℕ := fun k => (st k).1 0
      let cc : ℕ → Bool := fun k => gcol (st k)
      -- `nn` is a strictly increasing sequence of elements of `M`.
      have hnn_mono : StrictMono nn := by
        apply strictMono_nat_of_lt_succ
        intro k; have h := hgt (st k) 0; rw [← hstep k] at h; exact h
      have hnn_mem : ∀ k, nn k ∈ Set.range M := fun k => (st k).2.2 0
      -- Nesting of the tails, closed under `≤`.
      have hnest1 : ∀ k, ∀ i, (st (k + 1)).1 i ∈ Set.range (st k).1 := by
        intro k; rw [hstep k]; exact hnest (st k)
      have hnest_le : ∀ k l, Set.range (st (k + l)).1 ⊆ Set.range (st k).1 := by
        intro k l
        induction l with
        | zero => exact subset_rfl
        | succ m ih =>
          refine subset_trans ?_ ih
          rintro _ ⟨j, rfl⟩; exact hnest1 (k + m) j
      -- Pigeonhole: infinitely many steps share a colour `i`.
      obtain ⟨i, hi⟩ := exists_infinite_fiber_nat cc
      obtain ⟨φ, hφmono, hφmem⟩ := hi.exists_strictMono
      have hφcol : ∀ j, cc (φ j) = i := hφmem
      -- The chosen infinite subset `M ∘ e = {nn (φ j)}`.
      have hy_mono : StrictMono (fun j => nn (φ j)) := hnn_mono.comp hφmono
      have hy_mem : ∀ j, nn (φ j) ∈ Set.range M := fun j => hnn_mem (φ j)
      obtain ⟨e, he, hey⟩ := exists_strictMono_comp hF.mono hy_mono hy_mem
      refine ⟨e, he, ?_⟩
      -- Every element of the restricted front splits as `nn (φ j0) :: t` with `t` in the
      -- monochromatic sub-front at step `φ j0`.
      have key : ∀ s ∈ shrink F (M ∘ e), ∃ j0 t, s = nn (φ j0) :: t ∧
          t ∈ shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1 := by
        rintro s ⟨hsF, hsE⟩
        have hsne : s ≠ [] := fun h => h0 (h ▸ hsF)
        obtain ⟨a, t, rfl⟩ : ∃ a t, s = a :: t := by
          cases s with
          | nil => exact absurd rfl hsne
          | cons a t => exact ⟨a, t, rfl⟩
        have ha : a ∈ Set.range (M ∘ e) := hsE a List.mem_cons_self
        rw [hey] at ha
        obtain ⟨j0, hj0⟩ := ha
        have hj0 : nn (φ j0) = a := hj0
        refine ⟨j0, t, by rw [hj0], ?_, ?_⟩
        · change nn (φ j0) :: t ∈ F
          rw [hj0]; exact hsF
        · intro x hx
          have hxE : x ∈ Set.range (M ∘ e) := hsE x (List.mem_cons_of_mem a hx)
          rw [hey] at hxE
          obtain ⟨j', hj'⟩ := hxE
          have hj' : nn (φ j') = x := hj'
          have hax : a < x := (List.pairwise_cons.mp (hF.sorted (a :: t) hsF)).1 x hx
          rw [← hj0, ← hj'] at hax
          have hjj : φ j0 < φ j' := hnn_mono.lt_iff_lt.mp hax
          have hsub2 : Set.range (st (φ j')).1 ⊆ Set.range (st (φ j0 + 1)).1 := by
            obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (hjj : φ j0 + 1 ≤ φ j')
            rw [hd]; exact hnest_le (φ j0 + 1) d
          rw [← hj']; exact hsub2 ⟨0, rfl⟩
      -- Read off the uniform colour.
      cases i with
      | true =>
        refine Or.inl fun s hs => ?_
        obtain ⟨j0, t, hst, ht⟩ := key s hs
        have hsubset : shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1 ⊆ ray S (nn (φ j0)) := by
          have h := hcolT (st (φ j0)) (hφcol j0); rwa [← hstep (φ j0)] at h
        rw [hst]; exact hsubset ht
      | false =>
        refine Or.inr ?_
        rw [Set.disjoint_left]
        intro s hs hsS
        obtain ⟨j0, t, hst, ht⟩ := key s hs
        have hdisj2 :
            Disjoint (shrink (ray F (nn (φ j0))) (st (φ j0 + 1)).1) (ray S (nn (φ j0))) := by
          have h := hcolF (st (φ j0)) (hφcol j0); rwa [← hstep (φ j0)] at h
        rw [Set.disjoint_left] at hdisj2
        rw [hst] at hsS; exact hdisj2 ht hsS

/-- **The Nash-Williams theorem (subset form).** For a front `F` on `M` and any subset `S`, there
is an infinite subset `X ⊆ range M` on which the restricted front `shrinkOn F X` (the survey's
`F ↾ X`) is entirely inside `S` or entirely outside `S`.

The carrier is stated as a set `X`; its strictly monotone enumeration `N` (with `Set.range N = X`,
so that `shrinkOn F X = shrink F N`) is recovered through `Set.Infinite.exists_strictMono_range`.

Proved by transfinite recursion on `hF.rank` (the *ray recursion*). -/
theorem IsFront.nash_williams (hF : IsFront F M) (S : Set (List ℕ)) :
    ∃ X : Set ℕ, X ⊆ Set.range M ∧ X.Infinite ∧
      (shrinkOn F X ⊆ S ∨ Disjoint (shrinkOn F X) S) := by
  obtain ⟨e, he, hcase⟩ := nw_of_rank hF.rank M F hF S rfl
  refine ⟨Set.range (M ∘ e), Set.range_comp_subset_range e M,
    Set.infinite_range_of_injective (hF.mono.comp he).injective, ?_⟩
  rwa [shrink_eq_shrinkOn_range] at hcase

/-! ### Stage 2: the finite-color version -/

/-- Shrinking-palette core of the finite-color Nash-Williams theorem: if every element of the front
is colored within the finite palette `P`, some restriction is monochromatic. Proved by
well-founded induction on `P` (color-blurring), so the color type `κ` stays fixed. -/
private theorem nw_fin_aux {κ : Type*} (c : List ℕ → κ) (P : Finset κ) :
    ∀ (M : ℕ → ℕ) (F : Set (List ℕ)), IsFront F M → (∀ s ∈ F, c s ∈ P) →
      ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
        ∀ s ∈ shrink F (M ∘ e), c s = col := by
  classical
  induction P using Finset.strongInductionOn with
  | _ P IH =>
    intro M F hF hb
    -- Density gives an element of `F`, hence a color `a ∈ P` to blur on.
    obtain ⟨s0, hs0, -⟩ := hF.dense id strictMono_id
    have ha : c s0 ∈ P := hb s0 hs0
    -- Blur `c` to the 2-coloring "is it `c s0`?" and apply the base theorem.
    obtain ⟨e₁, he₁, hcase⟩ := nw_of_rank hF.rank M F hF {s | c s = c s0} rfl
    rcases hcase with hsub | hdis
    · exact ⟨e₁, he₁, c s0, fun s hs => hsub hs⟩
    · have hF' : IsFront (shrink F (M ∘ e₁)) (M ∘ e₁) := shrink_isFront hF he₁
      have hb' : ∀ s ∈ shrink F (M ∘ e₁), c s ∈ P.erase (c s0) := fun s hs =>
        Finset.mem_erase.mpr ⟨Set.disjoint_left.mp hdis hs, hb s hs.1⟩
      obtain ⟨e₂, he₂, col, hcol⟩ :=
        IH (P.erase (c s0)) (Finset.erase_ssubset ha) (M ∘ e₁) _ hF' hb'
      refine ⟨e₁ ∘ e₂, he₁.comp he₂, col, fun s hs => ?_⟩
      have hcol2 :
          shrink (shrink F (M ∘ e₁)) ((M ∘ e₁) ∘ e₂) = shrink F (M ∘ (e₁ ∘ e₂)) :=
        shrink_shrink (Set.range_comp_subset_range e₂ (M ∘ e₁))
      exact hcol s (hcol2 ▸ hs)

/-- **Finite-color Nash-Williams.** For a front `F` on `M` and a coloring `c` of finite lists by a
finite palette `κ`, there is an infinite subset `M ∘ e ⊆ M` on which `c` is constant over the
restricted front.

Obtained from `IsFront.nash_williams` by induction on the palette with color-blurring: split off one
color as a subset `S`, apply the base theorem, and recurse into the smaller palette on the
disjoint side (a front via `shrink_isFront`), composing restrictions with `shrink_shrink`. -/
theorem IsFront.nash_williams_fin (hF : IsFront F M) {κ : Type*} [Finite κ]
    (c : List ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ s ∈ shrink F (M ∘ e), c s = col := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  exact nw_fin_aux c Finset.univ M F hF (fun s _ => Finset.mem_univ _)

/-! ### Stage 3: the finite-arity infinite Ramsey theorem -/

/-- **Infinite Ramsey at arbitrary finite arity, via Nash-Williams.** A finite coloring `c` of the
size-`k` subsets of `ℕ` admits a strictly monotone `e` and a color `col` such that every size-`k`
subset of `range e` has color `col`.

Obtained by applying `IsFront.nash_williams_fin` to the uniform front `[ℕ]^k` (`powK id k`) with
the list-coloring `s ↦ c s.toFinset`, rewriting the restricted front via `shrink_powK`, and
bridging the size-`k` `Finset`s with their sorted lists. This matches `infinite_ramsey_seq` and
re-derives it from the Nash-Williams theorem. -/
theorem ramsey_seq_of_nashWilliams {κ : Type*} [Finite κ] (k : ℕ) (c : Finset ℕ → κ) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ col : κ,
      ∀ t : Finset ℕ, ↑t ⊆ Set.range e → t.card = k → c t = col := by
  classical
  -- Apply the finite-color theorem to `[ℕ]^k` with the list-coloring `c ∘ toFinset`.
  obtain ⟨e, he, col, hmono⟩ :=
    (isFront_powK (strictMono_id (α := ℕ)) k).nash_williams_fin (fun s => c s.toFinset)
  refine ⟨e, he, col, fun t hts htcard => ?_⟩
  -- The sorted list of `t` is a member of the restricted uniform front.
  have hmem : t.sort (· ≤ ·) ∈ powK (id ∘ e) k := by
    refine ⟨?_, (Finset.sortedLT_sort t).pairwise, fun x hx => ?_⟩
    · rw [Finset.length_sort]; exact htcard
    · rw [Finset.mem_sort] at hx; exact hts hx
  have hshr : t.sort (· ≤ ·) ∈ shrink (powK id k) (id ∘ e) := by
    rw [shrink_powK]; exact hmem
  have hc := hmono _ hshr
  rwa [Finset.sort_toFinset] at hc

end Front
