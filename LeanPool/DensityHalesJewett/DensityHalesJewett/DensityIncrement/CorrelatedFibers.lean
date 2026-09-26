/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.DensityIncrement.Parameters
public import LeanPool.DensityHalesJewett.DensityHalesJewett.Insensitive
import Mathlib.Tactic.Linarith

/-!
# Correlated fibers and many parameter lines

Uniformization and line canonization produce a subspace whose parameter-cube lines all have dense
common fibers; averaging over fixed suffixes then yields either an immediate density increment or a
suffix carrying many complete restricted-alphabet lines.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- A finite word family contains no complete combinatorial line. -/
def IsLineFree {α ι : Type*} (A : Finset (ι → α)) : Prop :=
  ∀ l : Combinatorics.Line α ι, ∃ a, l a ∉ A

/-- Pull a word family back to the parameter cube of a subspace. -/
noncomputable def pullback {η α ι : Type*} [Fintype (η → α)]
    (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι → α)) : Finset (η → α) :=
  parameterPreimage V A

/-- Pullback density agrees with the subspace-relative density. -/
lemma dens_pullback {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    (pullback V A).dens = Subspace.relativeDensity V A := by
  unfold pullback parameterPreimage Subspace.relativeDensity
  congr 1
  ext x
  simp only [Finset.mem_filter]

/-- The working parameter dimension of the correlated-fibers lemma. -/
noncomputable def correlatedFibersParameters (k m : ℕ) (δ : ℝ) : ℕ :=
  max m (Parameters.m₀ k δ)

/-- The line-canonization dimension of the correlated-fibers lemma. -/
noncomputable def correlatedFibersLines (k m : ℕ) (δ : ℝ) : ℕ :=
  max 1 (GrahamRothschild.bound (k + 1) 2 (correlatedFibersParameters k m δ))

/-- A bound for the correlated-fibers lemma.  Uniformization now returns its own coordinate cut,
so the bound constrains the total ambient dimension. -/
noncomputable def correlatedFibersBound (k m : ℕ) (δ : ℝ) : ℕ :=
  Subspace.variableCutFibersBound (k + 1) (correlatedFibersLines k m δ)
    (Parameters.η k δ ^ 2 / 2)

/-- Uniformization followed by line canonization produces a large subspace on which every
restricted-alphabet line is uniformly good or uniformly sparse. -/
lemma exists_uniform_fibers_and_homogeneous_lines {k M L : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
      ((∀ l : Combinatorics.Line (Fin k) (Fin M),
          Parameters.θ k δ ≤
            ((Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
        (∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ)) := by
  let : Nontrivial (Fin (k + 1)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      simp only [Fintype.card_fin]
      omega)
  let ε := Parameters.η k δ ^ 2 / 2
  have hε₀ : 0 < ε := by positivity [Parameters.η_pos hk hδ₀]
  by_cases hM : 1 ≤ M
  · have hL : 1 ≤ L := by
      by_contra hL
      obtain rfl : L = 0 := by omega
      obtain ⟨R, _⟩ :=
        GrahamRothschild.lines_twoColor (Fin (k + 1)) M 0
          (by simpa only [Fintype.card_fin] using hGR) ∅
      obtain ⟨i, _⟩ := R.proper ⟨0, hM⟩
      exact Fin.elim0 i
    obtain ⟨U, hU⟩ := huniform hL
    let : Fintype (Combinatorics.Line (Fin (k + 1)) (Fin L)) :=
      Subspace.lineFintype (k + 1) L
    let goodLines :=
      Finset.univ.filter fun q : Combinatorics.Line (Fin (k + 1)) (Fin L) ↦
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a : Fin k, Sum.elim (U (q a.castSucc)) y ∈ A).dens : ℝ)
    obtain ⟨R, hgood | hbad⟩ :=
      GrahamRothschild.lines_twoColor (Fin (k + 1)) M L
        (by simpa only [Fintype.card_fin] using hGR) goodLines
    · refine ⟨Subspace.compose U R, ?_, ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        linarith
      · left
        intro l
        have hl := hgood (l.map Fin.castSucc)
        simpa only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply,
          Subspace.compose_apply] using hl
    · refine ⟨Subspace.compose U R, ?_, ?_⟩
      · intro x
        rw [Subspace.compose_apply]
        have hx := hU (R x)
        linarith
      · right
        intro l
        have hl := hbad (l.map Fin.castSucc)
        simp only [goodLines, Finset.mem_filter, Finset.mem_univ, true_and,
          Subspace.mapLine_apply, Combinatorics.Line.map_apply] at hl
        simpa only [Subspace.compose_apply] using lt_of_not_ge hl
  · have hM₀ : M = 0 := by omega
    subst M
    let : Fintype (ι → Fin (k + 1)) := Fintype.ofFinite _
    have havg :
        δ ≤ 𝔼 x : ι → Fin (k + 1), ((fiber A x).dens : ℝ) := by
      simpa only [average_density_fiber] using hA
    obtain ⟨x, _, hx⟩ :=
      Finset.exists_le_of_le_expect Finset.univ_nonempty havg
    let W : Combinatorics.Subspace (Fin 0) (Fin (k + 1)) ι := {
      idxFun := fun i ↦ Sum.inl (x i)
      proper := fun e ↦ Fin.elim0 e
    }
    refine ⟨W, ?_, ?_⟩
    · intro z
      have hW : W z = x := by
        funext i
        simp only [W, Combinatorics.Subspace.coe_apply, Sum.elim_inl, id_eq]
      rw [hW]
      dsimp only [ε] at hε₀
      linarith
    · left
      intro l
      exact Fin.elim0 l.proper.choose

/-- Restricting the parameter directions of a good correlated-fibers subspace preserves its
uniform fiber and common-line-fiber estimates. -/
lemma restrict_correlated_fibers_subspace {k m M : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M)
    {δ : ℝ} {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  let R := Subspace.repeatInitial (Fin (k + 1)) hm hmM
  let V := Subspace.compose W R
  refine ⟨V, ?_, ?_⟩
  · intro x
    simpa only [V, Subspace.compose_apply] using hfibers (R x)
  · intro l
    let Rk := Subspace.repeatInitial (Fin k) hm hmM
    simpa only [V, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using
        hlines (Subspace.composeLine Rk l)

/-- Uniformize the fibers and canonize their line-density coloring.

The working parameter dimension is chosen large enough both for the requested `m`-dimensional
output and for the density Hales--Jewett argument at dimension `Parameters.m₀ k δ`.  In the
monochromatic good case, restrict the working subspace to `m` parameters.  In the bad case, retain
the larger subspace as a certificate whose every restricted-alphabet line has common-suffix density
strictly below `Parameters.θ k δ`. -/
lemma exists_correlated_fibers_or_sparse_certificate {k M L : ℕ} (hk : 2 ≤ k)
    (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hmM : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) ∨
      ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
        ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
          (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
          ∀ l : Combinatorics.Line (Fin k) (Fin M),
            ((Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
                Parameters.θ k δ := by
  obtain ⟨W, hfibers, hgood | hsparse⟩ :=
    exists_uniform_fibers_and_homogeneous_lines hk hδ₀ hGR A hA huniform
  · exact .inl <|
      restrict_correlated_fibers_subspace hm hmM A W hfibers hgood
  · right
    exact ⟨M, hm₀M, W, hfibers, hsparse⟩

/-- Uniformly dense fibers force a positive-density set of suffixes whose restricted parameter
slice has density at least `δ / 4`. -/
lemma dense_suffixes_of_uniform_fibers {k M : ℕ} (hk : 2 ≤ k)
    {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    δ / 4 ≤
      ((Finset.univ.filter fun y : κ → Fin (k + 1) ↦
        δ / 4 ≤
          ((Finset.univ.filter fun x : Fin M → Fin k ↦
            Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)).dens : ℝ) := by
  let : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  let f := fun y : κ → Fin (k + 1) ↦
    ((Finset.univ.filter fun x : Fin M → Fin k ↦
      Sum.elim (W (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hη₀ := Parameters.η_pos hk hδ₀
  have hηδ := Parameters.η_le_δ_div_six k δ
  have havg : δ - Parameters.η k δ ^ 2 / 2 ≤
      Finset.expect Finset.univ f := by
    rw [Subspace.average_restrictedParameterSlice]
    exact Finset.le_expect Finset.univ_nonempty fun x _ ↦ hfibers (Fin.castSucc ∘ x)
  have hthreshold := density_ge_threshold f
    (δ - Parameters.η k δ ^ 2 / 2) (δ / 4)
    (fun y ↦ by
      dsimp only [f]
      exact_mod_cast Finset.dens_le_one)
    (by nlinarith [sq_nonneg δ]) havg
  refine (le_div_iff₀ (by linarith : 0 < 1 - δ / 4)).mpr ?_ |>.trans hthreshold
  nlinarith [sq_nonneg δ]

/-- Density Hales--Jewett in every dense suffix slice, followed by finite pigeonhole, produces
one parameter line shared by at least a `θ`-density set of suffixes. -/
lemma exists_popular_line_of_dense_suffixes {k M : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) {δ : ℝ} (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hM : Parameters.m₀ k δ ≤ M)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι)
    (hfibers : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) :
    ∃ l : Combinatorics.Line (Fin k) (Fin M),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) := by
  classical
  let q := Parameters.m₀ k δ
  have hq₀ : 0 < q := Parameters.m₀_pos k δ
  let R := Subspace.repeatInitial (Fin (k + 1)) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  let W₀ := Subspace.compose W R
  have hW₀ : ∀ x,
      δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W₀ x)).dens : ℝ) := by
    intro x
    simpa only [W₀, Subspace.compose_apply] using hfibers (R x)
  have hdense := dense_suffixes_of_uniform_fibers hk hδ₀ hδ₁ A W₀ hW₀
  let := Subspace.lineFintype k q
  let B := Finset.univ.filter fun y : κ → Fin (k + 1) ↦
    δ / 4 ≤
      ((Finset.univ.filter fun x : Fin q → Fin k ↦
        Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A).dens : ℝ)
  have hB : δ / 4 ≤ (B.dens : ℝ) := by
    simpa only [B] using hdense
  have hBne : B.Nonempty :=
    Finset.dens_pos.mp (by exact_mod_cast lt_of_lt_of_le (by linarith : 0 < δ / 4) hB)
  have hbound : Subspace.densityOneBound k (δ / 4) ≤ q := by
    dsimp only [q]
    rw [Subspace.densityOneBound, dite_eq_left ⟨by linarith, hDHJ⟩,
      Parameters.m₀, dite_eq_left ⟨hδ₀, hDHJ⟩]
    omega
  have existsLine (y : κ → Fin (k + 1)) (hy : y ∈ B) :
      ∃ l : Combinatorics.Line (Fin k) (Fin q),
        ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    let S := Finset.univ.filter fun x : Fin q → Fin k ↦
      Sum.elim (W₀ (Fin.castSucc ∘ x)) y ∈ A
    obtain ⟨l, hl⟩ :=
      Subspace.densityOneBound_spec hDHJ (δ / 4) (by linarith) q hbound S <|
        Subspace.card_le_of_density_le (by omega) (δ / 4) S
          (by simpa only [B, Finset.mem_filter, Finset.mem_univ, true_and, S] using hy)
    exact ⟨l, fun a ↦ by
      simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hl a⟩
  choose lineAt hlineAt using fun y : {y // y ∈ B} ↦ existsLine y y.2
  let l₀ := lineAt ⟨hBne.choose, hBne.choose_spec⟩
  let : Nonempty (Combinatorics.Line (Fin k) (Fin q)) := ⟨l₀⟩
  let f : (κ → Fin (k + 1)) → Combinatorics.Line (Fin k) (Fin q) := fun y ↦
    if hy : y ∈ B then lineAt ⟨y, hy⟩ else l₀
  obtain ⟨l, hl⟩ := Subspace.exists_fiber_density B f
  have hcommon :
      (B.filter fun y ↦ f y = l) ⊆
        Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (W₀ (Fin.castSucc ∘ l a)) y ∈ A := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    have hline : lineAt ⟨y, hy.1⟩ = l := by
      simpa only [f, dite_eq_left hy.1] using hy.2
    intro a
    rw [← hline]
    exact hlineAt ⟨y, hy.1⟩ a
  have hcard :
      (Fintype.card (Combinatorics.Line (Fin k) (Fin q)) : ℝ) =
        ((k + 1 : ℕ) : ℝ) ^ q - (k : ℝ) ^ q := by
    rw [Subspace.card_line k q (by omega), Nat.cast_sub]
    · simp only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    · exact Nat.pow_le_pow_left (Nat.le_succ k) q
  have hθ :
      Parameters.θ k δ ≤
        (B.dens : ℝ) / Fintype.card (Combinatorics.Line (Fin k) (Fin q)) := by
    unfold Parameters.θ
    rw [← hcard]
    exact div_le_div_of_nonneg_right hB (by positivity)
  let Rk := Subspace.repeatInitial (Fin k) (Nat.one_le_iff_ne_zero.mpr hq₀.ne') hM
  refine ⟨Subspace.composeLine Rk l, hθ.trans (hl.trans ?_)⟩
  exact_mod_cast Finset.dens_le_dens <| by
    simpa only [W₀, R, Rk, Subspace.compose_apply, Subspace.composeLine_apply,
      Subspace.repeatInitial_map] using hcommon

/-- The uniformly sparse certificate is impossible.

Average the dense fibers over suffixes, find many suffix slices of density at least `δ / 4`, and
apply `hDHJ` on an embedded `Parameters.m₀ k δ`-dimensional parameter cube in each such slice.
Pigeonholing the resulting lines gives one line with common-suffix density at least
`Parameters.θ k δ`, contradicting the certificate. -/
lemma not_exists_sparse_correlated_fibers_certificate {k : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1))) :
    ¬ ∃ M : ℕ, Parameters.m₀ k δ ≤ M ∧
      ∃ W : Combinatorics.Subspace (Fin M) (Fin (k + 1)) ι,
        (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (W x)).dens : ℝ)) ∧
        ∀ l : Combinatorics.Line (Fin k) (Fin M),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (W (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) <
              Parameters.θ k δ := by
  rintro ⟨M, hM, W, hfibers, hsparse⟩
  obtain ⟨l, hl⟩ :=
    exists_popular_line_of_dense_suffixes hk hDHJ hδ₀ hδ₁ hM A W hfibers
  exact (not_lt_of_ge hl) (hsparse l)

/-- Every parameter-cube line in a suitable subspace has a dense common fiber. -/
lemma exists_subspace_correlated_fibers {k M L : ℕ} (hk : 2 ≤ k)
    (hDHJ : HasDensityHJ k) (m : ℕ) (hm : 1 ≤ m)
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Finite ι] [Fintype (κ → Fin (k + 1))]
    [Fintype (ι ⊕ κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (hmM : m ≤ M) (hm₀M : Parameters.m₀ k δ ≤ M)
    (hGR : GrahamRothschild.bound (k + 1) 2 M ≤ L)
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (hA : δ ≤ (A.dens : ℝ))
    (huniform : 1 ≤ L → ∃ U : Combinatorics.Subspace (Fin L) (Fin (k + 1)) ι,
      ∀ x, (A.dens : ℝ) - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (U x)).dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι,
      (∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ)) ∧
      ∀ l : Combinatorics.Line (Fin k) (Fin m),
        Parameters.θ k δ ≤
          ((Finset.univ.filter fun y ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
  (exists_correlated_fibers_or_sparse_certificate hk m hm δ hδ₀ hmM hm₀M hGR A hA
    huniform).resolve_right (not_exists_sparse_correlated_fibers_certificate hk hDHJ δ hδ₀ hδ₁ A)

/-- The pullback of a word family to a subspace after fixing the suffix coordinates. -/
def suffixPullback {α η ι κ : Type*} [Fintype (η → α)]
    [DecidableEq (ι ⊕ κ → α)] (V : Combinatorics.Subspace η α ι)
    (A : Finset (ι ⊕ κ → α)) (y : κ → α) : Finset (η → α) :=
  Finset.univ.filter fun x ↦ Sum.elim (V x) y ∈ A

/-- The parameter lines whose first-`k` points belong to a word family at a fixed suffix. -/
def suffixLines {k m : ℕ} {ι κ : Type*}
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (y : κ → Fin (k + 1)) :
    Finset (Combinatorics.Line (Fin k) (Fin m)) :=
  Finset.univ.filter fun l ↦ ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A

/-- Fix suffix coordinates of a subspace. -/
def Subspace.fixSuffix {α η ι κ : Type*} (V : Combinatorics.Subspace η α ι)
    (y : κ → α) : Combinatorics.Subspace η α (ι ⊕ κ) where
  idxFun := Sum.elim V.idxFun (Sum.inl ∘ y)
  proper e := by
    obtain ⟨i, hi⟩ := V.proper e
    exact ⟨Sum.inl i, hi⟩

/-- Fix suffix coordinates and transport the ambient coordinates along an equivalence. -/
def Subspace.fixSuffixReindex {α η ι κ ζ : Type*} (e : ι ⊕ κ ≃ ζ)
    (V : Combinatorics.Subspace η α ι) (y : κ → α) :
    Combinatorics.Subspace η α ζ :=
  (Subspace.fixSuffix V y).reindex (Equiv.refl _) (Equiv.refl _) e

/-- Pointwise fiber lower bounds imply the corresponding average lower bound for fixed-suffix
pullbacks.  This is a finite double-counting argument. -/
lemma average_suffixPullback_lower {α η ι κ : Type*} [Nonempty α] [Fintype (η → α)]
    [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (ι ⊕ κ → α)) (r : ℝ)
    (hV : ∀ x, r ≤ ((fiber A (V x)).dens : ℝ)) :
    r ≤ 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) =
      𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
    calc
      𝔼 x : η → α, ((fiber A (V x)).dens : ℝ)
          = 𝔼 x : η → α, 𝔼 y : κ → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        simp
      _ = 𝔼 y : κ → α, 𝔼 x : η → α, (Set.indicator (fiber A (V x)) (1 : (κ → α) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (η → α)) (Finset.univ : Finset (κ → α))]
      _ = 𝔼 y : κ → α, 𝔼 x : η → α,
          (Set.indicator (suffixPullback V A y) (1 : (η → α) → ℝ) x : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro x _
        by_cases h : Sum.elim (V x) y ∈ A <;> simp [fiber, suffixPullback, h]
      _ = 𝔼 y : κ → α, ((suffixPullback V A y).dens : ℝ) := by
        simp
  have h_r_le_expect : r ≤ 𝔼 x : η → α, ((fiber A (V x)).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := η → α)) fun x _ => hV x
  exact h_r_le_expect.trans h_expect_eq.le

/-- If a function has average at least `δ - η²/2` but never reaches `δ + η²/2`, then it is at
least `δ - 2η` on all but an `η`-fraction of its domain. -/
lemma density_near_average {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (δ η : ℝ) (hη₀ : 0 < η)
    (havg : δ - η ^ 2 / 2 ≤ 𝔼 x : X, f x)
    (hupper : ∀ x, f x < δ + η ^ 2 / 2) :
    1 - η ≤ ((Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x).dens : ℝ) := by
  set H := Finset.univ.filter fun x ↦ δ - 2 * η ≤ f x
  by_cases hH : 1 - η ≤ (H.dens : ℝ)
  · exact hH
  · exfalso
    have hfg : ∀ x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η)
        * (Set.indicator H (1 : X → ℝ) x : ℝ) := by
      intro x
      by_cases hxH : x ∈ H
      · rw [Set.indicator_of_mem (by simpa using hxH), Pi.one_apply, mul_one]
        linarith [hupper x]
      · rw [Set.indicator_of_notMem (by simpa using hxH), mul_zero, add_zero]
        have : ¬(δ - 2 * η ≤ f x) := by simpa [H] using hxH
        linarith
    have hexpect : 𝔼 x : X, f x ≤ (δ - 2 * η) + (η ^ 2 / 2 + 2 * η) * ((H.dens : ℝ)) := by
      apply (Finset.expect_le_expect fun x _ ↦ hfg x).trans_eq
      rw [Finset.expect_add_distrib, Finset.expect_const univ_nonempty, ← Finset.mul_expect]
      simp
    linarith [havg, hexpect,
      mul_le_mul_of_nonneg_left (not_le.mp hH).le (by positivity : (0 : ℝ) ≤ η ^ 2 / 2 + 2 * η),
      mul_pos hη₀ hη₀, pow_pos hη₀ 3]

/-- Dense common suffix fibers for every line give the same lower bound for the average
fixed-suffix line density.  This is the second finite double-counting step. -/
lemma average_suffixLines_lower {k m : ℕ} {ι κ : Type*}
    [Fintype (κ → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (A : Finset (ι ⊕ κ → Fin (k + 1))) (θ : ℝ)
    (hV : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      θ ≤ ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    θ ≤ 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
  have h_expect_eq : 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) =
      𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
    calc
      𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          ((Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)
          = 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
            𝔼 y : κ → Fin (k + 1),
            (Set.indicator (Finset.univ.filter fun y ↦
              ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
              (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        apply Finset.expect_congr rfl
        intro l _
        rw [← Finset.expect_indicator_one]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (Finset.univ.filter fun y ↦
            ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A)
            (1 : (κ → Fin (k + 1)) → ℝ) y : ℝ) := by
        rw [Finset.expect_comm (Finset.univ : Finset (Combinatorics.Line (Fin k) (Fin m)))
          (Finset.univ : Finset (κ → Fin (k + 1)))]
      _ = 𝔼 y : κ → Fin (k + 1),
          𝔼 l : Combinatorics.Line (Fin k) (Fin m),
          (Set.indicator (suffixLines V A y)
            (1 : Combinatorics.Line (Fin k) (Fin m) → ℝ) l : ℝ) := by
        apply Finset.expect_congr rfl
        intro y _
        apply Finset.expect_congr rfl
        intro l _
        dsimp [suffixLines]
        by_cases h : ∀ a : Fin k, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A <;> simp [h]
      _ = 𝔼 y : κ → Fin (k + 1), ((suffixLines V A y).dens : ℝ) := by
        simp
  have h_θ_le_expect : θ ≤ 𝔼 l : Combinatorics.Line (Fin k) (Fin m),
      ((Finset.univ.filter fun y ↦
        ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ) :=
    Finset.le_expect (Finset.univ_nonempty (α := Combinatorics.Line (Fin k) (Fin m)))
      fun l _ => hV l
  exact h_θ_le_expect.trans h_expect_eq.le

/-- A function bounded above by one with average at least `θ` exceeds `θ/2` on a set of
density at least `θ/2`. -/
lemma density_half_threshold {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ ≤ 1)
    (hf₁ : ∀ x, f x ≤ 1) (havg : θ ≤ 𝔼 x : X, f x) :
    θ / 2 ≤ ((Finset.univ.filter fun x ↦ θ / 2 ≤ f x).dens : ℝ) := by
  refine le_trans ?_
    (density_ge_threshold f θ (θ / 2) hf₁ (by linarith) havg)
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - θ / 2)]
  nlinarith [sq_nonneg (θ / 2)]

/-- Two subsets of densities at least `1-η` and `θ/2` intersect when `η < θ/2`. -/
lemma exists_mem_inter_of_large_density {X : Type*} [Fintype X]
    (S T : Finset X) (η θ : ℝ)
    (hS : 1 - η ≤ (S.dens : ℝ)) (hT : θ / 2 ≤ (T.dens : ℝ))
    (hηθ : η < θ / 2) : ∃ x, x ∈ S ∧ x ∈ T := by
  classical
  by_contra h
  have hunion : ((S ∪ T).dens : ℝ) = (S.dens : ℝ) + (T.dens : ℝ) := by
    exact_mod_cast Finset.dens_union_of_disjoint
      (Finset.disjoint_left.mpr fun x hxS hxT ↦ h ⟨x, hxS, hxT⟩)
  have hle : ((S ∪ T).dens : ℝ) ≤ 1 := by
    exact_mod_cast Finset.dens_le_one (s := S ∪ T)
  linarith [hunion, hle]

/-- Correlated fibers yield either a dense fixed suffix or a fixed suffix supporting many
complete parameter lines. -/
lemma exists_suffix_many_lines {k m : ℕ} (hk : 2 ≤ k)
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    {ι κ : Type*} [Fintype (Fin m → Fin (k + 1))]
    [Fintype (κ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (A : Finset (ι ⊕ κ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (hfiber : ∀ x, δ - Parameters.η k δ ^ 2 / 2 ≤ ((fiber A (V x)).dens : ℝ))
    (hlines : ∀ l : Combinatorics.Line (Fin k) (Fin m),
      Parameters.θ k δ ≤
        ((Finset.univ.filter fun y ↦
          ∀ a, Sum.elim (V (Fin.castSucc ∘ l a)) y ∈ A).dens : ℝ)) :
    (∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤
      ((suffixPullback V A y).dens : ℝ)) ∨
    ∃ y, δ - 2 * Parameters.η k δ ≤ ((suffixPullback V A y).dens : ℝ) ∧
      Parameters.θ k δ / 2 ≤ ((suffixLines V A y).dens : ℝ) := by
  classical
  let f := fun y : κ → Fin (k + 1) ↦ ((suffixPullback V A y).dens : ℝ)
  let g := fun y : κ → Fin (k + 1) ↦ ((suffixLines V A y).dens : ℝ)
  by_cases hinc : ∃ y, δ + Parameters.η k δ ^ 2 / 2 ≤ f y
  · exact .inl hinc
  right
  have hη₀ : 0 < Parameters.η k δ := Parameters.η_pos hk hδ₀
  have hη₁ : Parameters.η k δ ≤ 1 :=
    (Parameters.η_le_δ_div_six k δ).trans (by linarith)
  have havgf : δ - Parameters.η k δ ^ 2 / 2 ≤ 𝔼 y, f y :=
    average_suffixPullback_lower V A _ hfiber
  have hupper : ∀ y, f y < δ + Parameters.η k δ ^ 2 / 2 := by
    intro y
    exact lt_of_not_ge fun hy ↦ hinc ⟨y, hy⟩
  have hmostly : 1 - Parameters.η k δ ≤
      ((Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y).dens : ℝ) :=
    density_near_average f δ (Parameters.η k δ) hη₀ havgf hupper
  have havgg : Parameters.θ k δ ≤ 𝔼 y, g y :=
    average_suffixLines_lower V A (Parameters.θ k δ) hlines
  have hmany : Parameters.θ k δ / 2 ≤
      ((Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y).dens : ℝ) := by
    refine density_half_threshold g (Parameters.θ k δ) (Parameters.θ_pos hk hδ₀)
      (Parameters.θ_le_one hk hδ₁) ?_ havgg
    intro y
    dsimp only [g]
    exact_mod_cast Finset.dens_le_one (s := suffixLines V A y)
  obtain ⟨y, hy₁, hy₂⟩ := exists_mem_inter_of_large_density
    (Finset.univ.filter fun y ↦ δ - 2 * Parameters.η k δ ≤ f y)
    (Finset.univ.filter fun y ↦ Parameters.θ k δ / 2 ≤ g y)
    (Parameters.η k δ) (Parameters.θ k δ) hmostly hmany
    (Parameters.η_lt_θ_div_two hk hδ₀)
  refine ⟨y, ?_, ?_⟩
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, f] using hy₁
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and, g] using hy₂

/-- Fixing a suffix and reindexing preserves the relative-density and complete-line statistics.
The proof is coordinate bookkeeping using `Subspace.reindex_apply` and `Finset.mem_map_equiv`. -/
lemma Subspace.fixSuffixReindex_statistics {k m : ℕ} {ι κ ζ : Type*}
    [Fintype (Fin m → Fin (k + 1))]
    [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [DecidableEq (ζ → Fin (k + 1))]
    [DecidableEq (ι ⊕ κ → Fin (k + 1))]
    (e : ι ⊕ κ ≃ ζ) (A : Finset (ζ → Fin (k + 1)))
    (V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι)
    (y : κ → Fin (k + 1)) :
    let A' := A.map ((e.arrowCongr (Equiv.refl _)).symm.toEmbedding)
    (Subspace.relativeDensity (Subspace.fixSuffixReindex e V y) A : ℝ) =
        ((suffixPullback V A' y).dens : ℝ) ∧
      ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
        ∀ a, Subspace.fixSuffixReindex e V y (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) =
        ((suffixLines V A' y).dens : ℝ) := by
  intro A'
  have h_fixSuffix_eval (x : Fin m → Fin (k + 1)) :
      (Subspace.fixSuffix V y : (Fin m → Fin (k + 1)) → (ι ⊕ κ → Fin (k + 1))) x
        = Sum.elim (V x) y := by
    ext j
    cases j <;> simp [Subspace.fixSuffix, Combinatorics.Subspace.coe_apply]
  have h_eval (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x = Sum.elim (V x) y ∘ e.symm := by
    calc
      Subspace.fixSuffixReindex e V y x
          = (Subspace.fixSuffix V y) x ∘ e.symm := by
        ext i
        simp [Subspace.fixSuffixReindex, Combinatorics.Subspace.reindex_apply]
      _ = Sum.elim (V x) y ∘ e.symm := by rw [h_fixSuffix_eval x]
  have h_mem_map (x : Fin m → Fin (k + 1)) :
      Subspace.fixSuffixReindex e V y x ∈ A ↔ Sum.elim (V x) y ∈ A' := by
    rw [h_eval x]
    dsimp [A']
    simp [Finset.mem_map_equiv, Equiv.arrowCongr]
  constructor
  · dsimp [Subspace.relativeDensity, suffixPullback]
    congr
    ext x
    simp [h_mem_map x]
  · dsimp [suffixLines]
    congr
    ext l
    exact forall_congr' fun a ↦ h_mem_map (Fin.castSucc ∘ l a)

/-- A bound for the many-lines lemma. -/
noncomputable def manyLinesBound (k m : ℕ) (δ : ℝ) : ℕ :=
  correlatedFibersBound k m δ

/-- Either density has already increased on an `m`-subspace, or a dense slice contains a positive
proportion of all parameter-cube lines. -/
lemma exists_subspace_many_lines {k : ℕ} (hk : 2 ≤ k) (hDHJ : HasDensityHJ k)
    (m : ℕ) [Fintype (Combinatorics.Line (Fin k) (Fin m))]
    [Nonempty (Combinatorics.Line (Fin k) (Fin m))]
    (hm : 1 ≤ m) (δ : ℝ) (hδ₀ : 0 < δ) (hδ₁ : δ ≤ 1)
    (n : ℕ) (hn : manyLinesBound k m δ ≤ n)
    (A : Finset (Fin n → Fin (k + 1))) (hA : δ ≤ (A.dens : ℝ)) :
    (∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ + Parameters.η k δ ^ 2 / 2 ≤ (Subspace.relativeDensity V A : ℝ)) ∨
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n),
      δ - 2 * Parameters.η k δ ≤ (Subspace.relativeDensity V A : ℝ) ∧
      Parameters.θ k δ / 2 ≤
        ((Finset.univ.filter fun l : Combinatorics.Line (Fin k) (Fin m) ↦
          ∀ a, V (Fin.castSucc ∘ l a) ∈ A).dens : ℝ) := by
  classical
  have hε₀ : 0 < Parameters.η k δ ^ 2 / 2 := by
    positivity [Parameters.η_pos hk hδ₀]
  obtain ⟨p, q, e, _hq, U, hU⟩ :=
    Subspace.variableCutFibersBound_spec (k + 1) (correlatedFibersLines k m δ) n
      (le_max_left _ _) hε₀ (by simpa only [manyLinesBound, correlatedFibersBound] using hn) A
  let A' := Subspace.splitWords e A
  have hA' : δ ≤ (A'.dens : ℝ) := by
    simpa only [A', Subspace.dens_splitWords] using hA
  obtain ⟨W, hWfiber, hWlines⟩ :=
    exists_subspace_correlated_fibers hk hDHJ m hm δ hδ₀ hδ₁
      (ι := Fin p) (κ := Fin q) (M := correlatedFibersParameters k m δ)
      (L := correlatedFibersLines k m δ) (le_max_left _ _) (le_max_right _ _)
      (le_max_right _ _) A' hA' (fun _ ↦ ⟨U, fun x ↦ by
        simpa only [A', Subspace.dens_splitWords] using hU x⟩)
  obtain ⟨y, hy⟩ | ⟨y, hy, hylines⟩ :=
    exists_suffix_many_lines hk δ hδ₀ hδ₁ A' W hWfiber hWlines
  · left
    use Subspace.fixSuffixReindex e W y
    rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
    simpa only [A', Subspace.splitWords] using hy
  · right
    refine ⟨Subspace.fixSuffixReindex e W y, ?_, ?_⟩
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).1]
      simpa only [A', Subspace.splitWords] using hy
    · rw [(Subspace.fixSuffixReindex_statistics e A W y).2]
      simpa only [A', Subspace.splitWords] using hylines

end DensityHalesJewett
