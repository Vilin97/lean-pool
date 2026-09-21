/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/
/-
# LeanPool.AsymptoticTrianglePacking.Internal — the SHARP per-vertex safe-degree variance

This is the one analytic input the iterable nibble round was missing.  The Bonferroni route of
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.SafeDegreeVariance` bounds the variance of `safeDeg(v)` by
`Δ²((r−1)²ε₂ + 2(r−1)³q_hi(q_hi²+ε₂)) + q_hi κ(r−1)Δ ≈ 2γ³Δ²`; the `Θ(γ³Δ²)` residue is a constant
factor too large to iterate.  Here we prove the sharp bound

  `Var(safeDeg(v)) ≤ 2p·r²κΔ²·(1 + prΔ + (prΔ)²)`,

i.e. `≈ 2rγκΔ` at the nibble retention `p = γ/(rΔ)` — with NO `Δ²` term.

The route is bounded differences (Efron–Stein).  Everything happens on the explicit Bernoulli cube
`Finset V → Bool` of `LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance`, where the Efron–Stein inequality
`LeanPool.AsymptoticTrianglePacking.Internal.Cube.centred_sq_le_sum_sq_diff` is available.  The combinatorial input is
`LeanPool.AsymptoticTrianglePacking.Internal.Tight.FlipStability`: flipping the retention of a single edge `k` moves the covered set only
inside `k ∪ ⋃ {f ∈ R : f meets k}`, so the safe degree at `v` moves by at most

  `edgeWeight k + ∑_{f ∈ R, f meets k} edgeWeight f`,  `edgeWeight f = ∑_{u ∈ f∖v} codeg(v,u)`.

Squaring, taking expectations and summing over `k` produces exactly the three terms above.
-/
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.CubeVariance
import LeanPool.AsymptoticTrianglePacking.Internal.Tight.FlipStability
import Mathlib.Algebra.Order.Chebyshev

open Finset Hypergraph LeanPool.AsymptoticTrianglePacking.Internal.Cube

namespace LeanPool.AsymptoticTrianglePacking.Internal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The cube picture of a round -/

/-- The retained set at a configuration of the cube. -/
def retSet (H : Finset (Finset V)) (ω : Finset V → Bool) : Finset (Finset V) :=
  H.filter (fun e => ω e = true)

/-- The safe degree at `v` as a function on the cube. -/
def safeDegCube (H : Finset (Finset V)) (v : V) (ω : Finset V → Bool) : ℝ :=
  (safeDegree H (covered (retSet H ω)) v : ℝ)

/-- The codegree weight of an edge as seen from `v`: `∑_{u ∈ f∖v} codeg(v,u)`. -/
def edgeWeight (H : Finset (Finset V)) (v : V) (f : Finset V) : ℝ :=
  ∑ u ∈ f.erase v, (codegree H v u : ℝ)

/-- The edges of `H` meeting `k`. -/
def meets (H : Finset (Finset V)) (k : Finset V) : Finset (Finset V) :=
  H.filter (fun f => ¬ Disjoint f k)

/-- The random part of the flip bound: the total codegree weight of the retained edges meeting
`k`. -/
def flipWeight (H : Finset (Finset V)) (v : V) (k : Finset V) (ω : Finset V → Bool) : ℝ :=
  ∑ f ∈ meets H k, (if ω f then edgeWeight H v f else 0)

/-! ## Elementary bounds on the codegree weight -/

omit [Fintype V] in
theorem edgeWeight_nonneg (H : Finset (Finset V)) (v : V) (f : Finset V) :
    0 ≤ edgeWeight H v f :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

omit [Fintype V] in
theorem edgeWeight_le_of_mem {H : Finset (Finset V)} {r κ : ℕ} (hr : IsUniform H r)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) {f : Finset V} (hf : f ∈ H) :
    edgeWeight H v f ≤ (r : ℝ) * (κ : ℝ) := by
  have hcard : (f.erase v).card ≤ r := by
    have := hr f hf
    calc (f.erase v).card ≤ f.card := Finset.card_erase_le
      _ = r := this
  calc edgeWeight H v f ≤ ∑ _u ∈ f.erase v, (κ : ℝ) := by
        refine Finset.sum_le_sum fun u hu => ?_
        have hne : v ≠ u := (Finset.ne_of_mem_erase hu).symm
        exact_mod_cast hκ v u hne
    _ = ((f.erase v).card : ℝ) * (κ : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (r : ℝ) * (κ : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)

/-- Double counting: `∑_{f ∈ H} edgeWeight f = ∑_{u ≠ v} codeg(v,u)·deg(u)`. -/
theorem sum_edgeWeight_eq (H : Finset (Finset V)) (v : V) :
    ∑ f ∈ H, edgeWeight H v f
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ) := by
  classical
  have hstep : ∀ f ∈ H, edgeWeight H v f
      = ∑ u ∈ (Finset.univ : Finset V).erase v, (if u ∈ f then (codegree H v u : ℝ) else 0) := by
    intro f _
    rw [edgeWeight, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext u
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ]
    tauto
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, degree]
  ring

theorem sum_edgeWeight_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) (v : V) :
    ∑ f ∈ H, edgeWeight H v f ≤ (r : ℝ) * (Δ : ℝ) ^ 2 := by
  classical
  rw [sum_edgeWeight_eq]
  have h1 : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ)
      ≤ ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (Δ : ℝ) := by
    refine Finset.sum_le_sum fun u _ => ?_
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hΔ u) (Nat.cast_nonneg _)
  have h2 : ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (Δ : ℝ)
      = ((((r - 1) * degree H v : ℕ)) : ℝ) * (Δ : ℝ) := by
    rw [← Finset.sum_mul, ← Nat.cast_sum, sum_codegree_erase_eq hr v]
  have h3 : ((((r - 1) * degree H v : ℕ)) : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by
    have hd : degree H v ≤ Δ := hΔ v
    have : (r - 1) * degree H v ≤ r * Δ := Nat.mul_le_mul (Nat.sub_le r 1) hd
    exact_mod_cast this
  have h4 : ((((r - 1) * degree H v : ℕ)) : ℝ) * (Δ : ℝ) ≤ ((r : ℝ) * (Δ : ℝ)) * (Δ : ℝ) :=
    mul_le_mul_of_nonneg_right h3 (Nat.cast_nonneg _)
  calc ∑ u ∈ (Finset.univ : Finset V).erase v, (codegree H v u : ℝ) * (degree H u : ℝ)
      ≤ ((r : ℝ) * (Δ : ℝ)) * (Δ : ℝ) := by rw [h2] at h1; linarith only [h1, h4]
    _ = (r : ℝ) * (Δ : ℝ) ^ 2 := by ring

theorem sum_edgeWeight_sq_le {H : Finset (Finset V)} {r Δ κ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    ∑ f ∈ H, edgeWeight H v f ^ 2 ≤ (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by
  have hstep : ∀ f ∈ H, edgeWeight H v f ^ 2 ≤ ((r : ℝ) * (κ : ℝ)) * edgeWeight H v f := by
    intro f hf
    have h1 := edgeWeight_le_of_mem hr hκ v hf
    have h2 := edgeWeight_nonneg H v f
    nlinarith only [h1, h2]
  calc ∑ f ∈ H, edgeWeight H v f ^ 2 ≤ ∑ f ∈ H, ((r : ℝ) * (κ : ℝ)) * edgeWeight H v f :=
        Finset.sum_le_sum hstep
    _ = ((r : ℝ) * (κ : ℝ)) * ∑ f ∈ H, edgeWeight H v f := by rw [Finset.mul_sum]
    _ ≤ ((r : ℝ) * (κ : ℝ)) * ((r : ℝ) * (Δ : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_edgeWeight_le hr hΔ v) (by positivity)
    _ = (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 := by ring

omit [Fintype V] in
/-- At most `rΔ` edges meet a given edge. -/
theorem card_meets_le {H : Finset (Finset V)} {r Δ : ℕ} (hr : IsUniform H r)
    (hΔ : ∀ y : V, degree H y ≤ Δ) {k : Finset V} (hk : k ∈ H) :
    ((meets H k).card : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by
  classical
  have hsub : meets H k ⊆ k.biUnion (fun x => H.filter (fun f => x ∈ f)) := by
    intro f hf
    rw [meets, Finset.mem_filter] at hf
    obtain ⟨x, hxf, hxk⟩ := Finset.not_disjoint_iff.mp hf.2
    exact Finset.mem_biUnion.mpr ⟨x, hxk, Finset.mem_filter.mpr ⟨hf.1, hxf⟩⟩
  have hcard : (meets H k).card ≤ r * Δ := by
    calc (meets H k).card ≤ (k.biUnion (fun x => H.filter (fun f => x ∈ f))).card :=
          Finset.card_le_card hsub
      _ ≤ ∑ x ∈ k, (H.filter (fun f => x ∈ f)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ k, Δ := Finset.sum_le_sum (fun x _ => hΔ x)
      _ = k.card * Δ := by rw [Finset.sum_const, smul_eq_mul]
      _ = r * Δ := by rw [hr k hk]
  exact_mod_cast hcard

omit [Fintype V] in
theorem meets_comm (H : Finset (Finset V)) (f : Finset V) :
    meets H f = H.filter (fun k => ¬ Disjoint f k) := by
  classical
  refine Finset.filter_congr fun k _ => ?_
  constructor
  · intro h hd; exact h (Disjoint.symm hd)
  · intro h hd; exact h (Disjoint.symm hd)

/-- A sum over a `biUnion` is at most the sum of the sums, for a nonnegative summand. -/
theorem sum_biUnion_le_of_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β] (B : Finset β)
    (t : β → Finset α) (g : α → ℝ) (hg : ∀ a, 0 ≤ g a) :
    ∑ u ∈ B.biUnion t, g u ≤ ∑ f ∈ B, ∑ u ∈ t f, g u := by
  classical
  induction B using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert hb]
      have h1 : ∑ u ∈ t b ∪ s.biUnion t, g u ≤ ∑ u ∈ t b, g u + ∑ u ∈ s.biUnion t, g u := by
        have hi := Finset.sum_union_inter (s₁ := t b) (s₂ := s.biUnion t) (f := g)
        have h0 : 0 ≤ ∑ u ∈ t b ∩ s.biUnion t, g u := Finset.sum_nonneg fun a _ => hg a
        linarith only [hi, h0]
      linarith only [ih, h1]

omit [Fintype V] in
/-- Double counting the incidences `k ∈ H`, `f ∈ meets H k`. -/
theorem sum_meets_swap (H : Finset (Finset V)) (g : Finset V → ℝ) :
    ∑ k ∈ H, ∑ f ∈ meets H k, g f = ∑ f ∈ H, ((meets H f).card : ℝ) * g f := by
  classical
  have hL : ∀ k ∈ H, ∑ f ∈ meets H k, g f
      = ∑ f ∈ H, (if ¬ Disjoint f k then g f else 0) := by
    intro k _
    rw [meets, Finset.sum_filter]
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have : ∑ k ∈ H, (if ¬ Disjoint f k then g f else 0)
      = ∑ _k ∈ H.filter (fun k => ¬ Disjoint f k), g f := by rw [Finset.sum_filter]
  rw [this, Finset.sum_const, nsmul_eq_mul, meets_comm]

/-! ## The flip bound -/

omit [Fintype V] in
theorem retSet_update_true {H : Finset (Finset V)} {k : Finset V} (hk : k ∈ H)
    (ω : Finset V → Bool) : retSet H (Function.update ω k true) = insert k (retSet H ω) := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet, hk]
  · simp [retSet, he]

omit [Fintype V] in
theorem retSet_update_false (H : Finset (Finset V)) (k : Finset V) (ω : Finset V → Bool) :
    retSet H (Function.update ω k false) = (retSet H ω).erase k := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet]
  · simp [retSet, he]

omit [Fintype V] in
theorem retSet_update_of_notMem {H : Finset (Finset V)} {k : Finset V} (hk : k ∉ H)
    (ω : Finset V → Bool) (b : Bool) : retSet H (Function.update ω k b) = retSet H ω := by
  classical
  ext e
  by_cases he : e = k
  · subst he; simp [retSet, hk]
  · simp [retSet, Function.update_of_ne he]

omit [Fintype V] in
/-- The codegree weight of the vertices spanned by a family of edges is at most the total
codegree weight of the family. -/
theorem sum_codegree_biUnion_le (H : Finset (Finset V)) (v : V) (B : Finset (Finset V)) :
    ∑ u ∈ ((B.biUnion id).erase v), (codegree H v u : ℝ) ≤ ∑ f ∈ B, edgeWeight H v f := by
  classical
  have hsub : (B.biUnion id).erase v ⊆ B.biUnion (fun f => f.erase v) := by
    intro u hu
    rw [Finset.mem_erase] at hu
    obtain ⟨f, hfB, huf⟩ := Finset.mem_biUnion.mp hu.2
    exact Finset.mem_biUnion.mpr ⟨f, hfB, Finset.mem_erase.mpr ⟨hu.1, huf⟩⟩
  calc ∑ u ∈ ((B.biUnion id).erase v), (codegree H v u : ℝ)
      ≤ ∑ u ∈ B.biUnion (fun f => f.erase v), (codegree H v u : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    _ ≤ ∑ f ∈ B, ∑ u ∈ f.erase v, (codegree H v u : ℝ) :=
        sum_biUnion_le_of_nonneg B (fun f => f.erase v) _ (fun _ => Nat.cast_nonneg _)
    _ = ∑ f ∈ B, edgeWeight H v f := rfl

omit [Fintype V] in
theorem flipWeight_nonneg (H : Finset (Finset V)) (v : V) (k : Finset V) (ω : Finset V → Bool) :
    0 ≤ flipWeight H v k ω := by
  refine Finset.sum_nonneg fun f _ => ?_
  by_cases h : ω f <;> simp [h, edgeWeight_nonneg H v f]

omit [Fintype V] in
theorem D_safeDegCube_of_notMem {H : Finset (Finset V)} {k : Finset V} (hk : k ∉ H) (v : V)
    (ω : Finset V → Bool) : Cube.D k (safeDegCube H v) ω = 0 := by
  simp [Cube.D, safeDegCube, retSet_update_of_notMem hk]

/-- **The bounded-differences bound.**  Flipping the retention of `k` moves the safe degree at `v`
by at most `edgeWeight k + flipWeight k`. -/
theorem abs_D_safeDegCube_le (H : Finset (Finset V)) (v : V) (k : Finset V)
    (ω : Finset V → Bool) :
    |Cube.D k (safeDegCube H v) ω| ≤ edgeWeight H v k + flipWeight H v k ω := by
  classical
  by_cases hk : k ∈ H
  · set R := retSet H ω with hR
    have hT : retSet H (Function.update ω k true) = insert k R := retSet_update_true hk ω
    have hF : retSet H (Function.update ω k false) = R.erase k := retSet_update_false H k ω
    have hflip := abs_safeDegree_flip_le H R k v
    have hcod : (((((flipInfluence R k).biUnion id).erase v).sum (fun u => codegree H v u) : ℕ) : ℝ)
        ≤ ∑ f ∈ flipInfluence R k, edgeWeight H v f := by
      have h := sum_codegree_biUnion_le H v (flipInfluence R k)
      rw [Nat.cast_sum]
      exact h
    have hins : ∑ f ∈ flipInfluence R k, edgeWeight H v f
        ≤ edgeWeight H v k + ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f := by
      rw [flipInfluence]
      by_cases hmem : k ∈ R.filter (fun f => ¬ Disjoint f k)
      · rw [Finset.insert_eq_self.mpr hmem]
        have := edgeWeight_nonneg H v k
        linarith only [this]
      · rw [Finset.sum_insert hmem]
    have hfilt : R.filter (fun f => ¬ Disjoint f k)
        = (meets H k).filter (fun f => ω f = true) := by
      ext f
      simp [hR, retSet, meets, Finset.mem_filter]
      tauto
    have hfw : ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f
        = flipWeight H v k ω := by
      rw [hfilt, flipWeight, Finset.sum_filter]
    have hnat : (((safeDegree H (covered (insert k R)) v : ℤ)
        - (safeDegree H (covered (R.erase k)) v : ℤ)).natAbs : ℝ)
        ≤ edgeWeight H v k + flipWeight H v k ω := by
      calc (((safeDegree H (covered (insert k R)) v : ℤ)
            - (safeDegree H (covered (R.erase k)) v : ℤ)).natAbs : ℝ)
          ≤ ((((((flipInfluence R k).biUnion id).erase v).sum
              (fun u => codegree H v u)) : ℕ) : ℝ) := by exact_mod_cast hflip
        _ ≤ ∑ f ∈ flipInfluence R k, edgeWeight H v f := hcod
        _ ≤ edgeWeight H v k + ∑ f ∈ R.filter (fun f => ¬ Disjoint f k), edgeWeight H v f := hins
        _ = edgeWeight H v k + flipWeight H v k ω := by rw [hfw]
    rw [Cube.D, safeDegCube, safeDegCube, hT, hF]
    set a := safeDegree H (covered (insert k R)) v
    set b := safeDegree H (covered (R.erase k)) v
    set m := ((a : ℤ) - (b : ℤ)).natAbs with hm
    have h2 : ((a : ℤ) - (b : ℤ)) ≤ (m : ℤ) ∧ -(m : ℤ) ≤ ((a : ℤ) - (b : ℤ)) := by omega
    refine abs_le.mpr ⟨?_, ?_⟩
    · have h3 : -(m : ℝ) ≤ (a : ℝ) - (b : ℝ) := by exact_mod_cast h2.2
      linarith only [hnat, h3]
    · have h3 : (a : ℝ) - (b : ℝ) ≤ (m : ℝ) := by exact_mod_cast h2.1
      linarith only [hnat, h3]
  · rw [D_safeDegCube_of_notMem hk v ω, abs_zero]
    have h1 := edgeWeight_nonneg H v k
    have h2 := flipWeight_nonneg H v k ω
    linarith only [h1, h2]

/-! ## The second moment of the flip weight -/

theorem Exp_flipWeight_sq_le {H : Finset (Finset V)} {p : ℝ} (v : V) (k : Finset V) :
    Cube.Exp p (fun ω => flipWeight H v k ω ^ 2)
      ≤ p * (∑ f ∈ meets H k, edgeWeight H v f ^ 2)
        + p ^ 2 * (∑ f ∈ meets H k, edgeWeight H v f) ^ 2 :=
  Cube.Exp_weighted_sum_sq_le (meets H k) (edgeWeight H v)

/-! ## The variance bound -/

/-- **The sharp per-vertex safe-degree variance bound.** -/
theorem safeDegCube_variance_le {H : Finset (Finset V)} {r Δ κ : ℕ} {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hr : IsUniform H r) (hΔ : ∀ y : V, degree H y ≤ Δ)
    (hκ : ∀ y z : V, y ≠ z → codegree H y z ≤ κ) (v : V) :
    Cube.Exp p (fun ω => (safeDegCube H v ω - Cube.Exp p (safeDegCube H v)) ^ 2)
      ≤ 2 * p * ((r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2)
          * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by
  classical
  set w : Finset V → ℝ := edgeWeight H v with hwdef
  set Q : Finset V → ℝ := fun k => ∑ f ∈ meets H k, w f ^ 2 with hQ
  set C : Finset V → ℝ := fun k => ∑ f ∈ meets H k, w f with hC
  set M : ℝ := (r : ℝ) ^ 2 * (κ : ℝ) * (Δ : ℝ) ^ 2 with hM
  have hrΔ : (0 : ℝ) ≤ (r : ℝ) * (Δ : ℝ) := by positivity
  have hMnn : 0 ≤ M := by rw [hM]; positivity
  have hES := Cube.centred_sq_le_sum_sq_diff hp0 hp1 (safeDegCube H v)
  have hzero : ∀ k ∈ (Finset.univ : Finset (Finset V)), k ∉ H →
      p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) = 0 := by
    intro k _ hk
    have hfun : (fun ω : Finset V → Bool => Cube.D k (safeDegCube H v) ω ^ 2)
        = fun _ => (0 : ℝ) := by
      funext ω; rw [D_safeDegCube_of_notMem hk]; ring
    rw [hfun, Cube.Exp_const]; ring
  have hsum : ∑ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
      = ∑ k : Finset V, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) :=
    Finset.sum_subset (Finset.subset_univ H) hzero
  have hterm : ∀ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
      ≤ p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2) := by
    intro k _
    have hEnn : 0 ≤ Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) :=
      Cube.Exp_nonneg hp0 hp1 (fun _ => sq_nonneg _)
    have hmono : Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
        ≤ Cube.Exp p (fun ω => 2 * w k ^ 2 + 2 * flipWeight H v k ω ^ 2) := by
      refine Cube.Exp_mono hp0 hp1 fun ω => ?_
      have h1 := abs_D_safeDegCube_le H v k ω
      have h2 : Cube.D k (safeDegCube H v) ω ^ 2 ≤ (w k + flipWeight H v k ω) ^ 2 := by
        have := abs_nonneg (Cube.D k (safeDegCube H v) ω)
        nlinarith [sq_abs (Cube.D k (safeDegCube H v) ω)]
      nlinarith [sq_nonneg (w k - flipWeight H v k ω)]
    have hexp : Cube.Exp p (fun ω => 2 * w k ^ 2 + 2 * flipWeight H v k ω ^ 2)
        = 2 * w k ^ 2 + 2 * Cube.Exp p (fun ω => flipWeight H v k ω ^ 2) := by
      rw [Cube.Exp_add (f := fun _ => 2 * w k ^ 2) (g := fun ω => 2 * flipWeight H v k ω ^ 2),
        Cube.Exp_const, Cube.Exp_smul]
    have hfw : Cube.Exp p (fun ω => flipWeight H v k ω ^ 2) ≤ p * Q k + p ^ 2 * C k ^ 2 :=
      Exp_flipWeight_sq_le v k
    have hstep : Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2)
        ≤ 2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2 := by
      rw [hexp] at hmono; nlinarith only [hmono, hfw]
    nlinarith only [hp0, hEnn, hmono, hexp, hfw]
  have hS2 : ∑ k ∈ H, w k ^ 2 ≤ M := sum_edgeWeight_sq_le hr hΔ hκ v
  have hQnn : ∀ k, 0 ≤ Q k := fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hSQ : ∑ k ∈ H, Q k ≤ ((r : ℝ) * (Δ : ℝ)) * M := by
    have h1 : ∑ k ∈ H, Q k = ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2 :=
      sum_meets_swap H (fun f => w f ^ 2)
    have h2 : ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2
        ≤ ∑ f ∈ H, ((r : ℝ) * (Δ : ℝ)) * w f ^ 2 :=
      Finset.sum_le_sum fun f hf =>
        mul_le_mul_of_nonneg_right (card_meets_le hr hΔ hf) (sq_nonneg _)
    have h3 : ∑ f ∈ H, ((r : ℝ) * (Δ : ℝ)) * w f ^ 2
        = ((r : ℝ) * (Δ : ℝ)) * ∑ f ∈ H, w f ^ 2 := by rw [Finset.mul_sum]
    rw [h1]
    calc ∑ f ∈ H, ((meets H f).card : ℝ) * w f ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * ∑ f ∈ H, w f ^ 2 := by
          rw [← h3]; exact h2
      _ ≤ ((r : ℝ) * (Δ : ℝ)) * M := mul_le_mul_of_nonneg_left hS2 hrΔ
  have hSC : ∑ k ∈ H, C k ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M) := by
    have h1 : ∀ k ∈ H, C k ^ 2 ≤ ((r : ℝ) * (Δ : ℝ)) * Q k := by
      intro k hk
      have hcs : C k ^ 2 ≤ ((meets H k).card : ℝ) * Q k := sq_sum_le_card_mul_sum_sq
      have := card_meets_le hr hΔ hk
      nlinarith [hQnn k]
    calc ∑ k ∈ H, C k ^ 2 ≤ ∑ k ∈ H, ((r : ℝ) * (Δ : ℝ)) * Q k := Finset.sum_le_sum h1
      _ = ((r : ℝ) * (Δ : ℝ)) * ∑ k ∈ H, Q k := by rw [Finset.mul_sum]
      _ ≤ ((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M) := mul_le_mul_of_nonneg_left hSQ hrΔ
  have hfinal : ∑ k ∈ H, p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2)
      = 2 * p * (∑ k ∈ H, w k ^ 2) + 2 * p ^ 2 * (∑ k ∈ H, Q k)
        + 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  calc Cube.Exp p (fun ω => (safeDegCube H v ω - Cube.Exp p (safeDegCube H v)) ^ 2)
      ≤ ∑ k : Finset V, p * (1 - p)
          * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) := hES
    _ = ∑ k ∈ H, p * (1 - p) * Cube.Exp p (fun ω => Cube.D k (safeDegCube H v) ω ^ 2) := hsum.symm
    _ ≤ ∑ k ∈ H, p * (2 * w k ^ 2 + 2 * p * Q k + 2 * p ^ 2 * C k ^ 2) := Finset.sum_le_sum hterm
    _ = 2 * p * (∑ k ∈ H, w k ^ 2) + 2 * p ^ 2 * (∑ k ∈ H, Q k)
        + 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2) := hfinal
    _ ≤ 2 * p * M + 2 * p ^ 2 * (((r : ℝ) * (Δ : ℝ)) * M)
        + 2 * p ^ 3 * (((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M)) := by
          have e1 : 2 * p * (∑ k ∈ H, w k ^ 2) ≤ 2 * p * M :=
            mul_le_mul_of_nonneg_left hS2 (by linarith)
          have e2 : 2 * p ^ 2 * (∑ k ∈ H, Q k) ≤ 2 * p ^ 2 * (((r : ℝ) * (Δ : ℝ)) * M) :=
            mul_le_mul_of_nonneg_left hSQ (by positivity)
          have e3 : 2 * p ^ 3 * (∑ k ∈ H, C k ^ 2)
              ≤ 2 * p ^ 3 * (((r : ℝ) * (Δ : ℝ)) * (((r : ℝ) * (Δ : ℝ)) * M)) :=
            mul_le_mul_of_nonneg_left hSC
              (mul_nonneg (by norm_num) (pow_nonneg hp0 3))
          linarith only [e1, e2, e3]
    _ = 2 * p * M * (1 + p * (r : ℝ) * (Δ : ℝ) + (p * (r : ℝ) * (Δ : ℝ)) ^ 2) := by ring

end LeanPool.AsymptoticTrianglePacking.Internal
