/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Construction.Fibers
import LeanPool.Nikodym.Nikodym.Construction.ProductCriterion

/-!
# Tangent lines on the product set

This file implements blueprint node T01 of `docs/nikodym_construction_lean_blueprint.md`.

Everything is parametrised by `k = h - 1` (the number of digits), as in `Fibers.lean`: digit
vectors are `Fin k → R`, points of `F ^ h` are `Fin (k + 1) → F` built with `Fin.snoc`.

* Definitions: the point `Scaffold.pt φ n q k a w = (φ (a i))_i ++ φ (base w)`, the direction
  `Scaffold.dir φ w = (φ (w i))_i ++ 1`, the product family
  `Scaffold.ptFamily φ n q k A B = (A.image φ, …, A.image φ, B.image (φ ∘ base))` and the
  product set `Scaffold.ptSet φ n q k A B = Fintype.piFinset (ptFamily …)`, so that
  `ptSet = φ(A)^k × φ(b(B))`.
* T01a: `Scaffold.eq_zero_of_map_eq_zero_of_lt_M` (small kernel on boxes of radius `< M`),
  `Scaffold.eq_of_map_eq_of_box`, `Scaffold.injOn_of_box`, `Scaffold.injOn_A`,
  `Scaffold.eq_of_map_base_eq`, `Scaffold.injOn_base_B`, `Scaffold.pt_injOn`.
* T01b: `Scaffold.eq_zero_of_map_eq_zero_of_small`.
* T01c: `Scaffold.prefixSumBelow` (`y_{i-1}`), `Scaffold.abs_prefixSumBelow_le`,
  `Scaffold.base_sub_base_eq`, `Scaffold.abs_mul_sub_prefixSum_le`,
  `Scaffold.digit_eq_of_trace_eq_zero` (the D02 step) and `Scaffold.no_collision`.
* Main statements: `Scaffold.tangent_hypothesis` (the hypothesis of P01 for `ptSet`),
  `Scaffold.card_ptSet` (`#ptSet = #A ^ k * #B`) and
  `Scaffold.isNikodym_univ_sdiff_ptSet` (`univ \ ptSet` is a Nikodym set).

Throughout, `n` and `q` are the integer parameters of Q01, related to the types by
`Fintype.card ι = n` and `Fintype.card F = q`; the constants are given as hypotheses
`ρ = 1 / (100 (k + 1) √n)` and `γ = 1 / 10`. Only `1 ≤ n` and `1 ≤ q` are needed here (the
Q02 threshold `2 ^ (n 2 ^ k) ≤ q` implies `1 ≤ q`). Declarations involving `Finset.image`
carry a `[DecidableEq F]` assumption (consumers may use `classical`).
-/

namespace Nikodym

namespace Scaffold

/-! ### Blueprint T01: points, directions and the product set -/

section Defs

variable {R F : Type*} [CommRing R] [Field F]

/-- Blueprint T01: the point `p(a, w) = (φ (a 0), …, φ (a (k-1)), φ (b(w))) ∈ F ^ (k + 1)`. -/
noncomputable def pt (φ : R →+* F) (n q k : ℕ) (a w : Fin k → R) : Fin (k + 1) → F :=
  Fin.snoc (fun i ↦ φ (a i)) (φ (base n q k w))

/-- Blueprint T01: the direction `v(w) = (φ (w 0), …, φ (w (k-1)), 1) ∈ F ^ (k + 1)`. -/
noncomputable def dir (φ : R →+* F) {k : ℕ} (w : Fin k → R) : Fin (k + 1) → F :=
  Fin.snoc (fun i ↦ φ (w i)) 1

variable (φ : R →+* F) {n q k : ℕ}

/-- Blueprint T01: the first `k` coordinates of `pt`. -/
@[simp] theorem pt_castSucc (a w : Fin k → R) (i : Fin k) :
    pt φ n q k a w (Fin.castSucc i) = φ (a i) := by
  simp [pt]

/-- Blueprint T01: the last coordinate of `pt`. -/
@[simp] theorem pt_last (a w : Fin k → R) : pt φ n q k a w (Fin.last k) = φ (base n q k w) := by
  simp [pt]

/-- Blueprint T01: the first `k` coordinates of `dir`. -/
@[simp] theorem dir_castSucc (w : Fin k → R) (i : Fin k) :
    dir φ w (Fin.castSucc i) = φ (w i) := by
  simp [dir]

/-- Blueprint T01: the last coordinate of `dir`. -/
@[simp] theorem dir_last (w : Fin k → R) : dir φ w (Fin.last k) = 1 := by
  simp [dir]

/-- Blueprint T01: `v(w) ≠ 0`. -/
theorem dir_ne_zero (w : Fin k → R) : dir φ w ≠ 0 := fun h ↦ by
  have := congrFun h (Fin.last k)
  simp at this

variable [DecidableEq F]

/-- Blueprint T01: the family of factors `(φ(A), …, φ(A), φ(b(B)))` of the product set. -/
noncomputable def ptFamily (n q k : ℕ) (A : Finset R) (B : Finset (Fin k → R)) :
    Fin (k + 1) → Finset F :=
  Fin.snoc (fun _ ↦ A.image φ) (B.image (φ ∘ base n q k))

/-- Blueprint T01: the product set `P = φ(A) ^ k × φ(b(B)) ⊆ F ^ (k + 1)`. -/
noncomputable def ptSet (n q k : ℕ) (A : Finset R) (B : Finset (Fin k → R)) :
    Finset (Fin (k + 1) → F) :=
  Fintype.piFinset (ptFamily φ n q k A B)

/-- Blueprint T01: the first `k` factors of `ptFamily`. -/
@[simp] theorem ptFamily_castSucc (A : Finset R) (B : Finset (Fin k → R)) (i : Fin k) :
    ptFamily φ n q k A B (Fin.castSucc i) = A.image φ := by
  simp [ptFamily]

/-- Blueprint T01: the last factor of `ptFamily`. -/
@[simp] theorem ptFamily_last (A : Finset R) (B : Finset (Fin k → R)) :
    ptFamily φ n q k A B (Fin.last k) = B.image (φ ∘ base n q k) := by
  simp [ptFamily]

/-- Blueprint T01: membership in the product set. -/
theorem mem_ptSet {A : Finset R} {B : Finset (Fin k → R)} {u : Fin (k + 1) → F} :
    u ∈ ptSet φ n q k A B ↔
      (∀ i : Fin k, u (Fin.castSucc i) ∈ A.image φ) ∧
        u (Fin.last k) ∈ B.image (φ ∘ base n q k) := by
  rw [ptSet, Fintype.mem_piFinset, Fin.forall_fin_succ']
  simp only [ptFamily_castSucc, ptFamily_last]

/-- Blueprint T01: `p(a, w) ∈ P` for `a ∈ A ^ k` and `w ∈ B`. -/
theorem pt_mem_ptSet {A : Finset R} {B : Finset (Fin k → R)} {a w : Fin k → R}
    (ha : a ∈ Fintype.piFinset fun _ ↦ A) (hw : w ∈ B) : pt φ n q k a w ∈ ptSet φ n q k A B := by
  rw [Fintype.mem_piFinset] at ha
  rw [mem_ptSet]
  refine ⟨fun i ↦ ?_, ?_⟩
  · rw [pt_castSucc]
    exact Finset.mem_image_of_mem φ (ha i)
  · rw [pt_last]
    exact Finset.mem_image_of_mem (φ ∘ base n q k) hw

/-- Blueprint T01: every point of `P` is of the form `p(a, w)` with `a ∈ A ^ k` and `w ∈ B`. -/
theorem exists_pt_eq {A : Finset R} {B : Finset (Fin k → R)} {u : Fin (k + 1) → F}
    (hu : u ∈ ptSet φ n q k A B) :
    ∃ a w : Fin k → R, a ∈ (Fintype.piFinset fun _ ↦ A) ∧ w ∈ B ∧ pt φ n q k a w = u := by
  rw [mem_ptSet] at hu
  obtain ⟨h1, h2⟩ := hu
  have h1' : ∀ i : Fin k, ∃ x ∈ A, φ x = u (Fin.castSucc i) := fun i ↦
    Finset.mem_image.mp (h1 i)
  choose a ha hφa using h1'
  obtain ⟨w, hw, hφw⟩ := Finset.mem_image.mp h2
  refine ⟨a, w, Fintype.mem_piFinset.mpr ha, hw, ?_⟩
  funext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · rw [pt_last, ← hφw]
    rfl
  · rw [pt_castSucc, hφa]

end Defs

/-! ### Blueprint T01a: the small-kernel property on boxes of radius `< M` -/

section SmallKernel

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q : ℕ}

/-- Blueprint Q01 (bridge): `1 ≤ M` for `1 ≤ n` and `1 ≤ q`. -/
theorem one_le_M (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) : 1 ≤ Params.M n q :=
  Params.le_M_of_pow_le hn1 (by simpa using hq1)

/-- Blueprint T01a: if `x ∈ box T` with `T < M` and `φ x = 0` then `x = 0`, since
`∏ i, |σ i x| ≤ T ^ n < M ^ n ≤ q`. -/
theorem eq_zero_of_map_eq_zero_of_lt_M (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n)
    (hn1 : 1 ≤ n) (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) {T : ℝ} (hT : T < Params.M n q)
    {x : R} (hx : ∀ i, |σ i x| ≤ T) (h0 : φ x = 0) : x = 0 := by
  refine S.small_ker x h0 ?_
  have hι : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hx (Classical.arbitrary ι))
  have hMq : ((Params.M n q : ℝ)) ^ n ≤ (q : ℝ) := by
    exact_mod_cast Params.M_pow_le hn1 hq1
  calc ∏ i, |σ i x| ≤ ∏ _i : ι, T := Finset.prod_le_prod₀ (fun _ _ ↦ abs_nonneg _) fun i _ ↦ hx i
    _ = T ^ n := by rw [Finset.prod_const, Finset.card_univ, hn]
    _ < (Params.M n q : ℝ) ^ n := pow_lt_pow_left₀ hT hT0 (by omega)
    _ ≤ q := hMq
    _ = Fintype.card F := by rw [hqF]

/-- Blueprint T01a: `φ` is injective on any box of radius `T` with `2 T < M`. -/
theorem eq_of_map_eq_of_box (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n)
    (hn1 : 1 ≤ n) (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) {T : ℝ} (hT : 2 * T < Params.M n q)
    {x y : R} (hx : ∀ i, |σ i x| ≤ T) (hy : ∀ i, |σ i y| ≤ T) (hxy : φ x = φ y) : x = y := by
  have hsub : ∀ i, |σ i (x - y)| ≤ T + T := box_sub hx hy
  have h0 : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  have := S.eq_zero_of_map_eq_zero_of_lt_M hn hn1 hqF hq1 (by linarith : T + T < Params.M n q)
    hsub h0
  exact sub_eq_zero.mp this

/-- Blueprint T01a: `φ` is injective on any `Finset` contained in a box of radius `T` with
`2 T < M`. -/
theorem injOn_of_box (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n)
    (hn1 : 1 ≤ n) (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) {T : ℝ} (hT : 2 * T < Params.M n q)
    {A : Finset R} (hA : A ⊆ S.boxFinset T) : Set.InjOn φ ↑A := fun _x hx _y hy hxy ↦
  S.eq_of_map_eq_of_box hn hn1 hqF hq1 hT (S.mem_boxFinset.mp (hA hx))
    (S.mem_boxFinset.mp (hA hy)) hxy

end SmallKernel

/-! ### Blueprint T01: the constants `ρ = 1 / (100 (k + 1) √n)` and `γ = 1 / 10` -/

section Constants

variable {n k : ℕ} {ρ : ℝ}

/-- Blueprint T01: `1 ≤ √n` for `1 ≤ n`. -/
theorem one_le_sqrt_n (hn1 : 1 ≤ n) : 1 ≤ Real.sqrt n :=
  Real.one_le_sqrt.mpr (by exact_mod_cast hn1)

/-- Blueprint T01: the constant `ρ = 1 / (100 (k + 1) √n)` is positive. -/
theorem rho_pos (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) : 0 < ρ := by
  have := one_le_sqrt_n hn1
  rw [hρ]
  positivity

/-- Blueprint T01: `ρ (k + 1) √n = 1 / 100`. -/
theorem rho_mul_eq (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) :
    ρ * (k + 1) * Real.sqrt n = 1 / 100 := by
  have hs : 0 < Real.sqrt n := zero_lt_one.trans_le (one_le_sqrt_n hn1)
  rw [hρ]
  field_simp

/-- Blueprint T01: `ρ (k + 1) ≤ 1 / 100`. -/
theorem rho_mul_le (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) :
    ρ * (k + 1) ≤ 1 / 100 := by
  have hs := one_le_sqrt_n hn1
  have h := rho_mul_eq hn1 hρ
  have h0 : 0 ≤ ρ * (k + 1) := by
    have := rho_pos hn1 hρ
    positivity
  nlinarith

/-- Blueprint T01: `ρ √n ≤ 1 / 100`. -/
theorem rho_mul_sqrt_le (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) :
    ρ * Real.sqrt n ≤ 1 / 100 := by
  have hs := one_le_sqrt_n hn1
  have h := rho_mul_eq hn1 hρ
  have h0 : 0 ≤ ρ * Real.sqrt n := by
    have := rho_pos hn1 hρ
    positivity
  have hk : (1 : ℝ) ≤ k + 1 := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  nlinarith

/-- Blueprint T01: `ρ ≤ 1 / 100`. -/
theorem rho_le (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) : ρ ≤ 1 / 100 := by
  have h := rho_mul_le hn1 hρ
  have h0 := (rho_pos hn1 hρ).le
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  nlinarith

/-- Blueprint T01 / C02 hypothesis: `2 ρ √n < 1`. -/
theorem two_rho_sqrt_lt_one (hn1 : 1 ≤ n) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) :
    2 * ρ * Real.sqrt n < 1 := by
  have := rho_mul_sqrt_le hn1 hρ
  linarith

end Constants

/-! ### Blueprint T01a: injectivity of `φ` on `A` and on `b(B)`, injectivity of `p` -/

section Injectivity

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ} {ρ γ : ℝ}

/-- Blueprint T01a: `φ` is injective on the trace fiber `A ⊆ box (γ M)` (`γ = 1/10`). -/
theorem injOn_A (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hγ : γ = 1 / 10) {A : Finset R}
    (hA : A ⊆ S.boxFinset (γ * Params.M n q)) : Set.InjOn φ ↑A := by
  refine S.injOn_of_box hn hn1 hqF hq1 ?_ hA
  have hM : (1 : ℝ) ≤ Params.M n q := by exact_mod_cast one_le_M hn1 hq1
  rw [hγ]
  linarith

/-- Blueprint T01a: `φ` is injective on the base points `b(w)`, `w ∈ B ⊆ digitSpace`. -/
theorem eq_of_map_base_eq (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    {w w' : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (hw' : w' ∈ digitSpace S n q k ρ)
    (h : φ (base n q k w) = φ (base n q k w')) : w = w' := by
  have hρ0 : 0 ≤ ρ := (rho_pos hn1 hρ).le
  have hbase : base n q k w = base n q k w' := by
    refine S.eq_of_map_eq_of_box hn hn1 hqF hq1 (T := ρ * (k + 1) * Params.M n q) ?_
      (abs_base_le_M' S hn1 hq1 hρ0 hw) (abs_base_le_M' S hn1 hq1 hρ0 hw') h
    have hM : (1 : ℝ) ≤ Params.M n q := by exact_mod_cast one_le_M hn1 hq1
    have := rho_mul_le hn1 hρ
    nlinarith
  exact base_injOn S (hn ▸ two_rho_sqrt_lt_one hn1 hρ) hq1 hw hw' hbase

/-- Blueprint T01a: `φ ∘ b` is injective on `B ⊆ digitSpace`. -/
theorem injOn_base_B (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ) :
    Set.InjOn (φ ∘ base n q k) ↑B := fun _w hw _w' hw' h ↦
  S.eq_of_map_base_eq hn hn1 hqF hq1 hρ (hB hw) (hB hw') h

/-- Blueprint T01a: the point map `(a, w) ↦ p(a, w)` is injective on `A ^ k × B`. -/
theorem pt_injOn (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    (hγ : γ = 1 / 10) {A : Finset R} (hA : A ⊆ S.boxFinset (γ * Params.M n q))
    {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ) :
    Set.InjOn (fun p : (Fin k → R) × (Fin k → R) ↦ pt φ n q k p.1 p.2)
      ((Fintype.piFinset fun _ : Fin k ↦ A : Finset (Fin k → R)) ×ˢ (B : Set (Fin k → R))) := by
  rintro ⟨a, w⟩ ⟨ha, hw⟩ ⟨a', w'⟩ ⟨ha', hw'⟩ h
  simp only [Finset.mem_coe, Fintype.mem_piFinset] at ha hw ha' hw'
  simp only at h
  refine Prod.ext ?_ ?_
  · funext i
    have hi := congrFun h (Fin.castSucc i)
    rw [pt_castSucc, pt_castSucc] at hi
    exact S.injOn_A hn hn1 hqF hq1 hγ hA (ha i) (ha' i) hi
  · have hl := congrFun h (Fin.last k)
    rw [pt_last, pt_last] at hl
    exact S.eq_of_map_base_eq hn hn1 hqF hq1 hρ (hB hw) (hB hw') hl

end Injectivity

/-! ### Blueprint T01b: lifting -/

section Lifting

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ} {ρ γ : ℝ}

/-- Blueprint T01b: if `φ δ = 0` and `δ ∈ box (2 γ M + 2 ρ² (k + 1) M)` then `δ = 0`, because
`2 γ + 2 ρ² (k + 1) < 1`. -/
theorem eq_zero_of_map_eq_zero_of_small (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n)
    (hn1 : 1 ≤ n) (hqF : Fintype.card F = q) (hq1 : 1 ≤ q)
    (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) (hγ : γ = 1 / 10) {δ : R}
    (hδ : ∀ i, |σ i δ| ≤ 2 * γ * Params.M n q + 2 * ρ ^ 2 * (k + 1) * Params.M n q)
    (h0 : φ δ = 0) : δ = 0 := by
  refine S.eq_zero_of_map_eq_zero_of_lt_M hn hn1 hqF hq1 ?_ hδ h0
  have hM : (1 : ℝ) ≤ Params.M n q := by exact_mod_cast one_le_M hn1 hq1
  have h1 := rho_mul_le hn1 hρ
  have h2 := rho_le hn1 hρ
  have h0 := (rho_pos hn1 hρ).le
  have h3 : ρ ^ 2 * (k + 1) ≤ 1 / 10000 := by nlinarith
  rw [hγ]
  nlinarith

end Lifting

/-! ### Blueprint T01c: prefix sums below an index -/

section PrefixBelow

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint T01c: the prefix sum strictly below `i`, `y_{i-1}(w) = ∑_{j < i} Dⱼ wⱼ`
(`0` for `i = 0`). -/
noncomputable def prefixSumBelow (n q k : ℕ) (w : Fin k → R) (i : Fin k) : R :=
  ∑ j ∈ Finset.Iio i, (D (radix n q k) j : R) * w j

variable {n q k : ℕ} {ρ : ℝ}

/-- Blueprint T01c: `yᵢ(w) = y_{i-1}(w) + Dᵢ wᵢ`. -/
theorem prefixSum_eq_prefixSumBelow_add (w : Fin k → R) (i : Fin k) :
    prefixSum n q k w i = prefixSumBelow n q k w i + (D (radix n q k) i : R) * w i := by
  unfold prefixSum prefixSumBelow
  rw [← Finset.Iio_insert, Finset.sum_insert Finset.notMem_Iio_self, add_comm]

/-- Blueprint T01c: the prefix sum below `i` is bounded by `ρ i D_{i+1}` on the digit space. -/
theorem abs_prefixSumBelow_le (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    {w : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (i : Fin k) (ε : ι) :
    |σ ε (prefixSumBelow n q k w i)| ≤ ρ * i.val * Params.D n q (i.val + 1) := by
  unfold prefixSumBelow
  rw [map_sum]
  calc |∑ j ∈ Finset.Iio i, σ ε ((D (radix n q k) j : R) * w j)|
      ≤ ∑ j ∈ Finset.Iio i, |σ ε ((D (radix n q k) j : R) * w j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.Iio i).card • (ρ * Params.D n q (i.val + 1)) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj ↦ ?_
        refine (abs_term_le S hw j ε).trans ?_
        have hji : j < i := Finset.mem_Iio.mp hj
        have hji' : j.val < i.val := hji
        have hD := Params.D_mono (n := n) (q := q) hq (j := j.val + 2) (i := i.val + 1)
          (by omega) (by omega)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) hρ
    _ = ρ * i.val * Params.D n q (i.val + 1) := by
        rw [Fin.card_Iio, nsmul_eq_mul]
        ring

/-- Blueprint T01c: if `w` and `w'` agree above `i`, then `b(w') - b(w) = yᵢ(w') - yᵢ(w)`. -/
theorem base_sub_base_eq (w w' : Fin k → R) (i : Fin k) (h : ∀ j, i < j → w' j = w j) :
    base n q k w' - base n q k w = prefixSum n q k w' i - prefixSum n q k w i := by
  unfold base prefixSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  symm
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj ↦ ?_
  rw [Finset.mem_Iic, not_le] at hj
  rw [h j hj, sub_self]

end PrefixBelow

/-! ### Blueprint T01c: the collision argument -/

section Collision

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ} {ρ γ : ℝ}

/-- Blueprint T01c: `t = yᵢ(w') - yᵢ(w)` lies in `box (2 ρ (i + 1) D_{i+2})`. -/
theorem abs_sub_prefixSum_le (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    {w w' : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (hw' : w' ∈ digitSpace S n q k ρ)
    (i : Fin k) (ε : ι) :
    |σ ε (prefixSum n q k w' i - prefixSum n q k w i)| ≤
      2 * ρ * (i.val + 1) * Params.D n q (i.val + 2) := by
  have := box_sub (fun ε ↦ abs_prefixSum_le S hq hρ hw' i ε)
    (fun ε ↦ abs_prefixSum_le S hq hρ hw i ε) ε
  linarith

/-- Blueprint T01c: `wᵢ t` lies in `box (2 ρ² (k + 1) M)`, using `D_{i+1} Q_{i+1} ^ 2 ≤ M`. -/
theorem abs_mul_sub_prefixSum_le (S : Scaffold b σ φ K₀ K₁) (hn1 : 1 ≤ n) (hq1 : 1 ≤ q)
    (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) {w w' : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) (hw' : w' ∈ digitSpace S n q k ρ) (i : Fin k) (ε : ι) :
    |σ ε (w i * (prefixSum n q k w' i - prefixSum n q k w i))| ≤
      2 * ρ ^ 2 * (k + 1) * Params.M n q := by
  have hρ0 : 0 ≤ ρ := (rho_pos hn1 hρ).le
  have h1 : ∀ ε, |σ ε (w i)| ≤ ρ * Params.Q n q (i.val + 1) := fun ε ↦
    (mem_digitSpace S).mp hw i ε
  have h2 : ∀ ε, |σ ε (prefixSum n q k w' i - prefixSum n q k w i)| ≤
      2 * ρ * (i.val + 1) * Params.D n q (i.val + 2) := fun ε ↦
    abs_sub_prefixSum_le S hq1 hρ0 hw hw' i ε
  refine (box_mul_le h1 h2 ε).trans ?_
  have hDQ : (Params.D n q (i.val + 2) : ℝ) * Params.Q n q (i.val + 1) ≤ Params.M n q := by
    have h : Params.D n q (i.val + 2) * Params.Q n q (i.val + 1) ≤ Params.M n q := by
      have := Params.D_mul_Q_sq_le_M hn1 hq1 (i := i.val + 1) (by omega)
      rw [← D_radix_mul_radix (n := n) (q := q) (k := k) i, D_radix, radix_apply]
      calc Params.D n q (i.val + 1) * Params.Q n q (i.val + 1) * Params.Q n q (i.val + 1)
          = Params.D n q (i.val + 1) * Params.Q n q (i.val + 1) ^ 2 := by ring
        _ ≤ Params.M n q := this
    exact_mod_cast h
  have hi : (i.val : ℝ) + 1 ≤ k + 1 := by
    have := i.isLt
    exact_mod_cast (by omega : i.val + 1 ≤ k + 1)
  calc ρ * Params.Q n q (i.val + 1) * (2 * ρ * (i.val + 1) * Params.D n q (i.val + 2))
      = 2 * ρ ^ 2 * (i.val + 1) * (Params.D n q (i.val + 2) * Params.Q n q (i.val + 1)) := by
        ring
    _ ≤ 2 * ρ ^ 2 * (k + 1) * Params.M n q :=
        mul_le_mul (mul_le_mul_of_nonneg_left hi (by positivity)) hDQ (by positivity)
          (by positivity)

/-- Blueprint T01c (decoding step): if `w, w' ∈ digitSpace` have the same color and
`trace (wᵢ (yᵢ(w') - yᵢ(w))) = 0`, then `wᵢ = w'ᵢ`. This is D02 with `Q = Dᵢ`, `u = y_{i-1}(w)`,
`u' = y_{i-1}(w')`. -/
theorem digit_eq_of_trace_eq_zero (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n)
    (hn1 : 1 ≤ n) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    {w w' : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (hw' : w' ∈ digitSpace S n q k ρ)
    (hc : color σ n q k w = color σ n q k w') (i : Fin k)
    (ht : trace σ (w i * (prefixSum n q k w' i - prefixSum n q k w i)) = 0) : w i = w' i := by
  have hρ0 : 0 ≤ ρ := (rho_pos hn1 hρ).le
  set Di : ℕ := D (radix n q k) i with hDi
  have hDpos : 0 < Di := D_pos _ (radix_pos hq1) i
  have hDi' : (Di : ℝ) = Params.D n q (i.val + 1) := by rw [hDi, D_radix]
  have hx := trace_prefixSum_eq_of_color_eq n q k S hc i
  rw [prefixSum_eq_prefixSumBelow_add w, prefixSum_eq_prefixSumBelow_add w'] at hx ht
  refine S.decoding_eq (Q := (Di : ℤ)) (by exact_mod_cast hDpos) (u := prefixSumBelow n q k w i)
    (u' := prefixSumBelow n q k w' i) ?_ ?_ ?_
  · push_cast
    exact hx
  · push_cast
    exact ht
  · push_cast
    have hu := norm_emb_le fun ε ↦ abs_prefixSumBelow_le S hq1 hρ0 hw i ε
    have hu' := norm_emb_le fun ε ↦ abs_prefixSumBelow_le S hq1 hρ0 hw' i ε
    rw [hn] at hu hu'
    rw [hDi']
    have hD1 : (1 : ℝ) ≤ Params.D n q (i.val + 1) := by exact_mod_cast Params.D_pos hq1 _
    have hi : (i.val : ℝ) ≤ k + 1 := by
      have := i.isLt
      exact_mod_cast (by omega : i.val ≤ k + 1)
    have hrs := rho_mul_eq hn1 hρ
    have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hb : Real.sqrt n * (ρ * i.val * Params.D n q (i.val + 1)) ≤
        (Params.D n q (i.val + 1) : ℝ) / 100 := by
      calc Real.sqrt n * (ρ * i.val * Params.D n q (i.val + 1))
          = ρ * i.val * Real.sqrt n * Params.D n q (i.val + 1) := by ring
        _ ≤ ρ * (k + 1) * Real.sqrt n * Params.D n q (i.val + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi hρ0) hs)
              (Nat.cast_nonneg _)
        _ = (Params.D n q (i.val + 1) : ℝ) / 100 := by rw [hrs]; ring
    linarith

/-- Blueprint T01c (collision): if `p(a', w') = p(a, w) + μ v(w)` with `a, a' ∈ A ^ k` and
`w, w' ∈ B`, then `(a', w') = (a, w)`. -/
theorem no_collision (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    (hγ : γ = 1 / 10) {s : ℤ} {A : Finset R} (hA : A ⊆ S.boxFinset (γ * Params.M n q))
    (hAs : ∀ a ∈ A, trace σ a = s) {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ)
    (hBc : ∀ w ∈ B, ∀ w' ∈ B, color σ n q k w = color σ n q k w')
    {a a' w w' : Fin k → R} (ha : a ∈ Fintype.piFinset fun _ ↦ A) (hw : w ∈ B)
    (ha' : a' ∈ Fintype.piFinset fun _ ↦ A) (hw' : w' ∈ B) (μ : F)
    (hcol : pt φ n q k a' w' = pt φ n q k a w + μ • dir φ w) : a' = a ∧ w' = w := by
  rw [Fintype.mem_piFinset] at ha ha'
  -- the last coordinate determines `μ`
  have hlast := congrFun hcol (Fin.last k)
  simp only [Pi.add_apply, Pi.smul_apply, pt_last, dir_last, smul_eq_mul, mul_one] at hlast
  have hμ : μ = φ (base n q k w') - φ (base n q k w) := by rw [hlast]; ring
  -- the first `k` coordinates
  have hcoord : ∀ i : Fin k, φ (a' i) = φ (a i) + μ * φ (w i) := fun i ↦ by
    have := congrFun hcol (Fin.castSucc i)
    simpa only [Pi.add_apply, Pi.smul_apply, pt_castSucc, dir_castSucc, smul_eq_mul] using this
  by_cases hww : w' = w
  · subst hww
    have hμ0 : μ = 0 := by rw [hμ, sub_self]
    refine ⟨funext fun i ↦ ?_, rfl⟩
    have := hcoord i
    rw [hμ0, zero_mul, add_zero] at this
    exact S.injOn_A hn hn1 hqF hq1 hγ hA (ha' i) (ha i) this
  · exfalso
    classical
    -- the largest index where `w'` and `w` differ
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hww
    set Dset : Finset (Fin k) := Finset.univ.filter fun i ↦ w' i ≠ w i with hDset
    have hne : Dset.Nonempty := ⟨i₀, by simp [hDset, hi₀]⟩
    set i : Fin k := Dset.max' hne with hi
    have hi_mem : w' i ≠ w i := by
      have := Finset.max'_mem Dset hne
      simpa [hDset] using this
    have hgt : ∀ j, i < j → w' j = w j := fun j hj ↦ by
      by_contra hj'
      have hjD : j ∈ Dset := by simp [hDset, hj']
      exact absurd (Finset.le_max' Dset j hjD) (not_le.mpr hj)
    -- `t = b(w') - b(w) = yᵢ(w') - yᵢ(w)` and `μ = φ t`
    set t : R := prefixSum n q k w' i - prefixSum n q k w i with ht
    have hbt : base n q k w' - base n q k w = t := base_sub_base_eq w w' i hgt
    have hμt : μ = φ t := by rw [hμ, ← map_sub, hbt]
    -- `δ = a'ᵢ - aᵢ - wᵢ t` lies in the kernel of `φ` and in a small box
    have hδ0 : φ (a' i - a i - w i * t) = 0 := by
      rw [map_sub, map_sub, map_mul, hcoord i, hμt]
      ring
    have hδ : ∀ ε, |σ ε (a' i - a i - w i * t)| ≤
        2 * γ * Params.M n q + 2 * ρ ^ 2 * (k + 1) * Params.M n q := fun ε ↦ by
      have h1 : ∀ ε, |σ ε (a' i - a i)| ≤ γ * Params.M n q + γ * Params.M n q :=
        box_sub (S.mem_boxFinset.mp (hA (ha' i))) (S.mem_boxFinset.mp (hA (ha i)))
      have h2 : ∀ ε, |σ ε (w i * t)| ≤ 2 * ρ ^ 2 * (k + 1) * Params.M n q := fun ε ↦
        abs_mul_sub_prefixSum_le S hn1 hq1 hρ (hB hw) (hB hw') i ε
      have := box_sub h1 h2 ε
      linarith
    have heq : a' i - a i = w i * t :=
      sub_eq_zero.mp (S.eq_zero_of_map_eq_zero_of_small hn hn1 hqF hq1 hρ hγ hδ hδ0)
    -- the traces of `a'ᵢ` and `aᵢ` agree, so `trace (wᵢ t) = 0`
    have htr : trace σ (w i * t) = 0 := by
      rw [← heq, trace_sub, hAs _ (ha' i), hAs _ (ha i), sub_self]
    -- decoding gives `wᵢ = w'ᵢ`, a contradiction
    exact hi_mem
      (S.digit_eq_of_trace_eq_zero hn hn1 hq1 hρ (hB hw) (hB hw') (hBc w hw w' hw') i htr).symm

end Collision

/-! ### Blueprint T01: main statements -/

section Main

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ} {ρ γ : ℝ} [DecidableEq F]

/-- Blueprint T01 (main statement): the product set `P = ptSet φ n q k A B` satisfies the
hypothesis of P01: through every `u ∈ P` there is a direction `v ≠ 0` whose punctured line
`u + t v` (`t ≠ 0`) misses `P`. Here `A ⊆ box (γ M)` is a trace fiber and `B ⊆ digitSpace` is a
color class, with `ρ = 1 / (100 (k + 1) √n)` and `γ = 1 / 10`. -/
theorem tangent_hypothesis (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    (hγ : γ = 1 / 10) {s : ℤ} {A : Finset R} (hA : A ⊆ S.boxFinset (γ * Params.M n q))
    (hAs : ∀ a ∈ A, trace σ a = s) {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ)
    (hBc : ∀ w ∈ B, ∀ w' ∈ B, color σ n q k w = color σ n q k w') :
    ∀ u ∈ ptSet φ n q k A B, ∃ v : Fin (k + 1) → F, v ≠ 0 ∧
      ∀ t : F, t ≠ 0 → u + t • v ∉ ptSet φ n q k A B := by
  intro u hu
  obtain ⟨a, w, ha, hw, rfl⟩ := exists_pt_eq φ hu
  refine ⟨dir φ w, dir_ne_zero φ w, fun t ht hmem ↦ ?_⟩
  obtain ⟨a', w', ha', hw', heq⟩ := exists_pt_eq φ hmem
  obtain ⟨rfl, rfl⟩ := S.no_collision hn hn1 hqF hq1 hρ hγ hA hAs hB hBc ha hw ha' hw' t heq
  have := congrFun heq (Fin.last k)
  simp only [Pi.add_apply, Pi.smul_apply, pt_last, dir_last, smul_eq_mul, mul_one] at this
  exact ht (by linear_combination -this)

/-- Blueprint T01: `#P = #A ^ k * #B`. -/
theorem card_ptSet (S : Scaffold b σ φ K₀ K₁) (hn : Fintype.card ι = n) (hn1 : 1 ≤ n)
    (hqF : Fintype.card F = q) (hq1 : 1 ≤ q) (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n))
    (hγ : γ = 1 / 10) {A : Finset R} (hA : A ⊆ S.boxFinset (γ * Params.M n q))
    {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ) :
    (ptSet φ n q k A B).card = A.card ^ k * B.card := by
  rw [ptSet, Fintype.card_piFinset, Fin.prod_univ_castSucc]
  simp only [ptFamily_castSucc, ptFamily_last, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]
  rw [Finset.card_image_of_injOn (S.injOn_A hn hn1 hqF hq1 hγ hA),
    Finset.card_image_of_injOn (S.injOn_base_B hn hn1 hqF hq1 hρ hB)]

/-- Blueprint T01 + P01: the complement `univ \ P` of the product set is a Nikodym set in
`F ^ (k + 1)` (for `k ≥ 1`, i.e. `h = k + 1 ≥ 2`). -/
theorem isNikodym_univ_sdiff_ptSet (S : Scaffold b σ φ K₀ K₁) (hk : 1 ≤ k)
    (hn : Fintype.card ι = n) (hn1 : 1 ≤ n) (hqF : Fintype.card F = q) (hq1 : 1 ≤ q)
    (hρ : ρ = 1 / (100 * (k + 1) * Real.sqrt n)) (hγ : γ = 1 / 10) {s : ℤ} {A : Finset R}
    (hA : A ⊆ S.boxFinset (γ * Params.M n q)) (hAs : ∀ a ∈ A, trace σ a = s)
    {B : Finset (Fin k → R)} (hB : B ⊆ digitSpace S n q k ρ)
    (hBc : ∀ w ∈ B, ∀ w' ∈ B, color σ n q k w = color σ n q k w') :
    IsNikodym (Finset.univ \ ptSet φ n q k A B) := by
  -- P01 is stated with the classical decidability instance; `convert` reconciles the instances
  have := isNikodym_univ_sdiff_piFinset (by omega) (ptFamily φ n q k A B)
    (S.tangent_hypothesis hn hn1 hqF hq1 hρ hγ hA hAs hB hBc)
  unfold ptSet
  convert this using 3

end Main

end Scaffold

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
