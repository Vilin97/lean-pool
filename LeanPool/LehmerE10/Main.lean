/-
Copyright (c) 2026 Dillon Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dillon Ryan
-/

import LeanPool.LehmerE10.Defs
import LeanPool.LehmerE10.UnitCircleFactors
import LeanPool.LehmerE10.TraceQuintic

/-!
# the assembly:
    `Irreducible lehmerPolynomial`   and   `coxeterE10.charpoly = lehmerPolynomial`.
Route:
  (1) TRACE CENSUS: the trace quintic q (with L(x) = x⁵·q(x + 1/x), TraceQuintic)
      has EXACTLY the five IVT-located real roots y₁<y₂<y₃<y₄ ∈ (−2,2), y₅ ∈ (2,21/10):
      five distinct roots of a degree-5 polynomial exhaust its complex roots, and
      q = ∏(X − yᵢ) — so q'(y₅) = ∏_{i<5}(y₅ − yᵢ) ≠ 0: the Salem trace root is simple.
  (2) ROOT CLASSIFICATION: every complex root z of L has trace z + 1/z ∈ {y₁..y₅};
      the four ball traces force ‖z‖ = 1 (norm_eq_one_of_trace_in_ball), the Salem
      trace forces z ∈ {μ, ν} with μν = 1, ν < 1 < μ (the off-circle Salem pair).
  (3) SALEM PAIR SIMPLE: a double root of L at t ∈ {μ,ν} would kill L' there; the
      derivative–trace identity  z²·L'(z) = 5z⁶·q(y) + (z⁷ − z⁵)·q'(y)  then forces
      q'(y₅) = 0 (since t ∉ {0, ±1}) — refuted by (1).  count μ = count ν = 1 in L.
  (4) THE FACTOR ARGUMENT: L = F·G proper monic ⟹ F(0)·G(0) = L(0) = 1 ⟹ ‖F(0)‖ = 1;
      but ‖F(0)‖ = ∏‖roots F‖ = μ^a·ν^b with (a,b) ∈ {0,1}² by (3).  (1,0) gives μ = 1,
      (0,1) gives ν = 1 — both refuted; (0,0) makes F all-on-circle, (1,1) makes G
      all-on-circle — both killed by `no_unit_circle_factor` (Kronecker + the
      uniform-1291 cyclotomic kill).  No proper factor exists.
  (5) ASSEMBLY: `lehmer_irreducible` (ℤ, then ℚ by Gauss); the Coxeter element of
      E₁₀ is annihilated by L (kernel computation), so by
      `charpoly_eq_lehmer_of_irreducible` its characteristic polynomial is L —
      first over ℚ, then over ℤ by injectivity of the coefficient map.
SCOPE: Lehmer's 1933 conjecture (a positive lower bound for Mahler measures > 1)
is NOT claimed anywhere in this repository.
Axiom footprint: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace LehmerE10

open Polynomial

/-! ### The five trace roots, pinned from the RHLehmerTrace IVT witnesses. -/

noncomputable def y1 : ℝ := traceQ_root_1.choose
noncomputable def y2 : ℝ := traceQ_root_2.choose
noncomputable def y3 : ℝ := traceQ_root_3.choose
noncomputable def y4 : ℝ := traceQ_root_4.choose
noncomputable def y5 : ℝ := traceQ_root_salem.choose

lemma y1_mem : y1 ∈ Set.Ioo (-2 : ℝ) (-3/2) := traceQ_root_1.choose_spec.1
lemma y2_mem : y2 ∈ Set.Ioo (-3/2 : ℝ) (-1) := traceQ_root_2.choose_spec.1
lemma y3_mem : y3 ∈ Set.Ioo (-1 : ℝ) 0 := traceQ_root_3.choose_spec.1
lemma y4_mem : y4 ∈ Set.Ioo (0 : ℝ) 1 := traceQ_root_4.choose_spec.1
lemma y5_mem : y5 ∈ Set.Ioo (2 : ℝ) (21/10) := traceQ_root_salem.choose_spec.1

lemma y1_root : traceQ y1 = 0 := traceQ_root_1.choose_spec.2
lemma y2_root : traceQ y2 = 0 := traceQ_root_2.choose_spec.2
lemma y3_root : traceQ y3 = 0 := traceQ_root_3.choose_spec.2
lemma y4_root : traceQ y4 = 0 := traceQ_root_4.choose_spec.2
lemma y5_root : traceQ y5 = 0 := traceQ_root_salem.choose_spec.2

lemma y_chain : y1 < y2 ∧ y2 < y3 ∧ y3 < y4 ∧ y4 < y5 := by
  have h1 := Set.mem_Ioo.mp y1_mem
  have h2 := Set.mem_Ioo.mp y2_mem
  have h3 := Set.mem_Ioo.mp y3_mem
  have h4 := Set.mem_Ioo.mp y4_mem
  have h5 := Set.mem_Ioo.mp y5_mem
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### The trace quintic as a polynomial over ℂ, and its root census. -/

noncomputable def tracePoly : Polynomial ℂ :=
  X ^ 5 + X ^ 4 - C 5 * X ^ 3 - C 5 * X ^ 2 + C 4 * X + C 3

lemma tracePoly_monic : tracePoly.Monic := by unfold tracePoly; monicity!

lemma tracePoly_natDegree : tracePoly.natDegree = 5 := by unfold tracePoly; compute_degree!

lemma tracePoly_eval (z : ℂ) : tracePoly.eval z = traceQC z := by
  unfold tracePoly LehmerE10.traceQC
  simp
  try ring

lemma trace_root_mem {y : ℝ} (hy : traceQ y = 0) : (y : ℂ) ∈ tracePoly.roots := by
  rw [mem_roots tracePoly_monic.ne_zero, IsRoot.def, tracePoly_eval, traceQC_ofReal, hy]
  simp

noncomputable def T5 : Multiset ℂ := {(y1 : ℂ), (y2 : ℂ), (y3 : ℂ), (y4 : ℂ), (y5 : ℂ)}

lemma T5_nodup : T5.Nodup := by
  obtain ⟨c1, c2, c3, c4⟩ := y_chain
  have hne : ∀ a b : ℝ, a < b → ¬((a : ℂ) = (b : ℂ)) := fun a b h => by
    exact_mod_cast h.ne
  have m1 : ((y1 : ℝ) : ℂ) ∉ ({(y2 : ℂ), (y3 : ℂ), (y4 : ℂ), (y5 : ℂ)} : Multiset ℂ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    exact ⟨hne y1 y2 c1, hne y1 y3 (by linarith), hne y1 y4 (by linarith),
      hne y1 y5 (by linarith)⟩
  have m2 : ((y2 : ℝ) : ℂ) ∉ ({(y3 : ℂ), (y4 : ℂ), (y5 : ℂ)} : Multiset ℂ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    exact ⟨hne y2 y3 c2, hne y2 y4 (by linarith), hne y2 y5 (by linarith)⟩
  have m3 : ((y3 : ℝ) : ℂ) ∉ ({(y4 : ℂ), (y5 : ℂ)} : Multiset ℂ) := by
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton, not_or]
    exact ⟨hne y3 y4 c3, hne y3 y5 (by linarith)⟩
  have m4 : ((y4 : ℝ) : ℂ) ∉ ({(y5 : ℂ)} : Multiset ℂ) := by
    simp only [Multiset.mem_singleton]
    exact hne y4 y5 c4
  simp only [T5, Multiset.insert_eq_cons, Multiset.nodup_cons]
  exact ⟨m1, m2, m3, m4, Multiset.nodup_singleton _⟩

lemma trace_roots_eq : tracePoly.roots = T5 := by
  have hcard : tracePoly.roots.card = 5 := by
    rw [splits_iff_card_roots.mp (IsAlgClosed.splits tracePoly), tracePoly_natDegree]
  have hT5card : T5.card = 5 := by simp [T5]
  have hle : T5 ≤ tracePoly.roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ T5
    · rw [Multiset.count_eq_one_of_mem T5_nodup ha]
      have hmem : a ∈ tracePoly.roots := by
        rcases (by simpa [T5] using ha :
            a = (y1 : ℂ) ∨ a = (y2 : ℂ) ∨ a = (y3 : ℂ) ∨ a = (y4 : ℂ) ∨ a = (y5 : ℂ)) with
          rfl | rfl | rfl | rfl | rfl
        exacts [trace_root_mem y1_root, trace_root_mem y2_root, trace_root_mem y3_root,
          trace_root_mem y4_root, trace_root_mem y5_root]
      exact Multiset.count_pos.mpr hmem
    · rw [Multiset.count_eq_zero.mpr ha]; exact Nat.zero_le _
  exact (Multiset.eq_of_le_of_card_le hle (by rw [hcard, hT5card])).symm

/-- Trace exhaustion: every complex root of the trace quintic is one of the five. -/
lemma trace_root_cases {w : ℂ} (hw : traceQC w = 0) :
    w = (y1 : ℂ) ∨ w = (y2 : ℂ) ∨ w = (y3 : ℂ) ∨ w = (y4 : ℂ) ∨ w = (y5 : ℂ) := by
  have hmem : w ∈ tracePoly.roots := by
    rw [mem_roots tracePoly_monic.ne_zero, IsRoot.def, tracePoly_eval, hw]
  rw [trace_roots_eq] at hmem
  simpa [T5] using hmem

/-- The spectral factorization of the trace quintic: `q = ∏ (X − yᵢ)`. -/
lemma trace_factor :
    tracePoly = (X - C (y1 : ℂ)) * (X - C (y2 : ℂ)) * (X - C (y3 : ℂ)) *
      (X - C (y4 : ℂ)) * (X - C (y5 : ℂ)) := by
  have h := (IsAlgClosed.splits tracePoly).eq_prod_roots_of_monic tracePoly_monic
  rw [trace_roots_eq] at h
  rw [h]
  simp only [T5, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton]
  ring

/-! ### The derivative of the trace quintic; the Salem trace root is simple. -/

noncomputable def dtraceQC (y : ℂ) : ℂ := 5 * y ^ 4 + 4 * y ^ 3 - 15 * y ^ 2 - 10 * y + 4

lemma tracePoly_derivative_eval (w : ℂ) : (derivative tracePoly).eval w = dtraceQC w := by
  unfold tracePoly dtraceQC
  simp
  try ring

/-- **THE SALEM TRACE ROOT IS SIMPLE**: `q'(y₅) = ∏_{i<5}(y₅ − yᵢ) ≠ 0`. -/
lemma dtrace_y5_ne_zero : dtraceQC (y5 : ℂ) ≠ 0 := by
  have h1 := Set.mem_Ioo.mp y1_mem
  have h2 := Set.mem_Ioo.mp y2_mem
  have h3 := Set.mem_Ioo.mp y3_mem
  have h4 := Set.mem_Ioo.mp y4_mem
  have h5 := Set.mem_Ioo.mp y5_mem
  rw [← tracePoly_derivative_eval, trace_factor]
  simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, eval_add, eval_mul,
    eval_sub, eval_X, eval_C, sub_self, sub_zero, mul_zero, zero_mul, mul_one, one_mul,
    add_zero, zero_add]
  have hne : ∀ a : ℝ, a < y5 → (y5 : ℂ) - (a : ℂ) ≠ 0 := by
    intro a ha
    rw [sub_ne_zero]
    exact_mod_cast ha.ne'
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hne y1 (by linarith)) (hne y2 (by linarith)))
    (hne y3 (by linarith))) (hne y4 (by linarith))

/-! ### Lehmer over ℂ: evaluation bridge, derivative, and the derivative–trace identity. -/

noncomputable def LC : Polynomial ℂ := lehmerPolynomial.map (Int.castRingHom ℂ)

lemma LC_poly : LC = X ^ 10 + X ^ 9 - X ^ 7 - X ^ 6 - X ^ 5 - X ^ 4 - X ^ 3 + X + 1 := by
  unfold LC lehmerPolynomial
  simp [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_one,
    Polynomial.map_X]

lemma LC_eval (z : ℂ) : LC.eval z = lehmerC z := by
  rw [LC_poly]
  unfold LehmerE10.lehmerC
  simp

lemma LC_monic : LC.Monic := lehmerPolynomial_monic.map _
lemma LC_ne_zero : LC ≠ 0 := LC_monic.ne_zero

lemma LC_eval_zero : LC.eval 0 = 1 := by
  rw [LC_eval]
  unfold LehmerE10.lehmerC
  norm_num

lemma root_ne_zero {z : ℂ} (hz : z ∈ LC.roots) : z ≠ 0 := by
  rintro rfl
  have h := (mem_roots LC_ne_zero).mp hz
  rw [IsRoot.def, LC_eval_zero] at h
  exact one_ne_zero h

lemma LC_derivative_eval (z : ℂ) :
    (derivative LC).eval z =
      10 * z ^ 9 + 9 * z ^ 8 - 7 * z ^ 6 - 6 * z ^ 5 - 5 * z ^ 4 - 4 * z ^ 3 - 3 * z ^ 2 + 1 := by
  rw [LC_poly]
  simp [derivative_add, derivative_sub, derivative_X_pow, derivative_X, derivative_one]
  try push_cast
  try ring

/-- **THE DERIVATIVE–TRACE IDENTITY**: differentiating `L(z) = z⁵ q(z + 1/z)` and
    clearing denominators: `z²·L'(z) = 5z⁶·q(y) + (z⁷ − z⁵)·q'(y)` at `y = z + 1/z`. -/
lemma deriv_trace_identity {z : ℂ} (hz : z ≠ 0) :
    z ^ 2 * (derivative LC).eval z =
      5 * z ^ 6 * traceQC (z + 1 / z) + (z ^ 7 - z ^ 5) * dtraceQC (z + 1 / z) := by
  rw [LC_derivative_eval]
  unfold LehmerE10.traceQC dtraceQC
  field_simp
  ring

/-! ### The off-circle Salem pair `{μ, ν}`, `μν = 1`, `ν < 1 < μ`. -/

noncomputable def s5 : ℝ := Real.sqrt (y5 ^ 2 - 4)
noncomputable def mu : ℝ := (y5 + s5) / 2
noncomputable def nu : ℝ := (y5 - s5) / 2

lemma y5_gt_two : 2 < y5 := (Set.mem_Ioo.mp y5_mem).1

lemma s5_sq : s5 ^ 2 = y5 ^ 2 - 4 :=
  Real.sq_sqrt (by nlinarith [y5_gt_two])

lemma s5_pos : 0 < s5 := Real.sqrt_pos.mpr (by nlinarith [y5_gt_two])

lemma mu_nu_sum : mu + nu = y5 := by unfold mu nu; ring

lemma mu_nu_prod : mu * nu = 1 := by
  have h := s5_sq
  unfold mu nu
  linear_combination (-1/4 : ℝ) * h

lemma mu_gt_one : 1 < mu := by
  have hs := s5_pos; have hy := y5_gt_two
  unfold mu; linarith

lemma nu_pos : 0 < nu := by nlinarith [mu_nu_prod, mu_gt_one]

lemma nu_lt_one : nu < 1 := by nlinarith [mu_nu_prod, mu_gt_one, nu_pos]

lemma muC_prod : (mu : ℂ) * (nu : ℂ) = 1 := by exact_mod_cast mu_nu_prod
lemma muC_sum : (mu : ℂ) + (nu : ℂ) = (y5 : ℂ) := by exact_mod_cast mu_nu_sum

lemma muC_ne_zero : (mu : ℂ) ≠ 0 := by
  have h : mu ≠ 0 := by have := mu_gt_one; linarith
  exact_mod_cast h

lemma nuC_ne_zero : (nu : ℂ) ≠ 0 := by
  have h : nu ≠ 0 := nu_pos.ne'
  exact_mod_cast h

lemma muC_ne_nuC : (mu : ℂ) ≠ (nu : ℂ) := by
  exact_mod_cast ne_of_gt (lt_trans nu_lt_one mu_gt_one)

lemma mu_trace : (mu : ℂ) + 1 / (mu : ℂ) = (y5 : ℂ) := by
  have hinv : 1 / (mu : ℂ) = (nu : ℂ) := by
    rw [eq_comm, eq_div_iff muC_ne_zero]
    linear_combination muC_prod
  rw [hinv]; exact muC_sum

lemma nu_trace : (nu : ℂ) + 1 / (nu : ℂ) = (y5 : ℂ) := by
  have hinv : 1 / (nu : ℂ) = (mu : ℂ) := by
    rw [eq_comm, eq_div_iff nuC_ne_zero]
    linear_combination muC_prod
  rw [hinv]
  linear_combination muC_sum

lemma traceQC_y5 : traceQC (y5 : ℂ) = 0 := by
  rw [traceQC_ofReal, y5_root]; simp

/-! ### Root classification: on the circle, or in the Salem pair. -/

/-- **ROOT CLASSIFICATION (proven)**: every complex root of Lehmer is on the unit
    circle or equals `μ` or `ν` — the trace lands on one of the five census roots;
    ball traces pin the circle, the Salem trace pins the pair. -/
lemma root_classification {z : ℂ} (hz : z ∈ LC.roots) :
    ‖z‖ = 1 ∨ z = (mu : ℂ) ∨ z = (nu : ℂ) := by
  have hz0 : z ≠ 0 := root_ne_zero hz
  have hroot : lehmerC z = 0 := by
    have h := (mem_roots LC_ne_zero).mp hz
    rwa [IsRoot.def, LC_eval] at h
  have htr : traceQC (z + 1 / z) = 0 := by
    have h := lehmer_trace_reduction z hz0
    rw [hroot] at h
    rcases mul_eq_zero.mp h.symm with h5 | h5
    · exact absurd (by simpa using h5 : z = 0) hz0
    · exact h5
  have hb1 := Set.mem_Ioo.mp y1_mem
  have hb2 := Set.mem_Ioo.mp y2_mem
  have hb3 := Set.mem_Ioo.mp y3_mem
  have hb4 := Set.mem_Ioo.mp y4_mem
  rcases trace_root_cases htr with h | h | h | h | h
  · exact Or.inl (norm_eq_one_of_trace_in_ball hz0 h (by linarith) (by linarith))
  · exact Or.inl (norm_eq_one_of_trace_in_ball hz0 h (by linarith) (by linarith))
  · exact Or.inl (norm_eq_one_of_trace_in_ball hz0 h (by linarith) (by linarith))
  · exact Or.inl (norm_eq_one_of_trace_in_ball hz0 h (by linarith) (by linarith))
  · right
    have h1 : z * (1 / z) = 1 := by field_simp
    have hexp : (z - (mu : ℂ)) * (z - (nu : ℂ)) = z ^ 2 - (y5 : ℂ) * z + 1 := by
      linear_combination (-z) * muC_sum + muC_prod
    have hquad : (z - (mu : ℂ)) * (z - (nu : ℂ)) = 0 := by
      rw [hexp]
      linear_combination z * h - h1
    rcases mul_eq_zero.mp hquad with h' | h'
    · exact Or.inl (sub_eq_zero.mp h')
    · exact Or.inr (sub_eq_zero.mp h')

lemma muC_mem : (mu : ℂ) ∈ LC.roots := by
  rw [mem_roots LC_ne_zero, IsRoot.def, LC_eval, lehmer_trace_reduction _ muC_ne_zero,
    mu_trace, traceQC_y5, mul_zero]

lemma nuC_mem : (nu : ℂ) ∈ LC.roots := by
  rw [mem_roots LC_ne_zero, IsRoot.def, LC_eval, lehmer_trace_reduction _ nuC_ne_zero,
    nu_trace, traceQC_y5, mul_zero]

/-! ### The Salem pair is SIMPLE in L (multiplicity one). -/

/-- A real positive trace-`y₅` root of Lehmer other than `1` has multiplicity one:
    a double root kills `L'` there, and the derivative–trace identity then forces
    `q'(y₅)·t⁵(t² − 1) = 0` — refuted by the simple Salem trace root and `t ∉ {0, ±1}`. -/
lemma salem_count_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≠ 1)
    (htr : (t : ℂ) + 1 / (t : ℂ) = (y5 : ℂ)) : LC.roots.count (t : ℂ) ≤ 1 := by
  by_contra hcon
  push_neg at hcon
  have h2 : 2 ≤ rootMultiplicity ((t : ℝ) : ℂ) LC := by
    rw [← Polynomial.count_roots]; omega
  have hdvd : (X - C ((t : ℝ) : ℂ)) ^ 2 ∣ LC :=
    (pow_dvd_pow _ h2).trans (Polynomial.pow_rootMultiplicity_dvd LC _)
  obtain ⟨g, hg⟩ := hdvd
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hd0 : (derivative LC).eval (t : ℂ) = 0 := by
    rw [hg]
    simp [derivative_mul, derivative_pow, derivative_sub, derivative_X, derivative_C]
  have hid := deriv_trace_identity htC
  rw [hd0, htr, traceQC_y5, mul_zero, mul_zero, zero_add] at hid
  rcases mul_eq_zero.mp hid.symm with h7 | h7
  · have h7' : t ^ 7 - t ^ 5 = 0 := by exact_mod_cast h7
    have hfac : t ^ 5 * (t ^ 2 - 1) = 0 := by linear_combination h7'
    have ht5 : (0 : ℝ) < t ^ 5 := pow_pos ht0 5
    have hsq : t ^ 2 = 1 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h ht5.ne'
      · linarith
    rcases lt_or_gt_of_ne ht1 with hlt | hgt
    · nlinarith
    · nlinarith
  · exact dtrace_y5_ne_zero h7

lemma count_muC : LC.roots.count (mu : ℂ) = 1 :=
  le_antisymm
    (salem_count_le_one (by linarith [mu_gt_one]) (ne_of_gt mu_gt_one) mu_trace)
    (Multiset.count_pos.mpr muC_mem)

lemma count_nuC : LC.roots.count (nu : ℂ) = 1 :=
  le_antisymm
    (salem_count_le_one nu_pos (ne_of_lt nu_lt_one) nu_trace)
    (Multiset.count_pos.mpr nuC_mem)

/-! ### Norm products over classified root multisets. -/

lemma norm_multiset_prod (S : Multiset ℂ) : ‖S.prod‖ = (S.map fun z => ‖z‖).prod := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih => simp [norm_mul, ih]

lemma norm_muC : ‖((mu : ℝ) : ℂ)‖ = mu := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith [mu_gt_one])]

lemma norm_nuC : ‖((nu : ℝ) : ℂ)‖ = nu := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos nu_pos]

lemma classified_prod (S : Multiset ℂ)
    (hS : ∀ z ∈ S, ‖z‖ = 1 ∨ z = (mu : ℂ) ∨ z = (nu : ℂ)) :
    (S.map fun z => ‖z‖).prod = mu ^ S.count (mu : ℂ) * nu ^ S.count (nu : ℂ) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have hs' : ∀ z ∈ s, ‖z‖ = 1 ∨ z = (mu : ℂ) ∨ z = (nu : ℂ) :=
      fun z hz => hS z (Multiset.mem_cons_of_mem hz)
    have ihs := ih hs'
    rcases hS a (Multiset.mem_cons_self a s) with h1 | rfl | rfl
    · have hamu : (mu : ℂ) ≠ a := by
        intro h; rw [← h, norm_muC] at h1; linarith [mu_gt_one]
      have hanu : (nu : ℂ) ≠ a := by
        intro h; rw [← h, norm_nuC] at h1; linarith [nu_lt_one]
      rw [Multiset.map_cons, Multiset.prod_cons, h1, one_mul, ihs,
        Multiset.count_cons_of_ne hamu, Multiset.count_cons_of_ne hanu]
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_muC, ihs,
        Multiset.count_cons_self, Multiset.count_cons_of_ne muC_ne_nuC.symm, pow_succ]
      ring
    · rw [Multiset.map_cons, Multiset.prod_cons, norm_nuC, ihs,
        Multiset.count_cons_of_ne muC_ne_nuC, Multiset.count_cons_self, pow_succ]
      ring

/-- Norm of the constant term of a monic integer polynomial = product of root norms. -/
lemma norm_eval_zero_eq_prod {H : Polynomial ℤ} (hHm : H.Monic) :
    ‖(H.map (Int.castRingHom ℂ)).eval 0‖ =
      ((H.map (Int.castRingHom ℂ)).roots.map fun z => ‖z‖).prod := by
  rw [(IsAlgClosed.splits (H.map (Int.castRingHom ℂ))).eval_eq_prod_roots_of_monic
    (hHm.map _), norm_multiset_prod, Multiset.map_map]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x _ => by simp)

/-! ### THE FACTOR KILL: no proper monic factor of Lehmer exists. -/

/-- **STAGE 2, ASSEMBLED (proven)**: a monic factor of Lehmer of degree 1–9 is
    impossible.  `F(0)·G(0) = L(0) = 1` pins both constant terms at norm one; the
    classified norm product is `μ^a·ν^b` with the pair counts `a, b ∈ {0,1}` summing
    to one across the two factors; the split cases give `μ = 1` or `ν = 1` (refuted),
    and the non-split cases leave an all-on-circle factor — killed by
    `no_unit_circle_factor` (Kronecker + the uniform-1291 cyclotomic kill). -/
theorem lehmer_no_proper_factor {F : Polynomial ℤ} (hFm : F.Monic)
    (hd1 : 1 ≤ F.natDegree) (hd9 : F.natDegree ≤ 9) (hdvd : F ∣ lehmerPolynomial) : False := by
  obtain ⟨G, hG⟩ := hdvd
  have hGm : G.Monic := hFm.of_mul_monic_left (hG ▸ lehmerPolynomial_monic)
  have hdeg : F.natDegree + G.natDegree = 10 := by
    rw [← Polynomial.natDegree_mul hFm.ne_zero hGm.ne_zero, ← hG, lehmerPolynomial_natDegree]
  have hGdvd : G ∣ lehmerPolynomial := ⟨F, by rw [hG]; ring⟩
  -- constant terms multiply to L(0) = 1
  have hev : F.eval 0 * G.eval 0 = 1 := by
    have h := congrArg (Polynomial.eval 0) hG
    rw [Polynomial.eval_mul] at h
    rw [← h]
    unfold lehmerPolynomial
    simp
  -- complex sides
  have hLCsplit : LC = F.map (Int.castRingHom ℂ) * G.map (Int.castRingHom ℂ) := by
    rw [LC, hG, Polynomial.map_mul]
  have hroots_add : LC.roots =
      (F.map (Int.castRingHom ℂ)).roots + (G.map (Int.castRingHom ℂ)).roots := by
    rw [hLCsplit, Polynomial.roots_mul
      (mul_ne_zero (hFm.map (Int.castRingHom ℂ)).ne_zero (hGm.map (Int.castRingHom ℂ)).ne_zero)]
  have hFsub : ∀ z ∈ (F.map (Int.castRingHom ℂ)).roots, z ∈ LC.roots := by
    intro z hz; rw [hroots_add]; exact Multiset.mem_add.mpr (Or.inl hz)
  have hGsub : ∀ z ∈ (G.map (Int.castRingHom ℂ)).roots, z ∈ LC.roots := by
    intro z hz; rw [hroots_add]; exact Multiset.mem_add.mpr (Or.inr hz)
  -- pair counts split across the factors
  have hcnt_mu : (F.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) +
      (G.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) = 1 := by
    rw [← Multiset.count_add, ← hroots_add, count_muC]
  have hcnt_nu : (F.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) +
      (G.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) = 1 := by
    rw [← Multiset.count_add, ← hroots_add, count_nuC]
  -- both constant terms have norm one
  have hFev : ‖(F.map (Int.castRingHom ℂ)).eval 0‖ = 1 := by
    have hcast : (F.map (Int.castRingHom ℂ)).eval 0 = ((F.eval 0 : ℤ) : ℂ) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
        Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hev with ⟨hf, _⟩ | ⟨hf, _⟩ <;>
      rw [hcast, hf] <;> norm_num
  have hGev : ‖(G.map (Int.castRingHom ℂ)).eval 0‖ = 1 := by
    have hcast : (G.map (Int.castRingHom ℂ)).eval 0 = ((G.eval 0 : ℤ) : ℂ) := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
        Polynomial.coeff_zero_eq_eval_zero]
      rfl
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hev with ⟨_, hg⟩ | ⟨_, hg⟩ <;>
      rw [hcast, hg] <;> norm_num
  -- classified norm products
  have hFprod : mu ^ (F.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) *
      nu ^ (F.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) = 1 := by
    rw [← classified_prod _ (fun z hz => root_classification (hFsub z hz)),
      ← norm_eval_zero_eq_prod hFm, hFev]
  have hGprod : mu ^ (G.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) *
      nu ^ (G.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) = 1 := by
    rw [← classified_prod _ (fun z hz => root_classification (hGsub z hz)),
      ← norm_eval_zero_eq_prod hGm, hGev]
  -- case analysis on the pair counts in F
  have haF : (F.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) = 0 ∨
      (F.map (Int.castRingHom ℂ)).roots.count (mu : ℂ) = 1 := by omega
  have hbF : (F.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) = 0 ∨
      (F.map (Int.castRingHom ℂ)).roots.count (nu : ℂ) = 1 := by omega
  rcases haF with ha | ha <;> rcases hbF with hb | hb
  · -- (0,0): F is all-on-circle
    refine no_unit_circle_factor hFm (by omega) ⟨G, hG⟩ ?_
    intro z hz
    rcases root_classification (hFsub z hz) with h | rfl | rfl
    · exact h
    · exact absurd (Multiset.count_pos.mpr hz) (by omega)
    · exact absurd (Multiset.count_pos.mpr hz) (by omega)
  · -- (0,1): ν = 1
    rw [ha, hb, pow_zero, pow_one, one_mul] at hFprod
    linarith [nu_lt_one, hFprod.le]
  · -- (1,0): μ = 1
    rw [ha, hb, pow_one, pow_zero, mul_one] at hFprod
    linarith [mu_gt_one, hFprod.ge]
  · -- (1,1): G is all-on-circle
    refine no_unit_circle_factor hGm (by omega) hGdvd ?_
    intro z hz
    rcases root_classification (hGsub z hz) with h | rfl | rfl
    · exact h
    · exact absurd (Multiset.count_pos.mpr hz) (by omega)
    · exact absurd (Multiset.count_pos.mpr hz) (by omega)

/-! ### FIRE: irreducibility over ℤ and ℚ, and the unconditional charpoly. -/

/-- **IRREDUCIBILITY OF LEHMER'S POLYNOMIAL (proven, over ℤ)**. -/
theorem lehmer_irreducible : Irreducible lehmerPolynomial := by
  constructor
  · intro hu
    have h := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [lehmerPolynomial_natDegree] at h
    exact absurd h (by norm_num)
  · intro a b hab
    by_contra hcon
    push_neg at hcon
    obtain ⟨hua, hub⟩ := hcon
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_mul] at hab; exact lehmerPolynomial_monic.ne_zero hab
    have hb0 : b ≠ 0 := by
      rintro rfl; rw [mul_zero] at hab; exact lehmerPolynomial_monic.ne_zero hab
    have hdeg : a.natDegree + b.natDegree = 10 := by
      rw [← Polynomial.natDegree_mul ha0 hb0, ← hab, lehmerPolynomial_natDegree]
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact lehmerPolynomial_monic
    have hdega : a.natDegree ≠ 0 := by
      intro h0
      apply hua
      have hunit : IsUnit a.leadingCoeff := IsUnit.of_mul_eq_one _ hlc
      rw [Polynomial.leadingCoeff, h0] at hunit
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      exact Polynomial.isUnit_C.mpr hunit
    have hdegb : b.natDegree ≠ 0 := by
      intro h0
      apply hub
      have hunit : IsUnit b.leadingCoeff :=
        IsUnit.of_mul_eq_one_right _ hlc
      rw [Polynomial.leadingCoeff, h0] at hunit
      rw [Polynomial.eq_C_of_natDegree_eq_zero h0]
      exact Polynomial.isUnit_C.mpr hunit
    rcases Int.isUnit_iff.mp (IsUnit.of_mul_eq_one _ hlc) with h | h
    · exact lehmer_no_proper_factor h (by omega) (by omega) ⟨b, hab⟩
    · have hma : (-a).Monic := by
        rw [Polynomial.Monic, Polynomial.leadingCoeff_neg, h, neg_neg]
      exact lehmer_no_proper_factor hma
        (by rw [Polynomial.natDegree_neg]; omega)
        (by rw [Polynomial.natDegree_neg]; omega)
        ⟨-b, by rw [hab]; ring⟩

/-- **IRREDUCIBILITY OVER ℚ** (Gauss: primitivity transfers it from ℤ). -/
theorem lehmer_irreducible_rat : Irreducible (lehmerPolynomial.map (Int.castRingHom ℚ)) :=
  (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    lehmerPolynomial_monic.isPrimitive).mp lehmer_irreducible

/-! ### The Coxeter element of E₁₀. -/

/-- The Coxeter element `s₀ s₁ ⋯ s₉`, evaluated to an explicit matrix
    (kernel computation). -/
theorem coxeterE10_eq :
    coxeterE10 =
      !![ 0, 0, 1, 0, 0, 0, 0, 0, -1, -1;
          1, 0, 1, 0, 0, 0, 0, 0, -1, -1;
          0, 1, 1, 0, 0, 0, 0, 0, -1, -1;
          0, 0, 1, 0, 0, 0, 0, 0, -1,  0;
          0, 0, 0, 1, 0, 0, 0, 0, -1,  0;
          0, 0, 0, 0, 1, 0, 0, 0, -1,  0;
          0, 0, 0, 0, 0, 1, 0, 0, -1,  0;
          0, 0, 0, 0, 0, 0, 1, 0, -1,  0;
          0, 0, 0, 0, 0, 0, 0, 1, -1,  0;
          0, 0, 1, 0, 0, 0, 0, 0,  0, -1] := by
  decide

set_option maxRecDepth 1000000 in
/-- Lehmer's polynomial annihilates the Coxeter element (kernel computation). -/
theorem coxeter_annihilation :
    coxeterE10 ^ 10 + coxeterE10 ^ 9 - coxeterE10 ^ 7 - coxeterE10 ^ 6 - coxeterE10 ^ 5 -
      coxeterE10 ^ 4 - coxeterE10 ^ 3 + coxeterE10 + 1 = 0 := by
  rw [coxeterE10_eq]
  decide

/-- The annihilation, restated through `aeval`. -/
theorem aeval_coxeterE10_lehmer :
    (Polynomial.aeval coxeterE10) lehmerPolynomial = 0 := by
  have h := coxeter_annihilation
  unfold lehmerPolynomial
  simpa [map_add, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_one] using h

/-- The characteristic polynomial of the E₁₀ Coxeter element is Lehmer's polynomial,
    over ℚ. -/
theorem coxeter_charpoly_rat :
    (coxeterE10.map (Int.castRingHom ℚ)).charpoly =
      lehmerPolynomial.map (Int.castRingHom ℚ) :=
  charpoly_eq_lehmer_of_irreducible aeval_coxeterE10_lehmer lehmer_irreducible_rat

/-- **The characteristic polynomial of a Coxeter element of E₁₀ is Lehmer's
    polynomial**, over ℤ (McMullen, *Coxeter groups, Salem numbers and the Hilbert
    metric*, 2002 — here as a kernel-checked identity). -/
theorem coxeter_charpoly_lehmer :
    coxeterE10.charpoly = lehmerPolynomial := by
  have h := coxeter_charpoly_rat
  rw [Matrix.charpoly_map] at h
  exact Polynomial.map_injective _ Int.cast_injective h

end LehmerE10
