/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import LeanPool.HasseMinkowski.HighRank
public import LeanPool.HasseMinkowski.HilbertSymbol.Existence
public import LeanPool.HasseMinkowski.HilbertSymbol.Local
public import LeanPool.HasseMinkowski.Legendre
public import LeanPool.HasseMinkowski.Prod
public import LeanPool.HasseMinkowski.RankCriteria

/-!
# Rank-4 Hasse–Minkowski over ℚ

A diagonal rank-four form `⟨a₁,a₂,a₃,a₄⟩` splits as an orthogonal sum
`⟨a₁,a₂⟩ ⊥ ⟨a₃,a₄⟩`; over a field in which `2` is invertible we may reindex the four
coordinates as two pairs.  When the form is isotropic at a place `v`, this gives a nonzero
`x_v` represented by both `⟨a₁,a₂⟩` and `⟨−a₃,−a₄⟩` (WP4.1).  Feeding the resulting local
data into Serre's existence theorem produces a single rational `x` with the same local
behaviour, and then `isotropic_of_rank_three'` shows each half represents `x` over `ℚ`
(WP4.2).  Diagonalizing an arbitrary nondegenerate rank-four form gives the general theorem
(WP4.3).
-/

@[expose] public section

open Module QuadraticMap

namespace HasseMinkowski

/-! ### WP4.1 — local splitting of a rank-four diagonal form

The four coordinates `(x₀,x₁,x₂,x₃)` are regrouped as `((x₀,x₁),(x₂,x₃))`, and the
weighted sum of squares `⟨a₁,a₂,a₃,a₄⟩` becomes the orthogonal sum
`⟨a₁,a₂⟩ ⊥ ⟨a₃,a₄⟩`.  Since `⟨a₃,a₄⟩ = −⟨−a₃,−a₄⟩`, isotropy of the orthogonal sum and
nondegeneracy of both halves produce a common nonzero value. -/

section LocalSplitting

variable {k : Type*} [Field k] [Invertible (2 : k)]

-- Theorem: the linear equivalence `(x₀,x₁,x₂,x₃) ↦ ((x₀,x₁),(x₂,x₃))` splitting `Fin 4`
-- into two pairs of coordinates.
private noncomputable def splitLinearEquiv (k : Type*) [Field k] :
    (Fin 4 → k) ≃ₗ[k] ((Fin 2 → k) × (Fin 2 → k)) where
  toFun v := (![v 0, v 1], ![v 2, v 3])
  invFun p := ![p.1 0, p.1 1, p.2 0, p.2 1]
  map_add' v w := by
    ext i <;> fin_cases i <;> rfl
  map_smul' c v := by
    ext i <;> fin_cases i <;> rfl
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    obtain ⟨v, w⟩ := p
    ext i <;> fin_cases i <;> rfl

-- Theorem: the weighted sum of squares `⟨a₁,a₂,a₃,a₄⟩` is isometric to the orthogonal sum
-- of `⟨a₁,a₂⟩` and `⟨a₃,a₄⟩` under the coordinate split.
private noncomputable def splitIsometryEquiv (a₁ a₂ a₃ a₄ : k) :
    (weightedSumSquares k ![a₁, a₂, a₃, a₄]).IsometryEquiv
      ((weightedSumSquares k ![a₁, a₂]).prod (weightedSumSquares k ![a₃, a₄])) where
  toLinearEquiv := splitLinearEquiv k
  map_app' v := by
    simp only [splitLinearEquiv, QuadraticMap.prod_apply, weightedSumSquares_apply,
      Fin.sum_univ_two, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons]
    ring

-- Theorem: the diagonal form `⟨a₃,a₄⟩` is the negative of `⟨−a₃,−a₄⟩`.
omit [Invertible (2 : k)] in
private lemma weightedSumSquares_pair_neg (a₃ a₄ : k) :
    weightedSumSquares k ![a₃, a₄] = -(weightedSumSquares k ![-a₃, -a₄]) := by
  ext v
  simp only [neg_apply, weightedSumSquares_apply, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  ring

-- Theorem: a nondegenerate diagonal form with two nonzero weights.
private lemma nondegenerate_pair {a b : k} (ha : a ≠ 0) (hb : b ≠ 0) :
    (weightedSumSquares k ![a, b]).Nondegenerate := by
  let w : Fin 2 → kˣ := ![Units.mk0 a ha, Units.mk0 b hb]
  have hw : (fun i => (w i : k)) = ![a, b] := by
    funext i
    fin_cases i <;> simp [w]
  rw [← hw]
  exact nondegenerate_weightedSumSquares w

-- Theorem (WP4.1): local splitting of a rank-four diagonal form.  If `⟨a₁,a₂,a₃,a₄⟩` is
-- isotropic over a field with `2` invertible and all four weights are nonzero, then some
-- nonzero `x` is represented by both `⟨a₁,a₂⟩` and `⟨−a₃,−a₄⟩`.
theorem local_splitting {a₁ a₂ a₃ a₄ : k} (h₁ : a₁ ≠ 0) (h₂ : a₂ ≠ 0) (h₃ : a₃ ≠ 0)
    (h₄ : a₄ ≠ 0) (h : (weightedSumSquares k ![a₁, a₂, a₃, a₄]).Isotropic) :
    ∃ x : k, x ≠ 0 ∧ (weightedSumSquares k ![a₁, a₂]).represents x ∧
      (weightedSumSquares k ![-a₃, -a₄]).represents x := by
  have hE : (weightedSumSquares k ![a₁, a₂, a₃, a₄]).Equivalent
      ((weightedSumSquares k ![a₁, a₂]).prod (weightedSumSquares k ![a₃, a₄])) :=
    ⟨splitIsometryEquiv a₁ a₂ a₃ a₄⟩
  have hiso : ((weightedSumSquares k ![a₁, a₂]).prod
      (weightedSumSquares k ![a₃, a₄])).Isotropic :=
    (QuadraticMap.Equivalent.isotropic_iff hE).mp h
  rw [weightedSumSquares_pair_neg a₃ a₄] at hiso
  exact iso_prod_neg (nondegenerate_pair h₁ h₂) (nondegenerate_pair (neg_ne_zero.mpr h₃)
    (neg_ne_zero.mpr h₄)) hiso

end LocalSplitting

/-! ### WP4.2 — diagonal rank-four Hasse–Minkowski -/

section RankFourDiagonal

-- Theorem: at a place `K` in which the symbol identity `(x, −ab) = (a,b)` holds, the ternary
-- diagonal form `⟨a,b,−x⟩` is isotropic.
private lemma isotropic_three_of_symbol {K : Type*} [Field K] [Invertible (2 : K)]
    [HasBilinHilbertSym K] [CharZero K] {a b x : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) (hx : x ≠ 0)
    (h : hilbertSym (((-(a * b)) : ℚ) : K) (x : K) = hilbertSym (a : K) (b : K)) :
    (weightedSumSquares K ![(a : K), (b : K), -(x : K)]).Isotropic := by
  have hcast : (((-(a * b)) : ℚ) : K) = -((a : K) * (b : K)) := by push_cast; ring
  rw [hcast, hilbertSym_comm] at h
  exact (weightedSumSquares_two_represents_iff_ternary (Rat.cast_ne_zero.mpr ha)
    (Rat.cast_ne_zero.mpr hb) (Rat.cast_ne_zero.mpr hx)).mp
    ((represents_weightedSumSquares_two_iff (Rat.cast_ne_zero.mpr ha)
      (Rat.cast_ne_zero.mpr hb) (Rat.cast_ne_zero.mpr hx)).mpr h)

-- Theorem: the rank-three local–global principle upgrades the local symbol identities to a
-- global representation of `x` by `⟨a,b⟩`.
private lemma represents_two_of_local_symbol {a b x : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hx : x ≠ 0)
    (hp : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      hilbertSym (((-(a * b)) : ℚ) : ℚ_[p]) (x : ℚ_[p]) =
        hilbertSym (a : ℚ_[p]) (b : ℚ_[p]))
    (hR : hilbertSym (((-(a * b)) : ℚ) : ℝ) (x : ℝ) = hilbertSym (a : ℝ) (b : ℝ)) :
    (weightedSumSquares ℚ ![a, b]).represents x := by
  let w3 : Fin 3 → ℚ := ![a, b, -x]
  have hnd : (weightedSumSquares ℚ w3).Nondegenerate := by
    let u : Fin 3 → ℚˣ :=
      ![Units.mk0 a ha, Units.mk0 b hb, Units.mk0 (-x) (neg_ne_zero.mpr hx)]
    have hu : (fun i => (u i : ℚ)) = w3 := by
      funext i
      fin_cases i <;> simp [u, w3]
    rw [← hu]
    exact nondegenerate_weightedSumSquares u
  have hloc : EverywhereLocallyIsotropic (weightedSumSquares ℚ w3) := by
    constructor
    · intro p hpinst
      have heq := baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) w3
      refine (heq.isotropic_iff).mpr ?_
      rw [show (fun i => algebraMap ℚ ℚ_[p] (w3 i))
          = ![(a : ℚ_[p]), (b : ℚ_[p]), -(x : ℚ_[p])] by
        funext i
        fin_cases i <;> simp [w3]]
      exact isotropic_three_of_symbol ha hb hx (hp p)
    · have heq := baseChange_weightedSumSquares (R := ℚ) (A := ℝ) w3
      refine (heq.isotropic_iff).mpr ?_
      rw [show (fun i => algebraMap ℚ ℝ (w3 i))
          = ![(a : ℝ), (b : ℝ), -(x : ℝ)] by
        funext i
        fin_cases i <;> simp [w3]]
      exact isotropic_three_of_symbol ha hb hx hR
  have hiso : (weightedSumSquares ℚ w3).Isotropic :=
    isotropic_of_rank_three' (weightedSumSquares ℚ w3) (Module.finrank_fin_fun (R := ℚ))
      hnd hloc
  exact (weightedSumSquares_two_represents_iff_ternary ha hb hx).mpr hiso

-- Theorem (WP4.2): diagonal rank-four Hasse–Minkowski over `ℚ`.
theorem rankFourDiagonalHM : RankFourDiagonalHM := by
  intro w hw hp hR
  let b : Fin 2 → ℚ := ![-((w 0) * (w 1)), -((-(w 2)) * (-(w 3)))]
  let ε : Fin 2 → Nat.Primes → ℤ := ![
    fun p => hilbertSym ((w 0 : ℚ_[p])) ((w 1 : ℚ_[p])),
    fun p => hilbertSym ((-(w 2) : ℚ_[p])) ((-(w 3) : ℚ_[p]))]
  let εR : Fin 2 → ℤ := ![
    hilbertSym ((w 0 : ℝ)) ((w 1 : ℝ)),
    hilbertSym ((-(w 2) : ℝ)) ((-(w 3) : ℝ))]
  have hb : ∀ i, b i ≠ 0 := by
    intro i
    fin_cases i
    · simp only [b]
      exact neg_ne_zero.mpr (mul_ne_zero (hw 0) (hw 1))
    · simp only [b]
      exact neg_ne_zero.mpr (mul_ne_zero (neg_ne_zero.mpr (hw 2))
        (neg_ne_zero.mpr (hw 3)))
  have h1 : ∀ i, {p : Nat.Primes | ε i p ≠ 1}.Finite := by
    intro i
    fin_cases i
    · simpa [ε] using finite_nontrivial_hilbertSym (a := w 0) (b := w 1) (hw 0) (hw 1)
    · simpa [ε] using finite_nontrivial_hilbertSym (a := -(w 2)) (b := -(w 3))
        (neg_ne_zero.mpr (hw 2)) (neg_ne_zero.mpr (hw 3))
  have h2 : ∀ i, (∏ᶠ p : Nat.Primes, ε i p) * εR i = 1 := by
    intro i
    fin_cases i
    · simpa [ε, εR] using hilbertReciprocity (w 0) (w 1) (hw 0) (hw 1)
    · simpa [ε, εR] using hilbertReciprocity (-(w 2)) (-(w 3))
        (neg_ne_zero.mpr (hw 2)) (neg_ne_zero.mpr (hw 3))
  have h3 : ∀ p : Nat.Primes, ∃ x : ℚ_[p], x ≠ 0 ∧
      ∀ i, hilbertSym (b i : ℚ_[p]) x = ε i p := by
    intro p
    have hiso : (weightedSumSquares ℚ_[p]
        ![(w 0 : ℚ_[p]), (w 1 : ℚ_[p]), (w 2 : ℚ_[p]), (w 3 : ℚ_[p])]).Isotropic := by
      rw [← show (fun i : Fin 4 => (w i : ℚ_[p]))
          = ![(w 0 : ℚ_[p]), (w 1 : ℚ_[p]), (w 2 : ℚ_[p]), (w 3 : ℚ_[p])] by
        funext i
        fin_cases i <;> rfl]
      exact hp (p : ℕ)
    obtain ⟨x, hx0, hrep1, hrep2⟩ :=
      local_splitting (k := ℚ_[p]) (Rat.cast_ne_zero.mpr (hw 0))
        (Rat.cast_ne_zero.mpr (hw 1)) (Rat.cast_ne_zero.mpr (hw 2))
        (Rat.cast_ne_zero.mpr (hw 3)) hiso
    refine ⟨x, hx0, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hsym := (represents_weightedSumSquares_two_iff (Rat.cast_ne_zero.mpr (hw 0))
          (Rat.cast_ne_zero.mpr (hw 1)) hx0).mp hrep1
      simp only [b, ε, Matrix.cons_val_zero]
      rw [show (((-((w 0) * (w 1)) : ℚ) : ℚ_[p])) =
            -((w 0 : ℚ_[p]) * (w 1 : ℚ_[p])) by push_cast; ring,
        hilbertSym_comm]
      exact hsym
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      have hsym := (represents_weightedSumSquares_two_iff
          (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr (hw 2)))
          (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr (hw 3))) hx0).mp hrep2
      have hsym' : hilbertSym x (-((w 2 : ℚ_[p]) * (w 3 : ℚ_[p]))) =
          hilbertSym (-(w 2 : ℚ_[p])) (-(w 3 : ℚ_[p])) := by
        simpa only [neg_mul_neg] using hsym
      simp only [Fin.isValue, mul_neg, neg_mul, neg_neg, Fin.succ_zero_eq_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Rat.cast_neg, Rat.cast_mul, Matrix.cons_val', b, ε]
      rw [hilbertSym_comm]
      exact hsym'
  have h3R : ∃ x : ℝ, x ≠ 0 ∧ ∀ i, hilbertSym (b i : ℝ) x = εR i := by
    have hiso : (weightedSumSquares ℝ
        ![(w 0 : ℝ), (w 1 : ℝ), (w 2 : ℝ), (w 3 : ℝ)]).Isotropic := by
      rw [← show (fun i : Fin 4 => (w i : ℝ))
          = ![(w 0 : ℝ), (w 1 : ℝ), (w 2 : ℝ), (w 3 : ℝ)] by
        funext i
        fin_cases i <;> rfl]
      exact hR
    obtain ⟨x, hx0, hrep1, hrep2⟩ :=
      local_splitting (k := ℝ) (Rat.cast_ne_zero.mpr (hw 0))
        (Rat.cast_ne_zero.mpr (hw 1)) (Rat.cast_ne_zero.mpr (hw 2))
        (Rat.cast_ne_zero.mpr (hw 3)) hiso
    refine ⟨x, hx0, ?_⟩
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hsym := (represents_weightedSumSquares_two_iff (Rat.cast_ne_zero.mpr (hw 0))
          (Rat.cast_ne_zero.mpr (hw 1)) hx0).mp hrep1
      simp only [b, εR, Matrix.cons_val_zero]
      rw [show (((-((w 0) * (w 1)) : ℚ) : ℝ)) =
            -((w 0 : ℝ) * (w 1 : ℝ)) by push_cast; ring,
        hilbertSym_comm]
      exact hsym
    · have hj : j = 0 := Subsingleton.elim j 0
      subst hj
      have hsym := (represents_weightedSumSquares_two_iff
          (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr (hw 2)))
          (neg_ne_zero.mpr (Rat.cast_ne_zero.mpr (hw 3))) hx0).mp hrep2
      have hsym' : hilbertSym x (-((w 2 : ℝ) * (w 3 : ℝ))) =
          hilbertSym (-(w 2 : ℝ)) (-(w 3 : ℝ)) := by
        simpa only [neg_mul_neg] using hsym
      simp only [Fin.isValue, mul_neg, neg_mul, neg_neg, Fin.succ_zero_eq_one, Matrix.cons_val_one,
        Matrix.cons_val_fin_one, Rat.cast_neg, Rat.cast_mul, b, εR]
      rw [hilbertSym_comm]
      exact hsym'
  obtain ⟨x, hx0, hxp, hxR⟩ := Existence.exists_rat_hilbertSym b hb ε εR h1 h2 h3 h3R
  have hrepA : (weightedSumSquares ℚ ![w 0, w 1]).represents x :=
    represents_two_of_local_symbol (hw 0) (hw 1) hx0
      (fun p hpinst => by
        have h := hxp 0 ⟨p, hpinst.out⟩
        simpa only [b, ε, Matrix.cons_val_zero] using h)
      (by
        have h := hxR 0
        simpa only [b, εR, Matrix.cons_val_zero] using h)
  have hrepB : (weightedSumSquares ℚ ![-w 2, -w 3]).represents x :=
    represents_two_of_local_symbol (neg_ne_zero.mpr (hw 2)) (neg_ne_zero.mpr (hw 3)) hx0
      (fun p hpinst => by
        have h := hxp 1 ⟨p, hpinst.out⟩
        simpa only [b, ε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Rat.cast_neg] using h)
      (by
        have h := hxR 1
        simpa only [b, εR, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Rat.cast_neg] using h)
  have hrepB' : (weightedSumSquares ℚ ![w 2, w 3]).represents (-x) := by
    obtain ⟨v, hv, hvQ⟩ := hrepB
    refine ⟨v, hv, ?_⟩
    rw [weightedSumSquares_pair_neg (w 2) (w 3), neg_apply, hvQ]
  have hprod : ((weightedSumSquares ℚ ![w 0, w 1]).prod
      (weightedSumSquares ℚ ![w 2, w 3])).Isotropic :=
    (prod_isotropic_iff _ _).mpr (Or.inr (Or.inr ⟨x, hx0, hrepA, hrepB'⟩))
  have hE : (weightedSumSquares ℚ ![w 0, w 1, w 2, w 3]).Equivalent
      ((weightedSumSquares ℚ ![w 0, w 1]).prod (weightedSumSquares ℚ ![w 2, w 3])) :=
    ⟨splitIsometryEquiv (w 0) (w 1) (w 2) (w 3)⟩
  have hfinal : (weightedSumSquares ℚ ![w 0, w 1, w 2, w 3]).Isotropic :=
    (QuadraticMap.Equivalent.isotropic_iff hE).mpr hprod
  rwa [show (![w 0, w 1, w 2, w 3] : Fin 4 → ℚ) = w by
    funext i
    fin_cases i <;> rfl] at hfinal

end RankFourDiagonal

/-! ### WP4.3 — rank-four Hasse–Minkowski for an arbitrary form -/

section RankFourGeneral

variable {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]

-- Theorem: a nondegenerate rank-four form over `ℚ` that is isotropic over every completion is
-- isotropic over `ℚ`.
theorem isotropic_of_rank_four (Q : QuadraticForm ℚ V) (hr : finrank ℚ V = 4)
    (hQ : Q.Nondegenerate) (hQ' : EverywhereLocallyIsotropic Q) : Isotropic Q := by
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  have hsep : (QuadraticMap.associated (R := ℚ) Q).SeparatingLeft :=
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  obtain ⟨w₀, hw₀⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hsep
  have hw4 : ∃ w : Fin 4 → ℚˣ,
      Q.Equivalent (weightedSumSquares ℚ (fun i => (w i : ℚ))) := by
    revert w₀ hw₀
    rw [hr]
    exact fun w hw => ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hw4
  let wq : Fin 4 → ℚ := fun i => (w i : ℚ)
  have hwq : ∀ i, wq i ≠ 0 := fun i => by simp [wq]
  have hw' : Q.Equivalent (weightedSumSquares ℚ wq) := by simpa only [wq] using hw
  have hlocf : ∀ (p : ℕ) [Fact (Nat.Prime p)],
      (weightedSumSquares ℚ_[p] (fun i => (wq i : ℚ_[p]))).Isotropic := by
    intro p hpinst
    have heq : (Q.baseChange ℚ_[p]).Equivalent
        (weightedSumSquares ℚ_[p] (fun i => algebraMap ℚ ℚ_[p] (wq i))) :=
      (hw'.baseChange (A := ℚ_[p])).trans
        (baseChange_weightedSumSquares (R := ℚ) (A := ℚ_[p]) (w := wq))
    have h2 : Isotropic (weightedSumSquares ℚ_[p]
        (fun i => algebraMap ℚ ℚ_[p] (wq i))) :=
      (heq.isotropic_iff).mp (hQ'f p)
    have hfun : (fun i => algebraMap ℚ ℚ_[p] (wq i)) = (fun i => (wq i : ℚ_[p])) := by
      funext i
      simp
    rw [hfun] at h2
    exact h2
  have hlocR : (weightedSumSquares ℝ (fun i => (wq i : ℝ))).Isotropic := by
    have heq : (Q.baseChange ℝ).Equivalent
        (weightedSumSquares ℝ (fun i => algebraMap ℚ ℝ (wq i))) :=
      (hw'.baseChange (A := ℝ)).trans
        (baseChange_weightedSumSquares (R := ℚ) (A := ℝ) (w := wq))
    have h2 : Isotropic (weightedSumSquares ℝ (fun i => algebraMap ℚ ℝ (wq i))) :=
      (heq.isotropic_iff).mp hQ'R
    have hfun : (fun i => algebraMap ℚ ℝ (wq i)) = (fun i => (wq i : ℝ)) := by
      funext i
      simp
    rw [hfun] at h2
    exact h2
  have hglob : (weightedSumSquares ℚ wq).Isotropic :=
    rankFourDiagonalHM wq hwq hlocf hlocR
  exact (hw'.isotropic_iff).mpr hglob

end RankFourGeneral

end HasseMinkowski
