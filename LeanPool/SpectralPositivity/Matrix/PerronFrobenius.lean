/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.SpectralPositivity.Matrix.NonnegPower
import LeanPool.SpectralPositivity.Operator.JentzschProof
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences

/-!
# Perron–Frobenius Theorem for Nonneg Matrices

If A ≥ 0 is irreducible, then:
- The spectral radius r(A) is a simple eigenvalue of A
- There exists a corresponding eigenvector v > 0 (all entries strictly positive)
- |λ| ≤ r(A) for all eigenvalues λ

## Proof strategy

We prove the existence part using the Collatz–Wielandt minimax characterization.
For B = A^k with all entries strictly positive (from `exists_pos_power`):

1. Define ρ(v) = min_i (Bv)_i/v_i on the positive part of the simplex.
2. Restrict to compact subsets S_ε = {v | v_i ≥ ε, ∑ v_i = 1} and maximize ρ.
3. Show the maximizer has all ratios (Bv)_i/v_i equal (eigenvector of B).
4. Lift from B = A^k to A using commutativity and uniqueness of the Perron
   eigenvector of B.

## References

- Horn–Johnson, *Matrix Analysis*, Cambridge, 2013, Ch. 8
- Seneta, *Non-negative Matrices and Markov Chains*, Springer, 2006
-/

open Matrix BigOperators Finset MeasureTheory

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonneg matrix A is irreducible if:
(1) all entries are nonneg,
(2) for every pair (i, j) there exists k > 0 such that (A^k)_{ij} > 0
    (i.e., the directed graph of A is strongly connected), and
(3) there exists a vertex with a positive self-loop (aperiodicity).

The aperiodicity condition (3) is necessary for `exists_pos_power`. Without it,
periodic irreducible matrices (e.g., the permutation matrix of a 2-cycle
`[[0,1],[1,0]]`) satisfy (1)-(2) but have no single power k with all entries
of A^k strictly positive.

This definition therefore characterizes *primitive* nonneg matrices. -/
def Matrix.IsIrreducible (A : Matrix n n ℝ) : Prop :=
  A.Nonneg ∧ (∀ i j : n, ∃ k : ℕ, 0 < k ∧ 0 < (A ^ k) i j) ∧ (∃ i : n, 0 < A i i)

/-! ## Submultiplicativity and padding lemmas -/

/-- Submultiplicativity for nonneg matrix powers: if (A^a)_{ij} > 0 and
(A^b)_{jl} > 0, then (A^{a+b})_{il} > 0. This follows by extracting the
single positive term (A^a)_{ij} * (A^b)_{jl} from the matrix product sum
∑_m (A^a)_{im} * (A^b)_{ml}, with all other terms nonneg. -/
lemma Matrix.Nonneg.pos_pow_mul {A : Matrix n n ℝ} (hA : A.Nonneg)
    {a b : ℕ} {i j l : n}
    (ha : 0 < (A ^ a) i j) (hb : 0 < (A ^ b) j l) :
    0 < (A ^ (a + b)) i l := by
  rw [pow_add, Matrix.mul_apply]
  apply Finset.sum_pos'
  · intro m _; exact mul_nonneg ((hA.pow a) i m) ((hA.pow b) m l)
  · exact ⟨j, Finset.mem_univ j, mul_pos ha hb⟩

/-- Padding lemma: if A is nonneg with A_{rr} > 0 and (A^k)_{ir} > 0,
then (A^{k+m})_{ir} > 0 for all m ≥ 0. The positive self-loop at r absorbs
arbitrary additional steps: each extra step contributes a factor of A_{rr} > 0
through the path staying at r. -/
lemma Matrix.Nonneg.pos_pow_pad {A : Matrix n n ℝ} (hA : A.Nonneg)
    {r : n} (hdiag : 0 < A r r) {k : ℕ} {i : n}
    (hk : 0 < (A ^ k) i r) (m : ℕ) :
    0 < (A ^ (k + m)) i r := by
  induction m with
  | zero => simp [hk]
  | succ m ih =>
    rw [show k + (m + 1) = (k + m) + 1 from by omega]
    exact hA.pos_pow_mul ih (by rwa [pow_one])

/-! ## Primitive power existence -/

/-- An irreducible nonneg matrix has a primitive power: there exists k
such that A^k has all strictly positive entries.

**Proof.** Fix a vertex r with A_{rr} > 0 (the aperiodicity condition).
For each i, choose kᵢ with (A^{kᵢ})_{ir} > 0 (connectivity to r).
For each j, choose kⱼ with (A^{kⱼ})_{rj} > 0 (connectivity from r).
By submultiplicativity through r:
  (A^{kᵢ + kⱼ})_{ij} ≥ (A^{kᵢ})_{ir} · (A^{kⱼ})_{rj} > 0.
By the padding lemma (using A_{rr} > 0), we can inflate kᵢ by any amount:
  (A^{kᵢ + m})_{ir} > 0 for all m ≥ 0.
Setting K = max_i(kᵢ) + max_j(kⱼ) and writing K = kᵢ + slack + kⱼ with
slack = K − kᵢ − kⱼ ≥ 0, the padded submultiplicativity gives
  (A^K)_{ij} ≥ (A^{kᵢ + slack})_{ir} · (A^{kⱼ})_{rj} > 0
for all i, j. -/
theorem Matrix.IsIrreducible.exists_pos_power {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) :
    ∃ k : ℕ, 0 < k ∧ ∀ i j : n, 0 < (A ^ k) i j := by
  obtain ⟨hnn, hconn, r, hdiag⟩ := hA
  -- For each i, choose kᵢ with (A^{kᵢ})_{ir} > 0
  choose ki hki_pos hki_entry using (fun i => hconn i r)
  -- For each j, choose kⱼ with (A^{kⱼ})_{rj} > 0
  choose kj hkj_pos hkj_entry using (fun j => hconn r j)
  -- Handle the empty type (vacuously true)
  by_cases hn : IsEmpty n
  · exact ⟨1, Nat.one_pos, fun i => (hn.false i).elim⟩
  · rw [not_isEmpty_iff] at hn
    -- Take K = max_i(kᵢ) + max_j(kⱼ) via Finset.sup' on the nonempty universe
    let max_row := (Finset.univ : Finset n).sup' (Finset.univ_nonempty_iff.mpr hn) ki
    let max_col := (Finset.univ : Finset n).sup' (Finset.univ_nonempty_iff.mpr hn) kj
    refine ⟨max_row + max_col, ?_, ?_⟩
    · -- K > 0: max_row ≥ kᵢ(arbitrary) > 0
      have : ki (Classical.choice hn) ≤ max_row :=
        Finset.le_sup' ki (Finset.mem_univ _)
      linarith [hki_pos (Classical.choice hn)]
    · -- For each pair (p, q), show (A^K)_{pq} > 0
      intro p q
      -- Rewrite K = kᵢ(p) + slack + kⱼ(q) where slack absorbs into the padding
      have h_eq : max_row + max_col =
          ki p + ((max_row - ki p) + (max_col - kj q)) + kj q := by
        have : ki p ≤ max_row := Finset.le_sup' ki (Finset.mem_univ p)
        have : kj q ≤ max_col := Finset.le_sup' kj (Finset.mem_univ q)
        omega
      rw [h_eq]
      -- By padding: (A^{kᵢ(p) + slack})_{pr} > 0, then by submult with (A^{kⱼ(q)})_{rq} > 0
      exact hnn.pos_pow_mul (hnn.pos_pow_pad hdiag (hki_entry p) _) (hkj_entry q)

/-! ## Perron–Frobenius theorem -/

/-! ### Helper lemmas for mulVec positivity -/

omit [DecidableEq n] in
/-- A nonneg matrix applied to a nonneg vector gives a nonneg vector. -/
lemma Matrix.Nonneg.mulVec_nonneg {A : Matrix n n ℝ} (hA : A.Nonneg)
    {v : n → ℝ} (hv : ∀ i, 0 ≤ v i) : ∀ i, 0 ≤ A.mulVec v i := by
  intro i
  simp only [mulVec, dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hA i j) (hv j)

omit [DecidableEq n] in
/-- A matrix with all positive entries, applied to a nonneg nonzero vector,
gives a strictly positive vector. -/
lemma Matrix.mulVec_pos_of_allPos {B : Matrix n n ℝ} (hB : ∀ i j, 0 < B i j)
    {v : n → ℝ} (hv_nn : ∀ i, 0 ≤ v i) (hv_ne : ∃ j, 0 < v j) :
    ∀ i, 0 < B.mulVec v i := by
  intro i
  simp only [mulVec, dotProduct]
  obtain ⟨j, hj⟩ := hv_ne
  exact Finset.sum_pos' (fun l _ => mul_nonneg (le_of_lt (hB i l)) (hv_nn l))
    ⟨j, Finset.mem_univ j, mul_pos (hB i j) hj⟩

omit [DecidableEq n] in
/-- A nonneg matrix applied to a positive vector gives a positive vector,
provided each row has a positive entry. -/
lemma Matrix.mulVec_pos_of_pos {A : Matrix n n ℝ} (hA : A.Nonneg)
    (hrows : ∀ i, ∃ j, 0 < A i j)
    {v : n → ℝ} (hv : ∀ i, 0 < v i) : ∀ i, 0 < A.mulVec v i := by
  intro i
  simp only [mulVec, dotProduct]
  obtain ⟨j, hj⟩ := hrows i
  exact Finset.sum_pos' (fun l _ => mul_nonneg (hA i l) (le_of_lt (hv l)))
    ⟨j, Finset.mem_univ j, mul_pos hj (hv j)⟩

/-- An irreducible nonneg matrix has at least one positive entry in each row
(since for each i, there exists k > 0 and j with (A^k)_{ij} > 0, and the
first step of the path gives a positive entry in row i of A). -/
lemma Matrix.IsIrreducible.row_has_pos_entry {A : Matrix n n ℝ}
    (hA : A.IsIrreducible) (i : n) : ∃ j, 0 < A i j := by
  obtain ⟨hnn, hconn, _⟩ := hA
  obtain ⟨k, hk_pos, hk_entry⟩ := hconn i i
  -- (A^k)_{ii} > 0, so expanding A^k = A · A^{k-1}, there exists j with
  -- A_{ij} · (A^{k-1})_{ji} > 0, hence A_{ij} > 0.
  cases k with
  | zero => omega
  | succ m =>
    rw [pow_succ', mul_apply] at hk_entry
    -- Now hk_entry : 0 < ∑ j, A i j * (A^m) j i
    have h_nn_terms : ∀ j ∈ Finset.univ, 0 ≤ A i j * (A ^ m) j i :=
      fun j _ => mul_nonneg (hnn i j) ((hnn.pow m) j i)
    -- Extract a term that is positive
    obtain ⟨j, _, hj_pos⟩ := (Finset.sum_pos_iff_of_nonneg h_nn_terms).mp hk_entry
    -- A_{ij} * (A^m)_{ji} > 0 with both factors nonneg implies A_{ij} > 0
    exact ⟨j, by
      rcases (mul_pos_iff.mp hj_pos) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · linarith [hnn i j]⟩

-- Note: Matrix.mulVec_smul from Mathlib gives: M *ᵥ (b • v) = b • M *ᵥ v

/-- `pow` and `mulVec` interaction: (A^m).mulVec ((A^l).mulVec v) =
(A^(m+l)).mulVec v. -/
lemma Matrix.pow_mulVec_comp {A : Matrix n n ℝ} {m l : ℕ} {v : n → ℝ} :
    (A ^ m).mulVec ((A ^ l).mulVec v) = (A ^ (m + l)).mulVec v := by
  rw [pow_add, ← mulVec_mulVec]

-- ### Collatz–Wielandt monotonicity

omit [DecidableEq n] in
/-- Key Collatz–Wielandt monotonicity: if Bv >= lam*v componentwise and B >= 0,
then B^2 v >= lam*(Bv) componentwise. -/
lemma collatz_wielandt_monotone
    {B : Matrix n n ℝ} (hB_nn : ∀ i j, 0 ≤ B i j)
    {v : n → ℝ} {lam : ℝ}
    (hBv_ge : ∀ i, lam * v i ≤ B.mulVec v i) :
    ∀ i, lam * B.mulVec v i ≤ (B * B).mulVec v i := by
  intro i
  -- (B²v)_i = (B(Bv))_i = ∑_j B_{ij} (Bv)_j ≥ ∑_j B_{ij} (lam * v_j) = lam * (Bv)_i
  rw [← mulVec_mulVec]
  simp only [mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  calc B i j * B.mulVec v j ≥ B i j * (lam * v j) :=
        mul_le_mul_of_nonneg_left (hBv_ge j) (hB_nn i j)
    _ = lam * (B i j * v j) := by ring

omit [DecidableEq n] in
/-- Strict version: if B > 0 entrywise and Bv > lam*v at some coordinate,
then B^2 v > lam*(Bv) at every coordinate. -/
lemma collatz_wielandt_strict
    {B : Matrix n n ℝ} (hB : ∀ i j, 0 < B i j)
    {v : n → ℝ} {lam : ℝ}
    (hBv_ge : ∀ i, lam * v i ≤ B.mulVec v i)
    (hBv_strict : ∃ j, lam * v j < B.mulVec v j) :
    ∀ i, lam * B.mulVec v i < (B * B).mulVec v i := by
  intro i
  obtain ⟨j₀, hj₀⟩ := hBv_strict
  rw [← mulVec_mulVec]
  simp only [mulVec, dotProduct]
  rw [Finset.mul_sum]
  apply Finset.sum_lt_sum
  · intro j _
    calc B i j * B.mulVec v j ≥ B i j * (lam * v j) :=
          mul_le_mul_of_nonneg_left (hBv_ge j) (le_of_lt (hB i j))
      _ = lam * (B i j * v j) := by ring
  · exact ⟨j₀, Finset.mem_univ j₀, by
      calc B i j₀ * B.mulVec v j₀ > B i j₀ * (lam * v j₀) :=
            mul_lt_mul_of_pos_left hj₀ (hB i j₀)
        _ = lam * (B i j₀ * v j₀) := by ring⟩

/- A matrix with all strictly positive entries has a positive eigenvector.

This is the core of the Perron–Frobenius existence proof.

**Proof outline (Collatz–Wielandt).** Define ρ(v) = min_i (Bv)_i/v_i on
the positive simplex. By `collatz_wielandt_strict`, if Bv ≠ ρ(v)·v then
ρ(Bv) > ρ(v). On the compact set S_ε = {v | v_i ≥ ε, ∑ v_i = 1} for
ε = min_{ij} B_{ij} / (n · max_i ∑_j B_{ij}) > 0, the normalized map
ψ(v) = Bv/‖Bv‖₁ maps S_ε into its interior. The function ρ (continuous
as inf of continuous functions on S_ε) attains its maximum at v*. Since
ψ(v*) ∈ S_ε and ρ(ψ(v*)) ≥ ρ(v*) = max, equality holds, forcing
Bv* = ρ(v*)·v* by the strict monotonicity.

The full formalization connects Mathlib's `IsCompact.exists_isMaxOn`
with `ContinuousOn.finset_inf'_apply` on a compact subset of the standard simplex. -/
omit [DecidableEq n] in
theorem allpos_has_pos_eigenvec (hn : Nonempty n)
    {B : Matrix n n ℝ} (hB : ∀ i j, 0 < B i j) :
    ∃ (μ : ℝ) (w : n → ℝ), 0 < μ ∧ (∀ i, 0 < w i) ∧ B.mulVec w = μ • w := by
  -- Convenience abbreviations
  have huniv : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty_iff.mpr hn
  have hB_nn : ∀ i j, (0 : ℝ) ≤ B i j := fun i j => le_of_lt (hB i j)
  -- The Collatz–Wielandt ratio ρ(v) = min_i (Bv)_i / v_i
  let ρ : (n → ℝ) → ℝ := fun v => Finset.inf' Finset.univ huniv (fun i => B.mulVec v i / v i)
  -- Step 1: Define key constants
  -- c = minimum entry of B (> 0)
  let c : ℝ := Finset.inf' Finset.univ huniv (fun i =>
    Finset.inf' Finset.univ huniv (fun j => B i j))
  have hc_pos : 0 < c := by
    rw [Finset.lt_inf'_iff]
    intro i _
    rw [Finset.lt_inf'_iff]
    intro j _
    exact hB i j
  have hc_le : ∀ i j, c ≤ B i j := fun i j =>
    le_trans (Finset.inf'_le _ (Finset.mem_univ i)) (Finset.inf'_le _ (Finset.mem_univ j))
  -- R = maximum column sum of B (> 0)
  let R : ℝ := Finset.sup' Finset.univ huniv (fun j => ∑ i, B i j)
  have hR_pos : 0 < R := by
    calc (0 : ℝ) < ∑ i, B i hn.some :=
          Finset.sum_pos (fun i _ => hB i hn.some) ⟨hn.some, Finset.mem_univ _⟩
      _ ≤ R := Finset.le_sup' (fun j => ∑ i, B i j) (Finset.mem_univ hn.some)
  have hR_le : ∀ j, ∑ i, B i j ≤ R := fun j =>
    Finset.le_sup' (fun j => ∑ i, B i j) (Finset.mem_univ j)
  -- ε = c / R > 0
  let ε : ℝ := c / R
  have hε_pos : 0 < ε := div_pos hc_pos hR_pos
  -- The compact set S_ε = { v | ∀ i, ε ≤ v i, ∑ v = 1 }
  let S : Set (n → ℝ) := { v | (∀ i, ε ≤ v i) ∧ ∑ i, v i = 1 }
  -- S is closed
  have hS_closed : IsClosed S := by
    have h1 : IsClosed { v : n → ℝ | ∀ i, ε ≤ v i } := by
      have : { v : n → ℝ | ∀ i, ε ≤ v i } = ⋂ i, { v | ε ≤ v i } := by
        ext v; simp [Set.mem_iInter]
      rw [this]
      exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
    have h2 : IsClosed { v : n → ℝ | ∑ i, v i = 1 } :=
      isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i) continuous_const
    exact h1.inter h2
  -- S ⊆ stdSimplex
  have hS_sub : S ⊆ stdSimplex ℝ n := by
    intro v ⟨hv_lb, hv_sum⟩
    exact ⟨fun i => le_trans (le_of_lt hε_pos) (hv_lb i), hv_sum⟩
  -- S is compact
  have hS_compact : IsCompact S :=
    (isCompact_stdSimplex ℝ n).of_isClosed_subset hS_closed hS_sub
  -- Step 2: ψ(v) = Bv / ‖Bv‖₁ maps the standard simplex into S
  -- For v ∈ stdSimplex: v ≥ 0, ∑v = 1, v ≠ 0
  -- (Bv)_i ≥ c·∑v = c > 0, so ‖Bv‖₁ > 0 and ψ(v)_i = (Bv)_i/‖Bv‖₁
  -- ∑(Bv) = ∑_i ∑_j B_{ij} v_j ≤ R·∑v = R
  -- So ψ(v)_i ≥ c/R = ε, and ∑ψ(v) = 1
  have h_Bv_lb : ∀ v : n → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i = 1 →
      ∀ i, c ≤ B.mulVec v i := by
    intro v hv_nn hv_sum i
    simp only [mulVec, dotProduct]
    calc c = ∑ j, c * v j := by rw [← Finset.mul_sum, hv_sum, mul_one]
      _ ≤ ∑ j, B i j * v j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hc_le i j) (hv_nn j)
  have h_Bv_sum_ub : ∀ v : n → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i = 1 →
      ∑ i, B.mulVec v i ≤ R := by
    intro v hv_nn hv_sum
    simp only [mulVec, dotProduct]
    calc ∑ i, ∑ j, B i j * v j = ∑ j, v j * ∑ i, B i j := by
          rw [Finset.sum_comm]; congr 1; ext j; rw [Finset.mul_sum]; congr 1; ext i; ring
      _ ≤ ∑ j, v j * R :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hR_le j) (hv_nn j)
      _ = R := by rw [← Finset.sum_mul, hv_sum, one_mul]
  have h_psi_in_S : ∀ v : n → ℝ, (∀ i, 0 ≤ v i) → ∑ i, v i = 1 →
      (fun i => B.mulVec v i / ∑ k, B.mulVec v k) ∈ S := by
    intro v hv_nn hv_sum
    have hBv_pos : ∀ i, 0 < B.mulVec v i := by
      intro i; exact lt_of_lt_of_le hc_pos (h_Bv_lb v hv_nn hv_sum i)
    have hBv_sum_pos : 0 < ∑ i, B.mulVec v i :=
      Finset.sum_pos (fun i _ => hBv_pos i) ⟨hn.some, Finset.mem_univ _⟩
    refine ⟨fun i => ?_, ?_⟩
    · -- ε ≤ (Bv)_i / ∑(Bv)
      rw [le_div_iff₀ hBv_sum_pos]
      calc ε * ∑ k, B.mulVec v k = (c / R) * ∑ k, B.mulVec v k := rfl
        _ ≤ (c / R) * R := by
            apply mul_le_mul_of_nonneg_left (h_Bv_sum_ub v hv_nn hv_sum)
            exact le_of_lt hε_pos
        _ = c := by field_simp
        _ ≤ B.mulVec v i := h_Bv_lb v hv_nn hv_sum i
    · -- ∑ψ(v) = 1
      rw [← Finset.sum_div, div_self (ne_of_gt hBv_sum_pos)]
  -- S is nonempty (apply ψ to uniform distribution)
  have hS_nonempty : S.Nonempty := by
    have h_card_pos : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hn)
    have hu_nn : ∀ i : n, (0 : ℝ) ≤ 1 / Fintype.card n := fun _ => by positivity
    have hu_sum : ∑ _ : n, (1 : ℝ) / Fintype.card n = 1 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_div_cancel₀ 1 (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    exact ⟨_, h_psi_in_S _ hu_nn hu_sum⟩
  -- Step 3: ρ is continuous on S
  -- ρ(v) = inf'_i (Bv_i / v_i), and each Bv_i / v_i is continuous when v_i ≠ 0.
  -- On S, v_i ≥ ε > 0, so v_i ≠ 0.
  have hρ_continuousOn : ContinuousOn ρ S := by
    apply ContinuousOn.finset_inf'_apply
    intro i _
    apply ContinuousOn.div
    · -- B.mulVec v i = ∑ j, B i j * v j is continuous
      exact continuousOn_finsetSum Finset.univ fun j _ =>
        (continuous_const.mul (continuous_apply j)).continuousOn
    · exact (continuous_apply i).continuousOn
    · intro v ⟨hv_lb, _⟩
      exact ne_of_gt (lt_of_lt_of_le hε_pos (hv_lb i))
  -- Step 4: ρ attains its maximum on S
  obtain ⟨v_star, hv_mem, hv_max⟩ := hS_compact.exists_isMaxOn hS_nonempty hρ_continuousOn
  -- v* has strictly positive entries (since v_i ≥ ε > 0)
  have hv_pos : ∀ i, 0 < v_star i := fun i =>
    lt_of_lt_of_le hε_pos (hv_mem.1 i)
  -- v* is on the simplex
  have hv_nn : ∀ i, 0 ≤ v_star i := fun i => le_of_lt (hv_pos i)
  have hv_sum : ∑ i, v_star i = 1 := hv_mem.2
  -- Set μ = ρ(v*)
  let μ := ρ v_star
  -- μ > 0 since (Bv*)_i > 0 and v*_i > 0
  have hBv_pos : ∀ i, 0 < B.mulVec v_star i :=
    fun i => lt_of_lt_of_le hc_pos (h_Bv_lb v_star hv_nn hv_sum i)
  have hμ_pos : 0 < μ := by
    rw [show μ = Finset.inf' Finset.univ huniv
      (fun i => B.mulVec v_star i / v_star i) from rfl, Finset.lt_inf'_iff]
    intro i _
    exact div_pos (hBv_pos i) (hv_pos i)
  -- Step 5: Bv* ≥ μ·v* componentwise (by definition of inf')
  have h_ge : ∀ i, μ * v_star i ≤ B.mulVec v_star i := by
    intro i
    have : μ ≤ B.mulVec v_star i / v_star i := Finset.inf'_le _ (Finset.mem_univ i)
    rwa [le_div_iff₀ (hv_pos i)] at this
  -- Step 6: Show Bv* = μ·v* by contradiction
  have h_eig : B.mulVec v_star = μ • v_star := by
    -- Suppose Bv* ≠ μ·v*. Then ∃ j with μ·v*_j < (Bv*)_j.
    by_contra h_ne
    have h_strict : ∃ j, μ * v_star j < B.mulVec v_star j := by
      by_contra h_all
      push Not at h_all
      exact h_ne (funext fun i => le_antisymm (h_all i)
        (by simp only [Pi.smul_apply, smul_eq_mul]; exact h_ge i))
    -- Define w = Bv* / ∑(Bv*) ∈ S
    have hBv_sum_pos : 0 < ∑ i, B.mulVec v_star i :=
      Finset.sum_pos (fun i _ => hBv_pos i) ⟨hn.some, Finset.mem_univ _⟩
    let w : n → ℝ := fun i => B.mulVec v_star i / ∑ k, B.mulVec v_star k
    have hw_mem : w ∈ S := h_psi_in_S v_star hv_nn hv_sum
    -- Show ρ(w) > μ, contradicting maximality
    -- Key calculation: (Bw)_i / w_i = (B·Bv*)_i / (Bv*)_i = ((B*B)v*)_i / (Bv*)_i
    -- By collatz_wielandt_strict: ∀ i, μ·(Bv*)_i < (B*B)v*_i
    have h_cw_strict := collatz_wielandt_strict hB h_ge h_strict
    -- Therefore: (Bw)_i / w_i = ((B*B)v*)_i / (Bv*)_i > μ for all i
    -- Hence ρ(w) = inf_i (Bw)_i / w_i > μ
    have : μ < ρ w := by
      change μ < Finset.inf' Finset.univ huniv (fun i => B.mulVec w i / w i)
      rw [Finset.lt_inf'_iff]
      intro i _
      -- (Bw)_i = ∑_j B_{ij} · w_j = ∑_j B_{ij} · (Bv*)_j / S = (1/S) · ∑_j B_{ij} · (Bv*)_j
      -- w_i = (Bv*)_i / S
      -- So (Bw)_i / w_i = (∑_j B_{ij} · (Bv*)_j) / (Bv*)_i = ((B*B)·v*)_i / (Bv*)_i
      change μ < B.mulVec w i / w i
      have hw_i_pos : 0 < w i := lt_of_lt_of_le hε_pos (hw_mem.1 i)
      rw [lt_div_iff₀ hw_i_pos]
      -- Need: μ · w_i < (Bw)_i
      -- We show: (Bw)_i / w_i = ((B*B)v*)_i / (Bv*)_i
      -- and use collatz_wielandt_strict to get μ < this ratio.
      -- Direct calculation: w = Bv*/S where S = ∑(Bv*)
      -- (Bw)_i = (1/S)·∑_j B_{ij}·(Bv*)_j = (1/S)·((B*B)v*)_i
      -- w_i = (Bv*)_i / S
      -- So μ·w_i < (Bw)_i ↔ μ·(Bv*)_i/S < ((B*B)v*)_i/S ↔ μ·(Bv*)_i < ((B*B)v*)_i
      let S_val := ∑ k, B.mulVec v_star k
      have hS_val_pos : 0 < S_val := hBv_sum_pos
      -- LHS: μ * w_i = μ * (Bv*_i / S)
      -- RHS: (Bw)_i = ∑_j B_{ij} * (Bv*_j / S) = (1/S) * ∑_j B_{ij} * (Bv*_j)
      -- So goal: μ * (Bv*_i / S) < (1/S) * ∑_j B_{ij} * Bv*_j
      -- ↔ μ * Bv*_i < ∑_j B_{ij} * Bv*_j  (multiply both sides by S > 0)
      -- ↔ μ * Bv*_i < ((B*B)v*)_i  which is h_cw_strict i
      -- w = (1/S) • B.mulVec v_star
      have h_w_smul : w = (S_val⁻¹) • B.mulVec v_star := by
        ext j; simp only [w, S_val, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
      -- Bw = (1/S) • B(Bv*) = (1/S) • (B²)v*
      have h_Bw : B.mulVec w = (S_val⁻¹) • (B * B).mulVec v_star := by
        rw [h_w_smul, mulVec_smul, mulVec_mulVec]
      -- So (Bw)_i / w_i = ((B²)v*)_i / (Bv*)_i
      rw [show B.mulVec w i = S_val⁻¹ * (B * B).mulVec v_star i from by
          rw [h_Bw]; simp [Pi.smul_apply, smul_eq_mul],
        show w i = S_val⁻¹ * B.mulVec v_star i from by
          rw [h_w_smul]; simp [Pi.smul_apply, smul_eq_mul]]
      -- Goal: μ * (S⁻¹ * (Bv*)_i) < S⁻¹ * ((B²)v*)_i
      -- Rewrite LHS: μ * (S⁻¹ * a) = S⁻¹ * (μ * a)
      rw [show μ * (S_val⁻¹ * B.mulVec v_star i) =
        S_val⁻¹ * (μ * B.mulVec v_star i) from by ring]
      exact mul_lt_mul_of_pos_left (h_cw_strict i) (inv_pos.mpr hS_val_pos)
    have h_le : ρ w ≤ ρ v_star := isMaxOn_iff.mp hv_max w hw_mem
    linarith
  exact ⟨μ, v_star, hμ_pos, hv_pos, h_eig⟩

/-- Perron–Frobenius (existence): an irreducible nonneg matrix has a positive
eigenvalue with a strictly positive eigenvector.

**Proof.** We use the Collatz–Wielandt minimax characterization.

1. From `exists_pos_power`, get k > 0 with B = A^k all entries positive.
2. Define ρ(v) = min_i (Bv)_i / v_i on the positive simplex.
3. For B with all entries positive, the map v ↦ Bv/‖Bv‖₁ maps the simplex
   into its interior, and ρ is well-defined and continuous.
4. On the compact set {v | v_i ≥ ε, ∑ v_i = 1}, ρ attains its maximum.
5. At the maximizer v*, all ratios are equal: Bv* = μv* with μ > 0.
6. Since A commutes with B = A^k, Av* is also an eigenvector of B with
   eigenvalue μ. By uniqueness of the Perron eigenvector of B (all-positive
   matrix), Av* = λv* for some λ, and λ > 0 follows from v* > 0. -/
theorem perron_frobenius {A : Matrix n n ℝ} (hA : A.IsIrreducible) :
    ∃ (lam₀ : ℝ) (v : n → ℝ),
      0 < lam₀ ∧
      (∀ i, 0 < v i) ∧
      A.mulVec v = lam₀ • v := by
  -- Handle the empty type (vacuously true)
  by_cases hn : IsEmpty n
  · exact ⟨1, fun i => (hn.false i).elim, one_pos,
      fun i => (hn.false i).elim, funext fun i => (hn.false i).elim⟩
  · rw [not_isEmpty_iff] at hn
    -- Get the primitive power: B = A^k with all entries positive
    obtain ⟨k, hk_pos, hk_all⟩ := hA.exists_pos_power
    -- Each row of A has a positive entry (from irreducibility)
    have hrows : ∀ i, ∃ j, 0 < A i j := hA.row_has_pos_entry
    have hA_nn := hA.1
    -- Key claim: B = A^k with all positive entries has a positive eigenvector.
    -- We prove this using the Collatz–Wielandt argument.
    suffices h : ∃ (μ : ℝ) (w : n → ℝ), 0 < μ ∧ (∀ i, 0 < w i) ∧
        (A ^ k).mulVec w = μ • w by
      -- Given an eigenvector of B = A^k, construct one for A.
      obtain ⟨μ, w, hμ_pos, hw_pos, hw_eig⟩ := h
      -- Aw is nonneg since A ≥ 0 and w > 0
      -- Moreover, Aw > 0 since each row of A has a positive entry
      have hAw_pos : ∀ i, 0 < A.mulVec w i :=
        Matrix.mulVec_pos_of_pos hA_nn hrows hw_pos
      -- Key: A commutes with A^k, so Aw is an eigenvector of A^k with eigenvalue μ.
      -- (A^k)(Aw) = A((A^k)w) = A(μw) = μ(Aw)
      have hAw_eig : (A ^ k).mulVec (A.mulVec w) = μ • (A.mulVec w) := by
        -- (A^k)(Aw) = (A^k · A)w = (A · A^k)w = A((A^k)w) = A(μw) = μ(Aw)
        have h1 : (A ^ k).mulVec (A.mulVec w) = (A ^ k * A).mulVec w := mulVec_mulVec ..
        have h2 : A ^ k * A = A * A ^ k := pow_mul_comm' A k
        have h3 : (A * A ^ k).mulVec w = A.mulVec ((A ^ k).mulVec w) := by
          rw [← mulVec_mulVec]
        rw [h1, h2, h3, hw_eig, mulVec_smul]
      -- The Perron eigenspace of B = A^k (for the eigenvalue μ) is one-dimensional
      -- for a matrix with all positive entries. This means Aw = c·w for some scalar c.
      -- We establish this via the uniqueness of positive eigenvectors for B.
      --
      -- Uniqueness argument: If Bx = μx and By = μy with x, y > 0, then x and y
      -- are proportional. Proof: Let t = min_i y_i/x_i. Then y - tx ≥ 0 with
      -- (y - tx)_{i₀} = 0 for some i₀. But B(y - tx) = μ(y - tx), so if y - tx ≥ 0
      -- and y - tx ≠ 0, then B(y-tx) > 0 (since B > 0), contradicting (y-tx)_{i₀} = 0.
      -- Hence y = tx.
      --
      -- Apply this with x = w and y = Aw (both positive eigenvectors of B with
      -- eigenvalue μ).
      -- Define c = (Aw)_{i₀} / w_{i₀} for arbitrary i₀
      have hAw_prop : ∃ c : ℝ, A.mulVec w = c • w := by
        -- Uniqueness of positive eigenvectors for all-positive B
        -- Let t = min_i (Aw)_i / w_i
        let ratios : n → ℝ := fun i => A.mulVec w i / w i
        let t : ℝ := Finset.inf' Finset.univ (Finset.univ_nonempty_iff.mpr hn) ratios
        have ht_pos : 0 < t := by
          rw [Finset.lt_inf'_iff]
          intro i _
          exact div_pos (hAw_pos i) (hw_pos i)
        -- y - tx ≥ 0 where y = Aw, x = w
        have h_diff_nn : ∀ i, 0 ≤ (A.mulVec w - t • w) i := by
          intro i
          simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
          have hi : t ≤ ratios i := Finset.inf'_le ratios (Finset.mem_univ i)
          rw [sub_nonneg]
          -- t ≤ (Aw)_i / w_i  implies  t * w_i ≤ (Aw)_i
          rwa [le_div_iff₀ (hw_pos i)] at hi
        -- B(y - tx) = μ(y - tx)
        have h_diff_eig : (A ^ k).mulVec (A.mulVec w - t • w) =
            μ • (A.mulVec w - t • w) := by
          rw [mulVec_sub, mulVec_smul, hAw_eig, hw_eig, smul_sub, smul_comm]
        -- If the difference is nonzero, B applied to it is strictly positive
        -- (since B has all positive entries), contradicting that the difference
        -- has a zero entry. So the difference must be zero.
        by_cases h_diff_zero : A.mulVec w - t • w = 0
        · exact ⟨t, sub_eq_zero.mp h_diff_zero⟩
        · -- There exists i₀ where the difference achieves its minimum = 0
          exfalso
          -- The difference is nonneg, not identically zero, so Bz > 0 where z = y - tx
          have h_diff_pos_some : ∃ j, 0 < (A.mulVec w - t • w) j := by
            by_contra h_all
            push Not at h_all
            apply h_diff_zero
            ext i
            exact le_antisymm (h_all i) (h_diff_nn i)
          -- Apply B to get strictly positive result
          have h_B_diff_pos := Matrix.mulVec_pos_of_allPos hk_all h_diff_nn h_diff_pos_some
          -- But μ > 0 and the difference achieves 0 somewhere (by definition of inf')
          have h_min_achieved : ∃ i₀, (A.mulVec w - t • w) i₀ = 0 := by
            -- t = inf' of ratios, so t is achieved at some index
            obtain ⟨i₀, _, hi₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty_iff.mpr hn)
              ratios
            exact ⟨i₀, by
              simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
              -- hi₀ : t = ratios i₀ = (A *ᵥ w) i₀ / w i₀
              have ht_eq : t = (A.mulVec w i₀) / (w i₀) := hi₀
              rw [ht_eq, div_mul_cancel₀ _ (ne_of_gt (hw_pos i₀)), sub_self]⟩
          obtain ⟨i₀, hi₀⟩ := h_min_achieved
          -- (B(y - tx))_{i₀} = μ · (y - tx)_{i₀} = μ · 0 = 0
          have : (A ^ k).mulVec (A.mulVec w - t • w) i₀ = 0 := by
            rw [h_diff_eig]; simp [hi₀]
          -- But B(y - tx) > 0 at i₀, contradiction
          linarith [h_B_diff_pos i₀]
      obtain ⟨c, hc⟩ := hAw_prop
      refine ⟨c, w, ?_, hw_pos, hc⟩
      -- c > 0 since (Aw)_{i₀} = c · w_{i₀} with (Aw)_{i₀} > 0 and w_{i₀} > 0
      have i₀ := Classical.choice hn
      have h1 := hAw_pos i₀
      rw [show A.mulVec w i₀ = (c • w) i₀ from congr_fun hc i₀] at h1
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      -- 0 < c * w i₀ and 0 < w i₀, so 0 < c
      by_contra hc_le
      push Not at hc_le
      have : c * w i₀ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc_le (le_of_lt (hw_pos i₀))
      linarith
    -- Now prove the key claim: B = A^k has a positive eigenvector.
    -- This uses the Collatz–Wielandt argument on the compact positive simplex.
    exact allpos_has_pos_eigenvec hn hk_all

end
