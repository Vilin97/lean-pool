/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.FiniteRange.Pack
public import LeanPool.Sendov.FiniteRange.Recurrence

/-!
# Computing the recurrence by a single exponentiation

`Sendov.rev_qrow` says that `qrow` computes the coefficients of `(g₀ + g₁t + g₂t²) ^ k`.
Evaluating that identity at *integer* points turns it into a statement about packed values,
and the packing is nothing but the same Horner evaluation read in `ℤ` instead of `ℝ`.  So the
forward direction needs no new theory at all: `Sendov.pevZ_rowZ_qrow` follows from
`rev_qrow` by casting.

Two bases are involved:

* `β` packs a coefficient polynomial in `α` into one integer (`Sendov.pevZ`);
* `τ` packs the resulting row, a polynomial in `t`, into one integer.

Together they are the two-dimensional Kronecker substitution, and the whole recurrence
becomes `G ^ k` for the single integer `G = pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ²`.
`Sendov.unpackZ_pevZ` then reads the row back off, given the overflow bounds — which is where
the numerical parameters `β` and `τ` have to be chosen, one per degree.

## Main statements

* `Sendov.pev_intCast`, `Sendov.rev_intCast`: evaluation over `ℝ` at an integer point agrees
  with the packed evaluation over `ℤ`;
* `Sendov.pevZ_rowZ_qrow`: the recurrence as one integer exponentiation.
-/

public section

namespace Sendov

/-- The row with each coefficient polynomial packed at the base `β`. -/
@[expose]
def rowZ (r : List (List ℤ)) (β : ℤ) : List ℤ := r.map (fun p => pevZ p β)

@[simp] lemma rowZ_nil (β : ℤ) : rowZ [] β = [] := rfl

@[simp] lemma rowZ_cons (p : List ℤ) (r : List (List ℤ)) (β : ℤ) :
    rowZ (p :: r) β = pevZ p β :: rowZ r β := rfl

@[simp] lemma rowZ_length (r : List (List ℤ)) (β : ℤ) : (rowZ r β).length = r.length := by
  simp [rowZ]

/-- Evaluating a coefficient polynomial over `ℝ` at an integer point is the packed
evaluation over `ℤ`. -/
lemma pev_intCast (p : List ℤ) (b : ℤ) : pev p (b : ℝ) = (pevZ p b : ℝ) := by
  induction p with
  | nil => simp [pev]
  | cons a p ih =>
    simp only [pev, pevZ_cons, ih]
    push_cast
    ring

/-- Evaluating a row over `ℝ` at integer points is the packed evaluation over `ℤ`. -/
lemma rev_intCast (r : List (List ℤ)) (β τ : ℤ) :
    rev r (β : ℝ) (τ : ℝ) = (pevZ (rowZ r β) τ : ℝ) := by
  induction r with
  | nil => simp [rev]
  | cons p r ih =>
    simp only [rev_cons, rowZ_cons, pevZ_cons, ih, pev_intCast]
    push_cast
    ring

/-- **The recurrence as one exponentiation.**  The two-dimensionally packed row is the `k`-th
power of a single integer.  In the kernel this replaces `Θ(k³)` interpreted list steps by one
GMP-backed exponentiation; measured at `k = 46`, hours become about half a second. -/
theorem pevZ_rowZ_qrow (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) :
    pevZ (rowZ (qrow g₀ g₁ g₂ k) β) τ
      = (pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k := by
  have h := rev_qrow g₀ g₁ g₂ k (β : ℝ) (τ : ℝ)
  rw [rev_intCast, pev_intCast, pev_intCast, pev_intCast] at h
  exact_mod_cast h

/-- Reading the packed row back, given the overflow bound on the packed coefficients.  The
bound is a hypothesis: it is discharged per degree from explicit numerical parameters. -/
theorem rowZ_qrow_eq (g₀ g₁ g₂ : List ℤ) (k : ℕ) (β τ : ℤ) (hτ : 0 < τ)
    (hbound : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ) :
    unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)
      = rowZ (qrow g₀ g₁ g₂ k) β := by
  rw [← pevZ_rowZ_qrow, ← rowZ_length (qrow g₀ g₁ g₂ k) β]
  exact unpackZ_pevZ τ hτ _ hbound

/-! ### The moment as a single integer polynomial

`Sendov.irow` has rational weights `1/(j+4)`.  Scaling by a common multiple `L` of the
denominators clears them, turning the moment into one `ℤ`-polynomial in `α`. -/

/-- `∑ⱼ (L/(i+j+4)) • rⱼ`: the moment numerator, scaled by `L` to clear denominators. -/
@[expose]
def wsum (L : ℤ) : ℕ → List (List ℤ) → List ℤ
  | _, [] => []
  | i, p :: r => padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r)

@[simp] lemma wsum_nil (L : ℤ) (i : ℕ) : wsum L i [] = [] := rfl

@[simp] lemma wsum_cons (L : ℤ) (i : ℕ) (p : List ℤ) (r : List (List ℤ)) :
    wsum L i (p :: r)
      = padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r) := rfl

/-- **The scaled moment is an integer polynomial.**  Given that `L` clears every denominator
`i+j+4` occurring, `wsum` computes `L` times `Sendov.irow`. -/
theorem pev_wsum (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (α : ℝ),
    (∀ j, j < r.length → ((i : ℤ) + j + 4) ∣ L) →
    pev (wsum L i r) α = (L : ℝ) * irow r i α := by
  intro r
  induction r with
  | nil => intro i α _; simp [irow]
  | cons p r ih =>
    intro i α hdvd
    have h0 : ((i : ℤ) + 4) ∣ L := by
      have := hdvd 0 (by simp)
      simpa using this
    obtain ⟨m, hm⟩ := h0
    have hine : ((i : ℤ) + 4) ≠ 0 := by positivity
    have hw : L / ((i : ℤ) + 4) = m := by rw [hm, Int.mul_ediv_cancel_left _ hine]
    have hcast : ((m : ℤ) : ℝ) * ((i : ℝ) + 4) = (L : ℝ) := by
      rw [hm]; push_cast; ring
    have hi4 : ((i : ℝ) + 4) ≠ 0 := by positivity
    have hrest : ∀ j, j < r.length → (((i + 1 : ℕ) : ℤ) + j + 4) ∣ L := by
      intro j hj
      have := hdvd (j + 1) (by simpa using Nat.succ_lt_succ hj)
      push_cast at this ⊢
      convert this using 2
      ring
    rw [wsum_cons, pev_padd, pev_map_mul, hw, ih (i + 1) α hrest]
    simp only [irow]
    field_simp
    linear_combination (pev p α) * hcast

/-! ### Coefficient bounds

Injectivity of packing needs a bound on the coefficients of *both* lists compared — including
the true row, which is precisely the object we must not compute.  So the bound has to be
proved rather than checked.  The `L¹` norm does it: it is submultiplicative, so a coefficient
of the `k`-th power is at most `(l1 g₀ + l1 g₁ + l1 g₂) ^ k`. -/

/-- Sum of absolute values of the coefficients. -/
@[expose]
def l1 : List ℤ → ℤ
  | [] => 0
  | a :: p => |a| + l1 p

@[simp] lemma l1_nil : l1 [] = 0 := rfl

@[simp] lemma l1_cons (a : ℤ) (p : List ℤ) : l1 (a :: p) = |a| + l1 p := rfl

lemma l1_nonneg (p : List ℤ) : 0 ≤ l1 p := by
  induction p with
  | nil => simp
  | cons a p ih => have := abs_nonneg a; simp only [l1_cons]; omega

lemma abs_le_l1 : ∀ (p : List ℤ) (a : ℤ), a ∈ p → |a| ≤ l1 p := by
  intro p
  induction p with
  | nil => intro a ha; cases ha
  | cons c p ih =>
    intro a ha
    rcases List.mem_cons.1 ha with h | h
    · subst h; have := l1_nonneg p; simp only [l1_cons]; omega
    · have := ih a h; have := abs_nonneg c; simp only [l1_cons]; omega

lemma l1_padd (p q : List ℤ) : l1 (padd p q) ≤ l1 p + l1 q := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q =>
      have h1 := ih q
      have h2 := abs_add_le a b
      simp only [padd, l1_cons]
      omega

lemma l1_map_mul (c : ℤ) (q : List ℤ) : l1 (q.map (fun x => c * x)) = |c| * l1 q := by
  induction q with
  | nil => simp
  | cons b q ih =>
    simp only [List.map_cons, l1_cons, ih, abs_mul]
    ring

lemma l1_pmul (p q : List ℤ) : l1 (pmul p q) ≤ l1 p * l1 q := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    have hstep : l1 (padd (q.map (fun c => a * c)) (0 :: pmul p q))
        ≤ |a| * l1 q + l1 (pmul p q) := by
      have := l1_padd (q.map (fun c => a * c)) (0 :: pmul p q)
      rw [l1_map_mul] at this
      simpa using this
    have hq := l1_nonneg q
    simp only [pmul, l1_cons]
    nlinarith [ih, hq, hstep]

/-- The `L¹` norm of a row: the total of its coefficients' absolute values. -/
@[expose]
def l1row : List (List ℤ) → ℤ
  | [] => 0
  | p :: r => l1 p + l1row r

@[simp] lemma l1row_nil : l1row [] = 0 := rfl

@[simp] lemma l1row_cons (p : List ℤ) (r : List (List ℤ)) :
    l1row (p :: r) = l1 p + l1row r := rfl

lemma l1row_nonneg (r : List (List ℤ)) : 0 ≤ l1row r := by
  induction r with
  | nil => simp
  | cons p r ih => have := l1_nonneg p; simp only [l1row_cons]; omega

lemma l1row_radd (r s : List (List ℤ)) : l1row (radd r s) ≤ l1row r + l1row s := by
  induction r generalizing s with
  | nil => simp [radd]
  | cons p r ih =>
    cases s with
    | nil => simp [radd]
    | cons q s =>
      have h1 := ih s
      have h2 := l1_padd p q
      simp only [radd, l1row_cons]
      omega

lemma l1row_rscale (g : List ℤ) (r : List (List ℤ)) :
    l1row (rscale g r) ≤ l1 g * l1row r := by
  induction r with
  | nil => simp [rscale]
  | cons p r ih =>
    have := l1_pmul g p
    simp only [rscale, List.map_cons, l1row_cons] at *
    nlinarith [ih, l1_nonneg g, l1row_nonneg r]

lemma l1row_qstep (g₀ g₁ g₂ : List ℤ) (r : List (List ℤ)) :
    l1row (qstep g₀ g₁ g₂ r) ≤ (l1 g₀ + l1 g₁ + l1 g₂) * l1row r := by
  have h0 := l1row_rscale g₀ r
  have h1 := l1row_rscale g₁ r
  have h2 := l1row_rscale g₂ r
  have e1 := l1row_radd (rscale g₀ r) (radd ([] :: rscale g₁ r) ([] :: [] :: rscale g₂ r))
  have e2 := l1row_radd ([] :: rscale g₁ r) ([] :: [] :: rscale g₂ r)
  simp only [qstep, l1row_cons, l1_nil] at *
  nlinarith [e1, e2, h0, h1, h2]

/-- The coefficients of the `k`-th power are bounded by the `k`-th power of the `L¹` norm.
This is the bound that the packing base must exceed. -/
theorem l1row_qrow (g₀ g₁ g₂ : List ℤ) (k : ℕ) :
    l1row (qrow g₀ g₁ g₂ k) ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k := by
  induction k with
  | zero => simp [qrow]
  | succ k ih =>
    have hg : 0 ≤ l1 g₀ + l1 g₁ + l1 g₂ := by
      have := l1_nonneg g₀; have := l1_nonneg g₁; have := l1_nonneg g₂; omega
    calc l1row (qrow g₀ g₁ g₂ (k + 1))
        ≤ (l1 g₀ + l1 g₁ + l1 g₂) * l1row (qrow g₀ g₁ g₂ k) := l1row_qstep _ _ _ _
      _ ≤ (l1 g₀ + l1 g₁ + l1 g₂) * (l1 g₀ + l1 g₁ + l1 g₂) ^ k := by
          exact mul_le_mul_of_nonneg_left ih hg
      _ = (l1 g₀ + l1 g₁ + l1 g₂) ^ (k + 1) := by ring

/-! ### Lengths, and the magnitude of a packed value -/

lemma padd_length (p q : List ℤ) : (padd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons c q => simp [padd, ih]

lemma radd_length (r s : List (List ℤ)) :
    (radd r s).length = max r.length s.length := by
  induction r generalizing s with
  | nil => simp [radd]
  | cons p r ih =>
    cases s with
    | nil => simp [radd]
    | cons q s => simp [radd, ih]

@[simp] lemma rscale_length (g : List ℤ) (r : List (List ℤ)) :
    (rscale g r).length = r.length := by
  simp [rscale]

/-- The row of the `k`-th power has `2k+1` entries, whatever the multiplier. -/
@[simp] lemma qrow_length (g₀ g₁ g₂ : List ℤ) (k : ℕ) :
    (qrow g₀ g₁ g₂ k).length = 2 * k + 1 := by
  induction k with
  | zero => simp [qrow]
  | succ k ih =>
    simp only [qrow, qstep, radd_length, rscale_length, List.length_cons, ih]
    omega

/-- A packed value is bounded by the `L¹` norm times a power of the base. -/
lemma abs_pevZ_le (b : ℤ) (hb : 1 ≤ b) :
    ∀ p : List ℤ, |pevZ p b| ≤ l1 p * b ^ p.length := by
  intro p
  induction p with
  | nil => simp
  | cons a p ih =>
    have hb0 : (0 : ℤ) < b := by omega
    have hpow : (1 : ℤ) ≤ b ^ p.length := one_le_pow₀ hb
    have hl1 := l1_nonneg p
    have habs := abs_nonneg a
    calc |pevZ (a :: p) b| = |a + b * pevZ p b| := rfl
      _ ≤ |a| + |b * pevZ p b| := abs_add_le _ _
      _ = |a| + b * |pevZ p b| := by rw [abs_mul, abs_of_pos hb0]
      _ ≤ |a| + b * (l1 p * b ^ p.length) := by nlinarith [ih]
      _ ≤ (|a| + l1 p) * b ^ (p.length + 1) := by
            have hbb : (1 : ℤ) ≤ b * b ^ p.length := by nlinarith [hpow, hb0]
            have hkey := mul_le_mul_of_nonneg_left hbb habs
            ring_nf
            nlinarith [hkey, hpow, hl1, hb0]
      _ = l1 (a :: p) * b ^ (a :: p).length := by simp [l1_cons]

/-! ### The verification step

The generator supplies the moment numerator; Lean checks it with one integer comparison.
Lengths need not match exactly: a shorter list is compared against its zero-padding, which
has the same value as a polynomial. -/

/-- Evaluation ignores trailing zeros. -/
lemma pev_append_zeros (p : List ℤ) (j : ℕ) (α : ℝ) :
    pev (p ++ List.replicate j 0) α = pev p α := by
  induction p with
  | nil =>
    induction j with
    | zero => simp [pev]
    | succ j ih => simp only [List.replicate_succ, List.nil_append, pev] at *; simp [ih]
  | cons a p ih => simp only [List.cons_append, pev, ih]

/-- The round trip, tolerating extra room: unpacking to length `m ≥ p.length` returns `p`
zero-padded. -/
theorem unpackZ_pevZ_le (β : ℤ) (hβ : 0 < β) :
    ∀ (m : ℕ) (p : List ℤ), p.length ≤ m → (∀ a ∈ p, 2 * |a| < β) →
      unpackZ β m (pevZ p β) = p ++ List.replicate (m - p.length) 0 := by
  intro m
  induction m with
  | zero =>
    intro p hlen _
    simp [List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)]
  | succ m ih =>
    intro p hlen hb
    cases p with
    | nil =>
      have h0 : bdig β 0 = 0 := by
        have : (0 : ℤ) % β = 0 := Int.zero_emod β
        simp only [bdig, this]
        split_ifs <;> omega
      simp only [pevZ_nil, unpackZ_succ, h0, List.nil_append, List.length_nil,
        Nat.sub_zero, List.replicate_succ]
      have := ih [] (Nat.zero_le m) (by simp)
      simpa using this
    | cons a p =>
      have ha : 2 * |a| < β := hb a (List.mem_cons_self ..)
      have hp : ∀ x ∈ p, 2 * |x| < β := fun x hx => hb x (List.mem_cons_of_mem _ hx)
      have hd : bdig β (a + β * pevZ p β) = a := bdig_add_mul β a _ hβ ha
      have hq : (a + β * pevZ p β - a) / β = pevZ p β := by
        rw [add_sub_cancel_left, Int.mul_ediv_cancel_left _ hβ.ne']
      simp only [pevZ_cons, unpackZ_succ, hd, hq, List.length_cons]
      rw [ih p (by simpa using Nat.le_of_succ_le_succ hlen) hp]
      simp

/-- The weighted sum computed directly on the α-packed row. -/
@[expose]
def wsumZ (L : ℤ) : ℕ → List ℤ → ℤ
  | _, [] => 0
  | i, a :: s => (L / ((i : ℤ) + 4)) * a + wsumZ L (i + 1) s

@[simp] lemma wsumZ_nil (L : ℤ) (i : ℕ) : wsumZ L i [] = 0 := rfl

@[simp] lemma wsumZ_cons (L : ℤ) (i : ℕ) (a : ℤ) (s : List ℤ) :
    wsumZ L i (a :: s) = (L / ((i : ℤ) + 4)) * a + wsumZ L (i + 1) s := rfl

lemma pevZ_padd (p q : List ℤ) (b : ℤ) : pevZ (padd p q) b = pevZ p b + pevZ q b := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons c q => simp only [padd, pevZ_cons, ih]; ring

lemma pevZ_map_mul (c : ℤ) (q : List ℤ) (b : ℤ) :
    pevZ (q.map (fun x => c * x)) b = c * pevZ q b := by
  induction q with
  | nil => simp
  | cons x q ih => simp only [List.map_cons, pevZ_cons, ih]; ring

/-- The packed weighted sum agrees with packing the weighted sum: this is what makes the
check a single integer comparison. -/
lemma pevZ_wsum (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ) (β : ℤ),
    pevZ (wsum L i r) β = wsumZ L i (rowZ r β) := by
  intro r
  induction r with
  | nil => intro i β; simp
  | cons p r ih =>
    intro i β
    simp only [wsum_cons, pevZ_padd, pevZ_map_mul, rowZ_cons, wsumZ_cons, ih]

/-- Packing is injective on lists of the same length with coefficients below `β/2`. -/
lemma pevZ_inj (β : ℤ) (hβ : 0 < β) (p q : List ℤ)
    (hp : ∀ a ∈ p, 2 * |a| < β) (hq : ∀ a ∈ q, 2 * |a| < β)
    (hlen : p.length = q.length) (h : pevZ p β = pevZ q β) : p = q := by
  have h1 := unpackZ_pevZ β hβ p hp
  have h2 := unpackZ_pevZ β hβ q hq
  rw [← h1, ← h2, hlen, h]

/-- **Verification of a supplied moment numerator.**  Given the overflow bounds, checking a
generator-supplied `Nmom` is one integer comparison against the packed computation — which is
a single exponentiation and `2k+1` digit extractions. -/
theorem wsum_eq_of_packed (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hβ : 0 < β) (hτ : 0 < τ)
    (hbτ : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ)
    (hbN : ∀ a ∈ Nmom, 2 * |a| < β)
    (hbW : ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β)
    (hlen : Nmom.length = (wsum L 0 (qrow g₀ g₁ g₂ k)).length)
    (hcheck : wsumZ L 0 (unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)) = pevZ Nmom β) :
    Nmom = wsum L 0 (qrow g₀ g₁ g₂ k) := by
  rw [rowZ_qrow_eq g₀ g₁ g₂ k β τ hτ hbτ, ← pevZ_wsum] at hcheck
  exact pevZ_inj β hβ _ _ hbN hbW hlen hcheck.symm

/-! ### Entry lengths

`qrow_length` counts the entries of a row; bounding the α-packed values also needs each
entry's *length*.  Multiplying by a `g` of length at most `G` lengthens an entry by at most
`G`, so after `k` steps an entry has length at most `1 + G*k`.  This is what lets the
hypotheses of `wsum_eq_of_packed` be discharged by arithmetic instead of by computing
`qrow`. -/

lemma pmul_length_le (p q : List ℤ) : (pmul p q).length ≤ p.length + q.length := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    simp only [pmul, padd_length, List.length_map, List.length_cons]
    omega

lemma mem_radd_length_le {m : ℕ} : ∀ (r s : List (List ℤ)),
    (∀ p ∈ r, p.length ≤ m) → (∀ q ∈ s, q.length ≤ m) →
    ∀ x ∈ radd r s, x.length ≤ m := by
  intro r
  induction r with
  | nil => intro s _ hs x hx; exact hs x (by simpa [radd] using hx)
  | cons p r ih =>
    intro s hr hs x hx
    cases s with
    | nil => exact hr x (by simpa [radd] using hx)
    | cons q s =>
      rcases List.mem_cons.1 (by simpa [radd] using hx) with h | h
      · subst h
        have := hr p (List.mem_cons_self ..)
        have := hs q (List.mem_cons_self ..)
        rw [padd_length]
        omega
      · exact ih s (fun y hy => hr y (List.mem_cons_of_mem _ hy))
          (fun y hy => hs y (List.mem_cons_of_mem _ hy)) x h

lemma mem_rscale_length_le {m : ℕ} (g : List ℤ) (r : List (List ℤ))
    (hr : ∀ p ∈ r, p.length ≤ m) : ∀ x ∈ rscale g r, x.length ≤ g.length + m := by
  intro x hx
  simp only [rscale, List.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have := pmul_length_le g p
  have := hr p hp
  omega

/-- Each entry of the `k`-th row has length at most `1 + G*k`, where `G` bounds the lengths
of the multipliers. -/
theorem qrow_entry_length_le (g₀ g₁ g₂ : List ℤ) (G : ℕ)
    (h0 : g₀.length ≤ G) (h1 : g₁.length ≤ G) (h2 : g₂.length ≤ G) :
    ∀ (k : ℕ), ∀ p ∈ qrow g₀ g₁ g₂ k, p.length ≤ 1 + G * k := by
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [qrow, List.mem_singleton] at hp
    subst hp
    simp
  | succ k ih =>
    intro p hp
    have hGk : G * (k + 1) = G * k + G := by ring
    have hb : ∀ q ∈ qrow g₀ g₁ g₂ k, q.length ≤ 1 + G * k := ih
    have e0 : ∀ x ∈ rscale g₀ (qrow g₀ g₁ g₂ k), x.length ≤ 1 + G * (k + 1) := by
      intro x hx; have := mem_rscale_length_le g₀ _ hb x hx; omega
    have e1 : ∀ x ∈ ([] : List ℤ) :: rscale g₁ (qrow g₀ g₁ g₂ k),
        x.length ≤ 1 + G * (k + 1) := by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; simp
      · have := mem_rscale_length_le g₁ _ hb x h; omega
    have e2 : ∀ x ∈ ([] : List ℤ) :: ([] : List ℤ) :: rscale g₂ (qrow g₀ g₁ g₂ k),
        x.length ≤ 1 + G * (k + 1) := by
      intro x hx
      rcases List.mem_cons.1 hx with h | h
      · subst h; simp
      rcases List.mem_cons.1 h with h' | h'
      · subst h'; simp
      · have := mem_rscale_length_le g₂ _ hb x h'; omega
    exact mem_radd_length_le _ _ e0 (mem_radd_length_le _ _ e1 e2) p hp

/-- `l1` of an entry is at most `l1row` of the row. -/
lemma l1_le_l1row : ∀ (r : List (List ℤ)) (p : List ℤ), p ∈ r → l1 p ≤ l1row r := by
  intro r
  induction r with
  | nil => intro p hp; cases hp
  | cons q r ih =>
    intro p hp
    rcases List.mem_cons.1 hp with h | h
    · subst h; have := l1row_nonneg r; simp only [l1row_cons]; omega
    · have := ih p h; have := l1_nonneg q; simp only [l1row_cons]; omega

/-- The weighted sum is no longer than the entries it combines. -/
lemma wsum_length_le {m : ℕ} (L : ℤ) : ∀ (r : List (List ℤ)) (i : ℕ),
    (∀ p ∈ r, p.length ≤ m) → (wsum L i r).length ≤ m := by
  intro r
  induction r with
  | nil => intro i _; simp
  | cons p r ih =>
    intro i hr
    have hp := hr p (List.mem_cons_self ..)
    have := ih (i + 1) (fun q hq => hr q (List.mem_cons_of_mem _ hq))
    simp only [wsum_cons, padd_length, List.length_map]
    omega

/-- The weighted sum's `L¹` norm is at most `L` times the row's. -/
lemma l1_wsum_le (L : ℤ) (hL : 0 ≤ L) : ∀ (r : List (List ℤ)) (i : ℕ),
    l1 (wsum L i r) ≤ L * l1row r := by
  intro r
  induction r with
  | nil => intro i; simp
  | cons p r ih =>
    intro i
    have hd : (0 : ℤ) < (i : ℤ) + 4 := by positivity
    have hw0 : 0 ≤ L / ((i : ℤ) + 4) := Int.ediv_nonneg hL hd.le
    have hw1 : L / ((i : ℤ) + 4) ≤ L := Int.ediv_le_self _ hL
    have h1 := l1_padd (p.map (fun c => (L / ((i : ℤ) + 4)) * c)) (wsum L (i + 1) r)
    rw [l1_map_mul, abs_of_nonneg hw0] at h1
    have h2 := ih (i + 1)
    have hp := l1_nonneg p
    have hr := l1row_nonneg r
    simp only [wsum_cons, l1row_cons]
    nlinarith [h1, h2, hw0, hw1, hp, hr]

/-! ### The bounds in usable form

Each hypothesis of `Sendov.wsum_eq_of_packed` reduces to an inequality between explicit
numbers, so a degree file never computes `qrow`. -/

/-- The `τ` bound: the α-packed row entries are bounded by the `L¹` norm times a power of
`β`, the exponent coming from `Sendov.qrow_entry_length_le`. -/
theorem rowZ_bound (g₀ g₁ g₂ : List ℤ) (k G : ℕ) (β τ : ℤ) (hβ : 1 ≤ β)
    (h0 : g₀.length ≤ G) (h1 : g₁.length ≤ G) (h2 : g₂.length ≤ G)
    (hτ : 2 * ((l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k)) < τ) :
    ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ := by
  intro a ha
  simp only [rowZ, List.mem_map] at ha
  obtain ⟨p, hp, rfl⟩ := ha
  have hlen : p.length ≤ 1 + G * k := qrow_entry_length_le g₀ g₁ g₂ G h0 h1 h2 k p hp
  have hl1p : l1 p ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k :=
    le_trans (l1_le_l1row _ p hp) (l1row_qrow g₀ g₁ g₂ k)
  have hpow : β ^ p.length ≤ β ^ (1 + G * k) := pow_le_pow_right₀ hβ hlen
  have hbpos : (0 : ℤ) < β ^ p.length := by positivity
  have habs := abs_pevZ_le β hβ p
  have hl1nn := l1_nonneg p
  have : |pevZ p β| ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k) := by
    calc |pevZ p β| ≤ l1 p * β ^ p.length := habs
      _ ≤ (l1 g₀ + l1 g₁ + l1 g₂) ^ k * β ^ (1 + G * k) := by
          apply mul_le_mul hl1p hpow hbpos.le
          exact le_trans hl1nn hl1p
  omega

/-- The `β` bound for the moment numerator. -/
theorem wsum_bound (g₀ g₁ g₂ : List ℤ) (k : ℕ) (L β : ℤ) (hL : 0 ≤ L)
    (hβ : 2 * (L * (l1 g₀ + l1 g₁ + l1 g₂) ^ k) < β) :
    ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β := by
  intro a ha
  have h1 : |a| ≤ l1 (wsum L 0 (qrow g₀ g₁ g₂ k)) := abs_le_l1 _ a ha
  have h2 := l1_wsum_le L hL (qrow g₀ g₁ g₂ k) 0
  have h3 : L * l1row (qrow g₀ g₁ g₂ k) ≤ L * (l1 g₀ + l1 g₁ + l1 g₂) ^ k :=
    mul_le_mul_of_nonneg_left (l1row_qrow g₀ g₁ g₂ k) hL
  omega

/-- **Pad-tolerant verification.**  Concludes equality of the polynomial *functions*, which
is all the moment needs, and so requires only length *bounds* rather than an exact match. -/
theorem pev_wsum_eq_of_packed (g₀ g₁ g₂ : List ℤ) (k m : ℕ) (L β τ : ℤ) (Nmom : List ℤ)
    (hβ : 0 < β) (hτ : 0 < τ)
    (hbτ : ∀ a ∈ rowZ (qrow g₀ g₁ g₂ k) β, 2 * |a| < τ)
    (hbN : ∀ a ∈ Nmom, 2 * |a| < β)
    (hbW : ∀ a ∈ wsum L 0 (qrow g₀ g₁ g₂ k), 2 * |a| < β)
    (hlenN : Nmom.length ≤ m)
    (hlenW : (wsum L 0 (qrow g₀ g₁ g₂ k)).length ≤ m)
    (hcheck : wsumZ L 0 (unpackZ τ (qrow g₀ g₁ g₂ k).length
        ((pevZ g₀ β + pevZ g₁ β * τ + pevZ g₂ β * τ ^ 2) ^ k)) = pevZ Nmom β)
    (α : ℝ) :
    pev Nmom α = pev (wsum L 0 (qrow g₀ g₁ g₂ k)) α := by
  rw [rowZ_qrow_eq g₀ g₁ g₂ k β τ hτ hbτ, ← pevZ_wsum] at hcheck
  have hN := unpackZ_pevZ_le β hβ m Nmom hlenN hbN
  have hW := unpackZ_pevZ_le β hβ m _ hlenW hbW
  rw [hcheck, hN] at hW
  have := congrArg (fun l => pev l α) hW
  simpa [pev_append_zeros] using this

/-- **The moment from a verified numerator.**  Combining `Sendov.integral_moment_of` with
`Sendov.pev_wsum`, the integral is an explicit integer polynomial over an explicit
denominator.  Everything on the right is either supplied by the generator or a kernel
computation on integers. -/
theorem integral_moment_packed (n k : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (L : ℤ) (hL : 0 < L) (Nmom : List ℤ)
    (hdvd : ∀ j, j < 2 * k + 1 → ((0 : ℕ) + j + 4 : ℤ) ∣ L)
    (hNmom : pev Nmom α = pev (wsum L 0 (qrow (gg0 n) (gg1 n) (gg2 n) k)) α) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * Q n α t ^ k)
      = pev Nmom α / ((L : ℝ) * (2 * M n * (3 + α)) ^ k) := by
  have hM : 0 < M n := M_pos hn
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hD : (0 : ℝ) < 2 * M n * (3 + α) := by positivity
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hdvd' : ∀ j, j < (qrow (gg0 n) (gg1 n) (gg2 n) k).length →
      ((0 : ℕ) + j + 4 : ℤ) ∣ L := by
    intro j hj
    rw [qrow_length] at hj
    exact hdvd j hj
  have hw := pev_wsum L (qrow (gg0 n) (gg1 n) (gg2 n) k) 0 α hdvd'
  rw [integral_moment_of n k hn α hα, hNmom, hw]
  field_simp

/-- Every coefficient of every entry of a row is bounded by the row's `L¹` norm. -/
lemma abs_le_l1row : ∀ (r : List (List ℤ)) (p : List ℤ), p ∈ r → ∀ a ∈ p, |a| ≤ l1row r := by
  intro r
  induction r with
  | nil => intro p hp; cases hp
  | cons q r ih =>
    intro p hp a ha
    rcases List.mem_cons.1 hp with h | h
    · subst h
      have := abs_le_l1 p a ha
      have := l1row_nonneg r
      simp only [l1row_cons]
      omega
    · have := ih p h a ha
      have := l1_nonneg q
      simp only [l1row_cons]
      omega

end Sendov
