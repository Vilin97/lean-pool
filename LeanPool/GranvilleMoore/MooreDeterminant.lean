/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ken Ono
-/
module

public import LeanPool.GranvilleMoore.Ladder
public import LeanPool.GranvilleMoore.MasterExpansion
public import LeanPool.GranvilleMoore.VandermondeReduction

-- Adapted for Lean Pool: relocated imports and simplified supporting infrastructure.

/-!
# The Moore determinant

The two main theorems. `GranvilleMoore.Ladder` factors the Moore determinant as `p^C(d+1,3)` times
the determinant of the last rung `L_{d-1}` of the reduction ladder;
`GranvilleMoore.MasterExpansion` makes every entry of that rung an integer and pins it down modulo
`p`; and `GranvilleMoore.VandermondeReduction` evaluates the resulting determinant. Putting the
three together gives the exact power of `p` dividing the Moore determinant.

## Main results

* `GranvilleMoore.exists_intCast_det_ladderMatrix_last`: `det L_{d-1} ∈ ℤ` for `d ≤ p`.
* `GranvilleMoore.prod_factorial_mul_intCast_det_ladderMatrix_last`: for `d ≤ p - 1`,
  `(∏_i i!) det L_{d-1} ≡ (∏_j x_j) ∏_{i<j} (q_p(x_j) - q_p(x_i))` modulo `p`.
* `GranvilleMoore.prod_factorial_mul_intCast_det_ladderMatrix_last_of_eq`: the same identity
  at the boundary `d = p`, where the exceptional Fermat congruence is consumed.
* `GranvilleMoore.not_dvd_det_ladderMatrix_last_iff`: for `d ≤ p`, `p ∤ det L_{d-1}` exactly
  when the residues `q_p(x_j)` are pairwise distinct modulo `p`.
* `GranvilleMoore.det_mooreMatrix_eq_pow_mul`: the factorisation
  `GranvilleMoore.det_mooreMatrix_eq_pow_mul_det_ladderMatrix` as an identity in `ℤ`,
  `det M = p^C(d+1,3) * det L_{d-1}`.
* `GranvilleMoore.pow_dvd_det_mooreMatrix` (**`thm_lower_bound`**) and
  `GranvilleMoore.not_pow_succ_dvd_det_mooreMatrix_iff` (**`thm_main`**): the lower bound and
  the equality criterion.

## Implementation notes

Both main theorems are usually phrased as statements about `v_p(det M)`. They are stated here as
divisibilities in `ℤ` instead: `p^C(d+1,3) ∣ det M` for the bound, and `¬ p^{C(d+1,3)+1} ∣ det M`
for equality. The reason is the one recorded in the implementation notes of
`GranvilleMoore.CollapsedCoeff` and `GranvilleMoore.MasterExpansion`: `padicValRat p 0 = 0`, so a
valuation inequality says nothing at a vanishing argument and would silently hold for the wrong
reason. The divisibility form is unconditional, says exactly what `v_p ≥ C(d+1,3)` and
`v_p = C(d+1,3)` mean for a nonzero determinant, and is what the equality theorem needs anyway.

The standing hypotheses `d ≥ 1` and `det M ≠ 0` of the paper are kept, so that the two main
theorems read exactly as it states them, but in the divisibility form neither is needed; they are
named with a leading underscore to record that. Nothing is lost at `det M = 0`: there
`det L_{d-1} = 0`, so `p ∣ det L_{d-1}` and the equivalence of
`GranvilleMoore.not_pow_succ_dvd_det_mooreMatrix_iff` holds with both of its sides false.

The objects that are `ℚ`-valued by definition — `det L_{d-1}` and the Fermat quotients
`q_p(x_j)` — are handled by the house convention of `GranvilleMoore.UnitQuotient`: the
representing integers `D` and `q j` are taken as arguments together with the hypotheses
identifying them, so that no cast appears inside a proof. The congruences are stated as
equalities in `ZMod p` rather than as divisibilities in `ℤ`, because
`GranvilleMoore.det_of_eq_mul_pow` and `GranvilleMoore.det_of_eq_mul_pow_ne_zero_iff` are
about a matrix over a commutative ring and `ZMod p` is the ring in question; over an integral
domain the vanishing criterion is then immediate.

Rescaling row `r` of the reduced rung by `r!` is done in one stroke with
`Matrix.det_mul_column`, which — despite its name — scales rows; see the implementation notes
of `GranvilleMoore.VandermondeReduction`.

## References

* A. Granville, *The p-divisibility of the integer Moore determinant and iterated
  Fermat quotients*.
-/

public section

open Finset Matrix

namespace GranvilleMoore

variable {p d : ℕ}

/-! ### Integrality of the last ladder determinant -/

/-- The last rung of the ladder is the entrywise image of an integer matrix.

Every entry of `L (d-1)` is `F⁽ʳ⁾_0(x_j)` with `r ≤ d - 1 ≤ p - 1`
(`GranvilleMoore.ladderMatrix_last_apply`), hence an integer by
`GranvilleMoore.exists_intCast_iteratedFermatQuot`; choosing one witness per entry assembles
the integer matrix. -/
private theorem exists_intMatrix_ladderMatrix_last (hp : p.Prime) (hodd : Odd p) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) :
    ∃ N : Matrix (Fin d) (Fin d) ℤ,
      ladderMatrix p x (d - 1) = N.map (fun z : ℤ => (z : ℚ)) := by
  choose N hN using fun (r j : Fin d) =>
    exists_intCast_iteratedFermatQuot hp hodd (hx j)
      (show (r : ℕ) ≤ p - 1 by have := r.isLt; omega) 0
  refine ⟨Matrix.of N, ?_⟩
  ext r j
  rw [ladderMatrix_last_apply, Matrix.map_apply, Matrix.of_apply, hN r j]

/-- The determinant of the entrywise image of an integer matrix is the image of its
determinant. -/
private theorem det_eq_intCast_det {N : Matrix (Fin d) (Fin d) ℤ} {x : Fin d → ℤ}
    (hN : ladderMatrix p x (d - 1) = N.map (fun z : ℤ => (z : ℚ))) :
    (ladderMatrix p x (d - 1)).det = ((N.det : ℤ) : ℚ) := by
  rw [hN]
  exact (RingHom.map_det (Int.castRingHom ℚ) N).symm

/-- **Integrality of the last ladder determinant** (`lem_ladder_last_integral`): for an odd
prime `p`, `d ≤ p` and integers `x_j` prime to `p`, the determinant of the last rung of the
ladder is an integer.

Integrality is phrased as the existence of an integer whose cast is the value, matching
`GranvilleMoore.exists_intCast_iteratedFermatQuot`. Every entry of `L (d-1)` is an iterated
Fermat quotient of superscript at most `p - 1`, hence an integer, and a determinant is a
polynomial with integer coefficients in its entries. -/
theorem exists_intCast_det_ladderMatrix_last (hp : p.Prime) (hodd : Odd p) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) :
    ∃ D : ℤ, (ladderMatrix p x (d - 1)).det = (D : ℚ) := by
  obtain ⟨N, hN⟩ := exists_intMatrix_ladderMatrix_last hp hodd hdp hx
  exact ⟨N.det, det_eq_intCast_det hN⟩

/-- The integer matrix of `exists_intMatrix_ladderMatrix_last`, with its determinant
identified with a prescribed integer representative of `det L_{d-1}`. -/
private theorem exists_intMatrix_det_eq (hp : p.Prime) (hodd : Odd p) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {D : ℤ}
    (hD : (ladderMatrix p x (d - 1)).det = (D : ℚ)) :
    ∃ N : Matrix (Fin d) (Fin d) ℤ,
      ladderMatrix p x (d - 1) = N.map (fun z : ℤ => (z : ℚ)) ∧ N.det = D := by
  obtain ⟨N, hN⟩ := exists_intMatrix_ladderMatrix_last hp hodd hdp hx
  exact ⟨N, hN, by exact_mod_cast (det_eq_intCast_det hN).symm.trans hD⟩

/-! ### The entries of the last rung modulo `p` -/

/-- The generic entry of the rescaled last rung, modulo `p`: for a row index `r ≤ p - 2`,
`r! · N r j ≡ x_j q_p(x_j)^r`. This is `GranvilleMoore.dvd_factorial_mul_sub_mul_pow` read off the
entry `F⁽ʳ⁾_0(x_j)` of `L (d-1)`. -/
private theorem factorial_mul_intCast_eq (hp : p.Prime) (hodd : Odd p) {x : Fin d → ℤ}
    (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {N : Matrix (Fin d) (Fin d) ℤ}
    (hN : ladderMatrix p x (d - 1) = N.map (fun z : ℤ => (z : ℚ))) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) {r : Fin d} (hr : (r : ℕ) ≤ p - 2)
    (j : Fin d) :
    (((r : ℕ).factorial : ℕ) : ZMod p) * ((N r j : ℤ) : ZMod p)
      = ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (r : ℕ) := by
  have hz : iteratedFermatQuot p (r : ℕ) 0 (x j) = ((N r j : ℤ) : ℚ) := by
    rw [← ladderMatrix_last_apply p x r j, hN, Matrix.map_apply]
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (dvd_factorial_mul_sub_mul_pow hp hodd (hx j) hr 0 hz (hq j))
  push_cast at h0
  linear_combination h0

/-- The bottom entry of the rescaled last rung at `d = p`, modulo `p`: for the row index
`r = p - 1`, `(p-1)! · N r j ≡ x_j (q_p(x_j)^{p-1} - 1 · q_p(x_j)^1)`. This is
`GranvilleMoore.dvd_factorial_mul_sub_exceptional`, written so that the right-hand side is
literally the bottom row of `GranvilleMoore.det_of_eq_mul_pow_updateRow_sub` at `k = 1`. -/
private theorem factorial_mul_intCast_eq_exceptional (hp : p.Prime) (hodd : Odd p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {N : Matrix (Fin d) (Fin d) ℤ}
    (hN : ladderMatrix p x (d - 1) = N.map (fun z : ℤ => (z : ℚ))) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) {r : Fin d} (hr : (r : ℕ) = p - 1)
    (j : Fin d) :
    (((p - 1).factorial : ℕ) : ZMod p) * ((N r j : ℤ) : ZMod p)
      = ((x j : ℤ) : ZMod p) *
        (((q j : ℤ) : ZMod p) ^ (p - 1) - 1 * ((q j : ℤ) : ZMod p) ^ 1) := by
  have hz : iteratedFermatQuot p (p - 1) 0 (x j) = ((N r j : ℤ) : ℚ) := by
    rw [← hr, ← ladderMatrix_last_apply p x r j, hN, Matrix.map_apply]
  have h0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr
    (dvd_factorial_mul_sub_exceptional hp hodd (hx j) hz (hq j))
  push_cast at h0
  linear_combination h0

/-! ### The last rung is Vandermonde modulo `p` -/

/-- **The last ladder matrix is Vandermonde modulo `p`** (`lem_ladder_last_vandermonde`): for
an odd prime `p`, `1 ≤ d ≤ p - 1` and integers `x_j` prime to `p`,
```
(∏_i i!) det L_{d-1} ≡ (∏_j x_j) ∏_{i<j} (q_p(x_j) - q_p(x_i))  (mod p) .
```

The congruence is stated as an equality in `ZMod p` between the images of the integer
`D` representing `det L_{d-1}` and of the integers `q j` representing `q_p(x_j)`.

Since every row index `r` satisfies `r ≤ d - 1 ≤ p - 2`,
`GranvilleMoore.dvd_factorial_mul_sub_mul_pow` applies to every entry; scaling row `r` by `r!`
therefore turns the reduction of `L (d-1)` into the matrix with entries `x_j q_p(x_j)^r`, which is
the shape `GranvilleMoore.det_of_eq_mul_pow` evaluates. -/
theorem prod_factorial_mul_intCast_det_ladderMatrix_last (hp : p.Prime) (hodd : Odd p)
    (_hd : 1 ≤ d) (hdp : d ≤ p - 1) {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {D : ℤ}
    (hD : (ladderMatrix p x (d - 1)).det = (D : ℚ)) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) :
    (∏ i : Fin d, (((i : ℕ).factorial : ℕ) : ZMod p)) * ((D : ℤ) : ZMod p)
      = (∏ j, ((x j : ℤ) : ZMod p)) *
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (((q j : ℤ) : ZMod p) - ((q i : ℤ) : ZMod p)) := by
  have hp2 := hp.two_le
  obtain ⟨N, hN, hNd⟩ := exists_intMatrix_det_eq hp hodd (by omega) hx hD
  have hmap : ((D : ℤ) : ZMod p) = (N.map (fun z : ℤ => (z : ZMod p))).det := by
    rw [← hNd]
    exact RingHom.map_det (Int.castRingHom (ZMod p)) N
  rw [hmap, ← Matrix.det_mul_column (fun i : Fin d => (((i : ℕ).factorial : ℕ) : ZMod p))]
  refine det_of_eq_mul_pow (fun j => ((x j : ℤ) : ZMod p)) (fun j => ((q j : ℤ) : ZMod p)) _
    fun i j => ?_
  simp only [Matrix.of_apply, Matrix.map_apply]
  exact factorial_mul_intCast_eq hp hodd hx hN hq (by have := i.isLt; omega) j

/-- **The last ladder determinant at `d = p`** (`lem_ladder_last_vandermonde_eq_p`): the
conclusion of `GranvilleMoore.prod_factorial_mul_intCast_det_ladderMatrix_last` continues to
hold at the boundary `d = p`, with the same scaling factor `∏_i i!`.

This is where `GranvilleMoore.dvd_factorial_mul_sub_exceptional` is consumed. The rows `r ≤ p - 2`
behave as before, but the bottom row has `r = p - 1` and `k = 0`, the one pair at which the master
expansion has a second surviving term: there
`(p-1)! F⁽ᵖ⁻¹⁾_0(x_j) ≡ x_j q_p(x_j)^{p-1} - x_j q_p(x_j)`. So the rescaled matrix is the
Vandermonde shape with its bottom row replaced by the bottom row minus the row of index `1`, and
`GranvilleMoore.det_of_eq_mul_pow_updateRow_sub` says that this row operation changes nothing. A
weaker form allows an unspecified unit `ε` in place of `∏_i i!`; the sharp form of the exceptional
congruence makes `ε = ∏_i i!` exactly. -/
theorem prod_factorial_mul_intCast_det_ladderMatrix_last_of_eq (hp : p.Prime) (hodd : Odd p)
    (hdp : d = p) {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {D : ℤ}
    (hD : (ladderMatrix p x (d - 1)).det = (D : ℚ)) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) :
    (∏ i : Fin d, (((i : ℕ).factorial : ℕ) : ZMod p)) * ((D : ℤ) : ZMod p)
      = (∏ j, ((x j : ℤ) : ZMod p)) *
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (((q j : ℤ) : ZMod p) - ((q i : ℤ) : ZMod p)) := by
  have hp3 : 3 ≤ p := by
    have h2 := hp.two_le
    have : p % 2 = 1 := Nat.odd_iff.mp hodd
    omega
  obtain ⟨N, hN, hNd⟩ := exists_intMatrix_det_eq hp hodd (by omega) hx hD
  have hmap : ((D : ℤ) : ZMod p) = (N.map (fun z : ℤ => (z : ZMod p))).det := by
    rw [← hNd]
    exact RingHom.map_det (Int.castRingHom (ZMod p)) N
  obtain ⟨iL, hiL⟩ : ∃ i : Fin d, (i : ℕ) = p - 1 := ⟨⟨p - 1, by omega⟩, rfl⟩
  obtain ⟨i₁, hi₁⟩ : ∃ i : Fin d, (i : ℕ) = 1 := ⟨⟨1, by omega⟩, rfl⟩
  have hne : iL ≠ i₁ := fun h => by rw [h, hi₁] at hiL; omega
  have hclaim : (Matrix.of fun (i j : Fin d) =>
        (((i : ℕ).factorial : ℕ) : ZMod p) * (N.map (fun z : ℤ => (z : ZMod p))) i j)
      = (Matrix.of fun (i j : Fin d) =>
            ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (i : ℕ)).updateRow iL
          fun j => ((x j : ℤ) : ZMod p) *
            (((q j : ℤ) : ZMod p) ^ (iL : ℕ) - 1 * ((q j : ℤ) : ZMod p) ^ (i₁ : ℕ)) := by
    ext i j
    by_cases hi : i = iL
    · rw [hi, Matrix.updateRow_self]
      simp only [Matrix.of_apply, Matrix.map_apply]
      rw [hiL, hi₁]
      exact factorial_mul_intCast_eq_exceptional hp hodd hx hN hq hiL j
    · rw [Matrix.updateRow_ne hi]
      simp only [Matrix.of_apply, Matrix.map_apply]
      refine factorial_mul_intCast_eq hp hodd hx hN hq ?_ j
      have h1 := i.isLt
      have h2 : (i : ℕ) ≠ p - 1 := fun h => hi (Fin.val_injective (by rw [h, hiL]))
      omega
  rw [hmap, ← Matrix.det_mul_column (fun i : Fin d => (((i : ℕ).factorial : ℕ) : ZMod p)),
    hclaim]
  exact det_of_eq_mul_pow_updateRow_sub (fun j => ((x j : ℤ) : ZMod p))
    (fun j => ((q j : ℤ) : ZMod p)) _ hne 1 fun i j => rfl

/-! ### The last ladder determinant is a unit exactly when the quotients are distinct -/

/-- **The last ladder determinant is a unit exactly when the quotients are distinct**
(`lem_ladder_last_nonzero`): for an odd prime `p`, `1 ≤ d ≤ p` and integers `x_j` prime to
`p`, `p ∤ det L_{d-1}` if and only if the residues `q_p(x_1), …, q_p(x_d)` are pairwise
distinct modulo `p`.

Pairwise distinctness is phrased as injectivity of `j ↦ q_p(x_j)` in `ZMod p`.

Both scaling factors of the two preceding lemmas are units modulo `p`: each `i!` with
`i ≤ d - 1 ≤ p - 1` is prime to `p` by `Nat.Prime.dvd_factorial`, and each `x_j` is prime to
`p` by hypothesis. So the residue of `det L_{d-1}` is nonzero exactly when the Vandermonde
product is, and `GranvilleMoore.det_of_eq_mul_pow_ne_zero_iff` — over the field `ZMod p`,
which is a domain — turns that into injectivity. -/
theorem not_dvd_det_ladderMatrix_last_iff (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d)
    (hdp : d ≤ p) {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {D : ℤ}
    (hD : (ladderMatrix p x (d - 1)).det = (D : ℚ)) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) :
    ¬ (p : ℤ) ∣ D ↔ Function.Injective fun j => ((q j : ℤ) : ZMod p) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hc : ∀ j, ((x j : ℤ) : ZMod p) ≠ 0 := fun j => by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hx j
  have hfac : (∏ i : Fin d, (((i : ℕ).factorial : ℕ) : ZMod p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => by
      rw [Ne, ZMod.natCast_eq_zero_iff, hp.dvd_factorial]
      have := i.isLt
      omega
  have hkey : (∏ i : Fin d, (((i : ℕ).factorial : ℕ) : ZMod p)) * ((D : ℤ) : ZMod p)
      = (∏ j, ((x j : ℤ) : ZMod p)) *
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (((q j : ℤ) : ZMod p) - ((q i : ℤ) : ZMod p)) := by
    rcases eq_or_lt_of_le hdp with h | h
    · exact prod_factorial_mul_intCast_det_ladderMatrix_last_of_eq hp hodd h hx hD hq
    · exact prod_factorial_mul_intCast_det_ladderMatrix_last hp hodd hd (by omega) hx hD hq
  have hdetM : (Matrix.of fun (i j : Fin d) =>
        ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (i : ℕ)).det
      = (∏ j, ((x j : ℤ) : ZMod p)) *
        ∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (((q j : ℤ) : ZMod p) - ((q i : ℤ) : ZMod p)) :=
    det_of_eq_mul_pow (fun j => ((x j : ℤ) : ZMod p)) (fun j => ((q j : ℤ) : ZMod p))
      (Matrix.of fun (i j : Fin d) =>
        ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (i : ℕ)) fun i j => rfl
  have hM : ((Matrix.of fun (i j : Fin d) =>
        ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (i : ℕ)).det ≠ 0)
      ↔ ((D : ℤ) : ZMod p) ≠ 0 := by
    rw [hdetM, ← hkey]
    simp [hfac]
  have hinj := det_of_eq_mul_pow_ne_zero_iff (fun j => ((x j : ℤ) : ZMod p))
    (fun j => ((q j : ℤ) : ZMod p))
    (Matrix.of fun (i j : Fin d) =>
      ((x j : ℤ) : ZMod p) * ((q j : ℤ) : ZMod p) ^ (i : ℕ)) hc fun i j => rfl
  exact ((not_congr (ZMod.intCast_zmod_eq_zero_iff_dvd D p)).symm.trans hM.symm).trans hinj

/-! ### The exact power of `p` in the Moore determinant -/

/-- **Factoring the Moore determinant, in `ℤ`**: `det M = p^C(d+1,3) det L_{d-1}`, with
`det L_{d-1}` the integer `D` of `GranvilleMoore.exists_intCast_det_ladderMatrix_last`.

This is `GranvilleMoore.det_mooreMatrix_eq_pow_mul_det_ladderMatrix`, which lives in `ℚ`
because the ladder does, pushed back down to `ℤ` by injectivity of the cast. Both main
theorems read off this identity. -/
theorem det_mooreMatrix_eq_pow_mul (hp : p.Prime) {x : Fin d → ℤ} {D : ℤ}
    (hD : (ladderMatrix p x (d - 1)).det = (D : ℚ)) :
    (mooreMatrix p x).det = (p : ℤ) ^ Nat.choose (d + 1) 3 * D := by
  have h := det_mooreMatrix_eq_pow_mul_det_ladderMatrix hp.ne_zero x
  rw [hD] at h
  exact_mod_cast h

/-- **The lower bound** (`thm_lower_bound`): for an odd prime `p`, `1 ≤ d ≤ p` and integers
`x_j` prime to `p` with `det M_p(x) ≠ 0`, the power `p^C(d+1,3)` divides `det M_p(x)`.

This is usually stated as `v_p(det M) ≥ C(d+1,3)`; the divisibility is the same assertion for a
nonzero determinant and does not degenerate at `0`, see the implementation notes, which also
explain why `1 ≤ d` and `det M ≠ 0` are carried but unused.

`GranvilleMoore.det_mooreMatrix_eq_pow_mul` exhibits `det M` as `p^C(d+1,3)` times the
integer `D` of `GranvilleMoore.exists_intCast_det_ladderMatrix_last`, which is the
divisibility. -/
theorem pow_dvd_det_mooreMatrix (hp : p.Prime) (hodd : Odd p) (_hd : 1 ≤ d) (hdp : d ≤ p)
    {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) (_hdet : (mooreMatrix p x).det ≠ 0) :
    (p : ℤ) ^ Nat.choose (d + 1) 3 ∣ (mooreMatrix p x).det := by
  obtain ⟨D, hD⟩ := exists_intCast_det_ladderMatrix_last hp hodd hdp hx
  exact ⟨D, det_mooreMatrix_eq_pow_mul hp hD⟩

/-- **Equality in the Moore determinant bound** (`thm_main`): for an odd prime `p`,
`1 ≤ d ≤ p` and integers `x_j` prime to `p` with `det M_p(x) ≠ 0`, the exact power of `p`
dividing `det M_p(x)` is `C(d+1,3)` — that is, `p^{C(d+1,3)+1}` does *not* divide it — if and
only if the residues `q_p(x_1), …, q_p(x_d)` are pairwise distinct modulo `p`.

This is usually stated as `v_p(det M) = C(d+1,3)`; together with
`GranvilleMoore.pow_dvd_det_mooreMatrix` the failure of the next divisibility is the same
assertion, and it does not degenerate at `0`, see the implementation notes, which also explain why
`det M ≠ 0` is carried but unused. Pairwise distinctness of the residues is phrased as injectivity
of `j ↦ q_p(x_j)` in `ZMod p`, as in `GranvilleMoore.not_dvd_det_ladderMatrix_last_iff`.

By `GranvilleMoore.det_mooreMatrix_eq_pow_mul`, `det M = p^C(d+1,3) D`, so one further power
of `p` divides `det M` exactly when `p ∣ D`; the claim is therefore
`GranvilleMoore.not_dvd_det_ladderMatrix_last_iff`. The range is the paper's `d ≤ p`, the
boundary case `d = p` being covered by
`GranvilleMoore.prod_factorial_mul_intCast_det_ladderMatrix_last_of_eq`. -/
theorem not_pow_succ_dvd_det_mooreMatrix_iff (hp : p.Prime) (hodd : Odd p) (hd : 1 ≤ d)
    (hdp : d ≤ p) {x : Fin d → ℤ} (hx : ∀ j, ¬ (p : ℤ) ∣ x j) {q : Fin d → ℤ}
    (hq : ∀ j, fermatQuotient p (x j) = (q j : ℚ)) (_hdet : (mooreMatrix p x).det ≠ 0) :
    ¬ (p : ℤ) ^ (Nat.choose (d + 1) 3 + 1) ∣ (mooreMatrix p x).det
      ↔ Function.Injective fun j => ((q j : ℤ) : ZMod p) := by
  obtain ⟨D, hD⟩ := exists_intCast_det_ladderMatrix_last hp hodd hdp hx
  have hpz : ((p : ℤ)) ≠ 0 := Int.natCast_ne_zero.mpr hp.ne_zero
  rw [det_mooreMatrix_eq_pow_mul hp hD, pow_succ,
    mul_dvd_mul_iff_left (pow_ne_zero (Nat.choose (d + 1) 3) hpz)]
  exact not_dvd_det_ladderMatrix_last_iff hp hodd hd hdp hx hD hq

end GranvilleMoore
