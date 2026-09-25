/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.EuclideanJordan.EuclideanJordan.TraceForm
public import LeanPool.EuclideanJordan.EuclideanJordan.Order



/-!
# Koecher / Alfsen–Shultz: a unital linear order isomorphism is a Jordan automorphism

On a finite-dimensional formally real Jordan algebra, a linear bijection `Φ` that fixes the unit
and preserves the cone of sums of squares **in both directions** preserves the Jordan product.

This is the classical theorem — Koecher; Alfsen–Shultz, *Geometry of State Spaces*, Thm 2.80.  It is
**not** van Imhoff–Roelands' JB-generality version (arXiv:1904.09278), which concludes linearity
rather than assuming it.  Here `Φ : J ≃ₗ[ℝ] J` is linear **by type**, and that is the whole
difference.

## The route

Jordan-multiplicativity reduces to preservation of squares, and squares to preservation of
idempotents, provided idempotents can be recognised *order-theoretically*.  They can:

* `c` is idempotent **iff** `c` is **sharp** — `0 ≤ c ≤ e` and no nonzero element of the cone lies
  below both `c` and `e − c` (`isSharp_iff_idem`).

Sharpness is visibly transported by `Φ`, since every clause is a statement about the cone and the
unit; so `Φ` maps idempotents to idempotents.  A complete orthogonal family `∑ qᵢ = e` goes to a
family with `∑ Φqᵢ = e`, and orthogonality is then *recovered* rather than transported
(`orth_of_sum_eq_unit`).  Finally `x = ∑ λᵢ qᵢ ⟹ x ∘ x = ∑ λᵢ² qᵢ` gives `Φ(x ∘ x) = Φx ∘ Φx`, and
polarisation finishes it.

★ **The reflecting half of the order hypothesis is load-bearing.**  `horder` is a *biconditional*.
A one-directional `IsSoS x → IsSoS (Φ x)` would not do: the sharpness clause is a `∀` over the cone,
and transporting it along `Φ.symm` needs the converse.  This is checked, not assumed — see
`map_idem_of_orderIso`, where `(horder _).mpr` appears three times.

## What the argument runs on

Two facts about the cone, both of which need an **associative positive definite form**:

* a sum of squares has nonnegative spectral coefficients (`nonneg_coeff`);
* the **face lemma**: `0 ≤ x ≤ c` with `c` idempotent forces `c ∘ x = x` (`face_lemma`).

`EuclideanJordan/Order.lean` proves the first from the *ambient* inner product, under the
    hypothesis that the
inner product is associative for the Jordan product.  A consumer that carries an inner product
and a Jordan product as unrelated data has no such hypothesis available, which is why this file
pairs against `EuclideanJordan/TraceForm.lean`'s `traceForm` instead: a form built from the
    algebra, so nothing has to
be assumed about an ambient one.  Both facts are proved here from scratch in that vocabulary; the
`inner`-shaped originals in `EuclideanJordan/Order.lean` are untouched and are not used.

## Extreme points are not needed

The natural-looking characterisation — `c` is idempotent iff it is an extreme point of `[0, e]` —
is **avoided deliberately**.  ★ The reason is a price judgment and is recorded as one, not as a
theorem: on the classical proof both of its directions run through the same face lemma that
sharpness needs, and it additionally drags in Mathlib's `Set.extremePoints` and convexity API and
forces `[0, e]` to be stated as a `Set`.  Nothing below establishes that, because the
extreme-points route was never built.

★ `EuclideanJordan/OrderUnitSpace.lean` carries an `IsSharp` of its own, and this file does
**not** use it or bridge to it.  That one is stated over an `OrderUnitSpace` instance, and getting
one here would mean instantiating `EuclideanJordan/Order.lean`'s `orderUnitSpaceOfBilinear` — a
    `def`, whose
own docstring warns that instantiating it puts a second `PartialOrder J` in scope.
★★ **The two are not literally the same formula, and the difference is worth stating rather than
glossing.**  `OrderUnitSpace.IsSharp` quantifies its witness over the *effects* (`IsEffect a`, i.e.
`0 ≤ a ≤ 𝟙`); `IsSharp` below quantifies over the whole cone (`IsSoS mulLₗ x`, with no upper bound
on `x`).  The extra clause is redundant — `x ≤ c` and `c ≤ e` give `x ≤ e` by transitivity of the
cone order — so the two conditions are equivalent; but **that equivalence is proved nowhere below
and nothing needs it**, and the version used here is the one whose witness hypothesis is weaker,
hence the harder condition to satisfy and the safer one to transport.

## What this closes, and what it does not

★★ **This is one clause of a larger statement, and which clause it is matters.**  The route that
builds an order automorphism `Θ_a` out of a sequential product and then reads it as a Jordan
automorphism needs three separate things: the construction of `Θ_a` (van de Wetering,
arXiv:1803.11139, Prop 5.3), the upgrade of a unital linear order isomorphism to a Jordan
automorphism, and the fixing and cocycle properties (vdW Props 5.5, 5.7).  **Only the upgrade is
proved here.**  The other two are cited, not formalized, and nothing below establishes them.
-/

@[expose] public section

noncomputable section

namespace EuclideanJordan

open Finset

/-! ## Pairing against the trace form -/

section Abstract

variable {J : Type*} [NonUnitalNonAssocCommRing J] [IsCommJordan J] [Module ℝ J]
  [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J]

omit [IsFormallyReal J] [Module.Finite ℝ J] in
/-- **`L_c` is a positive operator for the trace form**, in the sharp form that also reads off when
the pairing vanishes: `τ(c ∘ y, y)` is the sum of two squares of the form, one for each nonzero
Peirce eigenvalue of `c`.

`L_c = P₁(c) + ½ P_{1/2}(c)`; both Peirce projections are self-adjoint for `τ` (associativity, three
times) and idempotent, so `τ(P y, y) = τ(P y, P y)`.

★ Stated as an equation rather than as an inequality because both consumers need it: nonnegativity
falls out, and so does `c ∘ y = 0` from a vanishing pairing — which an inequality would have
lost. -/
theorem traceForm_mulL_split {c : J} (hc : c * c = c) (y : J) :
    traceForm (c * y) y
      = traceForm (peirceOne c y) (peirceOne c y)
        + (2 : ℝ)⁻¹ * traceForm (peirceHalf c y) (peirceHalf c y) := by
  have hsa1 : ∀ u v : J, traceForm (peirceOne c u) v = traceForm u (peirceOne c v) := by
    intro u v
    simp only [peirceOne_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [traceForm_assoc c (c * u) v, traceForm_assoc c u (c * v), traceForm_assoc c u v]
  have hsah : ∀ u v : J, traceForm (peirceHalf c u) v = traceForm u (peirceHalf c v) := by
    intro u v
    simp only [peirceHalf_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    rw [traceForm_assoc c (c * u) v, traceForm_assoc c u (c * v), traceForm_assoc c u v]
  have hid1 : peirceOne c (peirceOne c y) = peirceOne c y :=
    peirceOne_of_eigen (mul_peirceOne hc y)
  have hidh : peirceHalf c (peirceHalf c y) = peirceHalf c y :=
    peirceHalf_of_eigen_half (mul_peirceHalf hc y)
  have key1 : traceForm (peirceOne c y) (peirceOne c y) = traceForm (peirceOne c y) y := by
    rw [hsa1 y (peirceOne c y), hid1, traceForm_comm]
  have keyh : traceForm (peirceHalf c y) (peirceHalf c y) = traceForm (peirceHalf c y) y := by
    rw [hsah y (peirceHalf c y), hidh, traceForm_comm]
  have hsplit : (c * y : J) = peirceOne c y + (2 : ℝ)⁻¹ • peirceHalf c y := by
    simp only [peirceOne_apply, peirceHalf_apply]
    module
  rw [key1, keyh, hsplit, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]

theorem traceForm_mulL_nonneg_of_idem {c : J} (hc : c * c = c) (y : J) :
    0 ≤ traceForm (c * y) y := by
  rw [traceForm_mulL_split hc y]
  have h1 := traceForm_self_nonneg (peirceOne c y)
  have h2 := traceForm_self_nonneg (peirceHalf c y)
  linarith

/-- A vanishing pairing kills the product outright: both Peirce components of `y` at `c` vanish, so
`c ∘ y = 0`.  This is where definiteness of `traceForm` is spent. -/
theorem mul_eq_zero_of_traceForm_mulL_eq_zero {c : J} (hc : c * c = c) {y : J}
    (h : traceForm (c * y) y = 0) : c * y = 0 := by
  rw [traceForm_mulL_split hc y] at h
  have h1 := traceForm_self_nonneg (peirceOne c y)
  have h2 := traceForm_self_nonneg (peirceHalf c y)
  have e1 : peirceOne c y = 0 := eq_zero_of_traceForm_self_eq_zero (by linarith)
  have e2 : peirceHalf c y = 0 := eq_zero_of_traceForm_self_eq_zero (by linarith)
  have hsplit : (c * y : J) = peirceOne c y + (2 : ℝ)⁻¹ • peirceHalf c y := by
    simp only [peirceOne_apply, peirceHalf_apply]
    module
  rw [hsplit, e1, e2, smul_zero, add_zero]

/-- **An idempotent pairs nonnegatively with the cone.**  Associativity moves `c` onto one factor of
each square, and the previous lemma does the rest. -/
theorem traceForm_nonneg_of_idem_of_isSoS {c x : J} (hc : c * c = c)
    (hx : IsSoS mulLₗ x) : 0 ≤ traceForm c x := by
  obtain ⟨k, f, hf⟩ := hx
  simp only [mulLₗ_apply, mulL_apply] at hf
  rw [hf, map_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  have hmove : traceForm c (f i * f i) = traceForm (c * f i) (f i) := by
    simp only [traceForm_apply]
    exact (jtr_assoc c (f i) (f i)).symm
  rw [hmove]
  exact traceForm_mulL_nonneg_of_idem hc (f i)

/-- **A vanishing pairing against the cone annihilates.**  Every square in the presentation is
killed factor by factor, and `J₀(c)` is a subalgebra, so the whole element is killed. -/
theorem mul_eq_zero_of_traceForm_eq_zero {c x : J} (hc : c * c = c)
    (hx : IsSoS mulLₗ x) (h : traceForm c x = 0) : c * x = 0 := by
  obtain ⟨k, f, hf⟩ := hx
  simp only [mulLₗ_apply, mulL_apply] at hf
  have hterm : ∀ i : Fin k, 0 ≤ traceForm c (f i * f i) := by
    intro i
    have hmove : traceForm c (f i * f i) = traceForm (c * f i) (f i) := by
      simp only [traceForm_apply]
      exact (jtr_assoc c (f i) (f i)).symm
    rw [hmove]
    exact traceForm_mulL_nonneg_of_idem hc (f i)
  have hsum : (∑ i, traceForm c (f i * f i)) = 0 := by rw [← map_sum, ← hf]; exact h
  have hzero : ∀ i : Fin k, traceForm c (f i * f i) = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hterm j).mp hsum i (Finset.mem_univ i)
  have hkill : ∀ i : Fin k, c * f i = 0 := by
    intro i
    refine mul_eq_zero_of_traceForm_mulL_eq_zero hc ?_
    have hmove : traceForm c (f i * f i) = traceForm (c * f i) (f i) := by
      simp only [traceForm_apply]
      exact (jtr_assoc c (f i) (f i)).symm
    rw [← hmove]
    exact hzero i
  rw [hf, Finset.mul_sum]
  exact Finset.sum_eq_zero fun i _ => eigen_zero_mul_zero hc (hkill i) (hkill i)

/-! ## The face lemma -/

omit [IsCommJordan J] [Module ℝ J] [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- The orthocomplement of an idempotent is an idempotent. -/
theorem sub_idem {e c : J} (he : ∀ y : J, e * y = y) (hc : c * c = c) :
    (e - c) * (e - c) = e - c := by
  have hce : c * e = c := by rw [mul_comm]; exact he c
  rw [sub_mul, mul_sub, mul_sub, he, he, hc, hce, sub_self, sub_zero]

/-- **The face lemma.**  If `0 ≤ x ≤ c` with `c` idempotent, then `c ∘ x = x`.

Pair against the complementary idempotent `e − c`: the pairing with `x` is nonnegative, and bounded
above by the pairing with `c`, which is `τ((e − c) ∘ c) = τ(0) = 0`.  So it vanishes, and the
previous lemma turns that into `(e − c) ∘ x = 0`. -/
theorem face_lemma {e c x : J} (he : ∀ y : J, e * y = y) (hc : c * c = c)
    (hx : IsSoS mulLₗ x) (hcx : IsSoS mulLₗ (c - x)) : c * x = x := by
  have hd : (e - c) * (e - c) = e - c := sub_idem he hc
  have h1 : 0 ≤ traceForm (e - c) x := traceForm_nonneg_of_idem_of_isSoS hd hx
  have h2 : 0 ≤ traceForm (e - c) (c - x) := traceForm_nonneg_of_idem_of_isSoS hd hcx
  have hdc : traceForm (e - c) c = 0 := by
    have hz : (e - c) * c = 0 := by rw [sub_mul, he, hc, sub_self]
    simp only [traceForm_apply, hz, map_zero]
  rw [map_sub, hdc] at h2
  have hzero : traceForm (e - c) x = 0 := le_antisymm (by linarith) h1
  have hdx : (e - c) * x = 0 := mul_eq_zero_of_traceForm_eq_zero hd hx hzero
  rw [sub_mul, he, sub_eq_zero] at hdx
  exact hdx.symm

/-- **Idempotents summing to the unit are pairwise orthogonal** — orthogonality is *recovered*, not
transported.  `qⱼ` lies under the idempotent `e − qᵢ`, because the difference is the sum of the
remaining members of the family; the face lemma then gives `(e − qᵢ) ∘ qⱼ = qⱼ`. -/
theorem orth_of_sum_eq_unit {n : ℕ} {q : Fin n → J} {e : J} (he : ∀ y : J, e * y = y)
    (hidem : ∀ i, q i * q i = q i) (hsum : (∑ i, q i) = e) (i j : Fin n) (hij : i ≠ j) :
    q i * q j = 0 := by
  classical
  have hjm : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩
  have h1 : (∑ k, q k) = q i + ∑ k ∈ Finset.univ.erase i, q k :=
    (Finset.add_sum_erase _ q (Finset.mem_univ i)).symm
  have h2 : (∑ k ∈ Finset.univ.erase i, q k)
      = q j + ∑ k ∈ (Finset.univ.erase i).erase j, q k :=
    (Finset.add_sum_erase _ q hjm).symm
  have hrest : e - q i - q j = ∑ k ∈ (Finset.univ.erase i).erase j, q k := by
    rw [← hsum, h1, h2]; abel
  have hsos : IsSoS mulLₗ (e - q i - q j) := by
    rw [hrest]
    exact isSoS_sum _ _ fun k _ => isSoS_of_idem (hidem k)
  have hfl : (e - q i) * q j = q j :=
    face_lemma he (sub_idem he (hidem i)) (isSoS_of_idem (hidem j)) hsos
  rw [sub_mul, he, sub_eq_self] at hfl
  exact hfl

/-! ## Reading the spectral coefficients -/

omit [IsCommJordan J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- A combination of orthogonal idempotents with nonnegative coefficients is in the cone.  The
coefficient condition is only imposed where the idempotent is nonzero, matching what
`nonneg_coeff` can supply: `EuclideanJordan/Spectral.lean`'s resolution pads with a
    possibly-zero idempotent,
whose coefficient is unconstrained. -/
theorem isSoS_sum_smul_idem {n : ℕ} {q : Fin n → J} (hidem : ∀ i, q i * q i = q i)
    {g : Fin n → ℝ} (hg : ∀ i, q i ≠ 0 → 0 ≤ g i) :
    IsSoS mulLₗ (∑ i, g i • q i) := by
  refine isSoS_sum _ _ fun i _ => ?_
  by_cases h : q i = 0
  · rw [h, smul_zero]; exact isSoS_zero
  · exact isSoS_smul_idem (hg i h) (hidem i)

/-- **A sum of squares has nonnegative spectral coefficients.**  Pairing against `qₖ` reads the
coefficient off directly — `τ(qₖ, qᵢ) = tr(L_{qₖ ∘ qᵢ})` is `0` off the diagonal by orthogonality —
and the pairing is nonnegative because `x` is in the cone; the diagonal value `tr(L_{qₖ})` is at
least `1`. -/
theorem nonneg_coeff {n : ℕ} {q : Fin n → J} {lam : Fin n → ℝ}
    (hidem : ∀ i, q i * q i = q i) (horth : ∀ i j, i ≠ j → q i * q j = 0)
    {x : J} (hx : x = ∑ i, lam i • q i) (hsos : IsSoS mulLₗ x)
    {k : Fin n} (hk : q k ≠ 0) : 0 ≤ lam k := by
  have hpair : traceForm (q k) x = lam k * jtr (q k) := by
    rw [hx, map_sum, Finset.sum_eq_single k]
    · rw [map_smul, smul_eq_mul, traceForm_apply, hidem k]
    · intro i _ hik
      rw [map_smul, smul_eq_mul, traceForm_apply, horth k i (Ne.symm hik), map_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ k) h
  have hnn : 0 ≤ traceForm (q k) x := traceForm_nonneg_of_idem_of_isSoS (hidem k) hsos
  have hpos : (0 : ℝ) < jtr (q k) :=
    lt_of_lt_of_le zero_lt_one (one_le_jtr_of_idem (hidem k) hk)
  nlinarith [hpair, hnn, hpos]

omit [IsCommJordan J] [IsScalarTower ℝ J J] [IsFormallyReal J] [Module.Finite ℝ J] in
/-- Subtracting a multiple of one member of a family shifts exactly that coefficient.  The
bookkeeping step behind both witnesses in `idem_of_isSharp`. -/
theorem sum_smul_sub_smul {n : ℕ} (q : Fin n → J) (g : Fin n → ℝ) (i : Fin n) (mu : ℝ) :
    (∑ j, g j • q j) - mu • q i = ∑ j, (if j = i then g i - mu else g j) • q j := by
  classical
  have hpt : ∀ j : Fin n, (if j = i then g i - mu else g j) • q j
      = g j • q j - (if j = i then mu • q i else 0) := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [sub_smul]
    · simp [hj]
  calc (∑ j, g j • q j) - mu • q i
      = (∑ j, g j • q j) - ∑ j, (if j = i then mu • q i else 0) := by
        simp [Finset.sum_ite_eq']
    _ = ∑ j, (g j • q j - (if j = i then mu • q i else 0)) := by
        rw [Finset.sum_sub_distrib]
    _ = ∑ j, (if j = i then g i - mu else g j) • q j :=
        (Finset.sum_congr rfl fun j _ => hpt j).symm

/-! ## Sharpness -/

/-- **A sharp element**: in the cone, below the unit, and with no nonzero element of the cone below
both it and its complement.

This is `EuclideanJordan/OrderUnitSpace.lean`'s `IsSharp` written in the sums-of-squares
vocabulary, with `0 ≤ z` spelled `IsSoS mulLₗ z` and `a ≤ b` spelled `IsSoS mulLₗ (b - a)`.  No
lemma below relates the two; see the module docstring for why not. -/
def IsSharp (e c : J) : Prop :=
  IsSoS mulLₗ c ∧ IsSoS mulLₗ (e - c) ∧
    ∀ x : J, IsSoS mulLₗ x → IsSoS mulLₗ (c - x) → IsSoS mulLₗ (e - c - x) → x = 0

/-- An idempotent is sharp.  The face lemma applies at `c` and at `e − c`, giving `x = c ∘ x` and
`x = (e − c) ∘ x = x − c ∘ x`, so `x = 0`. -/
theorem isSharp_of_idem {e c : J} (he : ∀ y : J, e * y = y) (hc : c * c = c) : IsSharp e c := by
  refine ⟨isSoS_of_idem hc, isSoS_of_idem (sub_idem he hc), fun x hx hcx hecx => ?_⟩
  have h1 : c * x = x := face_lemma he hc hx hcx
  have h2 : (e - c) * x = x := face_lemma he (sub_idem he hc) hx hecx
  rw [sub_mul, he, h1, sub_self] at h2
  exact h2.symm

/-- **A sharp element is an idempotent** — the half that spends the spectral theorem.

Resolve `c = ∑ λᵢ qᵢ`.  Being in the cone forces `λᵢ ≥ 0` and being below the unit forces
`λᵢ ≤ 1`, both by `nonneg_coeff`.  A coefficient strictly inside `(0, 1)` would make
`min(λₖ, 1 − λₖ) • qₖ` a nonzero witness against sharpness, so every coefficient at a nonzero
idempotent is `0` or `1` — and then `λᵢ² = λᵢ` termwise. -/
theorem idem_of_isSharp {e c : J} (he : ∀ y : J, e * y = y) (h : IsSharp e c) : c * c = c := by
  obtain ⟨hc, hec, hsharp⟩ := h
  obtain ⟨n, q, lam, hfam, hsum, hcq⟩ := spectral_resolution_complete e he c
  have hec' : e - c = ∑ i, (1 - lam i) • q i := by
    have hr := smul_unit_sub_eq hsum hcq 1
    rwa [one_smul] at hr
  have hlo : ∀ i, q i ≠ 0 → 0 ≤ lam i := fun i hi =>
    nonneg_coeff hfam.idem hfam.orth hcq hc hi
  have hhi : ∀ i, q i ≠ 0 → lam i ≤ 1 := by
    intro i hi
    have := nonneg_coeff hfam.idem hfam.orth hec' hec hi
    linarith
  have hbin : ∀ i, q i ≠ 0 → lam i = 0 ∨ lam i = 1 := by
    intro i hi
    rcases eq_or_lt_of_le (hlo i hi) with h0 | hlt0
    · exact Or.inl h0.symm
    rcases eq_or_lt_of_le (hhi i hi) with h1 | hlt1
    · exact Or.inr h1
    exfalso
    have hmupos : 0 < min (lam i) (1 - lam i) := lt_min hlt0 (by linarith)
    set mu := min (lam i) (1 - lam i) with hmudef
    have hmu1 : mu ≤ lam i := min_le_left _ _
    have hmu2 : mu ≤ 1 - lam i := min_le_right _ _
    have hwx : IsSoS mulLₗ (mu • q i) := isSoS_smul_idem (le_of_lt hmupos) (hfam.idem i)
    have hwc : IsSoS mulLₗ (c - mu • q i) := by
      rw [hcq, sum_smul_sub_smul q lam i mu]
      refine isSoS_sum_smul_idem hfam.idem fun j hj => ?_
      by_cases hji : j = i
      · rw [ite_eq_left hji]; linarith
      · rw [ite_eq_right hji]; exact hlo j hj
    have hwe : IsSoS mulLₗ (e - c - mu • q i) := by
      rw [hec', sum_smul_sub_smul q (fun j => 1 - lam j) i mu]
      refine isSoS_sum_smul_idem hfam.idem fun j hj => ?_
      by_cases hji : j = i
      · rw [ite_eq_left hji]
        show (0 : ℝ) ≤ 1 - lam i - mu
        linarith
      · rw [ite_eq_right hji]
        show (0 : ℝ) ≤ 1 - lam j
        linarith [hhi j hj]
    have hzero := hsharp (mu • q i) hwx hwc hwe
    rcases smul_eq_zero.mp hzero with hz | hz
    · exact absurd hz (ne_of_gt hmupos)
    · exact hi hz
  have hsq : c * c = ∑ i, (lam i * lam i) • q i := sq_of_orthIdem hfam hcq
  rw [hsq, hcq]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : q i = 0
  · rw [hi, smul_zero, smul_zero]
  · rcases hbin i hi with hb | hb <;> rw [hb] <;> norm_num

/-- **Idempotents are exactly the sharp elements.** -/
theorem isSharp_iff_idem {e c : J} (he : ∀ y : J, e * y = y) : IsSharp e c ↔ c * c = c :=
  ⟨idem_of_isSharp he, isSharp_of_idem he⟩

/-! ## The automorphism -/

variable {e : J}

/-- **A unital linear order isomorphism preserves idempotents.**

Sharpness is a statement about the cone and the unit, both of which `Φ` preserves; the `∀` clause is
transported through `Φ.symm`, which is where the *reflecting* half of `horder` is spent. -/
theorem map_idem_of_orderIso (he : ∀ y : J, e * y = y) (Φ : J ≃ₗ[ℝ] J) (hunital : Φ e = e)
    (horder : ∀ x : J, IsSoS mulLₗ x ↔ IsSoS mulLₗ (Φ x)) {c : J} (hc : c * c = c) :
    Φ c * Φ c = Φ c := by
  refine idem_of_isSharp he ?_
  obtain ⟨h1, h2, h3⟩ := isSharp_of_idem he hc
  refine ⟨(horder c).mp h1, ?_, ?_⟩
  · have hstep := (horder (e - c)).mp h2
    rwa [map_sub, hunital] at hstep
  · intro x hx hcx hecx
    have hw : Φ.symm x = 0 := by
      refine h3 (Φ.symm x) ((horder _).mpr ?_) ((horder _).mpr ?_) ((horder _).mpr ?_)
      · rwa [Φ.apply_symm_apply]
      · rwa [map_sub, Φ.apply_symm_apply]
      · rwa [map_sub, map_sub, hunital, Φ.apply_symm_apply]
    rw [← Φ.apply_symm_apply x, hw, map_zero]

/-- **A unital linear order isomorphism preserves squares.**

The image of a complete orthogonal family is a family of idempotents summing to the unit, hence
pairwise orthogonal by `orth_of_sum_eq_unit`; squaring is then coefficientwise on both sides. -/
theorem map_sq_of_orderIso (he : ∀ y : J, e * y = y) (Φ : J ≃ₗ[ℝ] J) (hunital : Φ e = e)
    (horder : ∀ x : J, IsSoS mulLₗ x ↔ IsSoS mulLₗ (Φ x)) (x : J) :
    Φ (x * x) = Φ x * Φ x := by
  obtain ⟨n, q, lam, hfam, hsum, hx⟩ := spectral_resolution_complete e he x
  have hidem' : ∀ i, Φ (q i) * Φ (q i) = Φ (q i) := fun i =>
    map_idem_of_orderIso he Φ hunital horder (hfam.idem i)
  have hsum' : (∑ i, Φ (q i)) = e := by rw [← map_sum, hsum, hunital]
  have hfam' : IsOrthIdemFamily (fun i => Φ (q i)) :=
    ⟨hidem', orth_of_sum_eq_unit he hidem' hsum'⟩
  have hΦx : Φ x = ∑ i, lam i • Φ (q i) := by
    rw [hx, map_sum]; simp only [map_smul]
  rw [sq_of_orthIdem hfam' hΦx, sq_of_orthIdem hfam hx, map_sum]
  simp only [map_smul]

/-- **Koecher / Alfsen–Shultz.**  A unital linear order isomorphism of a finite-dimensional formally
real Jordan algebra is a Jordan automorphism.

Polarisation: `2 (x ∘ y) = (x + y)² − x² − y²`, and `Φ` is linear, so preservation of squares is
preservation of the product once the `2` is cancelled. -/
theorem map_jordan_of_orderIso (he : ∀ y : J, e * y = y) (Φ : J ≃ₗ[ℝ] J) (hunital : Φ e = e)
    (horder : ∀ z : J, IsSoS mulLₗ z ↔ IsSoS mulLₗ (Φ z)) (x y : J) :
    Φ (x * y) = Φ x * Φ y := by
  have hxy := map_sq_of_orderIso he Φ hunital horder (x + y)
  have hxx := map_sq_of_orderIso he Φ hunital horder x
  have hyy := map_sq_of_orderIso he Φ hunital horder y
  have hl : (x + y) * (x + y) = x * x + (x * y + x * y) + y * y := by
    rw [add_mul, mul_add, mul_add, mul_comm y x]; abel
  have hr : (Φ x + Φ y) * (Φ x + Φ y)
      = Φ x * Φ x + (Φ x * Φ y + Φ x * Φ y) + Φ y * Φ y := by
    rw [add_mul, mul_add, mul_add, mul_comm (Φ y) (Φ x)]; abel
  rw [hl, map_add Φ x y, hr, map_add, map_add, map_add, hxx, hyy] at hxy
  have h4 : Φ (x * y) + Φ (x * y) = Φ x * Φ y + Φ x * Φ y :=
    add_left_cancel (add_right_cancel hxy)
  have h5 : (2 : ℕ) • (Φ (x * y) - Φ x * Φ y) = 0 := by
    rw [two_nsmul]
    linear_combination (norm := abel) h4
  exact sub_eq_zero.mp (nsmul_eq_zero_iff' (by norm_num) h5)

end Abstract

/-! ## The theorem in bilinear-map vocabulary

The crossing `EuclideanJordan/Bridge.lean` was built for: the *statement* mentions only the
    bundled bilinear
map, so no ring instance has to exist before it elaborates; only the proof needs one. -/

section Interface

variable {J : Type*} [NormedAddCommGroup J] [Module ℝ J] [Module.Finite ℝ J]

/-- **Koecher / Alfsen–Shultz, in bilinear-map vocabulary.**  The Jordan product as a bundled
bilinear map, the Jordan identity and formal reality as hypotheses in that vocabulary, and the cone
as `EuclideanJordan/Order.lean`'s `IsSoS`.

★ No inner product appears.  The ambient structure is a normed additive group carrying an
`ℝ`-module structure — `NormedAddCommGroup` only because `EuclideanJordan/Bridge.lean`'s
    `ringOfBilinear` is
stated over one — and the norm is never used. -/
theorem orderIso_preservesJordan (m : J →ₗ[ℝ] J →ₗ[ℝ] J)
    (hcomm : ∀ x y : J, m x y = m y x)
    (hjordan : ∀ a b : J, m (m a b) (m a a) = m a (m b (m a a)))
    (hfr : ∀ (k : ℕ) (f : Fin k → J), (∑ i, m (f i) (f i)) = 0 → ∀ i, f i = 0)
    (e : J) (he : ∀ y : J, m e y = y)
    (Φ : J ≃ₗ[ℝ] J) (hunital : Φ e = e)
    (horder : ∀ x : J, IsSoS m x ↔ IsSoS m (Φ x)) (x y : J) :
    Φ (m x y) = m (Φ x) (Φ y) := by
  let : NonUnitalNonAssocCommRing J := ringOfBilinear m hcomm
  let : IsCommJordan J := ⟨hjordan⟩
  let : IsScalarTower ℝ J J := ⟨fun r a b => smul_bilinear m r a b⟩
  let : IsFormallyReal J := isFormallyReal_of_fin m hcomm hfr
  have hm : (mulLₗ : J →ₗ[ℝ] J →ₗ[ℝ] J) = m := by ext a b; rfl
  rw [hm] at *
  exact map_jordan_of_orderIso he Φ hunital horder x y

end Interface

end EuclideanJordan
