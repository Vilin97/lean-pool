/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Germ.AlgebraicIndependence.Power

import LeanPool.ConwayRefinement.ConwayRefinement.Blueprint
import LeanPool.ConwayRefinement.ConwayRefinement.Topology.Order.LeftNeighborhood
import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.Nonpositive
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPrincipal
import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.NaturalPowerFactorization

/-!
# Cancellation through residual Cantor–Bendixson ranks

A lower bound on translated truncations at residual-rank cutoffs reconstructs a lower bound
at zero. Applied to the power remainder, this proves the pure-power cancellation step.
For a power times a second factor, multiply the product rule by that factor; the smaller
remainder and the deficient-product term cannot cancel the term of known value.

Both cancellation statements retain an explicit hypothesis about smaller products. They do
not assert multiplicativity on their own. The natural-number multiplicity survives because
the coefficient domain has characteristic zero. No field inverse is used.

V denotes the value in NatOrdinal, and T denotes translated weak truncation, in the proofs.
The ordinal factorisation calculation is the one used in Berarducci, Lemma 8.2, applied here
to the Cantor–Bendixson value on an ordered exponent group that is Cauchy complete.
-/

public noncomputable section

open Set Filter Topology
universe u v
namespace HahnSeries
variable {G : Type u} {R : Type v} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [UniformSpace G] [IsUniformAddGroup G] [OrderTopology G] [Nontrivial G] [CompleteSpace G]
  [CommRing R] [NoZeroDivisors R] [CharZero R]


local notation "V" => (fun b : HahnSeries G R ↦ NatOrdinal.of (cantorBendixsonValue b))
local notation:max "T" x:arg "," c:arg => translate (-c) (truncLE c x)

omit [CompleteSpace G] [NoZeroDivisors R] [CharZero R] in
/-- Eventual bounds at residual-rank cutoffs reconstruct an ordinary principal-factor multiple. -/
theorem cantorBendixsonValue_residual_reconstruction (b d : HahnSeries G R) (hb : b.support ⊆ Iic 0)
    (B : Ordinal.AdditivePrincipalAboveOne.{u}) (hB : b.cantorBendixsonValue = B.val)
    (X : NatOrdinal.{u}) (hX : Ordinal.IsAdditivelyPrincipal X.val)
    (hyp : ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ b)).cantorBendixsonValue =
        NatOrdinal.of B.residualFactor →
      X ≤ NatOrdinal.of (translate (-γ) (truncLE γ d)).cantorBendixsonValue) :
    X.val * B.principalFactor ≤ d.cantorBendixsonValue := by
  let a := Ordinal.log Ordinal.omega0 B.residualFactor
  let r := Ordinal.log Ordinal.omega0 B.principalFactor
  let c := Ordinal.log Ordinal.omega0 X.val
  have ha : Ordinal.omega0 ^ a = B.residualFactor :=
    B.residualFactor_isAdditivelyPrincipal.opow_log_self
  have hr : Ordinal.omega0 ^ r = B.principalFactor :=
    B.principalFactor_isInfiniteMultiplicativelyPrincipal.isAdditivelyPrincipal.opow_log_self
  have hc : Ordinal.omega0 ^ c = X.val := hX.opow_log_self
  have hrpos : 0 < r := by
    apply (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mp
    simpa only [Ordinal.opow_zero, hr] using B.one_lt_principalFactor
  have hbv : b.cantorBendixsonValue = Ordinal.omega0 ^ (a + r) := by
    rw [Ordinal.opow_add, ha, hr, B.residualFactor_mul_principalFactor, hB]
  have hl : ∀ᶠ γ in 𝓝[<] (0 : G),
      (T b, γ).cantorBendixsonValue = Ordinal.omega0 ^ a →
        Ordinal.omega0 ^ c ≤ (T d, γ).cantorBendixsonValue := by
    filter_upwards [hyp] with γ hγ he
    rw [ha] at he
    rw [hc]
    exact hγ (congrArg NatOrdinal.of he)
  have h := b.cantorBendixsonValue_reconstruction d hb a c r hrpos hbv hl
  rwa [Ordinal.opow_add, hc, hr] at h

/-- The expected values of the smaller residual-point products imply the pure-power formula. -/
@[blueprint "lem:cantor-bendixson-pure-power-cancellation"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Pure-power cancellation for the Cantor--Bendixson value")
  (statement := /--
    Let $R$ be a characteristic-zero domain, let $G$ be a nontrivial complete
    ordered abelian group equipped with a compatible additive uniformity and
    its order topology, and let $b\in R((G^{\le0}))$.  Suppose
    $V_{\mathrm{CB}}(b)=B>1$, where $B$ is additively principal, and write
    $B=\rho_B\odot\pi_B$ for its residual factor and its final infinite
    multiplicatively principal factor.  Let $m\in\mathbb N$.

    Suppose that, for every $\gamma<0$ sufficiently close to $0$,
    \[
      V_{\mathrm{CB}}(b^{\vert\gamma})=\rho_B
      \quad\Longrightarrow\quad
      V_{\mathrm{CB}}(b^{\vert\gamma}b^m)
        =B^{\odot m}\odot\rho_B.
    \]
    Then
    \[
      V_{\mathrm{CB}}(b^{m+1})=B^{\odot(m+1)}.
    \]
    Here products and powers marked by $\odot$ are Hessenberg's natural
    operations.
  -/)
  (proof := /--
    The translated truncation of $b^{m+1}$ is the main term
    $(m+1)b^{\vert\gamma}b^m$ plus a remainder of smaller
    Cantor--Bendixson value.  Characteristic zero preserves the value of the
    nonzero coefficient $m+1$, so the local hypothesis computes the value of
    the main term and hence of the whole truncation.  Applying
    \ref{lem:cantor-bendixson-rank-reconstruction} supplies the required lower
    bound at $0$; the reverse inequality follows by iterating
    \ref{lem:cantor-bendixson-value-product-upper-bound} over the power.
  -/)]
theorem cantorBendixsonValue_pow_eq_of_eventually (b : HahnSeries G R) (hb : b.support ⊆ Iic 0)
    (B : Ordinal.AdditivePrincipalAboveOne.{u}) (hB : b.cantorBendixsonValue = B.val) (m : ℕ)
    (hyp : ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ b)).cantorBendixsonValue =
        NatOrdinal.of B.residualFactor →
      NatOrdinal.of (translate (-γ) (truncLE γ b) * b ^ m).cantorBendixsonValue =
        NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor) :
    NatOrdinal.of (b ^ (m + 1)).cantorBendixsonValue =
      NatOrdinal.of B.val ^ (m + 1) := by
  let X := NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor
  have hX := B.power_residual_factorization m
  have hkey : ∀ᶠ γ in 𝓝[<] (0 : G), V (T b, γ) = NatOrdinal.of B.residualFactor →
      X ≤ V (T (b ^ (m + 1)), γ) := by
    filter_upwards [hyp, b.eventually_cantorBendixsonValue_powerRemainder_lt hb B hB m]
      with γ hγ hrem he
    have hmain : V ((m + 1) • (T b, γ * b ^ m)) = X := by
      dsimp only
      rw [cantorBendixsonValue_nsmul _ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))]
      exact hγ he
    have hsmall : V (T (b ^ (m + 1)), γ - (m + 1) • (T b, γ * b ^ m)) <
        V ((m + 1) • (T b, γ * b ^ m)) := by rwa [hmain]
    have hsum := cantorBendixsonValue_add_eq_max_of_ne
      (T (b ^ (m + 1)), γ - (m + 1) • (T b, γ * b ^ m))
      ((m + 1) • (T b, γ * b ^ m)) (ne_of_lt hsmall)
    rw [sub_add_cancel, max_eq_right (NatOrdinal.of.le_iff_le.mp hsmall.le)] at hsum
    exact le_of_eq ((congrArg NatOrdinal.of hsum).trans hmain).symm
  have hlow := cantorBendixsonValue_residual_reconstruction b (b ^ (m + 1)) hb B hB X hX.1 hkey
  have hid : X * NatOrdinal.of B.principalFactor = NatOrdinal.of B.val ^ (m + 1) := by
    dsimp only [X]
    rw [mul_assoc, B.naturalResidual_mul_naturalPrincipal, ← pow_succ]
  rw [← hX.2, hid] at hlow
  refine le_antisymm ?_ hlow
  simpa only [hB] using b.cantorBendixsonValue_pow_le hb (m + 1)


omit [CharZero R] [NoZeroDivisors R] [CommRing R] [CompleteSpace G] [Nontrivial G]
  [OrderTopology G] [IsUniformAddGroup G] [UniformSpace G] [IsOrderedAddMonoid G]
  [LinearOrder G] [AddCommGroup G] in
private theorem small_mul_lt (B C : Ordinal.AdditivePrincipalAboveOne.{u})
    (hp : B.principalFactor ≤ C.principalFactor) (X : NatOrdinal.{u}) (hX : 0 < X)
    (hfactor : (X * NatOrdinal.of B.principalFactor).val = X.val * B.principalFactor)
    {s t : NatOrdinal.{u}} (hs : s < X * NatOrdinal.of B.principalFactor)
    (ht : t < NatOrdinal.of C.val) :
    s * t < X * NatOrdinal.of C.val := by
  have hs' : s.val < X.val * B.principalFactor := by
    rw [← hfactor]
    exact hs
  have ht' : t.val < C.residualFactor * C.principalFactor := by
    rw [C.residualFactor_mul_principalFactor]
    exact ht
  obtain ⟨i, hi, hsi⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    B.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp hs'
  obtain ⟨j, hj, htj⟩ := (Ordinal.lt_mul_iff_of_isSuccLimit
    C.principalFactor_isInfiniteMultiplicativelyPrincipal.isSuccLimit).mp ht'
  have hρ : 0 < NatOrdinal.of C.residualFactor :=
    pos_iff_ne_zero.mpr C.residualFactor_isAdditivelyPrincipal.ne_zero
  have h := NatOrdinal.naturalMul_mul_lt_of_lt
    (ρ₁ := X) (ρ₂ := NatOrdinal.of C.residualFactor)
    (π₁ := NatOrdinal.of B.principalFactor) (π₂ := NatOrdinal.of C.principalFactor)
    (α₁ := NatOrdinal.of i) (α₂ := NatOrdinal.of j)
    C.principalFactor_isMultiplicativelyPrincipal hp hi hj (mul_pos hX hρ)
  rw [mul_assoc, C.naturalResidual_mul_naturalPrincipal] at h
  exact (mul_le_mul' (NatOrdinal.of.le_iff_le.mpr hsi.le)
    (NatOrdinal.of.le_iff_le.mpr htj.le)).trans_lt h

/-- The expected residual-point products imply the power-times-factor formula.
The second factor must have no smaller canonical principal factor. -/
@[blueprint "lem:cantor-bendixson-power-factor-cancellation"
  (phase := "Cantor–Bendixson ranks of supports")
  (title := "Power-times-factor cancellation for the Cantor--Bendixson value")
  (statement := /--
    Under the coefficient and exponent-group hypotheses of
    \ref{lem:cantor-bendixson-pure-power-cancellation}, let
    $b,c\in R((G^{\le0}))$ have additively principal values
    $V_{\mathrm{CB}}(b)=B>1$ and $V_{\mathrm{CB}}(c)=C>1$.  Write
    $B=\rho_B\odot\pi_B$ and $C=\rho_C\odot\pi_C$ as above, and suppose
    $\pi_B\le\pi_C$.  If, for every $\gamma<0$ sufficiently close to $0$,
    \[
      V_{\mathrm{CB}}(b^{\vert\gamma})=\rho_B
      \quad\Longrightarrow\quad
      V_{\mathrm{CB}}\!\left(
        b^{\vert\gamma}b^mc^2
      \right)
      =B^{\odot m}\odot\rho_B\odot C\odot C,
    \]
    then
    \[
      V_{\mathrm{CB}}(b^{m+1}c)
        =B^{\odot(m+1)}\odot C.
    \]
  -/)
  (proof := /--
    Put $d=b^{m+1}c$.  Multiply the translated-truncation expansion of $d$
    by $c$.  Its main term is
    $(m+1)b^{\vert\gamma}b^mc^2$; the two remaining terms have strictly
    smaller value by
    \ref{lem:cantor-bendixson-value-product-upper-bound}, the ordering
    $\pi_B\le\pi_C$, and the ordinal factorisation of $B$ and $C$.  Thus the
    hypothesis computes $V_{\mathrm{CB}}(c d^{\vert\gamma})$.  If
    $V_{\mathrm{CB}}(d^{\vert\gamma})$ were too small, the same upper bound
    would contradict this computation.  The resulting local lower bound is
    lifted to $0$ by
    \ref{lem:cantor-bendixson-rank-reconstruction}; the product upper bound
    gives the reverse inequality.
  -/)]
theorem cantorBendixsonValue_pow_mul_eq_of_eventually (b c : HahnSeries G R)
    (hb : b.support ⊆ Iic 0) (hc : c.support ⊆ Iic 0)
    (B C : Ordinal.AdditivePrincipalAboveOne.{u})
    (hB : b.cantorBendixsonValue = B.val) (hC : c.cantorBendixsonValue = C.val)
    (hp : B.principalFactor ≤ C.principalFactor) (m : ℕ)
    (hyp : ∀ᶠ γ in 𝓝[<] (0 : G),
      NatOrdinal.of (translate (-γ) (truncLE γ b)).cantorBendixsonValue =
        NatOrdinal.of B.residualFactor →
      NatOrdinal.of (translate (-γ) (truncLE γ b) * (b ^ m * c ^ 2)).cantorBendixsonValue =
        NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor *
          NatOrdinal.of C.val * NatOrdinal.of C.val) :
    NatOrdinal.of (b ^ (m + 1) * c).cantorBendixsonValue =
      NatOrdinal.of B.val ^ (m + 1) * NatOrdinal.of C.val := by
  let X := NatOrdinal.of B.val ^ m * NatOrdinal.of B.residualFactor * NatOrdinal.of C.val
  let d := b ^ (m + 1) * c
  have hd : d.support ⊆ Iic 0 :=
    (nonpositiveSubring G R).mul_mem ((nonpositiveSubring G R).pow_mem hb _) hc
  have hX := B.power_residual_mul_factorization C hp m
  have hCpos : 0 < NatOrdinal.of C.val := pos_iff_ne_zero.mpr C.2.1.ne_zero
  have hXpos : 0 < X := pos_iff_ne_zero.mpr hX.1.ne_zero
  have hZ : X * NatOrdinal.of B.principalFactor =
      NatOrdinal.of B.val ^ (m + 1) * NatOrdinal.of C.val := by
    dsimp only [X]
    rw [mul_assoc, mul_comm (NatOrdinal.of C.val), ← mul_assoc, mul_assoc _ _
      (NatOrdinal.of B.principalFactor), B.naturalResidual_mul_naturalPrincipal, ← pow_succ]
  refine le_antisymm ?_ ?_
  · exact (cantorBendixsonValue_mul_le _ _ ((nonpositiveSubring G R).pow_mem hb _) hc).trans
      (mul_le_mul' (by simpa only [hB] using b.cantorBendixsonValue_pow_le hb (m + 1))
        (le_of_eq (congrArg NatOrdinal.of hC)))
  by_contra hcon
  rw [not_le, ← hZ] at hcon
  have hkey : ∀ᶠ γ in 𝓝[<] (0 : G), V (T b, γ) = NatOrdinal.of B.residualFactor →
      X ≤ V (T d, γ) := by
    have hcut := (c.eventually_value_translated_truncLE_lt
      (hC ▸ C.2.1.ne_zero)).filter_mono (nhdsWithin_le_nhds (s := Iio (0 : G)))
    filter_upwards [hyp, b.eventually_cantorBendixsonValue_leibnizPowerRemainder_lt
      c hb hc B C hB hC hp m, hcut, self_mem_nhdsWithin]
      with γ hγ hrem hcut hneg he
    let main := (m + 1) • (T b, γ * (b ^ m * c ^ 2))
    let s1 := d * T c, γ
    let s2 := c * leibnizPowerRemainder b c m γ
    have hid : c * T d, γ = main + s1 + s2 := by
      dsimp only [main, s1, s2, d]
      rw [leibnizPowerRemainder_eq]
      simp only [nsmul_eq_mul]
      ring
    have hmain : V main = X * NatOrdinal.of C.val := by
      dsimp only [main]
      rw [cantorBendixsonValue_nsmul _ _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))]
      exact hγ he
    have hs1 : V s1 < X * NatOrdinal.of C.val := by
      refine (d.cantorBendixsonValue_mul_le (T c, γ) hd
        (c.support_translated_truncLE γ)).trans_lt ?_
      apply small_mul_lt B C hp X hXpos hX.2 hcon
      exact NatOrdinal.of.lt_iff_lt.mpr (hC ▸ hcut (ne_of_lt hneg))
    have hs2 : V s2 < X * NatOrdinal.of C.val := by
      have hle := c.cantorBendixsonValue_mul_le (leibnizPowerRemainder b c m γ) hc
        (support_leibnizPowerRemainder b c hb hc m γ)
      rw [hC] at hle
      have hlt : NatOrdinal.of C.val * V (leibnizPowerRemainder b c m γ) <
          NatOrdinal.of C.val * X := mul_lt_mul_of_pos_left hrem hCpos
      rw [mul_comm _ X] at hlt
      exact hle.trans_lt hlt
    have hsmall : (s1 + s2).cantorBendixsonValue <
        main.cantorBendixsonValue := by
      apply (s1.cantorBendixsonValue_add_le s2).trans_lt
      apply max_lt
      · exact NatOrdinal.of.lt_iff_lt.mp (hs1.trans_eq hmain.symm)
      · exact NatOrdinal.of.lt_iff_lt.mp (hs2.trans_eq hmain.symm)
    have hsum := main.cantorBendixsonValue_add_eq_max_of_ne (s1 + s2) (ne_of_gt hsmall)
    rw [max_eq_left hsmall.le] at hsum
    have hval : V (c * T d, γ) = X * NatOrdinal.of C.val := by
      rw [hid, add_assoc]
      exact (congrArg NatOrdinal.of hsum).trans hmain
    have hmul := c.cantorBendixsonValue_mul_le (T d, γ) hc (d.support_translated_truncLE γ)
    rw [hC] at hmul
    have hmul' : NatOrdinal.of C.val * X ≤ NatOrdinal.of C.val * V (T d, γ) := by
      rw [mul_comm _ X, ← hval]
      exact hmul
    exact le_of_mul_le_mul_left hmul' hCpos
  have hlow := cantorBendixsonValue_residual_reconstruction b d hb B hB X hX.1 hkey
  rw [← hX.2] at hlow
  exact (not_le.mpr hcon) hlow

end HahnSeries
