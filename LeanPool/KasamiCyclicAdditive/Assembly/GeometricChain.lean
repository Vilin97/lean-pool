/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Preliminaries.FiniteAverage
import LeanPool.KasamiCyclicAdditive.Counting.Definitions
import LeanPool.KasamiCyclicAdditive.Phase.DillonKashyapInterface
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.IncidenceChart
import LeanPool.KasamiCyclicAdditive.Geometry.PointFrobenius
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.RationalKernel
import LeanPool.KasamiCyclicAdditive.Phase.RootCount
import LeanPool.KasamiCyclicAdditive.Geometry.RootEquation
import LeanPool.KasamiCyclicAdditive.MCM.ComplementTransport
import LeanPool.KasamiCyclicAdditive.Geometry.EvenCase

/-!
# The assembled Kasami chain

This file is the place where the independently machine-checked
geometric and phase modules — `Geometry/FermatCubic`,
`Geometry/PointFrobenius.lean`, `Geometry/FermatCubic/RationalKernel.lean`,
`Geometry/EvenCase.lean` and `Phase/RootCount.lean` — are joined
into the final chain of the conjecture.

The main theorem is parameterized by explicit mathematical hypotheses for the
Walsh formula, the triple-count formula, and the slope average.  These are
ordinary theorem arguments, not axioms; the count and average formulas are
discharged internally from the half-size result, while the Walsh formula can
be supplied by the phase theorem.

The even-dimensional route is implemented outside this file:
`Geometry/EvenCase.lean` proves root-solvability by the quotient-first bridge,
inverting the prime-to-3 isogeny factor `G` on `E(K)` directly
(`PointFrobenius.exists_gMap_preimage`) and then taking a single `(1 + π)`
preimage over `AlgebraicClosure K`.
-/

open Finset
open KasamiCyclicAdditive.FermatCubic KasamiCyclicAdditive.PointFrobenius WeierstrassCurve

namespace KasamiCyclicAdditive

/-! ## The four bridging statements

The statements joining the geometric and phase modules to the counting
argument.  They are collected here so that the chain reads end to end. -/

/-! ## Auxiliary lemmas for the Dillon--Kashyap derivation -/

section Aux

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- Multiplicative Fourier inversion on `Kˣ`: additive sum to Gauss sums. -/
lemma fourier_units {psi : AddChar K ℂ} (g : Kˣ → ℂ) (a : Kˣ) :
    (Fintype.card Kˣ : ℂ) * ∑ x : Kˣ, g x * psi ((a : K) * (x : K)) =
      ∑ chi : MulChar K ℂ,
        (∑ y : Kˣ, g y * chi (y : K)) * chi (a : K) * gaussSum chi⁻¹ psi := by
  have hG : ∀ chi : MulChar K ℂ,
      gaussSum chi⁻¹ psi = ∑ z : Kˣ, chi⁻¹ (z : K) * psi (z : K) := by
    intro chi
    rw [gaussSum, ← KasamiCyclicAdditive.sum_units_eq_sum (fun z : K => chi⁻¹ z * psi z)
      (by simp only [MulChar.map_nonunit _ (by simp : ¬ IsUnit (0 : K)), zero_mul])]
  have key : ∀ chi : MulChar K ℂ,
      (∑ y : Kˣ, g y * chi (y : K)) * chi (a : K) * gaussSum chi⁻¹ psi =
        ∑ y : Kˣ, ∑ z : Kˣ, (g y * psi (z : K)) * chi (((a * y * z⁻¹ : Kˣ) : K)) := by
    intro chi
    rw [hG chi, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    have hchi : chi (a : K) * chi (y : K) * chi⁻¹ (z : K) = chi (((a * y * z⁻¹ : Kˣ) : K)) := by
      rw [MulChar.inv_apply']
      push_cast
      rw [map_mul, map_mul]
    rw [← hchi]
    ring
  simp only [key]
  rw [Finset.sum_comm]
  have : ∀ y : Kˣ, ∑ chi : MulChar K ℂ, ∑ z : Kˣ,
      (g y * psi (z : K)) * chi (((a * y * z⁻¹ : Kˣ) : K)) =
      (Fintype.card Kˣ : ℂ) * (g y * psi (((a * y : Kˣ) : K))) := by
    intro y
    rw [Finset.sum_comm]
    have : ∀ z : Kˣ, ∑ chi : MulChar K ℂ, (g y * psi (z : K)) * chi (((a * y * z⁻¹ : Kˣ) : K)) =
        if z = a * y then (Fintype.card Kˣ : ℂ) * (g y * psi (z : K)) else 0 := by
      intro z
      rw [← Finset.mul_sum, KasamiCyclicAdditive.Phase.sum_char_apply]
      by_cases hz : z = a * y
      · subst hz
        rw [mul_inv_cancel]
        simp [mul_comm]
      · have : a * y * z⁻¹ ≠ 1 := by
          intro hc
          exact hz (by rw [mul_inv_eq_one] at hc; exact hc.symm)
        simp [this, hz]
    rw [Finset.sum_congr rfl fun z _ => this z, Finset.sum_ite_eq' Finset.univ (a * y)]
    simp
  rw [Finset.sum_congr rfl fun y _ => this y, ← Finset.mul_sum]
  congr 1

end Aux

/-! ## The geometric input, in slope-free form

The two root-existence statements exist only to supply `RootEqSolvable`: the
bare statement that the twisted root equation is solvable at *every* affine
Fermat target with nonzero coordinates.  `one_le_rootCount` below uses it
directly to bound the root counts, with no intermediate geometric assumption.

Concretely `w = W ^ 3`, `z = T ^ 3` for a point `(W, T)` of the Fermat cubic, so
`w + z = 1` is the Fermat equation and `w ^ m = W ^ (3m) = W ^ (2^k+1)`; the
displayed equation is then exactly the twisted root equation of
`KasamiCyclicAdditive.FermatCubic.exists_twisted_root_equation`.

(`RootEqSolvable` lives in `Geometry/RootEquation.lean` so that
`Geometry/EvenCase.lean`, which proves it for even `n`, can be imported here
without an import cycle.) -/

section Bridge

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- On `Kˣ`, the derivative-image indicator is `(1 + F)/2`, where `F` is the
Dillon--Kashyap sign function.  Including the known point `0 ∈ Δ` gives the
corresponding identity for the Walsh coefficient. -/
private lemma twice_walshCoefficient_eq_one_add_sign_sum
    {k : ℕ} {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive) (a : Kˣ) :
    2 * walshCoefficient k ψ (a : K) =
      1 + ∑ x : Kˣ,
        (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * ψ ((a : K) * (x : K)) := by
  have hzero : (0 : K) ∈ derivativeImage k K := zero_mem_derivativeImage k
  set Su : ℂ := ∑ x : Kˣ,
    (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else 0) * ψ ((a : K) * (x : K))
    with hSu
  have hwalsh : walshCoefficient k ψ (a : K) = 1 + Su := by
    have hw : walshCoefficient k ψ (a : K)
        = ∑ x : K, (if x ∈ derivativeImage k K then (1 : ℂ) else 0) * ψ ((a : K) * x) := by
      rw [walshCoefficient]
      simp [ite_mul, Finset.sum_ite_mem]
    have hsplit := KasamiCyclicAdditive.sum_units_add
      (fun x : K => (if x ∈ derivativeImage k K then (1 : ℂ) else 0) * ψ ((a : K) * x))
    rw [hw, ← hsplit, hSu]
    simp [hzero]
  have hpsi1 := sum_units_addChar hψ a
  have hFsum : ∑ x : Kˣ,
      (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * ψ ((a : K) * (x : K))
      = 2 * Su + 1 := by
    have hpt : ∀ x : Kˣ,
        (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * ψ ((a : K) * (x : K))
          = 2 * ((if (x : K) ∈ derivativeImage k K then (1 : ℂ) else 0) *
              ψ ((a : K) * (x : K))) - ψ ((a : K) * (x : K)) := by
      intro x
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_sub_distrib, ← Finset.mul_sum, hpsi1,
      ← hSu]
    ring
  rw [hwalsh, hFsum]
  ring

/-- After inserting the Dillon--Kashyap phase formula, one multiplicative
Fourier coefficient contributes the desired Gauss-sum ratio; the principal
character contributes the unique correction term. -/
private lemma phase_fourier_character_term
    {k : ℕ} {ψ : AddChar K ℂ} (hψ : ψ.IsPrimitive)
    (hphase : DillonKashyapPhaseFormula k ψ) (a : Kˣ) (chi : MulChar K ℂ) :
    (∑ y : Kˣ,
        (if (y : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * chi (y : K)) *
        chi (a : K) * gaussSum chi⁻¹ ψ
      = (Fintype.card K : ℂ) *
          (gaussSum (chi ^ (2 ^ k + 1)) ψ / gaussSum (chi ^ 3) ψ * chi (a : K))
        - (if chi = 1 then (Fintype.card K : ℂ) - 1 else 0) := by
  rw [hphase chi]
  by_cases h1 : chi = 1
  · subst h1
    rw [ite_eq_left rfl, one_pow, one_pow, inv_one, gaussSum_principal hψ,
      MulChar.one_apply_coe]
    field_simp
    ring
  · rw [ite_eq_right h1, sub_zero]
    have h3 : gaussSum (chi ^ 3) ψ ≠ 0 := gaussSum_ne_zero_of_primitive hψ _
    have hmul : gaussSum chi ψ * gaussSum chi⁻¹ ψ = (Fintype.card K : ℂ) := by
      have h := gaussSum_mul_gaussSum_eq_card h1 hψ
      rwa [addChar_inv_self ψ] at h
    have hrw : gaussSum chi ψ * gaussSum (chi ^ (2 ^ k + 1)) ψ / gaussSum (chi ^ 3) ψ
          * chi (a : K) * gaussSum chi⁻¹ ψ
        = (gaussSum chi ψ * gaussSum chi⁻¹ ψ) *
            (gaussSum (chi ^ (2 ^ k + 1)) ψ / gaussSum (chi ^ 3) ψ * chi (a : K)) := by
      field_simp
    rw [hrw, hmul]

/-- **The Fourier interface.**  The
Dillon–Kashyap phase formula plus `0 ∈ Δ` give the
all-character Walsh identity `2 S(a) = (Q/N) ∑_χ [G(χ^e)/G(χ³)] χ(a)`, which is
`KasamiCyclicAdditive.Phase.WalshCharacterFormula` — the sole hypothesis consumed by
`KasamiCyclicAdditive.Phase.phase_to_root_count`.

The derivation: expand `1_Δ = (1 + F)/2` on `K*`, invert the
multiplicative transform, use `G(χ)G(χ⁻¹) = Q` for `χ ≠ 1` (valid because
`-1 = 1` in characteristic two) and `Ghat(1) = -1`, `Fhat(1) = -1`. -/
theorem walshCharacterFormula_of_phase_formula {k : ℕ} {ψ : AddChar K ℂ} (_hψ : ψ.IsPrimitive)
    (_hphase : DillonKashyapPhaseFormula k ψ) :
    KasamiCyclicAdditive.Phase.WalshCharacterFormula ψ (2 ^ k + 1) (walshCoefficient k ψ) := by
  intro a
  have hNpos : 0 < Fintype.card Kˣ := Fintype.card_pos
  have hN0 : (Fintype.card Kˣ : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hQeq : (Fintype.card K : ℂ) = (Fintype.card Kˣ : ℂ) + 1 := by
    have h := Fintype.card_units (α := K)
    have h2 : Fintype.card Kˣ + 1 = Fintype.card K := by
      rw [h]; exact Nat.succ_pred_eq_of_pos Fintype.card_pos
    exact_mod_cast h2.symm
  have hsign := twice_walshCoefficient_eq_one_add_sign_sum (k := k) _hψ a
  have hfourier := fourier_units (psi := ψ)
    (fun x : Kˣ => if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) a
  have hsum : (Fintype.card Kˣ : ℂ) *
      ∑ x : Kˣ,
        (if (x : K) ∈ derivativeImage k K then (1 : ℂ) else -1) * ψ ((a : K) * (x : K))
      = (Fintype.card K : ℂ) *
          (∑ chi : MulChar K ℂ,
            gaussSum (chi ^ (2 ^ k + 1)) ψ / gaussSum (chi ^ 3) ψ * chi (a : K))
        - ((Fintype.card K : ℂ) - 1) := by
    rw [hfourier,
      Finset.sum_congr rfl fun chi _ => phase_fourier_character_term _hψ _hphase a chi,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    simp
  rw [hsign, div_mul_eq_mul_div, eq_div_iff hN0]
  linear_combination hsum - hQeq

omit [DecidableEq K] in
/-- **Odd-dimensional root existence.**

For odd `n` every affine Fermat target with nonzero coordinates is hit by
`Φ_k = -(1 + π^k) + T₃`, so the twisted root equation is solvable.

Route.  `Φ_k(Q) = Φ_k(Q')` iff `(1 + π^k)(Q - Q') = 0`, and
`KasamiCyclicAdditive.FermatCubicFrobenius.rational_kernel_odd` says the `K`-rational kernel of
`1 + π^k` is just the origin, so `Φ_k` is injective, hence bijective on the
finite group `E(K)`.  Given a target `(p, q)` with `p, q ≠ 0` take
`Q = Φ_k⁻¹ (pt p q)`.  `Q` is affine (the three points at infinity are
`3`-torsion and `Φ_k` maps them among themselves, whereas `pt p q` is not
`3`-torsion by `KasamiCyclicAdditive.FermatCubic.three_torsion_pt_iff`), and `Q = pt W T` has
`W, T ≠ 0` by the same torsion criterion.  Then
`KasamiCyclicAdditive.FermatCubic.exists_twisted_root_equation` gives
`W ^ (2^k+1) + p * T ^ (2^k+1) = q`, and
`w = W ^ 3`, `z = T ^ 3` is the required pair. -/
theorem rootEquationSolvable_odd {n k m : ℕ} (hn : Odd n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n) (hm : 2 ^ k + 1 = 3 * m) :
    RootEqSolvable m K := by
  classical
  have hinj : Function.Injective
      (fun Q : (fer K).toAffine.Point => -(Q + (frobEnd K ^ k) Q) + t3 K) := by
    intro Q Q' hEq
    simp only at hEq
    have h1 : Q + (frobEnd K ^ k) Q = Q' + (frobEnd K ^ k) Q' :=
      neg_injective (add_right_cancel hEq)
    have h1' : (frobEnd K ^ k) Q + Q = (frobEnd K ^ k) Q' + Q' := by
      rw [add_comm ((frobEnd K ^ k) Q) Q, add_comm ((frobEnd K ^ k) Q') Q']; exact h1
    have h2 : (frobEnd K ^ k) (Q - Q') + (Q - Q') = 0 := by
      rw [map_sub, sub_add_sub_comm, h1', sub_self]
    exact sub_eq_zero.mp (kernel_trivial_odd hn hkn hcard h2)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro p q hp hq hpq
  obtain ⟨Q, hQ⟩ := hsurj (pt p q hpq)
  simp only at hQ
  have hzero : ¬ (-((0 : (fer K).toAffine.Point) + (frobEnd K ^ k) 0) + t3 K = pt p q hpq) := by
    intro hc
    rw [map_zero, add_zero, neg_zero, zero_add, t3] at hc
    exact hq (pt_inj hc).2.symm
  rcases point_repr Q with rfl | ⟨a, ha, rfl⟩ | ⟨W, T, h, rfl⟩
  · exact absurd hQ hzero
  · have ha1 : a = 1 :=
      KasamiCyclicAdditive.FermatCubicFrobenius.cube_root_eq_one_of_odd hn hcard ha
    subst ha1
    rw [show ptInf (1 : K) ha = 0 from by simp [ptInf]] at hQ
    exact absurd hQ hzero
  · rw [frobEnd_pow_pt] at hQ
    have hPhi : phi k W T h = pt p q hpq := hQ
    have hB5 : (3 : ℕ) • phi k W T h ≠ 0 := by
      rw [hPhi]
      intro hc
      rcases (three_torsion_pt_iff hpq).mp hc with hc' | hc'
      · exact hp hc'
      · exact hq hc'
    have hcoord : ∀ _ : W = 0 ∨ T = 0, False := by
      intro hor
      refine hB5 (three_torsion_phi h ?_)
      have htors : (3 : ℕ) • pt W T h = 0 := (three_torsion_pt_iff h).mpr hor
      rw [smul_add, htors, ← frobEnd_pow_pt k h, ← map_nsmul, htors, map_zero, add_zero]
    have hW : W ≠ 0 := fun hc => hcoord (Or.inl hc)
    have hT : T ≠ 0 := fun hc => hcoord (Or.inr hc)
    have hpc : ∀ x : K, x ^ 2 ^ n = x := by
      intro x
      have := FiniteField.pow_card x
      rwa [hcard] at this
    have hB3 : ∃ (c : K) (hc : c ^ 3 = 1),
        pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat h n) = pt W T h + ptInf c hc := by
      refine ⟨1, one_pow 3, ?_⟩
      rw [ptInf_one, add_zero]
      exact pt_congr _ _ (hpc W) (hpc T)
    obtain ⟨p', q', hpq', hPhi', hp', hq', hroot⟩ :=
      exists_twisted_root_equation h hW hT hkn hB3 hB5
    obtain ⟨hpe, hqe⟩ := pt_inj (hPhi'.symm.trans hPhi)
    subst hpe; subst hqe
    refine ⟨W ^ 3, T ^ 3, h, ?_⟩
    rw [← pow_mul, ← pow_mul, ← hm]
    exact hroot

/-- **Cube-support collapse.**  For even `n`,
`R(χ) = G((χ³)^m)/G(χ³)` is invariant under multiplication by cubic characters,
so summing each cubic orbit in the Walsh identity kills every non-cube.  Hence
`Z(ρ) = 0` unless both `ρ` and `1 + ρ` are cubes.

The character-sum half is `KasamiCyclicAdditive.Phase.S_eq_zero_of_not_cube`;
this lemma concludes vanishing of the triple sum.  It suffices that *one* of
`ρ`, `1 + ρ` fail to be a cube, since the triple sum then has a vanishing factor
either way. -/
theorem phaseTripleSum_eq_zero_of_not_cube {k m : ℕ} {ψ : AddChar K ℂ}
    {ρ : K} (_hψ : ψ.IsPrimitive) (_he : 2 ^ k + 1 = 3 * m)
    (_hW : KasamiCyclicAdditive.Phase.WalshCharacterFormula ψ (2 ^ k + 1) (walshCoefficient k ψ))
    (_hnc : (¬ ∃ A : K, A ^ 3 = ρ) ∨ (¬ ∃ B : K, B ^ 3 = 1 + ρ)) :
    KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) ρ (1 + ρ) = 0 := by
  have key : ∀ x : K, (¬ ∃ A : K, A ^ 3 = x) → ∀ lam : Kˣ,
      walshCoefficient k ψ ((lam : K)) = 0 ∨ walshCoefficient k ψ (x * (lam : K)) = 0 := by
    intro x hx lam
    have hx0 : x ≠ 0 := by
      rintro rfl; exact hx ⟨0, by ring⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    obtain ⟨z, hz⟩ : ∃ b : Kˣ, b ^ 3 = lam := by
      by_contra hb
      exact h1 (KasamiCyclicAdditive.Phase.S_eq_zero_of_not_cube _hψ _he _hW lam hb)
    obtain ⟨w, hw⟩ : ∃ b : Kˣ, b ^ 3 = Units.mk0 x hx0 * lam := by
      by_contra hb
      have h3 :=
        KasamiCyclicAdditive.Phase.S_eq_zero_of_not_cube _hψ _he _hW
          (Units.mk0 x hx0 * lam) hb
      exact h2 (by simpa using h3)
    refine hx ⟨((w * z⁻¹ : Kˣ) : K), ?_⟩
    have hcube : (w * z⁻¹) ^ 3 = Units.mk0 x hx0 := by
      rw [mul_pow, inv_pow, hz, hw, mul_inv_cancel_right]
    have := congrArg (fun u : Kˣ => (u : K)) hcube
    simpa using this
  rw [KasamiCyclicAdditive.Phase.phaseTripleSum]
  refine Finset.sum_eq_zero fun lam _ => ?_
  rcases _hnc with h | h
  · rcases key ρ h lam with h0 | h0 <;> rw [h0] <;> ring
  · rcases key (1 + ρ) h lam with h0 | h0 <;> rw [h0] <;> ring

/-- Every pair of cube roots of unity contributes at least one root.

Given `u, v ∈ μ₃`, set `a = u^m`, `b = v^m`, and apply `RootEqSolvable` at the
Fermat target `p = bA/a`, `q = bB`.  The resulting `w, z` produce the explicit
root `t = z^m / a`, for which `u t^D + v (A t + B)^D = z + w = 1`. -/
private lemma one_le_rootCount {m D : ℕ} {A B u v : K}
    (hA : A ≠ 0) (hB : B ≠ 0) (hAB : A ^ 3 + B ^ 3 = 1)
    (hpow : ∀ x : K, (x ^ m) ^ D = x) (hsolv : RootEqSolvable m K)
    (hu : u ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K)
    (hv : v ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K) :
    1 ≤ KasamiCyclicAdditive.Phase.rootCount D A B u v := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hu0 := KasamiCyclicAdditive.Phase.cubeRootsOne_ne_zero hu
  have hv0 := KasamiCyclicAdditive.Phase.cubeRootsOne_ne_zero hv
  have hu3 := KasamiCyclicAdditive.Phase.mem_cubeRootsOne.mp hu
  have hv3 := KasamiCyclicAdditive.Phase.mem_cubeRootsOne.mp hv
  set a : K := u ^ m with ha_def
  set b : K := v ^ m with hb_def
  have ha3 : a ^ 3 = 1 := by
    rw [ha_def, ← pow_mul, mul_comm, pow_mul, hu3, one_pow]
  have hb3 : b ^ 3 = 1 := by
    rw [hb_def, ← pow_mul, mul_comm, pow_mul, hv3, one_pow]
  have ha0 : a ≠ 0 := pow_ne_zero m hu0
  have hb0 : b ≠ 0 := pow_ne_zero m hv0
  set p : K := b * A / a with hp_def
  set q : K := b * B with hq_def
  have hp0 : p ≠ 0 := by simp [hp_def, hA, hb0, ha0]
  have hq0 : q ≠ 0 := by simp [hq_def, hB, hb0]
  have hpq : p ^ 3 + q ^ 3 = 1 := by
    have hp3 : p ^ 3 = A ^ 3 := by
      rw [hp_def, div_pow, mul_pow, hb3, ha3, one_mul, div_one]
    rw [hp3, hq_def]
    calc A ^ 3 + (b * B) ^ 3 = A ^ 3 + B ^ 3 := by linear_combination B ^ 3 * hb3
      _ = 1 := hAB
  obtain ⟨w, z, hwz, heq⟩ := hsolv p q hp0 hq0 hpq
  set s : K := z ^ m with hs_def
  set t : K := s / a with ht_def
  have haD : a ^ D = u := hpow u
  have hbD : b ^ D = v := hpow v
  have hsD : s ^ D = z := hpow z
  have hwD : (w ^ m) ^ D = w := hpow w
  have hat : a * t = s := by rw [ht_def]; field_simp
  have hkey : b * (A * t + B) = w ^ m := by
    have hps : b * (A * t + B) = p * s + q := by
      rw [hp_def, hq_def, ← hat]; field_simp
    rw [hps]
    linear_combination heq + (q - w ^ m) * h2
  have hut : u * t ^ D = z := by rw [← haD, ← mul_pow, hat, hsD]
  have hvt : v * (A * t + B) ^ D = w := by rw [← hbD, ← mul_pow, hkey, hwD]
  have htmem : t ∈ Finset.univ.filter
      (fun t : K => u * t ^ D + v * (A * t + B) ^ D = 1) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hut, hvt]
    linear_combination hwz
  have hne : (Finset.univ.filter
      (fun t : K => u * t ^ D + v * (A * t + B) ^ D = 1)).Nonempty := ⟨t, htmem⟩
  simpa [KasamiCyclicAdditive.Phase.rootCount] using Finset.card_pos.mpr hne

/-- `Z(ρ) ≥ 0` at a cube slope.  `KasamiCyclicAdditive.Phase.phase_to_root_count`
evaluates the correction term at the pair `(A³, B³)`, which for `ρ = A³`,
`1 + ρ = B³` is the slope of interest, as `Q²/8 * (T - c²)` with `T` the total
root count over `μ₃ × μ₃` and `c = |μ₃|`.  `one_le_rootCount` gives `c² ≤ T`. -/
theorem phaseTripleSum_re_nonneg_of_cube {k m D : ℕ} {ψ : AddChar K ℂ} {ρ : K}
    (hψ : ψ.IsPrimitive) (hm : m ≠ 0) (hD : D ≠ 0)
    (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ]) (he : 2 ^ k + 1 = 3 * m)
    (hW : KasamiCyclicAdditive.Phase.WalshCharacterFormula ψ (2 ^ k + 1) (walshCoefficient k ψ))
    (hadm : AdmissibleSlope ρ)
    {A B : K} (hA : A ≠ 0) (hAB : A ^ 3 + B ^ 3 = 1) (hrho : ρ = A ^ 3)
    (hsolv : RootEqSolvable m K) :
    0 ≤ (KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) ρ (1 + ρ)).re := by
  have hB3 : B ^ 3 = 1 + A ^ 3 := by
    have h := eq_sub_of_add_eq' hAB
    rwa [CharTwo.sub_eq_add] at h
  have hA3 : A ^ 3 ≠ 1 := by rw [← hrho]; exact hadm.2
  have hB : B ≠ 0 := by
    intro h
    apply hA3
    rw [h, zero_pow (by norm_num)] at hAB
    simpa using hAB
  have hZ := KasamiCyclicAdditive.Phase.phase_to_root_count (D := D) hψ hm hD hmD he hW hA hAB hA3
  have hpow : ∀ x : K, (x ^ m) ^ D = x := by
    intro x
    rw [← pow_mul]
    exact KasamiCyclicAdditive.Phase.pow_mul_eq_self hm hD hmD x
  set c : ℕ := (KasamiCyclicAdditive.Phase.cubeRootsOne K).card with hc
  set T : ℕ := ∑ u ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K,
      ∑ v ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K,
        KasamiCyclicAdditive.Phase.rootCount D A B u v with hT
  have hbound : c ^ 2 ≤ T := by
    have hrow : ∀ u ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K,
        c ≤ ∑ v ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K,
          KasamiCyclicAdditive.Phase.rootCount D A B u v := by
      intro u hu
      calc c = ∑ _v ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K, 1 := by simp [hc]
        _ ≤ _ := Finset.sum_le_sum fun v hv => one_le_rootCount hA hB hAB hpow hsolv hu hv
    calc c ^ 2 = ∑ _u ∈ KasamiCyclicAdditive.Phase.cubeRootsOne K, c := by simp [hc, sq]
      _ ≤ T := by rw [hT]; exact Finset.sum_le_sum hrow
  have hZ3 : KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) ρ (1 + ρ)
      = ((((Fintype.card K : ℝ) ^ 2 / 8 * ((T : ℝ) - (c : ℝ) ^ 2)) : ℝ) : ℂ) := by
    rw [hrho, ← hB3, hZ, hT, KasamiCyclicAdditive.Phase.mu3Card, ← hc]
    push_cast
    ring
  rw [hZ3, Complex.ofReal_re]
  have hle : ((c : ℝ)) ^ 2 ≤ (T : ℝ) := by exact_mod_cast hbound
  have hQ : (0 : ℝ) ≤ (Fintype.card K : ℝ) ^ 2 / 8 := by positivity
  exact mul_nonneg hQ (by linarith)

end Bridge

/-! ## Positivity of the correction term at every slope -/

section Positivity

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- `Z(ρ) ≥ 0` for every admissible slope: cube slopes by root existence,
non-cube slopes by the cube-support collapse.  In odd dimension every element
is a cube, so only the first branch occurs. -/
theorem phaseTripleSum_re_nonneg {n k m D : ℕ} {ψ : AddChar K ℂ} {ρ : K}
    (hψ : ψ.IsPrimitive) (hcard : Fintype.card K = 2 ^ n) (hkn : Nat.Coprime k n)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ])
    (he : 2 ^ k + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hW : KasamiCyclicAdditive.Phase.WalshCharacterFormula ψ (2 ^ k + 1) (walshCoefficient k ψ))
    (hadm : AdmissibleSlope ρ) :
    0 ≤ (KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) ρ (1 + ρ)).re := by
  by_cases hcube : ∃ A : K, A ^ 3 = ρ
  · obtain ⟨A, hA3⟩ := hcube
    by_cases hcube' : ∃ B : K, B ^ 3 = 1 + ρ
    · obtain ⟨B, hB3⟩ := hcube'
      have hA : A ≠ 0 := by
        rintro rfl
        exact hadm.1 (by simpa using hA3.symm)
      have hAB : A ^ 3 + B ^ 3 = 1 := by
        rw [hA3, hB3]
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination ρ * h2
      have hsolv : RootEqSolvable m K := by
        rcases Nat.even_or_odd n with hn | hn
        · exact rootEquationSolvable_even hn hkn hcard he hcop
        · exact rootEquationSolvable_odd hn hkn hcard he
      exact phaseTripleSum_re_nonneg_of_cube hψ hm hD hmD he hW hadm hA hAB hA3.symm hsolv
    · rw [phaseTripleSum_eq_zero_of_not_cube (k := k) (m := m) hψ he hW (Or.inr hcube')]
      simp
  · rw [phaseTripleSum_eq_zero_of_not_cube (k := k) (m := m) hψ he hW (Or.inl hcube)]
    simp

end Positivity

/-! ## The conjecture -/

section Conclusion

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K] [CharP K 2]

/-- **The Kasami cyclic-additive conjecture, in normalised slope form.**

Let `K = GF(2^n)`, `gcd(k, n) = 1`, `d = 4^k - 2^k + 1`, `δ(b) = (b+1)^d + b^d + 1`
and `Δ = im δ`.  Then for every `ρ ≠ 0, 1`

    #{(x,y,z) ∈ Δ³ : x + ρ y + (1+ρ) z = 0} = Q²/8 = 2^(2n-3).

The theorem is parameterized by the normalisation data `(m, D)` and by the
explicit Walsh, triple-count, and average equations.  The Walsh hypothesis
`hW` (`KasamiCyclicAdditive.Phase.WalshCharacterFormula`) can be obtained from
`DillonKashyapPhaseFormula` via `walshCharacterFormula_of_phase_formula`; the
triple-count and average hypotheses are discharged from the half-size result in
`Assembly/Reduction.lean`. -/
theorem kasami_conjecture_of_inputs {n k m D : ℕ} {ψ : AddChar K ℂ}
    (hψ : ψ.IsPrimitive) (hcard : Fintype.card K = 2 ^ n) (hkn : Nat.Coprime k n)
    (hm : m ≠ 0) (hD : D ≠ 0) (hmD : m * D ≡ 1 [MOD Fintype.card Kˣ])
    (he : 2 ^ k + 1 = 3 * m) (hcop : Nat.Coprime m (2 ^ n - 1))
    (hW : KasamiCyclicAdditive.Phase.WalshCharacterFormula ψ (2 ^ k + 1) (walshCoefficient k ψ))
    (hcount_formula : ∀ ρ : K, AdmissibleSlope ρ →
      (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8
        + (KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) ρ (1 + ρ)).re /
            (Fintype.card K : ℝ))
    (havg : (∑ ρ ∈ slopes K, (slopeTripleCount k ρ : ℝ)) / ((slopes K).card : ℝ)
      = (Fintype.card K : ℝ) ^ 2 / 8)
    (hne : (slopes K).Nonempty) :
    ∀ ρ ∈ slopes K, (slopeTripleCount k ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8 := by
  have hQ : (0 : ℝ) < (Fintype.card K : ℝ) := by
    have : 0 < Fintype.card K := Fintype.card_pos
    exact_mod_cast this
  have hmem : ∀ ρ ∈ slopes K, AdmissibleSlope ρ := by
    intro ρ hrho
    simpa [slopes, AdmissibleSlope] using hrho
  have key := forcing_of_average_and_nonneg (slopes K) hne
    (fun r => (slopeTripleCount k r : ℝ))
    (fun r => (KasamiCyclicAdditive.Phase.phaseTripleSum (walshCoefficient k ψ) r (1 + r)).re)
    ((Fintype.card K : ℝ) ^ 2 / 8) (Fintype.card K : ℝ) hQ
    (fun r hr => hcount_formula r (hmem r hr))
    havg
    (fun r hr => phaseTripleSum_re_nonneg (n := n) (k := k) (m := m) (D := D)
      hψ hcard hkn hm hD hmD he hcop hW (hmem r hr))
  exact fun ρ hrho => (key ρ hrho).1

end Conclusion

end KasamiCyclicAdditive
