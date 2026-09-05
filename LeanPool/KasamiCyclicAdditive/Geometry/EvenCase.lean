/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import LeanPool.KasamiCyclicAdditive.Geometry.RootEquation
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.IncidenceChart
import LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Quotient
import LeanPool.KasamiCyclicAdditive.Geometry.FrobeniusAnnihilator
import LeanPool.KasamiCyclicAdditive.Geometry.BaseChange

/-!
# The even-dimensional root-existence branch: the quotient-first bridge

The quotient-first route to `RootEqSolvable` in even dimension.

**The route.** Let `K = F_{2^n}` with `n` even, target `(p,q)` with `p,q ≠ 0`.

1. `PointFrobenius.exists_gMap_preimage` inverts the prime-to-3 factor `G` on
   `E(K)` directly (no algebraic closure), producing `Y` with
   `G(Y) = t3 - P`.
2. `Y` is not `3`-torsion (since `t3 - P` isn't), so `Y = (x,y)` with `x,y ≠ 0`.
3. Base-change `(x,y)` to `F = AlgebraicClosure K`.
4. Pick any cube root `W` of `(x+1)/(x+y)` in `F` and build `T` as in
   `FermatCubic.explicit_quotient_coordinates`: this gives a point `Q = (W,T)`
   with `Q + π Q = (x,y)_F`, i.e. `Q` is a preimage of `(x,y)_F` under the
   "quotient" map `id + π`.
5. Since `G` and `1 + π` commute (both are polynomials in `π`), and `G`
   transports along the base-change map `basePt K F` (which itself commutes
   with `π`), `(1 + π)(G(Q)) = G(Q + π Q) = G((x,y)_F) = (t3 - P)_F`. Combined
   with the abstract factorization `(1+π) ∘ G = 1 + π^k`
   (`Isogeny.gMap_factor`), this gives `(1 + π^k) Q = t3 - P` over `F`, i.e.
   `phi k W T = P` over `F`.
6. The Frobenius-twist relation `π^n Q = Q + ptInf α` needed by
   `exists_twisted_root_equation` follows from `Q + π Q` being `K`-rational (hence fixed by the
   `n`-th Frobenius power) together with `π^n` commuting with `1 + π`: this
   puts `π^n Q - Q` in `ker(1+π)`, which is exactly the three points at
   infinity (`frobFixed_eq_ptInf`, a small self-contained restatement that
   needs no kernel-split machinery).
7. `exists_twisted_root_equation` gives the ambient twisted-root equation, and since
   `W^3, T^3` were built from `K`-rational data *before* the cube root was
   chosen, they are already `algebraMap`-images of elements of `K` — no
   fixed-field descent theorem is needed.
-/

open KasamiCyclicAdditive.FermatCubic KasamiCyclicAdditive.PointFrobenius WeierstrassCurve

namespace KasamiCyclicAdditive

namespace EvenAssembly

/-- If `C` is fixed by `-π` (i.e. `C + π C = 0`), then `C` is one of the three
points at infinity: `ker(1 + π) = K0`. -/
theorem frobFixed_eq_ptInf {F : Type*} [Field F] [DecidableEq F] [CharP F 2]
    {C : (fer F).toAffine.Point} (hC : C + frobPt F C = 0) :
    ∃ a : F, ∃ ha : a ^ 3 = 1, C = ptInf a ha := by
  rcases point_repr C with rfl | ⟨a, ha, rfl⟩ | ⟨w, t, h, rfl⟩
  · exact ⟨1, one_pow 3, (ptInf_one (K := F)).symm⟩
  · exact ⟨a, ha, rfl⟩
  · exfalso
    rw [add_comm] at hC
    have hneg : frobPt F (pt w t h) = -(pt w t h) := eq_neg_of_add_eq_zero_left hC
    have hneg' : (frobEnd F ^ 1) (pt w t h) = -(pt w t h) := by rwa [pow_one]
    have hk : KasamiCyclicAdditive.FermatCubicFrobenius.IsKernelPoint 1 w t 1 :=
      (isKernelPoint_iff h).mpr hneg'
    have hpt : KasamiCyclicAdditive.FermatCubicFrobenius.IsPoint w t (1 : F) := by
      refine ⟨?_, by linear_combination h⟩
      rintro ⟨-, -, hz⟩
      exact one_ne_zero hz
    have hz := (KasamiCyclicAdditive.FermatCubicFrobenius.geometric_kernel_one_add_frobenius
      (CharTwo.two_eq_zero : (2 : F) = 0) hpt).mp hk
    exact one_ne_zero hz

/-- A point that is not `3`-torsion is affine, with both coordinates nonzero. -/
private lemma exists_pt_of_not_three_torsion {K : Type*} [Field K] [DecidableEq K] [CharP K 2]
    {Y : (fer K).toAffine.Point} (hY3 : (3 : ℤ) • Y ≠ 0) :
    ∃ (x y : K) (h : x ^ 3 + y ^ 3 = 1), x ≠ 0 ∧ y ≠ 0 ∧ Y = pt x y h := by
  rcases point_repr Y with rfl | ⟨α, hα, rfl⟩ | ⟨x0, y0, hxy0, rfl⟩
  · exact absurd (by simp : (3 : ℤ) • (0 : (fer K).toAffine.Point) = 0) hY3
  · exact absurd (by exact_mod_cast three_torsion_ptInf hα) hY3
  · refine ⟨x0, y0, hxy0, ?_, ?_, rfl⟩
    · intro hc
      exact hY3 (by exact_mod_cast (three_torsion_pt_iff hxy0).mpr (Or.inl hc))
    · intro hc
      exact hY3 (by exact_mod_cast (three_torsion_pt_iff hxy0).mpr (Or.inr hc))

/-- If `Q + π Q` is fixed by `π^n`, then `π^n Q - Q` lies in the kernel of `1 + π`. -/
private lemma frobEnd_pow_sub_mem_kernel {F : Type*} [Field F] [DecidableEq F] [CharP F 2]
    {n : ℕ} {Q : (fer F).toAffine.Point}
    (hfix : (frobEnd F ^ n) (Q + frobPt F Q) = Q + frobPt F Q) :
    (frobEnd F ^ n) Q - Q + frobPt F ((frobEnd F ^ n) Q - Q) = 0 := by
  have hcommuteN : (frobEnd F ^ n) (frobPt F Q) = frobPt F ((frobEnd F ^ n) Q) := by
    change (frobEnd F ^ n) (frobEnd F Q) = frobEnd F ((frobEnd F ^ n) Q)
    have heq : (frobEnd F ^ n * frobEnd F) Q = (frobEnd F * frobEnd F ^ n) Q := by
      rw [← pow_succ, ← pow_succ']
    exact heq
  have hexpand : (frobEnd F ^ n) (Q + frobPt F Q)
      = (frobEnd F ^ n) Q + (frobEnd F ^ n) (frobPt F Q) := map_add _ _ _
  rw [hexpand, hcommuteN] at hfix
  have heq : (frobEnd F ^ n) Q - Q + frobPt F ((frobEnd F ^ n) Q - Q)
      = ((frobEnd F ^ n) Q + frobPt F ((frobEnd F ^ n) Q)) - (Q + frobPt F Q) := by
    rw [map_sub]; abel
  rw [heq, hfix, sub_self]

end EvenAssembly

open EvenAssembly

/-- **The even branch: the quotient-first bridge.**  For even `n` the twisted
root equation is solvable at every affine Fermat target with nonzero
coordinates, by the route set out in the module docstring. -/
theorem rootEquationSolvable_even {K : Type*} [Field K] [Fintype K] [CharP K 2]
    {n k m : ℕ} (hn : Even n) (hkn : Nat.Coprime k n)
    (hcard : Fintype.card K = 2 ^ n) (he : 2 ^ k + 1 = 3 * m)
    (hm : Nat.Coprime m (2 ^ n - 1)) :
    RootEqSolvable m K := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have := Classical.decEq (AlgebraicClosure K)
  set F := AlgebraicClosure K with hFdef
  have hk : Odd k := by
    rcases Nat.even_or_odd k with hke | hko
    · exfalso
      have h2k : 2 ∣ Nat.gcd k n := Nat.dvd_gcd hke.two_dvd hn.two_dvd
      rw [hkn.gcd_eq_one] at h2k
      omega
    · exact hko
  intro p q hp hq hpq
  set P : (fer K).toAffine.Point := pt p q hpq with hPdef
  set R : (fer K).toAffine.Point := t3 K - P with hRdef
  -- Step 1: invert `G` on `E(K)`.
  obtain ⟨a, b, r, Y, hkr, hab1, hab2, hY⟩ :=
    PointFrobenius.exists_gMap_preimage hn hk hcard he hm R
  -- Step 2: `Y` is not `3`-torsion.
  have hP3 : (3 : ℤ) • P ≠ 0 := by
    intro hz
    have hz' : (3 : ℕ) • P = 0 := by exact_mod_cast hz
    rcases (three_torsion_pt_iff hpq).mp hz' with h | h
    · exact hp h
    · exact hq h
  have hR3 : (3 : ℤ) • R ≠ 0 := by
    have hT3 : (3 : ℤ) • t3 K = 0 := by
      exact_mod_cast (three_torsion_t3 (K := K))
    rw [hRdef, smul_sub, hT3, zero_sub, neg_ne_zero]
    exact hP3
  have hY3 : (3 : ℤ) • Y ≠ 0 := by
    intro hz
    apply hR3
    rw [← hY, ← Isogeny.gMap_zsmul, hz]
    simp [Isogeny.gMap]
  obtain ⟨x0, y0, hxy0, hx0, hy0, rfl⟩ := exists_pt_of_not_three_torsion hY3
  -- Step 3: base-change to `F`.
  have hx0F : algebraMap K F x0 ≠ 0 := by
    intro hc; exact hx0 ((algebraMap K F).injective (by rw [hc, map_zero]))
  have hy0F : algebraMap K F y0 ≠ 0 := by
    intro hc; exact hy0 ((algebraMap K F).injective (by rw [hc, map_zero]))
  have hxy0F : (algebraMap K F x0) ^ 3 + (algebraMap K F y0) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ← map_add, hxy0, map_one]
  -- Step 4: choose a cube root and build `Q`.
  obtain ⟨W, hW⟩ : ∃ W : F,
      W ^ 3 = (algebraMap K F x0 + 1) / (algebraMap K F x0 + algebraMap K F y0) :=
    IsAlgClosed.exists_pow_nat_eq _ (by norm_num)
  obtain ⟨hT3cube, hWTsum, hDne, hXeq, hYeq⟩ :=
    FermatCubic.explicit_quotient_coordinates hx0F hy0F hxy0F hW
  set T : F := FermatCubic.quotientT (algebraMap K F x0) (algebraMap K F y0) W with hTdef
  set Q : (fer F).toAffine.Point := pt W T hWTsum with hQdef
  have hfrob2 : (W ^ 2) ^ 3 + (T ^ 2) ^ 3 = 1 := frob_fermat hWTsum 1
  have hQfrobY : Q + frobPt F Q = basePt K F (pt x0 y0 hxy0) := by
    rw [hQdef, frobPt_pt hWTsum, add_pt hWTsum hfrob2 hDne, basePt_pt]
    exact pt_congr _ _ hXeq hYeq
  -- Step 5: naturality of `gMap` under `basePt`, plus the abstract factorization,
  -- give `(1 + π_F^k) Q = t3 F - P_F`.
  have hpqF : (algebraMap K F p) ^ 3 + (algebraMap K F q) ^ 3 = 1 := by
    rw [← map_pow, ← map_pow, ← map_add, hpq, map_one]
  set PF : (fer F).toAffine.Point := pt (algebraMap K F p) (algebraMap K F q) hpqF with hPFdef
  have hbaseR : basePt K F R = t3 F - PF := by
    rw [hRdef, map_sub, basePt_t3, hPdef, basePt_pt]
  have hstep1 : basePt K F R = Isogeny.gMap (frobPt F) a b (Q + frobPt F Q) := by
    rw [← hY, basePt_gMap, hQfrobY]
  have hI : Isogeny.gMap (frobPt F) a b Q + frobPt F (Isogeny.gMap (frobPt F) a b Q)
      = t3 F - PF := by
    rw [Isogeny.gMap_add_map, ← hstep1, hbaseR]
  have hII := Isogeny.gMap_factor (frobPt F) (r := r) (a := a) (b := b)
    (fun x => frobPt_frobPt (K := F) x) hab1 hab2 Q
  rw [← hkr] at hII
  have hIII : Q + Isogeny.piIter (frobPt F) k Q = t3 F - PF := by rw [hII, hI]
  rw [piIter_frobPt] at hIII
  have hPhi : phi k W T hWTsum = PF := by
    rw [phi, ← frobEnd_pow_pt k hWTsum, ← hQdef, hIII]
    abel
  -- `W, T ≠ 0` from the Hessian denominator.
  have hWT0 : W * T ≠ 0 := by
    intro hc
    apply hDne
    change W * T + W ^ 2 * T ^ 2 = 0
    rw [show W ^ 2 * T ^ 2 = (W * T) ^ 2 by ring, hc]; ring
  have hW0 : W ≠ 0 := left_ne_zero_of_mul hWT0
  have hT0 : T ≠ 0 := right_ne_zero_of_mul hWT0
  -- Step 6-7: the Frobenius-twist relation.
  have hx0fix : x0 ^ 2 ^ n = x0 := by
    have h := FiniteField.pow_card x0; rwa [hcard] at h
  have hy0fix : y0 ^ 2 ^ n = y0 := by
    have h := FiniteField.pow_card y0; rwa [hcard] at h
  have hYfix : (frobEnd F ^ n) (basePt K F (pt x0 y0 hxy0)) = basePt K F (pt x0 y0 hxy0) := by
    rw [basePt_pt, frobEnd_pow_pt]
    refine pt_congr _ _ ?_ ?_
    · rw [← map_pow, hx0fix]
    · rw [← map_pow, hy0fix]
  have hQYfix : (frobEnd F ^ n) (Q + frobPt F Q) = Q + frobPt F Q := by
    rw [hQfrobY]; exact hYfix
  have hker := frobEnd_pow_sub_mem_kernel hQYfix
  obtain ⟨α, hα, hCeq⟩ := frobFixed_eq_ptInf hker
  have hB3eq : pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat hWTsum n)
      = pt W T hWTsum + ptInf α hα := by
    have hstep : (frobEnd F ^ n) Q = Q + ptInf α hα := by
      have : (frobEnd F ^ n) Q - Q = ptInf α hα := hCeq
      rw [← this]; abel
    rw [frobEnd_pow_pt, hQdef] at hstep
    exact hstep
  have hB3 : ∃ (c : F) (hc : c ^ 3 = 1),
      pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat hWTsum n) = pt W T hWTsum + ptInf c hc :=
    ⟨α, hα, hB3eq⟩
  -- `phi k W T` is not 3-torsion
  have hB5 : (3 : ℕ) • phi k W T hWTsum ≠ 0 := by
    rw [hPhi]
    intro hz
    rcases (three_torsion_pt_iff hpqF).mp hz with h | h
    · exact hp ((algebraMap K F).injective (by rw [h, map_zero]))
    · exact hq ((algebraMap K F).injective (by rw [h, map_zero]))
  -- Step 8: apply the twisted root equation and descend.
  obtain ⟨p', q', hpq', hPhi', hp', hq', hroot⟩ :=
    exists_twisted_root_equation hWTsum hW0 hT0 hkn hB3 hB5
  have hmatch : pt p' q' hpq' = PF := hPhi'.symm.trans hPhi
  rw [hPFdef] at hmatch
  obtain ⟨hpe, hqe⟩ := pt_inj hmatch
  subst hpe; subst hqe
  set w0 : K := (x0 + 1) / (x0 + y0) with hw0def
  set z0 : K := (y0 + 1) / (x0 + y0) with hz0def
  have hWcube : W ^ 3 = algebraMap K F w0 := by
    rw [hW, hw0def, map_div₀, map_add, map_add, map_one]
  have hTcube : T ^ 3 = algebraMap K F z0 := by
    rw [hT3cube, hz0def, map_div₀, map_add, map_add, map_one]
  have hwz0 : w0 + z0 = 1 :=
    (algebraMap K F).injective (by rw [map_add, map_one, ← hWcube, ← hTcube]; exact hWTsum)
  refine ⟨w0, z0, hwz0, ?_⟩
  apply (algebraMap K F).injective
  rw [map_add, map_pow, map_mul, map_pow, ← hWcube, ← hTcube]
  rw [he, pow_mul, pow_mul] at hroot
  exact hroot

end KasamiCyclicAdditive
