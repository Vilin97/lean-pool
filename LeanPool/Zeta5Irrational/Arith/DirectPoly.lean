/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Arith.DirectBound
import LeanPool.Zeta5Irrational.Arith.IntPoly
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

import Mathlib.Tactic.NormNum.Prime

/-! # The class-wise bound for the polynomial part

For every integer `m`, `v_p(P(m)) ≥ β` where `P` is the polynomial part of
`κ ∏ (x - ζ) / ∏ (x - r)` and `β ≤ e_c - ℓ_c` for every class `c`.
-/

public section

open Finset Polynomial

namespace Zeta5Irrational

variable {p : ℕ} [hp : Fact p.Prime]

lemma prod_erase_split {f : ℤ → ℚ[X]} (S : Finset ℤ) (q : ℤ → Prop) [DecidablePred q] (r : ℤ) :
    ∏ s ∈ S.erase r, f s =
      (∏ s ∈ (S.filter q).erase r, f s) * ∏ s ∈ (S.filter (¬q ·)).erase r, f s :=
  by rw [← Finset.filter_erase, ← Finset.filter_erase, Finset.prod_filter_mul_prod_filter_not]

lemma GV_lin_comp_class (m ζ : ℤ) (h : (ζ : ZMod p) = m) :
    GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 1 := by
  rw [sub_comp, X_comp, C_comp,
    show C (m : ℚ) + C (p : ℚ) * X - C (ζ : ℚ) = C (((m - ζ : ℤ) : ℚ)) + C (p : ℚ) * X by
      push_cast; rw [C_sub]; ring]
  have h1 : VG p (((m - ζ : ℤ) : ℚ)) 1 := VG_int_one ((zmod_eq_iff_dvd (p := p)).mp h.symm)
  have h2 : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
  exact (GV.C h1).add (by simpa using GV.C_mul h2 GV.X)

lemma GV_lin_comp (m ζ : ℤ) : GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 0 := by
  rw [sub_comp, X_comp, C_comp,
    show C (m : ℚ) + C (p : ℚ) * X - C (ζ : ℚ) = C (((m - ζ : ℤ) : ℚ)) + C (p : ℚ) * X by
      push_cast; rw [C_sub]; ring]
  exact (GV.C (VG.intCast _)).add (by simpa using GV.C_mul (VG.natCast (p := p) p) GV.X)

lemma GV_numOf_comp (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (m : ℤ) :
    GV p ((numOf κ Z).comp (C (m : ℚ) + C (p : ℚ) * X)) (cnt p Z (m : ZMod p)) := by
  unfold numOf
  rw [mul_comp, C_comp, multiset_prod_comp, Multiset.map_map]
  suffices h :
    GV p
      ((Z.map ((fun q => q.comp (C (m : ℚ) + C (p : ℚ) * X)) ∘ fun ζ : ℤ => X - C (ζ : ℚ))).prod)
      (cnt p Z (m : ZMod p))
    by simpa using GV.C_mul hκ h
  induction Z using Multiset.induction_on with
  | empty => simpa [cnt] using GV.C (p := p) (VG.one (p := p))
  | cons a Z ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    unfold cnt at ih ⊢
    rw [Multiset.filter_cons]
    split_ifs with h
    · rw [Multiset.card_add, Multiset.card_singleton]
      have := (GV_lin_comp_class m a h).mul ih
      convert this using 1
      · simp [Function.comp]
      · push_cast; ring
    · rw [zero_add]
      simpa using (GV_lin_comp m a).mul ih

/-- `(x - r)(m + p z) = p (z - ρ)` with `ρ = (r - m)/p`, for `r ≡ m`. -/
lemma lin_comp_eq {m r : ℤ} (h : (p : ℤ) ∣ r - m) :
    (X - C (r : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X) =
      C (p : ℚ) * (X - C (((r - m) / p : ℤ) : ℚ)) := by
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have e : (p : ℚ) * (((r - m) / p : ℤ) : ℚ) = (r : ℚ) - m := by
    have := Int.mul_ediv_cancel' h
    exact_mod_cast this
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, e, C_sub]; ring

/-- **Class-wise bound for the polynomial part.** -/
theorem VG_polyPart_eval (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (β : ℚ) (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card)
    (m : ℤ) : VG p ((polyPart (numOf κ Z) Pl).eval (m : ℚ)) β := by
  classical
  set A := numOf κ Z with hA
  set P := polyPart A Pl with hP
  set c : ZMod p := (m : ZMod p) with hc
  set Plc := plc p Pl c with hPlc
  set Plo := Pl.filter fun r : ℤ => ¬(r : ZMod p) = c with hPlo
  set PiC := ∏ r ∈ Plc, (X - C (r : ℚ)) with hPiC
  set PiO := ∏ r ∈ Plo, (X - C (r : ℚ)) with hPiO
  have hPi : piPl Pl = PiC * PiO := by
    unfold piPl;
    rw [hPiC, hPiO, hPlc, plc, Finset.prod_filter_mul_prod_filter_not]
  set H := P * PiO + ∑ r ∈ Plo, C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ)) with hH
  set I := ∑ r ∈ Plc, C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ)) with hI
    -- the splitting identity
  have hAHI : A = PiC * H + PiO * I := by
    have hpf := partial_fractionsP A Pl
    rw [← Finset.sum_filter_add_sum_filter_not Pl (fun r : ℤ => (r : ZMod p) = c)] at hpf
    have h1 :
      ∀ r ∈ Pl.filter (fun r : ℤ => (r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiO * (C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hro : r ∉ Plo := by rw [hPlo, Finset.mem_filter]; rw [Finset.mem_filter] at hr; tauto
      rw [Finset.erase_eq_of_notMem hro]
      rw [hPlc, plc]; ring
    have h2 :
      ∀ r ∈ Pl.filter (fun r : ℤ => ¬(r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiC * (C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hrc : r ∉ Plc := by
        rw [hPlc, plc, Finset.mem_filter]; rw [Finset.mem_filter] at hr;
        tauto
      rw [show (Pl.filter fun s : ℤ => (s : ZMod p) = c).erase r = Plc by
          rw [hPlc, plc];
          exact Finset.erase_eq_of_notMem hrc]
      rw [hPiC]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
      hPi] at hpf
    have e1 : (Pl.filter fun r : ℤ => (r : ZMod p) = c) = Plc := by rw [hPlc, plc]
    have e2 : (Pl.filter fun r : ℤ => ¬(r : ZMod p) = c) = Plo := by rw [hPlo]
    rw [e1, e2] at hpf
    conv_lhs => rw [hpf]
    rw [hH, hI, hP];
    ring
      -- membership facts
  have hmemc : ∀ r ∈ Plc, r ∈ Pl ∧ (r : ZMod p) = c := fun r hr => by
    rw [hPlc, plc, Finset.mem_filter] at hr; exact hr
  have hmemo : ∀ r ∈ Plo, r ∈ Pl ∧ ¬(r : ZMod p) = c := fun r hr => by
    rw [hPlo, Finset.mem_filter] at hr; exact hr
  have hdiv : ∀ r ∈ Plc, (p : ℤ) ∣ r - m := fun r hr =>
    (zmod_eq_iff_dvd (p := p)).mp (by rw [(hmemc r hr).2, hc])
  have hndiv : ∀ r ∈ Plo, ¬(p : ℤ) ∣ m - r := fun r hr hd =>
    (hmemo r hr).2
      (by rw [hc]; exact ((zmod_eq_iff_dvd (p := p)).mpr hd).symm)
        -- Part A: `P(m) = H(m)/PiO(m) - ∑ res_r/(m - r)`
  have hfac : ∀ r ∈ Plo, ((m : ℚ) - r) ≠ 0 := fun r hr h =>
    hndiv r hr
      (by
        have : m - r = 0 := by exact_mod_cast h
        rw [this]; exact dvd_zero _)
  have hPiOm : PiO.eval (m : ℚ) = ∏ r ∈ Plo, ((m : ℚ) - r) := by rw [hPiO, eval_prod]; simp
  have hPiOne : PiO.eval (m : ℚ) ≠ 0 := by rw [hPiOm]; exact Finset.prod_ne_zero_iff.mpr hfac
  have hVGinv : ∀ r ∈ Plo, VG p ((m : ℚ) - r)⁻¹ 0 := fun r hr =>
    by
    refine (VG.inv (p := p) (r := 0) (hfac r hr) ?_).mono (by norm_num)
    rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
      padicValRat_int_eq_zero (hndiv r hr)];
    simp
  have hVGinvPiO : VG p (PiO.eval (m : ℚ))⁻¹ 0 := by
    refine (VG.inv (p := p) (r := 0) hPiOne ?_).mono (by norm_num)
    rw [hPiOm, padicValRat_finset_prod _ _ hfac]
    push_cast
    rw [Finset.sum_eq_zero fun r hr => by
        rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
          padicValRat_int_eq_zero (hndiv r hr)];
        simp]
  have hEo :
    ∀ r ∈ Plo,
      (∏ s ∈ Plo.erase r, (X - C (s : ℚ))).eval (m : ℚ) = PiO.eval (m : ℚ) * ((m : ℚ) - r)⁻¹ := by
    intro r hr
    have h := Finset.mul_prod_erase Plo (fun s : ℤ => X - C (s : ℚ)) hr
    rw [← hPiO] at h
    have h2 := congrArg (eval (m : ℚ)) h
    rw [eval_mul, eval_sub, eval_X, eval_C] at h2
    rw [← h2]; field_simp [hfac r hr]
  have hPm :
    P.eval (m : ℚ) =
      H.eval (m : ℚ) * (PiO.eval (m : ℚ))⁻¹ - ∑ r ∈ Plo, resP A Pl r * ((m : ℚ) - r)⁻¹ := by
    rw [hH, eval_add, eval_mul, eval_finsetSum]
    simp only [eval_mul, eval_C]
    rw [Finset.sum_congr rfl fun r hr => by rw [hEo r hr]]
    rw [add_mul, Finset.sum_mul]
    field_simp
    ring_nf
      -- Part B: the substitution `x = m + p z`
  set G : ℚ[X] := C (m : ℚ) + C (p : ℚ) * X with hG
  set e : ℕ := cnt p Z c with he
  set ℓ : ℕ := Plc.card with hℓ
  set ρ : ℤ → ℚ := fun r => (((r - m) / p : ℤ) : ℚ) with hρ
  set T : ℚ[X] := ∏ r ∈ Plc, (X - C (ρ r)) with hT
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hPiCcomp : PiC.comp G = C ((p : ℚ) ^ ℓ) * T := by
    rw [hPiC, Polynomial.prod_comp, Finset.prod_congr rfl fun r hr => lin_comp_eq (hdiv r hr),
      Finset.prod_mul_distrib, Finset.prod_const, ← C_pow]
  have hAcomp : A.comp G = PiC.comp G * H.comp G + PiO.comp G * I.comp G := by
    conv_lhs => rw [hAHI]
    rw [add_comp, mul_comp, mul_comp]
  have hGA : GV p (A.comp G) e := by rw [hA, he, hc]; exact GV_numOf_comp κ hκ Z m
  have hGPiO : GV p (PiO.comp G) 0 := by
    rw [hPiO, Polynomial.prod_comp]
    exact (GV.prod (p := p) Plo (r := fun _ => (0 : ℚ)) fun r _ => GV_lin_comp m r).mono (by simp)
  have hGI : GV p (I.comp G) e := by
    rw [hI, Polynomial.sum_comp]
    refine GV.sum _ fun r hr => ?_
    rw [mul_comp, C_comp, Polynomial.prod_comp]
    have hprod : GV p (∏ s ∈ Plc.erase r, (X - C (s : ℚ)).comp G) ((Plc.erase r).card) := by
      exact
        (GV.prod (p := p) (Plc.erase r) (r := fun _ => (1 : ℚ)) fun s hs =>
              GV_lin_comp_class m s (by rw [(hmemc s (Finset.mem_of_mem_erase hs)).2, hc])).mono
          (by simp)
    have hres := VG_res κ hκ Z Pl hsep (hmemc r hr).1
    have hrc : (r : ZMod p) = c := (hmemc r hr).2
    rw [hrc, ← hPlc, ← he] at hres
    have := GV.C_mul hres hprod
    refine this.mono (le_of_eq ?_)
    rw [Finset.card_erase_of_mem hr]
    have : 1 ≤ Plc.card := Finset.card_pos.mpr ⟨r, hr⟩
    push_cast [this]; ring
  have hRHS : GV p (A.comp G - PiO.comp G * I.comp G) e :=
    hGA.sub ((hGPiO.mul hGI).mono (by simp))
  set F : ℚ[X] := C ((p : ℚ) ^ (-(e : ℤ))) * (A.comp G - PiO.comp G * I.comp G) with hF
  have hFint : GV p F 0 := by
    have := GV.C_mul (VG.primePow (p := p) (-(e : ℤ))) hRHS
    refine this.mono (le_of_eq ?_); push_cast; ring
  have hFeq : F = T * (C ((p : ℚ) ^ ((ℓ : ℤ) - e)) * H.comp G) := by
    rw [hF, show A.comp G - PiO.comp G * I.comp G = PiC.comp G * H.comp G by rw [hAcomp]; ring,
      hPiCcomp]
    have hz : (p : ℚ) ^ (-(e : ℤ)) * (p : ℚ) ^ ℓ = (p : ℚ) ^ ((ℓ : ℤ) - e) := by
      rw [← zpow_natCast, ← zpow_add₀ hp0]; ring_nf
    rw [← hz, C_mul]; ring
  have hroot : ∀ x ∈ Plc.image ρ, F.eval x = 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [hFeq, eval_mul, hT, eval_prod]
    rw [Finset.prod_eq_zero hr (by simp), zero_mul]
  have hρint : ∀ x ∈ Plc.image ρ, VG p x 0 := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨r, _, rfl⟩ := hx
    exact VG.intCast _
  obtain ⟨S, hS, hFS⟩ := factor_roots (Plc.image ρ) hρint hFint hroot
  have hinj : Set.InjOn ρ Plc := by
    intro r hr s hs h
    have h1 : ((r - m) / p : ℤ) = (s - m) / p := by
      have h' : ((((r - m) / p : ℤ) : ℚ)) = (((s - m) / p : ℤ) : ℚ) := h
      exact_mod_cast h'
    have h2 := Int.ediv_mul_cancel (hdiv r hr)
    have h3 := Int.ediv_mul_cancel (hdiv s hs)
    have : r - m = s - m := by rw [← h2, ← h3, h1]
    omega
  rw [Finset.prod_image hinj, ← hT] at hFS
  have hT0 : T ≠ 0 := (monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _).ne_zero
  have hcancel : C ((p : ℚ) ^ ((ℓ : ℤ) - e)) * H.comp G = S :=
    mul_left_cancel₀ hT0 (hFeq.symm.trans hFS)
  have hGm : G.eval 0 = (m : ℚ) := by rw [hG]; simp
  have hHm : H.eval (m : ℚ) = (p : ℚ) ^ ((e : ℤ) - ℓ) * S.eval 0 := by
    have := congrArg (eval 0) hcancel
    rw [eval_mul, eval_C, eval_comp, hGm] at this
    rw [← this, ← mul_assoc, ← zpow_add₀ hp0]; ring_nf; simp
  have hVGH : VG p (H.eval (m : ℚ)) ((e : ℚ) - ℓ) := by
    rw [hHm]
    have := (VG.primePow (p := p) ((e : ℤ) - ℓ)).mul (VG.eval_zero hS)
    simpa using
      this
        -- Part C: combine
  rw [hPm]
  have hβc : β ≤ (e : ℚ) - ℓ := hβ c
  refine VG.sub ((hVGH.mul hVGinvPiO).mono (by linarith)) (VG.sum _ fun r hr => ?_)
  have hres := VG_res κ hκ Z Pl hsep (hmemo r hr).1
  have := hres.mul (hVGinv r hr)
  refine this.mono ?_
  have := hβ (r : ZMod p)
  linarith

lemma natDegree_numOf_le (κ : ℚ) (Z : Multiset ℤ) : (numOf κ Z).natDegree ≤ Z.card := by
  unfold numOf
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_multiset_prod_le (t := Z.map fun ζ : ℤ => X - C (ζ : ℚ))).trans ?_
  rw [Multiset.map_map]
  have : ∀ ζ ∈ Z, ((natDegree ∘ fun ζ : ℤ => X - C (ζ : ℚ)) ζ) = 1 := fun ζ _ =>
    natDegree_X_sub_C ((ζ : ℤ) : ℚ)
  rw [Multiset.map_congr rfl this, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul,
    mul_one]

lemma padicValNat_24 (hp5 : 5 ≤ p) : padicValNat p 24 = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h1 : p ≤ 24 := Nat.le_of_dvd (by norm_num) h
  have hpr := hp.out
  interval_cases p <;>
    first
    | omega
    | (norm_num at hpr)


/-- **The direct bound** `v_p^G(τ_X(g)) ≥ min_c (e_c - ℓ_c) - 4`. -/
theorem tauX_direct (hp5 : 5 ≤ p) (κ : ℚ) (hκ : VG p κ 0) (Z : Multiset ℤ) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (hH : ∀ r ∈ Pl, dd r < p ^ 2) (hdeg : Z.card - Pl.card + 1 < p ^ 2) (β : ℚ)
    (hβ : ∀ c : ZMod p, β ≤ (cnt p Z c : ℚ) - (plc p Pl c).card) :
    GV p (tauX (numOf κ Z) Pl) (β - 4) := by
  unfold tauX
  refine GV.add (GV.C ?_) (GV.sum _ fun r hr => ?_)
  · have hd : (polyPart (numOf κ Z) Pl).natDegree ≤ Z.card - Pl.card :=
      (natDegree_polyPart_le _ _).trans (Nat.sub_le_sub_right (natDegree_numOf_le κ Z) _)
    have h :=
      tau_bound (p := p) hd (β := β)
        (fun m _ => by
          have := VG_polyPart_eval κ hκ Z Pl hsep β hβ (m : ℤ)
          simpa using this)
    have hlog : Nat.log p (Z.card - Pl.card + 1) ≤ 1 :=
      Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow (by omega) hdeg)
    rw [padicValNat_24 hp5] at h
    refine h.mono ?_
    have : (Nat.log p (Z.card - Pl.card + 1) : ℚ) ≤ 1 := by exact_mod_cast hlog
    push_cast; linarith
  · have hres := VG_res κ hκ Z Pl hsep hr
    have hH5 : GV p (C (H5 (dd r)) - X) (-5) :=
      (GV.C (VG_H5 (hH r hr))).sub (GV.X.mono (by norm_num))
    refine (GV.C_mul hres hH5).mono ?_
    have := hβ (r : ZMod p)
    linarith

end Zeta5Irrational
