/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import LeanPool.Zeta32.Arith.Local.Val
public import LeanPool.Zeta5Irrational.SimplePoles

/-!
# Class-wise partial fractions

For a numerator `A ∈ ℚ[x]` and a finite set `Pl ⊆ ℤ` of simple poles:

* `polyPart A Pl = A /ₘ ∏ (x - r)`, `resP A Pl r = A(r) / ∏_{s ≠ r} (r - s)`;
* `partial_fractionsP` : `A = polyPart · ∏ (x - r) + ∑_r res_r ∏_{s ≠ r} (x - s)`;
* `Adm p A e` : for every integer `m`, `A(m + p x)` has Gauss valuation `≥ e (m mod p)`;
* `VG_res` : `v_p(res_r) ≥ e_c - ℓ_c + 1` (`c` the class of `r`, `ℓ_c` the number of poles in it);
* `VG_polyPart_eval` : a class-wise lower bound for the values of the polynomial part at integers.
-/

public section

-- adapted from mo271/Zeta5@f19a196:Apery/Arith/PoleFun.lean,
-- .../Apery/Arith/DirectBound.lean and .../Apery/Arith/DirectPoly.lean
-- (mo271/Zeta5 by Moritz Firsching, Apache-2.0).
-- Changes: the numerator `κ ∏ (x - ζ)` is replaced by any polynomial satisfying the class-count
-- predicate `Adm`; the polynomial-part bound is refined (`VG_polyPart_eval`) so that poles in
-- classes other than the evaluation class only need the residue bound.

open Finset Polynomial

namespace Zeta32.Arith.Local

export Zeta5Irrational (piPl piPl_monic natDegree_piPl polyPart resP lagrange_basis_eq
  partial_fractionsP natDegree_polyPart_le)

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Integer valuations -/
omit hp in
lemma zmod_eq_iff_dvd {a b : ℤ} : (a : ZMod p) = b ↔ (p : ℤ) ∣ a - b := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; exact sub_eq_zero.symm

lemma VG_int_one {z : ℤ} (h : (p : ℤ) ∣ z) : VG p (z : ℚ) 1 := by
  by_cases hz : z = 0
  · left; simp [hz]
  right
  rw [padicValRat.of_int]
  have := (padicValInt_dvd_iff (p := p) 1 z).mp (by simpa using h)
  rcases this with h | h
  · exact absurd h hz
  · exact_mod_cast h

lemma padicValRat_int_eq_zero {z : ℤ} (h : ¬ (p : ℤ) ∣ z) : padicValRat p (z : ℚ) = 0 := by
  rw [padicValRat.of_int]
  have hz : z ≠ 0 := fun h' => h (h' ▸ dvd_zero _)
  by_contra hne
  have h1 : 1 ≤ padicValInt p z := Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne)
  exact h (by simpa using (padicValInt_dvd_iff (p := p) 1 z).mpr (Or.inr h1))

lemma padicValRat_int_le_one {z : ℤ} (h2 : ¬ (p : ℤ) ^ 2 ∣ z) : padicValRat p (z : ℚ) ≤ 1 := by
  rw [padicValRat.of_int]
  by_contra hne
  rw [not_le] at hne
  have : 2 ≤ padicValInt p z := by exact_mod_cast hne
  have hz : z ≠ 0 := by rintro rfl; simp at hne
  exact h2 ((padicValInt_dvd_iff (p := p) 2 z).mpr (Or.inr this))

/-! ### The class-count predicate -/

/-- `A(m + p x)` has Gauss valuation `≥ e (m mod p)` for every integer `m`. -/
def Adm (p : ℕ) (A : ℚ[X]) (e : ZMod p → ℤ) : Prop :=
  ∀ m : ℤ, GV p (A.comp (C (m : ℚ) + C (p : ℚ) * X)) (e (m : ZMod p))

namespace Adm

omit hp in
lemma mono {A : ℚ[X]} {e e' : ZMod p → ℤ} (h : Adm p A e) (he : ∀ c, e' c ≤ e c) :
    Adm p A e' := fun m => (h m).mono (by exact_mod_cast he _)

omit hp in
lemma one : Adm p 1 0 := fun m => by
  rw [one_comp]
  simpa using GV.C (p := p) (VG.one (p := p))

lemma mul {A B : ℚ[X]} {e e' : ZMod p → ℤ} (hA : Adm p A e) (hB : Adm p B e') :
    Adm p (A * B) (e + e') := fun m => by
  rw [mul_comp]
  have := (hA m).mul (hB m)
  simpa [Pi.add_apply] using this

lemma prod {ι : Type*} (s : Finset ι) (A : ι → ℚ[X]) (e : ι → ZMod p → ℤ)
    (h : ∀ i ∈ s, Adm p (A i) (e i)) : Adm p (∏ i ∈ s, A i) (fun c => ∑ i ∈ s, e i c) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine this.mono fun c => ?_
    rw [Finset.sum_insert ha]; rfl

lemma pow {A : ℚ[X]} {e : ZMod p → ℤ} (h : Adm p A e) (k : ℕ) :
    Adm p (A ^ k) (fun c => k * e c) := by
  induction k with
  | zero =>
    rw [pow_zero]
    exact (one : Adm p 1 0).mono fun c => by simp
  | succ k ih =>
    rw [pow_succ]
    refine (ih.mul h).mono fun c => ?_
    simp only [Pi.add_apply]; push_cast; ring_nf; rfl

lemma X_sub_C (ζ : ℤ) :
    Adm p (X - C (ζ : ℚ)) (fun c => if (ζ : ZMod p) = c then 1 else 0) := fun m => by
  rw [sub_comp, X_comp, C_comp, show C (m : ℚ) + C (p : ℚ) * X - C (ζ : ℚ) =
    C (((m - ζ : ℤ) : ℚ)) + C (p : ℚ) * X by push_cast; rw [C_sub]; ring]
  dsimp only
  split_ifs with h
  · have h1 : VG p (((m - ζ : ℤ) : ℚ)) 1 := VG_int_one ((zmod_eq_iff_dvd (p := p)).mp h.symm)
    have h2 : VG p (p : ℚ) 1 := by simpa using VG.primePow (p := p) 1
    have := (GV.C h1).add (by simpa using GV.C_mul h2 GV.X)
    simpa using this
  · have := (GV.C (VG.intCast (p := p) (m - ζ))).add
      (by simpa using GV.C_mul (VG.natCast (p := p) p) GV.X)
    simpa using this

omit hp in
lemma eval {A : ℚ[X]} {e : ZMod p → ℤ} (h : Adm p A e) (x : ℤ) :
    VG p (A.eval (x : ℚ)) (e (x : ZMod p)) := by
  have h1 := VG.eval_zero (h x)
  rwa [eval_comp, eval_add, eval_C, eval_mul, eval_C, eval_X, mul_zero, add_zero] at h1

end Adm

/-! ### Residues -/

/-- Poles in the class `c`. -/
def plc (p : ℕ) (Pl : Finset ℤ) (c : ZMod p) : Finset ℤ := Pl.filter fun r : ℤ => (r : ZMod p) = c

/-- Poles in the same class differ by exactly one power of `p`. -/
@[expose]
def Sep (p : ℕ) (Pl : Finset ℤ) : Prop :=
  ∀ r ∈ Pl, ∀ s ∈ Pl, r ≠ s → (r : ZMod p) = s → ¬ (p : ℤ) ^ 2 ∣ r - s

lemma padicValRat_denom_le (Pl : Finset ℤ) (hsep : Sep p Pl) {r : ℤ} (hr : r ∈ Pl) :
    (padicValRat p (∏ s ∈ Pl.erase r, ((r : ℚ) - s)) : ℚ) ≤ (plc p Pl r).card - 1 := by
  rw [padicValRat_finset_prod _ _ (fun s hs => by
    rw [Finset.mem_erase] at hs
    exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm))]
  have hterm : ∀ s ∈ Pl.erase r, (padicValRat p ((r : ℚ) - s) : ℚ) ≤
      if (s : ZMod p) = r then 1 else 0 := by
    intro s hs
    rw [Finset.mem_erase] at hs
    have e : ((r : ℚ) - s) = ((r - s : ℤ) : ℚ) := by push_cast; ring
    rw [e]
    split_ifs with h
    · exact_mod_cast padicValRat_int_le_one (hsep r hr s hs.2 (Ne.symm hs.1) h.symm)
    · rw [padicValRat_int_eq_zero (fun hd => h ((zmod_eq_iff_dvd (p := p)).mpr
        (by rw [← neg_sub]; exact (dvd_neg).mpr hd)))]
      simp
  push_cast
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul, mul_one]
  have hcard : ((Pl.erase r).filter fun s : ℤ => (s : ZMod p) = r) = (plc p Pl r).erase r := by
    unfold plc; rw [Finset.filter_erase]
  rw [hcard, Finset.card_erase_of_mem (by unfold plc; simp [hr])]
  have : 1 ≤ (plc p Pl r).card := Finset.card_pos.mpr ⟨r, by unfold plc; simp [hr]⟩
  push_cast [this]
  linarith

/-- **Residue bound**: `v_p(res_r) ≥ e_c - ℓ_c + 1` for the class `c` of `r`. -/
theorem VG_res {A : ℚ[X]} {e : ZMod p → ℤ} (hA : Adm p A e) (Pl : Finset ℤ) (hsep : Sep p Pl)
    {r : ℤ} (hr : r ∈ Pl) :
    VG p (resP A Pl r) ((e (r : ZMod p) : ℚ) - (plc p Pl r).card + 1) := by
  unfold resP
  rw [div_eq_mul_inv]
  have hD : ∏ s ∈ Pl.erase r, ((r : ℚ) - s) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s hs => by
    rw [Finset.mem_erase] at hs
    exact sub_ne_zero.mpr (by exact_mod_cast hs.1.symm)
  have h1 := hA.eval r
  have h2 := VG.inv (p := p)  (padicValRat_denom_le Pl hsep hr)
  convert h1.mul h2 using 1
  ring

/-! ### The polynomial part -/
lemma prod_erase_split {f : ℤ → ℚ[X]} (S : Finset ℤ) (q : ℤ → Prop) [DecidablePred q] (r : ℤ) :
    ∏ s ∈ S.erase r, f s =
      (∏ s ∈ (S.filter q).erase r, f s) * ∏ s ∈ (S.filter (¬ q ·)).erase r, f s := by
  rw [← Finset.filter_erase, ← Finset.filter_erase, Finset.prod_filter_mul_prod_filter_not]

lemma GV_lin_comp_class (m ζ : ℤ) (h : (ζ : ZMod p) = m) :
    GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 1 := by
  have := Adm.X_sub_C (p := p) ζ m
  simpa [h] using this

lemma GV_lin_comp (m ζ : ℤ) : GV p ((X - C (ζ : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X)) 0 := by
  have := Adm.X_sub_C (p := p) ζ m
  refine this.mono ?_
  dsimp only
  split_ifs <;> norm_num

omit hp in
/-- `(x - r)(m + p z) = p (z - ρ)` with `ρ = (r - m)/p`, for `r ≡ m`. -/
lemma lin_comp_eq {m r : ℤ} (h : (p : ℤ) ∣ r - m) :
    (X - C (r : ℚ)).comp (C (m : ℚ) + C (p : ℚ) * X) =
      C (p : ℚ) * (X - C (((r - m) / p : ℤ) : ℚ)) := by
  have e : (p : ℚ) * (((r - m) / p : ℤ) : ℚ) = (r : ℚ) - m := by
    have := Int.mul_ediv_cancel' h
    exact_mod_cast this
  rw [sub_comp, X_comp, C_comp, mul_sub, ← C_mul, e, C_sub]; ring

/-- **Class-wise bound for the polynomial part** at an integer `m`: poles in the class of `m`
enter through `e_c - ℓ_c`, poles in the other classes only through their residues. -/
theorem VG_polyPart_eval {A : ℚ[X]} {e : ZMod p → ℤ} (hA : Adm p A e) (Pl : Finset ℤ)
    (hsep : Sep p Pl) (m : ℤ) (β : ℚ)
    (hβm : β ≤ (e (m : ZMod p) : ℚ) - (plc p Pl m).card)
    (hβo : ∀ r ∈ Pl, ¬ (r : ZMod p) = m → β ≤ (e (r : ZMod p) : ℚ) - (plc p Pl r).card + 1) :
    VG p ((polyPart A Pl).eval (m : ℚ)) β := by
  classical
  set P := polyPart A Pl with hP
  set c : ZMod p := (m : ZMod p) with hc
  set Plc := plc p Pl c with hPlc
  set Plo := Pl.filter fun r : ℤ => ¬ (r : ZMod p) = c with hPlo
  set PiC := ∏ r ∈ Plc, (X - C (r : ℚ)) with hPiC
  set PiO := ∏ r ∈ Plo, (X - C (r : ℚ)) with hPiO
  have hPi : piPl Pl = PiC * PiO := by
    unfold piPl; rw [hPiC, hPiO, hPlc, plc, Finset.prod_filter_mul_prod_filter_not]
  set H := P * PiO + ∑ r ∈ Plo, C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ)) with hH
  set I := ∑ r ∈ Plc, C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ)) with hI
  -- the splitting identity
  have hAHI : A = PiC * H + PiO * I := by
    have hpf := partial_fractionsP A Pl
    rw [← Finset.sum_filter_add_sum_filter_not Pl (fun r : ℤ => (r : ZMod p) = c)] at hpf
    have h1 : ∀ r ∈ Pl.filter (fun r : ℤ => (r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiO * (C (resP A Pl r) * ∏ s ∈ Plc.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hro : r ∉ Plo := by
        rw [hPlo, Finset.mem_filter]; rw [Finset.mem_filter] at hr; tauto
      rw [Finset.erase_eq_of_notMem hro]
      rw [hPlc, plc]; ring
    have h2 : ∀ r ∈ Pl.filter (fun r : ℤ => ¬ (r : ZMod p) = c),
        C (resP A Pl r) * ∏ s ∈ Pl.erase r, (X - C (s : ℚ)) =
          PiC * (C (resP A Pl r) * ∏ s ∈ Plo.erase r, (X - C (s : ℚ))) := by
      intro r hr
      rw [prod_erase_split Pl (fun s : ℤ => (s : ZMod p) = c) r]
      have hrc : r ∉ Plc := by
        rw [hPlc, plc, Finset.mem_filter]; rw [Finset.mem_filter] at hr; tauto
      rw [show (Pl.filter fun s : ℤ => (s : ZMod p) = c).erase r = Plc by
        rw [hPlc, plc]; exact Finset.erase_eq_of_notMem hrc]
      rw [hPiC]; ring
    rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, ← Finset.mul_sum, ← Finset.mul_sum,
      hPi] at hpf
    have e1 : (Pl.filter fun r : ℤ => (r : ZMod p) = c) = Plc := by rw [hPlc, plc]
    have e2 : (Pl.filter fun r : ℤ => ¬ (r : ZMod p) = c) = Plo := by rw [hPlo]
    rw [e1, e2] at hpf
    conv_lhs => rw [hpf]
    rw [hH, hI, hP]; ring
  -- membership facts
  have hmemc : ∀ r ∈ Plc, r ∈ Pl ∧ (r : ZMod p) = c := fun r hr => by
    rw [hPlc, plc, Finset.mem_filter] at hr; exact hr
  have hmemo : ∀ r ∈ Plo, r ∈ Pl ∧ ¬ (r : ZMod p) = c := fun r hr => by
    rw [hPlo, Finset.mem_filter] at hr; exact hr
  have hdiv : ∀ r ∈ Plc, (p : ℤ) ∣ r - m := fun r hr =>
    (zmod_eq_iff_dvd (p := p)).mp (by rw [(hmemc r hr).2, hc])
  have hndiv : ∀ r ∈ Plo, ¬ (p : ℤ) ∣ m - r := fun r hr hd =>
    (hmemo r hr).2 (by rw [hc]; exact ((zmod_eq_iff_dvd (p := p)).mpr hd).symm)
  -- Part A: `P(m) = H(m)/PiO(m) - ∑ res_r/(m - r)`
  have hfac : ∀ r ∈ Plo, ((m : ℚ) - r) ≠ 0 := fun r hr h => hndiv r hr (by
    have : m - r = 0 := by exact_mod_cast h
    rw [this]; exact dvd_zero _)
  have hPiOm : PiO.eval (m : ℚ) = ∏ r ∈ Plo, ((m : ℚ) - r) := by
    rw [hPiO, eval_prod]; simp
  have hPiOne : PiO.eval (m : ℚ) ≠ 0 := by
    rw [hPiOm]; exact Finset.prod_ne_zero_iff.mpr hfac
  have hVGinv : ∀ r ∈ Plo, VG p ((m : ℚ) - r)⁻¹ 0 := fun r hr => by
    refine (VG.inv (p := p) (r := 0)  ?_).mono (by norm_num)
    rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
      padicValRat_int_eq_zero (hndiv r hr)]; simp
  have hVGinvPiO : VG p (PiO.eval (m : ℚ))⁻¹ 0 := by
    refine (VG.inv (p := p) (r := 0)  ?_).mono (by norm_num)
    rw [hPiOm, padicValRat_finset_prod _ _ hfac]
    push_cast
    rw [Finset.sum_eq_zero fun r hr => by
      rw [show ((m : ℚ) - r) = ((m - r : ℤ) : ℚ) by push_cast; ring,
        padicValRat_int_eq_zero (hndiv r hr)]; simp]
  have hEo : ∀ r ∈ Plo, (∏ s ∈ Plo.erase r, (X - C (s : ℚ))).eval (m : ℚ) =
      PiO.eval (m : ℚ) * ((m : ℚ) - r)⁻¹ := by
    intro r hr
    have h := Finset.mul_prod_erase Plo (fun s : ℤ => X - C (s : ℚ)) hr
    rw [← hPiO] at h
    have h2 := congrArg (eval (m : ℚ)) h
    rw [eval_mul, eval_sub, eval_X, eval_C] at h2
    rw [← h2]; field_simp [hfac r hr]
  have hPm : P.eval (m : ℚ) = H.eval (m : ℚ) * (PiO.eval (m : ℚ))⁻¹ -
      ∑ r ∈ Plo, resP A Pl r * ((m : ℚ) - r)⁻¹ := by
    rw [hH, eval_add, eval_mul, eval_finsetSum]
    simp only [eval_mul, eval_C]
    rw [Finset.sum_congr rfl fun r hr => by rw [hEo r hr]]
    rw [add_mul, Finset.sum_mul]
    field_simp
    ring_nf
  -- Part B: the substitution `x = m + p z`
  set G : ℚ[X] := C (m : ℚ) + C (p : ℚ) * X with hG
  set ec : ℤ := e c with hec
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
  have hGA : GV p (A.comp G) ec := hA m
  have hGPiO : GV p (PiO.comp G) 0 := by
    rw [hPiO, Polynomial.prod_comp]
    exact (GV.prod (p := p) Plo (r := fun _ => (0 : ℚ)) fun r _ => GV_lin_comp m r).mono
      (by simp)
  have hGI : GV p (I.comp G) ec := by
    rw [hI, Polynomial.sum_comp]
    refine GV.sum _ fun r hr => ?_
    rw [mul_comp, C_comp, Polynomial.prod_comp]
    have hprod : GV p (∏ s ∈ Plc.erase r, (X - C (s : ℚ)).comp G) ((Plc.erase r).card) := by
      exact (GV.prod (p := p) (Plc.erase r) (r := fun _ => (1 : ℚ)) fun s hs =>
        GV_lin_comp_class m s (by rw [(hmemc s (Finset.mem_of_mem_erase hs)).2, hc])).mono
        (by simp)
    have hres := VG_res hA Pl hsep (hmemc r hr).1
    have hrc : (r : ZMod p) = c := (hmemc r hr).2
    rw [hrc, ← hPlc] at hres
    have := GV.C_mul hres hprod
    refine this.mono (le_of_eq ?_)
    rw [Finset.card_erase_of_mem hr]
    have : 1 ≤ Plc.card := Finset.card_pos.mpr ⟨r, hr⟩
    push_cast [this]; ring
  have hRHS : GV p (A.comp G - PiO.comp G * I.comp G) ec :=
    hGA.sub ((hGPiO.mul hGI).mono (by simp))
  set F : ℚ[X] := C ((p : ℚ) ^ (-ec)) * (A.comp G - PiO.comp G * I.comp G) with hF
  have hFint : GV p F 0 := by
    have := GV.C_mul (VG.primePow (p := p) (-ec)) hRHS
    refine this.mono (le_of_eq ?_); push_cast; ring
  have hFeq : F = T * (C ((p : ℚ) ^ ((ℓ : ℤ) - ec)) * H.comp G) := by
    rw [hF, show A.comp G - PiO.comp G * I.comp G = PiC.comp G * H.comp G by rw [hAcomp]; ring,
      hPiCcomp]
    have hz : (p : ℚ) ^ (-ec) * (p : ℚ) ^ ℓ = (p : ℚ) ^ ((ℓ : ℤ) - ec) := by
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
  have hcancel : C ((p : ℚ) ^ ((ℓ : ℤ) - ec)) * H.comp G = S :=
    mul_left_cancel₀ hT0 (hFeq.symm.trans hFS)
  have hGm : G.eval 0 = (m : ℚ) := by rw [hG]; simp
  have hHm : H.eval (m : ℚ) = (p : ℚ) ^ (ec - ℓ) * S.eval 0 := by
    have := congrArg (eval 0) hcancel
    rw [eval_mul, eval_C, eval_comp, hGm] at this
    rw [← this, ← mul_assoc, ← zpow_add₀ hp0]; ring_nf; simp
  have hVGH : VG p (H.eval (m : ℚ)) ((ec : ℚ) - ℓ) := by
    rw [hHm]
    have := (VG.primePow (p := p) (ec - ℓ)).mul (VG.eval_zero hS)
    simpa using this
  -- Part C: combine
  rw [hPm]
  refine VG.sub ((hVGH.mul hVGinvPiO).mono (by rw [hec, hℓ, hPlc]; linarith))
    (VG.sum _ fun r hr => ?_)
  have hres := VG_res hA Pl hsep (hmemo r hr).1
  have := hres.mul (hVGinv r hr)
  refine this.mono ?_
  have := hβo r (hmemo r hr).1 (hmemo r hr).2
  linarith

end Zeta32.Arith.Local

end
