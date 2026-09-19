/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module


import Mathlib.Algebra.Module.Submodule.Union
public import LeanPool.RiemannRochFunctionFields.WeilDifferential.Basic
import LeanPool.RiemannRochFunctionFields.LinearKneser
import LeanPool.RiemannRochFunctionFields.RiemannRochTheorem.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corollaries of Riemann–Roch
Standard consequences of the main theorem, including C5 (Clifford) and C6 (existence of
non-special divisors).
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

namespace FunctionField.Chart

variable (k K : Type*) [Field k] [Field K]

variable [Algebra k K] [Algebra k[X] K] [Algebra k⟮X⟯ K] [IsScalarTower k k[X] K]
  [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

section Canonical

variable {W : DivisorA k K} (hW : IsCanonical k K W)

include hW

/-- **C1**: for a canonical divisor, `ℓ(W) = g`. -/
theorem ell_canonical : ell k K W = genus k K := by
  have hRR := riemann_roch k K hW (0 : DivisorA k K)
  rw [ell_zero k K, deg_zero, zero_add, sub_zero] at hRR
  omega

/-- **C2**: `deg W = 2g − 2`. -/
theorem deg_canonical : deg k K W = 2 * (genus k K : ℤ) - 2 := by
  have hRR := riemann_roch k K hW W
  rw [sub_self, ell_zero k K, ell_canonical k K hW] at hRR
  omega

/-- **C3**: if `deg D ≥ 2g − 1` then `ℓ(D) = deg D + 1 − g`. -/
theorem ell_eq_of_deg_ge (D : DivisorA k K) (hdeg : deg k K D ≥ 2 * (genus k K : ℤ) - 1) :
    (ell k K D : ℤ) = deg k K D + 1 - (genus k K : ℤ) := by
  have hcanonical := deg_canonical k K hW
  have hneg : deg k K (W - D) < 0 := by
    rw [deg_sub, hcanonical]
    omega
  have hell := RRspace_neg_deg_ell k K hneg
  rw [riemann_roch k K hW D, hell, Int.ofNat_zero, add_zero]

/-- **C4**: index-of-specialty language matches `ℓ(W − D)`. -/
theorem indexOfSpecialty_eq_ell (D : DivisorA k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K (W - D) := by
  exact indexOfSpecialty_eq_ell_sub k K hW D

end Canonical

/-- The specialty index vanishes in degree at least `2g - 1`. -/
theorem indexOfSpecialty_eq_zero_of_large_deg (D : DivisorA k K)
    (hdeg : deg k K D ≥ 2 * (genus k K : ℤ) - 1) :
    indexOfSpecialty k K D = 0 := by
  obtain ⟨W, hW⟩ := exists_isCanonical k K
  have hell := ell_eq_of_deg_ge k K hW D hdeg
  have hi := indexOfSpecialty_eq k K D
  omega

/-- The specialty index vanishes above a uniform degree bound. -/
theorem indexOfSpecialty_eq_zero_of_le_deg :
    ∃ c : ℤ, ∀ D : DivisorA k K, c ≤ deg k K D → indexOfSpecialty k K D = 0 := by
  exact ⟨2 * (genus k K : ℤ) - 1, fun D hD =>
    indexOfSpecialty_eq_zero_of_large_deg k K D hD⟩

omit [IsFullConstantField k K] in
/-- A positive-dimensional Riemann–Roch space supplies an effective representative of the
divisor's linear-equivalence class. -/
theorem exists_effective_add_principal_of_ell_pos (D : DivisorA k K)
    (hD : 0 < ell k K D) :
    ∃ x : Kˣ, IsEffective k K
      (D + principalDivisorA k K (Additive.ofMul x)) := by
  let : FiniteDimensional k (RRspace k K D) := finiteDimensional_RRspace_aux k K D
  obtain ⟨f, hf⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := k)
    (M := RRspace k K D)).mp hD
  have hfval : (f : K) ≠ 0 := by
    intro h
    apply hf
    exact Subtype.ext h
  let x : Kˣ := Units.mk0 (f : K) hfval
  refine ⟨x, ?_⟩
  have hle : (0 : DivisorA k K) ≤
      D + principalDivisorA k K (Additive.ofMul x) :=
    le_add_principal_of_memRRspace (k := k) (K := K)
      (D₀ := (0 : DivisorA k K)) (D₁ := D) hfval
      (by simpa only [sub_zero] using
        ((mem_RRspace_iff k K D (f : K)).mp f.property))
  exact hle

omit [IsFullConstantField k K] in
/-- Riemann–Roch spaces preserve infima of divisors. -/
theorem RRspace_inf (D E : DivisorA k K) :
    RRspace k K (D ⊓ E) = RRspace k K D ⊓ RRspace k K E := by
  ext f
  simp only [Submodule.mem_inf, mem_RRspace_iff]
  constructor
  · intro hf
    exact ⟨memRRspace.memRRspace_mono (k := k) (K := K) inf_le_left hf,
      memRRspace.memRRspace_mono (k := k) (K := K) inf_le_right hf⟩
  · rintro ⟨hD, hE⟩ v
    change placeValuation k K v f ≤ WithZero.exp ((D ⊓ E) v)
    rw [Finsupp.inf_apply]
    by_cases h : D v ≤ E v
    · rw [inf_eq_left.mpr h]
      exact hD v
    · rw [inf_eq_right.mpr (le_of_not_ge h)]
      exact hE v

omit [IsFullConstantField k K] in
/-- The sum of two Riemann–Roch spaces lies in the space of the supremum divisor. -/
theorem RRspace_sup_le (D E : DivisorA k K) :
    RRspace k K D ⊔ RRspace k K E ≤ RRspace k K (D ⊔ E) := by
  rw [sup_le_iff]
  exact ⟨RRspace_mono k K le_sup_left, RRspace_mono k K le_sup_right⟩

omit [IsFullConstantField k K] in
/-- Riemann–Roch dimension is submodular on the divisor lattice. -/
theorem ell_submodular (D E : DivisorA k K) :
    ell k K D + ell k K E ≤ ell k K (D ⊔ E) + ell k K (D ⊓ E) := by
  let : FiniteDimensional k (RRspace k K D) := finiteDimensional_RRspace_aux k K D
  let : FiniteDimensional k (RRspace k K E) := finiteDimensional_RRspace_aux k K E
  have hsup : Module.finrank k ↑(RRspace k K D ⊔ RRspace k K E) ≤
      Module.finrank k (RRspace k K (D ⊔ E)) :=
    Submodule.finrank_mono (RRspace_sup_le k K D E)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (RRspace k K D) (RRspace k K E)
  rw [← RRspace_inf k K D E] at hdim
  dsimp only [ell]
  omega

omit [IsFullConstantField k K] in
/-- Every positive-dimensional complete linear system has a representative minimal under
removing one copy of any place. -/
theorem exists_minimal_RRspace (A : DivisorA k K) (hA : 0 < ell k K A) :
    ∃ D₀ : DivisorA k K, D₀ ≤ A ∧ RRspace k K D₀ = RRspace k K A ∧
      ∀ v : PlaceA k K, ell k K (D₀ - Finsupp.single v 1) < ell k K D₀ := by
  let S : Set ℕ := {n | ∃ D : DivisorA k K,
    D ≤ A ∧ RRspace k K D = RRspace k K A ∧ deg k K D = (n : ℤ)}
  have hdegA : 0 ≤ deg k K A := by
    obtain ⟨x, hx⟩ := exists_effective_add_principal_of_ell_pos k K A hA
    have hdeg := deg_nonneg k K hx
    rw [deg_add, deg_principalDivisor_eq_zero k K x, add_zero] at hdeg
    exact hdeg
  have hS : S.Nonempty := by
    refine ⟨(deg k K A).toNat, A, le_rfl, rfl, ?_⟩
    exact (Int.toNat_of_nonneg hdegA).symm
  obtain ⟨D₀, hD₀A, hspace, hdegD₀⟩ := Nat.sInf_mem hS
  refine ⟨D₀, hD₀A, hspace, fun v => ?_⟩
  have hle : D₀ - Finsupp.single v 1 ≤ D₀ := by
    intro w
    simp only [Finsupp.sub_apply]
    exact sub_le_self _ (Finsupp.single_nonneg.mpr (by omega) w)
  have hell_le : ell k K (D₀ - Finsupp.single v 1) ≤ ell k K D₀ :=
    Submodule.finrank_mono (RRspace_mono k K hle)
  rw [lt_iff_le_and_ne]
  refine ⟨hell_le, ?_⟩
  intro hell_eq
  have : FiniteDimensional k (RRspace k K D₀) := finiteDimensional_RRspace_aux k K D₀
  have hspace_sub : RRspace k K (D₀ - Finsupp.single v 1) = RRspace k K D₀ :=
    Submodule.eq_of_le_of_finrank_eq (RRspace_mono k K hle) hell_eq
  have hdegsub_nonneg : 0 ≤ deg k K (D₀ - Finsupp.single v 1) := by
    have hpos : 0 < ell k K (D₀ - Finsupp.single v 1) := by
      rw [hell_eq]
      dsimp only [ell] at hA ⊢
      rw [hspace]
      exact hA
    obtain ⟨x, hx⟩ := exists_effective_add_principal_of_ell_pos k K _ hpos
    have hdeg := deg_nonneg k K hx
    rw [deg_add, deg_principalDivisor_eq_zero k K x, add_zero] at hdeg
    exact hdeg
  let m := (deg k K (D₀ - Finsupp.single v 1)).toNat
  have hmcast : (m : ℤ) = deg k K (D₀ - Finsupp.single v 1) :=
    Int.toNat_of_nonneg hdegsub_nonneg
  have hmS : m ∈ S := by
    refine ⟨D₀ - Finsupp.single v 1, hle.trans hD₀A, ?_, hmcast.symm⟩
    exact hspace_sub.trans hspace
  have hmin := Nat.sInf_le hmS
  have hdegdrop : deg k K (D₀ - Finsupp.single v 1) < deg k K D₀ := by
    rw [deg_sub, deg_single]
    have hv := placeDegree_pos k K v
    omega
  rw [hdegD₀, ← hmcast] at hdegdrop
  exact (not_lt_of_ge hmin) (by exact_mod_cast hdegdrop)

omit [IsFullConstantField k K] in
/-- Over an infinite constant field, finitely many one-place drops from a minimal complete
linear system can be avoided simultaneously. -/
theorem exists_RRspace_avoiding [Infinite k] (D₀ : DivisorA k K)
    (s : Finset (PlaceA k K))
    (hdrop : ∀ v ∈ s, ell k K (D₀ - Finsupp.single v 1) < ell k K D₀) :
    ∃ z : RRspace k K D₀, ∀ v ∈ s,
      (z : K) ∉ RRspace k K (D₀ - Finsupp.single v 1) := by
  let p : {v // v ∈ s} → Submodule k (RRspace k K D₀) := fun v =>
    Submodule.comap (RRspace k K D₀).subtype
      (RRspace k K (D₀ - Finsupp.single v.1 1))
  have hp : ∀ v, p v ≠ ⊤ := by
    intro v hv
    have hrev : RRspace k K D₀ ≤ RRspace k K (D₀ - Finsupp.single v.1 1) :=
      Submodule.comap_subtype_eq_top.mp hv
    have hle : D₀ - Finsupp.single v.1 1 ≤ D₀ := by
      intro w
      simp only [Finsupp.sub_apply]
      exact sub_le_self _ (Finsupp.single_nonneg.mpr (by omega) w)
    have heq : RRspace k K (D₀ - Finsupp.single v.1 1) = RRspace k K D₀ :=
      le_antisymm (RRspace_mono k K hle) hrev
    have hell : ell k K (D₀ - Finsupp.single v.1 1) = ell k K D₀ := by
      dsimp only [ell]
      rw [heq]
    exact (ne_of_lt (hdrop v.1 v.2)) hell
  obtain ⟨z, hz⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
  refine ⟨z, fun v hv hmem => ?_⟩
  exact hz ⟨v, hv⟩ (by
    simpa only [p, Submodule.mem_comap, Submodule.coe_subtype] using hmem)

omit [Algebra k K] [IsScalarTower k k[X] K] [IsFullConstantField k K] in
/-- Membership of a nonzero function in `L(D)` expressed coefficientwise through its principal
divisor. -/
theorem memRRspace_iff_neg_principalDivisor_le {D : DivisorA k K} {f : K}
    (hf : f ≠ 0) :
    memRRspace k K D f ↔ ∀ v, -(principalDivisorA k K
      (Additive.ofMul (Units.mk0 f hf)) v) ≤ D v := by
  constructor
  · intro h v
    have hv := h v
    have hval := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 f hf)) v
    change placeValuation k K v f ≤ WithZero.exp (D v) at hv
    change placeValuation k K v f = WithZero.exp
      (-(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v)) at hval
    rw [hval] at hv
    exact WithZero.exp_le_exp.mp hv
  · intro h v
    have hval := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul (Units.mk0 f hf)) v
    change placeValuation k K v f ≤ WithZero.exp (D v)
    change placeValuation k K v f = WithZero.exp
      (-(principalDivisorA k K (Additive.ofMul (Units.mk0 f hf)) v)) at hval
    rw [hval]
    exact WithZero.exp_le_exp.mpr (h v)

/-- If multiplication by a section that is exact at every place in `supp B` creates no new
poles, the other factor is constant. -/
theorem eq_algebraMap_of_mul_mem {D₀ B : DivisorA k K} (hB0 : B ≠ 0) {z x : K}
    (hz : memRRspace k K D₀ z)
    (havoid : ∀ v ∈ B.support, z ∉ RRspace k K (D₀ - Finsupp.single v 1))
    (hx : memRRspace k K B x) (hmul : memRRspace k K D₀ (x * z)) :
    ∃ c : k, x = algebraMap k K c := by
  have hsupp : B.support.Nonempty := Finsupp.support_nonempty_iff.mpr hB0
  obtain ⟨v₀, hv₀⟩ := hsupp
  have hz0 : z ≠ 0 := by
    intro hz0
    subst z
    exact havoid v₀ hv₀ (memRRspace.zero_mem (k := k) (K := K) _)
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have hxz0 : x * z ≠ 0 := mul_ne_zero hx0 hz0
  let ux : Kˣ := Units.mk0 x hx0
  let uz : Kˣ := Units.mk0 z hz0
  let uxz : Kˣ := Units.mk0 (x * z) hxz0
  have hxdiv := (memRRspace_iff_neg_principalDivisor_le k K hx0).mp hx
  have hzdiv := (memRRspace_iff_neg_principalDivisor_le k K hz0).mp hz
  have hmuldiv := (memRRspace_iff_neg_principalDivisor_le k K hxz0).mp hmul
  change ∀ v, -(principalDivisorA k K (Additive.ofMul ux) v) ≤ B v at hxdiv
  change ∀ v, -(principalDivisorA k K (Additive.ofMul uz) v) ≤ D₀ v at hzdiv
  change ∀ v, -(principalDivisorA k K (Additive.ofMul uxz) v) ≤ D₀ v at hmuldiv
  have hvalx : ∀ v : PlaceA k K, placeValuation k K v x ≤ 1 := by
    intro v
    have hdivx : 0 ≤ principalDivisorA k K (Additive.ofMul ux) v := by
      by_cases hv : v ∈ B.support
      · have hzexact : -(principalDivisorA k K (Additive.ofMul uz) v) = D₀ v := by
          have hle := hzdiv v
          have hnle : ¬ -(principalDivisorA k K (Additive.ofMul uz) v) ≤ D₀ v - 1 := by
            intro hsmall
            apply havoid v hv
            rw [mem_RRspace_iff]
            apply (memRRspace_iff_neg_principalDivisor_le k K hz0).mpr
            intro w
            by_cases hw : w = v
            · subst w
              simpa using hsmall
            · simpa [Finsupp.single_apply, hw] using hzdiv w
          omega
        have hdivmul : principalDivisorA k K (Additive.ofMul uxz) v =
            principalDivisorA k K (Additive.ofMul ux) v +
              principalDivisorA k K (Additive.ofMul uz) v := by
          have hu : uxz = ux * uz := by
            apply Units.ext
            rfl
          rw [hu, ofMul_mul, (principalDivisorA k K).map_add, Finsupp.add_apply]
        have hp := hmuldiv v
        rw [hdivmul] at hp
        omega
      · have hBv : B v = 0 := Finsupp.notMem_support_iff.mp hv
        have hp := hxdiv v
        rw [hBv] at hp
        omega
    have hval := placeValuation_eq_exp_neg_principalDivisor k K
      (Additive.ofMul ux) v
    change placeValuation k K v x = WithZero.exp
      (-(principalDivisorA k K (Additive.ofMul ux) v)) at hval
    rw [hval, ← WithZero.exp_zero]
    exact WithZero.exp_le_exp.mpr (by omega)
  exact IsFullConstantField.algebraic_mem (k := k) (K := K) x
    (isAlgebraic_of_placeValuation_le_one k K x hvalx)

/-- Stichtenoth's key Clifford inequality for an effective nonzero second divisor and a first
divisor minimal under one-place drops. -/
theorem ell_add_ell_le_of_effective_minimal [Infinite k]
    (D₀ B : DivisorA k K) (hB : IsEffective k K B) (hB0 : B ≠ 0)
    (hdrop : ∀ v ∈ B.support,
      ell k K (D₀ - Finsupp.single v 1) < ell k K D₀) :
    ell k K D₀ + ell k K B ≤ 1 + ell k K (D₀ + B) := by
  obtain ⟨z, hzavoid⟩ := exists_RRspace_avoiding k K D₀ B.support hdrop
  let T := RRspace k K (D₀ + B)
  let P : Submodule k T := Submodule.comap T.subtype (RRspace k K D₀)
  let mulZ : RRspace k K B →ₗ[k] T := {
    toFun x := ⟨(x : K) * (z : K), by
      rw [mem_RRspace_iff]
      simpa only [add_comm] using memRRspace.mul_mem (k := k) (K := K)
        ((mem_RRspace_iff k K B (x : K)).mp x.property)
        ((mem_RRspace_iff k K D₀ (z : K)).mp z.property)⟩
    map_add' x y := Subtype.ext (add_mul (x : K) (y : K) (z : K))
    map_smul' c x := Subtype.ext (by
      simp only [Submodule.coe_smul_of_tower, RingHom.id_apply, Algebra.smul_def]
      ring) }
  let φ : RRspace k K B →ₗ[k] T ⧸ P := P.mkQ.comp mulZ
  have hone_mem : memRRspace k K B (1 : K) :=
    memRRspace.memRRspace_mono (k := k) (K := K) (show (0 : DivisorA k K) ≤ B from hB)
      (memRRspace.one_mem (k := k) (K := K))
  let oneB : RRspace k K B := ⟨1, hone_mem⟩
  have hker_le : φ.ker ≤ k ∙ oneB := by
    intro x hxker
    have hq : P.mkQ (mulZ x) = 0 := by
      exact hxker
    have hp : mulZ x ∈ P := Submodule.Quotient.mk_eq_zero P |>.mp hq
    have hmul : memRRspace k K D₀ ((x : K) * (z : K)) := by
      exact hp
    obtain ⟨c, hc⟩ := eq_algebraMap_of_mul_mem k K hB0
      ((mem_RRspace_iff k K D₀ (z : K)).mp z.property) hzavoid
      ((mem_RRspace_iff k K B (x : K)).mp x.property) hmul
    have hxeq : x = c • oneB := by
      apply Subtype.ext
      simp only [Submodule.coe_smul_of_tower, oneB, Algebra.smul_def]
      rw [hc, mul_one]
    rw [hxeq]
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self oneB)
  have hker_ge : k ∙ oneB ≤ φ.ker := by
    rw [Submodule.span_singleton_le_iff_mem]
    rw [LinearMap.mem_ker]
    change P.mkQ (mulZ oneB) = 0
    apply (Submodule.Quotient.mk_eq_zero P).mpr
    change (1 : K) * (z : K) ∈ RRspace k K D₀
    simpa only [one_mul] using z.property
  have hker : φ.ker = k ∙ oneB := le_antisymm hker_le hker_ge
  have honeB : oneB ≠ 0 := by
    intro h
    have hc := congr_arg (fun q : RRspace k K B => (q : K)) h
    change (1 : K) = 0 at hc
    exact one_ne_zero hc
  have hfinKer : Module.finrank k φ.ker = 1 := by
    rw [hker, finrank_span_singleton honeB]
  have hDle : RRspace k K D₀ ≤ T := by
    exact RRspace_mono k K (show D₀ ≤ D₀ + B by
      intro v
      simp only [Finsupp.add_apply]
      linarith [hB v])
  have hmapP : P.map T.subtype = RRspace k K D₀ := by
    dsimp only [P]
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hDle]
  have hfinP : Module.finrank k P = ell k K D₀ := by
    rw [← Submodule.finrank_map_subtype_eq T P, hmapP]
    rfl
  let : FiniteDimensional k (RRspace k K B) := finiteDimensional_RRspace_aux k K B
  let : FiniteDimensional k T := finiteDimensional_RRspace_aux k K (D₀ + B)
  have hranknull := φ.finrank_range_add_finrank_ker
  have hrange : Module.finrank k φ.range ≤ Module.finrank k (T ⧸ P) := by
    simpa only [finrank_top] using
      Submodule.finrank_mono (show φ.range ≤ (⊤ : Submodule k (T ⧸ P)) from le_top)
  have hquot := P.finrank_quotient_add_finrank
  dsimp only [ell] at hfinP
  rw [hfinKer] at hranknull
  rw [hfinP] at hquot
  dsimp only [ell] at ⊢
  change Module.finrank k (RRspace k K D₀) + Module.finrank k (RRspace k K B) ≤
    1 + Module.finrank k T
  omega

/-- Stichtenoth Lemma 1.6.14 over an infinite full constant field. -/
theorem ell_add_ell_le_infinite [Infinite k]
    (A B : DivisorA k K) (hA : 0 < ell k K A) (hB : 0 < ell k K B) :
    ell k K A + ell k K B ≤ 1 + ell k K (A + B) := by
  obtain ⟨x, hxeff⟩ := exists_effective_add_principal_of_ell_pos k K A hA
  obtain ⟨y, hyeff⟩ := exists_effective_add_principal_of_ell_pos k K B hB
  let A₀ := A + principalDivisorA k K (Additive.ofMul x)
  let B₀ := B + principalDivisorA k K (Additive.ofMul y)
  have hellA₀ : ell k K A₀ = ell k K A := ell_add_principal k K A x
  have hellB₀ : ell k K B₀ = ell k K B := ell_add_principal k K B y
  have hA₀pos : 0 < ell k K A₀ := hellA₀.symm ▸ hA
  obtain ⟨D₀, hD₀le, hspace, hdrop⟩ := exists_minimal_RRspace k K A₀ hA₀pos
  have hellD₀ : ell k K D₀ = ell k K A₀ := by
    dsimp only [ell]
    rw [hspace]
  have hle : D₀ + B₀ ≤ A₀ + B₀ := by
    intro v
    simp only [Finsupp.add_apply]
    linarith [hD₀le v]
  have hell_mono : ell k K (D₀ + B₀) ≤ ell k K (A₀ + B₀) :=
    Submodule.finrank_mono (RRspace_mono k K hle)
  have hsum : A₀ + B₀ = (A + B) +
      principalDivisorA k K (Additive.ofMul (x * y)) := by
    dsimp only [A₀, B₀]
    rw [ofMul_mul, (principalDivisorA k K).map_add]
    abel
  have hellsum : ell k K (A₀ + B₀) = ell k K (A + B) := by
    rw [hsum, ell_add_principal]
  by_cases hB₀0 : B₀ = 0
  · have hellB₀one : ell k K B₀ = 1 := by
      rw [hB₀0, ell_zero k K]
    have hellsum0 : ell k K A₀ = ell k K (A + B) := by
      simpa only [hB₀0, add_zero] using hellsum
    rw [← hellA₀, ← hellB₀, hellB₀one, ← hellsum0]
    omega
  · have hkey := ell_add_ell_le_of_effective_minimal k K D₀ B₀ hyeff hB₀0
      (fun v _ => hdrop v)
    rw [← hellA₀, ← hellB₀, ← hellsum]
    omega

/-- Stichtenoth Lemma 1.6.14 over an arbitrary full constant field. This is the
Riemann–Roch-space specialization of `mul_finrank`. -/
theorem ell_add_ell_le (A B : DivisorA k K) (hA : 0 < ell k K A)
    (hB : 0 < ell k K B) :
    ell k K A + ell k K B ≤ 1 + ell k K (A + B) := by
  let : FiniteDimensional k (RRspace k K A) := finiteDimensional_RRspace_aux k K A
  let : FiniteDimensional k (RRspace k K B) := finiteDimensional_RRspace_aux k K B
  have hAne : RRspace k K A ≠ ⊥ := by
    intro hzero
    dsimp only [ell] at hA
    rw [hzero, finrank_bot] at hA
    omega
  have hBne : RRspace k K B ≠ ⊥ := by
    intro hzero
    dsimp only [ell] at hB
    rw [hzero, finrank_bot] at hB
    omega
  have hAfg : (RRspace k K A).FG :=
    (Submodule.fg_top (RRspace k K A)).mp Module.Finite.fg_top
  have hBfg : (RRspace k K B).FG :=
    (Submodule.fg_top (RRspace k K B)).mp Module.Finite.fg_top
  let : FiniteDimensional k (RRspace k K A * RRspace k K B) :=
    Module.Finite.of_fg (hAfg.mul hBfg)
  have hproduct := mul_finrank k K (RRspace k K A) (RRspace k K B) hAne hBne
  have hmul : RRspace k K A * RRspace k K B ≤ RRspace k K (A + B) := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    rw [mem_RRspace_iff] at hx hy ⊢
    exact memRRspace.mul_mem (k := k) (K := K) hx hy
  have hmono : Module.finrank k (RRspace k K A * RRspace k K B) ≤
      Module.finrank k (RRspace k K (A + B)) :=
    Submodule.finrank_mono hmul
  dsimp only [ell]
  omega

/-- The core Clifford inequality: with `W` canonical, whenever both `ℓ(D)` and `ℓ(W − D)` are
positive, `2(ℓ(D) − 1) ≤ deg D`. The textbook degree bounds
`0 ≤ deg D ≤ 2g − 2` are **not** required — positivity of both dimensions, the linear
product bound, and Riemann–Roch suffice. -/
theorem clifford_of_ell_pos {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K)
    (hℓD : 0 < ell k K D) (hℓW : 0 < ell k K (W - D)) :
    2 * ((ell k K D : ℤ) - 1) ≤ deg k K D := by
  have hkey := ell_add_ell_le k K D (W - D) hℓD hℓW
  have hsum : D + (W - D) = W := by abel
  rw [hsum, ell_canonical k K hW] at hkey
  have hRR := riemann_roch k K hW D
  omega

/-- **C5** (Clifford): if `0 ≤ deg D ≤ 2g − 2` and both `ℓ(D)` and `ℓ(W − D)` are
positive, then `2(ℓ(D) − 1) ≤ deg D`. This is the conventional textbook statement; the degree
hypotheses are kept for fidelity but are not needed for the inequality (see
`clifford_of_ell_pos`). -/
theorem clifford {W : DivisorA k K} (hW : IsCanonical k K W) (D : DivisorA k K)
    (_hdeg₀ : 0 ≤ deg k K D) (_hdeg₁ : deg k K D ≤ 2 * (genus k K : ℤ) - 2)
    (hℓD : 0 < ell k K D) (hℓW : 0 < ell k K (W - D)) :
    2 * ((ell k K D : ℤ) - 1) ≤ deg k K D :=
  clifford_of_ell_pos k K hW D hℓD hℓW

/-- **C6** (field-independent form): a divisor attaining the maximal defect is nonspecial.
The stronger assertion that one can choose an effective divisor of degree `g` requires
additional hypotheses on the constant field and is not valid over every field. -/
theorem exists_nonspecial_divisor :
    ∃ D : DivisorA k K, indexOfSpecialty k K D = 0 := by
  obtain ⟨D, hD⟩ := exists_defect_eq k K
  refine ⟨D, ?_⟩
  have hi := indexOfSpecialty_eq k K D
  simp only [defect] at hD
  omega

end FunctionField.Chart

end
