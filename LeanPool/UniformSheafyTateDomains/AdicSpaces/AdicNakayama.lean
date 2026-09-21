/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Topological Nakayama: finiteness from a finite adic quotient

([hrw-decomposition] "THE TATE LEAF DECOMPOSED", leaf 10.)  If `R` is
`I`-adically precomplete, `M` is `I`-adically Hausdorff, and `M/IM` is a
finite `R`-module, then `M` is a finite `R`-module: lift generators of the
quotient, and apply the adic surjectivity criterion
`surjective_of_mkQ_comp_surjective`.

The consumer instantiates `R = 𝒪_K` (`π`-adically complete), `M = B` a
noetherian-domain quotient of the integral Tate algebra (`π`-adically
Hausdorff by Krull intersection), with `B/πB` finite over the residue field.
-/

@[expose] public section


section AdicNakayama

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open Classical in
/-- `I • ⊤` on `R` itself is `I`. -/
theorem ideal_smul_top_self {R : Type*} [CommRing R] (I : Ideal R) :
    (I • (⊤ : Submodule R R)) = (I : Submodule R R) := by
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · simpa [smul_eq_mul] using Ideal.mul_mem_right x _ ha
  · have h1 : x • (1 : R) ∈ I • (⊤ : Submodule R R) :=
      Submodule.smul_mem_smul hx Submodule.mem_top
    simpa using h1

open Classical in
/-- `I • ⊤` on a finite power of `R` is the coordinatewise ideal. -/
theorem ideal_smul_top_pi {R : Type*} [CommRing R] (I : Ideal R)
    {ι : Type*} [Finite ι] :
     (I • (⊤ : Submodule R (ι → R))) =
      Submodule.pi Set.univ (fun _ => (I : Submodule R R)) := by
  classical
  let : DecidableEq ι := Classical.decEq ι
  let := Fintype.ofFinite ι
  refine le_antisymm (Submodule.smul_le.mpr fun a ha x _ => ?_) fun x hx => ?_
  · refine Submodule.mem_pi.mpr fun i _ => ?_
    simpa [smul_eq_mul] using Ideal.mul_mem_right (x i) _ ha
  · rw [Submodule.mem_pi] at hx
    have hxs : x = ∑ i : ι, Pi.single i (x i) :=
      (Finset.univ_sum_single x).symm
    rw [hxs]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : Pi.single i (x i) = (x i) • Pi.single i (1 : R) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [ hj]
    rw [h1]
    exact Submodule.smul_mem_smul (hx i trivial) Submodule.mem_top

open Classical in
/-- Precompleteness passes to finite powers, coordinatewise. -/
theorem isPrecomplete_pi {R : Type*} [CommRing R] (I : Ideal R)
    [IsPrecomplete I R] (ι : Type*) [Finite ι] :
    IsPrecomplete I (ι → R) := by
  classical
  cases nonempty_fintype ι
  constructor
  intro f hf
  have hcomp : ∀ i : ι, ∃ L : R, ∀ n,
      f n i ≡ L [SMOD (I ^ n • (⊤ : Submodule R R))] := by
    intro i
    refine IsPrecomplete.prec ‹IsPrecomplete I R› (fun {m n} hmn => ?_)
    have h1 := hf hmn
    rw [SModEq.sub_mem] at h1 ⊢
    rw [ideal_smul_top_pi] at h1
    rw [ideal_smul_top_self]
    have h2 := Submodule.mem_pi.mp h1 i trivial
    simpa using h2
  choose L hL using hcomp
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, ideal_smul_top_pi]
  refine Submodule.mem_pi.mpr fun i _ => ?_
  have h3 := hL i n
  rw [SModEq.sub_mem, ideal_smul_top_self] at h3
  simpa using h3

open Classical in
/-- **Topological Nakayama**: over an `I`-precomplete base, an `I`-Hausdorff
module with finitely generated reduction mod `I` is finitely generated. -/
theorem Module.Finite.of_finite_quotient_smul_top_of_isPrecomplete
    (I : Ideal R) [IsPrecomplete I R] [IsHausdorff I M]
    (hfin : Module.Finite R (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Finite R M := by
  classical
  obtain ⟨s, hs⟩ := hfin.fg_top
  choose g hg using Submodule.mkQ_surjective (I • (⊤ : Submodule R M))
  set v : s → M := fun i => g i.1 with hv
  set F : (s → R) →ₗ[R] M := Fintype.linearCombination R v with hF
  have hcomp : Function.Surjective
      ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) := by
    intro y
    have hy : y ∈ Submodule.span R (↑s : Set (M ⧸ (I • (⊤ : Submodule R M)))) := by
      rw [hs]
      exact Submodule.mem_top
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.mp hy
    refine ⟨fun i => c i.1, ?_⟩
    have h1 : ((I • (⊤ : Submodule R M)).mkQ ∘ₗ F) (fun i => c i.1) =
        ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i) := by
      rw [LinearMap.comp_apply, hF, Fintype.linearCombination_apply,
        map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul]
    rw [h1]
    have h2 : ∀ i : s, (I • (⊤ : Submodule R M)).mkQ (v i) = i.1 := by
      intro i
      rw [hv]
      exact hg i.1
    calc ∑ i : s, c i.1 • (I • (⊤ : Submodule R M)).mkQ (v i)
        = ∑ i : s, c i.1 • i.1 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [h2 i]
      _ = ∑ a ∈ s, c a • a := Finset.sum_coe_sort s (fun a => c a • a)
      _ = y := hc
  let : IsPrecomplete I (s → R) := isPrecomplete_pi I s
  exact Module.Finite.of_surjective F
    (surjective_of_mkQ_comp_surjective hcomp)

section PrincipalAdicDivision

open AdicCompletion

variable {R : Type*} [CommRing R]

open Classical in
/-- **Tower division in a principal adic completion**: an element of the
`(a)`-adic completion whose level-one component vanishes is divisible by `a`,
provided `a` is a nonzerodivisor ([hrw-decomposition] Tate leaf 4 engine:
the kernel of `evalOneₐ` is generated by `a`). -/
theorem AdicCompletion.exists_eq_of_mul_of_component_one_eq_zero
    {a : R} (ha : a ∈ nonZeroDivisors R)
    (x : AdicCompletion (Ideal.span {a}) R)
    (h1 : x.1 1 = 0) :
    ∃ y : AdicCompletion (Ideal.span {a}) R,
      x = AdicCompletion.of (Ideal.span {a}) R a * y := by
  classical
  have hlift : ∀ n : ℕ, ∃ r : R,
      Submodule.Quotient.mk r = x.1 (n + 1) :=
    fun n => Submodule.Quotient.mk_surjective _ (x.1 (n + 1))
  choose r hr using hlift
  have hdiv : ∀ n : ℕ, ∃ s : R, r n = a * s := by
    intro n
    have hcoh := x.2 (show 1 ≤ n + 1 by omega)
    rw [← hr n] at hcoh
    have h3 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show 1 ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ 1 • ⊤ : Submodule R R)) (r n) := rfl
    rw [h3, h1] at hcoh
    have h4 : r n ∈ ((Ideal.span {a}) ^ 1 • ⊤ : Submodule R R) :=
      (Submodule.Quotient.mk_eq_zero _).mp hcoh
    rw [ideal_smul_top_self, pow_one] at h4
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h4
    exact ⟨s, by rw [← hs]; ring⟩
  choose sfun hs using hdiv
  have hscoh : ∀ {m n : ℕ}, m ≤ n →
      Submodule.Quotient.mk
        (p := ((Ideal.span {a}) ^ m • ⊤ : Submodule R R)) (sfun n) =
      Submodule.Quotient.mk (sfun m) := by
    intro m n hmn
    rw [Submodule.Quotient.eq]
    have hcoh := x.2 (show m + 1 ≤ n + 1 by omega)
    rw [← hr n, ← hr m] at hcoh
    have h5 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show m + 1 ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ (m + 1) • ⊤ : Submodule R R))
          (r n) := rfl
    rw [h5] at hcoh
    have h6 : r n - r m ∈
        ((Ideal.span {a}) ^ (m + 1) • ⊤ : Submodule R R) := by
      rw [← Submodule.Quotient.eq]
      exact hcoh
    rw [ideal_smul_top_self, Ideal.span_singleton_pow] at h6
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h6
    have h7 : a * (sfun n - sfun m) = a * (a ^ m * c) := by
      have h8 : a * sfun n - a * sfun m = a ^ (m + 1) * c := by
        rw [← hs n, ← hs m, ← hc]
        ring
      calc a * (sfun n - sfun m) = a * sfun n - a * sfun m := by ring
        _ = a ^ (m + 1) * c := h8
        _ = a * (a ^ m * c) := by ring
    have h9 : sfun n - sfun m = a ^ m * c :=
      (mul_cancel_left_mem_nonZeroDivisors ha).mp h7
    rw [ideal_smul_top_self, Ideal.span_singleton_pow, h9]
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  refine ⟨⟨fun n => Submodule.Quotient.mk (sfun n), ?_⟩, ?_⟩
  · intro m n hmn
    have h10 : AdicCompletion.transitionMap (Ideal.span {a}) R hmn
        (Submodule.Quotient.mk (sfun n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ m • ⊤ : Submodule R R))
          (sfun n) := rfl
    rw [h10]
    exact hscoh hmn
  · refine Subtype.ext (funext fun n => ?_)
    change x.1 n = Submodule.Quotient.mk
      (p := ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)) (a * sfun n)
    rw [← hs n]
    have h12 := x.2 (show n ≤ n + 1 by omega)
    rw [← hr n] at h12
    have h13 : AdicCompletion.transitionMap (Ideal.span {a}) R
        (show n ≤ n + 1 by omega)
        (Submodule.Quotient.mk (r n)) =
        Submodule.Quotient.mk
          (p := ((Ideal.span {a}) ^ n • ⊤ : Submodule R R)) (r n) := rfl
    rw [h13] at h12
    exact h12.symm

open Classical in
/-- The level-one quotient map `AdicCompletion (a) R →+* R ⧸ (a)`. -/
noncomputable def AdicCompletion.toQuotientSpan (a : R) :
    AdicCompletion (Ideal.span {a}) R →+* R ⧸ Ideal.span {a} :=
  (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).toRingHom.comp
    (AdicCompletion.evalₐ (Ideal.span {a}) 1).toRingHom

open Classical in
theorem AdicCompletion.toQuotientSpan_surjective (a : R) :
    Function.Surjective (AdicCompletion.toQuotientSpan a) :=
  (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).surjective.comp
    (AdicCompletion.surjective_evalₐ (Ideal.span {a}) 1)

open Classical in
theorem AdicCompletion.toQuotientSpan_of (a r : R) :
    AdicCompletion.toQuotientSpan a
      (AdicCompletion.of (Ideal.span {a}) R r) =
    Ideal.Quotient.mk (Ideal.span {a}) r := by
  rw [AdicCompletion.toQuotientSpan, RingHom.comp_apply]
  have h1 : (AdicCompletion.evalₐ (Ideal.span {a}) 1).toRingHom
      (AdicCompletion.of (Ideal.span {a}) R r) =
      Ideal.Quotient.mk ((Ideal.span {a}) ^ 1) r := rfl
  rw [h1]
  exact Ideal.quotEquivOfEq_mk _ _

open Classical in
/-- **The kernel of the level-one quotient is generated by `a`** (tower
division; [hrw-decomposition] Tate leaf 4). -/
theorem AdicCompletion.ker_toQuotientSpan {a : R}
    (ha : a ∈ nonZeroDivisors R) :
    RingHom.ker (AdicCompletion.toQuotientSpan a) =
      Ideal.span {AdicCompletion.of (Ideal.span {a}) R a} := by
  ext x
  rw [RingHom.mem_ker]
  constructor
  · intro hx
    have h1 : AdicCompletion.evalₐ (Ideal.span {a}) 1 x = 0 := by
      have h2 := congrArg
        (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).symm hx
      rw [_root_.map_zero] at h2
      rw [show (Ideal.quotEquivOfEq (pow_one (Ideal.span {a}))).symm
          (AdicCompletion.toQuotientSpan a x) =
        AdicCompletion.evalₐ (Ideal.span {a}) 1 x from by
          rw [AdicCompletion.toQuotientSpan]
          exact RingEquiv.symm_apply_apply _ _] at h2
      exact h2
    have h3 : x.1 1 = 0 := by
      refine (Ideal.quotientEquivAlgOfEq R (show
          ((Ideal.span {a}) ^ 1 • ⊤ : Ideal R) = (Ideal.span {a}) ^ 1 from
          by ext y; simp)).injective ?_
      rw [_root_.map_zero]
      exact h1
    obtain ⟨y, hy⟩ :=
      AdicCompletion.exists_eq_of_mul_of_component_one_eq_zero ha x h3
    rw [Ideal.mem_span_singleton']
    exact ⟨y, by rw [hy]; ring⟩
  · intro hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hx
    rw [← hy, map_mul, AdicCompletion.toQuotientSpan_of]
    have h6 : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self a)
    rw [h6, mul_zero]

open Classical in
/-- **The principal adic completion modulo its uniformizer** is the base
modulo the uniformizer. -/
noncomputable def AdicCompletion.quotientSpanEquiv {a : R}
    (ha : a ∈ nonZeroDivisors R) :
    (AdicCompletion (Ideal.span {a}) R ⧸
      Ideal.span {AdicCompletion.of (Ideal.span {a}) R a}) ≃+*
    R ⧸ Ideal.span {a} :=
  (Ideal.quotEquivOfEq (AdicCompletion.ker_toQuotientSpan ha).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.toQuotientSpan_surjective a))

open Classical in
/-- Computation law for `quotientSpanEquiv` on canonical images. -/
theorem AdicCompletion.quotientSpanEquiv_mk_of {a : R}
    (ha : a ∈ nonZeroDivisors R) (x : R) :
    AdicCompletion.quotientSpanEquiv ha
      (Ideal.Quotient.mk _ (AdicCompletion.of (Ideal.span {a}) R x)) =
    Ideal.Quotient.mk _ x := by
  change (RingHom.quotientKerEquivOfSurjective
      (AdicCompletion.toQuotientSpan_surjective a))
      ((Ideal.quotEquivOfEq (AdicCompletion.ker_toQuotientSpan ha).symm)
        (Ideal.Quotient.mk _ (AdicCompletion.of (Ideal.span {a}) R x))) =
    Ideal.Quotient.mk _ x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
    AdicCompletion.toQuotientSpan_of]

end PrincipalAdicDivision

section LevelwiseCongr

variable {A B : Type*} [CommRing A] [CommRing B]

open Classical in
/-- Levelwise identification of the adic quotients with ideal-power
quotients. -/
noncomputable def AdicCompletion.levelEquiv (I : Ideal A) (n : ℕ) :
    (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃+* (A ⧸ I ^ n) :=
  Ideal.quotEquivOfEq (ideal_smul_top_self (I ^ n))

open Classical in
theorem AdicCompletion.levelEquiv_transitionMap (I : Ideal A) {a b : ℕ}
    (hab : a ≤ b) (x : A ⧸ (I ^ b • ⊤ : Ideal A)) :
    AdicCompletion.levelEquiv I a (AdicCompletion.transitionMap I A hab x) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
        (AdicCompletion.levelEquiv I b x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : AdicCompletion.transitionMap I A hab
      (Ideal.Quotient.mk ((I ^ b • ⊤ : Ideal A)) y) =
      Ideal.Quotient.mk ((I ^ a • ⊤ : Ideal A)) y := rfl
  rw [h1, AdicCompletion.levelEquiv, AdicCompletion.levelEquiv,
    Ideal.quotEquivOfEq_mk, Ideal.quotEquivOfEq_mk, Ideal.Quotient.factor_mk]

open Classical in
/-- Adic completions along levelwise-compatible ring equivalences. -/
noncomputable def AdicCompletion.congrLevel (I : Ideal A) (J : Ideal B)
    (F : ∀ n : ℕ, (A ⧸ (I ^ n • ⊤ : Ideal A)) ≃+*
      (B ⧸ (J ^ n • ⊤ : Ideal B)))
    (hF : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ (I ^ b • ⊤ : Ideal A)),
      AdicCompletion.transitionMap J B hab (F b x) =
        F a (AdicCompletion.transitionMap I A hab x)) :
    AdicCompletion I A ≃+* AdicCompletion J B where
  toFun x := ⟨fun n => F n (x.1 n), fun {a b} hab => by
    rw [hF hab, x.2 hab]⟩
  invFun y := ⟨fun n => (F n).symm (y.1 n), fun {a b} hab => by
    have h1 := hF hab ((F b).symm (y.1 b))
    rw [RingEquiv.apply_symm_apply, y.2 hab] at h1
    exact ((F a).symm_apply_eq.mpr h1).symm⟩
  left_inv x := Subtype.ext (funext fun n => (F n).symm_apply_apply _)
  right_inv y := Subtype.ext (funext fun n => (F n).apply_symm_apply _)
  map_mul' x y := Subtype.ext (funext fun n => map_mul (F n) (x.1 n) (y.1 n))
  map_add' x y := Subtype.ext (funext fun n => map_add (F n) (x.1 n) (y.1 n))

open Classical in
/-- **Levelwise power-quotient equivalences induce an equivalence of adic
completions.** -/
noncomputable def AdicCompletion.congrPow (I : Ideal A) (J : Ideal B)
    (e : ∀ n : ℕ, (A ⧸ I ^ n) ≃+* (B ⧸ J ^ n))
    (hcomp : ∀ {a b : ℕ} (hab : a ≤ b) (x : A ⧸ I ^ b),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (e b x) =
        e a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x)) :
    AdicCompletion I A ≃+* AdicCompletion J B :=
  AdicCompletion.congrLevel I J
    (fun n => ((AdicCompletion.levelEquiv I n).trans (e n)).trans
      (AdicCompletion.levelEquiv J n).symm)
    (fun {a b} hab x => by
      simp only [RingEquiv.trans_apply]
      have h2 := AdicCompletion.levelEquiv_transitionMap J hab
        ((AdicCompletion.levelEquiv J b).symm
          (e b (AdicCompletion.levelEquiv I b x)))
      rw [RingEquiv.apply_symm_apply] at h2
      rw [hcomp hab] at h2
      have h3 := AdicCompletion.levelEquiv_transitionMap I hab x
      rw [← h3] at h2
      exact (RingEquiv.eq_symm_apply _).mpr h2)

end LevelwiseCongr

section InterleavedCongr

variable {A : Type*} [CommRing A]

open Classical in
/-- **Adic completions along interleaved towers**: if `J^(c·r) ≤ I^r ≤ J^r`
for all `r` with `1 ≤ c`, the two adic completions agree (cofinal
filtrations). -/
noncomputable def AdicCompletion.congrOfInterleaved (I J : Ideal A) (c : ℕ)
    (hc : 1 ≤ c)
    (h1 : ∀ r : ℕ, J ^ (c * r) ≤ I ^ r) (h2 : ∀ r : ℕ, I ^ r ≤ J ^ r) :
    AdicCompletion I A ≃+* AdicCompletion J A where
  toFun x := ⟨fun r => (AdicCompletion.levelEquiv J r).symm
      (Ideal.Quotient.factor (h2 r)
        (AdicCompletion.levelEquiv I r (x.1 r))), by
    intro a b hab
    have h3 := AdicCompletion.levelEquiv_transitionMap J hab
      ((AdicCompletion.levelEquiv J b).symm (Ideal.Quotient.factor (h2 b)
        (AdicCompletion.levelEquiv I b (x.1 b))))
    rw [RingEquiv.apply_symm_apply] at h3
    refine (RingEquiv.eq_symm_apply _).mpr ?_
    rw [h3]
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.levelEquiv I b (x.1 b))
    have h4 := AdicCompletion.levelEquiv_transitionMap I hab (x.1 b)
    rw [x.2 hab, ← hy] at h4
    rw [← hy, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, h4,
      Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]⟩
  invFun y := ⟨fun r => (AdicCompletion.levelEquiv I r).symm
      (Ideal.Quotient.factor (h1 r)
        (AdicCompletion.levelEquiv J (c * r) (y.1 (c * r)))), by
    intro a b hab
    have h3 := AdicCompletion.levelEquiv_transitionMap I hab
      ((AdicCompletion.levelEquiv I b).symm (Ideal.Quotient.factor (h1 b)
        (AdicCompletion.levelEquiv J (c * b) (y.1 (c * b)))))
    rw [RingEquiv.apply_symm_apply] at h3
    refine (RingEquiv.eq_symm_apply _).mpr ?_
    rw [h3]
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.levelEquiv J (c * b) (y.1 (c * b)))
    have h4 := AdicCompletion.levelEquiv_transitionMap J
      (Nat.mul_le_mul_left c hab) (y.1 (c * b))
    rw [y.2 (Nat.mul_le_mul_left c hab), ← hz] at h4
    rw [← hz, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, h4,
      Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk]⟩
  left_inv x := by
    refine Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv I r).symm
      (Ideal.Quotient.factor (h1 r)
        ((AdicCompletion.levelEquiv J (c * r))
          ((AdicCompletion.levelEquiv J (c * r)).symm
            (Ideal.Quotient.factor (h2 (c * r))
              (AdicCompletion.levelEquiv I (c * r) (x.1 (c * r))))))) = x.1 r
    rw [RingEquiv.apply_symm_apply]
    refine (RingEquiv.symm_apply_eq _).mpr ?_
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.levelEquiv I (c * r) (x.1 (c * r)))
    have hrcr : r ≤ c * r := Nat.le_mul_of_pos_left r
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hc)
    have h4 := AdicCompletion.levelEquiv_transitionMap I hrcr (x.1 (c * r))
    rw [x.2 hrcr, ← hy, Ideal.Quotient.factor_mk] at h4
    rw [← hy, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, h4]
  right_inv y := by
    refine Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv J r).symm
      (Ideal.Quotient.factor (h2 r)
        ((AdicCompletion.levelEquiv I r)
          ((AdicCompletion.levelEquiv I r).symm
            (Ideal.Quotient.factor (h1 r)
              (AdicCompletion.levelEquiv J (c * r) (y.1 (c * r))))))) = y.1 r
    rw [RingEquiv.apply_symm_apply]
    refine (RingEquiv.symm_apply_eq _).mpr ?_
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.levelEquiv J (c * r) (y.1 (c * r)))
    have hrcr : r ≤ c * r := Nat.le_mul_of_pos_left r
      (Nat.lt_of_lt_of_le Nat.zero_lt_one hc)
    have h4 := AdicCompletion.levelEquiv_transitionMap J hrcr (y.1 (c * r))
    rw [y.2 hrcr, ← hz, Ideal.Quotient.factor_mk] at h4
    rw [← hz, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk, h4]
  map_mul' x y := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (Ideal.Quotient.factor (h2 r)
        (AdicCompletion.levelEquiv I r ((x * y).1 r))) = _
    rw [show (x * y).1 r = x.1 r * y.1 r from rfl, map_mul, map_mul, map_mul]
    rfl)
  map_add' x y := Subtype.ext (funext fun r => by
    change (AdicCompletion.levelEquiv J r).symm
      (Ideal.Quotient.factor (h2 r)
        (AdicCompletion.levelEquiv I r ((x + y).1 r))) = _
    rw [show (x + y).1 r = x.1 r + y.1 r from rfl, map_add, map_add, map_add]
    rfl)

end InterleavedCongr

section PiSplit

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι]

omit [Fintype ι] in
open Classical in
/-- Powers commute with intersections of pairwise-comaximal families. -/
theorem Ideal.iInf_pow_eq_iInf_pow [Finite ι] (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j)) (r : ℕ) :
    (⨅ i, f i) ^ r = ⨅ i, (f i) ^ r := by
  classical
  let := Fintype.ofFinite ι
  classical
  have h1 : ∏ i, f i = ⨅ i, f i := by
    have h0 := Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := f) (fun i _ j _ hij => hf hij)
    simpa using h0
  have h2 : ∏ i, (f i) ^ r = ⨅ i, (f i) ^ r := by
    have h0 := Ideal.prod_eq_iInf_of_pairwise_isCoprime
      (s := Finset.univ) (J := fun i => (f i) ^ r)
      (fun i _ j _ hij => (hf hij).pow)
    simpa using h0
  rw [← h1, ← h2, ← Finset.prod_pow]

open Classical in
/-- The levelwise Chinese remainder identification for the split (hand-rolled
lift to keep elaboration cheap). -/
noncomputable def AdicCompletion.splitLevel (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j)) (r : ℕ) :
    (A ⧸ (⨅ i, f i) ^ r) ≃+* ∀ i, A ⧸ (f i) ^ r := by
  classical
  refine RingEquiv.ofBijective
    (Ideal.Quotient.lift ((⨅ i, f i) ^ r)
      (RingHom.pi fun i => Ideal.Quotient.mk ((f i) ^ r)) ?_) ⟨?_, ?_⟩
  · intro a ha
    rw [Ideal.iInf_pow_eq_iInf_pow f hf r] at ha
    funext i
    change Ideal.Quotient.mk ((f i) ^ r) a = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_iInf.mp ha i)
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.lift_mk, Ideal.Quotient.lift_mk] at hxy
    refine Ideal.Quotient.eq.mpr ?_
    rw [Ideal.iInf_pow_eq_iInf_pow f hf r]
    refine Ideal.mem_iInf.mpr fun i => ?_
    have h1 := congrFun hxy i
    change a - b ∈ (f i) ^ r
    exact Ideal.Quotient.eq.mp h1
  · intro u
    obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective
      (I := fun i => (f i) ^ r) (fun _ _ hij => (hf hij).pow) u
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.Quotient.lift_mk]
    funext i
    exact ha i

open Classical in
theorem AdicCompletion.splitLevel_mk (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j)) (r : ℕ) (y : A) :
    AdicCompletion.splitLevel f hf r (Ideal.Quotient.mk _ y) =
      fun _i => Ideal.Quotient.mk _ y := rfl

open Classical in
/-- The forward map of the completion decomposition, defined levelwise. -/
private noncomputable def AdicCompletion.piSplitForward (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j))
    (x : AdicCompletion (⨅ i, f i) A) : ∀ i, AdicCompletion (f i) A :=
  fun i => ⟨fun r => (AdicCompletion.levelEquiv (f i) r).symm
    ((AdicCompletion.splitLevel f hf r
      (AdicCompletion.levelEquiv (⨅ i, f i) r (x.1 r))) i), by
  intro a b hab
  have h3 := AdicCompletion.levelEquiv_transitionMap (f i) hab
    ((AdicCompletion.levelEquiv (f i) b).symm
      ((AdicCompletion.splitLevel f hf b
        (AdicCompletion.levelEquiv (⨅ i, f i) b (x.1 b))) i))
  rw [RingEquiv.apply_symm_apply] at h3
  refine (RingEquiv.eq_symm_apply _).mpr ?_
  rw [h3]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.levelEquiv (⨅ i, f i) b (x.1 b))
  have h4 := AdicCompletion.levelEquiv_transitionMap (⨅ i, f i) hab (x.1 b)
  rw [x.2 hab, ← hy, Ideal.Quotient.factor_mk] at h4
  rw [← hy, AdicCompletion.splitLevel_mk, h4,
    AdicCompletion.splitLevel_mk]
  rw [Ideal.Quotient.factor_mk]⟩

open Classical in
/-- The inverse map of the completion decomposition, defined by the Chinese remainder maps. -/
private noncomputable def AdicCompletion.piSplitBackward (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j))
    (y : ∀ i, AdicCompletion (f i) A) : AdicCompletion (⨅ i, f i) A :=
  ⟨fun r => (AdicCompletion.levelEquiv (⨅ i, f i) r).symm
    ((AdicCompletion.splitLevel f hf r).symm
      (fun i => AdicCompletion.levelEquiv (f i) r ((y i).1 r))), by
  intro a b hab
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
    ((AdicCompletion.splitLevel f hf b).symm
      (fun i => AdicCompletion.levelEquiv (f i) b ((y i).1 b)))
  have hz2 : (fun i => AdicCompletion.levelEquiv (f i) b ((y i).1 b)) =
      fun i => Ideal.Quotient.mk _ z := by
    rw [← AdicCompletion.splitLevel_mk f hf b z, hz,
      RingEquiv.apply_symm_apply]
  have h3 := AdicCompletion.levelEquiv_transitionMap (⨅ i, f i) hab
    ((AdicCompletion.levelEquiv (⨅ i, f i) b).symm
      ((AdicCompletion.splitLevel f hf b).symm
        (fun i => AdicCompletion.levelEquiv (f i) b ((y i).1 b))))
  rw [RingEquiv.apply_symm_apply] at h3
  refine (RingEquiv.eq_symm_apply _).mpr ?_
  rw [h3, ← hz, Ideal.Quotient.factor_mk]
  -- the a-level tuple is the constant-z tuple
  have h5 : (fun i => AdicCompletion.levelEquiv (f i) a ((y i).1 a)) =
      fun i => Ideal.Quotient.mk _ z := by
    funext i
    have h6 := AdicCompletion.levelEquiv_transitionMap (f i) hab ((y i).1 b)
    rw [(y i).2 hab] at h6
    have h7 := congrFun hz2 i
    rw [h7, Ideal.Quotient.factor_mk] at h6
    exact h6
  rw [h5, ← AdicCompletion.splitLevel_mk f hf a z,
    RingEquiv.symm_apply_apply]⟩

open Classical in
/-- **The adic completion splits along a finite pairwise-comaximal
family.** -/
noncomputable def AdicCompletion.piSplit (f : ι → Ideal A)
    (hf : Pairwise fun i j => IsCoprime (f i) (f j)) :
    AdicCompletion (⨅ i, f i) A ≃+* ∀ i, AdicCompletion (f i) A where
  toFun := AdicCompletion.piSplitForward f hf
  invFun := AdicCompletion.piSplitBackward f hf
  left_inv x := by
    refine Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv (⨅ i, f i) r).symm
      ((AdicCompletion.splitLevel f hf r).symm
        (fun i => AdicCompletion.levelEquiv (f i) r
          ((AdicCompletion.levelEquiv (f i) r).symm
            ((AdicCompletion.splitLevel f hf r
              (AdicCompletion.levelEquiv (⨅ i, f i) r (x.1 r))) i)))) = x.1 r
    have h8 : (fun i => AdicCompletion.levelEquiv (f i) r
        ((AdicCompletion.levelEquiv (f i) r).symm
          ((AdicCompletion.splitLevel f hf r
            (AdicCompletion.levelEquiv (⨅ i, f i) r (x.1 r))) i))) =
        AdicCompletion.splitLevel f hf r
          (AdicCompletion.levelEquiv (⨅ i, f i) r (x.1 r)) := by
      funext i
      rw [RingEquiv.apply_symm_apply]
    rw [h8, RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
  right_inv y := by
    refine funext fun i => Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv (f i) r).symm
      ((AdicCompletion.splitLevel f hf r
        (AdicCompletion.levelEquiv (⨅ i, f i) r
          ((AdicCompletion.levelEquiv (⨅ i, f i) r).symm
            ((AdicCompletion.splitLevel f hf r).symm
              (fun j => AdicCompletion.levelEquiv (f j) r
                ((y j).1 r)))))) i) = (y i).1 r
    rw [RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
    rw [RingEquiv.symm_apply_apply]
  map_mul' x y := by
    refine funext fun i => Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv (f i) r).symm
      ((AdicCompletion.splitLevel f hf r
        (AdicCompletion.levelEquiv (⨅ i, f i) r ((x * y).1 r))) i) = _
    rw [show (x * y).1 r = x.1 r * y.1 r from rfl, map_mul, map_mul]
    rw [show ∀ (u v : ∀ j, A ⧸ (f j) ^ r), (u * v) i = u i * v i from
      fun u v => rfl, map_mul]
    rfl
  map_add' x y := by
    refine funext fun i => Subtype.ext (funext fun r => ?_)
    change (AdicCompletion.levelEquiv (f i) r).symm
      ((AdicCompletion.splitLevel f hf r
        (AdicCompletion.levelEquiv (⨅ i, f i) r ((x + y).1 r))) i) = _
    rw [show (x + y).1 r = x.1 r + y.1 r from rfl, map_add, map_add]
    rw [show ∀ (u v : ∀ j, A ⧸ (f j) ^ r), (u + v) i = u i + v i from
      fun u v => rfl, map_add]
    rfl

open Classical in
/-- **The semilocal completion decomposition**: if `Q` lies under finitely
many pairwise-comaximal ideals whose intersection is nilpotent modulo `Q`,
the `Q`-adic completion is the product of the completions at the family. -/
noncomputable def AdicCompletion.semilocalSplit (Q : Ideal A)
    (𝔫 : ι → Ideal A) (hpair : Pairwise fun i j => IsCoprime (𝔫 i) (𝔫 j))
    (hle : ∀ i, Q ≤ 𝔫 i) (e : ℕ) (he : 1 ≤ e)
    (hnil : (⨅ i, 𝔫 i) ^ e ≤ Q) :
    AdicCompletion Q A ≃+* ∀ i, AdicCompletion (𝔫 i) A :=
  (AdicCompletion.congrOfInterleaved Q (⨅ i, 𝔫 i) e he
    (fun r => by
      rw [pow_mul]
      exact pow_le_pow_left' hnil r)
    (fun r => pow_le_pow_left' (le_iInf hle) r)).trans
    (AdicCompletion.piSplit 𝔫 hpair)

end PiSplit

section LocalizationInvariance

open IsLocalRing

variable {A : Type*} [CommRing A] (p : Ideal A) [p.IsMaximal]
variable (Rₚ : Type*) [CommRing Rₚ] [Algebra A Rₚ]
  [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]

open Classical in
/-- **Localization invariance of the maximal-adic completion**: completing at
a maximal ideal agrees with completing the localization at its maximal
ideal. -/
noncomputable def AdicCompletion.localizationEquiv :
    AdicCompletion p A ≃+* AdicCompletion (maximalIdeal Rₚ) Rₚ :=
  AdicCompletion.congrPow p (maximalIdeal Rₚ)
    (fun n => (IsLocalization.AtPrime.equivQuotMaximalIdealPow
      p Rₚ n).toRingEquiv)
    (fun {a b} hab x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
        ((IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ b)
          (Ideal.Quotient.mk _ y)) =
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow p Rₚ a)
          (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
            (Ideal.Quotient.mk _ y))
      rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
        Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
        IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk])

end LocalizationInvariance

end AdicNakayama
