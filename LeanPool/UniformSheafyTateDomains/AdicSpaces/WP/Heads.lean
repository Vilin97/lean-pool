/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Algebra
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFNoetherian
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetNoetherianVertices
import LeanPool.UniformSheafyTateDomains.AdicSpaces.SheafyRing

/-!
# The affinoid heads `𝒜_N` ([WP] §6.1, lem:finite-stage-normal-form)

The `N`-th head is the **support subalgebra** of monomials involving only
`W, U_1, …, U_N` (documented route change: the paper's quotient presentation
`𝒜_N = k⟨W,Y,Z⟩/(Y_n² − W^{2n}Z_n)` is never formed; the load-bearing content of
lem:finite-stage-normal-form — the unique factorization eq:parity-factorization and
the resulting finite free module structure over the even Tate subalgebra
`T_N = k⟨W,Z_1,…,Z_N⟩` — is established directly on the support side).

Deliverables: the head subring and its instance stack; noetherianity of the head and
of its unit ball (finite free module over the Tate algebra `K⟨W,Z⟩`, whose
noetherianity is the FJP-CDVF `Uniformizer.isNoetherianRing_P` package); **strong**
noetherianity (same argument after adjoining Tate variables — NEVER inferred from
noetherianity alone, per the prior-B2 log); head sheafiness via Wedhorn 8.28(b)
(`isSheafyFor_of_stronglyNoetherianTate` / `isSheafy_of_stronglyNoetherian_828b`);
density of the union of heads ([WP] eq:A-completion-of-heads).
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver ValuationSpectrum

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-- The `N`-th head support subring: allowed monomials involving only `W, U_1,…,U_N`
([WP] lem:finite-stage-normal-form). -/
noncomputable def wpHeadSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ, ¬ HeadMem w N t → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := fun t _ => by
    show MvPowerSeries.coeff t (0 : MvPowerSeries ℕ K) = 0
    simp
  one_mem' := fun t ht => by
    show MvPowerSeries.coeff t (1 : MvPowerSeries ℕ K) = 0
    classical
    rcases eq_or_ne t 0 with rfl | h0
    · exact absurd ⟨wpMem_zero w, fun n _ => rfl⟩ ht
    · rw [MvPowerSeries.coeff_one, if_neg h0]
  add_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 + g.1) = 0
    rw [map_add, hf t ht, hg t ht, add_zero]
  neg_mem' := fun {f} hf t ht => by
    show MvPowerSeries.coeff t (-f.1) = 0
    rw [map_neg, hf t ht, neg_zero]
  mul_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 * g.1) = 0
    classical
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpt : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hpt
    by_cases h1 : HeadMem w N p.1
    · by_cases h2 : HeadMem w N p.2
      · exact absurd (h1.add h2) ht
      · rw [hg p.2 h2, mul_zero]
    · rw [hf p.1 h1, zero_mul]

/-- The `N`-th affinoid head `𝒜_N` ([WP] §6.1). -/
abbrev WPHead : Type _ := ↥(wpHeadSupport K w N)

theorem wpHeadSupport_le_wpSupport : wpHeadSupport K w N ≤ wpSupport K w :=
  fun f hf t ht => hf t fun hh => ht hh.1

theorem wpHeadSupport_mono {N M : ℕ} (h : N ≤ M) :
    wpHeadSupport K w N ≤ wpHeadSupport K w M :=
  fun f hf t ht => hf t fun hh => ht (hh.mono h)

/-- The isometric inclusion `𝒜_N →+* 𝒜` ([WP]: "The transition maps are isometric"). -/
noncomputable def headIncl : WPHead K w N →+* WPA K w :=
  Subring.inclusion (wpHeadSupport_le_wpSupport K w N)

@[simp] theorem norm_headIncl (x : WPHead K w N) : ‖headIncl K w N x‖ = ‖x‖ := rfl

theorem isClosed_wpHeadSupport : IsClosed ((wpHeadSupport K w N : Set (Amb K))) := by
  have h := isClosed_setOf_coeff_eq_zero (R := K) (σ := ℕ) {t | HeadMem w N t}
  convert h using 1
  ext g
  exact Iff.rfl

instance : CompleteSpace (WPHead K w N) :=
  (isClosed_wpHeadSupport K w N).completeSpace_coe

instance : NormOneClass (WPHead K w N) :=
  ⟨by rw [show ‖(1 : WPHead K w N)‖ = ‖((1 : WPHead K w N) : Amb K)‖ from rfl]
      exact norm_one⟩

/-- The constant embedding `K →+* 𝒜_N`. -/
noncomputable def constHead : K →+* WPHead K w N where
  toFun x :=
    ⟨⟨MvPowerSeries.C x, MvPowerSeries.isRestrictedGauss_C _ _⟩, fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.C (σ := ℕ) x) = 0
      classical
      rw [MvPowerSeries.coeff_C, if_neg (by
        intro h; subst h; exact hs ⟨wpMem_zero w, fun n _ => rfl⟩)]⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_mul' x y := Subtype.ext (Subtype.ext (map_mul (MvPowerSeries.C (σ := ℕ)) x y))
  map_zero' := Subtype.ext (Subtype.ext (map_zero (MvPowerSeries.C (σ := ℕ) (R := K))))
  map_add' x y := Subtype.ext (Subtype.ext (map_add (MvPowerSeries.C (σ := ℕ)) x y))

@[simp] theorem headIncl_constHead (x : K) :
    headIncl K w N (constHead K w N x) = constA K w x := rfl

variable {K w N} in
/-- The pseudouniformizer of the head. -/
noncomputable def piHead (ϖ : Uniformizer K) : WPHead K w N := constHead K w N ϖ.val

variable {K w N} in
theorem norm_piHead (ϖ : Uniformizer K) : ‖piHead (w := w) (N := N) ϖ‖ = ‖ϖ.val‖ := by
  rw [show ‖piHead (w := w) (N := N) ϖ‖ =
    ‖headIncl K w N (constHead K w N ϖ.val)‖ from rfl, headIncl_constHead,
    norm_constA]

variable {K w N} in
theorem norm_piHead_lt_one (ϖ : Uniformizer K) : ‖piHead (w := w) (N := N) ϖ‖ < 1 := by
  rw [norm_piHead]; exact ϖ.norm_val_lt_one

variable {K w N} in
theorem norm_piHead_pos (ϖ : Uniformizer K) : 0 < ‖piHead (w := w) (N := N) ϖ‖ := by
  rw [norm_piHead]; exact ϖ.norm_val_pos

variable {K w N} in
theorem isUnit_piHead (ϖ : Uniformizer K) : IsUnit (piHead (w := w) (N := N) ϖ) :=
  ϖ.isUnit_val.map (constHead K w N)

variable {K w N} in
theorem norm_constHead_mul (x : K) (f : WPHead K w N) :
    ‖constHead K w N x * f‖ = ‖x‖ * ‖f‖ := by
  rw [show ‖constHead K w N x * f‖ =
      ‖headIncl K w N (constHead K w N x * f)‖ from rfl,
    map_mul, headIncl_constHead, norm_constA_mul]
  rfl

variable {K w N} in
theorem norm_piHead_mul (ϖ : Uniformizer K) (f : WPHead K w N) :
    ‖piHead ϖ * f‖ = ‖piHead (w := w) (N := N) ϖ‖ * ‖f‖ := by
  rw [norm_piHead]
  exact norm_constHead_mul ϖ.val f

variable {K w N} in
theorem isHuberRing_WPHead (ϖ : Uniformizer K) : IsHuberRing (WPHead K w N) :=
  FiniteJet.isHuberRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

variable {K w N} in
theorem isTateRing_WPHead (ϖ : Uniformizer K) : IsTateRing (WPHead K w N) :=
  FiniteJet.isTateRing_of_scale (piHead ϖ) (isUnit_piHead ϖ) (norm_piHead_lt_one ϖ)
    (norm_piHead_pos ϖ) (norm_piHead_mul ϖ)

variable {K w N} in
@[simp] theorem norm_constHead (x : K) : ‖constHead K w N x‖ = ‖x‖ := by
  rw [show ‖constHead K w N x‖ = ‖headIncl K w N (constHead K w N x)‖ from rfl,
    headIncl_constHead, norm_constA]

/-- Unconditional Huber instance via a norm-window element (the
`FJP/Over/Functoriality.lean:160` pattern — no uniformizer needed). -/
instance : IsHuberRing (WPHead K w N) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isHuberRing_of_scale (constHead K w N c) (hcu.map (constHead K w N))
    (by rw [norm_constHead]; exact hc1) (by rw [norm_constHead]; exact hc0)
    (fun f => by rw [norm_constHead_mul, norm_constHead])

instance : IsTateRing (WPHead K w N) := by
  obtain ⟨c, hcu, hc1, hc0⟩ := exists_norm_window' K
  exact FiniteJet.isTateRing_of_scale (constHead K w N c) (hcu.map (constHead K w N))
    (by rw [norm_constHead]; exact hc1) (by rw [norm_constHead]; exact hc0)
    (fun f => by rw [norm_constHead_mul, norm_constHead])

noncomputable instance : ValuationSpectrum.PlusSubring (WPHead K w N) :=
  ⟨TopologicalRing.powerBoundedSubring.toSubring (WPHead K w N)⟩

instance : ValuationSpectrum.IsRingOfIntegralElements
    ((ValuationSpectrum.ringPlus (WPHead K w N) : Subring (WPHead K w N))) :=
  FiniteJet.isRingOfIntegralElements_powerBounded

instance : IsUniformAddGroup (WPHead K w N) :=
  SeminormedAddCommGroup.to_isUniformAddGroup

instance : @CompleteSpace (WPHead K w N)
    (IsTopologicalAddGroup.rightUniformSpace (WPHead K w N)) := by
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  infer_instance

variable {K w N} in
theorem norm_wphead_mul (a b : WPHead K w N) : ‖a * b‖ = ‖a‖ * ‖b‖ := by
  show ‖((a * b : WPHead K w N) : Amb K)‖ = _
  rw [show ((a * b : WPHead K w N) : Amb K) = (a : Amb K) * (b : Amb K) from rfl,
    norm_restricted_mul_general (fun x y => norm_mul x y)]
  rfl

instance : Nontrivial (WPHead K w N) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h2 := congrArg (norm : WPHead K w N → ℝ) h
  rw [norm_zero, norm_one] at h2
  exact zero_ne_one h2

instance : NoZeroDivisors (WPHead K w N) := by
  refine ⟨fun {a b} hab => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨ha, hb⟩ := hne
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hb
  have hm := norm_wphead_mul (K := K) (w := w) (N := N) a b
  rw [hab, norm_zero] at hm
  nlinarith

/-- The heads are integral domains (isometric subrings of the multiplicative-norm
ambient; [WP] thm:parity-rationally-reduced: "The affinoid algebra `𝒜_N` is a domain
by lem:finite-stage-normal-form"). -/
instance : IsDomain (WPHead K w N) :=
  NoZeroDivisors.to_isDomain _

/-! ### Noetherianity via the finite free module structure
([WP] lem:finite-stage-normal-form: `𝒜_N ≅ ⊕_{ε ∈ {0,1}^N} k⟨W,Z⟩·Y^ε`) -/

/-- Even head membership: in the head, with all `U`-exponents even (hence weight
zero) — the exponent monoid of `T_N = K⟨W, Z_1,…,Z_N⟩`. -/
def EvenHeadMem (t : ℕ →₀ ℕ) : Prop :=
  HeadMem w N t ∧ ∀ n, n ≠ 0 → t n % 2 = 0

variable {w N} in
theorem EvenHeadMem.add {s t : ℕ →₀ ℕ} (hs : EvenHeadMem w N s)
    (ht : EvenHeadMem w N t) : EvenHeadMem w N (s + t) :=
  ⟨hs.1.add ht.1, fun n hn => by
    rw [Finsupp.add_apply]
    have h1 := hs.2 n hn
    have h2 := ht.2 n hn
    omega⟩

theorem evenHeadMem_zero : EvenHeadMem w N (0 : ℕ →₀ ℕ) :=
  ⟨⟨wpMem_zero w, fun _ _ => rfl⟩, fun _ _ => rfl⟩

noncomputable def wpEvenSupport : Subring (Amb K) where
  carrier := {f | ∀ t : ℕ →₀ ℕ,
    ¬ EvenHeadMem w N t → MvPowerSeries.coeff t f.1 = 0}
  zero_mem' := fun t _ => by
    show MvPowerSeries.coeff t (0 : MvPowerSeries ℕ K) = 0
    simp
  one_mem' := fun t ht => by
    show MvPowerSeries.coeff t (1 : MvPowerSeries ℕ K) = 0
    classical
    rcases eq_or_ne t 0 with rfl | h0
    · exact absurd (evenHeadMem_zero w N) ht
    · rw [MvPowerSeries.coeff_one, if_neg h0]
  add_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 + g.1) = 0
    rw [map_add, hf t ht, hg t ht, add_zero]
  neg_mem' := fun {f} hf t ht => by
    show MvPowerSeries.coeff t (-f.1) = 0
    rw [map_neg, hf t ht, neg_zero]
  mul_mem' := fun {f} {g} hf hg t ht => by
    show MvPowerSeries.coeff t (f.1 * g.1) = 0
    classical
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    have hpt : p.1 + p.2 = t := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hpt
    by_cases h1 : EvenHeadMem w N p.1
    · by_cases h2 : EvenHeadMem w N p.2
      · exact absurd (h1.add h2) ht
      · rw [hg p.2 h2, mul_zero]
    · rw [hf p.1 h1, zero_mul]

/-! #### The exponent halving/unhalving bijection -/

/-- The exponent embedding of `T_N`'s abstract monoid into the even head monoid:
`s ↦ W^{s 0}·∏ U_i^{2·s i}` ([WP] eq:finite-stage-substitution `Z_n ↦ U_n²`,
inverted). -/
noncomputable def unhalve (s : Fin (N + 1) →₀ ℕ) : ℕ →₀ ℕ :=
  Finsupp.single 0 (s 0) +
    2 • (Finsupp.embDomain ⟨Fin.val, Fin.val_injective⟩ s).update 0 0

variable {N} in
theorem unhalve_apply (s : Fin (N + 1) →₀ ℕ) (n : ℕ) :
    unhalve N s n =
      if n = 0 then s 0 else if h : n < N + 1 then 2 * s ⟨n, h⟩ else 0 := by
  classical
  unfold unhalve
  rw [Finsupp.add_apply, Finsupp.single_apply]
  rcases eq_or_ne n 0 with rfl | h0
  · rw [if_pos rfl, if_pos rfl]
    rw [two_nsmul, Finsupp.add_apply, Finsupp.update_apply, if_pos rfl]
    simp
  · rw [if_neg (fun h => h0 h.symm), if_neg h0, zero_add]
    rw [two_nsmul, Finsupp.add_apply, Finsupp.update_apply, if_neg h0]
    by_cases hn : n < N + 1
    · rw [dif_pos hn]
      have hemb : Finsupp.embDomain ⟨Fin.val, Fin.val_injective⟩ s n = s ⟨n, hn⟩ :=
        Finsupp.embDomain_apply_self ⟨Fin.val, Fin.val_injective⟩ s ⟨n, hn⟩
      rw [hemb]
      omega
    · rw [dif_neg hn]
      have : Finsupp.embDomain ⟨Fin.val, Fin.val_injective⟩ s n = 0 := by
        rw [Finsupp.embDomain_of_notMem_range]
        rintro ⟨i, hi⟩
        exact hn (hi ▸ i.2)
      rw [this]

variable {N} in
theorem unhalve_add (s t : Fin (N + 1) →₀ ℕ) :
    unhalve N (s + t) = unhalve N s + unhalve N t := by
  classical
  ext n
  rw [Finsupp.add_apply, unhalve_apply, unhalve_apply, unhalve_apply]
  split_ifs <;> simp [Finsupp.add_apply] <;> ring

variable {N} in
theorem unhalve_injective : Function.Injective (unhalve N) := by
  classical
  intro s t hst
  ext i
  have h := congrArg (fun u : ℕ →₀ ℕ => u i.1) hst
  rw [unhalve_apply, unhalve_apply] at h
  rcases eq_or_ne (i : ℕ) 0 with h0 | h0
  · have hi0 : i = 0 := Fin.ext h0
    subst hi0
    simpa using h
  · rw [if_neg h0, if_neg h0, dif_pos i.2, dif_pos i.2] at h
    have : s ⟨i.1, i.2⟩ = t ⟨i.1, i.2⟩ := by omega
    simpa using this

variable {w N} in
theorem evenHeadMem_unhalve (s : Fin (N + 1) →₀ ℕ) : EvenHeadMem w N (unhalve N s) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · unfold WPMem
    have hzero : wpWeight w (unhalve N s) = 0 := by
      unfold wpWeight
      refine Finset.sum_eq_zero fun n _ => ?_
      rw [unhalve_apply]
      rcases eq_or_ne n 0 with rfl | h0
      · simp
      · rw [if_neg h0]
        by_cases hn : n < N + 1
        · rw [dif_pos hn, if_neg]
          rintro ⟨hpar, -⟩
          omega
        · rw [dif_neg hn, if_neg]
          rintro ⟨hpar, -⟩
          omega
    rw [hzero]
    exact Nat.zero_le _
  · intro n hn
    rw [unhalve_apply, if_neg (by omega), dif_neg (by omega)]
  · intro n hn
    rw [unhalve_apply, if_neg hn]
    split_ifs <;> omega

/-- The exponent halving: the inverse of `unhalve` on the even head monoid. -/
noncomputable def halve (t : ℕ →₀ ℕ) : Fin (N + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i : Fin (N + 1) =>
    if i = 0 then t 0 else t i.1 / 2

variable {N} in
theorem halve_apply (t : ℕ →₀ ℕ) (i : Fin (N + 1)) :
    halve N t i = if i = 0 then t 0 else t i.1 / 2 := rfl

variable {w N} in
theorem unhalve_halve {t : ℕ →₀ ℕ} (ht : EvenHeadMem w N t) :
    unhalve N (halve N t) = t := by
  classical
  obtain ⟨⟨_, hbd⟩, hev⟩ := ht
  ext n
  rw [unhalve_apply]
  rcases eq_or_ne n 0 with rfl | h0
  · rw [if_pos rfl, halve_apply, if_pos rfl]
  · rw [if_neg h0]
    by_cases hn : n < N + 1
    · rw [dif_pos hn, halve_apply, if_neg (by
        intro h
        exact h0 (by simpa using congrArg Fin.val h))]
      have := hev n h0
      show 2 * (t n / 2) = t n
      omega
    · rw [dif_neg hn]
      exact (hbd n (by omega)).symm

variable {w N} in
/-- The even head monoid is exactly the range of `unhalve`. -/
theorem evenHeadMem_iff_mem_range_unhalve (t : ℕ →₀ ℕ) :
    EvenHeadMem w N t ↔ t ∈ Set.range (unhalve N) := by
  constructor
  · intro ht
    exact ⟨halve N t, unhalve_halve ht⟩
  · rintro ⟨s, rfl⟩
    exact evenHeadMem_unhalve s

variable {N} in
theorem halve_unhalve (s : Fin (N + 1) →₀ ℕ) : halve N (unhalve N s) = s :=
  unhalve_injective (unhalve_halve (evenHeadMem_unhalve (w := fun _ => 0) s))

variable {K w N} in
/-- The underlying coefficient-transport map. -/
noncomputable def evenToPFun (F : ↥(wpEvenSupport K w N)) :
    FiniteJet.GraphKoszul.P K (N + 1) :=
  ⟨fun s : Fin (N + 1) →₀ ℕ => MvPowerSeries.coeff (unhalve N s) F.1.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    have hnull : Filter.Tendsto
        (fun t : ℕ →₀ ℕ => ‖MvPowerSeries.coeff t F.1.1‖) Filter.cofinite (nhds 0) := by
      have h2 : Filter.Tendsto (fun t : ℕ →₀ ℕ =>
          ‖MvPowerSeries.coeff t F.1.1‖ *
            t.prod ((fun _ : ℕ => (1 : ℝ)) · ^ ·)) Filter.cofinite (nhds 0) := F.1.2
      refine h2.congr fun t => ?_
      rw [prod_one_weights, mul_one]
    have hcomp := hnull.comp ((unhalve_injective (N := N)).tendsto_cofinite)
    refine hcomp.congr fun s => ?_
    rw [prod_one_weights, mul_one]
    rfl⟩

variable {K w N} in
theorem evenToPFun_coeff (F : ↥(wpEvenSupport K w N)) (s : Fin (N + 1) →₀ ℕ) :
    MvPowerSeries.coeff s (evenToPFun F).1 = MvPowerSeries.coeff (unhalve N s) F.1.1 :=
  rfl

variable {K w N} in
/-- The coefficient-transport homomorphism `T_N →+* K⟨T_0,…,T_N⟩` along the exponent
halving. -/
noncomputable def evenToP :
    ↥(wpEvenSupport K w N) →+* FiniteJet.GraphKoszul.P K (N + 1) where
  toFun := evenToPFun
  map_zero' := Subtype.ext (MvPowerSeries.ext (by
    intro s
    rw [evenToPFun_coeff]
    show MvPowerSeries.coeff (unhalve N s) (0 : MvPowerSeries ℕ K) =
      MvPowerSeries.coeff s (0 : MvPowerSeries (Fin (N + 1)) K)
    simp))
  map_one' := Subtype.ext (MvPowerSeries.ext (by
    classical
    intro s
    rw [evenToPFun_coeff]
    show MvPowerSeries.coeff (unhalve N s) (1 : MvPowerSeries ℕ K) =
      MvPowerSeries.coeff s (1 : MvPowerSeries (Fin (N + 1)) K)
    have h0 : unhalve N (0 : Fin (N + 1) →₀ ℕ) = 0 := by
      ext n
      rw [unhalve_apply]
      split_ifs <;> simp
    rcases eq_or_ne s 0 with rfl | hs
    · rw [h0]
      simp
    · rw [MvPowerSeries.coeff_one, MvPowerSeries.coeff_one, if_neg, if_neg hs]
      intro h
      exact hs (unhalve_injective (h.trans h0.symm))))
  map_add' F G := Subtype.ext (MvPowerSeries.ext (by
    intro s
    rw [evenToPFun_coeff]
    show MvPowerSeries.coeff (unhalve N s) (F.1.1 + G.1.1) =
      MvPowerSeries.coeff s ((evenToPFun F).1 + (evenToPFun G).1)
    rw [map_add, map_add, evenToPFun_coeff, evenToPFun_coeff]))
  map_mul' F G := Subtype.ext (MvPowerSeries.ext (by
    classical
    intro s
    rw [evenToPFun_coeff]
    show MvPowerSeries.coeff (unhalve N s) (F.1.1 * G.1.1) =
      MvPowerSeries.coeff s ((evenToPFun F).1 * (evenToPFun G).1)
    rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
    have hvanish : ∀ p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ),
        p ∈ Finset.HasAntidiagonal.antidiagonal (unhalve N s) →
        ¬ (EvenHeadMem w N p.1 ∧ EvenHeadMem w N p.2) →
        MvPowerSeries.coeff p.1 F.1.1 * MvPowerSeries.coeff p.2 G.1.1 = 0 := by
      intro p _ hne
      by_cases h1 : EvenHeadMem w N p.1
      · have h2 : ¬ EvenHeadMem w N p.2 := fun h2 => hne ⟨h1, h2⟩
        rw [G.2 p.2 h2, mul_zero]
      · rw [F.2 p.1 h1, zero_mul]
    rw [← Finset.sum_filter_of_ne
      (p := fun p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) => EvenHeadMem w N p.1 ∧ EvenHeadMem w N p.2)
      (by
        intro p hp hne
        by_contra hcon
        exact hne (hvanish p hp hcon))]
    refine (Finset.sum_nbij'
      (i := fun p : (Fin (N + 1) →₀ ℕ) × (Fin (N + 1) →₀ ℕ) =>
        (unhalve N p.1, unhalve N p.2))
      (j := fun p : (ℕ →₀ ℕ) × (ℕ →₀ ℕ) => (halve N p.1, halve N p.2))
      ?_ ?_ ?_ ?_ ?_).symm
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal]
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      exact ⟨by rw [← unhalve_add, hp], evenHeadMem_unhalve p.1, evenHeadMem_unhalve p.2⟩
    · intro p hp
      rw [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [Finset.HasAntidiagonal.mem_antidiagonal]
      have := congrArg (halve N) hp.1
      rw [← unhalve_halve hp.2.1, ← unhalve_halve hp.2.2, ← unhalve_add] at hp
      exact unhalve_injective hp.1
    · intro p hp
      ext : 1 <;> simp [halve_unhalve]
    · intro p hp
      rw [Finset.mem_filter] at hp
      ext : 1 <;> simp [unhalve_halve hp.2.1, unhalve_halve hp.2.2]
    · intro p _
      rw [evenToPFun_coeff, evenToPFun_coeff]))

variable {K w N} in
theorem evenToP_coeff (F : ↥(wpEvenSupport K w N)) (s : Fin (N + 1) →₀ ℕ) :
    MvPowerSeries.coeff s (evenToP F).1 = MvPowerSeries.coeff (unhalve N s) F.1.1 :=
  rfl

variable {K w N} in
theorem evenToP_bijective : Function.Bijective (evenToP (K := K) (w := w) (N := N)) := by
  classical
  constructor
  · intro F G h
    refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun t => ?_))
    by_cases ht : EvenHeadMem w N t
    · have := congrArg (fun x : FiniteJet.GraphKoszul.P K (N + 1) =>
        MvPowerSeries.coeff (halve N t) x.1) h
      simp only [evenToP_coeff, unhalve_halve ht] at this
      exact this
    · rw [F.2 t ht, G.2 t ht]
  · intro G
    classical
    have hbwd_res : MvPowerSeries.IsRestrictedGauss (fun _ : ℕ => (1 : ℝ))
        (fun t => if _ : EvenHeadMem w N t then
          MvPowerSeries.coeff (halve N t) G.1 else 0) := by
      have hchar : ∀ ε : ℝ, 0 < ε → {t : ℕ →₀ ℕ |
          ε ≤ ‖(if _ : EvenHeadMem w N t then
            MvPowerSeries.coeff (halve N t) G.1 else 0 : K)‖}.Finite := by
        intro ε hε
        have hfin := finite_setOf_le_norm_coeff (f := G) hε
        refine (hfin.image (unhalve N)).subset ?_
        intro t ht
        rw [Set.mem_setOf_eq] at ht
        by_cases hmem : EvenHeadMem w N t
        · rw [dif_pos hmem] at ht
          exact ⟨halve N t, ht, unhalve_halve hmem⟩
        · rw [dif_neg hmem, norm_zero] at ht
          exact absurd (hε.trans_le ht) (lt_irrefl 0)
      show Filter.Tendsto _ Filter.cofinite (nhds 0)
      rw [Metric.tendsto_nhds]
      intro ε hε
      rw [Filter.eventually_cofinite]
      refine (hchar ε hε).subset ?_
      intro t ht
      rw [Set.mem_setOf_eq] at ht ⊢
      rw [Real.dist_eq, sub_zero, prod_one_weights, mul_one] at ht
      rw [abs_of_nonneg (norm_nonneg _)] at ht
      exact not_lt.mp ht
    refine ⟨⟨⟨fun t => if _ : EvenHeadMem w N t then
        MvPowerSeries.coeff (halve N t) G.1 else 0, hbwd_res⟩,
      fun t ht => by
        show (if _ : EvenHeadMem w N t then
          MvPowerSeries.coeff (halve N t) G.1 else 0) = 0
        rw [dif_neg ht]⟩, ?_⟩
    refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
    rw [evenToP_coeff]
    show (if _ : EvenHeadMem w N (unhalve N s) then
      MvPowerSeries.coeff (halve N (unhalve N s)) G.1 else 0) = _
    rw [dif_pos (evenHeadMem_unhalve s), halve_unhalve]

/-- `T_N` is isometrically isomorphic to the Tate algebra `K⟨T_0,…,T_N⟩ = P K (N+1)`
(the exponent-halving reindexing `(a, 2ν) ↦ (a, ν)`; [WP]
eq:finite-stage-normal-form). -/
noncomputable def evenSupportEquiv :
    ↥(wpEvenSupport K w N) ≃+* FiniteJet.GraphKoszul.P K (N + 1) :=
  RingEquiv.ofBijective evenToP evenToP_bijective

theorem norm_evenSupportEquiv (x : ↥(wpEvenSupport K w N)) :
    ‖evenSupportEquiv K w N x‖ = ‖x‖ := by
  classical
  have hLHS : ‖evenSupportEquiv K w N x‖ =
      ⨆ s : Fin (N + 1) →₀ ℕ, ‖MvPowerSeries.coeff (unhalve N s) x.1.1‖ := by
    rw [show ‖evenSupportEquiv K w N x‖ =
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : Fin (N + 1) => (1 : ℝ))
        (evenToP (K := K) (w := w) (N := N) x).1 from rfl, MvPowerSeries.gaussNorm]
    exact iSup_congr fun s => by
      rw [prod_one_weights, mul_one, evenToP_coeff]
  have hRHS : ‖x‖ = ⨆ t : ℕ →₀ ℕ, ‖MvPowerSeries.coeff t x.1.1‖ := by
    rw [show ‖x‖ =
      MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : ℕ => (1 : ℝ)) x.1.1 from rfl,
      MvPowerSeries.gaussNorm]
    exact iSup_congr fun t => by rw [prod_one_weights, mul_one]
  rw [hLHS, hRHS]
  have hbddR : ∀ t : ℕ →₀ ℕ, ‖MvPowerSeries.coeff t x.1.1‖ ≤ ‖x‖ := fun t =>
    norm_coeff_le_one_norm x.1 t
  have hbddL : ∀ s : Fin (N + 1) →₀ ℕ,
      ‖MvPowerSeries.coeff (unhalve N s) x.1.1‖ ≤ ‖x‖ := fun s => hbddR _
  apply le_antisymm
  · refine ciSup_le fun s => ?_
    exact le_ciSup ⟨‖x‖, Set.forall_mem_range.mpr hbddR⟩ (unhalve N s)
  · refine ciSup_le fun t => ?_
    by_cases hmem : EvenHeadMem w N t
    · have h1 : MvPowerSeries.coeff t x.1.1 =
          MvPowerSeries.coeff (unhalve N (halve N t)) x.1.1 := by
        rw [unhalve_halve hmem]
      rw [h1]
      exact le_ciSup ⟨‖x‖, Set.forall_mem_range.mpr hbddL⟩ (halve N t)
    · rw [x.2 t hmem, norm_zero]
      have h0 := hbddL 0
      refine le_trans ?_ (le_ciSup ⟨‖x‖, Set.forall_mem_range.mpr hbddL⟩ 0)
      exact norm_nonneg _

theorem wpEvenSupport_le_wpHeadSupport :
    wpEvenSupport K w N ≤ wpHeadSupport K w N :=
  fun f hf t ht => hf t fun hh => ht hh.1

/-! #### Parity patterns and the free generators `Y^ε` -/

/-- The exponent of the pattern monomial `Y^ε = ∏_{i : ε i} Y_{i+1}`
([WP] eq:parity-factorization: `ν_n = 2q_n + ε_n`). -/
noncomputable def patExp (ε : Fin N → Bool) : ℕ →₀ ℕ :=
  ∑ i : Fin N, if ε i then Finsupp.single 0 (w (i.1 + 1)) + Finsupp.single (i.1 + 1) 1
    else 0

variable {w N} in
theorem patExp_apply_zero (ε : Fin N → Bool) :
    patExp w N ε 0 = ∑ i : Fin N, if ε i then w (i.1 + 1) else 0 := by
  classical
  unfold patExp
  rw [Finset.sum_apply']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_pos rfl, if_neg (by omega), add_zero]
  · simp

variable {w N} in
theorem patExp_apply_succ (ε : Fin N → Bool) (i : Fin N) :
    patExp w N ε (i.1 + 1) = if ε i then 1 else 0 := by
  classical
  unfold patExp
  rw [Finset.sum_apply']
  rw [Finset.sum_eq_single i]
  · split_ifs with hi
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (by omega), if_pos rfl, zero_add]
    · simp
  · intro j _ hj
    split_ifs with hj'
    · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
        if_neg (by omega), if_neg (by
          intro h
          exact hj (Fin.ext (by omega))), add_zero]
    · simp
  · intro h
    exact absurd (Finset.mem_univ _) h

variable {w N} in
theorem patExp_apply_out (ε : Fin N → Bool) {n : ℕ} (h0 : n ≠ 0)
    (hbd : ¬ (1 ≤ n ∧ n ≤ N)) : patExp w N ε n = 0 := by
  classical
  unfold patExp
  rw [Finset.sum_apply']
  refine Finset.sum_eq_zero fun i _ => ?_
  split_ifs with hi
  · rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply,
      if_neg (by omega), if_neg (by
        intro h
        have := i.isLt
        omega), add_zero]
  · simp

variable {w N} in
theorem headMem_patExp (ε : Fin N → Bool) : HeadMem w N (patExp w N ε) := by
  classical
  constructor
  · unfold WPMem
    have hw : wpWeight w (patExp w N ε) =
        ∑ i : Fin N, if ε i then w (i.1 + 1) else 0 := by
      have hsub : (patExp w N ε).support ⊆
          insert 0 (Finset.univ.image fun i : Fin N => i.1 + 1) := by
        intro n hn
        rw [Finsupp.mem_support_iff] at hn
        rw [Finset.mem_insert]
        by_cases h0 : n = 0
        · exact Or.inl h0
        · refine Or.inr (Finset.mem_image.mpr ?_)
          by_cases hbd : 1 ≤ n ∧ n ≤ N
          · exact ⟨⟨n - 1, by omega⟩, Finset.mem_univ _,
              by show n - 1 + 1 = n; omega⟩
          · exact absurd (patExp_apply_out ε h0 hbd) hn
      rw [wpWeight_eq_sum_subset w hsub, Finset.sum_insert (by
        rw [Finset.mem_image]
        rintro ⟨i, -, hi⟩
        omega)]
      have h0term : (if (patExp w N ε) 0 % 2 = 1 ∧ (0 : ℕ) ≠ 0 then w 0 else 0) = 0 := by
        simp
      rw [h0term, zero_add,
        Finset.sum_image (fun i _ j _ h => Fin.ext (by omega))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [patExp_apply_succ]
      rcases hb : ε i with _ | _ <;> simp [hb]
    rw [hw, patExp_apply_zero]
  · intro n hn
    exact patExp_apply_out ε (by omega) (by omega)

/-- The pattern generator `Y^ε` as a head element. -/
noncomputable def Ypat (ε : Fin N → Bool) : WPHead K w N :=
  ⟨⟨MvPowerSeries.monomial (patExp w N ε) 1,
    MvPowerSeries.isRestrictedGauss_monomial _ _ _⟩, fun s hs => by
      show MvPowerSeries.coeff s (MvPowerSeries.monomial (patExp w N ε) 1) = 0
      classical
      rw [MvPowerSeries.coeff_monomial,
        if_neg (by intro h; subst h; exact hs (headMem_patExp ε))]⟩

/-! #### The parity-slice decomposition ([WP] eq:parity-factorization) -/

variable {N} in
/-- The parity pattern of an exponent. -/
noncomputable def patOf (t : ℕ →₀ ℕ) : Fin N → Bool := fun i =>
  decide (t (i.1 + 1) % 2 = 1)

open scoped Classical in
variable {K w N} in
/-- The `ε`-slice of a head element: the even-head series of coefficients at
`(· + Y^ε-exponent)`. -/
noncomputable def slice (ε : Fin N → Bool) (f : WPHead K w N) :
    ↥(wpEvenSupport K w N) := by
  classical
  refine ⟨⟨fun u => if EvenHeadMem w N u then
    MvPowerSeries.coeff (u + patExp w N ε) f.1.1 else 0, ?_⟩, fun u hu => by
      show (if EvenHeadMem w N u then
        MvPowerSeries.coeff (u + patExp w N ε) f.1.1 else 0) = 0
      rw [if_neg hu]⟩
  show MvPowerSeries.IsRestrictedGauss _ _
  have hchar : ∀ ε' : ℝ, 0 < ε' → {u : ℕ →₀ ℕ |
      ε' ≤ ‖(if EvenHeadMem w N u then
        MvPowerSeries.coeff (u + patExp w N ε) f.1.1 else 0 : K)‖}.Finite := by
    intro ε' hε'
    have hfin := finite_setOf_le_norm_coeff (f := f.1) hε'
    refine (hfin.preimage
      (Set.injOn_of_injective (add_left_injective (patExp w N ε)))).subset ?_
    intro u hu
    rw [Set.mem_setOf_eq] at hu
    by_cases hmem : EvenHeadMem w N u
    · rw [if_pos hmem] at hu
      exact hu
    · rw [if_neg hmem, norm_zero] at hu
      exact absurd (hε'.trans_le hu) (lt_irrefl 0)
  show Filter.Tendsto _ Filter.cofinite (nhds 0)
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  rw [Filter.eventually_cofinite]
  refine (hchar ε' hε').subset ?_
  intro u hu
  rw [Set.mem_setOf_eq] at hu ⊢
  rw [Real.dist_eq, sub_zero, prod_one_weights, mul_one] at hu
  rw [abs_of_nonneg (norm_nonneg _)] at hu
  exact not_lt.mp hu

open scoped Classical in
variable {K w N} in
theorem slice_coeff (ε : Fin N → Bool) (f : WPHead K w N) (u : ℕ →₀ ℕ) :
    MvPowerSeries.coeff u (slice ε f).1.1 =
      if EvenHeadMem w N u then
        MvPowerSeries.coeff (u + patExp w N ε) f.1.1 else 0 := rfl

variable {w N} in
theorem wpWeight_eq_zero_of_even {t : ℕ →₀ ℕ} (h : ∀ n, n ≠ 0 → t n % 2 = 0) :
    wpWeight w t = 0 := by
  unfold wpWeight
  refine Finset.sum_eq_zero fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | h0
  · simp
  · rw [if_neg]
    rintro ⟨hpar, -⟩
    have := h n h0
    omega

variable {w N} in
/-- On a head exponent, the parity weight is the pattern sum. -/
theorem wpWeight_head_eq_patSum {t : ℕ →₀ ℕ} (hhead : HeadMem w N t) :
    wpWeight w t = ∑ i : Fin N, if patOf (N := N) t i then w (i.1 + 1) else 0 := by
  classical
  have hsub : t.support ⊆ insert 0 (Finset.univ.image fun i : Fin N => i.1 + 1) := by
    intro m hm
    rw [Finsupp.mem_support_iff] at hm
    rw [Finset.mem_insert]
    by_cases hm0 : m = 0
    · exact Or.inl hm0
    · refine Or.inr (Finset.mem_image.mpr ?_)
      by_cases hbd : 1 ≤ m ∧ m ≤ N
      · exact ⟨⟨m - 1, by omega⟩, Finset.mem_univ _, by show m - 1 + 1 = m; omega⟩
      · exact absurd (hhead.2 m (by omega)) hm
  rw [wpWeight_eq_sum_subset w hsub, Finset.sum_insert (by
    rw [Finset.mem_image]
    rintro ⟨i, -, hi⟩
    omega)]
  rw [show (if t 0 % 2 = 1 ∧ (0 : ℕ) ≠ 0 then w 0 else 0) = 0 by simp, zero_add,
    Finset.sum_image (fun i _ j _ h => Fin.ext (by omega))]
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold patOf
  rcases hb : decide (t (i.1 + 1) % 2 = 1) with _ | _
  · rw [if_neg (by simpa using of_decide_eq_false hb), if_neg (by simp [hb])]
  · rw [if_pos ⟨of_decide_eq_true hb, by omega⟩, if_pos (by simp [hb])]

variable {w N} in
/-- (A) The pattern exponent of a head exponent divides it. -/
theorem patExp_patOf_le {t : ℕ →₀ ℕ} (hhead : HeadMem w N t) :
    patExp w N (patOf t) ≤ t := by
  classical
  intro n
  rcases eq_or_ne n 0 with rfl | h0
  · rw [patExp_apply_zero]
    exact le_trans (le_of_eq (wpWeight_head_eq_patSum hhead).symm) hhead.1
  · by_cases hbd : 1 ≤ n ∧ n ≤ N
    · obtain ⟨i, rfl⟩ : ∃ i : Fin N, i.1 + 1 = n :=
        ⟨⟨n - 1, by omega⟩, by show n - 1 + 1 = n; omega⟩
      rw [patExp_apply_succ]
      unfold patOf
      rcases hb : decide (t (i.1 + 1) % 2 = 1) with _ | _
      · simp
      · rw [if_pos rfl]
        have := of_decide_eq_true hb
        omega
    · rw [patExp_apply_out _ h0 hbd]
      exact Nat.zero_le _

variable {w N} in
/-- (B) Subtracting the pattern exponent of a head exponent leaves an even head
exponent. -/
theorem evenHeadMem_sub_patExp {t : ℕ →₀ ℕ} (hhead : HeadMem w N t) :
    EvenHeadMem w N (t - patExp w N (patOf t)) := by
  classical
  have heven : ∀ n, n ≠ 0 → (t - patExp w N (patOf t)) n % 2 = 0 := by
    intro n h0
    rw [Finsupp.tsub_apply]
    by_cases hbd : 1 ≤ n ∧ n ≤ N
    · obtain ⟨i, rfl⟩ : ∃ i : Fin N, i.1 + 1 = n :=
        ⟨⟨n - 1, by omega⟩, by show n - 1 + 1 = n; omega⟩
      rw [patExp_apply_succ]
      unfold patOf
      rcases hb : decide (t (i.1 + 1) % 2 = 1) with _ | _
      · have := of_decide_eq_false hb
        simp only [Bool.false_eq_true, if_false]
        omega
      · have := of_decide_eq_true hb
        simp only [if_true]
        omega
    · rw [patExp_apply_out _ h0 hbd]
      by_cases hN : N < n
      · rw [hhead.2 n hN]
      · omega
  refine ⟨⟨?_, ?_⟩, heven⟩
  · unfold WPMem
    rw [wpWeight_eq_zero_of_even heven]
    exact Nat.zero_le _
  · intro n hn
    rw [Finsupp.tsub_apply, hhead.2 n hn]
    simp

variable {w N} in
/-- (C) The conditions select a unique pattern. -/
theorem patOf_eq_of_evenSub {t : ℕ →₀ ℕ} {ε : Fin N → Bool}
    (hle : patExp w N ε ≤ t) (hev : EvenHeadMem w N (t - patExp w N ε)) :
    ε = patOf t := by
  classical
  funext i
  have h1 := hev.2 (i.1 + 1) (by omega)
  rw [Finsupp.tsub_apply, patExp_apply_succ] at h1
  have h2 := hle (i.1 + 1)
  rw [patExp_apply_succ] at h2
  unfold patOf
  rcases hb : ε i with _ | _ <;> rw [hb] at h1 h2 <;>
    simp only [Bool.false_eq_true, if_false, if_true] at h1 h2
  · rw [Nat.sub_zero] at h1
    exact (decide_eq_false (by omega)).symm
  · exact (decide_eq_true (by omega)).symm

variable {K w N} in
/-- **The parity-slice decomposition** ([WP] eq:parity-factorization /
lem:finite-stage-normal-form): every head element is the sum over the `2^N` parity
patterns of an even-head slice times the pattern generator. -/
theorem sum_slice_mul_Ypat (f : WPHead K w N) :
    (∑ ε : Fin N → Bool,
      (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)) (slice ε f) *
        Ypat K w N ε) = f := by
  classical
  refine Subtype.ext (Subtype.ext (MvPowerSeries.ext fun t => ?_))
  let V : WPHead K w N →+* MvPowerSeries ℕ K :=
    ((MvPowerSeries.isSubring (fun _ : ℕ => (1 : ℝ))).subtype).comp
      (wpHeadSupport K w N).subtype
  have hV : ∀ g : WPHead K w N, V g = g.1.1 := fun _ => rfl
  have hsum : ((∑ ε : Fin N → Bool,
      (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)) (slice ε f) *
        Ypat K w N ε : WPHead K w N)).1.1 =
      ∑ ε : Fin N → Bool, (slice ε f).1.1 *
        MvPowerSeries.monomial (patExp w N ε) (1 : K) := by
    rw [← hV, map_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    rw [map_mul]
    rfl
  show MvPowerSeries.coeff t ((∑ ε : Fin N → Bool,
      (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)) (slice ε f) *
        Ypat K w N ε : WPHead K w N)).1.1 = MvPowerSeries.coeff t f.1.1
  rw [hsum, map_sum]
  have hterm : ∀ ε : Fin N → Bool,
      MvPowerSeries.coeff t ((slice ε f).1.1 *
        MvPowerSeries.monomial (patExp w N ε) (1 : K)) =
      if patExp w N ε ≤ t ∧ EvenHeadMem w N (t - patExp w N ε) then
        MvPowerSeries.coeff t f.1.1 else 0 := by
    intro ε
    rw [MvPowerSeries.coeff_mul_monomial]
    by_cases hle : patExp w N ε ≤ t
    · rw [if_pos hle, slice_coeff, mul_one]
      by_cases hev : EvenHeadMem w N (t - patExp w N ε)
      · rw [if_pos hev, if_pos ⟨hle, hev⟩, tsub_add_cancel_of_le hle]
      · rw [if_neg hev, if_neg (fun h => hev h.2)]
    · rw [if_neg hle, if_neg (fun h => hle h.1)]
  rw [Finset.sum_congr rfl fun ε _ => hterm ε]
  rw [Finset.sum_eq_single (patOf t)]
  · by_cases hhead : HeadMem w N t
    · rw [if_pos ⟨patExp_patOf_le hhead, evenHeadMem_sub_patExp hhead⟩]
    · rw [f.2 t hhead]
      split_ifs <;> rfl
  · intro ε _ hne
    rw [if_neg]
    rintro ⟨hle, hev⟩
    exact hne (patOf_eq_of_evenSub hle hev)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The head is a finite module over its even Tate subalgebra — the formal content of
the rank-`2^N` free normal form [WP] eq:finite-stage-normal-form. -/
theorem moduleFinite_head_over_even :
    letI : Algebra ↥(wpEvenSupport K w N) (WPHead K w N) :=
      (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)).toAlgebra
    Module.Finite ↥(wpEvenSupport K w N) (WPHead K w N) := by
  classical
  letI : Algebra ↥(wpEvenSupport K w N) (WPHead K w N) :=
    (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)).toAlgebra
  refine ⟨⟨Finset.univ.image (Ypat K w N), ?_⟩⟩
  rw [eq_top_iff]
  intro f _
  rw [← sum_slice_mul_Ypat f]
  refine Submodule.sum_mem _ fun ε _ => ?_
  have hsmul : (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
      (slice ε f) * Ypat K w N ε = (slice ε f) • Ypat K w N ε := by
    rw [Algebra.smul_def]
    rfl
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ ε))))

variable {K} in
/-- **The heads are noetherian** ([WP]: "`𝒜_N` is affinoid"; via
`IsNoetherianRing.of_finite` over `T_N ≅ P K (N+1)`, whose noetherianity is
`FiniteJetOver.Uniformizer.isNoetherianRing_P`). -/
theorem isNoetherianRing_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsNoetherianRing (WPHead K w N) := by
  haveI hP : IsNoetherianRing (FiniteJet.GraphKoszul.P K (N + 1)) :=
    ϖ.isNoetherianRing_P hK₀ (N + 1)
  haveI hTN : IsNoetherianRing ↥(wpEvenSupport K w N) :=
    isNoetherianRing_of_ringEquiv _ (evenSupportEquiv K w N).symm
  letI : Algebra ↥(wpEvenSupport K w N) (WPHead K w N) :=
    (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)).toAlgebra
  haveI : Module.Finite ↥(wpEvenSupport K w N) (WPHead K w N) :=
    moduleFinite_head_over_even K w N
  exact IsNoetherianRing.of_finite ↥(wpEvenSupport K w N) (WPHead K w N)

open scoped Classical in
variable {K w N} in
/-- Slices do not increase the norm (their coefficients are a subfamily of `f`'s). -/
theorem norm_slice_le (ε : Fin N → Bool) (f : WPHead K w N) :
    ‖slice ε f‖ ≤ ‖f‖ := by
  have hb : ∀ u : ℕ →₀ ℕ, ‖MvPowerSeries.coeff u (slice ε f).1.1‖ ≤ ‖f‖ := by
    intro u
    rw [slice_coeff]
    by_cases hev : EvenHeadMem w N u
    · rw [if_pos hev]
      exact norm_coeff_le_one_norm f.1 _
    · rw [if_neg hev, norm_zero]
      exact norm_nonneg _
  rw [show ‖slice ε f‖ =
    MvPowerSeries.gaussNorm (norm : K → ℝ) (fun _ : ℕ => (1 : ℝ)) (slice ε f).1.1
    from rfl, MvPowerSeries.gaussNorm]
  refine ciSup_le fun u => ?_
  rw [prod_one_weights, mul_one]
  exact hb u

variable {K} in
/-- The unit ball of the head is noetherian (needed by the graph-Koszul layer at the
head; same finite-module argument over the unit ball of `P K (N+1)`,
`FiniteJetOver.Uniformizer.isNoetherianRing_unitBall_P`). -/
theorem isNoetherianRing_unitBall_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsNoetherianRing (FiniteJet.unitBall (WPHead K w N)) := by
  classical
  haveI hPball : IsNoetherianRing
      ↥(FiniteJet.unitBall (FiniteJet.GraphKoszul.P K (N + 1))) :=
    ϖ.isNoetherianRing_unitBall_P hK₀ (N + 1)
  have heq : ∀ y, ‖(evenSupportEquiv K w N).symm y‖ = ‖y‖ := by
    intro y
    rw [← norm_evenSupportEquiv K w N ((evenSupportEquiv K w N).symm y),
      RingEquiv.apply_symm_apply]
  haveI hEball : IsNoetherianRing ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N)) :=
    FiniteJet.isNoetherianRing_unitBall_of_isometry
      (evenSupportEquiv K w N).symm heq hPball
  -- the ball-level inclusion of the even part
  set ι : ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N)) →+*
      ↥(FiniteJet.unitBall (WPHead K w N)) :=
    RingHom.codRestrict
      ((Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)).comp
        (FiniteJet.unitBall ↥(wpEvenSupport K w N)).subtype)
      (FiniteJet.unitBall (WPHead K w N)) (fun x => by
        rw [FiniteJet.mem_unitBall_iff]
        show ‖Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N) x.1‖ ≤ 1
        rw [show ‖Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N) x.1‖ =
          ‖x.1‖ from rfl]
        exact (FiniteJet.mem_unitBall_iff _ _).mp x.2) with hι_def
  letI : Algebra ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))
      ↥(FiniteJet.unitBall (WPHead K w N)) := ι.toAlgebra
  haveI hMF : Module.Finite ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))
      ↥(FiniteJet.unitBall (WPHead K w N)) := by
    -- ball-level generators and slices
    have hYb : ∀ ε : Fin N → Bool, Ypat K w N ε ∈ FiniteJet.unitBall (WPHead K w N) := by
      intro ε
      rw [FiniteJet.mem_unitBall_iff]
      rw [show ‖Ypat K w N ε‖ = MvPowerSeries.gaussNorm (norm : K → ℝ)
        (fun _ : ℕ => (1 : ℝ)) (Ypat K w N ε).1.1 from rfl, MvPowerSeries.gaussNorm]
      refine ciSup_le fun t => ?_
      rw [prod_one_weights, mul_one]
      show ‖MvPowerSeries.coeff t (MvPowerSeries.monomial (patExp w N ε) (1 : K))‖ ≤ 1
      rw [MvPowerSeries.coeff_monomial]
      split_ifs <;> simp
    refine ⟨⟨Finset.univ.image fun ε : Fin N → Bool =>
      (⟨Ypat K w N ε, hYb ε⟩ : ↥(FiniteJet.unitBall (WPHead K w N))), ?_⟩⟩
    rw [eq_top_iff]
    rintro ⟨f, hf⟩ _
    have hsb : ∀ ε : Fin N → Bool, slice ε f ∈
        FiniteJet.unitBall ↥(wpEvenSupport K w N) := by
      intro ε
      rw [FiniteJet.mem_unitBall_iff]
      exact (norm_slice_le ε f).trans ((FiniteJet.mem_unitBall_iff _ _).mp hf)
    have hidentity : (∑ ε : Fin N → Bool,
        (⟨slice ε f, hsb ε⟩ : ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))) •
          (⟨Ypat K w N ε, hYb ε⟩ : ↥(FiniteJet.unitBall (WPHead K w N)))) =
        ⟨f, hf⟩ := by
      refine Subtype.ext ?_
      have hval : ((∑ ε : Fin N → Bool,
          (⟨slice ε f, hsb ε⟩ : ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))) •
            (⟨Ypat K w N ε, hYb ε⟩ : ↥(FiniteJet.unitBall (WPHead K w N)))) :
          ↥(FiniteJet.unitBall (WPHead K w N))).1 =
          ∑ ε : Fin N → Bool,
            (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N)) (slice ε f) *
              Ypat K w N ε := by
        show (FiniteJet.unitBall (WPHead K w N)).subtype (∑ ε : Fin N → Bool,
          (⟨slice ε f, hsb ε⟩ : ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))) •
            (⟨Ypat K w N ε, hYb ε⟩ : ↥(FiniteJet.unitBall (WPHead K w N)))) = _
        rw [map_sum]
        refine Finset.sum_congr rfl fun ε _ => ?_
        rw [Algebra.smul_def]
        rfl
      rw [hval, sum_slice_mul_Ypat]
    rw [← hidentity]
    refine Submodule.sum_mem _ fun ε _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span
      (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ ε))))
  exact IsNoetherianRing.of_finite ↥(FiniteJet.unitBall ↥(wpEvenSupport K w N))
    ↥(FiniteJet.unitBall (WPHead K w N))

variable {K} in
/-! #### Generalized scale-bundle noetherianity (port of `CDVFNoetherian` to an
arbitrary normed base) and isometric transport of restricted series -/

section ScaleNoetherian

variable {E : Type*} [NormedCommRing E] [IsUltrametricDist E] [NormOneClass E]
  [CompleteSpace E]

/-- `CDVFNoetherian.isNoetherianRing_unitBall_P`, generalized from the base field to
any complete normed ultrametric base with a norm-scaling pseudouniformizer. -/
theorem isNoetherianRing_unitBall_P_of_scale (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀ : IsNoetherianRing (FiniteJet.unitBall E)) (m : ℕ) :
    IsNoetherianRing ↥(FiniteJet.unitBall (FiniteJet.GraphKoszul.P E m)) := by
  haveI := hE₀
  haveI hcomp : IsNoetherianRing (AdicCompletion
      (FiniteJet.GraphKoszul.I0 t ht1)
      (MvPolynomial (Fin m) ↥(FiniteJet.unitBall E))) :=
    AdicCompletion.isNoetherianRing_span_singleton _ _
  exact isNoetherianRing_of_ringEquiv _
    (FiniteJet.GraphKoszul.ballAdicEquiv (E := E) (m := m) t htu ht1 ht0 hscale).symm

/-- `CDVFNoetherian.isNoetherianRing_P`, generalized to any scale-bundle base:
`E⟨T₁,…,T_m⟩` is the localization of its noetherian unit ball at the scaling
constant. -/
theorem isNoetherianRing_P_of_scale (t : E) (htu : IsUnit t) (ht1 : ‖t‖ < 1)
    (ht0 : 0 < ‖t‖) (hscale : ∀ x : E, ‖t * x‖ = ‖t‖ * ‖x‖)
    (hE₀ : IsNoetherianRing (FiniteJet.unitBall E)) (m : ℕ) :
    IsNoetherianRing (FiniteJet.GraphKoszul.P E m) := by
  haveI hball := isNoetherianRing_unitBall_P_of_scale t htu ht1 ht0 hscale hE₀ m
  letI : Algebra ↥(FiniteJet.unitBall (FiniteJet.GraphKoszul.P E m))
      (FiniteJet.GraphKoszul.P E m) :=
    (FiniteJet.unitBall (FiniteJet.GraphKoszul.P E m)).subtype.toAlgebra
  set s : ↥(FiniteJet.unitBall (FiniteJet.GraphKoszul.P E m)) :=
    ⟨FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t),
      (FiniteJet.mem_unitBall_iff _ _).mpr (by
        rw [FiniteJet.GraphKoszul.norm_tP t hscale]
        exact ht1.le)⟩ with hs
  haveI hloc : IsLocalization (Submonoid.powers s) (FiniteJet.GraphKoszul.P E m) := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨y, k, rfl⟩
      show IsUnit ((FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t) :
        FiniteJet.GraphKoszul.P E m) ^ k)
      exact (FiniteJet.GraphKoszul.isUnit_tP t htu).pow k
    · intro F
      obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖t‖ ^ n * ‖F‖ ≤ 1 := by
        rcases eq_or_ne ‖F‖ 0 with h0 | h0
        · exact ⟨0, by rw [h0, mul_zero]; exact zero_le_one⟩
        · have hpos : 0 < ‖F‖ := lt_of_le_of_ne (norm_nonneg F) (Ne.symm h0)
          obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr hpos) ht1
          exact ⟨n, by
            calc ‖t‖ ^ n * ‖F‖ ≤ ‖F‖⁻¹ * ‖F‖ :=
                  mul_le_mul_of_nonneg_right hn.le (norm_nonneg _)
              _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)⟩
      have hmem : ‖FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t) ^ n * F‖ ≤ 1 := by
        rw [FiniteJet.norm_pow_mul_of_scale (E := FiniteJet.GraphKoszul.P E m)
          (fun G => by
            rw [FiniteJet.GraphKoszul.norm_tP t hscale]
            exact FiniteJet.GraphKoszul.norm_tP_mul t hscale G) n,
          FiniteJet.GraphKoszul.norm_tP t hscale]
        exact hn
      refine ⟨(⟨FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t) ^ n * F, hmem⟩,
        ⟨s ^ n, n, rfl⟩), ?_⟩
      show F * (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t) :
        FiniteJet.GraphKoszul.P E m) ^ n =
        FiniteJet.GraphKoszul.polyToP (MvPolynomial.C t) ^ n * F
      exact mul_comm F _
    · intro x y h
      refine ⟨1, ?_⟩
      have hinj : Function.Injective
          ((FiniteJet.unitBall (FiniteJet.GraphKoszul.P E m)).subtype) :=
        Subtype.val_injective
      rw [hinj h]
  exact IsLocalization.isNoetherianRing (Submonoid.powers s)
    (FiniteJet.GraphKoszul.P E m) hball

end ScaleNoetherian

section RestrictedTransport

variable {R S : Type*} [NormedCommRing R] [IsUltrametricDist R]
  [NormedCommRing S] [IsUltrametricDist S] {σ : Type*}

/-- Norm-nonincreasing coefficientwise transport of radius-one restricted series
along a ring homomorphism. -/
noncomputable def mvRestrictedMapHom (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖) :
    MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) →+*
      MvPowerSeries.Restricted S (fun _ : σ => (1 : ℝ)) where
  toFun F := ⟨MvPowerSeries.map φ F.1, by
    show MvPowerSeries.IsRestrictedGauss _ _
    show Filter.Tendsto _ Filter.cofinite (nhds 0)
    have h2 : Filter.Tendsto (fun t : σ →₀ ℕ =>
        ‖MvPowerSeries.coeff t F.1‖ * t.prod ((fun _ : σ => (1 : ℝ)) · ^ ·))
        Filter.cofinite (nhds 0) := F.2
    refine squeeze_zero (fun t => ?_) (fun t => ?_) h2
    · exact mul_nonneg (norm_nonneg _) (prod_weights_pos _ t).le
    · rw [MvPowerSeries.coeff_map]
      exact mul_le_mul_of_nonneg_right (hφ _) (prod_weights_pos _ t).le⟩
  map_zero' := Subtype.ext (map_zero (MvPowerSeries.map φ))
  map_one' := Subtype.ext (map_one (MvPowerSeries.map φ))
  map_add' F G := Subtype.ext (map_add (MvPowerSeries.map φ) F.1 G.1)
  map_mul' F G := Subtype.ext (map_mul (MvPowerSeries.map φ) F.1 G.1)

@[simp] theorem mvRestrictedMapHom_coeff (φ : R →+* S) (hφ : ∀ x, ‖φ x‖ ≤ ‖x‖)
    (F : MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ))) (t : σ →₀ ℕ) :
    MvPowerSeries.coeff t ((mvRestrictedMapHom φ hφ F) :
      MvPowerSeries.Restricted S (fun _ : σ => (1 : ℝ))).1 =
      φ (MvPowerSeries.coeff t F.1) :=
  MvPowerSeries.coeff_map φ t F.1

/-- Isometric transport of radius-one restricted series along a ring isomorphism. -/
noncomputable def mvRestrictedCongr (e : R ≃+* S) (he : ∀ x, ‖e x‖ = ‖x‖) :
    MvPowerSeries.Restricted R (fun _ : σ => (1 : ℝ)) ≃+*
      MvPowerSeries.Restricted S (fun _ : σ => (1 : ℝ)) := by
  have he' : ∀ y, ‖e.symm y‖ = ‖y‖ := fun y => by
    rw [← he (e.symm y), RingEquiv.apply_symm_apply]
  refine RingEquiv.ofRingHom
    (mvRestrictedMapHom (e : R →+* S) (fun x => (he x).le))
    (mvRestrictedMapHom (e.symm : S →+* R) (fun y => (he' y).le)) ?_ ?_
  · ext G
    refine Subtype.ext (MvPowerSeries.ext fun t => ?_)
    show e (e.symm (MvPowerSeries.coeff t G.1)) = MvPowerSeries.coeff t G.1
    exact RingEquiv.apply_symm_apply e _
  · ext F
    refine Subtype.ext (MvPowerSeries.ext fun t => ?_)
    show e.symm (e (MvPowerSeries.coeff t F.1)) = MvPowerSeries.coeff t F.1
    exact RingEquiv.symm_apply_apply e _

end RestrictedTransport

section PerK

variable {K w N}
variable (k : ℕ)

open scoped Classical in
/-- The coefficientwise `ε`-slice of a restricted series over the head. -/
noncomputable def sliceP (ε : Fin N → Bool)
    (F : FiniteJet.GraphKoszul.P (WPHead K w N) k) :
    FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k := by
  refine ⟨fun s : Fin k →₀ ℕ => slice ε (MvPowerSeries.coeff s F.1), ?_⟩
  show MvPowerSeries.IsRestrictedGauss _ _
  show Filter.Tendsto _ Filter.cofinite (nhds 0)
  have h2 : Filter.Tendsto (fun s : Fin k →₀ ℕ =>
      ‖MvPowerSeries.coeff s F.1‖ * s.prod ((fun _ : Fin k => (1 : ℝ)) · ^ ·))
      Filter.cofinite (nhds 0) := F.2
  refine squeeze_zero (fun s => ?_) (fun s => ?_) h2
  · exact mul_nonneg (norm_nonneg _) (prod_weights_pos _ s).le
  · exact mul_le_mul_of_nonneg_right (norm_slice_le ε _) (prod_weights_pos _ s).le

@[simp] theorem sliceP_coeff (ε : Fin N → Bool)
    (F : FiniteJet.GraphKoszul.P (WPHead K w N) k) (s : Fin k →₀ ℕ) :
    MvPowerSeries.coeff s (sliceP k ε F).1 = slice ε (MvPowerSeries.coeff s F.1) :=
  rfl

/-- The coefficientwise inclusion of the even part into the head, at the `k`-th
Tate extension. -/
noncomputable def inclP : FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k →+*
    FiniteJet.GraphKoszul.P (WPHead K w N) k :=
  mvRestrictedMapHom (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
    (fun x => le_of_eq rfl)

/-- **The `k`-th Tate extension of the head is module-finite over that of the even
part** (the parity-slice decomposition applied to every `T`-coefficient). -/
theorem moduleFinite_P_head_over_even :
    letI : Algebra (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
        (FiniteJet.GraphKoszul.P (WPHead K w N) k) := (inclP k).toAlgebra
    Module.Finite (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
      (FiniteJet.GraphKoszul.P (WPHead K w N) k) := by
  classical
  letI : Algebra (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
      (FiniteJet.GraphKoszul.P (WPHead K w N) k) := (inclP k).toAlgebra
  refine ⟨⟨Finset.univ.image fun ε : Fin N → Bool =>
    FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε)), ?_⟩⟩
  rw [eq_top_iff]
  intro F _
  have hCP : ∀ a : WPHead K w N,
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C a) :
        FiniteJet.GraphKoszul.P (WPHead K w N) k).1 = MvPowerSeries.C a := by
    intro a
    refine MvPowerSeries.ext fun s => ?_
    classical
    rw [FiniteJet.GraphKoszul.coeff_polyToP, MvPowerSeries.coeff_C]
    by_cases hs : s = (0 : Fin k →₀ ℕ)
    · subst hs
      simp
    · rw [if_neg hs, MvPolynomial.coeff_C, if_neg (fun h => hs h.symm)]
  have hident : (∑ ε : Fin N → Bool, inclP k (sliceP k ε F) *
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε))) = F := by
    refine Subtype.ext (MvPowerSeries.ext fun s => ?_)
    have hval : ((∑ ε : Fin N → Bool, inclP k (sliceP k ε F) *
        FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε)) :
        FiniteJet.GraphKoszul.P (WPHead K w N) k)).1 =
        ∑ ε : Fin N → Bool, (inclP k (sliceP k ε F)).1 *
          MvPowerSeries.C (Ypat K w N ε) := by
      show (MvPowerSeries.isSubring
          (R := WPHead K w N) (fun _ : Fin k => (1 : ℝ))).subtype
          (∑ ε : Fin N → Bool, inclP k (sliceP k ε F) *
            FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε))) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun ε _ => ?_
      show ((inclP k (sliceP k ε F)) * FiniteJet.GraphKoszul.polyToP
        (MvPolynomial.C (Ypat K w N ε)) :
          FiniteJet.GraphKoszul.P (WPHead K w N) k).1 = _
      rw [show ((inclP k (sliceP k ε F)) * FiniteJet.GraphKoszul.polyToP
          (MvPolynomial.C (Ypat K w N ε)) :
            FiniteJet.GraphKoszul.P (WPHead K w N) k).1 =
          (inclP k (sliceP k ε F)).1 * (FiniteJet.GraphKoszul.polyToP
            (MvPolynomial.C (Ypat K w N ε)) :
              FiniteJet.GraphKoszul.P (WPHead K w N) k).1 from rfl, hCP]
    rw [hval, map_sum]
    have hterm : ∀ ε : Fin N → Bool,
        MvPowerSeries.coeff s ((inclP k (sliceP k ε F)).1 *
          MvPowerSeries.C (Ypat K w N ε)) =
        (Subring.inclusion (wpEvenSupport_le_wpHeadSupport K w N))
          (slice ε (MvPowerSeries.coeff s F.1)) * Ypat K w N ε := by
      intro ε
      rw [MvPowerSeries.coeff_mul_C]
      rfl
    rw [Finset.sum_congr rfl fun ε _ => hterm ε]
    exact sum_slice_mul_Ypat (MvPowerSeries.coeff s F.1)
  rw [← hident]
  refine Submodule.sum_mem _ fun ε _ => ?_
  have hsmul : inclP k (sliceP k ε F) *
      FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε)) =
      (sliceP k ε F) •
        FiniteJet.GraphKoszul.polyToP (MvPolynomial.C (Ypat K w N ε)) := by
    rw [Algebra.smul_def]
    rfl
  rw [hsmul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (Finset.mem_univ ε))))

end PerK

variable {K} in
/-- **The heads are strongly noetherian** ([WP] §6.4: "Since `𝒜_N` is affinoid" —
the input to the head graph-Koszul bounds and to Wedhorn 8.28(b).  Proven for every
Tate-variable count by the same finite-free-module argument at head
`K⟨W,Z,T_1,…,T_k⟩`; NEVER inferred from noetherianity (prior-B2 T-SUM-6/T-Q4). -/
theorem isStronglyNoetherian_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsStronglyNoetherian (WPHead K w N) := by
  constructor
  intro k
  -- the base Tate algebra `P K (N+1)` with its own scale bundle
  have hballP : IsNoetherianRing
      ↥(FiniteJet.unitBall (FiniteJet.GraphKoszul.P K (N + 1))) :=
    ϖ.isNoetherianRing_unitBall_P hK₀ (N + 1)
  have hnormt : ‖(FiniteJet.GraphKoszul.polyToP (MvPolynomial.C ϖ.val) :
      FiniteJet.GraphKoszul.P K (N + 1))‖ = ‖ϖ.val‖ :=
    FiniteJet.GraphKoszul.norm_tP ϖ.val ϖ.norm_val_mul
  haveI h1 : IsNoetherianRing
      (FiniteJet.GraphKoszul.P (FiniteJet.GraphKoszul.P K (N + 1)) k) :=
    isNoetherianRing_P_of_scale
      (FiniteJet.GraphKoszul.polyToP (MvPolynomial.C ϖ.val))
      ((FiniteJet.GraphKoszul.isUnit_tP ϖ.val ϖ.isUnit_val))
      (by rw [hnormt]; exact ϖ.norm_val_lt_one)
      (by rw [hnormt]; exact ϖ.norm_val_pos)
      (fun G => by
        rw [FiniteJet.GraphKoszul.norm_tP_mul ϖ.val ϖ.norm_val_mul G, hnormt])
      hballP k
  -- transport to the even part along the halving equiv
  have heq' : ∀ y, ‖(evenSupportEquiv K w N).symm y‖ = ‖y‖ := fun y => by
    rw [← norm_evenSupportEquiv K w N ((evenSupportEquiv K w N).symm y),
      RingEquiv.apply_symm_apply]
  haveI h2 : IsNoetherianRing
      (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k) :=
    isNoetherianRing_of_ringEquiv _
      (mvRestrictedCongr (σ := Fin k) (evenSupportEquiv K w N).symm heq')
  -- module-finiteness of the head extension
  letI : Algebra (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
      (FiniteJet.GraphKoszul.P (WPHead K w N) k) := (inclP k).toAlgebra
  haveI h3 : Module.Finite (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
      (FiniteJet.GraphKoszul.P (WPHead K w N) k) :=
    moduleFinite_P_head_over_even k
  haveI h4 : IsNoetherianRing (FiniteJet.GraphKoszul.P (WPHead K w N) k) :=
    IsNoetherianRing.of_finite (FiniteJet.GraphKoszul.P ↥(wpEvenSupport K w N) k)
      (FiniteJet.GraphKoszul.P (WPHead K w N) k)
  exact isNoetherianRing_of_ringEquiv _
    (UnitDiscExample.restrictedGaussEquiv (WPHead K w N) k)

variable {K} in
/-- **The heads are sheafy** (Wedhorn 8.28(b) at the head;
`isSheafy_of_stronglyNoetherian_828b` — the `isSheafy_JetB/C/D` pattern,
`FJP/Over/SheafTransfer.lean:63`). -/
theorem isSheafy_WPHead (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    ValuationSpectrum.IsSheafy (WPHead K w N) := by
  haveI := isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  exact ValuationSpectrum.isSheafy_of_stronglyNoetherian_828b

/-! ### Density of the heads ([WP] eq:A-completion-of-heads) -/

variable {K w} in
/-- Truncation to a head: every element of `𝒜` is approximated to any `ϖ`-power
precision by an element of some head ([WP] eq:A-completion-of-heads:
"`𝒜 = closure(⋃_N 𝒜_N)`"). -/
theorem exists_head_approx (ϖ : Uniformizer K) (f : WPA K w) (ℓ : ℕ) :
    ∃ (N : ℕ) (g : WPHead K w N),
      ‖f - headIncl K w N g‖ ≤ ‖ϖ.val‖ ^ ℓ * ‖f‖ := by
  classical
  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, 0, ?_⟩
    rw [map_zero, sub_zero, norm_zero]
    exact mul_nonneg (pow_nonneg (norm_nonneg _) _) (le_refl _)
  · set ε : ℝ := ‖ϖ.val‖ ^ ℓ * ‖f‖ with hε_def
    have hf_pos : (0 : ℝ) < ‖f‖ := norm_pos_iff.mpr hf0
    have hε_pos : 0 < ε := mul_pos (pow_pos ϖ.norm_val_pos ℓ) hf_pos
    have hSfin : {t : ℕ →₀ ℕ | ε < ‖coeffA K w t f‖}.Finite := by
      refine (finite_setOf_le_norm_coeff (f := f.1) hε_pos).subset ?_
      intro t ht
      rw [Set.mem_setOf_eq] at ht ⊢
      exact le_of_lt ht
    set S : Finset (ℕ →₀ ℕ) := hSfin.toFinset with hS_def
    set N : ℕ := S.sup fun t => t.support.sup id with hN_def
    have hbound : ∀ t ∈ S, ∀ n, N < n → t n = 0 := by
      intro t ht n hn
      by_contra hne
      have hmem : n ∈ t.support := Finsupp.mem_support_iff.mpr hne
      have h1 : n ≤ t.support.sup id := Finset.le_sup (f := id) hmem
      have h2 : t.support.sup id ≤ N := Finset.le_sup (f := fun t => t.support.sup id) ht
      omega
    have hres : MvPowerSeries.IsRestrictedGauss (fun _ : ℕ => (1 : ℝ))
        (fun t => if t ∈ S then coeffA K w t f else 0) := by
      have hchar : ∀ δ : ℝ, 0 < δ → {t : ℕ →₀ ℕ |
          δ ≤ ‖(if t ∈ S then coeffA K w t f else 0 : K)‖}.Finite := by
        intro δ hδ
        refine S.finite_toSet.subset ?_
        intro t ht
        rw [Set.mem_setOf_eq] at ht
        by_cases htS : t ∈ S
        · exact htS
        · rw [if_neg htS, norm_zero] at ht
          exact absurd (hδ.trans_le ht) (lt_irrefl 0)
      show Filter.Tendsto _ Filter.cofinite (nhds 0)
      rw [Metric.tendsto_nhds]
      intro δ hδ
      rw [Filter.eventually_cofinite]
      refine (hchar δ hδ).subset ?_
      intro t ht
      rw [Set.mem_setOf_eq] at ht ⊢
      rw [Real.dist_eq, sub_zero, prod_one_weights, mul_one] at ht
      rw [abs_of_nonneg (norm_nonneg _)] at ht
      exact not_lt.mp ht
    have hsupp : ∀ t : ℕ →₀ ℕ, ¬ HeadMem w N t →
        (⟨(fun t => if t ∈ S then coeffA K w t f else 0 : (ℕ →₀ ℕ) → K), hres⟩ :
          Amb K).1 t = 0 := by
      intro t ht
      show (if t ∈ S then coeffA K w t f else 0) = 0
      by_cases htS : t ∈ S
      · exfalso
        apply ht
        have hlt : ε < ‖coeffA K w t f‖ := hSfin.mem_toFinset.mp htS
        have hne : coeffA K w t f ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hlt
          linarith
        refine ⟨?_, fun n hn => hbound t htS n hn⟩
        by_contra hmem
        exact hne (coeffA_of_not_wpMem K w hmem f)
      · rw [if_neg htS]
    refine ⟨N, ⟨⟨(fun t => if t ∈ S then coeffA K w t f else 0 : (ℕ →₀ ℕ) → K),
      hres⟩, hsupp⟩, ?_⟩
    rw [norm_eq_iSup_coeffA]
    refine ciSup_le fun t => ?_
    have hco : coeffA K w t (f - headIncl K w N
        ⟨⟨(fun t => if t ∈ S then coeffA K w t f else 0 : (ℕ →₀ ℕ) → K), hres⟩,
          hsupp⟩) = coeffA K w t f - (if t ∈ S then coeffA K w t f else 0) := by
      show MvPowerSeries.coeff t (f.1.1 - _) = _
      rw [map_sub]
      rfl
    rw [hco]
    by_cases htS : t ∈ S
    · rw [if_pos htS, sub_self, norm_zero]
      exact le_of_lt hε_pos
    · rw [if_neg htS, sub_zero]
      have : ¬ ε < ‖coeffA K w t f‖ := fun h => htS (hSfin.mem_toFinset.mpr h)
      linarith [not_lt.mp this]



end WeightedParity
