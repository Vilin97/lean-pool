/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.Palomar.Bridge
public import LeanPool.UniformSheafyTateDomains.AdicSpaces

/-!
# The Challenge's finite-jet algebra is the library's

The Challenge defines `𝓐` as the closure of the jet polynomials ([FJP] (1.7)) in
`K⟨W, W⁻¹, Q⟩ = Completion K[W, W⁻¹, Q]` for the Gauss norm; the library defines it as the
support subring `jetSupport` of `L⟨Q⟩ = PowerSeries.Restricted (RestrictedLaurent K) 1`. This
file identifies them: the obvious embedding `ι : K[W, W⁻¹, Q] → L⟨Q⟩` is an isometry with
dense image, so it extends to an isometric ring isomorphism of the completion with `L⟨Q⟩`,
which carries the closure of the jet polynomials onto `jetSupport`.
-/

@[expose] public section


noncomputable section

open Filter Topology

namespace PalomarBridge.Jet

open FiniteJetOver

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-! ### Monomials `W^a Q^q` and the embedding `ι` -/

/-- The monomial `W^a Q^q` of `L⟨Q⟩`. -/
def mono (a : ℤ) (q : ℕ) : JetC K :=
  ⟨PowerSeries.monomial q (FiniteJet.RestrictedLaurent.single a (1 : K)),
    PowerSeries.IsRestricted.monomial (1 : ℝ) q _⟩

theorem mono_zero_zero : mono K 0 0 = 1 := by
  apply Subtype.ext
  show PowerSeries.monomial 0 (FiniteJet.RestrictedLaurent.single 0 (1 : K)) = 1
  rw [FiniteJet.RestrictedLaurent.single_zero_one, PowerSeries.monomial_zero_eq_C_apply, map_one]

theorem mono_mul (a b : ℤ) (q r : ℕ) : mono K a q * mono K b r = mono K (a + b) (q + r) := by
  apply Subtype.ext
  show PowerSeries.monomial q _ * PowerSeries.monomial r _ = PowerSeries.monomial (q + r) _
  rw [PowerSeries.monomial_mul_monomial, FiniteJet.RestrictedLaurent.single_mul_single, one_mul]

/-- The monomials, as a monoid hom out of `Multiplicative (ℤ × ℕ)`. -/
def monoHom : Multiplicative (ℤ × ℕ) →* JetC K where
  toFun m := mono K m.toAdd.1 m.toAdd.2
  map_one' := mono_zero_zero K
  map_mul' _ _ := (mono_mul K _ _ _ _).symm

/-- `ι : K[W, W⁻¹, Q] →+* L⟨Q⟩`, sending `c · W^a Q^q` to itself. -/
def iota : AddMonoidAlgebra K (ℤ × ℕ) →+* JetC K :=
  AddMonoidAlgebra.liftNCRingHom (constC K) (monoHom K) fun _ _ => Commute.all _ _

theorem iota_single (a : ℤ) (q : ℕ) (c : K) :
    iota K (AddMonoidAlgebra.single (a, q) c) = constC K c * mono K a q :=
  AddMonoidAlgebra.liftNC_single _ _ _ _

/-- `ι` followed by the inclusion into `PowerSeries (L K)`. -/
def iotaVal : AddMonoidAlgebra K (ℤ × ℕ) →+* PowerSeries (L K) :=
  (PowerSeries.isSubring (R := L K) (1 : ℝ)).subtype.comp (iota K)

theorem iotaVal_apply (p : AddMonoidAlgebra K (ℤ × ℕ)) : iotaVal K p = (iota K p).1 := rfl

theorem iotaVal_single (m : ℤ × ℕ) (c : K) :
    iotaVal K (AddMonoidAlgebra.single m c) =
      PowerSeries.monomial m.2 (FiniteJet.RestrictedLaurent.single m.1 c) := by
  obtain ⟨a, q⟩ := m
  rw [iotaVal_apply, iota_single]
  show PowerSeries.C (FiniteJet.RestrictedLaurent.single 0 c) *
    PowerSeries.monomial q (FiniteJet.RestrictedLaurent.single a 1) = _
  rw [← PowerSeries.monomial_zero_eq_C_apply, PowerSeries.monomial_mul_monomial, zero_add,
    FiniteJet.RestrictedLaurent.single_mul_single, zero_add, mul_one]

/-- The `Q^n`-coefficient of `ι p` is the Laurent series `∑ₐ p(a, n) W^a`. -/
theorem coeff_iota (p : AddMonoidAlgebra K (ℤ × ℕ)) (n : ℕ) (a : ℤ) :
    (PowerSeries.coeff n (iota K p).1).coeff a = p.coeff (a, n) := by
  classical
  rw [← iotaVal_apply]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single p, map_finsuppSum, map_finsuppSum]
  simp only [iotaVal_single, PowerSeries.coeff_monomial]
  rw [show (p.coeff.sum fun m c =>
      if n = m.2 then FiniteJet.RestrictedLaurent.single m.1 c else 0).coeff a =
      p.coeff.sum fun m c => if m = (a, n) then c else 0 from ?_]
  · rw [Finsupp.sum_ite_eq']
    split_ifs with h
    · rfl
    · exact (Finsupp.notMem_support_iff.mp h).symm
  · rw [Finsupp.sum, Finsupp.sum]
    have hcoe : ∀ (s : Finset (ℤ × ℕ)) (g : ℤ × ℕ → FiniteJet.RestrictedLaurent K),
        (∑ m ∈ s, g m).coeff a = ∑ m ∈ s, (g m).coeff a := fun s g =>
      map_sum (FiniteJet.RestrictedLaurent.coeffHom a) g s
    rw [hcoe]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases h2 : n = m.2
    · by_cases h1 : a = m.1
      · rw [if_pos h2, FiniteJet.RestrictedLaurent.coeff_single, if_pos h1,
          if_pos (Prod.ext h1.symm h2.symm)]
      · rw [if_pos h2, FiniteJet.RestrictedLaurent.coeff_single, if_neg h1,
          if_neg (fun h => h1 (congrArg Prod.fst h).symm)]
    · rw [if_neg h2, FiniteJet.RestrictedLaurent.coeff_zero,
        if_neg (fun h => h2 (congrArg Prod.snd h).symm)]

/-! ### `ι` is an isometry -/

/-- The Gauss norm of `L⟨Q⟩`, coefficient by coefficient. -/
theorem norm_jetC_eq (g : JetC K) :
    ‖g‖ = ⨆ n : ℕ, ⨆ a : ℤ, ‖(PowerSeries.coeff n g.1).coeff a‖ := by
  rw [Restricted.norm_eq, PowerSeries.gaussNorm_eq]
  simp only [one_pow, mul_one]
  rfl

theorem norm_coeff_coeff_le (g : JetC K) (n : ℕ) (a : ℤ) :
    ‖(PowerSeries.coeff n g.1).coeff a‖ ≤ ‖g‖ := by
  rw [norm_jetC_eq]
  have hbdd : ∀ n : ℕ, BddAbove (Set.range fun a : ℤ => ‖(PowerSeries.coeff n g.1).coeff a‖) :=
    fun n => ⟨‖PowerSeries.coeff n g.1‖, by
      rintro _ ⟨a, rfl⟩
      exact FiniteJet.RestrictedLaurent.norm_coeff_le_gaussNorm _ a⟩
  have hbdd' : BddAbove (Set.range fun n : ℕ =>
      ⨆ a : ℤ, ‖(PowerSeries.coeff n g.1).coeff a‖) := ⟨‖g‖, by
    rintro _ ⟨n, rfl⟩
    refine ciSup_le fun a => ?_
    calc ‖(PowerSeries.coeff n g.1).coeff a‖ ≤ ‖PowerSeries.coeff n g.1‖ :=
          FiniteJet.RestrictedLaurent.norm_coeff_le_gaussNorm _ a
      _ ≤ ‖g‖ := by
        rw [Restricted.norm_eq]
        simpa using PowerSeries.le_gaussNorm norm 1 g.1 (Restricted.hasGaussNorm 1 g) n⟩
  exact le_ciSup_of_le hbdd' n (le_ciSup (hbdd n) a)

theorem norm_coeff_le_norm (p : AddMonoidAlgebra K (ℤ × ℕ)) (m : ℤ × ℕ) :
    ‖p.coeff m‖ ≤ ‖p‖ := by
  rw [← coe_nnnorm, ← coe_nnnorm, Palomar.nnnorm_eq_gauss]
  exact_mod_cast Palomar.nnnorm_coeff_le_gauss p m

theorem norm_iota (p : AddMonoidAlgebra K (ℤ × ℕ)) : ‖iota K p‖ = ‖p‖ := by
  apply le_antisymm
  · rw [norm_jetC_eq]
    refine Real.iSup_le (fun n => Real.iSup_le (fun a => ?_) (norm_nonneg _)) (norm_nonneg _)
    rw [coeff_iota]
    exact norm_coeff_le_norm K p (a, n)
  · by_cases hp : p = 0
    · subst hp; simp
    · have hne : p.coeff.support.Nonempty := Finsupp.support_nonempty_iff.mpr fun h =>
        hp (AddMonoidAlgebra.coeff_injective (h.trans AddMonoidAlgebra.coeff_zero.symm))
      obtain ⟨m₀, -, hsup⟩ := Finset.exists_mem_eq_sup _ hne fun m => ‖p.coeff m‖₊
      have h0 : ‖p‖ = ‖p.coeff m₀‖ := by
        rw [← coe_nnnorm, Palomar.nnnorm_eq_gauss, Palomar.gauss, hsup, coe_nnnorm]
      rw [h0, ← coeff_iota K p m₀.2 m₀.1]
      exact norm_coeff_coeff_le K (iota K p) m₀.2 m₀.1

/-! ### `ι` has dense range -/

/-- The truncation of `g ∈ L⟨Q⟩` to the box `|a| ≤ N`, `n ≤ N`, as a Laurent polynomial. -/
def trunc (N : ℕ) (g : JetC K) : AddMonoidAlgebra K (ℤ × ℕ) :=
  .ofCoeff <| Finsupp.onFinset (Finset.Icc (-(N : ℤ)) N ×ˢ Finset.range (N + 1))
    (fun m => if |m.1| ≤ N ∧ m.2 ≤ N then (PowerSeries.coeff m.2 g.1).coeff m.1 else 0)
    fun m hm => by
      by_contra hbox
      refine hm (if_neg fun h => hbox ?_)
      rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_range, abs_le] at *
      exact ⟨⟨h.1.1, h.1.2⟩, by omega⟩

theorem coeff_trunc (N : ℕ) (g : JetC K) (m : ℤ × ℕ) :
    (trunc K N g).coeff m =
      if |m.1| ≤ N ∧ m.2 ≤ N then (PowerSeries.coeff m.2 g.1).coeff m.1 else 0 := rfl

/-- The coefficients of `g ∈ L⟨Q⟩` tend to zero jointly in `(a, n)`: outside a large enough
box they are all small. -/
theorem exists_box (g : JetC K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (a : ℤ) (n : ℕ), ¬ (|a| ≤ N ∧ n ≤ N) →
      ‖(PowerSeries.coeff n g.1).coeff a‖ < ε := by
  -- the `Q`-coefficients tend to zero in `L`
  have h1 : Tendsto (fun n => ‖PowerSeries.coeff n g.1‖) atTop (𝓝 0) := by
    have h0 : PowerSeries.IsRestricted (1 : ℝ) g.1 := g.2
    unfold PowerSeries.IsRestricted at h0
    simpa only [one_pow, mul_one] using h0
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp h1 ε hε
  -- for each of the finitely many `n < N₁`, finitely many `W`-coefficients are large
  have hfin : ∀ n : ℕ, {a : ℤ | ε ≤ ‖(PowerSeries.coeff n g.1).coeff a‖}.Finite := fun n =>
    FiniteJet.RestrictedLaurent.finite_setOf_le_norm_coeff _ hε
  classical
  let S : Finset ℤ := (Finset.range N₁).biUnion fun n => (hfin n).toFinset
  refine ⟨max N₁ (S.sup fun a => a.natAbs), fun a n hbox => ?_⟩
  by_cases hn : N₁ ≤ n
  · -- `n` large: the whole `Q^n`-coefficient is small
    have := hN₁ n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] at this
    exact (FiniteJet.RestrictedLaurent.norm_coeff_le_gaussNorm _ a).trans_lt this
  · -- `n` small, so `|a|` is large: `a` is outside the finite set of large coefficients
    push Not at hn
    by_contra hle
    push Not at hle
    have haS : a ∈ S := Finset.mem_biUnion.mpr ⟨n, Finset.mem_range.mpr hn,
      (hfin n).mem_toFinset.mpr hle⟩
    have h1 : a.natAbs ≤ S.sup fun a => a.natAbs := Finset.le_sup (f := fun a : ℤ => a.natAbs) haS
    refine hbox ⟨?_, by omega⟩
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h1.trans (le_max_right _ _)

theorem exists_norm_sub_iota_trunc_le (g : JetC K) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ‖g - iota K (trunc K N g)‖ ≤ ε := by
  obtain ⟨N, hN⟩ := exists_box K g hε
  refine ⟨N, ?_⟩
  rw [norm_jetC_eq]
  refine Real.iSup_le (fun n => Real.iSup_le (fun a => ?_) hε.le) hε.le
  have hc : (PowerSeries.coeff n (g - iota K (trunc K N g)).1).coeff a =
      (PowerSeries.coeff n g.1).coeff a - (trunc K N g).coeff (a, n) := by
    rw [show (g - iota K (trunc K N g)).1 = g.1 - (iota K (trunc K N g)).1 from rfl, map_sub,
      FiniteJet.RestrictedLaurent.coeff_sub, coeff_iota]
  rw [hc, coeff_trunc]
  split_ifs with h
  · simp [hε.le]
  · rw [sub_zero]; exact (hN a n h).le

theorem denseRange_iota : DenseRange (iota K) := by
  refine Metric.denseRange_iff.mpr fun g ε hε => ?_
  obtain ⟨N, hN⟩ := exists_norm_sub_iota_trunc_le K g (half_pos hε)
  exact ⟨trunc K N g, by rw [dist_eq_norm]; exact hN.trans_lt (half_lt_self hε)⟩

theorem isometry_iota : Isometry (iota K) :=
  AddMonoidHomClass.isometry_of_norm (iota K) (norm_iota K)

/-! ### The completion of `K[W, W⁻¹, Q]` is `L⟨Q⟩` -/

/-- `L⟨Q⟩`, with `ι`, is an abstract completion of `K[W, W⁻¹, Q]`. -/
def jetCPkg : AbstractCompletion (AddMonoidAlgebra K (ℤ × ℕ)) where
  space := JetC K
  coe := iota K
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := (isometry_iota K).isUniformInducing
  dense := denseRange_iota K

/-- The uniform isomorphism `K⟨W, W⁻¹, Q⟩ ≃ᵤ L⟨Q⟩`. -/
def jetCUniformEquiv : Palomar.TateAlgebra K (ℤ × ℕ) ≃ᵤ JetC K :=
  UniformSpace.Completion.cPkg.compareEquiv (jetCPkg K)

theorem jetCUniformEquiv_apply (x : Palomar.TateAlgebra K (ℤ × ℕ)) :
    jetCUniformEquiv K x = UniformSpace.Completion.extension (iota K) x := rfl

/-- **`K⟨W, W⁻¹, Q⟩ ≃+* L⟨Q⟩`**: the completion of the Laurent polynomials for the Gauss norm is
the restricted series ring. -/
def jetCEquiv : Palomar.TateAlgebra K (ℤ × ℕ) ≃+* JetC K :=
  { UniformSpace.Completion.extensionHom (iota K) (isometry_iota K).continuous with
    invFun := (jetCUniformEquiv K).symm
    left_inv := fun x => (jetCUniformEquiv K).symm_apply_apply x
    right_inv := fun y => (jetCUniformEquiv K).apply_symm_apply y }

theorem jetCEquiv_coe (p : AddMonoidAlgebra K (ℤ × ℕ)) :
    jetCEquiv K (p : Palomar.TateAlgebra K (ℤ × ℕ)) = iota K p :=
  UniformSpace.Completion.extensionHom_coe (iota K) (isometry_iota K).continuous p

theorem continuous_jetCEquiv : Continuous (jetCEquiv K) :=
  UniformSpace.Completion.continuous_extension

theorem norm_jetCEquiv (x : Palomar.TateAlgebra K (ℤ × ℕ)) : ‖jetCEquiv K x‖ = ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp (continuous_jetCEquiv K)) continuous_norm
  | ih p => rw [jetCEquiv_coe, norm_iota, UniformSpace.Completion.norm_coe]

theorem continuous_jetCEquiv_symm : Continuous (jetCEquiv K).symm :=
  (jetCUniformEquiv K).symm.continuous

/-! ### The jet subrings correspond -/

/-- Jet polynomials land in the library's support subring. -/
theorem map_jetPolys_le : (Palomar.jetPolys K).map (iota K) ≤ jetSupport K := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · show (PowerSeries.coeff 0 (iota K p).1).coeff a = 0
    rw [coeff_iota]; exact hp a 0 zero_le_one ha
  · show (PowerSeries.coeff 1 (iota K p).1).coeff a = 0
    rw [coeff_iota]; exact hp a 1 le_rfl ha

/-- Truncating an element of the support subring gives a jet polynomial. -/
theorem trunc_mem_jetPolys (N : ℕ) {g : JetC K} (hg : g ∈ jetSupport K) :
    trunc K N g ∈ Palomar.jetPolys K := by
  intro a q hq ha
  rw [coeff_trunc]
  split_ifs with h
  · interval_cases q
    · exact hg.1 a ha
    · exact hg.2 a ha
  · rfl

/-- The closure of the jet polynomials in `L⟨Q⟩` is exactly the support subring. -/
theorem topologicalClosure_map_jetPolys :
    ((Palomar.jetPolys K).map (iota K)).topologicalClosure = jetSupport K := by
  refine le_antisymm (Subring.topologicalClosure_minimal _ (map_jetPolys_le K)
    (isClosed_jetSupport K)) fun g hg => ?_
  show g ∈ closure ((Palomar.jetPolys K).map (iota K) : Set (JetC K))
  refine Metric.mem_closure_iff.mpr fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_norm_sub_iota_trunc_le K g (half_pos hε)
  exact ⟨iota K (trunc K N g), ⟨trunc K N g, trunc_mem_jetPolys K N hg, rfl⟩,
    by rw [dist_eq_norm]; exact hN.trans_lt (half_lt_self hε)⟩

/-- The completion isomorphism carries the Challenge's `𝓐` onto the library's. -/
theorem map_jetSubring :
    (Palomar.jetSubring K).map (jetCEquiv K).toRingHom = jetSupport K := by
  rw [← topologicalClosure_map_jetPolys]
  apply SetLike.ext'
  -- both sides are images/closures of the jet polynomials
  show (jetCEquiv K) '' closure (((Palomar.jetPolys K).map
      (UniformSpace.Completion.coeRingHom : AddMonoidAlgebra K (ℤ × ℕ) →+*
        Palomar.TateAlgebra K (ℤ × ℕ)) : Subring _) : Set _) =
    closure (((Palomar.jetPolys K).map (iota K) : Subring _) : Set _)
  have he : (⇑(jetCEquiv K) : Palomar.TateAlgebra K (ℤ × ℕ) → JetC K) =
      ⇑(jetCUniformEquiv K).toHomeomorph := rfl
  rw [he, Homeomorph.image_closure, ← he]
  congr 1
  show (jetCEquiv K) '' ((UniformSpace.Completion.coeRingHom : AddMonoidAlgebra K (ℤ × ℕ) →+*
      Palomar.TateAlgebra K (ℤ × ℕ)) '' (Palomar.jetPolys K : Set _)) =
    (iota K) '' (Palomar.jetPolys K : Set _)
  rw [Set.image_image]
  exact Set.image_congr fun p _ => jetCEquiv_coe K p

/-- **The Challenge's `𝓐` is the library's `𝓐`**, as rings. -/
def jetAEquiv : Palomar.JetA K ≃+* JetA K :=
  (RingEquiv.subringMap (jetCEquiv K) (s := Palomar.jetSubring K)).trans
    (RingEquiv.subringCongr (map_jetSubring K))

theorem coe_jetAEquiv (x : Palomar.JetA K) : (jetAEquiv K x : JetC K) = jetCEquiv K x := rfl

theorem coe_jetAEquiv_symm (y : JetA K) :
    (((jetAEquiv K).symm y : Palomar.JetA K) : Palomar.TateAlgebra K (ℤ × ℕ)) =
      (jetCEquiv K).symm y := by
  apply (jetCEquiv K).injective
  rw [RingEquiv.apply_symm_apply, ← coe_jetAEquiv, RingEquiv.apply_symm_apply]

/-- The identification is isometric. -/
theorem norm_jetAEquiv (x : Palomar.JetA K) : ‖jetAEquiv K x‖ = ‖x‖ := by
  show ‖(jetAEquiv K x : JetC K)‖ = ‖(x : Palomar.TateAlgebra K (ℤ × ℕ))‖
  rw [coe_jetAEquiv, norm_jetCEquiv]

theorem norm_jetAEquiv_symm (y : JetA K) : ‖(jetAEquiv K).symm y‖ = ‖y‖ := by
  rw [← norm_jetAEquiv, RingEquiv.apply_symm_apply]

theorem isometry_jetAEquiv : Isometry (jetAEquiv K) :=
  AddMonoidHomClass.isometry_of_norm _ (norm_jetAEquiv K)

theorem isometry_jetAEquiv_symm : Isometry (jetAEquiv K).symm :=
  AddMonoidHomClass.isometry_of_norm _ (norm_jetAEquiv_symm K)

theorem continuous_jetAEquiv : Continuous (jetAEquiv K) := (isometry_jetAEquiv K).continuous

theorem continuous_jetAEquiv_symm : Continuous (jetAEquiv K).symm :=
  (isometry_jetAEquiv_symm K).continuous

/-- The identification as a homeomorphism. -/
def jetAHomeo : Palomar.JetA K ≃ₜ JetA K where
  toEquiv := (jetAEquiv K).toEquiv
  continuous_toFun := continuous_jetAEquiv K
  continuous_invFun := continuous_jetAEquiv_symm K

end PalomarBridge.Jet
