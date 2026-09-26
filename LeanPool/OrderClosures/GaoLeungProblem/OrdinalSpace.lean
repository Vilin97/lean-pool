/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.GaoLeungProblem.CNFOrder


/-!
# The compact ordinal space and coordinate projections
-/

@[expose] public section

namespace OrderClosures

open Set

universe u v

section OrdinalConstruction

/-- Coordinate indices in the compact ordinal construction. -/
abbrev GaoIndex (ξ : Ordinal.{u}) := Set.Iic (Ordinal.omega0 ^ ξ + 1)

/-- The closed subspace of the Cantor cube used in the proof of
`thm:solid-iterations`. -/
def GaoCompactSpace (ξ : Ordinal.{u}) :=
  {x : GaoIndex ξ → Bool |
    ∀ a b : GaoIndex ξ, cnfExtensionLT a.1 b.1 → x a ≤ x b}

/-- Coordinate projection `π_ζ` on the Gao compact space. -/
noncomputable def ordinalProjection (ξ : Ordinal.{u}) (ζ : GaoIndex ξ) :
    C(GaoCompactSpace ξ, ℝ) where
  toFun := fun x ↦ if x.1 ζ then 1 else 0
  continuous_toFun := by
    exact (continuous_of_discreteTopology :
      Continuous (fun b : Bool ↦ if b then (1 : ℝ) else 0)).comp
        ((continuous_apply ζ).comp continuous_subtype_val)

/-- Extracts finitely many Cantor-cube coordinates controlling a continuous
real map; used to prove the incomparable-projection infimum formula. -/
theorem continuousMap_exists_finite_coordinates
    {I : Type u} {K : Set (I → Bool)} (f : C(K, ℝ)) (x : K)
    {V : Set ℝ} (hV : IsOpen V) (hxV : f x ∈ V) :
    ∃ F : Finset I, ∀ y : K, (∀ i ∈ F, y.1 i = x.1 i) → f y ∈ V := by
  have hopen : IsOpen (f ⁻¹' V) := hV.preimage f.continuous
  rcases isOpen_induced_iff.mp hopen with ⟨W, hW, hWeq⟩
  have hxW : x.1 ∈ W := by
    have : x ∈ f ⁻¹' V := hxV
    rw [← hWeq] at this
    exact this
  rcases isOpen_pi_iff.mp hW x.1 hxW with ⟨F, v, hv, hvW⟩
  refine ⟨F, fun y hy ↦ ?_⟩
  have hyv : y.1 ∈ (F : Set I).pi v := by
    intro i hi
    rw [hy i (Finset.mem_coe.mp hi)]
    exact (hv i (Finset.mem_coe.mp hi)).2
  have hyW := hvW hyv
  have : y ∈ Subtype.val ⁻¹' W := hyW
  rw [hWeq] at this
  exact this

/-- The least exponent in the Cantor normal form of an ordinal (zero at the
empty normal form). -/
noncomputable def leastCNFExponent (ζ : Ordinal.{u}) : Ordinal.{u} :=
  ((Ordinal.CNF Ordinal.omega0 ζ).getLast?.map Prod.fst).getD 0

/-- The index set `Z_β` from Claim 3. -/
def GaoStageIndices (ξ β : Ordinal.{u}) : Set (GaoIndex ξ) :=
  {ζ | ζ.1 ≤ Ordinal.omega0 ^ ξ ∧ leastCNFExponent ζ.1 < β}

/-- The solid set `S_β` from Claim 3. -/
def GaoStageSet (ξ β : Ordinal.{u}) : Set C(GaoCompactSpace ξ, ℝ) :=
  {f | ∃ ζ ∈ GaoStageIndices ξ β, |f| ≤ ordinalProjection ξ ζ}

/-- Records solidity of each Gao stage set; used to invoke the solid form of
order adherence in the stage formula. -/
theorem isSolid_gaoStageSet (ξ β : Ordinal.{u}) :
    LatticeOrderedAddCommGroup.IsSolid (GaoStageSet ξ β) := by
  intro f hf g hgf
  obtain ⟨ζ, hζ, hfζ⟩ := hf
  exact ⟨ζ, hζ, hgf.trans hfζ⟩

/-- Claim 1 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_incomparable_iInf
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (hZ : Z.Infinite)
    (hinc : Z.Pairwise fun ζ ζ' ↦ ¬ cnfExtensionLE ζ.1 ζ'.1) :
    IsGLB (ordinalProjection ξ '' Z) 0 := by
  classical
  constructor
  · rintro p ⟨ζ, _, rfl⟩ x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  · intro f hf x
    by_contra hfx
    have hfxpos : 0 < f x := lt_of_not_ge hfx
    obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
      isOpen_Ioi hfxpos
    let bad : Set (GaoIndex ξ) := ⋃ i ∈ (F : Set (GaoIndex ξ)),
      {ζ | ζ ∈ Z ∧ x.1 i = true ∧ cnfExtensionLE i.1 ζ.1}
    have hbad : bad.Finite := by
      apply F.finite_toSet.biUnion
      intro i _
      apply Set.Subsingleton.finite
      intro ζ hζ ζ' hζ'
      rcases hζ with ⟨hζZ, _, hiζ⟩
      rcases hζ' with ⟨hζ'Z, _, hiζ'⟩
      by_contra hne
      have hnot := hinc hζZ hζ'Z hne
      rcases hiζ with hiζ | hiζ
      · have : i = ζ := Subtype.ext hiζ
        subst i
        exact hnot hiζ'
      rcases hiζ' with hiζ' | hiζ'
      · have : i = ζ' := Subtype.ext hiζ'
        subst i
        exact (hinc hζ'Z hζZ (Ne.symm hne)) (Or.inr hiζ)
      · rcases lt_trichotomy ζ.1 ζ'.1 with hlt | heq | hgt
        · exact hnot (Or.inr
            ((cnfExtensionLT_linear_above i.1 hiζ hiζ').mpr hlt))
        · exact hne (Subtype.ext heq)
        · exact (hinc hζ'Z hζZ (Ne.symm hne))
            (Or.inr ((cnfExtensionLT_linear_above i.1 hiζ' hiζ).mpr hgt))
    obtain ⟨ζ, hζZ, hζbad⟩ := hZ.exists_notMem_finite hbad
    let y : GaoIndex ξ → Bool := fun a ↦
      if cnfExtensionLE a.1 ζ.1 then false else x.1 a
    have hy_mono : ∀ a b : GaoIndex ξ,
        cnfExtensionLT a.1 b.1 → y a ≤ y b := by
      intro a b hab
      dsimp [y]
      by_cases ha : cnfExtensionLE a.1 ζ.1
      · rw [ite_eq_left ha]
        exact Bool.false_le _
      · rw [ite_eq_right ha]
        by_cases hb : cnfExtensionLE b.1 ζ.1
        · exact (ha (cnfExtensionLE_partialOrder_and_subrelation.1.trans
            a.1 b.1 ζ.1 (Or.inr hab) hb)).elim
        · rw [ite_eq_right hb]
          exact x.2 a b hab
    let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
    have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
      intro i hi
      dsimp [yK, y]
      by_cases hxi : x.1 i = true
      · rw [ite_eq_right]
        intro hiζ
        apply hζbad
        simp only [bad, Set.mem_iUnion]
        exact ⟨i, Finset.mem_coe.mpr hi, hζZ, hxi, hiζ⟩
      · have hxi' : x.1 i = false := Bool.eq_false_of_not_eq_true hxi
        by_cases hiζ : cnfExtensionLE i.1 ζ.1
        · rw [ite_eq_left hiζ, hxi']
        · rw [ite_eq_right hiζ, hxi']
    have hfy : 0 < f yK := hF yK hyF
    have hfζ := hf ⟨ζ, hζZ, rfl⟩ yK
    have hyζ : yK.1 ζ = false := by
      dsimp [yK, y]
      rw [ite_eq_left (show cnfExtensionLE ζ.1 ζ.1 from Or.inl rfl)]
    simp only [ordinalProjection, hyζ, Bool.false_eq_true, ↓reduceIte] at hfζ
    exact not_lt_of_ge hfζ hfy

/-- Characterizes order between coordinate projections by CNF extension;
used in all dominator and strict-stage arguments. -/
theorem ordinalProjection_le_iff
    (ξ : Ordinal.{u}) (a b : GaoIndex ξ) :
    ordinalProjection ξ a ≤ ordinalProjection ξ b ↔ cnfExtensionLE a.1 b.1 := by
  classical
  constructor
  · intro hab
    by_contra hrel
    let x : GaoIndex ξ → Bool := fun c ↦
      if cnfExtensionLE a.1 c.1 then true else false
    have hxmono : ∀ c d : GaoIndex ξ,
        cnfExtensionLT c.1 d.1 → x c ≤ x d := by
      intro c d hcd
      dsimp [x]
      by_cases hac : cnfExtensionLE a.1 c.1
      · rw [ite_eq_left hac, ite_eq_left]
        exact cnfExtensionLE_partialOrder_and_subrelation.1.trans
          a.1 c.1 d.1 hac (Or.inr hcd)
      · rw [ite_eq_right hac]
        exact Bool.false_le _
    let xK : GaoCompactSpace ξ := ⟨x, hxmono⟩
    have habx := hab xK
    have hxa : xK.1 a = true := by
      simp [xK, x, cnfExtensionLE]
    have hxb : xK.1 b = false := by
      simp [xK, x, hrel]
    simp only [ordinalProjection, hxa, hxb, Bool.false_eq_true, ↓reduceIte] at habx
    norm_num at habx
  · intro hab x
    rcases hab with hab | hab
    · have : a = b := Subtype.ext hab
      subst b
      exact le_rfl
    · dsimp [ordinalProjection]
      by_cases hxa : x.1 a = true
      · have hxb : x.1 b = true := by
          have hx := Bool.le_iff_imp.mp (x.2 a b hab)
          have hx' : True → x.1 b = true := by
            simpa only [hxa, Bool.true_eq] using hx
          exact hx' trivial
        simp only [hxa, hxb, ite_true]
        norm_num
      · simp only [hxa]
        positivity

/-- The leading monomial of an ordinal's canonical normal form; isolated for
the singleton-chain supremum analysis. -/
noncomputable def leadingCNFTerm (a : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a *
    (a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)

/-- Bounds a singleton CNF monomial by the leading term of an ordinal; used
to identify possible upper bounds of singleton chains. -/
theorem cnf_singleton_le_leadingCNFTerm
    {q a γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) (hqa : q ≤ a) :
    q ≤ leadingCNFTerm a := by
  have hqeq : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  have hlogq : Ordinal.log Ordinal.omega0 q = γ := by
    rw [hqeq, Ordinal.log_opow_mul Ordinal.one_lt_omega0 γ hdpos.ne',
      Ordinal.log_eq_zero hdlt, add_zero]
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hlogle := Ordinal.log_mono_right Ordinal.omega0 hqa
  rw [hlogq] at hlogle
  rcases hlogle.eq_or_lt with hloge | hloglt
  · rw [leadingCNFTerm, ← hloge, hqeq]
    apply mul_le_mul_right
    exact (Ordinal.mul_le_iff_le_div
      (Ordinal.opow_ne_zero γ Ordinal.omega0_ne_zero)).mp (hqeq ▸ hqa)
  · have hqpow : q < Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hq0).2 (by
        simpa only [hlogq] using hloglt)
    exact hqpow.le.trans (by
      rw [leadingCNFTerm]
      exact Ordinal.le_mul_left _
        (Ordinal.div_opow_log_pos Ordinal.omega0 ha0))

/-- Gives the canonical CNF description of a singleton omega monomial; used
to translate singleton-chain inequalities into exponent inequalities. -/
theorem cnf_singleton_spec
    {q γ d : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(γ, d)]) :
    q = Ordinal.omega0 ^ γ * d ∧ 0 < d ∧ d < Ordinal.omega0 ∧
      Ordinal.log Ordinal.omega0 q = γ := by
  have hqeq : q = Ordinal.omega0 ^ γ * d := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 q, hq]
    simp
  have hdpos : 0 < d := by
    apply Ordinal.CNF.snd_pos (b := Ordinal.omega0) (o := q) (x := (γ, d))
    rw [hq]
    simp
  have hdlt : d < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt (b := Ordinal.omega0) (o := q) (x := (γ, d))
      Ordinal.one_lt_omega0
    rw [hq]
    simp
  refine ⟨hqeq, hdpos, hdlt, ?_⟩
  rw [hqeq, Ordinal.log_opow_mul Ordinal.one_lt_omega0 γ hdpos.ne',
    Ordinal.log_eq_zero hdlt, add_zero]

/-- Shows that the least upper bound of a nonempty singleton-monomial chain is
itself a singleton monomial; used in the chain-supremum analysis. -/
theorem cnf_eq_singleton_of_isLUB
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u}) (hQ : Q.Nonempty)
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) :
    ∃ γ d, Ordinal.CNF Ordinal.omega0 a = [(γ, d)] := by
  obtain ⟨q, hqQ⟩ := hQ
  obtain ⟨γ, d, hq⟩ := hsingle q hqQ
  have hq0 : q ≠ 0 := by
    intro hzero
    rw [hzero, Ordinal.CNF.zero_right] at hq
    simp at hq
  have hqa : q ≤ a := hlub.1 hqQ
  have ha0 : a ≠ 0 := by
    intro ha
    apply hq0
    exact le_antisymm (ha ▸ hqa) (zero_le : (0 : Ordinal) ≤ q)
  have hleadUpper : leadingCNFTerm a ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨e, c, hr⟩ := hsingle r hrQ
    exact cnf_singleton_le_leadingCNFTerm hr (hlub.1 hrQ)
  have halead : a ≤ leadingCNFTerm a := hlub.2 hleadUpper
  have hleada : leadingCNFTerm a ≤ a := by
    exact Ordinal.mul_div_le a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
  have hleadeq : leadingCNFTerm a = a := le_antisymm hleada halead
  have hmod : a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = 0 := by
    have hdiv := Ordinal.div_add_mod a
      (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a)
    change leadingCNFTerm a +
      a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) = a at hdiv
    apply add_left_cancel (a := leadingCNFTerm a)
    calc
      leadingCNFTerm a + a % (Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a) =
          a := hdiv
      _ = leadingCNFTerm a + 0 := by rw [add_zero, hleadeq]
  refine ⟨Ordinal.log Ordinal.omega0 a,
    a / Ordinal.omega0 ^ Ordinal.log Ordinal.omega0 a, ?_⟩
  rw [Ordinal.CNF.ne_zero ha0, hmod, Ordinal.CNF.zero_right]

/-- Makes the exponent of a nonattained singleton-chain supremum strictly
larger than every member exponent; used at the limit case of the CNF chain. -/
theorem cnf_singleton_exponent_lt_of_isLUB_not_mem
    (Q : Set (Ordinal.{u})) (a : Ordinal.{u})
    (hsingle : ∀ q ∈ Q, ∃ γ d, Ordinal.CNF Ordinal.omega0 q = [(γ, d)])
    (hlub : IsLUB Q a) (haQ : a ∉ Q)
    {q β c γ d : Ordinal.{u}} (hqQ : q ∈ Q)
    (hq : Ordinal.CNF Ordinal.omega0 q = [(β, c)])
    (ha : Ordinal.CNF Ordinal.omega0 a = [(γ, d)]) : β < γ := by
  obtain ⟨hqeq, hcpos, hclt, hlogq⟩ := cnf_singleton_spec hq
  obtain ⟨haeq, hdpos, hdlt, hloga⟩ := cnf_singleton_spec ha
  have hqa : q ≤ a := hlub.1 hqQ
  have hqne : q ≠ a := fun h ↦ haQ (h ▸ hqQ)
  have hqalt : q < a := lt_of_le_of_ne hqa hqne
  have hβγ : β ≤ γ := by
    have := Ordinal.log_mono_right Ordinal.omega0 hqa
    simpa only [hlogq, hloga] using this
  apply hβγ.lt_of_ne
  intro hβγeq
  subst β
  obtain ⟨m, rfl⟩ := Ordinal.lt_omega0.mp hclt
  obtain ⟨n, rfl⟩ := Ordinal.lt_omega0.mp hdlt
  have hmpos : 0 < m := by exact_mod_cast hcpos
  have hnpos : 0 < n := by exact_mod_cast hdpos
  have hmn : m < n := by
    by_contra h
    have hnm : n ≤ m := le_of_not_gt h
    have hmul : Ordinal.omega0 ^ γ * (n : Ordinal) ≤
        Ordinal.omega0 ^ γ * (m : Ordinal) :=
      mul_le_mul_right (by exact_mod_cast hnm) _
    have hmulLt : Ordinal.omega0 ^ γ * (m : Ordinal) <
        Ordinal.omega0 ^ γ * (n : Ordinal) := by
      rw [← hβγeq, ← hqeq, hβγeq, ← haeq]
      exact hqalt
    exact (not_le_of_gt hmulLt) hmul
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hnpos)
  have hkpos : 0 < k := lt_of_lt_of_le hmpos (Nat.le_of_lt_succ hmn)
  let b : Ordinal.{u} := Ordinal.omega0 ^ γ * (k : Ordinal)
  have hbUpper : b ∈ upperBounds Q := by
    intro r hrQ
    obtain ⟨ε, e, hr⟩ := hsingle r hrQ
    obtain ⟨hreq, hepos, helt, hlogr⟩ := cnf_singleton_spec hr
    have hra : r ≤ a := hlub.1 hrQ
    have hrne : r ≠ a := fun h ↦ haQ (h ▸ hrQ)
    have hralt : r < a := lt_of_le_of_ne hra hrne
    have hεγ : ε ≤ γ := by
      have := Ordinal.log_mono_right Ordinal.omega0 hra
      simpa only [hlogr, hloga] using this
    rcases hεγ.eq_or_lt with rfl | hεγlt
    · obtain ⟨j, rfl⟩ := Ordinal.lt_omega0.mp helt
      have hjlt : j < k + 1 := by
        by_contra h
        have hle : k + 1 ≤ j := le_of_not_gt h
        have hmul : Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) ≤
            Ordinal.omega0 ^ ε * (j : Ordinal) :=
          mul_le_mul_right (by exact_mod_cast hle) _
        have hmulLt : Ordinal.omega0 ^ ε * (j : Ordinal) <
            Ordinal.omega0 ^ ε * ((k + 1 : ℕ) : Ordinal) := by
          rw [← hreq, ← haeq]
          exact hralt
        exact (not_le_of_gt hmulLt) hmul
      dsimp [b]
      rw [hreq]
      exact mul_le_mul_right (by exact_mod_cast (Nat.le_of_lt_succ hjlt)) _
    · have hr0 : r ≠ 0 := by
        intro hzero
        rw [hzero, Ordinal.CNF.zero_right] at hr
        simp at hr
      have hrpow : r < Ordinal.omega0 ^ γ :=
        (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).2 (by
          simpa only [hlogr] using hεγlt)
      exact hrpow.le.trans (by
        dsimp [b]
        exact Ordinal.le_mul_left _ (by exact_mod_cast hkpos))
  have hab : a ≤ b := hlub.2 hbUpper
  have hba : b < a := by
    dsimp [b]
    rw [haeq]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast (Nat.lt_succ_self k))
      (Ordinal.opow_pos γ Ordinal.omega0_pos)
  exact (not_le_of_gt hba) hab

/-- Identifies an equal-length CNF extension as deletion of the last source
term; used to analyze stabilization in chains of extensions. -/
theorem CNFListLT.eq_dropLast_of_length_eq
    {l m : List (Ordinal.{u} × Ordinal.{u})}
    (h : CNFListLT l m) (hlen : m.length = l.length) :
    ∃ x y, l = l.dropLast ++ [x] ∧ m = l.dropLast ++ [y] ∧
      CNFStep l.dropLast x y := by
  rcases h with ⟨pre, tail, x, y, hl, hm, hstep⟩
  have htail : tail = [] := by
    have hlength := congrArg List.length hl
    rw [hm] at hlen
    simp only [List.length_append, List.length_cons, List.length_nil] at hlength hlen
    have : tail.length = 0 := by omega
    simpa using this
  subst tail
  have hdrop : l.dropLast = pre := by simp [hl]
  exact ⟨x, y, by simp [hl], by simpa [hdrop] using hm,
    by simpa [hdrop] using hstep⟩

/-- Proves that the ordinary supremum of a nonempty extension chain remains
above every member in `cnfExtensionLE`; used by `ordinalProjection_chain_iSup`. -/
theorem cnfExtensionLE_chain_lub
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    ∀ ζ ∈ Z, cnfExtensionLE ζ.1 α.1 := by
  classical
  intro ζ hζZ
  by_cases hαZ : α ∈ Z
  · rcases hchain hζZ hαZ with hζα | hαζ
    · exact hζα
    · exact Or.inl (le_antisymm
        (hsup.1 ⟨ζ, hζZ, rfl⟩)
        (cnfExtensionLE_partialOrder_and_subrelation.2 hαζ))
  have hζαle : ζ.1 ≤ α.1 := hsup.1 ⟨ζ, hζZ, rfl⟩
  have hζα : ζ.1 < α.1 := hζαle.lt_of_ne fun h ↦ by
    have hsub : ζ = α := Subtype.ext h
    exact hαZ (hsub ▸ hζZ)
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := by
    by_contra h
    have hαζle : α.1 ≤ ζ.1 := hsup.2 (by
      rintro _ ⟨η, hηZ, rfl⟩
      exact le_of_not_gt fun hζη ↦ h ⟨η, hηZ, hζη⟩)
    exact (not_le_of_gt hζα) hαζle
  obtain ⟨η₀, hη₀U, hη₀min⟩ :=
    exists_minimalFor_of_wellFoundedLT U
      (fun η : GaoIndex ξ ↦ (Ordinal.CNF Ordinal.omega0 η.1).length) hU
  have hζη₀ : cnfExtensionLT ζ.1 η₀.1 := by
    rcases hchain hζZ hη₀U.1 with h | h
    · rcases h with heq | hlt
      · exact (hη₀U.2.ne' heq.symm).elim
      · exact hlt
    · exact (not_le_of_gt hη₀U.2
        (cnfExtensionLE_partialOrder_and_subrelation.2 h)).elim
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀U.1, le_rfl⟩
  have hrelV : ∀ η ∈ V, cnfExtensionLE η₀.1 η.1 := by
    intro η hηV
    rcases hchain hη₀U.1 hηV.1 with h | h
    · exact h
    · have hOrd := cnfExtensionLE_partialOrder_and_subrelation.2 h
      have heq : η₀.1 = η.1 := le_antisymm hηV.2 hOrd
      exact Or.inl heq
  have hlenV : ∀ η ∈ V,
      (Ordinal.CNF Ordinal.omega0 η.1).length =
        (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · rw [heq]
    · have hle : (Ordinal.CNF Ordinal.omega0 η.1).length ≤
          (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
        rcases cnfExtensionLT_iff_CNFListLT.mp hlt with
          ⟨pre, tail, x, y, hη₀cnf, hηcnf, _⟩
        rw [hη₀cnf, hηcnf]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hηU : U η := ⟨hηV.1, hη₀U.2.trans_le hηV.2⟩
      exact le_antisymm hle (hη₀min hηU hle)
  let pre := (Ordinal.CNF Ordinal.omega0 η₀.1).dropLast
  have hη₀ne : Ordinal.CNF Ordinal.omega0 η₀.1 ≠ [] := by
    have hη₀pos : 0 < η₀.1 := (zero_le : (0 : Ordinal) ≤ ζ.1).trans_lt hη₀U.2
    intro h
    have := Ordinal.CNF.foldr Ordinal.omega0 η₀.1
    rw [h] at this
    exact hη₀pos.ne' this.symm
  have hcnfV : ∀ η ∈ V, ∃ γ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(γ, d)] := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · have hsub : η₀ = η := Subtype.ext heq
      subst η
      let p := (Ordinal.CNF Ordinal.omega0 η₀.1).getLast hη₀ne
      refine ⟨p.1, p.2, ?_⟩
      simpa only [pre, p] using (List.dropLast_append_getLast hη₀ne).symm
    · obtain ⟨x, y, _, hηcnf, _⟩ :=
        CNFListLT.eq_dropLast_of_length_eq
          (cnfExtensionLT_iff_CNFListLT.mp hlt) (hlenV η hηV)
      obtain ⟨γ, d⟩ := y
      exact ⟨γ, d, hηcnf⟩
  let ρ : Ordinal.{u} := cnfValue pre
  have residual_of_common : ∀ (η : GaoIndex ξ) (γ d : Ordinal.{u}),
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(γ, d)] →
      Ordinal.CNF Ordinal.omega0 (η.1 - ρ) = [(γ, d)] ∧
        ρ + (η.1 - ρ) = η.1 := by
    intro η γ d hηcnf
    have hηeq : ρ + cnfValue [(γ, d)] = η.1 := by
      rw [← Ordinal.CNF.foldr Ordinal.omega0 η.1]
      change ρ + cnfValue [(γ, d)] = cnfValue (Ordinal.CNF Ordinal.omega0 η.1)
      rw [hηcnf, cnfValue_append]
    have hρle : ρ ≤ η.1 := hηeq ▸ le_self_add
    have hsub : η.1 - ρ = cnfValue [(γ, d)] :=
      Ordinal.sub_eq_of_add_eq hηeq
    constructor
    · rw [hsub]
      apply CNF_cnfValue
      · simp
      · intro p hp
        have hpη : p ∈ Ordinal.CNF Ordinal.omega0 η.1 := by
          rw [hηcnf]
          exact List.mem_append_right _ hp
        exact Ordinal.CNF.snd_pos hpη
      · intro p hp
        have hpη : p ∈ Ordinal.CNF Ordinal.omega0 η.1 := by
          rw [hηcnf]
          exact List.mem_append_right _ hp
        exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 hpη
    · exact Ordinal.add_sub_cancel_of_le hρle
  let Q : Set (Ordinal.{u}) :=
    (fun η : GaoIndex ξ ↦ η.1 - ρ) '' V
  have hQne : Q.Nonempty := ⟨η₀.1 - ρ, ⟨η₀, hη₀V, rfl⟩⟩
  have hsingleQ : ∀ q ∈ Q, ∃ γ d,
      Ordinal.CNF Ordinal.omega0 q = [(γ, d)] := by
    rintro q ⟨η, hηV, rfl⟩
    obtain ⟨γ, d, hηcnf⟩ := hcnfV η hηV
    exact ⟨γ, d, (residual_of_common η γ d hηcnf).1⟩
  obtain ⟨β, c, hη₀cnf⟩ := hcnfV η₀ hη₀V
  have hq₀cnf : Ordinal.CNF Ordinal.omega0 (η₀.1 - ρ) = [(β, c)] :=
    (residual_of_common η₀ β c hη₀cnf).1
  have hρaddη₀ : ρ + (η₀.1 - ρ) = η₀.1 :=
    (residual_of_common η₀ β c hη₀cnf).2
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hη₀αle : η₀.1 ≤ α.1 := hsup.1 ⟨η₀, hη₀U.1, rfl⟩
  have hρleα : ρ ≤ α.1 := hρleη₀.trans hη₀αle
  let a : Ordinal.{u} := α.1 - ρ
  have hρadda : ρ + a = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  have hlubQ : IsLUB Q a := by
    constructor
    · rintro q ⟨η, hηV, rfl⟩
      rw [Ordinal.sub_le]
      rw [hρadda]
      exact hsup.1 ⟨η, hηV.1, rfl⟩
    · intro b hb
      rw [Ordinal.sub_le]
      apply hsup.2
      rintro _ ⟨η, hηZ, rfl⟩
      rcases hchain hηZ hη₀U.1 with hηη₀ | hη₀η
      · have hηleη₀ := cnfExtensionLE_partialOrder_and_subrelation.2 hηη₀
        calc
          η.1 ≤ η₀.1 := hηleη₀
          _ = ρ + (η₀.1 - ρ) := hρaddη₀.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η₀, hη₀V, rfl⟩) ρ
      · have hη₀leη := cnfExtensionLE_partialOrder_and_subrelation.2 hη₀η
        have hηV : η ∈ V := ⟨hηZ, hη₀leη⟩
        obtain ⟨γ', d', hηcnf⟩ := hcnfV η hηV
        have hρaddη := (residual_of_common η γ' d' hηcnf).2
        calc
          η.1 = ρ + (η.1 - ρ) := hρaddη.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η, hηV, rfl⟩) ρ
  have haQ : a ∉ Q := by
    rintro ⟨η, hηV, hηsub⟩
    obtain ⟨γ', d', hηcnf⟩ := hcnfV η hηV
    have hρaddη := (residual_of_common η γ' d' hηcnf).2
    change η.1 - ρ = a at hηsub
    have hηα : η.1 = α.1 := by
      calc
        η.1 = ρ + (η.1 - ρ) := hρaddη.symm
        _ = ρ + a := by rw [hηsub]
        _ = α.1 := hρadda
    have hsub : η = α := Subtype.ext hηα
    exact hαZ (hsub ▸ hηV.1)
  obtain ⟨γ, d, hacnf⟩ :=
    cnf_eq_singleton_of_isLUB Q a hQne hsingleQ hlubQ
  have hβγ : β < γ := cnf_singleton_exponent_lt_of_isLUB_not_mem
    Q a hsingleQ hlubQ haQ ⟨η₀, hη₀V, rfl⟩ hq₀cnf hacnf
  obtain ⟨hq₀eq, _, _, hlogq₀⟩ := cnf_singleton_spec hq₀cnf
  obtain ⟨haeq, hdpos, _, _⟩ := cnf_singleton_spec hacnf
  have hq₀a : (η₀.1 - ρ) + a = a := by
    apply Ordinal.add_of_omega0_opow_le
    · apply (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 ?_).2
      · simpa only [hlogq₀] using hβγ
      · rw [hq₀eq]
        exact mul_ne_zero (Ordinal.opow_ne_zero β Ordinal.omega0_ne_zero)
          (ne_of_gt (cnf_singleton_spec hq₀cnf).2.1)
    · rw [haeq]
      exact Ordinal.le_mul_left _ hdpos
  have hη₀adda : η₀.1 + a = α.1 := by
    calc
      η₀.1 + a = (ρ + (η₀.1 - ρ)) + a := by rw [hρaddη₀]
      _ = ρ + ((η₀.1 - ρ) + a) := add_assoc _ _ _
      _ = ρ + a := by rw [hq₀a]
      _ = α.1 := hρadda
  have hη₀α : cnfExtensionLT η₀.1 α.1 := by
    rw [← hη₀adda]
    exact cnfExtensionLT_add_singleton_of_last hη₀cnf hacnf hβγ.le
  exact cnfExtensionLE_partialOrder_and_subrelation.1.trans
    ζ.1 η₀.1 α.1 (Or.inr hζη₀) (Or.inr hη₀α)

/-- Controls the least CNF exponent of a chain supremum; used to keep the
supremum projection inside the required Gao stage. -/
theorem leastCNFExponent_chain_lub_le
    (ξ γ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1)
    (hleast : ∀ ζ ∈ Z, leastCNFExponent ζ.1 < γ) :
    leastCNFExponent α.1 ≤ γ := by
  classical
  by_cases hαZ : α ∈ Z
  · exact (hleast α hαZ).le
  obtain ⟨ζ, hζZ⟩ := hne
  have hζα : ζ.1 < α.1 := (hsup.1 ⟨ζ, hζZ, rfl⟩).lt_of_ne fun h ↦ by
    have hsub : ζ = α := Subtype.ext h
    exact hαZ (hsub ▸ hζZ)
  let U : GaoIndex ξ → Prop := fun η ↦ η ∈ Z ∧ ζ.1 < η.1
  have hU : ∃ η, U η := by
    by_contra h
    have hαζ : α.1 ≤ ζ.1 := hsup.2 (by
      rintro _ ⟨η, hηZ, rfl⟩
      exact le_of_not_gt fun hζη ↦ h ⟨η, hηZ, hζη⟩)
    exact (not_le_of_gt hζα) hαζ
  obtain ⟨η₀, hη₀U, hη₀min⟩ := exists_minimalFor_of_wellFoundedLT U
    (fun η : GaoIndex ξ ↦ (Ordinal.CNF Ordinal.omega0 η.1).length) hU
  have hη₀Z : η₀ ∈ Z := hη₀U.1
  let V : Set (GaoIndex ξ) := {η | η ∈ Z ∧ η₀.1 ≤ η.1}
  have hη₀V : η₀ ∈ V := ⟨hη₀Z, le_rfl⟩
  have hrelV : ∀ η ∈ V, cnfExtensionLE η₀.1 η.1 := by
    intro η hηV
    rcases hchain hη₀Z hηV.1 with h | h
    · exact h
    · exact Or.inl (le_antisymm hηV.2
        (cnfExtensionLE_partialOrder_and_subrelation.2 h))
  have hlenV : ∀ η ∈ V,
      (Ordinal.CNF Ordinal.omega0 η.1).length =
        (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · rw [heq]
    · have hle : (Ordinal.CNF Ordinal.omega0 η.1).length ≤
          (Ordinal.CNF Ordinal.omega0 η₀.1).length := by
        rcases cnfExtensionLT_iff_CNFListLT.mp hlt with
          ⟨pre, tail, x, y, hη₀cnf, hηcnf, _⟩
        rw [hη₀cnf, hηcnf]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      exact le_antisymm hle
        (hη₀min ⟨hηV.1, hη₀U.2.trans_le hηV.2⟩ hle)
  let pre := (Ordinal.CNF Ordinal.omega0 η₀.1).dropLast
  have hη₀ne : Ordinal.CNF Ordinal.omega0 η₀.1 ≠ [] := by
    have hη₀pos : 0 < η₀.1 :=
      (zero_le : (0 : Ordinal) ≤ ζ.1).trans_lt hη₀U.2
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 η₀.1
    rw [h] at hfold
    exact hη₀pos.ne' hfold.symm
  have hcnfV : ∀ η ∈ V, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] := by
    intro η hηV
    rcases hrelV η hηV with heq | hlt
    · have hsub : η₀ = η := Subtype.ext heq
      subst η
      let p := (Ordinal.CNF Ordinal.omega0 η₀.1).getLast hη₀ne
      refine ⟨p.1, p.2, ?_⟩
      simpa only [pre, p] using (List.dropLast_append_getLast hη₀ne).symm
    · obtain ⟨x, y, _, hηcnf, _⟩ :=
        CNFListLT.eq_dropLast_of_length_eq
          (cnfExtensionLT_iff_CNFListLT.mp hlt) (hlenV η hηV)
      exact ⟨y.1, y.2, hηcnf⟩
  let ρ : Ordinal.{u} := cnfValue pre
  have residual_of_common : ∀ (η : GaoIndex ξ) (δ d : Ordinal.{u}),
      Ordinal.CNF Ordinal.omega0 η.1 = pre ++ [(δ, d)] →
      Ordinal.CNF Ordinal.omega0 (η.1 - ρ) = [(δ, d)] ∧
        ρ + (η.1 - ρ) = η.1 := by
    intro η δ d hηcnf
    have hηeq : ρ + cnfValue [(δ, d)] = η.1 := by
      rw [← Ordinal.CNF.foldr Ordinal.omega0 η.1]
      change ρ + cnfValue [(δ, d)] = cnfValue (Ordinal.CNF Ordinal.omega0 η.1)
      rw [hηcnf, cnfValue_append]
    have hρle : ρ ≤ η.1 := hηeq ▸ le_self_add
    have hsub : η.1 - ρ = cnfValue [(δ, d)] :=
      Ordinal.sub_eq_of_add_eq hηeq
    constructor
    · rw [hsub]
      apply CNF_cnfValue
      · simp
      · intro p hp
        exact Ordinal.CNF.snd_pos (by
          rw [hηcnf]
          exact List.mem_append_right _ hp)
      · intro p hp
        exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
          rw [hηcnf]
          exact List.mem_append_right _ hp)
    · exact Ordinal.add_sub_cancel_of_le hρle
  let Q : Set (Ordinal.{u}) := (fun η : GaoIndex ξ ↦ η.1 - ρ) '' V
  have hQne : Q.Nonempty := ⟨η₀.1 - ρ, ⟨η₀, hη₀V, rfl⟩⟩
  have hsingleQ : ∀ q ∈ Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ := by
    rintro q ⟨η, hηV, rfl⟩
    obtain ⟨δ, d, hηcnf⟩ := hcnfV η hηV
    refine ⟨δ, d, (residual_of_common η δ d hηcnf).1, ?_⟩
    have := hleast η hηV.1
    simpa [leastCNFExponent, hηcnf] using this
  obtain ⟨δ₀, d₀, hη₀cnf⟩ := hcnfV η₀ hη₀V
  have hρaddη₀ := (residual_of_common η₀ δ₀ d₀ hη₀cnf).2
  have hρleη₀ : ρ ≤ η₀.1 := hρaddη₀ ▸ le_self_add
  have hρleα : ρ ≤ α.1 := hρleη₀.trans (hsup.1 ⟨η₀, hη₀Z, rfl⟩)
  let a : Ordinal.{u} := α.1 - ρ
  have hρadda : ρ + a = α.1 := Ordinal.add_sub_cancel_of_le hρleα
  have hlubQ : IsLUB Q a := by
    constructor
    · rintro _ ⟨η, hηV, rfl⟩
      rw [Ordinal.sub_le, hρadda]
      exact hsup.1 ⟨η, hηV.1, rfl⟩
    · intro b hb
      rw [Ordinal.sub_le]
      apply hsup.2
      rintro _ ⟨η, hηZ, rfl⟩
      rcases hchain hηZ hη₀Z with hηη₀ | hη₀η
      · calc
          η.1 ≤ η₀.1 := cnfExtensionLE_partialOrder_and_subrelation.2 hηη₀
          _ = ρ + (η₀.1 - ρ) := hρaddη₀.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η₀, hη₀V, rfl⟩) ρ
      · have hηV : η ∈ V := ⟨hηZ,
          cnfExtensionLE_partialOrder_and_subrelation.2 hη₀η⟩
        obtain ⟨δ, d, hηcnf⟩ := hcnfV η hηV
        have hρaddη := (residual_of_common η δ d hηcnf).2
        calc
          η.1 = ρ + (η.1 - ρ) := hρaddη.symm
          _ ≤ ρ + b := add_le_add_right (hb ⟨η, hηV, rfl⟩) ρ
  obtain ⟨Γ, D, hacnf⟩ := cnf_eq_singleton_of_isLUB Q a hQne
    (fun q hq ↦ let ⟨δ, d, h, _⟩ := hsingleQ q hq; ⟨δ, d, h⟩) hlubQ
  have hpowUpper : Ordinal.omega0 ^ γ ∈ upperBounds Q := by
    intro q hq
    obtain ⟨δ, d, hqcnf, hδγ⟩ := hsingleQ q hq
    obtain ⟨_, _, _, hlogq⟩ := cnf_singleton_spec hqcnf
    exact ((Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
      obtain ⟨hqeq, hdpos, _, _⟩ := cnf_singleton_spec hqcnf
      rw [hqeq]
      exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
        hdpos.ne')).2 (by simpa only [hlogq] using hδγ)).le
  have haPow : a ≤ Ordinal.omega0 ^ γ := hlubQ.2 hpowUpper
  obtain ⟨haeq, hDpos, _, _⟩ := cnf_singleton_spec hacnf
  have hΓγ : Γ ≤ γ := by
    rw [haeq] at haPow
    have hΓa : Ordinal.omega0 ^ Γ ≤ Ordinal.omega0 ^ Γ * D :=
      Ordinal.le_mul_left _ hDpos
    exact (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).mp
      (hΓa.trans haPow)
  have hsortedPre : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 η₀.1).pairwise
    rw [hη₀cnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hposPre : ∀ p ∈ pre, 0 < p.2 := by
    intro p hp
    exact Ordinal.CNF.snd_pos (by rw [hη₀cnf]; exact List.mem_append_left _ hp)
  have hltPre : ∀ p ∈ pre, p.2 < Ordinal.omega0 := by
    intro p hp
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hη₀cnf]
      exact List.mem_append_left _ hp)
  have hαcnf : Ordinal.CNF Ordinal.omega0 α.1 = cnfAddMonomial pre Γ D := by
    rw [← hρadda, haeq]
    exact CNF_cnfValue_add_monomial pre hsortedPre hposPre hltPre Γ D hDpos
      (cnf_singleton_spec hacnf).2.2.1
  rw [leastCNFExponent, hαcnf, cnfAddMonomial_lastExponent]
  exact hΓγ

/-- Claim 2 in the proof of Theorem `thm:solid-iterations`. -/
theorem ordinalProjection_chain_iSup
    (ξ : Ordinal.{u}) (Z : Set (GaoIndex ξ)) (α : GaoIndex ξ)
    (hne : Z.Nonempty)
    (hchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1)
    (hsup : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) α.1) :
    IsLUB (ordinalProjection ξ '' Z) (ordinalProjection ξ α) := by
  classical
  constructor
  · rintro _ ⟨ζ, hζ, rfl⟩
    exact (ordinalProjection_le_iff ξ ζ α).2
      (cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ hζ)
  · intro f hf
    by_cases hαZ : α ∈ Z
    · exact hf ⟨α, hαZ, rfl⟩
    · intro x
      by_cases hx : x.1 α = true
      · change (if x.1 α = true then 1 else 0) ≤ f x
        rw [ite_eq_left hx]
        by_contra hle
        have hfx : f x < 1 := lt_of_not_ge hle
        obtain ⟨F, hF⟩ := continuousMap_exists_finite_coordinates f x
          isOpen_Iio hfx
        have hαpos : 0 < α.1 := by
          rw [pos_iff_ne_zero]
          intro hαzero
          obtain ⟨ζ, hζ⟩ := hne
          have hζα : ζ.1 ≤ α.1 := hsup.1 ⟨ζ, hζ, rfl⟩
          have hζzero : ζ.1 = 0 :=
            le_antisymm (hαzero ▸ hζα) (zero_le : (0 : Ordinal) ≤ ζ.1)
          apply hαZ
          have hζeq : ζ = α := Subtype.ext (hζzero.trans hαzero.symm)
          exact hζeq ▸ hζ
        let Fα := F.filter fun i ↦ i.1 < α.1
        let δ : Ordinal.{u} := Fα.sup fun i ↦ i.1
        have hδα : δ < α.1 := by
          apply (Finset.sup_lt_iff hαpos).2
          intro i hi
          exact (Finset.mem_filter.mp hi).2
        have hex : ∃ ζ ∈ Z, δ < ζ.1 := by
          by_contra h
          push Not at h
          have hαδ : α.1 ≤ δ := hsup.2 (by
            rintro _ ⟨ζ, hζ, rfl⟩
            exact h ζ hζ)
          exact (not_le_of_gt hδα) hαδ
        obtain ⟨ζ₀, hζ₀Z, hδζ₀⟩ := hex
        let y : GaoIndex ξ → Bool := fun a ↦
          if cnfExtensionLE ζ₀.1 a.1 then true else x.1 a
        have hy_mono : ∀ a b : GaoIndex ξ,
            cnfExtensionLT a.1 b.1 → y a ≤ y b := by
          intro a b hab
          dsimp [y]
          by_cases ha : cnfExtensionLE ζ₀.1 a.1
          · have hb : cnfExtensionLE ζ₀.1 b.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.1.trans
                ζ₀.1 a.1 b.1 ha (Or.inr hab)
            rw [ite_eq_left ha, ite_eq_left hb]
          · rw [ite_eq_right ha]
            by_cases hb : cnfExtensionLE ζ₀.1 b.1
            · rw [ite_eq_left hb]
              exact Bool.le_true _
            · rw [ite_eq_right hb]
              exact x.2 a b hab
        have hζ₀α : cnfExtensionLT ζ₀.1 α.1 := by
          rcases cnfExtensionLE_chain_lub ξ Z α hchain hsup ζ₀ hζ₀Z with
            heq | hlt
          · have hsubeq : ζ₀ = α := Subtype.ext heq
            exact (hαZ (hsubeq ▸ hζ₀Z)).elim
          · exact hlt
        have hζ₀αOrd : ζ₀.1 < α.1 :=
          CNFListLT.ordinal_lt (cnfExtensionLT_iff_CNFListLT.mp hζ₀α)
        let yK : GaoCompactSpace ξ := ⟨y, hy_mono⟩
        have hyF : ∀ i ∈ F, yK.1 i = x.1 i := by
          intro i hi
          dsimp [yK, y]
          by_cases hζ₀i : cnfExtensionLE ζ₀.1 i.1
          · rw [ite_eq_left hζ₀i]
            have hζ₀iOrd : ζ₀.1 ≤ i.1 :=
              cnfExtensionLE_partialOrder_and_subrelation.2 hζ₀i
            by_cases hiα : i.1 < α.1
            · have hiFα : i ∈ Fα := Finset.mem_filter.mpr ⟨hi, hiα⟩
              have hiδ : i.1 ≤ δ := Finset.le_sup (f := fun j ↦ j.1) hiFα
              exact (not_lt_of_ge hiδ (hδζ₀.trans_le hζ₀iOrd)).elim
            · have hαi : α.1 ≤ i.1 := le_of_not_gt hiα
              rcases hαi.eq_or_lt with hαeqi | hαi
              · have hsubeq : α = i := Subtype.ext hαeqi
                subst i
                exact hx.symm
              · have hζ₀iLT : cnfExtensionLT ζ₀.1 i.1 := by
                  rcases hζ₀i with hζ₀eqi | hζ₀i
                  · exact (not_lt_of_ge hαi.le (hζ₀eqi ▸ hζ₀αOrd)).elim
                  · exact hζ₀i
                have hαiLT : cnfExtensionLT α.1 i.1 :=
                  (cnfExtensionLT_linear_above ζ₀.1 hζ₀α hζ₀iLT).mpr hαi
                exact (Bool.le_iff_imp.mp (x.2 α i hαiLT) hx).symm
          · rw [ite_eq_right hζ₀i]
        have hfy : f yK < 1 := hF yK hyF
        have hupper := hf ⟨ζ₀, hζ₀Z, rfl⟩ yK
        have hyζ₀ : yK.1 ζ₀ = true := by
          dsimp [yK, y]
          rw [ite_eq_left (show cnfExtensionLE ζ₀.1 ζ₀.1 from Or.inl rfl)]
        change (if yK.1 ζ₀ = true then 1 else 0) ≤ f yK at hupper
        rw [ite_eq_left hyζ₀] at hupper
        exact (not_lt_of_ge hupper hfy).elim
      · have hnonneg : 0 ≤ f x := by
          obtain ⟨ζ, hζ⟩ := hne
          have hproj : 0 ≤ ordinalProjection ξ ζ x := by
            change 0 ≤ if x.1 ζ = true then 1 else 0
            split_ifs <;> norm_num
          exact hproj.trans (hf ⟨ζ, hζ, rfl⟩ x)
        simp only [ordinalProjection, hx]
        exact hnonneg

end OrdinalConstruction

end OrderClosures
