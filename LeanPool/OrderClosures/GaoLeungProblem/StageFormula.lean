/-
Copyright (c) 2026 Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antonio Avilés, Mitchell A. Taylor, Pedro Tradacete
-/

module

public import LeanPool.OrderClosures.GaoLeungProblem.OrdinalSpace


/-!
# Adherence formulas for Gao stages
-/

@[expose] public section

namespace OrderClosures

open Set

universe u v

section OrdinalConstruction

/-- Stage indices whose coordinate projections dominate a given function;
used to select finite minimal dominators. -/
def gaoDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {ζ | ζ ∈ GaoStageIndices ξ γ ∧ b ≤ ordinalProjection ξ ζ}

/-- Minimal elements of the dominator set in the CNF extension order; used to
reduce a positive directed family to finitely many coordinates. -/
def gaoMinimalDominators (ξ γ : Ordinal.{u})
    (b : C(GaoCompactSpace ξ, ℝ)) : Set (GaoIndex ξ) :=
  {μ | μ ∈ gaoDominators ξ γ b ∧
    ∀ η ∈ gaoDominators ξ γ b, cnfExtensionLE η.1 μ.1 → η = μ}

/-- Extracts a coordinate projection dominating a positive Gao-stage element;
this starts the finite-minimal-dominator reduction. -/
theorem gaoDominators_nonempty
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hb : b ∈ GaoStageSet ξ γ) :
    (gaoDominators ξ γ b).Nonempty := by
  obtain ⟨ζ, hζ, hbζ⟩ := hb
  refine ⟨ζ, hζ, ?_⟩
  simpa only [abs_of_nonneg hb0] using hbζ

/-- Refines any dominator to a minimal one; used to replace arbitrary
dominating coordinates by a finite canonical family. -/
theorem gaoDominator_above_minimal
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    {ζ : GaoIndex ξ} (hζ : ζ ∈ gaoDominators ξ γ b) :
    ∃ μ ∈ gaoMinimalDominators ξ γ b, cnfExtensionLE μ.1 ζ.1 := by
  classical
  let P : GaoIndex ξ → Prop := fun η ↦
    η ∈ gaoDominators ξ γ b ∧ cnfExtensionLE η.1 ζ.1
  obtain ⟨μ, hμP, hμmin⟩ := exists_minimalFor_of_wellFoundedLT P
    (fun η : GaoIndex ξ ↦ η.1) ⟨ζ, hζ, Or.inl rfl⟩
  refine ⟨μ, ⟨hμP.1, ?_⟩, hμP.2⟩
  intro η hη hημ
  have hηP : P η := ⟨hη,
    cnfExtensionLE_partialOrder_and_subrelation.1.trans
      η.1 μ.1 ζ.1 hημ hμP.2⟩
  have hηleμ := cnfExtensionLE_partialOrder_and_subrelation.2 hημ
  exact Subtype.ext (le_antisymm hηleμ (hμmin hηP hηleμ))

/-- Shows that distinct minimal dominators are CNF-incomparable; used with the
incomparable-projection infimum theorem. -/
theorem gaoMinimalDominators_pairwise
    (ξ γ : Ordinal.{u}) (b : C(GaoCompactSpace ξ, ℝ)) :
    (gaoMinimalDominators ξ γ b).Pairwise
      (fun μ ν ↦ ¬ cnfExtensionLE μ.1 ν.1) := by
  intro μ hμ ν hν hne hμν
  exact hne (hν.2 μ hμ.1 hμν)

/-- Proves finiteness of the minimal dominator family; needed to combine it
with directedness of the positive approximating set. -/
theorem gaoMinimalDominators_finite
    (ξ γ : Ordinal.{u}) {b : C(GaoCompactSpace ξ, ℝ)}
    (hb0 : 0 ≤ b) (hbne : b ≠ 0) :
    (gaoMinimalDominators ξ γ b).Finite := by
  classical
  by_contra hinf
  have hMInf : (gaoMinimalDominators ξ γ b).Infinite := hinf
  have hglb := ordinalProjection_incomparable_iInf ξ
    (gaoMinimalDominators ξ γ b) hMInf
    (gaoMinimalDominators_pairwise ξ γ b)
  have hbLower : b ∈ lowerBounds
      (ordinalProjection ξ '' gaoMinimalDominators ξ γ b) := by
    rintro _ ⟨μ, hμ, rfl⟩
    exact hμ.1.2
  have hb_le_zero : b ≤ 0 := hglb.2 hbLower
  exact hbne (le_antisymm hb_le_zero hb0)

/-- Produces one Gao-stage coordinate dominating an entire directed positive
family; this is the main input to the forward adherence inclusion. -/
theorem directedPositive_gaoStage_dominated
    (ξ γ : Ordinal.{u}) {z : C(GaoCompactSpace ξ, ℝ)}
    (hz : z ∈ directedPositiveAdherence (GaoStageSet ξ γ)) :
    ∃ α : GaoIndex ξ, α.1 ≤ Ordinal.omega0 ^ ξ ∧
      leastCNFExponent α.1 ≤ γ ∧ z ≤ ordinalProjection ξ α := by
  classical
  rcases hz with ⟨hz0, B, hBstage, hBne, hBdir, hBlub⟩
  by_cases hzero : z = 0
  · let α : GaoIndex ξ := ⟨0, by simp⟩
    refine ⟨α, by simp [α], by simp [α, leastCNFExponent], ?_⟩
    rw [hzero]
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  have hbne : ∃ b ∈ B, b ≠ 0 := by
    by_contra h
    have hzeroUpper : (0 : C(GaoCompactSpace ξ, ℝ)) ∈ upperBounds B := by
      intro b hb
      have hb0 := (hBstage hb).2
      have hbzero : b = 0 := by
        by_contra hbne'
        exact h ⟨b, hb, hbne'⟩
      rw [hbzero]
    exact hzero (le_antisymm (hBlub.2 hzeroUpper) hz0)
  obtain ⟨b₀, hb₀B, hb₀ne⟩ := hbne
  have hb₀0 : 0 ≤ b₀ := (hBstage hb₀B).2
  let M := gaoMinimalDominators ξ γ b₀
  have hMfin : M.Finite := gaoMinimalDominators_finite ξ γ hb₀0 hb₀ne
  have hMne : M.Nonempty := by
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb₀0 (hBstage hb₀B).1
    obtain ⟨μ, hμ, _⟩ := gaoDominator_above_minimal ξ γ hζ
    exact ⟨μ, hμ⟩
  let : Nonempty B := hBne.to_subtype
  let : IsDirectedOrder B := hBdir.isDirectedOrder
  let b₀B : B := ⟨b₀, hb₀B⟩
  let D : M → Set B := fun μ ↦
    {b | b₀ ≤ b.1 ∧ ∃ ζ ∈ gaoDominators ξ γ b.1,
      cnfExtensionLE μ.1.1 ζ.1}
  have hcover : ∀ b : B, b₀ ≤ b.1 → ∃ μ : M, b ∈ D μ := by
    intro b hb₀b
    have hb0 : 0 ≤ b.1 := (hBstage b.2).2
    obtain ⟨ζ, hζ⟩ := gaoDominators_nonempty ξ γ hb0 (hBstage b.2).1
    have hζ₀ : ζ ∈ gaoDominators ξ γ b₀ := ⟨hζ.1, hb₀b.trans hζ.2⟩
    obtain ⟨μ, hμ, hμζ⟩ := gaoDominator_above_minimal ξ γ hζ₀
    exact ⟨⟨μ, hμ⟩, hb₀b, ζ, hζ, hμζ⟩
  have hcofinal : ∃ μ : M, ∀ b : B, ∃ c ∈ D μ, b ≤ c := by
    by_contra h
    have hbad : ∀ μ : M, ∃ b : B, ∀ c ∈ D μ, ¬ b ≤ c := by
      intro μ
      have hμ : ¬ ∀ b : B, ∃ c ∈ D μ, b ≤ c := fun hμ ↦ h ⟨μ, hμ⟩
      push Not at hμ
      exact hμ
    choose w hw using hbad
    let : Fintype M := hMfin.fintype
    obtain ⟨d, hd⟩ := Finite.exists_le w
    obtain ⟨e, hde, hb₀e⟩ := exists_ge_ge d b₀B
    obtain ⟨μ, heD⟩ := hcover e hb₀e
    exact (hw μ e heD) ((hd μ).trans hde)
  obtain ⟨μ, hμcofinal⟩ := hcofinal
  have hDne : (D μ).Nonempty := by
    obtain ⟨c, hcD, _⟩ := hμcofinal b₀B
    exact ⟨c, hcD⟩
  let ζfun : D μ → GaoIndex ξ := fun b ↦ Classical.choose b.2.2
  have hζfun : ∀ b : D μ,
      ζfun b ∈ gaoDominators ξ γ b.1.1 ∧
        cnfExtensionLE μ.1.1 (ζfun b).1 := fun b ↦
    ⟨Classical.choose_spec b.2.2 |>.1,
      Classical.choose_spec b.2.2 |>.2⟩
  let Z : Set (GaoIndex ξ) := Set.range ζfun
  have hZne : Z.Nonempty := by
    obtain ⟨b, hb⟩ := hDne
    exact ⟨ζfun ⟨b, hb⟩, ⟨⟨b, hb⟩, rfl⟩⟩
  have hZchain : ∀ ⦃ζ⦄, ζ ∈ Z → ∀ ⦃ζ'⦄, ζ' ∈ Z →
      cnfExtensionLE ζ.1 ζ'.1 ∨ cnfExtensionLE ζ'.1 ζ.1 := by
    rintro _ ⟨b, rfl⟩ _ ⟨c, rfl⟩
    exact cnfExtensionLE_linear_above μ.1.1 (hζfun b).2 (hζfun c).2
  let a : Ordinal.{u} := sSup ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z)
  have hvalsne : ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z).Nonempty := hZne.image _
  have hvalsBdd : BddAbove ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) := by
    refine ⟨Ordinal.omega0 ^ ξ, ?_⟩
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  have haLUB : IsLUB ((fun ζ : GaoIndex ξ ↦ ζ.1) '' Z) a :=
    isLUB_csSup hvalsne hvalsBdd
  have hale : a ≤ Ordinal.omega0 ^ ξ := by
    apply haLUB.2
    rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
    exact (hζfun b).1.1.1
  let α : GaoIndex ξ := ⟨a, hale.trans le_self_add⟩
  have hprojLUB : IsLUB (ordinalProjection ξ '' Z)
      (ordinalProjection ξ α) :=
    ordinalProjection_chain_iSup ξ Z α hZne hZchain haLUB
  have hzα : z ≤ ordinalProjection ξ α := hBlub.2 (by
    intro b hbB
    obtain ⟨c, hcD, hbc⟩ := hμcofinal ⟨b, hbB⟩
    let cD : D μ := ⟨c, hcD⟩
    calc
      b ≤ c.1 := hbc
      _ ≤ ordinalProjection ξ (ζfun cD) := (hζfun cD).1.2
      _ ≤ ordinalProjection ξ α := hprojLUB.1 ⟨ζfun cD, ⟨cD, rfl⟩, rfl⟩)
  have hleast : leastCNFExponent α.1 ≤ γ := by
    apply leastCNFExponent_chain_lub_le ξ γ Z α hZne hZchain haLUB
    rintro _ ⟨b, rfl⟩
    exact (hζfun b).1.1.2
  exact ⟨α, hale, hleast, hzα⟩

/-- Establishes the forward inclusion for one order-adherence step by using a
single coordinate dominator. -/
theorem orderAdherence_gaoStage_subset
    (ξ γ : Ordinal.{u}) :
    orderAdherence (GaoStageSet ξ γ) ⊆ GaoStageSet ξ (γ + 1) := by
  rw [orderAdherence_eq_solidOrderAdherence (isSolid_gaoStageSet ξ γ)]
  rintro f ⟨z, hz, hfz⟩
  obtain ⟨α, hαbound, hαleast, hzα⟩ :=
    directedPositive_gaoStage_dominated ξ γ hz
  refine ⟨α, ⟨hαbound, ?_⟩, hfz.trans ?_⟩
  · exact hαleast.trans_lt (lt_add_one γ)
  · simpa only [abs_of_nonneg hz.1] using hzα

/-- Singleton omega monomials with exponent below `γ`; used as the directed
approximating family for a limit-stage coordinate. -/
def singletonCNFBelow (γ : Ordinal.{u}) : Set (Ordinal.{u}) :=
  {q | ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧
    q < Ordinal.omega0 ^ γ}

/-- Shows that singleton CNF monomials below `γ` have supremum `ω^γ`; used to
construct the reverse adherence approximation at limit exponents. -/
theorem singletonCNFBelow_isLUB (γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    IsLUB (singletonCNFBelow γ) (Ordinal.omega0 ^ γ) := by
  constructor
  · rintro q ⟨δ, d, hq, hqpow⟩
    exact hqpow.le
  · intro c hc
    have hlim : Order.IsSuccLimit (Ordinal.omega0 ^ γ) :=
      Ordinal.isSuccLimit_opow_left Ordinal.isSuccLimit_omega0 hγ
    apply hlim.isLUB_Iio.2
    intro r hr
    by_cases hr0 : r = 0
    · subst r
      exact zero_le
    let δ := Ordinal.log Ordinal.omega0 r
    let d := r / Ordinal.omega0 ^ δ
    let q := Ordinal.omega0 ^ δ * (d + 1)
    have hdpos : 0 < d := Ordinal.div_opow_log_pos Ordinal.omega0 hr0
    have hdlt : d < Ordinal.omega0 :=
      Ordinal.div_opow_log_lt r Ordinal.one_lt_omega0
    have hdsuccpos : 0 < d + 1 := hdpos.trans_le le_self_add
    have hdsucclt : d + 1 < Ordinal.omega0 := by
      obtain ⟨n, hn⟩ := Ordinal.lt_omega0.mp hdlt
      rw [hn, ← Nat.cast_one, ← Nat.cast_add]
      exact Ordinal.natCast_lt_omega0 (n + 1)
    have hδγ : δ < γ :=
      (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 hr0).mp hr
    have hqcnf : Ordinal.CNF Ordinal.omega0 q = [(δ, d + 1)] := by
      dsimp [q]
      simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
        (e := δ) (x := d + 1) (y := 0) Ordinal.one_lt_omega0
        hdsuccpos.ne' hdsucclt (Ordinal.opow_pos δ Ordinal.omega0_pos)
    have hqpow : q < Ordinal.omega0 ^ γ := by
      dsimp [q]
      simpa only [add_zero] using Ordinal.opow_mul_add_lt_opow hdsucclt
        (Ordinal.opow_pos δ Ordinal.omega0_pos) hδγ
    have hrq : r < q := by
      rw [← Ordinal.div_add_mod r (Ordinal.omega0 ^ δ)]
      dsimp [q, d]
      exact Ordinal.opow_mul_add_lt_opow_mul
        (Ordinal.mod_lt r (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero))
        (lt_add_one (r / Ordinal.omega0 ^ δ))
    exact hrq.le.trans (hc ⟨δ, d + 1, hqcnf, hqpow⟩)

/-- Turns a strict exponent inequality into a strict CNF extension of
singleton monomials; used by `gaoIndex_approximation`. -/
theorem singletonCNF_step_of_lt
    {q r δ d ε e : Ordinal.{u}}
    (hq : Ordinal.CNF Ordinal.omega0 q = [(δ, d)])
    (hr : Ordinal.CNF Ordinal.omega0 r = [(ε, e)]) (hqr : q < r) :
    (ε = δ ∧ d < e) ∨ δ < ε := by
  obtain ⟨hqeq, _, _, hlogq⟩ := cnf_singleton_spec hq
  obtain ⟨hreq, _, _, hlogr⟩ := cnf_singleton_spec hr
  have hδε : δ ≤ ε := by
    have := Ordinal.log_mono_right Ordinal.omega0 hqr.le
    simpa only [hlogq, hlogr] using this
  rcases hδε.eq_or_lt with hδε | hδε
  · left
    refine ⟨hδε.symm, ?_⟩
    rw [← hδε] at hreq
    by_contra h
    have hed : e ≤ d := le_of_not_gt h
    have hmul : Ordinal.omega0 ^ δ * e ≤ Ordinal.omega0 ^ δ * d :=
      mul_le_mul_right hed _
    exact (not_le_of_gt (by rw [← hqeq, ← hreq]; exact hqr)) hmul
  · exact Or.inr hδε

/-- Appending a smaller singleton CNF term to a finite prefix computes its normal form. -/
theorem cnfValue_add_singleton_below
    (pre : List (Ordinal.{u} × Ordinal.{u})) (γ : Ordinal.{u}) (n : ℕ)
    (hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x))
    (hpreAbove : ∀ x ∈ pre, γ < x.1)
    (hprePos : ∀ x ∈ pre, 0 < x.2)
    (hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0)
    (q : Ordinal.{u}) (hq : q ∈ singletonCNFBelow γ) :
    ∃ δ d, Ordinal.CNF Ordinal.omega0 q = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0
        (cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + q) =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by
  obtain ⟨δ, d, hqcnf, hqpow⟩ := hq
  obtain ⟨hqeq, hdpos, hdlt, hlogq⟩ := cnf_singleton_spec hqcnf
  have hδγraw : Ordinal.log Ordinal.omega0 q < γ :=
    (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0 (by
      rw [hqeq]
      exact mul_ne_zero (Ordinal.opow_ne_zero δ Ordinal.omega0_ne_zero)
        hdpos.ne')).mp hqpow
  have hδγ : δ < γ := by simpa only [hlogq] using hδγraw
  refine ⟨δ, d, hqcnf, hδγ, ?_⟩
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, mul_zero, add_zero, ↓reduceIte]
    rw [hqeq, CNF_cnfValue_add_monomial pre hpreSorted hprePos hpreLt
      δ d hdpos hdlt, cnfAddMonomial_eq_append_of_lt_all pre δ d
        (fun x hx ↦ hδγ.trans (hpreAbove x hx))]
  · let l := pre ++ [(γ, (n : Ordinal))]
    have hnpos : 0 < (n : Ordinal) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hnlt : (n : Ordinal) < Ordinal.omega0 := Ordinal.natCast_lt_omega0 n
    have hlsorted : (l.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
      dsimp [l]
      rw [List.map_append, List.pairwise_append]
      refine ⟨hpreSorted, by simp, ?_⟩
      intro a ha b hb
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      simp only [List.map_singleton, List.mem_singleton] at hb
      subst b
      exact hpreAbove x hx
    have hlpos : ∀ x ∈ l, 0 < x.2 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hprePos x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact hnpos
    have hllt : ∀ x ∈ l, x.2 < Ordinal.omega0 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hpreLt x hx
      · simp only [List.mem_singleton] at hx
        subst x
        exact hnlt
    have hδl : ∀ x ∈ l, δ < x.1 := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hδγ.trans (hpreAbove x hx)
      · simp only [List.mem_singleton] at hx
        subst x
        exact hδγ
    rw [ite_eq_right hn]
    change Ordinal.CNF Ordinal.omega0
      ((cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal)) + q) =
        pre ++ (γ, (n : Ordinal)) :: [(δ, d)]
    have hlvalue : cnfValue l = cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) := by
      dsimp [l]
      rw [cnfValue_append]
      simp [cnfValue]
    rw [← hlvalue, hqeq,
      CNF_cnfValue_add_monomial l hlsorted hlpos hllt δ d hdpos hdlt,
      cnfAddMonomial_eq_append_of_lt_all l δ d hδl]
    simp [l, List.append_assoc]

/-- Builds a directed family of earlier-stage indices whose projections order
converge to a prescribed next-stage projection. -/
theorem gaoIndex_approximation
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) (ζ : GaoIndex ξ)
    (hζbound : ζ.1 ≤ Ordinal.omega0 ^ ξ)
    (hζleast : leastCNFExponent ζ.1 = γ) :
    ∃ Z : Set (GaoIndex ξ), Z.Nonempty ∧
      (∀ η ∈ Z, η ∈ GaoStageIndices ξ γ) ∧
      (∀ ⦃η⦄, η ∈ Z → ∀ ⦃η'⦄, η' ∈ Z →
        cnfExtensionLE η.1 η'.1 ∨ cnfExtensionLE η'.1 η.1) ∧
      IsLUB ((fun η : GaoIndex ξ ↦ η.1) '' Z) ζ.1 := by
  classical
  have hζ0 : ζ.1 ≠ 0 := by
    intro hzero
    have : γ = 0 := by
      rw [← hζleast, hzero]
      simp [leastCNFExponent]
    exact hγ this
  let pre := (Ordinal.CNF Ordinal.omega0 ζ.1).dropLast
  have hcnfne : Ordinal.CNF Ordinal.omega0 ζ.1 ≠ [] := by
    intro h
    have hfold := Ordinal.CNF.foldr Ordinal.omega0 ζ.1
    rw [h] at hfold
    exact hζ0 hfold.symm
  let p := (Ordinal.CNF Ordinal.omega0 ζ.1).getLast hcnfne
  have hpcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [p] := by
    simpa only [pre, p] using (List.dropLast_append_getLast hcnfne).symm
  have hpγ : p.1 = γ := by
    have := hζleast
    rw [leastCNFExponent, hpcnf] at this
    have hlast : (pre ++ [p]).getLast? = some p := by simp
    rw [hlast] at this
    simpa using this
  let c := p.2
  have hpeq : p = (γ, c) := Prod.ext hpγ rfl
  have hζcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = pre ++ [(γ, c)] := by
    rw [hpcnf, hpeq]
  have hcpos : 0 < c := by
    apply Ordinal.CNF.snd_pos (x := (γ, c))
    rw [hζcnf]
    simp
  have hclt : c < Ordinal.omega0 := by
    apply Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (x := (γ, c))
    rw [hζcnf]
    simp
  obtain ⟨m, hm⟩ := Ordinal.lt_omega0.mp hclt
  have hmpos : 0 < m := by rw [hm] at hcpos; exact_mod_cast hcpos
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hmpos)
  let ρ : Ordinal.{u} := cnfValue pre
  let base : Ordinal.{u} := ρ + Ordinal.omega0 ^ γ * (n : Ordinal)
  have hζeq : ζ.1 = base + Ordinal.omega0 ^ γ := by
    rw [← Ordinal.CNF.foldr Ordinal.omega0 ζ.1, hζcnf, hm]
    change cnfValue (pre ++ [(γ, ((n + 1 : ℕ) : Ordinal))]) =
      base + Ordinal.omega0 ^ γ
    rw [cnfValue_append]
    simp only [cnfValue, List.foldr_cons, List.foldr_nil, add_zero]
    dsimp [base, ρ]
    change cnfValue pre + Ordinal.omega0 ^ γ * ((n + 1 : ℕ) : Ordinal) =
      cnfValue pre + Ordinal.omega0 ^ γ * (n : Ordinal) + Ordinal.omega0 ^ γ
    simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, add_assoc]
  let Q := singletonCNFBelow γ
  have hQne : Q.Nonempty := by
    have hγpos : 0 < γ := (pos_iff_ne_zero).2 hγ
    have honepow : (1 : Ordinal) < Ordinal.omega0 ^ γ := by
      have hp : Ordinal.omega0 ^ (1 : Ordinal) ≤ Ordinal.omega0 ^ γ :=
        (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).2
          (by simpa using (Order.succ_le_iff.2 hγpos : Order.succ 0 ≤ γ))
      exact Ordinal.one_lt_omega0.trans_le (by simpa using hp)
    refine ⟨1, 0, 1, ?_, honepow⟩
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := 0) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos 0 Ordinal.omega0_pos)
  let ηval : Q → Ordinal.{u} := fun q ↦ base + q.1
  have hηlt : ∀ q : Q, ηval q < ζ.1 := by
    intro q
    obtain ⟨δ, d, hqcnf, hqpow⟩ := q.2
    rw [hζeq]
    exact (add_lt_add_iff_left base).2 hqpow
  let η : Q → GaoIndex ξ := fun q ↦
    ⟨ηval q, (hηlt q).le.trans hζbound |>.trans le_self_add⟩
  have hpreSorted : (pre.map Prod.fst).Pairwise (fun x y ↦ y < x) := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    exact h.1
  have hpreAbove : ∀ x ∈ pre, γ < x.1 := by
    have h := (Ordinal.CNF.sortedGT Ordinal.omega0 ζ.1).pairwise
    rw [hζcnf, List.map_append, List.pairwise_append] at h
    intro x hx
    exact h.2.2 x.1 (by exact List.mem_map.mpr ⟨x, hx, rfl⟩)
      γ (by simp)
  have hprePos : ∀ x ∈ pre, 0 < x.2 := by
    intro x hx
    exact Ordinal.CNF.snd_pos (by rw [hζcnf]; exact List.mem_append_left _ hx)
  have hpreLt : ∀ x ∈ pre, x.2 < Ordinal.omega0 := by
    intro x hx
    exact Ordinal.CNF.snd_lt Ordinal.one_lt_omega0 (by
      rw [hζcnf]
      exact List.mem_append_left _ hx)
  have hηcnf : ∀ q : Q, ∃ δ d,
      Ordinal.CNF Ordinal.omega0 q.1 = [(δ, d)] ∧ δ < γ ∧
      Ordinal.CNF Ordinal.omega0 (η q).1 =
        if n = 0 then pre ++ [(δ, d)]
        else pre ++ (γ, (n : Ordinal)) :: [(δ, d)] := by
    intro q
    exact cnfValue_add_singleton_below pre γ n hpreSorted hpreAbove hprePos hpreLt q.1 q.2
  have hηstage : ∀ q : Q, η q ∈ GaoStageIndices ξ γ := by
    intro q
    obtain ⟨δ, d, hqcnf, hδγ, hcnf⟩ := hηcnf q
    refine ⟨(hηlt q).le.trans hζbound, ?_⟩
    rw [leastCNFExponent, hcnf]
    split_ifs <;> simp_all
  let Z : Set (GaoIndex ξ) := Set.range η
  let : Nonempty Q := hQne.to_subtype
  have hZne : Z.Nonempty := Set.range_nonempty η
  have hZstage : ∀ η' ∈ Z, η' ∈ GaoStageIndices ξ γ := by
    rintro _ ⟨q, rfl⟩
    exact hηstage q
  have hηchainLT : ∀ q r : Q, q.1 < r.1 →
      cnfExtensionLT (η q).1 (η r).1 := by
    intro q r hqr
    obtain ⟨δ, d, hqcnf, hδγ, hqηcnf⟩ := hηcnf q
    obtain ⟨ε, e, hrcnf, hεγ, hrηcnf⟩ := hηcnf r
    have hstep := singletonCNF_step_of_lt hqcnf hrcnf hqr
    by_cases hn : n = 0
    · refine ⟨pre, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn] using hqηcnf
      · simpa [hn] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, by
            by_cases hp : pre = []
            · exact Or.inl hp
            · let last := pre.getLast hp
              have hlast : pre.getLast? = some last := by
                dsimp [last]
                exact List.getLast?_eq_getLast_of_ne_nil hp
              have hlastMem : last ∈ pre := by
                dsimp [last]
                exact List.getLast_mem hp
              exact Or.inr ⟨last.1, last.2, hlast,
                hεγ.trans (hpreAbove last hlastMem)⟩⟩
    · let common := pre ++ [(γ, (n : Ordinal))]
      refine ⟨common, [], δ, d, ε, e, ?_, ?_, ?_⟩
      · simpa [hn, common, List.append_assoc] using hqηcnf
      · simpa [hn, common, List.append_assoc] using hrηcnf
      · rcases hstep with hsame | hexp
        · exact Or.inl hsame
        · exact Or.inr ⟨hexp, Or.inr ⟨γ, (n : Ordinal), by
            simp [common], hεγ⟩⟩
  have hZchain : ∀ ⦃η₁⦄, η₁ ∈ Z → ∀ ⦃η₂⦄, η₂ ∈ Z →
      cnfExtensionLE η₁.1 η₂.1 ∨ cnfExtensionLE η₂.1 η₁.1 := by
    rintro _ ⟨q, rfl⟩ _ ⟨r, rfl⟩
    rcases lt_trichotomy q.1 r.1 with hlt | heq | hgt
    · exact Or.inl (Or.inr (hηchainLT q r hlt))
    · have hsub : q = r := Subtype.ext heq
      subst r
      exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr (hηchainLT r q hgt))
  have hvalLUB : IsLUB ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) ζ.1 := by
    have hmap := (Ordinal.isNormal_add_right base).map_isLUB
      (singletonCNFBelow_isLUB γ hγ) hQne
    rw [hζeq]
    have hsets : ((fun η' : GaoIndex ξ ↦ η'.1) '' Z) =
        (fun q : Ordinal.{u} ↦ base + q) '' Q := by
      ext x
      constructor
      · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
        exact ⟨q.1, q.2, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact ⟨η ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, rfl⟩
    rw [hsets]
    exact hmap
  exact ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩

/-- Establishes the reverse inclusion for a successor Gao stage from the
explicit coordinate approximations. -/
theorem gaoStage_succ_subset_orderAdherence
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    GaoStageSet ξ (γ + 1) ⊆ orderAdherence (GaoStageSet ξ γ) := by
  classical
  intro f hf
  obtain ⟨ζ, hζstage, hfζ⟩ := hf
  by_cases hleast : leastCNFExponent ζ.1 < γ
  · exact subset_orderAdherence (GaoStageSet ξ γ)
      ⟨ζ, ⟨hζstage.1, hleast⟩, hfζ⟩
  have hleastLe : leastCNFExponent ζ.1 ≤ γ := by
    rw [← Order.succ_eq_add_one] at hζstage
    exact Order.lt_succ_iff.mp hζstage.2
  have hleastEq : leastCNFExponent ζ.1 = γ :=
    le_antisymm hleastLe (le_of_not_gt hleast)
  obtain ⟨Z, hZne, hZstage, hZchain, hvalLUB⟩ :=
    gaoIndex_approximation ξ γ hγ ζ hζstage.1 hleastEq
  have hprojLUB := ordinalProjection_chain_iSup ξ Z ζ hZne hZchain hvalLUB
  let : Nonempty Z := hZne.to_subtype
  let p : Z → C(GaoCompactSpace ξ, ℝ) := fun η ↦ ordinalProjection ξ η.1
  have hpmono : Monotone p := by
    intro η θ hηθ
    apply (ordinalProjection_le_iff ξ η.1 θ.1).2
    rcases hZchain η.2 θ.2 with h | h
    · exact h
    · have hOrd := cnfExtensionLE_partialOrder_and_subrelation.2 h
      exact Or.inl (le_antisymm hηθ hOrd)
  have hpLUB : IsLUB (Set.range p) (ordinalProjection ξ ζ) := by
    have hsets : Set.range p = ordinalProjection ξ '' Z := by
      ext g
      constructor
      · rintro ⟨η, rfl⟩
        exact ⟨η.1, η.2, rfl⟩
      · rintro ⟨η, hηZ, rfl⟩
        exact ⟨⟨η, hηZ⟩, rfl⟩
    rw [hsets]
    exact hprojLUB
  have hprojAdh : ordinalProjection ξ ζ ∈ orderAdherence (GaoStageSet ξ γ) := by
    refine ⟨Z, inferInstance, inferInstance, inferInstance, p, ?_,
      orderConvergesTo_of_monotone_isLUB hpmono hpLUB⟩
    intro η
    refine ⟨η.1, hZstage η.1 η.2, ?_⟩
    have hnonneg : 0 ≤ ordinalProjection ξ η.1 := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg]
  apply isSolid_orderAdherence (isSolid_gaoStageSet ξ γ) hprojAdh
  have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
    intro x
    simp only [ordinalProjection]
    split_ifs <;> norm_num
  simpa only [abs_of_nonneg hnonneg] using hfζ

/-- Packages both inclusions into the one-step Gao-stage formula; used by the
transfinite induction in `gao_orderAdherence_stage_formula`. -/
theorem orderAdherence_gaoStage
    (ξ γ : Ordinal.{u}) (hγ : γ ≠ 0) :
    orderAdherence (GaoStageSet ξ γ) = GaoStageSet ξ (γ + 1) :=
  Set.Subset.antisymm (orderAdherence_gaoStage_subset ξ γ)
    (gaoStage_succ_subset_orderAdherence ξ γ hγ)

/-- Claim 3 in the proof of Theorem `thm:solid-iterations`. -/
theorem gao_orderAdherence_stage_formula
    (ξ : Ordinal.{u}) (T : OrderAdherenceTower (GaoStageSet ξ 1)) :
    ∀ β ≤ ξ, T.stage (Ordinal.lift.{u + 1, u} β) = GaoStageSet ξ (1 + β) := by
  intro β
  induction β using Ordinal.limitRecOn with
  | zero =>
      intro hzero
      simpa using T.stage_zero
  | add_one β ih =>
      intro hβ
      have hβξ : β ≤ ξ := le_self_add.trans hβ
      have hstage := ih hβξ
      have hnonzero : 1 + β ≠ 0 := by
        exact (zero_lt_one.trans_le (le_self_add : (1 : Ordinal) ≤ 1 + β)).ne'
      rw [show Ordinal.lift.{u + 1, u} (β + 1) =
          Order.succ (Ordinal.lift.{u + 1, u} β) by
            rw [Order.succ_eq_add_one, Ordinal.lift_add_one],
        T.stage_succ, hstage, orderAdherence_gaoStage ξ (1 + β) hnonzero,
        add_assoc]
  | limit β hβlim ih =>
      intro hβξ
      rw [T.stage_limit _ (Ordinal.isSuccLimit_lift.mpr hβlim)]
      ext f
      constructor
      · intro hf
        rcases Set.mem_iUnion.mp hf with ⟨η, hfη⟩
        obtain ⟨δ, hδη⟩ := Ordinal.mem_range_lift_of_le η.2.le
        have hδβ : δ < β := by
          have h := η.2
          rw [← hδη] at h
          exact Ordinal.lift_lt.mp h
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        have hfδ : f ∈ GaoStageSet ξ (1 + δ) := by
          rw [← ih δ hδβ hδξ]
          simpa only [hδη] using hfη
        obtain ⟨ζ, hζ, hfζ⟩ := hfδ
        exact ⟨ζ, ⟨hζ.1, hζ.2.trans_le (add_le_add_right hδβ.le 1)⟩, hfζ⟩
      · intro hf
        obtain ⟨ζ, hζ, hfζ⟩ := hf
        obtain ⟨δ, hδβ, hleastδ⟩ :=
          ((Ordinal.isNormal_add_right 1).lt_iff_exists_lt hβlim).mp hζ.2
        have hδξ : δ ≤ ξ := hδβ.le.trans hβξ
        apply Set.mem_iUnion.mpr
        let η : Set.Iio (Ordinal.lift.{u + 1, u} β) :=
          ⟨Ordinal.lift.{u + 1, u} δ, Ordinal.lift_lt.mpr hδβ⟩
        refine ⟨η, ?_⟩
        rw [ih δ hδβ hδξ]
        exact ⟨ζ, ⟨hζ.1, hleastδ⟩, hfζ⟩

/-- The strict witness separating consecutive stages in Claim 3. -/
theorem ordinalProjection_strict_stage
    (ξ γ : Ordinal.{u}) (hγ : γ ≤ ξ) :
    ∃ ζ : GaoIndex ξ,
      ordinalProjection ξ ζ ∈ GaoStageSet ξ (γ + 1) ∧
        ordinalProjection ξ ζ ∉ GaoStageSet ξ γ := by
  have hpow : Ordinal.omega0 ^ γ ≤ Ordinal.omega0 ^ ξ :=
    Ordinal.opow_le_opow_right Ordinal.omega0_pos hγ
  let ζ : GaoIndex ξ := ⟨Ordinal.omega0 ^ γ,
    hpow.trans le_self_add⟩
  have hcnf : Ordinal.CNF Ordinal.omega0 ζ.1 = [(γ, 1)] := by
    dsimp [ζ]
    simpa using Ordinal.CNF.opow_mul_add (b := Ordinal.omega0)
      (e := γ) (x := 1) (y := 0) Ordinal.one_lt_omega0 one_ne_zero
      Ordinal.one_lt_omega0 (Ordinal.opow_pos γ Ordinal.omega0_pos)
  have hleast : leastCNFExponent ζ.1 = γ := by
    simp [leastCNFExponent, hcnf]
  refine ⟨ζ, ?_, ?_⟩
  · refine ⟨ζ, ⟨hpow, ?_⟩, ?_⟩
    · rw [hleast]
      rw [Ordinal.lt_add_iff one_ne_zero]
      exact ⟨0, zero_lt_one, by simp⟩
    · have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
        intro x
        simp only [ordinalProjection]
        split_ifs <;> norm_num
      rw [abs_of_nonneg hnonneg]
  · rintro ⟨η, hη, hdom⟩
    have hnonneg : 0 ≤ ordinalProjection ξ ζ := by
      intro x
      simp only [ordinalProjection]
      split_ifs <;> norm_num
    rw [abs_of_nonneg hnonneg] at hdom
    have hrel := (ordinalProjection_le_iff ξ ζ η).mp hdom
    rcases hrel with heq | hrel
    · have : leastCNFExponent η.1 = γ := by
        rw [← heq]
        exact hleast
      exact (lt_irrefl γ) (by simpa only [this] using hη.2)
    · rcases hrel with ⟨pre, tail, β, c, δ, d, hζcnf, hηcnf, hstep⟩
      rw [hcnf] at hζcnf
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨hhead, rfl⟩
          have hβ : β = γ := congrArg Prod.fst hhead.symm
          have hc : c = 1 := congrArg Prod.snd hhead.symm
          subst β
          subst c
          have hγδ : γ ≤ δ := by
            rcases hstep with ⟨rfl, _⟩ | ⟨hγδ, _⟩
            · exact le_rfl
            · exact hγδ.le
          have hleastη : leastCNFExponent η.1 = δ := by
            simp [leastCNFExponent, hηcnf]
          exact (not_lt_of_ge (hleastη.symm ▸ hγδ)) hη.2
      | cons p pre =>
          simp only [List.cons_append, List.cons.injEq] at hζcnf
          rcases hζcnf with ⟨rfl, hfalse⟩
          simp at hfalse

end OrdinalConstruction

end OrderClosures
