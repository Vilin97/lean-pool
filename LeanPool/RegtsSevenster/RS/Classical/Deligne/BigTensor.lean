/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# The tensor product of an arbitrary family of monoid objects

Infrastructure for Deligne's 2.11: in a braided monoidal category
`D` with filtered colimits, an arbitrary family `B : ι → D` of
(commutative) monoid objects has a tensor product, defined as the
filtered colimit of the tensor products of its finite
subfamilies.

The index type carries a linear order, which fixes the ordering
of the tensor slots: the finite sub-tensor-product over
`s : Finset ι` is the fold of `B` over the sorted list of `s`.
For `s ⊆ t` there is an insertion morphism which places the unit
of the missing factors into the extra slots; these are the
transition maps of a `Finset ι`-shaped diagram, and the big
tensor product is its colimit.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

/- `open MonObj` would activate the scoped notation `ι` for
`GrpObj.inv`, clashing with our index type; we redeclare the unit
and multiplication notations locally instead. -/
local notation "η[" M "]" => MonObj.one (X := M)
local notation "μ[" M "]" => MonObj.mul (X := M)

universe v u

variable {ι : Type v}
variable {D : Type u}

/-! ## Finite tensor products -/

/-- The tensor product of the factors `B i` over a list of
indices, folded to the right with the unit object as seed. -/
def listTensor [Category.{v} D] [MonoidalCategory D]
    (B : ι → D) : List ι → D
  | [] => 𝟙_ D
  | i :: l => B i ⊗ listTensor B l

@[simp] lemma listTensor_nil [Category.{v} D] [MonoidalCategory D]
    (B : ι → D) : listTensor B [] = 𝟙_ D := rfl

@[simp] lemma listTensor_cons [Category.{v} D] [MonoidalCategory D]
    (B : ι → D) (i : ι) (l : List ι) :
    listTensor B (i :: l) = B i ⊗ listTensor B l := rfl

section LinearOrder

/-- The tensor product of the factors `B i` over a finite set of
indices, in the slot order given by the linear order on `ι`. -/
def finTensor [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    (B : ι → D) (s : Finset ι) : D :=
  listTensor B (s.sort (· ≤ ·))

@[simp] lemma finTensor_empty
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    (B : ι → D) : finTensor B ∅ = 𝟙_ D := by
  simp [finTensor]

@[simp] lemma finTensor_singleton
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    (B : ι → D) (i : ι) :
    finTensor B {i} = B i ⊗ 𝟙_ D := by
  simp [finTensor]

end LinearOrder

section Monoid

/-- The finite tensor products of a family of monoid objects are
monoid objects, by folding the binary braided instance. -/
instance listTensorMon [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (B : ι → D) [∀ i, MonObj (B i)] :
    ∀ l : List ι, MonObj (listTensor B l)
  | [] => inferInstanceAs (MonObj (𝟙_ D))
  | i :: l =>
    letI := listTensorMon B l
    inferInstanceAs (MonObj (B i ⊗ listTensor B l))

instance finTensorMon [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [LinearOrder ι] (B : ι → D) [∀ i, MonObj (B i)]
    (s : Finset ι) :
    MonObj (finTensor B s) :=
  inferInstanceAs (MonObj (listTensor B (s.sort (· ≤ ·))))

end Monoid

section CommMonoid

/-- Finite tensor products of commutative monoid objects are
commutative, by folding the binary instance of the symmetric
category. -/
instance listTensorCommMon
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    (B : ι → D) [∀ i, MonObj (B i)]
    [∀ i, IsCommMonObj (B i)] :
    ∀ l : List ι, IsCommMonObj (listTensor B l)
  | [] => inferInstanceAs (IsCommMonObj (𝟙_ D))
  | i :: l =>
    letI := listTensorCommMon B l
    inferInstanceAs (IsCommMonObj (B i ⊗ listTensor B l))

instance finTensorCommMon
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [∀ i, IsCommMonObj (B i)] (s : Finset ι) :
    IsCommMonObj (finTensor B s) :=
  inferInstanceAs (IsCommMonObj (listTensor B (s.sort (· ≤ ·))))

end CommMonoid

/-! ## Insertion of units -/

/-- The unit `η[M] : 𝟙_ D ⟶ M` is a morphism of monoid objects
from the trivial monoid. -/
instance isMonHom_one [Category.{v} D] [MonoidalCategory D]
    (M : D) [MonObj M] : IsMonHom η[M] where
  one_hom := by simp
  mul_hom := by simp [unitors_equal]

/-- Insertion of the unit of the monoid `M` in the front slot. -/
def unitIncl [Category.{v} D] [MonoidalCategory D]
    (M X : D) [MonObj M] : X ⟶ M ⊗ X :=
  (λ_ X).inv ≫ η[M] ▷ X

lemma unitIncl_eq_tensorHom [Category.{v} D] [MonoidalCategory D]
    (M X : D) [MonObj M] :
    unitIncl M X = (λ_ X).inv ≫ (η[M] ⊗ₘ 𝟙 X) := by
  simp [unitIncl]

@[reassoc]
lemma unitIncl_naturality [Category.{v} D] [MonoidalCategory D]
    (M : D) [MonObj M] {X Y : D} (f : X ⟶ Y) :
    f ≫ unitIncl M Y = unitIncl M X ≫ (M ◁ f) := by
  simp only [unitIncl, Category.assoc]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange]

instance isMonHom_unitIncl [Category.{v} D] [MonoidalCategory D]
    [BraidedCategory D] (M X : D) [MonObj M]
    [MonObj X] : IsMonHom (unitIncl M X) := by
  rw [unitIncl_eq_tensorHom]
  infer_instance

/-! ## Inclusions of finite tensor products

The inclusion of a sub-tensor-product is defined at the level of
lists: for a Boolean predicate `p`, the tensor product over
`l.filter p` maps into the tensor product over `l` by inserting
the unit of each factor whose index fails `p`. -/

section Insertion

/-- Insertion morphism from the tensor product over the filtered
list into the tensor product over the full list, placing units in
the slots dropped by the filter.

Convention: all stated morphisms have `listTensor`-form
endpoints; the tensor-shaped intermediate objects appear only
between explicit `eqToHom` guards, so that every composition in
the subsequent lemmas is well typed on the nose. -/
def inclFilter
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) :
    ∀ l : List ι, listTensor B (l.filter p) ⟶ listTensor B l
  | [] => 𝟙 _
  | i :: l =>
    if h : p i then
      eqToHom (show listTensor B ((i :: l).filter p) =
          B i ⊗ listTensor B (l.filter p) by
        rw [List.filter_cons_of_pos h, listTensor_cons]) ≫
        (B i ◁ inclFilter B p l) ≫
        eqToHom (listTensor_cons B i l).symm
    else
      eqToHom (show listTensor B ((i :: l).filter p) =
          listTensor B (l.filter p) by
        rw [List.filter_cons_of_neg (by simp [h])]) ≫
        inclFilter B p l ≫ unitIncl (B i) (listTensor B l) ≫
        eqToHom (listTensor_cons B i l).symm

@[simp] lemma inclFilter_nil
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) :
    inclFilter B p [] = 𝟙 (𝟙_ D) := rfl

lemma inclFilter_cons_pos
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) {i : ι} (l : List ι)
    (h : p i) :
    inclFilter B p (i :: l) =
      eqToHom (show listTensor B ((i :: l).filter p) =
          B i ⊗ listTensor B (l.filter p) by
        rw [List.filter_cons_of_pos h, listTensor_cons]) ≫
        (B i ◁ inclFilter B p l) ≫
        eqToHom (listTensor_cons B i l).symm := by
  rw [inclFilter, dif_pos h]

lemma inclFilter_cons_neg
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) {i : ι} (l : List ι)
    (h : ¬ p i) :
    inclFilter B p (i :: l) =
      eqToHom (show listTensor B ((i :: l).filter p) =
          listTensor B (l.filter p) by
        rw [List.filter_cons_of_neg (by simp [h])]) ≫
        inclFilter B p l ≫ unitIncl (B i) (listTensor B l) ≫
        eqToHom (listTensor_cons B i l).symm := by
  rw [inclFilter, dif_neg h]

/-- Equal index lists give equal (conjugated) insertions. -/
lemma inclFilter_congr
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) {l₁ l₂ : List ι} (h : l₁ = l₂) :
    inclFilter B p l₁ =
      eqToHom (by rw [h]) ≫ inclFilter B p l₂ ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- Equal predicates give equal (transported) insertions. -/
lemma inclFilter_congr_pred
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    {p q : ι → Bool} (h : p = q)
    (l : List ι) :
    inclFilter B p l = eqToHom (by rw [h]) ≫ inclFilter B q l := by
  subst h
  simp

/-- Transporting along an equality of index lists is a morphism
of monoid objects. -/
lemma isMonHom_eqToHom
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [BraidedCategory D] {l₁ l₂ : List ι}
    (h : l₁ = l₂) (q : listTensor B l₁ = listTensor B l₂) :
    IsMonHom (eqToHom q) := by
  subst h
  simp only [eqToHom_refl]
  infer_instance

/-- The insertions are morphisms of monoid objects. -/
instance isMonHom_inclFilter
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [BraidedCategory D] (p : ι → Bool) :
    ∀ l : List ι, IsMonHom (inclFilter B p l)
  | [] => inferInstanceAs (IsMonHom (𝟙 (𝟙_ D)))
  | i :: l => by
    haveI := isMonHom_inclFilter B p l
    haveI : IsMonHom (eqToHom (listTensor_cons B i l).symm) :=
      isMonHom_eqToHom B (l₁ := i :: l) (l₂ := i :: l) rfl
        (listTensor_cons B i l).symm
    by_cases h : p i
    · rw [inclFilter_cons_pos B p l h]
      haveI : IsMonHom (eqToHom
          (show listTensor B ((i :: l).filter p) =
            B i ⊗ listTensor B (l.filter p) by
          rw [List.filter_cons_of_pos h, listTensor_cons])) :=
        isMonHom_eqToHom B (List.filter_cons_of_pos (p := p) h)
          (by rw [List.filter_cons_of_pos h] :
            listTensor B ((i :: l).filter p) =
              listTensor B (i :: l.filter p))
      infer_instance
    · rw [inclFilter_cons_neg B p l h]
      haveI : IsMonHom (eqToHom
          (show listTensor B ((i :: l).filter p) =
            listTensor B (l.filter p) by
          rw [List.filter_cons_of_neg (by simp [h])])) :=
        isMonHom_eqToHom B (List.filter_cons_of_neg
          (by simp [h] : ¬ p i = true) (p := p))
          (by rw [List.filter_cons_of_neg (by simp [h])] :
            listTensor B ((i :: l).filter p) = listTensor B (l.filter p))
      infer_instance

/-- Inserting nothing: if every index passes the filter, the
insertion is the transport of the identity. -/
lemma inclFilter_of_forall
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p : ι → Bool) :
    ∀ (l : List ι) (h : ∀ i ∈ l, p i),
      inclFilter B p l = eqToHom (by rw [List.filter_eq_self.mpr h])
  | [], _ => by simp
  | i :: l, h => by
    rw [inclFilter_cons_pos B p l (h i (by simp)),
      inclFilter_of_forall B p l (fun j hj => h j (by simp [hj]))]
    simp

/-- The composition law for insertions: inserting the units of
`l.filter q` past `p` and then those of `l` past `q` is the
insertion past the conjunction.  This is the coherence heart of
the transition maps of the big tensor product. -/
lemma inclFilter_inclFilter
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (p q : ι → Bool) :
    ∀ l : List ι,
      inclFilter B p (l.filter q) ≫ inclFilter B q l =
        eqToHom (by rw [List.filter_filter]) ≫
          inclFilter B (fun i => p i && q i) l
  | [] => by simp
  | i :: l => by
    have IH := inclFilter_inclFilter B p q l
    by_cases hq : q i
    · have hfq : (i :: l).filter q = i :: l.filter q :=
        List.filter_cons_of_pos hq
      by_cases hp : p i
      · rw [inclFilter_congr B p hfq,
          inclFilter_cons_pos B p (l.filter q) hp,
          inclFilter_cons_pos B q l hq,
          inclFilter_cons_pos B (fun j => p j && q j) l
            (by simp [hp, hq])]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        rw [← MonoidalCategory.whiskerLeft_comp_assoc, IH]
        simp
      · rw [inclFilter_congr B p hfq,
          inclFilter_cons_neg B p (l.filter q) hp,
          inclFilter_cons_pos B q l hq,
          inclFilter_cons_neg B (fun j => p j && q j) l
            (by simp [hp])]
        simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
          Category.id_comp]
        slice_lhs 3 4 => rw [← unitIncl_naturality]
        slice_lhs 2 3 => rw [IH]
        simp
    · have hfq : (i :: l).filter q = l.filter q :=
        List.filter_cons_of_neg (by simp [hq])
      rw [inclFilter_congr B p hfq,
        inclFilter_cons_neg B q l (by simp [hq]),
        inclFilter_cons_neg B (fun j => p j && q j) l
          (by simp [hq])]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp]
      slice_lhs 2 3 => rw [IH]
      simp

/-! Bridging lemmas for the units of the fold monoids. -/

/-- On a vanishing index list, the unit of the fold monoid is the
canonical identification with the monoidal unit. -/
lemma listTensor_one_eq
    [Category.{v} D] [MonoidalCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [BraidedCategory D] {l : List ι} (h : l = []) :
    η[listTensor B l] =
      eqToHom (show 𝟙_ D = listTensor B l by rw [h, listTensor_nil]) := by
  subst h
  rfl

end Insertion

/-! ## Inclusions between finite sub-tensor-products -/

section FinsetIncl

/-- Sorting commutes with restriction: the sorted list of a
subset of `t` is the filtering of the sorted list of `t`. -/
lemma sort_filter_of_subset [LinearOrder ι]
    {s t : Finset ι} (h : s ⊆ t) :
    (t.sort (· ≤ ·)).filter (fun i => decide (i ∈ s)) =
      s.sort (· ≤ ·) := by
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact (Finset.pairwise_sort t _).sublist List.filter_sublist
  · exact Finset.pairwise_sort s _
  · rw [← Multiset.coe_eq_coe, ← Multiset.filter_coe, Finset.sort_eq,
      Finset.sort_eq, ← Finset.filter_val, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr h]

/-- The inclusion of the finite sub-tensor-product over `s ⊆ t`,
inserting the units of the factors missing from `s`. -/
def finTensorIncl
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)]
    {s t : Finset ι} (h : s ⊆ t) :
    finTensor B s ⟶ finTensor B t :=
  eqToHom (show finTensor B s =
      listTensor B ((t.sort (· ≤ ·)).filter fun i => decide (i ∈ s)) by
    rw [sort_filter_of_subset h]; rfl) ≫
  inclFilter B (fun i => decide (i ∈ s)) (t.sort (· ≤ ·)) ≫
  eqToHom (show listTensor B (t.sort (· ≤ ·)) = finTensor B t from rfl)

@[simp] lemma finTensorIncl_refl
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)]
    (s : Finset ι) :
    finTensorIncl B (subset_refl s) = 𝟙 (finTensor B s) := by
  rw [finTensorIncl, inclFilter_of_forall B _ _
    (fun i hi => by simpa using hi)]
  simp

/-- Functoriality of the inclusions of sub-tensor-products. -/
@[reassoc]
lemma finTensorIncl_trans
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)]
    {s t u : Finset ι} (hst : s ⊆ t)
    (htu : t ⊆ u) :
    finTensorIncl B hst ≫ finTensorIncl B htu =
      finTensorIncl B (hst.trans htu) := by
  rw [finTensorIncl, finTensorIncl, finTensorIncl,
    inclFilter_congr B (fun i => decide (i ∈ s))
      (sort_filter_of_subset htu).symm]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  slice_lhs 2 3 => rw [inclFilter_inclFilter]
  have hpq : (fun i => decide (i ∈ s) && decide (i ∈ t)) =
      (fun i => decide (i ∈ s)) := funext fun i => by
    by_cases hi : i ∈ s
    · simp [hi, hst hi]
    · simp [hi]
  rw [inclFilter_congr_pred B hpq (u.sort (· ≤ ·))]
  simp

/-- The inclusions of sub-tensor-products are morphisms of monoid
objects. -/
instance isMonHom_finTensorIncl
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)]
    [BraidedCategory D] {s t : Finset ι}
    (h : s ⊆ t) : IsMonHom (finTensorIncl B h) := by
  rw [finTensorIncl]
  haveI : IsMonHom (eqToHom (show finTensor B s =
      listTensor B ((t.sort (· ≤ ·)).filter fun i => decide (i ∈ s)) by
    rw [sort_filter_of_subset h]; rfl)) :=
    isMonHom_eqToHom B (l₁ := s.sort (· ≤ ·))
      (l₂ := (t.sort (· ≤ ·)).filter fun i => decide (i ∈ s))
      (sort_filter_of_subset h).symm
      (by rw [sort_filter_of_subset h])
  haveI : IsMonHom (eqToHom
      (show listTensor B (t.sort (· ≤ ·)) = finTensor B t from rfl)) :=
    isMonHom_eqToHom B (l₁ := t.sort (· ≤ ·)) (l₂ := t.sort (· ≤ ·))
      rfl rfl
  infer_instance

end FinsetIncl

/-! ## The big tensor product as a filtered colimit -/

section BigTensor

/-- The index category of finite stages is filtered: `Finset ι`
is a directed order with unions as upper bounds. -/
example : IsFiltered (Finset ι) := inferInstance

/-- The `Finset ι`-shaped diagram of finite sub-tensor-products,
with the unit insertions as transition maps. -/
@[simps]
def finTensorDiagram
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] : Finset ι ⥤ D where
  obj s := finTensor B s
  map f := finTensorIncl B (leOfHom f)
  map_id s := finTensorIncl_refl B s
  map_comp f g :=
    (finTensorIncl_trans B (leOfHom f) (leOfHom g)).symm

/-- The tensor product of the whole family `B`, as the filtered
colimit of its finite sub-tensor-products. -/
noncomputable def bigTensor
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D] :
    D := colimit (finTensorDiagram B)

/-- The stage inclusion of a finite sub-tensor-product into the
big tensor product. -/
noncomputable def bigTensorStage
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D]
    (s : Finset ι) :
    finTensor B s ⟶ bigTensor B :=
  colimit.ι (finTensorDiagram B) s

/-- Stage inclusions are compatible with the insertions. -/
@[reassoc (attr := simp)]
lemma finTensorIncl_bigTensorStage
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D]
    {s t : Finset ι} (h : s ⊆ t) :
    finTensorIncl B h ≫ bigTensorStage B t = bigTensorStage B s :=
  colimit.w (finTensorDiagram B) (homOfLE h)

/-- The unit of the big tensor product: the empty stage. -/
noncomputable def bigTensorUnit
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D] :
    𝟙_ D ⟶ bigTensor B :=
  eqToHom (finTensor_empty B).symm ≫ bigTensorStage B ∅

/-- The inclusion of a single factor, through the stage at the
singleton. -/
noncomputable def bigTensorOf
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D]
    (i : ι) : B i ⟶ bigTensor B :=
  (ρ_ (B i)).inv ≫ eqToHom (finTensor_singleton B i).symm ≫
    bigTensorStage B {i}

end BigTensor

/-! ## The unit against the stages -/

section StageMonoid

lemma finTensor_one_def [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (s : Finset ι) :
    η[finTensor B s] = η[listTensor B (s.sort (· ≤ ·))] := rfl

/-- The unit of the empty stage is the canonical identification
with the monoidal unit. -/
lemma finTensor_one_empty [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)] :
    η[finTensor B ∅] = eqToHom (finTensor_empty B).symm := by
  rw [finTensor_one_def,
    listTensor_one_eq B (Finset.sort_empty (fun a b => a ≤ b))]
  rfl

/-- The unit of the big tensor product is reached from the unit
of any finite stage. -/
lemma bigTensorUnit_stage [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    (s : Finset ι) :
    η[finTensor B s] ≫ bigTensorStage B s = bigTensorUnit B := by
  rw [← (isMonHom_finTensorIncl B (Finset.empty_subset s)).one_hom,
    Category.assoc, finTensorIncl_bigTensorStage, finTensor_one_empty,
    bigTensorUnit]

end StageMonoid

/-! ## Merge maps

The multiplication of the big tensor product is presented on the
finite stages by the merge maps: include both stages into their
union, then multiply there.  This section provides the merge maps
together with their coherence squares. -/

section Merge

/-- The inclusion of the empty stage is the unit. -/
lemma finTensorIncl_empty [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (u : Finset ι) :
    finTensorIncl B (Finset.empty_subset u) =
      eqToHom (finTensor_empty B) ≫ η[finTensor B u] := by
  rw [← (isMonHom_finTensorIncl B (Finset.empty_subset u)).one_hom,
    finTensor_one_empty]
  simp

/-- The merge map of two finite stages: include both into the
union stage and multiply there. -/
def finTensorMul [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (s t : Finset ι) :
    finTensor B s ⊗ finTensor B t ⟶ finTensor B (s ∪ t) :=
  (finTensorIncl B Finset.subset_union_left ⊗ₘ
    finTensorIncl B Finset.subset_union_right) ≫ μ[finTensor B (s ∪ t)]

/-- Include-then-multiply is independent of the receiving stage:
merging and then including into any common superset is inclusion
into the superset followed by its multiplication. -/
lemma finTensorMul_incl [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    {s t v : Finset ι} (hs : s ⊆ v) (ht : t ⊆ v)
    (huv : s ∪ t ⊆ v) :
    finTensorMul B s t ≫ finTensorIncl B huv =
      (finTensorIncl B hs ⊗ₘ finTensorIncl B ht) ≫
        μ[finTensor B v] := by
  rw [finTensorMul, Category.assoc,
    (isMonHom_finTensorIncl B huv).mul_hom, ← Category.assoc,
    tensorHom_comp_tensorHom, finTensorIncl_trans, finTensorIncl_trans]

/-- Naturality of the merge maps in both stages. -/
@[reassoc]
lemma finTensorMul_natural [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    {s s' t t' : Finset ι} (hs : s ⊆ s')
    (ht : t ⊆ t') :
    (finTensorIncl B hs ⊗ₘ finTensorIncl B ht) ≫
        finTensorMul B s' t' =
      finTensorMul B s t ≫
        finTensorIncl B (Finset.union_subset_union hs ht) := by
  rw [finTensorMul_incl B (hs.trans Finset.subset_union_left)
    (ht.trans Finset.subset_union_right), finTensorMul,
    ← Category.assoc, tensorHom_comp_tensorHom, finTensorIncl_trans,
    finTensorIncl_trans]

/-- The merge maps composed with the stage inclusions form a
cocone in each variable: the square defining the multiplication
of the big tensor product commutes. -/
lemma finTensorMul_stage [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    {s s' t t' : Finset ι} (hs : s ⊆ s')
    (ht : t ⊆ t') :
    (finTensorIncl B hs ⊗ₘ finTensorIncl B ht) ≫
        finTensorMul B s' t' ≫ bigTensorStage B (s' ∪ t') =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  rw [← Category.assoc, finTensorMul_natural, Category.assoc,
    finTensorIncl_bigTensorStage]

/-- The stage identification along an equality of finite sets is
an inclusion. -/
lemma eqToHom_eq_finTensorIncl
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)]
    {s t : Finset ι} (e : s = t)
    (h : s ⊆ t) :
    eqToHom (show finTensor B s = finTensor B t by rw [e]) =
      finTensorIncl B h := by
  subst e
  simp

/-- Unit square: merging with the empty stage on the left is the
left unitor followed by the inclusion. -/
lemma finTensorMul_empty_left
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (t : Finset ι) :
    (eqToHom (finTensor_empty B).symm ▷ finTensor B t) ≫
        finTensorMul B ∅ t =
      (λ_ (finTensor B t)).hom ≫
        finTensorIncl B Finset.subset_union_right := by
  rw [finTensorMul, finTensorIncl_empty, ← Category.assoc,
    ← tensorHom_id, tensorHom_comp_tensorHom]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [MonObj.one_mul_hom]

/-- Unit square: merging with the empty stage on the right is the
right unitor followed by the inclusion. -/
lemma finTensorMul_empty_right
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (t : Finset ι) :
    (finTensor B t ◁ eqToHom (finTensor_empty B).symm) ≫
        finTensorMul B t ∅ =
      (ρ_ (finTensor B t)).hom ≫
        finTensorIncl B Finset.subset_union_left := by
  rw [finTensorMul, finTensorIncl_empty, ← Category.assoc,
    ← id_tensorHom, tensorHom_comp_tensorHom]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [MonObj.mul_one_hom]

/-- Three-fold multiplication of a monoid object is associative,
in the folded form used by the merge maps. -/
lemma tensor_mul_assoc [Category.{v} D] [MonoidalCategory D]
    {M X Y Z : D} [MonObj M] (a : X ⟶ M)
    (b : Y ⟶ M) (c : Z ⟶ M) :
    (((a ⊗ₘ b) ≫ μ[M]) ⊗ₘ c) ≫ μ[M] =
      (α_ X Y Z).hom ≫ (a ⊗ₘ ((b ⊗ₘ c) ≫ μ[M])) ≫ μ[M] := by
  rw [← Category.comp_id c, ← tensorHom_comp_tensorHom,
    Category.assoc, Category.comp_id, tensorHom_id,
    MonObj.mul_assoc, ← Category.assoc, associator_naturality,
    Category.assoc, ← id_tensorHom,
    tensorHom_comp_tensorHom_assoc, Category.comp_id]

/-- Definitional unfolding of the merge map, for targeted
rewriting. -/
lemma finTensorMul_def [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (s t : Finset ι) :
    finTensorMul B s t =
      (finTensorIncl B Finset.subset_union_left ⊗ₘ
        finTensorIncl B Finset.subset_union_right) ≫
        μ[finTensor B (s ∪ t)] := rfl

/-- Associativity square of the merge maps. -/
@[reassoc]
lemma finTensorMul_assoc [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    (s t u : Finset ι) :
    (finTensorMul B s t ▷ finTensor B u) ≫ finTensorMul B (s ∪ t) u =
      (α_ (finTensor B s) (finTensor B t) (finTensor B u)).hom ≫
        (finTensor B s ◁ finTensorMul B t u) ≫
        finTensorMul B s (t ∪ u) ≫
        eqToHom (show finTensor B (s ∪ (t ∪ u)) =
            finTensor B (s ∪ t ∪ u) by
          rw [Finset.union_assoc]) := by
  conv_rhs =>
    rw [eqToHom_eq_finTensorIncl B (Finset.union_assoc s t u).symm
        (le_of_eq (Finset.union_assoc s t u).symm),
      finTensorMul_incl B
        (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.union_subset
          (Finset.subset_union_right.trans Finset.subset_union_left)
          Finset.subset_union_right),
      ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
      Category.id_comp,
      finTensorMul_incl B
        (Finset.subset_union_right.trans Finset.subset_union_left)
        Finset.subset_union_right]
  conv_lhs =>
    rw [finTensorMul_def B (s ∪ t) u, ← tensorHom_id,
      tensorHom_comp_tensorHom_assoc, Category.id_comp,
      finTensorMul_incl B
        (Finset.subset_union_left.trans Finset.subset_union_left)
        (Finset.subset_union_right.trans Finset.subset_union_left)]
  rw [tensor_mul_assoc]

end Merge

/-! ## The multiplication of the big tensor product

With tensoring preserving `Finset ι`-colimits, `bigTensor B ⊗ X`
and `X ⊗ bigTensor B` are colimits of the corresponding stage
diagrams; maps out of them are determined by the stages, and the
merge maps assemble into the multiplication. -/

section BigTensorMul

/-- Maps out of `bigTensor B ⊗ X` are determined by their
restrictions to the stages. -/
lemma bigTensor_tensorRight_hom_ext
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    {X Z : D}
    {f g : bigTensor B ⊗ X ⟶ Z}
    (w : ∀ s, (bigTensorStage B s ▷ X) ≫ f =
      (bigTensorStage B s ▷ X) ≫ g) : f = g := by
  apply (cancel_epi
    (preservesColimitIso (tensorRight X) (finTensorDiagram B)).inv).mp
  apply colimit.hom_ext
  intro s
  rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
  exact w s

/-- Maps out of `X ⊗ bigTensor B` are determined by their
restrictions to the stages. -/
lemma tensorLeft_bigTensor_hom_ext
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι] (B : ι → D)
    [∀ i, MonObj (B i)] [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    {X Z : D}
    {f g : X ⊗ bigTensor B ⟶ Z}
    (w : ∀ t, (X ◁ bigTensorStage B t) ≫ f =
      (X ◁ bigTensorStage B t) ≫ g) : f = g := by
  apply (cancel_epi
    (preservesColimitIso (tensorLeft X) (finTensorDiagram B)).inv).mp
  apply colimit.hom_ext
  intro t
  rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
  exact w t

/-- Left compatibility of the merge-then-stage maps. -/
@[reassoc]
lemma finTensorMul_stage_left
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    {s s' t : Finset ι} (hs : s ⊆ s') :
    (finTensorIncl B hs ▷ finTensor B t) ≫ finTensorMul B s' t ≫
        bigTensorStage B (s' ∪ t) =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  have h := finTensorMul_stage B hs (subset_refl t)
  rwa [finTensorIncl_refl, tensorHom_id] at h

/-- Right compatibility of the merge-then-stage maps. -/
@[reassoc]
lemma finTensorMul_stage_right
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    {s t t' : Finset ι} (ht : t ⊆ t') :
    (finTensor B s ◁ finTensorIncl B ht) ≫ finTensorMul B s t' ≫
        bigTensorStage B (s ∪ t') =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  have h := finTensorMul_stage B (subset_refl s) ht
  rwa [finTensorIncl_refl, id_tensorHom] at h

/-- The merge maps into the big tensor product form a cocone on
the stage diagram tensored with a fixed finite stage. -/
noncomputable def bigTensorMulCocone
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    (t : Finset ι) :
    Cocone (finTensorDiagram B ⋙ tensorRight (finTensor B t)) where
  pt := bigTensor B
  ι :=
    { app := fun s => finTensorMul B s t ≫ bigTensorStage B (s ∪ t)
      naturality := fun {s s'} f => by
        show (finTensorIncl B (leOfHom f) ▷ finTensor B t) ≫
            (finTensorMul B s' t ≫ bigTensorStage B (s' ∪ t)) =
          (finTensorMul B s t ≫ bigTensorStage B (s ∪ t)) ≫
            𝟙 (bigTensor B)
        rw [Category.comp_id]
        exact finTensorMul_stage_left B (leOfHom f) }

/-- Multiplication of the big tensor product against a fixed
finite stage. -/
noncomputable def bigTensorMulStage
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (t : Finset ι) :
    bigTensor B ⊗ finTensor B t ⟶ bigTensor B :=
  ((preservesColimitIso (tensorRight (finTensor B t))
      (finTensorDiagram B)).hom ≫
    colimit.desc _ (bigTensorMulCocone B t) :
    (tensorRight (finTensor B t)).obj (colimit (finTensorDiagram B)) ⟶
      bigTensor B)

/-- On a stage, the partial multiplication is merge-then-stage. -/
@[reassoc]
lemma stage_bigTensorMulStage
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s t : Finset ι) :
    (bigTensorStage B s ▷ finTensor B t) ≫ bigTensorMulStage B t =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  show (tensorRight (finTensor B t)).map
      (colimit.ι (finTensorDiagram B) s) ≫ bigTensorMulStage B t =
    finTensorMul B s t ≫ bigTensorStage B (s ∪ t)
  rw [bigTensorMulStage, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (bigTensorMulCocone B t) s

/-- The partial multiplications are natural in the stage. -/
@[reassoc]
lemma bigTensorMulStage_natural
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    {t t' : Finset ι} (ht : t ⊆ t') :
    (bigTensor B ◁ finTensorIncl B ht) ≫ bigTensorMulStage B t' =
      bigTensorMulStage B t := by
  apply bigTensor_tensorRight_hom_ext B
  intro s
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    stage_bigTensorMulStage, stage_bigTensorMulStage]
  exact finTensorMul_stage_right B ht

/-- The partial multiplications form a cocone on the stage
diagram tensored on the left with the big tensor product. -/
noncomputable def bigTensorMulTotalCocone
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    Cocone (finTensorDiagram B ⋙ tensorLeft (bigTensor B)) where
  pt := bigTensor B
  ι :=
    { app := fun t => bigTensorMulStage B t
      naturality := fun {t t'} f => by
        show (bigTensor B ◁ finTensorIncl B (leOfHom f)) ≫
            bigTensorMulStage B t' =
          bigTensorMulStage B t ≫ 𝟙 (bigTensor B)
        rw [Category.comp_id]
        exact bigTensorMulStage_natural B (leOfHom f) }

/-- The multiplication of the big tensor product. -/
noncomputable def bigTensorMul
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    bigTensor B ⊗ bigTensor B ⟶ bigTensor B :=
  ((preservesColimitIso (tensorLeft (bigTensor B))
      (finTensorDiagram B)).hom ≫
    colimit.desc _ (bigTensorMulTotalCocone B) :
    (tensorLeft (bigTensor B)).obj (colimit (finTensorDiagram B)) ⟶
      bigTensor B)

/-- On a stage in the second variable, the multiplication is the
partial multiplication. -/
@[reassoc]
lemma stage_bigTensorMul_right
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (t : Finset ι) :
    (bigTensor B ◁ bigTensorStage B t) ≫ bigTensorMul B =
      bigTensorMulStage B t := by
  show (tensorLeft (bigTensor B)).map
      (colimit.ι (finTensorDiagram B) t) ≫ bigTensorMul B =
    bigTensorMulStage B t
  rw [bigTensorMul, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (bigTensorMulTotalCocone B) t

/-- The multiplication restricted to a pair of stages is the
merge map followed by the union stage: the presentation of the
multiplication over pairs of finite stages. -/
@[reassoc]
lemma stage_bigTensorMul [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s t : Finset ι) :
    (bigTensorStage B s ⊗ₘ bigTensorStage B t) ≫ bigTensorMul B =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  rw [tensorHom_def, Category.assoc, stage_bigTensorMul_right,
    stage_bigTensorMulStage]

/-- Sandwich extension: maps out of `X ⊗ (bigTensor B ⊗ Y)` are
determined by the stages in the middle slot. -/
lemma bigTensor_sandwich_hom_ext
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (X Y : D) {Z : D}
    {f g : X ⊗ (bigTensor B ⊗ Y) ⟶ Z}
    (w : ∀ t, (X ◁ bigTensorStage B t ▷ Y) ≫ f =
      (X ◁ bigTensorStage B t ▷ Y) ≫ g) : f = g := by
  apply (cancel_epi (preservesColimitIso
    (tensorRight Y ⋙ tensorLeft X) (finTensorDiagram B)).inv).mp
  apply colimit.hom_ext
  intro t
  rw [ι_preservesColimitIso_inv_assoc, ι_preservesColimitIso_inv_assoc]
  exact w t

/-- Maps out of `bigTensor B ⊗ bigTensor B` are determined by
pairs of stages. -/
lemma bigTensor_pair_hom_ext
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    {Z : D}
    {f g : bigTensor B ⊗ bigTensor B ⟶ Z}
    (w : ∀ s t, (bigTensorStage B s ⊗ₘ bigTensorStage B t) ≫ f =
      (bigTensorStage B s ⊗ₘ bigTensorStage B t) ≫ g) : f = g := by
  apply tensorLeft_bigTensor_hom_ext B
  intro t
  apply bigTensor_tensorRight_hom_ext B
  intro s
  rw [← Category.assoc, ← Category.assoc,
    show bigTensorStage B s ▷ finTensor B t ≫
        bigTensor B ◁ bigTensorStage B t =
      bigTensorStage B s ⊗ₘ bigTensorStage B t from
        (tensorHom_def _ _).symm]
  exact w s t

/-- The merge maps against a fixed first stage form a cocone. -/
noncomputable def bigTensorMulLCocone
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    (s : Finset ι) :
    Cocone (finTensorDiagram B ⋙ tensorLeft (finTensor B s)) where
  pt := bigTensor B
  ι :=
    { app := fun t => finTensorMul B s t ≫ bigTensorStage B (s ∪ t)
      naturality := fun {t t'} f => by
        show (finTensor B s ◁ finTensorIncl B (leOfHom f)) ≫
            (finTensorMul B s t' ≫ bigTensorStage B (s ∪ t')) =
          (finTensorMul B s t ≫ bigTensorStage B (s ∪ t)) ≫
            𝟙 (bigTensor B)
        rw [Category.comp_id]
        exact finTensorMul_stage_right B (leOfHom f) }

/-- Multiplication of a fixed finite stage against the big tensor
product. -/
noncomputable def bigTensorMulStageL
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s : Finset ι) :
    finTensor B s ⊗ bigTensor B ⟶ bigTensor B :=
  ((preservesColimitIso (tensorLeft (finTensor B s))
      (finTensorDiagram B)).hom ≫
    colimit.desc _ (bigTensorMulLCocone B s) :
    (tensorLeft (finTensor B s)).obj (colimit (finTensorDiagram B)) ⟶
      bigTensor B)

/-- On a stage, the left partial multiplication is
merge-then-stage. -/
@[reassoc]
lemma stage_bigTensorMulStageL
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s t : Finset ι) :
    (finTensor B s ◁ bigTensorStage B t) ≫ bigTensorMulStageL B s =
      finTensorMul B s t ≫ bigTensorStage B (s ∪ t) := by
  show (tensorLeft (finTensor B s)).map
      (colimit.ι (finTensorDiagram B) t) ≫ bigTensorMulStageL B s =
    finTensorMul B s t ≫ bigTensorStage B (s ∪ t)
  rw [bigTensorMulStageL, ι_preservesColimitIso_hom_assoc]
  exact colimit.ι_desc (bigTensorMulLCocone B s) t

/-- On a stage in the first variable, the multiplication is the
left partial multiplication. -/
@[reassoc]
lemma stage_bigTensorMul_left
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s : Finset ι) :
    (bigTensorStage B s ▷ bigTensor B) ≫ bigTensorMul B =
      bigTensorMulStageL B s := by
  apply tensorLeft_bigTensor_hom_ext B
  intro t
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    stage_bigTensorMul_right, stage_bigTensorMulStage,
    stage_bigTensorMulStageL]

/-! ## The monoid structure on the big tensor product -/

/-- Left unit law of the big tensor product. -/
lemma bigTensor_one_mul [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    (bigTensorUnit B ▷ bigTensor B) ≫ bigTensorMul B =
      (λ_ (bigTensor B)).hom := by
  apply tensorLeft_bigTensor_hom_ext B
  intro t
  rw [← Category.assoc, whisker_exchange, Category.assoc,
    stage_bigTensorMul_right, bigTensorUnit, comp_whiskerRight,
    Category.assoc, stage_bigTensorMulStage, ← Category.assoc,
    finTensorMul_empty_left, Category.assoc,
    finTensorIncl_bigTensorStage, leftUnitor_naturality]

/-- Right unit law of the big tensor product. -/
lemma bigTensor_mul_one [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    (bigTensor B ◁ bigTensorUnit B) ≫ bigTensorMul B =
      (ρ_ (bigTensor B)).hom := by
  apply bigTensor_tensorRight_hom_ext B
  intro s
  rw [← Category.assoc, ← whisker_exchange, Category.assoc,
    stage_bigTensorMul_left, bigTensorUnit,
    MonoidalCategory.whiskerLeft_comp, Category.assoc,
    stage_bigTensorMulStageL, ← Category.assoc,
    finTensorMul_empty_right, Category.assoc,
    finTensorIncl_bigTensorStage, rightUnitor_naturality]

/-- Associativity of the big tensor product multiplication. -/
lemma bigTensor_mul_assoc [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    (bigTensorMul B ▷ bigTensor B) ≫ bigTensorMul B =
      (α_ (bigTensor B) (bigTensor B) (bigTensor B)).hom ≫
        (bigTensor B ◁ bigTensorMul B) ≫ bigTensorMul B := by
  apply tensorLeft_bigTensor_hom_ext B
  intro u
  conv_lhs =>
    rw [← Category.assoc, whisker_exchange, Category.assoc,
      stage_bigTensorMul_right]
  conv_rhs =>
    rw [associator_naturality_right_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      stage_bigTensorMul_right]
  apply (cancel_epi
    (α_ (bigTensor B) (bigTensor B) (finTensor B u)).inv).mp
  rw [Iso.inv_hom_id_assoc]
  apply bigTensor_tensorRight_hom_ext B
  intro s
  conv_lhs =>
    rw [associator_inv_naturality_left_assoc,
      ← comp_whiskerRight_assoc, stage_bigTensorMul_left]
  conv_rhs =>
    rw [← whisker_exchange_assoc, stage_bigTensorMul_left]
  apply bigTensor_sandwich_hom_ext B
  intro t
  conv_lhs =>
    rw [associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, stage_bigTensorMulStageL,
      comp_whiskerRight, Category.assoc, stage_bigTensorMulStage,
      finTensorMul_assoc_assoc, Iso.inv_hom_id_assoc,
      eqToHom_eq_finTensorIncl B (Finset.union_assoc s t u).symm
        (le_of_eq (Finset.union_assoc s t u).symm),
      finTensorIncl_bigTensorStage]
  conv_rhs =>
    rw [← MonoidalCategory.whiskerLeft_comp_assoc,
      stage_bigTensorMulStage, MonoidalCategory.whiskerLeft_comp,
      Category.assoc, stage_bigTensorMulStageL]

/-- The big tensor product of a family of monoid objects is a
monoid object: the unit is the empty stage and the multiplication
is assembled from the merge maps. -/
noncomputable instance bigTensorMon
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    MonObj (bigTensor B) where
  one := bigTensorUnit B
  mul := bigTensorMul B
  one_mul := bigTensor_one_mul B
  mul_one := bigTensor_mul_one B
  mul_assoc := bigTensor_mul_assoc B

/-- The stage inclusions are morphisms of monoid objects. -/
instance isMonHom_bigTensorStage
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (s : Finset ι) :
    IsMonHom (bigTensorStage B s) where
  one_hom := bigTensorUnit_stage B s
  mul_hom := by
    rw [show μ[bigTensor B] = bigTensorMul B from rfl,
      stage_bigTensorMul]
    conv_rhs => rw [← finTensorIncl_bigTensorStage B
      (le_of_eq (Finset.union_self s))]
    rw [← Category.assoc,
      finTensorMul_incl B (subset_refl s) (subset_refl s),
      finTensorIncl_refl, id_tensorHom_id, Category.id_comp]

/-- The single-factor inclusions are morphisms of monoid
objects. -/
instance isMonHom_bigTensorOf
    [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [BraidedCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)]
    (i : ι) :
    IsMonHom (bigTensorOf B i) := by
  rw [bigTensorOf]
  haveI : IsMonHom (eqToHom (finTensor_singleton B i).symm) :=
    isMonHom_eqToHom B (l₁ := [i])
      (l₂ := ({i} : Finset ι).sort (· ≤ ·))
      (Finset.sort_singleton (fun a b => a ≤ b) i).symm
      (by rw [Finset.sort_singleton])
  infer_instance

end BigTensorMul

/-! ## Commutativity -/

section MergeComm

/-- Commutativity square of the merge maps. -/
@[reassoc]
lemma finTensorMul_comm [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [SymmetricCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [∀ i, IsCommMonObj (B i)]
    (s t : Finset ι) :
    (β_ (finTensor B s) (finTensor B t)).hom ≫ finTensorMul B t s =
      finTensorMul B s t ≫
        eqToHom (show finTensor B (s ∪ t) = finTensor B (t ∪ s) by
          rw [Finset.union_comm]) := by
  rw [eqToHom_eq_finTensorIncl B (Finset.union_comm s t)
      (le_of_eq (Finset.union_comm s t)),
    finTensorMul_incl B Finset.subset_union_right
      Finset.subset_union_left,
    finTensorMul_def B t s, ← BraidedCategory.braiding_naturality_assoc,
    IsCommMonObj.mul_comm]

/-- The big tensor product of commutative monoid objects is
commutative. -/
instance bigTensorCommMon [Category.{v} D] [MonoidalCategory D] [LinearOrder ι]
    [SymmetricCategory D] (B : ι → D) [∀ i, MonObj (B i)]
    [∀ i, IsCommMonObj (B i)] [HasColimitsOfShape (Finset ι) D]
    [∀ X : D, PreservesColimitsOfShape (Finset ι) (tensorLeft X)] :
    IsCommMonObj (bigTensor B) where
  mul_comm := by
    show (β_ (bigTensor B) (bigTensor B)).hom ≫ bigTensorMul B =
      bigTensorMul B
    apply bigTensor_pair_hom_ext B
    intro s t
    rw [BraidedCategory.braiding_naturality_assoc,
      stage_bigTensorMul, stage_bigTensorMul,
      finTensorMul_comm_assoc B s t,
      eqToHom_eq_finTensorIncl B (Finset.union_comm s t)
        (le_of_eq (Finset.union_comm s t)),
      finTensorIncl_bigTensorStage]

end MergeComm

end RS
