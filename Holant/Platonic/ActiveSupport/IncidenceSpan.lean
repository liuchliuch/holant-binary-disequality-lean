import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Four small binary support sets with repeated incidence span at most four
coordinates. The proof uses actual indicator relations, not a graph oracle. -/
namespace Holant.Platonic.ActiveSupport
noncomputable section
open scoped BigOperators
open Module
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [DecidableEq V]

 def supportUnion (S : Fin 4→Finset V) : Finset V := Finset.univ.biUnion S

 theorem support_subset_union (S : Fin 4→Finset V) (i : Fin 4) : S i⊆supportUnion S := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩

 theorem support_incidence_count (S : Fin 4→Finset V) :
    (∑i,(S i).card)=∑x∈supportUnion S,(Finset.univ.filter (fun i=>x∈S i)).card := by
  have he (i : Fin 4) : (S i).card=∑x∈supportUnion S,if x∈S i then 1 else 0 := by
    rw [←Finset.sum_filter]
    have hf : (supportUnion S).filter (fun x=>x∈S i)=S i := by
      ext x
      simp only [Finset.mem_filter]
      exact and_iff_right_of_imp (fun hx=>support_subset_union S i hx)
    simp [hf]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  simp

 theorem support_double_count (S : Fin 4→Finset V)
    (hcover : ∀x∈supportUnion S,2≤(Finset.univ.filter (fun i=>x∈S i)).card) :
    2*(supportUnion S).card≤∑i,(S i).card := by
  rw [support_incidence_count]
  calc
    _ = ∑x∈supportUnion S,2 := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum hcover

 theorem support_union_card_le_six (S : Fin 4→Finset V)
    (hs : ∀i,(S i).card≤3)
    (hcover : ∀x∈supportUnion S,2≤(Finset.univ.filter (fun i=>x∈S i)).card) :
    (supportUnion S).card≤6 := by
  have hl := support_double_count S hcover
  have hu : (∑i,(S i).card)≤12 := by
    calc
      _ ≤ ∑_i : Fin 4,3 := Finset.sum_le_sum (fun i _=>hs i)
      _ = 12 := by norm_num
  omega

 theorem exists_triple_of_five (S : Fin 4→Finset V)
    (hs : ∀i,(S i).card≤3)
    (hcover : ∀x∈supportUnion S,2≤(Finset.univ.filter (fun i=>x∈S i)).card)
    (hn : 5≤(supportUnion S).card) : ∃i,(S i).card=3 := by
  by_contra h
  have ht : ∀i,(S i).card≤2 := by
    intro i
    have hi := hs i
    have hne : (S i).card≠3 := fun hh=>h ⟨i,hh⟩
    omega
  have hl := support_double_count S hcover
  have hu : (∑i,(S i).card)≤8 := by
    calc
      _ ≤ ∑_i : Fin 4,2 := Finset.sum_le_sum (fun i _=>ht i)
      _ = 8 := by norm_num
  omega

 theorem six_forces_triples (S : Fin 4→Finset V)
    (hs : ∀i,(S i).card≤3)
    (hcover : ∀x∈supportUnion S,2≤(Finset.univ.filter (fun i=>x∈S i)).card)
    (hn : (supportUnion S).card=6) : ∀i,(S i).card=3 := by
  have hl := support_double_count S hcover
  rw [hn] at hl
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hl
  change 12≤(S 0).card+((S 1).card+((S 2).card+(S 3).card)) at hl
  have h0:=hs 0
  have h1:=hs 1
  have h2:=hs 2
  have h3:=hs 3
  intro i
  fin_cases i
  · change (S 0).card=3; omega
  · change (S 1).card=3; omega
  · change (S 2).card=3; omega
  · change (S 3).card=3; omega

/-- The coefficient-to-vector map of the actual finite support union. -/
def supportMap (U : Finset V) : (U→ZMod 2) →ₗ[ZMod 2] V where
  toFun c := ∑x : U,c x • x.val
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum,smul_smul]

 theorem supportMap_range (U : Finset V) :
    LinearMap.range (supportMap U)=Submodule.span (ZMod 2) (U : Set V) := by
  apply le_antisymm
  · rintro _ ⟨c,rfl⟩
    apply Submodule.sum_mem
    intro x hx
    exact Submodule.smul_mem _ _ (Submodule.subset_span x.property)
  · apply Submodule.span_le.mpr
    intro x hx
    refine ⟨Pi.single (⟨x,hx⟩ : U) 1,?_⟩
    simp [supportMap,Pi.single_apply,ite_smul]

 def incidenceVector (U A : Finset V) : U→ZMod 2 := fun x=>if x.val∈A then 1 else 0

 theorem incidenceVector_image (U A : Finset V) (hA : A⊆U) :
    supportMap U (incidenceVector U A)=∑x∈A,x := by
  classical
  change (∑x : U,(if x.val∈A then (1 : ZMod 2) else 0) • x.val)=_
  simp only [ite_smul,one_smul,zero_smul]
  rw [←Finset.sum_filter]
  apply Finset.sum_bij (fun x _=>x.val)
  · intro x hx;exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy h;exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x,hA hx⟩,by simp [hx],rfl⟩
  · intro x hx;rfl

 theorem incidenceVector_ne_zero (U A : Finset V) (hA : A⊆U) (hn : A.Nonempty) :
    incidenceVector U A≠0 := by
  obtain ⟨x,hx⟩ := hn
  intro h
  have hh := congrFun h (⟨x,hA hx⟩ : U)
  norm_num [incidenceVector,hx] at hh

 theorem incidenceVector_injective (U : Finset V) {A B : Finset V}
    (hA : A⊆U) (hB : B⊆U) (h : incidenceVector U A=incidenceVector U B) : A=B := by
  ext x
  by_cases hx : x∈U
  · have hh := congrFun h (⟨x,hx⟩ : U)
    by_cases ha : x∈A <;> by_cases hb : x∈B <;> simp_all [incidenceVector]
  · have ha : x∉A := fun ha=>hx (hA ha)
    have hb : x∉B := fun hb=>hx (hB hb)
    simp [ha,hb]


 theorem support_rank_nullity (U : Finset V) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set V))+
      finrank (ZMod 2) (LinearMap.ker (supportMap U))=U.card := by
  have h := (supportMap U).finrank_range_add_finrank_ker
  rw [supportMap_range] at h
  simpa using h

 theorem one_support_relation_bound (U A : Finset V) (hA : A⊆U)
    (hAn : A.Nonempty) (hAs : ∑x∈A,x=0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set V))+1≤U.card := by
  have hr : incidenceVector U A∈LinearMap.ker (supportMap U) := by
    change supportMap U (incidenceVector U A)=0
    rw [incidenceVector_image U A hA,hAs]
  let r : LinearMap.ker (supportMap U) := ⟨incidenceVector U A,hr⟩
  have hn : r≠0 := fun h=>incidenceVector_ne_zero U A hA hAn (congrArg Subtype.val h)
  have hi : LinearIndependent (ZMod 2) (fun _ : Unit=>r) :=
    linearIndependent_unique_iff.mpr hn
  have hk : 1≤finrank (ZMod 2) (LinearMap.ker (supportMap U)) := by
    simpa using hi.fintype_card_le_finrank
  have hd := support_rank_nullity U
  omega

 theorem two_support_relations_bound (U A B : Finset V) (hA : A⊆U) (hB : B⊆U)
    (hAn : A.Nonempty) (hBn : B.Nonempty) (hne : A≠B)
    (hAs : ∑x∈A,x=0) (hBs : ∑x∈B,x=0) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (U : Set V))+2≤U.card := by
  have hAr : incidenceVector U A∈LinearMap.ker (supportMap U) := by
    change supportMap U (incidenceVector U A)=0
    rw [incidenceVector_image U A hA,hAs]
  have hBr : incidenceVector U B∈LinearMap.ker (supportMap U) := by
    change supportMap U (incidenceVector U B)=0
    rw [incidenceVector_image U B hB,hBs]
  let a : LinearMap.ker (supportMap U) := ⟨incidenceVector U A,hAr⟩
  let b : LinearMap.ker (supportMap U) := ⟨incidenceVector U B,hBr⟩
  have ha : a≠0 := fun h=>incidenceVector_ne_zero U A hA hAn (congrArg Subtype.val h)
  have hb : b≠0 := fun h=>incidenceVector_ne_zero U B hB hBn (congrArg Subtype.val h)
  have hab : a≠b := by
    intro h
    exact hne (incidenceVector_injective U hA hB (congrArg Subtype.val h))
  have hi : LinearIndependent (ZMod 2) ![a,b] := by
    apply linearIndependent_fin2.mpr
    refine ⟨hb,?_⟩
    intro c
    fin_cases c
    · change (0 : ZMod 2) • b≠a
      simpa only [zero_smul] using Ne.symm ha
    · change (1 : ZMod 2) • b≠a
      simpa only [one_smul] using Ne.symm hab
  have hk : 2≤finrank (ZMod 2) (LinearMap.ker (supportMap U)) := by
    simpa using hi.fintype_card_le_finrank
  have hd := support_rank_nullity U
  omega

/-- The source's four-support incidence bound. Sizes zero, one and three are
covered; allowing size two makes this statement slightly stronger. -/
 theorem four_support_span_le_four (S : Fin 4→Finset V)
    (hsize : ∀i,(S i).card≤3)
    (hsum : ∀i,(S i).card=3 → ∑x∈S i,x=0)
    (hcover : ∀x∈supportUnion S,2≤(Finset.univ.filter (fun i=>x∈S i)).card) :
    finrank (ZMod 2) (Submodule.span (ZMod 2) (supportUnion S : Set V))≤4 := by
  have hn := support_union_card_le_six S hsize hcover
  by_cases hsmall : (supportUnion S).card≤4
  · exact (finrank_span_finset_le_card (supportUnion S)).trans hsmall
  have hfive : 5≤(supportUnion S).card := by omega
  by_cases h6 : (supportUnion S).card=6
  · have ht := six_forces_triples S hsize hcover h6
    have hd : ∃i,S i≠S 0 := by
      by_contra hh
      have hall : ∀i,S i=S 0 := by
        intro i
        by_contra hi
        exact hh ⟨i,hi⟩
      have he : supportUnion S=S 0 := by
        ext x
        constructor
        · intro hx
          obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
          simpa only [hall i] using hi
        · exact fun hx=>support_subset_union S 0 hx
      have hc := ht 0
      rw [he] at h6
      omega
    obtain ⟨i,hi⟩ := hd
    have h0n : (S 0).Nonempty := Finset.card_pos.mp (by rw [ht 0];omega)
    have hin : (S i).Nonempty := Finset.card_pos.mp (by rw [ht i];omega)
    have hr := two_support_relations_bound (supportUnion S) (S 0) (S i)
      (support_subset_union S 0) (support_subset_union S i) h0n hin (Ne.symm hi)
      (hsum 0 (ht 0)) (hsum i (ht i))
    omega
  · obtain ⟨i,hi⟩ := exists_triple_of_five S hsize hcover hfive
    have hin : (S i).Nonempty := Finset.card_pos.mp (by rw [hi];omega)
    have hr := one_support_relation_bound (supportUnion S) (S i)
      (support_subset_union S i) hin (hsum i hi)
    omega

end
end Holant.Platonic.ActiveSupport
