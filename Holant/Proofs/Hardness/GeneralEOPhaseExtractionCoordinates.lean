import Holant.Proofs.Hardness.GeneralEOPhaseExtractionStep
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionDistance
import Holant.Proofs.Hardness.GeneralEOCentralHoleCoordinates

/-! Finite column counts select actual prefix permutations of two balanced words. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionCoordinates
open Holant
open scoped BigOperators
namespace D
export GeneralEOPhaseExtractionDistance (distance distance_pos)
end D
namespace E
export GeneralEOCentralHoleCoordinates (tail2 prefix_two reboundary_word reboundary_central weight_comp)
end E
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace T
export GeneralEOPhaseExtractionStep (triple)
end T
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def columns (x y : Fin n → Bool) (u v : Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => x i=u ∧ y i=v)

theorem columns_card (x y : Fin n → Bool) (u v : Bool) :
    (columns x y u v).card=∑i : Fin n,if x i=u ∧ y i=v then 1 else 0 := by
  simp only [columns,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem column_equations (x y : Fin n → Bool) :
    weight x=(columns x y true false).card+(columns x y true true).card ∧
    weight y=(columns x y false true).card+(columns x y true true).card ∧
    D.distance x y=(columns x y false true).card+(columns x y true false).card ∧
    n=(columns x y false false).card+(columns x y false true).card+
      (columns x y true false).card+(columns x y true true).card := by
  simp only [columns_card, ←Finset.sum_add_distrib]
  refine ⟨?_,?_,?_,?_⟩
  · apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> rfl
  · apply Finset.sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> rfl
  · calc
      n = ∑_i : Fin n,(1 : ℕ) := by simp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        cases x i <;> cases y i <;> rfl

theorem opposite_columns (x y : Fin n → Bool) (he : weight x=weight y) (hne : x≠y) :
    ∃i j : Fin n,i≠j ∧ x i=false ∧ y i=true ∧ x j=true ∧ y j=false := by
  have h := column_equations x y
  have hd := D.distance_pos hne
  have h01 : 0<(columns x y false true).card := by omega
  have h10 : 0<(columns x y true false).card := by omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp h01
  obtain ⟨j,hj⟩ := Finset.card_pos.mp h10
  simp only [columns,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  refine ⟨i,j,?_,hi.1,hi.2,hj.1,hj.2⟩
  rintro rfl
  simp_all

theorem common_triple (x y : Fin n → Bool) (hx : 2*weight x=n) (hy : 2*weight y=n)
    (hn : 6≤n) (hd : D.distance x y=2) :
    ∃i j k : Fin n,i≠j ∧ i≠k ∧ j≠k ∧
      x i=false ∧ y i=false ∧ x j=true ∧ y j=true ∧ x k=true ∧ y k=true := by
  have h := column_equations x y
  have h00 : 0<(columns x y false false).card := by omega
  have h11 : 1<(columns x y true true).card := by omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp h00
  obtain ⟨j,hj,k,hk,hjk⟩ := Finset.one_lt_card.mp h11
  simp only [columns,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj hk
  refine ⟨i,j,k,?_,?_,hjk,hi.1,hi.2,hj.1,hj.2,hk.1,hk.2⟩
  · rintro rfl
    simp_all
  · rintro rfl
    simp_all

theorem opposite_prefix (x y : Fin (n+2) → Bool) (he : weight x=weight y) (hne : x≠y) :
    ∃e : Equiv.Perm (Fin (n+2)),
      x ∘ e=O.word false true (E.tail2 (x ∘ e)) ∧
      y ∘ e=O.word true false (E.tail2 (y ∘ e)) := by
  obtain ⟨i,j,hij,hxi,hyi,hxj,hyj⟩ := opposite_columns x y he hne
  let v : Fin 2 → Fin (n+2) := ![i,j]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  obtain ⟨h,e,he⟩ := GeneralEOCentralHolePatterns.exists_prefix_permutation v hv
  refine ⟨e,E.prefix_two (x ∘ e) false true h ?_,E.prefix_two (y ∘ e) true false h ?_⟩
  all_goals
    funext q
    simp only [Function.comp_apply,he]
    fin_cases q <;> simp [v,hxi,hyi,hxj,hyj]

def tail3 (x : Fin (n+3) → Bool) : Fin n → Bool := fun i => x i.succ.succ.succ

theorem prefix_three (x : Fin (n+3) → Bool) (h : 3≤n+3)
    (hp : x ∘ Fin.castLE h=![false,true,true]) :
    x=T.triple false true true (tail3 x) := by
  have h0 : x 0=false := by simpa using congrFun hp 0
  have h1 : x 1=true := by
    have hi : Fin.castLE h (1 : Fin 3)=(1 : Fin (n+3)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [hi] using congrFun hp 1
  have h2 : x 2=true := by
    have hi : Fin.castLE h (2 : Fin 3)=(2 : Fin (n+3)) := by
      apply Fin.ext
      simp (disch := omega) [Nat.mod_eq_of_lt]
    simpa [hi] using congrFun hp 2
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => ?_) i) i) i
  · exact h0
  · exact h1
  · exact h2
  · rfl

theorem common_prefix (x y : Fin (n+3) → Bool)
    (hx : 2*weight x=n+3) (hy : 2*weight y=n+3) (hn : 6≤n+3) (hd : D.distance x y=2) :
    ∃e : Equiv.Perm (Fin (n+3)),
      x ∘ e=T.triple false true true (tail3 (x ∘ e)) ∧
      y ∘ e=T.triple false true true (tail3 (y ∘ e)) := by
  obtain ⟨i,j,k,hij,hik,hjk,hxi,hyi,hxj,hyj,hxk,hyk⟩ := common_triple x y hx hy hn hd
  let v : Fin 3 → Fin (n+3) := ![i,j,k]
  have hv : Function.Injective v := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [v]
  obtain ⟨h,e,he⟩ := GeneralEOCentralHolePatterns.exists_prefix_permutation v hv
  refine ⟨e,prefix_three (x ∘ e) h ?_,prefix_three (y ∘ e) h ?_⟩
  all_goals
    funext q
    simp only [Function.comp_apply,he]
    fin_cases q <;> simp [v,hxi,hyi,hxj,hyj,hxk,hyk]

theorem distance_comp (x y : Fin n → Bool) (e : Equiv.Perm (Fin n)) :
    D.distance (x ∘ e) (y ∘ e)=D.distance x y :=
  Equiv.sum_comp e (fun i => if x i=y i then 0 else 1)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionCoordinates
