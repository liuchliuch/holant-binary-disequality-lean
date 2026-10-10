import Holant.Proofs.Hardness.GeneralEOPhaseExtractionCoordinates
import Holant.Proofs.Hardness.GeneralEOPinnedDescentLabels

/-! Coordinate invariants for the literal pinned DEQ producer. An isolated
interval is stated only in terms of the original support and its two words;
it does not assume any network, equality signature, or hardness conclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerCore
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace D
export GeneralEOPhaseExtractionDistance (distance distance_word distance_pos distance_self)
end D
namespace C
export GeneralEOPhaseExtractionCoordinates (columns column_equations opposite_prefix distance_comp)
end C
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote reboundaryLabels)
end N
namespace E
export GeneralEOCentralHoleCoordinates (tail2 word_tail prefix_two reboundary_word reboundary_central)
end E
namespace O
export GeneralEOPinnedDescentOperations (word word_weight pinned pinned_denote)
end O
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

/-- The supported interval between the two designated words has no third point. -/
def Isolated (f : Signature K n) (a b : Fin n → Bool) : Prop :=
  ∀ x, f x ≠ 0 → (∀ i, a i=b i → x i=a i) → x=a ∨ x=b

structure Pair (f : Signature K n) where
  left : Fin n → Bool
  right : Fin n → Bool
  left_supported : f left ≠ 0
  right_supported : f right ≠ 0
  distant : 4 ≤ D.distance left right
  isolated : Isolated f left right

theorem distance_le (a b : Fin n → Bool) : D.distance a b≤n := by
  calc
    D.distance a b ≤ ∑ _i : Fin n, (1 : ℕ) :=
      Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = n := by simp

theorem distance_eq_iff (a b : Fin n → Bool) :
    D.distance a b=n ↔ ∀i,a i≠b i := by
  have h := C.column_equations a b
  constructor
  · intro hd i hi
    by_cases ha : a i=false
    · have hm : i∈C.columns a b false false := by simp [C.columns,ha,←hi]
      have hp := Finset.card_pos.mpr ⟨i,hm⟩
      omega
    · have hat : a i=true := Bool.eq_true_of_not_eq_false ha
      have hm : i∈C.columns a b true true := by simp [C.columns,hat,←hi]
      have hp := Finset.card_pos.mpr ⟨i,hm⟩
      omega
  · intro hn
    simp [D.distance,hn]

theorem complementary_of_max (a b : Fin n → Bool) (hd : D.distance a b=n) :
    b=fun i => !(a i) := by
  have hn := (distance_eq_iff a b).mp hd
  funext i
  have hi := hn i
  cases ha : a i <;> cases hb : b i <;> simp_all

theorem central_word (f : Signature K n) (he : Signature.CentralSupport f)
    (x : Fin n → Bool) (hx : f x≠0) : 2*weight x=n := by
  by_contra h
  exact hx (he x h)

theorem isolated_comp (f : Signature K n) (a b : Fin n → Bool)
    (hi : Isolated f a b) (e : Equiv.Perm (Fin n)) :
    Isolated (fun x => f (x ∘ e.symm)) (a ∘ e) (b ∘ e) := by
  intro x hx hfix
  have hfix' : ∀i,a i=b i → (x ∘ e.symm) i=a i := by
    intro i hi
    have hh := hfix (e.symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using hh (by simpa using hi)
  rcases hi (x ∘ e.symm) hx hfix' with h | h
  · left
    funext i
    have hh := congrFun h (e i)
    simpa using hh
  · right
    funext i
    have hh := congrFun h (e i)
    simpa using hh

def Pair.reboundary (S : Network K n) (p : Pair S.denote) (e : Equiv.Perm (Fin n)) :
    Pair (N.reboundary S e.symm).denote where
  left := p.left ∘ e
  right := p.right ∘ e
  left_supported := by simpa only [E.reboundary_word] using p.left_supported
  right_supported := by simpa only [E.reboundary_word] using p.right_supported
  distant := by simpa only [C.distance_comp] using p.distant
  isolated := by
    rw [N.reboundary_denote]
    exact isolated_comp S.denote p.left p.right p.isolated e

/-- Shared coordinates of two central words occur in balanced 00/11 pairs. -/
theorem common_columns (a b : Fin n → Bool) (ha : 2*weight a=n)
    (hb : 2*weight b=n) (hd : D.distance a b<n) :
    ∃i j : Fin n,i≠j ∧ a i=false ∧ b i=false ∧ a j=true ∧ b j=true := by
  have h := C.column_equations a b
  have h00 : 0<(C.columns a b false false).card := by omega
  have h11 : 0<(C.columns a b true true).card := by omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp h00
  obtain ⟨j,hj⟩ := Finset.card_pos.mp h11
  simp only [C.columns,Finset.mem_filter,Finset.mem_univ,true_and] at hi hj
  refine ⟨i,j,?_,hi.1,hi.2,hj.1,hj.2⟩
  rintro rfl
  simp_all

theorem common_prefix (a b : Fin (n+2) → Bool) (ha : 2*weight a=n+2)
    (hb : 2*weight b=n+2) (hd : D.distance a b<n+2) :
    ∃e : Equiv.Perm (Fin (n+2)),
      a ∘ e=O.word false true (E.tail2 (a ∘ e)) ∧
      b ∘ e=O.word false true (E.tail2 (b ∘ e)) := by
  obtain ⟨i,j,hij,hai,hbi,haj,hbj⟩ := common_columns a b ha hb hd
  let v : Fin 2 → Fin (n+2) := ![i,j]
  have hv : Function.Injective v := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all [v]
  obtain ⟨h,e,he⟩ := GeneralEOCentralHolePatterns.exists_prefix_permutation v hv
  refine ⟨e,E.prefix_two (a ∘ e) false true h ?_,E.prefix_two (b ∘ e) false true h ?_⟩
  all_goals
    funext q
    simp only [Function.comp_apply,he]
    fin_cases q <;> simp [v,hai,hbi,haj,hbj]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerCore
