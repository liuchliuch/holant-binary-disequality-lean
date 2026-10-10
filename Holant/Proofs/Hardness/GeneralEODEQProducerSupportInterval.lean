import Holant.Proofs.Hardness.GeneralEODEQProducerCore
import Holant.Proofs.Hardness.GeneralEODEQProducerSupportBasic

/-! An improving interval of central support descends to an improving
two-coordinate move unless an isolated distant pair already exists. Every
selected coordinate remains in the original interval's difference set. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportInterval
open Holant Holant.Tractable
open scoped BigOperators
namespace C
export GeneralEODEQProducerCore (Pair Isolated central_word)
end C
namespace D
export GeneralEOPhaseExtractionDistance (distance distance_self distance_pos)
end D
namespace B
export GeneralEODEQProducerSupportBasic (TwoFlip charge_sum spin)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

def Between (a b c : Fin n → Bool) : Prop := ∀ i, a i=b i → c i=a i

theorem distance_split (a b c : Fin n → Bool) (hc : Between a b c) :
    D.distance a c+D.distance c b=D.distance a b := by
  simp only [D.distance,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := hc i
  cases ha : a i <;> cases hb : b i <;> cases hci : c i <;> simp_all

theorem charge_split (δ a b c : Fin n → Bool) (hc : Between a b c) :
    charge (tripleXor δ a b)+charge δ =
      charge (tripleXor δ a c)+charge (tripleXor δ c b) := by
  simp only [B.charge_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := hc i
  unfold tripleXor B.spin
  cases hd : δ i <;> cases ha : a i <;> cases hb : b i <;> cases hci : c i <;> simp_all

theorem left_subset (a b c : Fin n → Bool) (hc : Between a b c) :
    ∀ i, a i≠c i → a i≠b i := by
  intro i h hi
  exact h (hc i hi).symm

theorem right_subset (a b c : Fin n → Bool) (hc : Between a b c) :
    ∀ i, c i≠b i → a i≠b i := by
  intro i h hi
  exact h ((hc i hi).trans hi)

variable (f : Signature AlgebraicComplex n) (he : Signature.CentralSupport f)
variable (noPair : ¬Nonempty (C.Pair f))

include he noPair in
/-- The charge comparison uses the same test word throughout the descent;
the two subintervals have disjoint changed coordinates. -/
theorem exists_distance_two (δ a b : Fin n → Bool) (ha : f a≠0) (hb : f b≠0)
    (gain : charge δ < charge (tripleXor δ a b)) :
    ∃ u v, f u≠0 ∧ f v≠0 ∧ D.distance u v=2 ∧
      charge δ < charge (tripleXor δ u v) ∧
      (∀ i, u i≠v i → a i≠b i) := by
  generalize hd : D.distance a b=d
  induction d using Nat.strong_induction_on generalizing a b with
  | h d ih =>
    have hab : a≠b := by
      rintro rfl
      have hx : tripleXor δ a a=δ := by
        funext i
        unfold tripleXor
        cases δ i <;> cases a i <;> rfl
      rw [hx] at gain
      omega
    by_cases large : 4≤d
    · have hi : ¬C.Isolated f a b := by
        intro hiso
        exact noPair ⟨⟨a,b,ha,hb,by omega,hiso⟩⟩
      unfold C.Isolated at hi
      push Not at hi
      obtain ⟨c,hc,hfix,hca,hcb⟩ := hi
      have split := distance_split a b c hfix
      have hac := D.distance_pos (Ne.symm hca)
      have hbc := D.distance_pos hcb
      have improve := charge_split δ a b c hfix
      have cases_gain : charge δ < charge (tripleXor δ a c) ∨
          charge δ < charge (tripleXor δ c b) := by omega
      rcases cases_gain with hgain | hgain
      · obtain ⟨u,v,hu,hv,huv,hg,hsub⟩ := ih (D.distance a c) (by omega) a c ha hc hgain rfl
        exact ⟨u,v,hu,hv,huv,hg,fun i hi => left_subset a b c hfix i (hsub i hi)⟩
      · obtain ⟨u,v,hu,hv,huv,hg,hsub⟩ := ih (D.distance c b) (by omega) c b hc hb hgain rfl
        exact ⟨u,v,hu,hv,huv,hg,fun i hi => right_subset a b c hfix i (hsub i hi)⟩
    · have haW := C.central_word f he a ha
      have hbW := C.central_word f he b hb
      have cols := GeneralEOPhaseExtractionCoordinates.column_equations a b
      have pos := D.distance_pos hab
      have two : D.distance a b=2 := by omega
      exact ⟨a,b,ha,hb,two,gain,fun _ hi => hi⟩

theorem distance_two_coordinates (u v : Fin n → Bool) (hd : D.distance u v=2) :
    ∃ i j, i≠j ∧ ∀ k, u k≠v k ↔ k=i ∨ k=j := by
  let changed : Finset (Fin n) := Finset.univ.filter (fun k => u k≠v k)
  have hcard : changed.card=2 := by
    rw [←hd]
    simp only [changed,Finset.card_eq_sum_ones,Finset.sum_filter,D.distance]
    apply Finset.sum_congr rfl
    intro k _
    by_cases h : u k=v k <;> simp [h]
  obtain ⟨i,j,hij,hchanged⟩ := Finset.card_eq_two.mp hcard
  refine ⟨i,j,hij,?_⟩
  intro k
  have h : k∈changed ↔ k=i ∨ k=j := by rw [hchanged]; simp
  simpa only [changed,Finset.mem_filter,Finset.mem_univ,true_and] using h

include he noPair in
/-- The zero-moving step receives two actual original-support words, two
zero bits of the test word, and their membership in the original difference
set. No DEQ4 source or interval completeness is assumed. -/
theorem exists_twoFlip (δ a b : Fin n → Bool) (ha : f a≠0) (hb : f b≠0)
    (gain : charge δ < charge (tripleXor δ a b)) :
    ∃ i j, Nonempty (B.TwoFlip f i j) ∧ δ i=false ∧ δ j=false ∧
      a i≠b i ∧ a j≠b j := by
  obtain ⟨u,v,hu,hv,hd,hgain,hsub⟩ := exists_distance_two f he noPair δ a b ha hb gain
  obtain ⟨i,j,hij,hdiff⟩ := distance_two_coordinates u v hd
  let T : B.TwoFlip f i j := ⟨u,v,hu,hv,hij,hdiff⟩
  have hcharge := T.charge_xor δ
  change charge (tripleXor δ u v)=_ at hcharge
  have zeros : δ i=false ∧ δ j=false := by
    cases hi : δ i <;> cases hj : δ j <;> simp_all [B.spin]
    omega
  exact ⟨i,j,⟨T⟩,zeros.1,zeros.2,hsub i ((hdiff i).mpr (Or.inl rfl)),
    hsub j ((hdiff j).mpr (Or.inr rfl))⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerSupportInterval
