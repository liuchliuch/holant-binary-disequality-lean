import Holant.Pauli.ExoticKlein.EightPortBase
import Holant.Pauli.ExoticKlein.EightPortTheorem

/-! The complete source 8.8 statement uses exactly the original 112 contexts:
28 unordered original-port pairs and four displayed Frobenius duals. The
opposite pair order is proved safe with its exact transpose scalar. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
namespace MatchingCard

theorem exotic_scale {P : Type*} (f : Tensor ℂ P) (hf : ExoticMatchingOrZero f) (c : ℂ) :
    ExoticMatchingOrZero (fun x => c*f x) := by
  by_cases hc : c = 0
  · left; subst c; funext x; simp
  rcases hf with hz | ⟨r,M,labels,d,hd,he⟩
  · left; rw [hz]; funext x; simp
  · exact Or.inr ⟨r,M,labels,c*d,mul_ne_zero hc hd,by rw [he]; funext x; ring⟩

theorem contractPair_scale {P : Type*} [DecidableEq P] (u v : P) (C : Kernel ℂ)
    (c : ℂ) (f : Tensor ℂ P) :
    contractPair u v (scale c C) f = fun x => c*contractPair u v C f x := by
  funext x
  simp only [contractPair,scale,Fintype.sum_bool]
  ring

def swapRemaining {P : Type*} (u v : P) : Remaining u v ≃ Remaining v u :=
  Equiv.subtypeEquivRight (fun _ => and_comm)

theorem contractPair_swap {P : Type*} [DecidableEq P] (u v : P) (huv : u ≠ v)
    (C : Kernel ℂ) (f : Tensor ℂ P) :
    contractPair u v C f = Tensor.reindex (swapRemaining v u) (contractPair v u (Kernel.transpose C) f) := by
  funext x
  have hw (a b : Bool) : insertPair u v a b (extendRemaining u v x) =
      insertPair v u b a (extendRemaining v u (fun j => x (swapRemaining v u j))) := by
    funext i
    by_cases hi : i = u
    · subst i
      simp [insertPair,huv,Ne.symm huv]
    by_cases hj : i = v
    · subst i
      simp [insertPair,huv,Ne.symm huv]
    simp [insertPair,extendRemaining,hi,hj,swapRemaining]
    rfl
  simp only [contractPair,Tensor.reindex,Kernel.transpose_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  rw [hw]

theorem transpose_dual (a : Label) :
    ∃ c : ℂ, c ≠ 0 ∧ Kernel.transpose (dual a) = scale c (dual (theta a)) := by
  refine ⟨(d a)⁻¹*transposeScalar (theta a)*d (theta a),
    mul_ne_zero (mul_ne_zero (inv_ne_zero (d_ne_zero a)) (transposeScalar_ne_zero _)) (d_ne_zero _),?_⟩
  funext u v
  have he := congrFun (congrFun (transpose_E (theta a)) u) v
  change E (theta a) v u = transposeScalar (theta a)*E (theta (theta a)) u v at he
  change (d a)⁻¹*E (theta a) v u =
    ((d a)⁻¹*transposeScalar (theta a)*d (theta a))*((d (theta a))⁻¹*E (theta (theta a)) u v)
  rw [he]
  field_simp [d_ne_zero (theta a)]

theorem insertPair_eq_fill {P : Type*} [DecidableEq P] (u v : P) (huv : u ≠ v)
    (a b : Bool) (x : Remaining u v → Bool) :
    insertPair u v a b (extendRemaining u v x) = ProjectiveDetermination.fill u v a b x := by
  funext i
  by_cases hi : i = u
  · subst i
    simp [insertPair,ProjectiveDetermination.fill,huv]
  by_cases hj : i = v
  · subst i
    simp [insertPair,ProjectiveDetermination.fill,Ne.symm huv]
  simp [insertPair,extendRemaining,ProjectiveDetermination.fill,hi,hj]

theorem eight_pairCard_eq (u v : Fin 8) (huv : u ≠ v) (a : Label) (f : Signature ℂ 8) :
    EightPort.pairCard u v a f = contractPair u v (asMatrix (dual a)) f := by
  funext x
  simp only [EightPort.pairCard,contractPair,insertPair_eq_fill u v huv,asMatrix,Matrix.of_apply]

theorem pairSafe_of_allSafeCards (f : Signature ℂ 8) (hf : EightPort.AllSafeCards f) : PairSafe f := by
  have hsorted (u v : Fin 8) (huv : u < v) (a : Label) :
      ExoticMatchingOrZero (contractPair u v (asMatrix (dual a)) f) := by
    rw [←eight_pairCard_eq u v (ne_of_lt huv)]
    rcases hf u v huv a with hz | ⟨M,labels,c,hc,he⟩
    · exact Or.inl hz
    · exact Or.inr ⟨3,M,labels,c,hc,he⟩
  intro u v huv a
  rcases lt_or_gt_of_ne huv with hlt | hgt
  · exact hsorted u v hlt a
  · change ExoticMatchingOrZero (contractPair u v (dual a) f)
    rw [contractPair_swap u v huv]
    obtain ⟨c,hc,he⟩ := transpose_dual a
    rw [he,contractPair_scale]
    exact exotic_reindex _ _ (exotic_scale _ (hsorted v u hgt (theta a)) c)

end MatchingCard

namespace EightPort

/-- Full source Lemma 8.8, without a stipulated linear or permutation normal
form. Both factor arities are positive and the partition covers all eight
original ports. Every possible zero card and complex cancellation is allowed. -/
theorem full_eight_port_has_proper_tensor_factor (h : Signature ℂ 8) (hn : h ≠ 0)
    (hs : AllSafeCards h) : HasProperTensorFactor h :=
  MatchingCard.eight_port_factor_of_pairSafe h hn (MatchingCard.pairSafe_of_allSafeCards h hs)

end EightPort
end
end Holant.Pauli.ExoticKlein
