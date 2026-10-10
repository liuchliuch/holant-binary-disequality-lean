import Holant.Certificates.FourthRootOdd.NetworkTools
import Holant.Certificates.FourthRootOdd.TwoCopy

/-! Genuine two-vertex/two-native-edge network for the source two-copy output.
Every vertex is the original signature, not an evaluated replacement table. -/
namespace Holant.Certificates.FourthRootOdd
open Holant
set_option backward.isDefEq.respectTransparency false

def copyOrder : Fin 6 → Fin 8 → Fin 8 :=
  ![![0,4,1,5,2,3,6,7],![0,4,2,6,1,3,5,7],![0,4,3,7,1,2,5,6],
    ![1,5,2,6,0,3,4,7],![1,5,3,7,0,2,4,6],![2,6,3,7,0,1,4,5]]
def copyInverse : Fin 6 → Fin 8 → Fin 8 :=
  ![![0,2,4,5,1,3,6,7],![0,4,2,5,1,6,3,7],![0,4,5,2,1,6,7,3],
    ![4,0,2,5,6,1,3,7],![4,0,5,2,6,1,7,3],![4,5,0,2,6,7,1,3]]
def copyEquiv (p : Fin 6) : Equiv.Perm (Fin 8) where
  toFun := copyOrder p
  invFun := copyInverse p
  left_inv := by
    have h : ∀ p i,copyInverse p (copyOrder p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i,copyOrder p (copyInverse p i)=i := by decide
    exact h p

def fourPrefix (u r v t : Bool) (x : Fin 4 → Bool) : Fin 8 → Bool :=
  Fin.cons u (Fin.cons r (Fin.cons v (Fin.cons t x)))

theorem first_copy_word (p : Fin 6) (u v : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => fourPrefix u (!u) v (!v) x ((copyEquiv p).symm (Fin.castAdd 4 i))) =
      insertPair p u v (firstHalf x) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

theorem second_copy_word (p : Fin 6) (u v : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => fourPrefix u (!u) v (!v) x ((copyEquiv p).symm (Fin.natAdd 4 i))) =
      insertPair p (!u) (!v) (secondHalf x) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

variable {K : Type*} [CommSemiring K]

noncomputable def twoCopyNetwork (f : Signature K 4) (p : Fin 6) : Network K 4 :=
  ((reorderNetwork ((singleVertexNetwork f).tensor (singleVertexNetwork f)) (copyEquiv p).symm).contract
    Signature.disequality).contract Signature.disequality

theorem twoCopyNetwork_denote (f : Signature K 4) (p : Fin 6) :
    (twoCopyNetwork f p).denote=twoCopy f p := by
  rw [twoCopyNetwork,Network.denote_contract,Network.denote_contract,reorderNetwork_denote,
    Network.denote_tensor,singleVertexNetwork_denote]
  funext x
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  change
    (f (fun i => fourPrefix false true false true x ((copyEquiv p).symm (Fin.castAdd 4 i))) *
      f (fun i => fourPrefix false true false true x ((copyEquiv p).symm (Fin.natAdd 4 i))) +
    f (fun i => fourPrefix true false false true x ((copyEquiv p).symm (Fin.castAdd 4 i))) *
      f (fun i => fourPrefix true false false true x ((copyEquiv p).symm (Fin.natAdd 4 i)))) +
    (f (fun i => fourPrefix false true true false x ((copyEquiv p).symm (Fin.castAdd 4 i))) *
      f (fun i => fourPrefix false true true false x ((copyEquiv p).symm (Fin.natAdd 4 i))) +
    f (fun i => fourPrefix true false true false x ((copyEquiv p).symm (Fin.castAdd 4 i))) *
      f (fun i => fourPrefix true false true false x ((copyEquiv p).symm (Fin.natAdd 4 i)))) = _
  have l00 := first_copy_word p false false x
  have r00 := second_copy_word p false false x
  have l10 := first_copy_word p true false x
  have r10 := second_copy_word p true false x
  have l01 := first_copy_word p false true x
  have r01 := second_copy_word p false true x
  have l11 := first_copy_word p true true x
  have r11 := second_copy_word p true true x
  simp only [Bool.not_false,Bool.not_true] at l00 r00 l10 r10 l01 r01 l11 r11
  rw [l00,r00,l10,r10,l01,r01,l11,r11]
  simp [twoCopy,add_comm,add_left_comm,add_assoc]

theorem twoCopy_realizes (f : Signature K 4) (p : Fin 6) :
    Gadget.Realizes ({⟨4,f⟩} : SignatureFamily K) .disequality (twoCopyNative f p) := by
  rw [twoCopyNative_eq,←twoCopyNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    change (⟨_,(Network.tensorFinite (singleVertexNetwork f) (singleVertexNetwork f)).vertex
      ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)⟩ : AnySignature K) ∈ ({⟨4,f⟩} : SignatureFamily K)
    cases (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v <;> exact Set.mem_singleton _
  · intro e
    refine Fin.cases rfl (fun e => ?_) e
    refine Fin.cases rfl (fun e => ?_) e
    exact Fin.elim0 e

end Holant.Certificates.FourthRootOdd
