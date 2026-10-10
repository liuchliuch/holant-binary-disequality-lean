import Holant.Certificates.AffineReference.FullEvenData
import Holant.EightVertex.ProductAnchor.NetworksData

/-! Literal crossed two-copy construction from A.2(iv)/A.5(iii). The selected
ports 0,j are joined to j,0 on the other copy, using two native X edges. -/
namespace Holant.Certificates.AffineReference
open Holant Holant.Certificates.TwelveLoops Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def crossedOrder : Fin 3 → Fin 8 → Fin 8 :=
  ![![0,5,1,4,2,3,6,7],![0,6,2,4,1,3,5,7],![0,7,3,4,1,2,5,6]]
def crossedInverse : Fin 3 → Fin 8 → Fin 8 :=
  ![![0,2,4,5,3,1,6,7],![0,4,2,5,3,6,1,7],![0,4,5,2,3,6,7,1]]
def crossedEquiv (e : Fin 3) : Equiv.Perm (Fin 8) where
  toFun := crossedOrder e
  invFun := crossedInverse e
  left_inv := by
    have h : ∀ e i,crossedInverse e (crossedOrder e i)=i := by decide
    exact h e
  right_inv := by
    have h : ∀ e i,crossedOrder e (crossedInverse e i)=i := by decide
    exact h e

def crossPrefix (u r v t : Bool) (x : Fin 4 → Bool) : Fin 8 → Bool :=
  Fin.cons u (Fin.cons r (Fin.cons v (Fin.cons t x)))

theorem crossed_left_word (e : Fin 3) (u v : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => crossPrefix u (!u) v (!v) x ((crossedEquiv e).symm (Fin.castAdd 4 i)))=
      insertPair (initialPair e) u v (firstHalf x) := by
  funext i
  fin_cases e <;> fin_cases i <;> rfl

theorem crossed_right_word (e : Fin 3) (u v : Bool) (x : Fin 4 → Bool) :
    (fun i : Fin 4 => crossPrefix u (!u) v (!v) x ((crossedEquiv e).symm (Fin.natAdd 4 i)))=
      insertPair (initialPair e) (!v) (!u) (secondHalf x) := by
  funext i
  fin_cases e <;> fin_cases i <;> rfl

variable {K : Type*} [CommSemiring K]

def crossedCopies (f : Signature K 4) (e : Fin 3) : Signature K 4 := fun x =>
  ∑ u : Bool, ∑ v : Bool, f (insertPair (initialPair e) u v (firstHalf x))*
    f (insertPair (initialPair e) (!v) (!u) (secondHalf x))

def crossedNativeNetwork (f : Signature K 4) (e : Fin 3) : Network K 4 :=
  ((reorderNetwork (EightVertex.ProductAnchor.pairCorolla f) (crossedEquiv e).symm).contract
    Signature.disequality).contract Signature.disequality

theorem crossedNativeNetwork_denote (f : Signature K 4) (e : Fin 3) :
    (crossedNativeNetwork f e).denote=crossedCopies f e := by
  rw [crossedNativeNetwork,Network.denote_contract,Network.denote_contract,
    reorderNetwork_denote,EightVertex.ProductAnchor.pairCorolla_denote]
  funext x
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  change
    (f (fun i => crossPrefix false true false true x ((crossedEquiv e).symm (Fin.castAdd 4 i))) *
      f (fun i => crossPrefix false true false true x ((crossedEquiv e).symm (Fin.natAdd 4 i))) +
    f (fun i => crossPrefix true false false true x ((crossedEquiv e).symm (Fin.castAdd 4 i))) *
      f (fun i => crossPrefix true false false true x ((crossedEquiv e).symm (Fin.natAdd 4 i)))) +
    (f (fun i => crossPrefix false true true false x ((crossedEquiv e).symm (Fin.castAdd 4 i))) *
      f (fun i => crossPrefix false true true false x ((crossedEquiv e).symm (Fin.natAdd 4 i))) +
    f (fun i => crossPrefix true false true false x ((crossedEquiv e).symm (Fin.castAdd 4 i))) *
      f (fun i => crossPrefix true false true false x ((crossedEquiv e).symm (Fin.natAdd 4 i)))) = _
  have l00 := crossed_left_word e false false x
  have r00 := crossed_right_word e false false x
  have l10 := crossed_left_word e true false x
  have r10 := crossed_right_word e true false x
  have l01 := crossed_left_word e false true x
  have r01 := crossed_right_word e false true x
  have l11 := crossed_left_word e true true x
  have r11 := crossed_right_word e true true x
  simp only [Bool.not_false,Bool.not_true] at l00 r00 l10 r10 l01 r01 l11 r11
  rw [l00,r00,l10,r10,l01,r01,l11,r11]
  simp [crossedCopies,add_comm,add_left_comm,add_assoc]

theorem crossedCopies_realizes (f : Signature K 4) (e : Fin 3) :
    Gadget.Realizes ({⟨4,f⟩} : SignatureFamily K) .disequality (crossedCopies f e) := by
  rw [←crossedNativeNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    exact Set.mem_singleton _
  · intro j
    change Fin 2 at j
    fin_cases j <;> rfl

end Holant.Certificates.AffineReference
