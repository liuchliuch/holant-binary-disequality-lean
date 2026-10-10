import Holant.Certificates.FourthRootOdd.NativeLoop
import Holant.Certificates.FourthRootOdd.TwoCopy

/-! Equality-mediated loop as a genuine two-vertex, two-native-X-edge network.
The equality vertex is an explicit resource, not an installed structural edge. -/
namespace Holant.Certificates.FourthRootOdd
open Holant Holant.Certificates.TwelveLoops
set_option backward.isDefEq.respectTransparency false

def equalityOrder : Fin 6 → Fin 6 → Fin 6 :=
  ![![0,4,1,5,2,3],![0,4,2,5,1,3],![0,4,3,5,1,2],
    ![1,4,2,5,0,3],![1,4,3,5,0,2],![2,4,3,5,0,1]]
def equalityInverse : Fin 6 → Fin 6 → Fin 6 :=
  ![![0,2,4,5,1,3],![0,4,2,5,1,3],![0,4,5,2,1,3],
    ![4,0,2,5,1,3],![4,0,5,2,1,3],![4,5,0,2,1,3]]
def equalityEquiv (p : Fin 6) : Equiv.Perm (Fin 6) where
  toFun := equalityOrder p
  invFun := equalityInverse p
  left_inv := by
    have h : ∀ p i,equalityInverse p (equalityOrder p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i,equalityOrder p (equalityInverse p i)=i := by decide
    exact h p

def equalityPrefix (u v : Bool) (x : Fin 2 → Bool) : Fin 6 → Bool :=
  Fin.cons u (Fin.cons (!u) (Fin.cons v (Fin.cons (!v) x)))
def equalityFirstWord (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) : Fin 4 → Bool :=
  fun i => equalityPrefix u v x ((equalityEquiv p).symm (Fin.castAdd 2 i))
def equalitySecondWord (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) : Fin 2 → Bool :=
  fun i => equalityPrefix u v x ((equalityEquiv p).symm (Fin.natAdd 4 i))

theorem equalityFirstWord_eq (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) :
    equalityFirstWord p u v x=insertPair p u v x := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

variable {K : Type*} [CommSemiring K]
def equalitySignature : Signature K 2 := fun x => Signature.equality (x 0) (x 1)

theorem equalitySecondWord_value (p : Fin 6) (u v : Bool) (x : Fin 2 → Bool) :
    (equalitySignature : Signature K 2) (equalitySecondWord p u v x)=Signature.equality u v := by
  fin_cases p <;> cases u <;> cases v <;> rfl

def equalityContract (f : Signature K 4) (p : Fin 6) : Signature K 2 :=
  Signature.contract Signature.equality (Tensor.reindex (portEquiv p).symm f)

noncomputable def equalityLoopNetwork (f : Signature K 4) (p : Fin 6) : Network K 2 :=
  ((reorderNetwork ((singleVertexNetwork f).tensor (singleVertexNetwork equalitySignature))
    (equalityEquiv p).symm).contract Signature.disequality).contract Signature.disequality

theorem equalityLoopNetwork_denote (f : Signature K 4) (p : Fin 6) :
    (equalityLoopNetwork f p).denote=equalityContract f p := by
  rw [equalityLoopNetwork,Network.denote_contract,Network.denote_contract,reorderNetwork_denote,
    Network.denote_tensor,singleVertexNetwork_denote,singleVertexNetwork_denote]
  funext x
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  change
    (f (equalityFirstWord p false false x)*equalitySignature (equalitySecondWord p false false x)+
      f (equalityFirstWord p true false x)*equalitySignature (equalitySecondWord p true false x))+
    (f (equalityFirstWord p false true x)*equalitySignature (equalitySecondWord p false true x)+
      f (equalityFirstWord p true true x)*equalitySignature (equalitySecondWord p true true x)) = _
  simp only [equalitySecondWord_value,equalityFirstWord_eq]
  simp [Signature.equality,equalityContract,Signature.contract_equality,Tensor.reindex_apply,insertPair]
  rfl

def loopResources (f : Signature K 4) : SignatureFamily K := {⟨4,f⟩,⟨2,equalitySignature⟩}

theorem equalityContract_realizes (f : Signature K 4) (p : Fin 6) :
    Gadget.Realizes (loopResources f) .disequality (equalityContract f p) := by
  rw [←equalityLoopNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    change (⟨_,(Network.tensorFinite (singleVertexNetwork f) (singleVertexNetwork equalitySignature)).vertex
      ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)⟩ : AnySignature K) ∈ loopResources f
    cases (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v <;>
      simp [loopResources,Network.tensorFinite,singleVertexNetwork]
  · intro e
    refine Fin.cases rfl (fun e => ?_) e
    refine Fin.cases rfl (fun e => ?_) e
    exact Fin.elim0 e

end Holant.Certificates.FourthRootOdd
