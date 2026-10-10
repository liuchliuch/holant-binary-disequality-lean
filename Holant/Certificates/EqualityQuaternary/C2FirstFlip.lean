import Holant.Certificates.EqualityQuaternary.CountedNetwork
import Holant.Certificates.EqualityQuaternary.C2OneCopy

/-! One literal equality attachment reverses every complementary Walsh-block
sign, and keeps exactly the same number of original-q vertices. -/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant Holant.Marked Holant.Tractable
open Holant.Marked.SupportAtlas
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat Representatives
open Holant.Projective.CyclicDressing
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def firstMask : Word := ![true,false,false,false]
def firstFlip (q : Signature Scalar 4) : Signature Scalar 4 := Flip.value q firstMask

def flipWiring : Equiv.Perm (Fin 6) where
  toFun := ![0,5,4,1,2,3]
  invFun := ![0,3,4,5,2,1]
  left_inv := by decide
  right_inv := by decide

def firstFlipNetwork (N : Network Scalar 4) : Network Scalar 4 :=
  (reorderNetwork (N.tensor Counted.equality) flipWiring.symm).contract Signature.disequality

theorem firstFlip_allowed {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : Counted.Allowed q N) : Counted.Allowed q (firstFlipNetwork N) :=
  ((h.tensor (Counted.equality_allowed q)).reorder flipWiring.symm).contract

theorem firstFlip_copies (N : Network Scalar 4) : Counted.copies (firstFlipNetwork N)=Counted.copies N := by
  simp [firstFlipNetwork]

theorem flip_left_word (a : Bool) (w : Word) :
    (fun i : Fin 4 => (Fin.cons a (Fin.cons (!a) w) : Fin 6 → Bool)
      (flipWiring.symm (Fin.castAdd 2 i))) = ![a,w 1,w 2,w 3] := by
  funext i; fin_cases i <;> rfl
theorem flip_right_word (a : Bool) (w : Word) :
    (fun i : Fin 2 => (Fin.cons a (Fin.cons (!a) w) : Fin 6 → Bool)
      (flipWiring.symm (Fin.natAdd 4 i))) = ![w 0,!a] := by
  funext i; fin_cases i <;> rfl

theorem firstFlip_denote (N : Network Scalar 4) : (firstFlipNetwork N).denote=firstFlip N.denote := by
  rw [firstFlipNetwork,Network.denote_contract,reorderNetwork_denote,
    Network.denote_tensor,Counted.equality_denote]
  funext w
  have hw : xorWord w firstMask = ![!(w 0),w 1,w 2,w 3] := by
    funext i; fin_cases i <;> simp [xorWord,firstMask]
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply,
    ]
  have hl0 := flip_left_word false w
  have hl1 := flip_left_word true w
  have hr0 := flip_right_word false w
  have hr1 := flip_right_word true w
  simp only [Bool.not_false,Bool.not_true] at hl0 hl1 hr0 hr1
  rw [hl0,hl1,hr0,hr1]
  cases h0 : w 0 <;> simp [firstFlip,Flip.value,hw,kernelSignature,Signature.equality,h0]

theorem firstFlip_onePort (q : Signature Scalar 4) :
    firstFlip q=onePort q 0 Signature.equality := by
  funext w
  have he : onePort q 0 Signature.equality w=q (Function.update w 0 (!(w 0))) := by
    have hs : scale (1 : Scalar) Signature.disequality=Signature.disequality := by
      funext a b; simp [scale]
    have h := one_flip_action q 1 0 w
    rw [hs] at h
    simpa [onePort] using h
  rw [he]
  apply congrArg q
  funext i
  fin_cases i <;> simp [firstFlip,Flip.value,xorWord,firstMask]

def walshBasis : InvertibleKernel := ⟨P,Pinv,P_Pinv,Pinv_P⟩

theorem firstFlip_walsh (q : Signature Scalar 4) (w : Word) :
    walsh (firstFlip q) w=sign (w 0)*walsh q w := by
  rw [firstFlip_onePort]
  have hs : sectorTransfer walshBasis Signature.equality=
      Projective.CyclicPhasePencil.phase (-1) := by
    funext a b
    cases a <;> cases b <;>
      norm_num [sectorTransfer,conjugate,walshBasis,InvertibleKernel.symm,Kernel.mul_apply,
        Signature.equality,Signature.disequality,P,Pinv,Projective.CyclicPhasePencil.phase,
        Projective.CyclicPhasePencil.diagonal]
  have ht := congrFun (sector_onePort_action walshBasis q Signature.equality 0) w
  change walsh (onePort q 0 Signature.equality) w = _ at ht
  rw [ht,hs]
  have hk : (fun j : Fin 4 => if j=0 then Projective.CyclicPhasePencil.phase (-1 : Scalar)
      else Signature.equality) = (fun j => (1 : Scalar) •
        Projective.CyclicPhasePencil.phase (if j=0 then (-1 : Scalar) else 1)) := by
    funext j a b
    by_cases hj : j=0 <;> cases a <;> cases b <;>
      simp [hj,Projective.CyclicPhasePencil.phase,Projective.CyclicPhasePencil.diagonal,Signature.equality]
  rw [hk,phase_action]
  change (∏ i : Fin 4,(1:Scalar))*(∏ i : Fin 4,(if i=0 then (-1:Scalar) else 1)^(if w i then 1 else 0))*walsh q w=_
  simp only [Fin.prod_univ_succ]
  cases h0 : w 0 <;> simp [sign,h0]

theorem proper_reindex {q : Signature Scalar 4} (hp : ProperFactor q) (e : Equiv.Perm (Fin 4)) :
    ProperFactor (Tensor.reindex e q) := by
  obtain ⟨m,n,hm,hn,p,f,g,h⟩ := hp
  refine ⟨m,n,hm,hn,p.trans e,f,g,?_⟩
  rw [h,Tensor.reindex_trans]

theorem prime_reindex {q : Signature Scalar 4} (hp : TensorPrime q) (e : Equiv.Perm (Fin 4)) :
    TensorPrime (Tensor.reindex e q) := by
  constructor
  · intro hz
    have hh := congrArg (Tensor.reindex e.symm) hz
    simp only [Tensor.reindex_symm] at hh
    exact hp.1 hh
  · intro hf
    have hh := proper_reindex hf e.symm
    rw [Tensor.reindex_symm] at hh
    exact hp.2 hh

end Holant.Certificates.EqualityQuaternary.C2
