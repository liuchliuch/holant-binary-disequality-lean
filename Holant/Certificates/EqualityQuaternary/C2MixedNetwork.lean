import Holant.Certificates.EqualityQuaternary.CountedNetwork
import Holant.Projective.CyclicQuaternary.Contraction

/-! The three literal two-copy X-I-X joins from the mixed-sign C2 proof.
The construction accepts an already dressed original-q network, preserving
all its actual vertices and exactly doubling its original-q count.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2.Mixed
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def order : Fin 3 → Fin 12 → Fin 12 :=
  ![![0,8,4,9,1,10,5,11,2,3,6,7],
    ![0,8,4,9,2,10,6,11,1,3,5,7],
    ![0,8,4,9,3,10,7,11,1,2,5,6]]
def inverse : Fin 3 → Fin 12 → Fin 12 :=
  ![![0,4,8,9,2,6,10,11,1,3,5,7],
    ![0,8,4,9,2,10,6,11,1,3,5,7],
    ![0,8,9,4,2,10,11,6,1,3,5,7]]
def wiring (p : Fin 3) : Equiv.Perm (Fin 12) where
  toFun := order p
  invFun := inverse p
  left_inv := by
    have h : ∀ p i,inverse p (order p i)=i := by decide
    exact h p
  right_inv := by
    have h : ∀ p i,order p (inverse p i)=i := by decide
    exact h p

def output (q : Signature Scalar 4) (p : Fin 3) : Signature Scalar 4 := fun w =>
  ∑ a : Bool, ∑ b : Bool,
    q (join p false a b (w 0) (w 1))*q (join p false a b (w 2) (w 3))

def network (N : Network Scalar 4) (p : Fin 3) : Network Scalar 4 :=
  ((((reorderNetwork ((N.tensor N).tensor (Counted.equality.tensor Counted.equality))
    (wiring p).symm).contract Signature.disequality).contract Signature.disequality).contract
      Signature.disequality).contract Signature.disequality

theorem allowed {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : Counted.Allowed q N) (p : Fin 3) : Counted.Allowed q (network N p) := by
  exact (((((h.tensor h).tensor ((Counted.equality_allowed q).tensor
    (Counted.equality_allowed q))).reorder (wiring p).symm).contract).contract).contract.contract

theorem copies (N : Network Scalar 4) (p : Fin 3) :
    Counted.copies (network N p)=2*Counted.copies N := by
  simp [network,two_mul]

def wordPrefix (a b c d : Bool) (w : Word) : Fin 12 → Bool :=
  Fin.cons a (Fin.cons (!a) (Fin.cons b (Fin.cons (!b)
    (Fin.cons c (Fin.cons (!c) (Fin.cons d (Fin.cons (!d) w)))))))

theorem four_contract (f : Signature Scalar 12) (w : Word) :
    Signature.contract Signature.disequality (Signature.contract Signature.disequality
      (Signature.contract Signature.disequality (Signature.contract Signature.disequality f))) w =
      ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, ∑ d : Bool, f (wordPrefix a b c d w) := by
  simp only [Signature.contract_disequality,Fintype.sum_bool,wordPrefix,Bool.not_false,Bool.not_true]
  ac_rfl

theorem left_word (p : Fin 3) (a b c d : Bool) (w : Word) :
    (fun i : Fin 4 => wordPrefix a b c d w
      ((wiring p).symm (Fin.castAdd 4 (Fin.castAdd 4 i)))) =
      join p false a c (w 0) (w 1) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

theorem right_word (p : Fin 3) (a b c d : Bool) (w : Word) :
    (fun i : Fin 4 => wordPrefix a b c d w
      ((wiring p).symm (Fin.castAdd 4 (Fin.natAdd 4 i)))) =
      join p false b d (w 2) (w 3) := by
  funext i
  fin_cases p <;> fin_cases i <;> rfl

theorem first_equality (p : Fin 3) (a b c d : Bool) (w : Word) :
    kernelSignature Signature.equality (fun i : Fin 2 => wordPrefix a b c d w
      ((wiring p).symm (Fin.natAdd 8 (Fin.castAdd 2 i)))) =
      Signature.equality a b := by
  fin_cases p <;> cases a <;> cases b <;> rfl

theorem second_equality (p : Fin 3) (a b c d : Bool) (w : Word) :
    kernelSignature Signature.equality (fun i : Fin 2 => wordPrefix a b c d w
      ((wiring p).symm (Fin.natAdd 8 (Fin.natAdd 2 i)))) =
      Signature.equality c d := by
  fin_cases p <;> cases c <;> cases d <;> rfl

theorem denote (N : Network Scalar 4) (p : Fin 3) :
    (network N p).denote=output N.denote p := by
  rw [network,Network.denote_contract,Network.denote_contract,Network.denote_contract,
    Network.denote_contract,reorderNetwork_denote,Network.denote_tensor,
    Network.denote_tensor,Network.denote_tensor,Counted.equality_denote]
  funext w
  rw [four_contract]
  simp only [Tensor.reindex_apply,Signature.tensor_apply,left_word,right_word,
    first_equality,second_equality]
  simp [Signature.equality,output]

theorem realizes {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : Counted.Allowed q N) (F : SignatureFamily Scalar)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F) (p : Fin 3) :
    Gadget.Realizes F .disequality (output N.denote p) := by
  rw [←denote]
  exact (allowed h p).realizes F hq hI

end Holant.Certificates.EqualityQuaternary.C2.Mixed
