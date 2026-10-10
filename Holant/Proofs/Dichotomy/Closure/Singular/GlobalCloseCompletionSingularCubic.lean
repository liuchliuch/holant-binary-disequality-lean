import Holant.Proofs.Dichotomy.Retained.StableDenseGaugeUnary
import Holant.Dihedral.CompatibleClosure.ActualReindex

/-! A dense parity quaternary and the actual scaled computational pins yield
an actual symmetric full even cubic. Every correction is a pinned copy of that
same cubic, followed by the retained identity, and every scalar is kept. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCubic
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.LocalDrafts.FinitePGL2.Stabilization
namespace Pn
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugePinAccess
  (scaledPin slice slice_value slice_actual)
end Pn
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def parity (x : Fin 3→Bool) : Bool := (x 0 ^^ x 1) ^^ x 2

def cubic (a b c d : K) : Signature K 3 := fun x =>
  if parity x then 0 else if x 0 then (if x 1 then d else c) else (if x 1 then b else a)

def symmetric (a b : K) : Signature K 3 := cubic a b b b

def pinOrder : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv := by decide
  right_inv := by decide

def pinFirst (f : Signature K 3) (u : Signature K 1) : Signature K 2 :=
  Signature.contract Signature.disequality (Tensor.reindex pinOrder (Signature.tensor f u))

theorem pinFirst_value (f : Signature K 3) (c : K) (x : Fin 2→Bool) :
    pinFirst f (Pn.scaledPin true c) x=c*f ![false,x 0,x 1] := by
  rw [pinFirst,Signature.contract_disequality]
  have left (a d : Bool) :
      (fun i : Fin 3=>(Fin.cons a (Fin.cons d x) : Fin 4→Bool)
        (pinOrder (Fin.castAdd 1 i)))=![a,x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  have right (a d : Bool) :
      (fun i : Fin 1=>(Fin.cons a (Fin.cons d x) : Fin 4→Bool)
        (pinOrder (Fin.natAdd 3 i)))=fun _=>d := by
    funext i
    fin_cases i
    rfl
  simp only [Tensor.reindex_apply,Signature.tensor_apply,left,right]
  simp [Pn.scaledPin,mul_comm]

theorem pinFirst_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (f : Signature K 3) (u : Signature K 1)
    (hf : Gadget.Realizes F .disequality f) (hu : Gadget.Realizes F .disequality u) :
    Gadget.Realizes F .disequality (pinFirst f u) := by
  have ht := realizes_tensor F .disequality f u hf hu
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ ht pinOrder.symm
  simp only [Equiv.symm_symm] at hr
  exact realizes_contract_exact_of_identity F hI _ hr

def diagonal (a b : K) : Signature K 2 := fun x=>
  if x 0=x 1 then (if x 0 then b else a) else 0

def antidiagonal (a b : K) : Signature K 2 := fun x=>
  if x 0= !x 1 then (if x 0 then b else a) else 0

theorem pin_cubic (a b c d v : K) (i : Fin 3) :
    pinFirst (Tensor.reindex (Equiv.swap 0 i) (cubic a b c d)) (Pn.scaledPin true v)=
      diagonal (v*a) (v*(![b,c,d] i)) := by
  funext x
  rw [pinFirst_value]
  fin_cases i <;> cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Tensor.reindex_apply,Equiv.swap_apply_def,cubic,parity,diagonal,h0,h1]

theorem flip_diagonal (a b : K) :
    spliceTensor (diagonal a b) OrdinaryNormalization.identitySignature 1=antidiagonal a b := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [spliceTensor,diagonal,antidiagonal,OrdinaryNormalization.identitySignature,
      Signature.equality,Signature.disequality,Function.update,h0,h1]

theorem splice_antidiagonal {n : ℕ} (f : Signature K n) (a b : K)
    (i : Fin n) (x : Fin n→Bool) :
    spliceTensor f (antidiagonal a b) i x=(if x i then b else a)*f x := by
  have hx : Function.update x i (x i)=x := Function.update_eq_self i x
  cases hi : x i
  all_goals
    rw [hi] at hx
    simp [spliceTensor,antidiagonal,Signature.disequality,hi,hx,mul_comm]

theorem correction_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (a b c d v : K) (i : Fin 3)
    (hf : Gadget.Realizes F .disequality (cubic a b c d))
    (hv : Gadget.Realizes F .disequality (Pn.scaledPin true v)) :
    Gadget.Realizes F .disequality (antidiagonal (v*a) (v*(![b,c,d] i))) := by
  have hr := Holant.Dihedral.CompatibleClosure.realizes_reindex F .disequality _ hf
    (Equiv.swap 0 i).symm
  simp only [Equiv.symm_symm] at hr
  have hp := pinFirst_actual F hI _ _ hr hv
  rw [pin_cubic] at hp
  rw [←flip_diagonal]
  exact realizes_splice F _ _ hp (Gadget.realizes_of_mem F .disequality _ hI) 1

def corrected (a b c d v : K) : Signature K 3 :=
  spliceTensor (spliceTensor (spliceTensor (cubic a b c d)
    (antidiagonal (v*a) (v*b)) 0) (antidiagonal (v*a) (v*c)) 1)
    (antidiagonal (v*a) (v*d)) 2

theorem corrected_value (a b c d v : K) :
    corrected a b c d v=symmetric (v^3*a^4) (v^3*a*b*c*d) := by
  funext x
  simp only [corrected,splice_antidiagonal]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [cubic,symmetric,parity,h0,h1,h2] <;> ring

theorem corrected_actual (F : SignatureFamily K) (hI : RetainsIdentity F)
    (a b c d v : K) (hf : Gadget.Realizes F .disequality (cubic a b c d))
    (hv : Gadget.Realizes F .disequality (Pn.scaledPin true v)) :
    Gadget.Realizes F .disequality (symmetric (v^3*a^4) (v^3*a*b*c*d)) := by
  rw [←corrected_value]
  exact realizes_splice F _ _
    (realizes_splice F _ _ (realizes_splice F _ _ hf
      (correction_actual F hI a b c d v 0 hf hv) 0)
      (correction_actual F hI a b c d v 1 hf hv) 1)
    (correction_actual F hI a b c d v 2 hf hv) 2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSingularCubic
end
