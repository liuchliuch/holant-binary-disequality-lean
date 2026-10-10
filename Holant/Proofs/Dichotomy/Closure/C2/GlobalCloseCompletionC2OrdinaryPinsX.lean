import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationChain
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedAlgebra

/-! An endpoint and two live mixed coefficients of an actual ordinary
complementary-even q4 give scalar X using the actual two pins. The three
binary caps are diag(a,c), anti(c,d), diag(a,d); their literal ordinary path
is a*c*d*X, with no quotient or root-of-unity case. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPinsX
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain
open OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (seriesOrder)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] {s : ℕ} {arity : ℕ→ℕ}
variable {H : (i : Fin s)→Signature K (arity i.val)}

@[simp] private theorem cons2_five (u v : Bool) (x : Fin 4→Bool) :
    (Fin.cons u (Fin.cons v x) : Fin 6→Bool) 5=x 3 := rfl

def pinOrder (choice : Fin 3) : Equiv.Perm (Fin 6) where
  toFun := (![![0,4,2,5,1,3],![0,2,4,5,1,3],![0,4,5,2,1,3]] : Fin 3→Fin 6→Fin 6) choice
  invFun := (![![0,4,2,5,1,3],![0,4,1,5,2,3],![0,4,3,5,1,2]] : Fin 3→Fin 6→Fin 6) choice
  left_inv := by fin_cases choice <;> decide
  right_inv := by fin_cases choice <;> decide

def cap (N : Macro H 4) (pins : Bool→Macro H 1) (choice : Fin 3) : Macro H 2 :=
  (((N.tensor ((pins false).tensor (pins (decide (choice=1))))).reindex (pinOrder choice)).contract).contract

def diagonal (a b : K) : Binary (K:=K) := fun u v => if u=v then (if u then b else a) else 0

def anti (a b : K) : Binary (K:=K) := fun u v => if u=v then 0 else (if u then b else a)

def capMatrix (a c d : K) (choice : Fin 3) : Binary (K:=K) :=
  if choice=0 then diagonal a c else if choice=1 then anti c d else diagonal a d

theorem cap_denote (N : Macro H 4) (pins : Bool→Macro H 1) (a b c d : K)
    (form : N.network.denote=T.normal a b c d)
    (pinValues : ∀p,(pins p).network.denote=QuaternaryUnaryAccess.pin p) (choice : Fin 3) :
    (cap N pins choice).network.denote=binarySignature (capMatrix a c d choice) := by
  funext x
  fin_cases choice <;> cases h0 : x 0 <;> cases h1 : x 1
  all_goals simp [cap,pinOrder,Macro.contract_denote,Macro.reindex_denote,Macro.tensor_denote,
    Signature.tensor_apply,Tensor.reindex,form,pinValues,QuaternaryUnaryAccess.pin,
    T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
    binarySignature,capMatrix,diagonal,anti,h0,h1]

def series (L R : Macro H 2) : Macro H 2 := ((L.tensor R).reindex C.seriesOrder).contract

theorem series_denote (L R : Macro H 2) (A B : Binary (K:=K))
    (left : L.network.denote=binarySignature A) (right : R.network.denote=binarySignature B) :
    (series L R).network.denote=binarySignature (A*B) :=
  OrdinaryTargetInterpolationChain.seriesI_denote L.network R.network A B left right

def network (N : Macro H 4) (pins : Bool→Macro H 1) : Macro H 2 :=
  series (series (cap N pins 0) (cap N pins 1)) (cap N pins 2)

theorem denote (N : Macro H 4) (pins : Bool→Macro H 1) (a b c d : K)
    (form : N.network.denote=T.normal a b c d)
    (pinValues : ∀p,(pins p).network.denote=QuaternaryUnaryAccess.pin p) :
    (network N pins).network.denote=fun x=>a*c*d*Signature.disequality (x 0) (x 1) := by
  have left := cap_denote N pins a b c d form pinValues 0
  have middle := cap_denote N pins a b c d form pinValues 1
  have right := cap_denote N pins a b c d form pinValues 2
  rw [network,series_denote _ _ _ _ (series_denote _ _ _ _ left middle) right]
  change binarySignature ((diagonal a c * anti c d) * diagonal a d)=_
  have matrix : (diagonal a c * anti c d) * diagonal a d=(a*c*d) • X := by
    have entry (A B : Binary (K:=K)) (u v : Bool) :
        (A*B) u v=A u false*B false v+A u true*B true v := by
      rw [Matrix.mul_apply,Fintype.sum_bool]
      exact add_comm _ _
    ext u v
    cases u <;> cases v
    all_goals rw [entry,entry,entry]
    · change (a*0+0*d)*a+(a*c+0*0)*0=(a*c*d)*0
      ring
    · change (a*0+0*d)*0+(a*c+0*0)*d=(a*c*d)*1
      ring
    · change (0*0+c*d)*a+(0*c+c*0)*0=(a*c*d)*1
      ring
    · change (0*0+c*d)*0+(0*c+c*0)*d=(a*c*d)*0
      ring
  rw [matrix]
  rfl

def output (N : Macro H 4) (pins : Bool→Macro H 1) (a b c d : K)
    (ha : a≠0) (hc : c≠0) (hd : d≠0)
    (form : N.network.denote=T.normal a b c d)
    (pinValues : ∀p,(pins p).network.denote=QuaternaryUnaryAccess.pin p) :
    GlobalCloseCompletionOrdinaryXAdjoin.Output H where
  network := (network N pins).network
  labels := (network N pins).labels
  exact := (network N pins).exact
  ordinary := (network N pins).edges
  scalar := a*c*d
  nonzero := mul_ne_zero (mul_ne_zero ha hc) hd
  denote := denote N pins a b c d form pinValues

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPinsX
end
