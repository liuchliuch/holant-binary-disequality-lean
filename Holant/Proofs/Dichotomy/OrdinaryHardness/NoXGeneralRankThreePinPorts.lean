import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateEvenReflection
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralLocalMasks
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreePorts

/-! Exact rank-two signed support of every coordinate pin of rank three.
Each surviving character is the merger of exactly two original characters;
separately odd original counts become separately even on every such face. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankThreePinPorts
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
namespace P
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSparseRankThreePorts (port word_code)
end P
namespace C
export OrdinaryNegativeSparseMixingAlpha (codeThree codeSeven codeThree_affine)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 32768
set_option Elab.async false

theorem cons_vector (bit : Bool) (x : Word 2) : Fin.cons bit x=![bit,x 0,x 1]:=by
  funext i
  fin_cases i <;> rfl

def input (i : Fin 3) (bit : Bool) (x : Word 2) : Word 3:=
  NoXLocalPermutation.word (Equiv.swap 0 i) (Fin.cons bit x)

def name (i : Fin 3) (bit : Bool) : Fin 7→Port 3:=
  ![![.inl bit,.inr (0,false),.inr (1,false),.inr (2,false),.inr (1,bit),.inr (0,bit),.inr (2,bit)],
    ![.inr (0,false),.inl bit,.inr (1,false),.inr (1,bit),.inr (2,false),.inr (0,bit),.inr (2,bit)],
    ![.inr (1,false),.inr (0,false),.inl bit,.inr (0,bit),.inr (1,bit),.inr (2,false),.inr (2,bit)]] i

def left (i : Fin 3) : Fin 3→Fin 7:=![![1,2,3],![0,2,4],![1,0,5]] i
def right (i : Fin 3) : Fin 3→Fin 7:=![![5,4,6],![5,3,6],![3,4,6]] i

def mapPort (i : Fin 3) (bit : Bool) (q : Port 7) : Port 3:=
  match q with
  | .inl b=>.inl b
  | .inr (j,b)=>match name i bit j with
    | .inl c=>.inl (b ^^ c)
    | .inr (k,c)=>.inr (k,b ^^ c)

def ports {n : ℕ} (ps : Fin n→Port 7) (i : Fin 3) (bit : Bool) : Fin n→Port 3:=
  fun j=>mapPort i bit (ps j)

theorem word_value {n : ℕ} (ps : Fin n→Port 7) (i : Fin 3) (bit : Bool) (x : Word 2) :
    word (ports ps i bit) (C.codeThree x)=word ps (C.codeSeven (input i bit x)):=by
  funext v
  cases hp : ps v with
  | inl b=>simp [ports,mapPort,OrdinaryNegativeSignedPortsCore.word,hp]
  | inr q=>
      rcases q with ⟨j,b⟩
      fin_cases i <;> fin_cases j <;> cases b <;> cases bit <;> cases hx0 : x 0 <;> cases hx1 : x 1 <;>
        simp [ports,mapPort,name,OrdinaryNegativeSignedPortsCore.word,C.codeThree,C.codeSeven,input,NoXLocalPermutation.word,
          hp,hx0,hx1,Equiv.swap_apply_def,cons_vector]

theorem count {n : ℕ} (ps : Fin n→Port 7) (i q : Fin 3) (bit sgn : Bool) :
    P.signedCount (ports ps i bit) q sgn=
      P.signedCount ps (left i q) sgn+P.signedCount ps (right i q) (sgn ^^ bit):=by
  rw [P.signedCount,P.signedCount,P.signedCount,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases hp : ps v with
  | inl b=>simp [ports,mapPort,hp]
  | inr a=>
      rcases a with ⟨j,b⟩
      fin_cases i <;> fin_cases q <;> fin_cases j <;> cases bit <;> cases sgn <;> cases b <;>
        simp [ports,mapPort,name,left,right,hp]

theorem even {n : ℕ} (ps : Fin n→Port 7) (odd : ∀q bit,Odd (P.signedCount ps q bit))
    (i q : Fin 3) (bit sgn : Bool) : Even (P.signedCount (ports ps i bit) q sgn):=by
  rw [count]
  exact (odd _ _).add_odd (odd _ _)

variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)

def chart (i : Fin 3) (bit : Bool) :
    SystematicSupport (pinMask f (D.ports i) bit) 2:=by
  let E:=NoXLocalPermutation.logical D (Equiv.swap 0 i)
  have first : E.ports 0=D.ports i:=by simp [E,NoXLocalPermutation.logical]
  exact first ▸ E.pinFirst bit

theorem chart_encode (i : Fin 3) (bit : Bool) (x : Word 2) :
    (chart D i bit).encode x=D.encode (input i bit x):=by
  simp [chart,SystematicSupport.pinFirst,NoXLocalPermutation.logical,input]

theorem code_value (i : Fin 3) (bit : Bool) (x : Word 2) :
    word (ports (P.port D) i bit) (C.codeThree x)=(chart D i bit).encode x:=by
  rw [word_value,P.word_code,chart_encode]

theorem affine_mask (odd : ∀q bit,Odd (P.signedCount (P.port D) q bit))
    (i : Fin 3) (bit : Bool)
    (square : Affine (fun x=>(pinMask f (D.ports i) bit x)^2))
    (localGood : LocalAffine (pinMask f (D.ports i) bit)) :
    Affine (pinMask f (D.ports i) bit):=
  NoXGeneralSeparateEvenReflection.affine_of_local (chart D i bit) (ports (P.port D) i bit)
    (fun q sgn=>even (P.port D) odd i q bit sgn) C.codeThree C.codeThree_affine
    (code_value D i bit) square localGood

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralRankThreePinPorts
end
