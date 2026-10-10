import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureClosedUniformMinimal
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceRecipe

/-! Canonical signed original-port names for the one-, two-, and three-rank
closed-support witnesses. The code maps are used only to evaluate the real
support chart, never as available XOR gates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseSmallPorts
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace A
export NoIPurePhaseIncidenceCore.C (codeThree codeSeven)
end A
namespace P
export NoIPurePhaseIncidenceRegularization.P (name inputs Transform)
export NoIPurePhaseIncidencePorts.P (value linearWord)
end P
namespace C
export OrdinaryNegativeAffineCharacters (coordinate_vector mask)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

def one (D : SystematicSupport f 1) (i : Fin n) : Port 1 :=
  let a:=D.encode (fun _=>false) i
  let b:=D.encode (fun _=>true) i
  if a=b then .inl a else .inr (0,a)

theorem one_value (D : SystematicSupport f 1) (z : Fin 1→Bool) : word (one D) z=D.encode z := by
  have hz : z=(fun _=>z 0) := by funext j;fin_cases j;rfl
  rw [hz]
  funext i
  cases h0:z 0 <;> cases ha:D.encode (fun _=>false) i <;> cases hb:D.encode (fun _=>true) i <;>
    simp [one,word,ha,hb]

def two (D : SystematicSupport f 2) (i : Fin n) : Port 3 :=
  let a:=D.encode ![false,false] i
  let b:=a ^^ D.encode ![true,false] i
  let c:=a ^^ D.encode ![false,true] i
  if b then (if c then .inr (2,a) else .inr (0,a))
  else if c then .inr (1,a) else .inl a

theorem two_value (D : SystematicSupport f 2) (z : Fin 2→Bool) :
    word (two D) (A.codeThree z)=D.encode z := by
  funext i
  have hh:=congrFun (D.affine ![true,false] ![false,true]) i
  have hx : AffinePhase.xor (![true,false] : Fin 2→Bool) ![false,true]=![true,true] := by decide
  have ho : AffinePhase.origin 2=(![false,false] : Fin 2→Bool) := by funext j;fin_cases j <;> rfl
  rw [hx,ho] at hh
  change D.encode ![true,true] i=
    (D.encode ![true,false] i ^^ (D.encode ![false,true] i ^^ D.encode ![false,false] i)) at hh
  have hz : z=![z 0,z 1] := by funext j;fin_cases j <;> rfl
  rw [hz]
  cases h0:z 0 <;> cases h1:z 1 <;>
    cases ha:D.encode ![false,false] i <;> cases hb:D.encode ![true,false] i <;>
    cases hc:D.encode ![false,true] i <;>
    simp [word,two,A.codeThree,ha,hb,hc,hh]

def rawName (D : SystematicSupport f 3) (i : Fin n) : Fin 8 :=
  let a:=D.encode (AffinePhase.origin 3) i
  P.name (a ^^ D.encode (AffinePhase.basis 0) i)
    (a ^^ D.encode (AffinePhase.basis 1) i) (a ^^ D.encode (AffinePhase.basis 2) i)

def three (D : SystematicSupport f 3) (i : Fin n) : Port 7 :=
  if h:rawName D i=0 then .inl (D.encode (AffinePhase.origin 3) i)
  else .inr (⟨(rawName D i).val-1,by have hlt:=(rawName D i).isLt;have hn:=(rawName D i).pos_iff_ne_zero.mpr h;omega⟩,
    D.encode (AffinePhase.origin 3) i)

theorem rawName_value (D : SystematicSupport f 3) (i : Fin n) (x : Fin 3→Bool) :
    Bool.xor (D.encode (AffinePhase.origin 3) i) (P.value (rawName D i) x)=D.encode x i := by
  apply Holant.ReedMuller.FlatNetwork.boolEquiv.injective
  change bitValue (ZMod 2) (D.encode (AffinePhase.origin 3) i ^^ P.value (rawName D i) x)=
    bitValue (ZMod 2) (D.encode x i)
  rw [C.coordinate_vector D i x]
  cases ha:D.encode (AffinePhase.origin 3) i <;>
    cases hb:D.encode (AffinePhase.basis 0) i <;> cases hc:D.encode (AffinePhase.basis 1) i <;>
    cases hd:D.encode (AffinePhase.basis 2) i <;>
    cases hx0:x 0 <;> cases hx1:x 1 <;> cases hx2:x 2 <;>
    norm_num [rawName,P.name,P.value,A.codeSeven,C.mask,TwoTranslate.dot,
      Fin.sum_univ_three,bitValue,ha,hb,hc,hd,hx0,hx1,hx2]
  all_goals decide

theorem three_value (D : SystematicSupport f 3) (x : Fin 3→Bool) :
    word (three D) (A.codeSeven x)=D.encode x := by
  funext i
  rw [←rawName_value D i x]
  simp only [word,three]
  split_ifs with h
  · simp [P.value,h]
  · simp [P.value,h]

theorem linearWord_pin (t : P.Transform) (x : Fin 3→Bool) : P.linearWord t x t.axis=false := by
  rcases t with ⟨a,u,v⟩
  fin_cases a <;> simp [P.linearWord,P.inputs,P.value]

theorem linearWord_affine (t : P.Transform) : TwoTranslate.IsAffineMap (P.linearWord t) := by
  intro x y
  funext i
  unfold P.linearWord
  by_cases h:P.inputs t i=0
  · simp [P.value,h,AffinePhase.xor]
  · have hn:=(P.inputs t i).pos_iff_ne_zero.mpr h
    have hl:=(P.inputs t i).isLt
    have hc:=congrFun (NoIPurePhaseAnchorRecipe.A.codeSeven_affine x y)
      (⟨(P.inputs t i).val-1,by omega⟩ : Fin 7)
    simpa [P.value,h,AffinePhase.xor] using hc


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseSmallPorts
end
