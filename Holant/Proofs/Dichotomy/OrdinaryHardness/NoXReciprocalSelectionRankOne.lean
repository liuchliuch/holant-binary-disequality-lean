import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXSeparateSignedSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned

/-! Separate the two orientations of a rank-one support without a flip
resource. The resulting unsigned binary is a literal weighted anti when both
orientations occur. Its odd/even incidence is handled separately. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOne
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port word)
namespace P
export NoXSeparateSignedProjection (rowPort signedCount coefficient_value)
end P
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] {n : ℕ}

def ports (x y : Fin n→Bool) (i : Fin n) : Port 1 :=
  if x i=y i then .inl (x i) else .inr (0,x i)

def projected (f : Signature K n) (x y : Fin n→Bool) : Signature K 2 :=
  fun z=>f (T.substitute (P.rowPort (ports x y)) z)

theorem word_left (x y : Fin n→Bool) :
    T.substitute (P.rowPort (ports x y)) ![false,true]=x := by
  funext i
  cases hx:x i <;> cases hy:y i <;> simp [T.substitute,P.rowPort,ports,hx,hy]

theorem word_right (x y : Fin n→Bool) :
    T.substitute (P.rowPort (ports x y)) ![true,false]=y := by
  funext i
  cases hx:x i <;> cases hy:y i <;> simp [T.substitute,P.rowPort,ports,hx,hy]

variable (f : Signature K n) (x y : Fin n→Bool)
variable (support : ∀z,f z≠0→z=x ∨ z=y)
variable (positive negative : Fin n)
variable (hp : x positive=false ∧ y positive=true)
variable (hn : x negative=true ∧ y negative=false)
include support hp hn in
theorem equal_zero (bit : Bool) : projected f x y (fun _=>bit)=0 := by
  by_contra live
  rcases support _ live with h|h
  · cases bit
    · have eqn:=congrFun h negative
      simp [T.substitute,P.rowPort,ports,hn] at eqn
    · have eqn:=congrFun h positive
      simp [T.substitute,P.rowPort,ports,hp] at eqn
  · cases bit
    · have eqn:=congrFun h positive
      simp [T.substitute,P.rowPort,ports,hp] at eqn
    · have eqn:=congrFun h negative
      simp [T.substitute,P.rowPort,ports,hn] at eqn

include support hp hn in
theorem anti : projected f x y=NoXWeightedAntiSigned.anti (f x) (f y) := by
  funext z
  have hz:z=![z 0,z 1] := by funext i;fin_cases i <;> rfl
  rw [hz]
  cases h0:z 0 <;> cases h1:z 1
  · have hv : (![false,false] : Fin 2→Bool)=(fun _=>false) := by funext i;fin_cases i <;> rfl
    rw [hv]
    exact equal_zero f x y support positive negative hp hn false
  · change f (T.substitute (P.rowPort (ports x y)) ![false,true])=f x
    rw [word_left]
  · change f (T.substitute (P.rowPort (ports x y)) ![true,false])=f y
    rw [word_right]
  · have hv : (![true,true] : Fin 2→Bool)=(fun _=>true) := by funext i;fin_cases i <;> rfl
    rw [hv]
    exact equal_zero f x y support positive negative hp hn true

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalSelectionRankOne
end
