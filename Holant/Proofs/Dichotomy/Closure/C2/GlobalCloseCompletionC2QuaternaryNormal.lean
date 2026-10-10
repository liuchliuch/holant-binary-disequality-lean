import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CurrentComplement
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinTwistedAlgebra

/-! The normal complementary-even q4 form is recovered from the actual
stable tensor, with its four literal coefficients and ordered ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2QuaternaryNormal
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

theorem complementary_even (f : Signature K 4) (he : EvenSupport f)
    (hc : ∀x,f x=f (fun i=>!(x i))) :
    f=T.normal (f ![false,false,false,false]) (f ![false,false,true,true])
      (f ![false,true,false,true]) (f ![false,true,true,false]) := by
  have odd (b c d e : Bool) (h : weight (![b,c,d,e] : Fin 4→Bool)%2≠0) : f ![b,c,d,e]=0 := he _ h
  have comp (b c d e : Bool) : f ![b,c,d,e]=f ![!b,!c,!d,!e] := by
    have eqn := hc ![b,c,d,e]
    convert eqn using 1
    congr 1
    funext i
    fin_cases i <;> rfl
  funext x
  rw [word_eta x]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3
  all_goals simp [T.normal,table]
  all_goals first
    | rfl
    | exact odd _ _ _ _ (by decide)
    | simpa using comp true false false true
    | simpa using comp true false true false
    | simpa using comp true true false false
    | simpa using comp true true true true

variable [NumberField K]

theorem current_normal (F : SignatureFamily K) (torsion : ResidualTorsion F)
    (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
    (f : Signature K 4) (he : EvenSupport f)
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    f=T.normal (f ![false,false,false,false]) (f ![false,false,true,true])
      (f ![false,true,false,true]) (f ![false,true,true,false]) :=
  complementary_even f he (GlobalCloseCompletionC2CurrentComplement.current_complement
    F torsion hI cardTwo f stable)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2QuaternaryNormal
end
