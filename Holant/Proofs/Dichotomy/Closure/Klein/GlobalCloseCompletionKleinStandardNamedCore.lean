import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardCoreAffine
import Holant.ReedMuller.CharacterFlat.NoInverse

/-! Exact identification of the proved algebraic six-port affine tensor with
the existing manuscript H6 named core, including its ordered Bell signs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardNamedCore
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.CharacterFlat
namespace C
export GlobalCloseCompletionKleinStandardCoreAffine (bell core affine_core)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem bell_complex (d l a b : Bool) :
    (C.bell d l a b : ℂ)=bellKernel (bitValue (ZMod 2) d) (bitValue (ZMod 2) l) a b := by
  cases d <;> cases l <;> cases a <;> cases b <;>
    norm_num [C.bell,bellKernel,parityKernel,sign,intSign,bit,boolEquiv,bitValue] <;> decide

theorem core_complex : (fun x=>(C.core x : ℂ))=hCore := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion (C.core x)=hCore x
  have mapped (d l a b : Bool) : CyclicBoundary.AlgebraicRepresentatives.inclusion (C.bell d l a b)=
      bellKernel (bitValue (ZMod 2) d) (bitValue (ZMod 2) l) a b := bell_complex d l a b
  simp only [C.core,hCore,map_add,map_mul,mapped,bitValue_false,bitValue_true]

theorem named_core_affine : ∃f : Signature AlgebraicComplex 6,Affine f ∧ (fun x=>(f x : ℂ))=hCore :=
  ⟨C.core,C.affine_core,core_complex⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardNamedCore
end
