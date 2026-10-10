import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeDenseNetwork
import Holant.Proofs.Dichotomy.Main.PaperTerminalBridgeCancellationActual

/-! Full dense differing-products hardness from a genuine infinite-ratio
native antidiagonal output. All two diagonal parameters are selected from the
original coefficients, adjoined by proved interpolation, attached by the
explicit no-I network, and compiled back to the original whole table. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseInfinite
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export NativeAntiTargetSource (Output base)
end S
namespace A
export NativeAntiTargetAlgebra (anti)
end A
namespace E
export NativeAntiTargetPair (Extension produce)
end E
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (binarySignature)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [NumberField K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

structure Packet where
  first : K
  second : K
  extension : E.Extension H F first second
  output : S.Output extension.table 4
  applicable : EightVertexCancellationLocal.Applicable output.network.denote

variable (M : Signature K 4) (label : Fin s)
variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨4,M⟩)
variable (even : EvenSupport M) (dense : StableDenseParityAlgebra.Dense M)
variable (different : ¬PaperTerminalBridgeDenseOrders.EqualProducts M)
variable (N : S.Output H 2) (p q : K) (hp : p≠0) (hq : q≠0)
variable (infinite : ∀k : ℕ,0<k→(q/p)^k≠1)
variable (form : N.network.denote=C.binarySignature (A.anti p q))

include literal even dense different hp hq infinite form in
theorem packet_exists : Nonempty (Packet H F) := by
  obtain ⟨k,r,t,hr,ht,_choice,applicable⟩ := PaperTerminalBridgeDenseOrders.source M even dense different
  let E := E.produce H F N p q r t hp hq infinite form
  let out := PaperTerminalBridgeDenseNetwork.output E.table M k r t (E.old label) E.left E.right
    ((E.old_literal label).trans literal) E.left_literal E.right_literal
  refine ⟨⟨r,t,E,out,?_⟩⟩
  change EightVertexCancellationLocal.Applicable (PaperTerminalBridgeDenseNetwork.network M k r t).denote
  rw [PaperTerminalBridgeDenseNetwork.value]
  exact applicable

def packet : Packet H F :=
  (packet_exists H F M label literal even dense different N p q hp hq infinite form).some

variable {α : Type} {ea : Encoding α Bool} {count : α→ℕ}
def source (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding count ((S.base H F).evaluate F) := by
  let P := packet H F M label literal even dense different N p q hp hq infinite form
  exact Programme.compose
    (PaperTerminalBridgeCancellationActual.source P.extension.table F P.output P.applicable w)
    P.extension.source

include literal even dense different hp hq infinite form in
theorem countingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding ((S.base H F).evaluate F) := by
  intro α ea count w
  exact ⟨(source H F M label literal even dense different N p q hp hq infinite form w).reduction⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperTerminalBridgeDenseInfinite
end
