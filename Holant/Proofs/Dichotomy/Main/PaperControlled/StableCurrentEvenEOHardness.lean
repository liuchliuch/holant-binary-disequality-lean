import Holant.Proofs.Dichotomy.Main.PaperControlledHardness
import Holant.Proofs.Hardness.EOQuaternaryOriginalSource
import Holant.Proofs.Closure.ClosurePhysicalBridgeNetwork

/-! A negative EO graph output of the actual current palette yields a genuine
counting source at the frozen original-G endpoint. The selected-label adapter
and the rational-linear coefficient decoder are actual programmes. In
particular, the independently generated answer field of the algebraically
mapped extended palette is never identified with the fixed original field.
The final substitution is the programme saved by this same graph receipt. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.StableCurrentEvenEOHardness
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1

namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (N : Network AlgebraicComplex 4)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
  ClosurePhysicalBridge.RH.mapFamily (ClosurePhysicalBridge.algebraicEmbedding G) P.family)
variable (d : ClosurePhysicalBridge.NetworkGraphAccess G P
  (ClosurePhysicalBridge.algebraicEmbedding G) N labels)

abbrev originalEmbedding := OriginalFrozenForest.OriginalInput.embedding G
abbrev mappedOutput : Signature AlgebraicComplex 4 :=
  ClosurePhysicalBridge.RH.mapSignature (ClosurePhysicalBridge.algebraicEmbedding G) d.output
abbrev extended := RetainedBranch.extended G P ⟨4,d.output⟩
abbrev mappedExtended := OriginalLCodec.mapped (originalEmbedding G) (extended G P N labels d)

/-- The singleton source is sent to the actual appended row, even when an
earlier row has identical coefficients. -/
def newLabel : Fin (P.count+1) := ⟨P.count,Nat.lt_succ_self _⟩

theorem selected :
    (⟨RetainedBranch.arity G P ⟨4,d.output⟩ (newLabel G P).val,
      mappedExtended G P N labels d (newLabel G P)⟩ : AnySignature AlgebraicComplex) =
        ⟨4,mappedOutput G P N labels d⟩ := by
  have h := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,fun x => originalEmbedding G (f.2 x)⟩ : AnySignature AlgebraicComplex))
      (RetainedBranch.extended_new G P ⟨4,d.output⟩)
  exact h

variable (he : DenseEOUnitLocal.EOSupport (mappedOutput G P N labels d))
variable (hn : ¬ EOTract {⟨4,mappedOutput G P N labels d⟩})
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

/-- Physical singleton relabeling followed by a total rational-linear answer
retraction into the fixed OI field. No answer-codec equality is a premise. -/
def branchSource (w : SharpPWitness ea f) : LengthControlledOracleReduction
    ea encodingNatBool
    (RawClosedNetwork.validatedEncoding (P.count+1) 1
      (RetainedBranch.arity G P ⟨4,d.output⟩)) (OI.presentation G).encoding
    f (OriginalLCodec.value (extended G P N labels d)) :=
  Compose.composeControlled
    (EOQuaternaryOriginalSource.Family.source (mappedOutput G P N labels d) he hn
      (mappedExtended G P N labels d) (newLabel G P) (selected G P N labels d) w)
    (OriginalLCodec.fromCoefficient (originalEmbedding G) (extended G P N labels d))

/-- The only local hypotheses are EO support and failure of EO tractability
for the mapped output of this actual saved current-palette graph. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction
    ea encodingNatBool (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding f (OriginalForestSource.value G) :=
  Compose.composeControlled (branchSource G P N labels d he hn w) d.toOriginal.controlled

include he hn in
theorem witnessCountingHard : PaperControlledHardness.Hard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea f w
  exact ⟨(source G P N labels d he hn w)⟩

/-- Correct timed execution under the exact original input and answer codecs. -/
def outputs (w : SharpPWitness ea f) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) oracle)
    (x : α) : (source G P N labels d he hn w).reduction.machine.OutputsInTime
      oracle (ea.encode x) (encodingNatBool.encode (f x))
      ((source G P N labels d he hn w).reduction.time.eval (ea.encode x).length) :=
  (source G P N labels d he hn w).reduction.correct oracle ho x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperControlled.StableCurrentEvenEOHardness
