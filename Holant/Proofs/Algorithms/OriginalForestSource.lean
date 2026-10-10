import Holant.Proofs.Algorithms.OriginalWireTransport
import Holant.Proofs.Reductions.RootPreprocessing.ForestEndpoint


namespace Holant.LocalDrafts.MainChain.OriginalForestSource
open Computability Holant.Tractable Holant.Algebraic Holant.Complexity EdgeSubdivision
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness
noncomputable section
variable {s : ℕ} {arity : ℕ → ℕ}
    (G : (i : Fin s) → Signature AlgebraicComplex (arity i.val))

abbrev nativeSignatures := OriginalWireTransport.nativeSignatures G

/-- The added identity is a literal member of the actual query alphabet,
independently of whether the user's original family contains any binary. -/
theorem retains_identity : RetainsIdentity
    (Set.range (fun i => (⟨targetArity s arity i.val,nativeSignatures G i⟩ :
      AnySignature AlgebraicComplex))) := by
  change (⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩ :
    AnySignature AlgebraicComplex) ∈ _
  change _ ∈ Set.range (fun i : Fin (s+1) =>
    (⟨targetArity s arity i.val,extendedSignatures G
      (fun _ : Fin 1 => Signature.equality) i⟩ : AnySignature AlgebraicComplex))
  rw [Source.native_family]
  exact Or.inr rfl

abbrev roots := RootPreprocessing.roots (nativeSignatures G) (retains_identity G)
abbrev inputEncoding := OriginalWireTransport.inputEncoding (s:=s) (arity:=arity)
abbrev presentation := OriginalWireTransport.literalPresentation G
abbrev value := OriginalWireTransport.literalValue G
abbrev forestEncoding := FactorSaturation.WholeForest.inputEncoding (roots G)
abbrev forestPresentation := FactorSaturation.WholeForest.presentation (roots G)
abbrev forestValue := FactorSaturation.WholeForest.sourceValue (roots G)

/-- The forward route physically inserts/subdivides the wires, tests actual
zero occurrences, computes nullary products, and includes retained labels in
the actual finite forest alphabet, with answer conversion at each boundary. -/
def toForest : PolyTimeOracleReduction
    (inputEncoding (s:=s) (arity:=arity)) (presentation G).encoding
    (forestEncoding G) (forestPresentation G).encoding (value G) (forestValue G) :=
  (OriginalWireTransport.literalToNative G).compose
    (RootPreprocessing.originalToForest (nativeSignatures G) (retains_identity G))

/-- Reverse is a real finite chain interpretation. A leaf can require many
queries; the source field conversion is folded before the concrete retained
label inclusion and original Holant(G,X) wire compiler. -/
def fromForest : PolyTimeOracleReduction
    (forestEncoding G) (forestPresentation G).encoding
    (inputEncoding (s:=s) (arity:=arity)) (presentation G).encoding (forestValue G) (value G) :=
  let D := roots G
  FactorSaturation.PrefixMachine.withTerminal
    (FactorSaturation.CommonField.table D.signature D.nonzero D.identity)
    (FactorSaturation.WholeForest.presentation D)
    ((FactorSaturation.CommonField.originalTransport D.signature D.nonzero D.identity).compose
      ((FactorSaturation.OriginalCodec.transport D).compose
        ((RootPreprocessing.reverse (nativeSignatures G) (retains_identity G)).compose
          (OriginalWireTransport.nativeToLiteral G).reduction)))
    (FactorSaturation.WholeForest.chain D)

theorem equivalent :
    OracleReducible (inputEncoding (s:=s) (arity:=arity)) (presentation G).encoding
      (forestEncoding G) (forestPresentation G).encoding (value G) (forestValue G) ∧
    OracleReducible (forestEncoding G) (forestPresentation G).encoding
      inputEncoding (presentation G).encoding (forestValue G) (value G) :=
  ⟨⟨toForest G⟩,⟨fromForest G⟩⟩

/-- The output is the chosen-tree saturated retained family; this is not a
claim that canonical deduplication, Stable or Close has been constructed. -/
theorem forest_saturated : FactorSaturated
    (Set.range (fun i =>
      (⟨FactorSaturation.WholeForest.A (roots G) i.val,
        FactorSaturation.WholeForest.outputFamily (roots G) i⟩ : AnySignature AlgebraicComplex))) :=
  FactorSaturation.WholeForest.output_saturated (roots G)

end
end Holant.LocalDrafts.MainChain.OriginalForestSource
