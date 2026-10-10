import Holant.Proofs.Reductions.RootPreprocessing.Reverse


noncomputable section
namespace Holant.LocalDrafts.Hardness.RootPreprocessing
open Holant.Tractable
open Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.FinitePGL2.Stabilization
open FactorSaturation
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hI : RetainsIdentity (Set.range (fun i => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))))

def originalToForest : PolyTimeOracleReduction
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (WholeForest.inputEncoding (roots G hI)) (WholeForest.presentation (roots G hI)).encoding
    (sourceValue G) (WholeForest.sourceValue (roots G hI)) :=
  (controlled G hI).compose (OriginalCodec.reverse (roots G hI)).reduction

/-- Reuse the old chain interpreter; do not attempt to compose an arbitrary
uncontrolled outer reduction by asserting a free transitivity principle. -/
def forestToOriginal : PolyTimeOracleReduction
    (WholeForest.inputEncoding (roots G hI)) (WholeForest.presentation (roots G hI)).encoding
    (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
    (WholeForest.sourceValue (roots G hI)) (sourceValue G) :=
  let D := roots G hI
  PrefixMachine.withTerminal (CommonField.table D.signature D.nonzero D.identity)
    (WholeForest.presentation D)
    ((CommonField.originalTransport D.signature D.nonzero D.identity).compose
      ((OriginalCodec.transport D).compose (reverse G hI).reduction))
    (WholeForest.chain D)

theorem forest_equivalent :
    OracleReducible (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
      (WholeForest.inputEncoding (roots G hI)) (WholeForest.presentation (roots G hI)).encoding
      (sourceValue G) (WholeForest.sourceValue (roots G hI)) ∧
    OracleReducible (WholeForest.inputEncoding (roots G hI)) (WholeForest.presentation (roots G hI)).encoding
      (sourceEncoding (s:=s) (a:=a)) (sourcePresentation G).encoding
      (WholeForest.sourceValue (roots G hI)) (sourceValue G) :=
  ⟨⟨originalToForest G hI⟩,⟨forestToOriginal G hI⟩⟩

end Holant.LocalDrafts.Hardness.RootPreprocessing
