import Holant.Proofs.Reductions.CyclicRetainedAugmentation.Forest
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Proofs.Algorithms.FamilyAnswerTransport


noncomputable section
namespace Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation.LiteralCodec
open Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.Complexity.BinaryInterpolation.Chains
open GeneralExtraction

variable {s : ℕ} {a c : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (H : (i : Fin s) → Signature AlgebraicComplex (c i.val))
variable (h : ∀ i, (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex) = ⟨c i.val,H i⟩)

def arities (i : Fin s) : a i.val = c i.val := congrArg Sigma.fst (h i)
def query := RawArityTransport.input (b:=1) (arities G H h)
def queryComputes := RawArityTransport.computes (b:=1) (arities G H h)

theorem transported : RawArityTransport.signatures (arities G H h) G = H := by
  funext i x
  exact signature_cast_apply (G i) (H i) (h i) (arities G H h i) x

theorem ambient (r : ExactSignatureTables.Input s 1 a) :
    (GeneralOriginalTarget.originalValue H (query G H h r) : AlgebraicComplex) =
      (GeneralOriginalTarget.originalValue G r : AlgebraicComplex) := by
  rw [GeneralOriginalTarget.target_exact,GeneralOriginalTarget.target_exact]
  have he := RawArityTransport.denote (arities G H h) G (fun _ => Signature.disequality) r
  rw [transported G H h] at he
  exact he

def correction := FamilyAnswerTransport.recover
  (GeneralOriginalTarget.coefficients G) (GeneralOriginalTarget.coefficients H)
def correctionComputes := FamilyAnswerTransport.computes
  (GeneralOriginalTarget.coefficients G) (GeneralOriginalTarget.coefficients H)
  (GeneralOriginalTarget.coefficients_algebraic G) (GeneralOriginalTarget.coefficients_algebraic H)

def toTarget : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 a) (GeneralOriginalTarget.originalPresentation G).encoding
    (RawClosedNetwork.validatedEncoding s 1 c) (GeneralOriginalTarget.originalPresentation H).encoding
    (GeneralOriginalTarget.originalValue G) (GeneralOriginalTarget.originalValue H) :=
  controlledOneQueryOfEq (queryComputes G H h) (correctionComputes G H)
    ((GeneralOriginalTarget.originalTables H).outputBound (GeneralOriginalTarget.originalPresentation H))
    (GeneralOriginalTarget.originalValue G) (fun r =>
      (FamilyAnswerTransport.recover_exact (GeneralOriginalTarget.coefficients G)
        (GeneralOriginalTarget.coefficients H) (GeneralOriginalTarget.originalValue G r)
        (GeneralOriginalTarget.originalValue H (query G H h r)) (ambient G H h r)).symm)

end Holant.LocalDrafts.Hardness.CyclicRetainedAugmentation.LiteralCodec
