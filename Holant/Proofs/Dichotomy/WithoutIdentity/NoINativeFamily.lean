import Mathlib.FieldTheory.IntermediateField.Basic
import Holant.Algebraic.FixedField
import Holant.Tractable.Criteria

/-! Literal finite alphabets and their coefficient-field inclusion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource
open Holant Holant.Tractable
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
def original : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin s => (⟨a i.val,G i⟩ : AnySignature AlgebraicComplex))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDescentSource
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
variable {r : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r)→Signature L (b i.val))
def family : SignatureFamily L := Set.range fun i : Fin r=>(⟨b i.val,H i⟩ : AnySignature L)
def mapped (i : Fin r) : Signature AlgebraicComplex (b i.val) := fun x=>(H i x : AlgebraicComplex)
def ambient : SignatureFamily AlgebraicComplex := GeneralOddUnarySource.original (mapped L H)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryDescentSource
end
