import Holant.Proofs.Hardness.EOQuaternaryComplexTransport
import Holant.Proofs.Hardness.ComplexNonselfdualSource
import Holant.Proofs.Hardness.ComplexPlaneThreeSupportSource
import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportSource

/-! Original algebraic EO quaternary counting source. Every support and
coefficient branch selects a concrete already implemented reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryCompleteSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace S
export EOQuaternarySparseDispatch (complex complex_algebraic complex_eo complex_applicable Plane)
end S
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O
namespace Standard
export Holant.LocalDrafts.MainChain.CBStandardNativeHardness.Standard
  (Model injectedEncoding standard_to_witness)
end Standard
set_option backward.isDefEq.respectTransparency false
variable (M : Signature AlgebraicComplex 4)
variable (he : DenseEOUnitLocal.EOSupport M) (hn : ¬EOTract {⟨4,M⟩})
local instance originalAlgebra : Algebra ℚ (O.field (S.complex M)) := (O.field (S.complex M)).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}

theorem algebraic_roundtrip :
    EOBinaryPlaneFullSupportData.algebraic (S.complex M) (S.complex_algebraic M)=M := by
  funext x
  apply Subtype.ext
  rfl

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation (S.complex M) (S.complex_algebraic M)).encoding
    f (O.targetValue (S.complex M) (S.complex_algebraic M)) := by
  classical
  by_cases hd : DenseEOUnitLocal.NonzeroMiddle M
  · exact ComplexNonselfdualSource.source (S.complex M) (S.complex_algebraic M)
      (S.complex_eo M he) (EOQuaternaryComplexTransport.dense M hd) w
  by_cases hf : FiveSupportEOOrdering.ExactlyFive M
  · exact ComplexFiveSupportSource.source (S.complex M) (S.complex_algebraic M)
      (S.complex_eo M he) (EOQuaternaryComplexTransport.five M hf) w
  by_cases ha : EOQuaternarySparseFourLocal.Applicable M
  · exact EOQuaternarySparseFourSource.source (S.complex M) (S.complex_algebraic M)
      (S.complex_eo M he) (S.complex_applicable M ha) w
  have hr : (S.Plane M ∧ (EOQuaternarySparseTract.support M).card=3) ∨
      (S.Plane M ∧ (EOQuaternarySparseTract.support M).card=4) := by
    rcases EOQuaternarySupportCases.classified M he with ht|hd'|hf'|ha'|h3|h4
    · exact False.elim (hn ht)
    · exact False.elim (hd hd')
    · exact False.elim (hf hf')
    · exact False.elim (ha ha')
    · exact Or.inl h3
    · exact Or.inr h4
  have hp : S.Plane M := hr.elim And.left And.left
  by_cases h3 : (EOQuaternarySparseTract.support M).card=3
  · exact ComplexPlaneThreeSupportSource.source (S.complex M) (S.complex_algebraic M)
      (EOQuaternarySupportCases.complex_plane M hp) (S.complex_eo M he)
      (EOQuaternaryComplexTransport.three M h3) w
  have h4 : (EOQuaternarySparseTract.support M).card=4 :=
    hr.elim (fun h=>False.elim (h3 h.2)) And.right
  exact EOBinaryPlaneFullSupportSource.source (S.complex M) (S.complex_algebraic M)
    (EOQuaternarySupportCases.complex_plane M hp) (S.complex_eo M he)
    (by change (ComplexPlaneThreeSupportData.support (S.complex M)).card=4
        rw [EOQuaternarySupportCases.complex_support_card]; exact h4)
    (by simpa only [algebraic_roundtrip] using hn) w

include he hn in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    O.targetEncoding (O.presentation (S.complex M) (S.complex_algebraic M)).encoding
    (O.targetValue (S.complex M) (S.complex_algebraic M)) := by
  intro α ea f w
  exact ⟨(source M he hn w).reduction⟩

variable {Δ Q : Type} [Fintype Δ] [Fintype Q]
variable (m : Standard.Model Δ Q) (input : Bool→Δ) (hinj : Function.Injective input)
variable (clock : Polynomial ℕ) (htime : m.PolyTimeOn input clock)

def standardSource : LengthControlledOracleReduction ea encodingNatBool
    O.targetEncoding (O.presentation (S.complex M) (S.complex_algebraic M)).encoding
    (m.physicalCount (Standard.injectedEncoding ea input hinj))
    (O.targetValue (S.complex M) (S.complex_algebraic M)) :=
  source M he hn (Standard.standard_to_witness (ea:=ea) m input hinj clock htime)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryCompleteSource
