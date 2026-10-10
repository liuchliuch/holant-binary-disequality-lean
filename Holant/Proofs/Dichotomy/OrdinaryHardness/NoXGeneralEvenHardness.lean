import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenDiagonal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralFullBinarySupply
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalComplete

/-! A genuine ordinary Eq4/both-pins/Z source with a whole-family obstruction
and any actual non-Affine even resource is counting hard. Support and binary
selection, finite-ratio normalization, actual diagonal exposure, interpolation,
relabeling and the final three-support/even-anti split are all internal. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenHardness
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
export OrdinaryNegativeXUniversalResource (EvenBad)
end B
namespace P
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification (full_product_iff)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (src : GenericOrdinarySource.Data G)
local instance : Algebra ℚ src.K := src.K.algebra'
variable (zLabel : Fin src.size)
variable (zLiteral : (⟨src.b zLabel.val,src.H zLabel⟩ : AnySignature src.K)=⟨2,NoXGeneralZSign.signature⟩)
variable (negative : StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (GenericOrdinarySource.family G src)))
include zLiteral negative in
theorem countingHard (bad : B.EvenBad src.H) : NoXWeightedAntiResourcesOriginal.Hard G := by
  classical
  by_contra noHard
  obtain ⟨m,first,nonaffine⟩ := bad
  let second : B.Block (s:=src.size) (b:=src.b) (NoXNonproduct.arity G src negative) :=
    ⟨0,NoXNonproduct.blocks G src negative,NoXNonproduct.balanced G src negative⟩
  obtain ⟨row,full,badA,badP,infinite⟩ := NoXGeneralFullBinarySupply.exists_infinite_binary
    G src first second nonaffine (NoXNonproduct.row_nonproduct G src negative) noHard zLabel zLiteral
  have det : row.signature src.H ![false,false]*row.signature src.H ![true,true]≠
      row.signature src.H ![false,true]*row.signature src.H ![true,false] := by
    intro eqn
    apply badP
    apply (P.full_product_iff _ (fun x hz=>full x (Subtype.ext hz))).mpr
    exact congrArg (fun c : src.K=>(c : AlgebraicComplex)) eqn
  have reversed : ∀k : ℕ,0<k→(row.signature src.H ![false,true]/row.signature src.H ![false,false])^k≠1 := by
    intro k hk eqn
    apply infinite k hk
    rw [div_pow,div_eq_one_iff_eq (pow_ne_zero _ (full _))] at eqn
    rw [div_pow,eqn,div_self (pow_ne_zero _ (full _))]
  let graph:=NoXGeneralEvenDiagonal.binaryOutput src.H src.e (src.p false) (src.p true)
    src.he (src.hp false) (src.hp true) row
  have graphValue:=NoXGeneralEvenDiagonal.binary_diagonal src.H src.e (src.p false) (src.p true)
    src.he (src.hp false) (src.hp true) row
  exact noHard (NoXReciprocalComplete.countingHard G src row (full _) (full _) det graph graphValue
    reversed negative ⟨2,row,badA⟩)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenHardness
end
