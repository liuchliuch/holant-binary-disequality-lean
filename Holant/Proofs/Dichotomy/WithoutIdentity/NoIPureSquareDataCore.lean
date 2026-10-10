import Holant.Tractable.Scalars
import Mathlib.FieldTheory.IntermediateField.Basic
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.TargetCore
import Holant.Proofs.Dichotomy.Native.NativeTableBase
import Holant.Proofs.CountingMachines.GatePins
import Holant.EightVertex.ProductAnchor.NetworksData

/-! A literal native Eq4/pin/X table and its unchanged controlled oracle,
independent of theorems classifying or adjoining its descendants. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareData
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
variable (target : NoIOrdinaryRaw.Target)
structure Data : Type 1 where
  K : IntermediateField ℚ AlgebraicComplex
  degree : ℕ
  F : letI : Algebra ℚ K:=K.algebra'; FixedField K degree
  count : ℕ
  arity : ℕ→ℕ
  table : (i : Fin count)→Signature K (arity i.val)
  eq4 : Fin count
  pin : Bool→Fin count
  x : Fin count
  eq4_literal : (⟨arity eq4.val,table eq4⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩
  pin_literal : ∀b,(⟨arity (pin b).val,table (pin b)⟩ : AnySignature K)=
    ⟨1,Holant.LocalDrafts.RemoteWork.CountingBridge.Gates.pin b⟩
  x_literal : (⟨arity x.val,table x⟩ : AnySignature K)=⟨2,fun z=>Signature.disequality (z 0) (z 1)⟩
  back : letI : Algebra ℚ K:=K.algebra'; LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding target.inputEncoding target.outputEncoding
    ((NativeAntiTargetSource.base table F).evaluate F) target.value

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureSquareData
end
