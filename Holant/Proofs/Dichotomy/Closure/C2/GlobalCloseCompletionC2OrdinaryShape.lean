import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SignedSixClassified
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4Charts
import Holant.Proofs.Algorithms.RingHomDescent

/-! Chart coefficients are recovered from the actual source graph's entries.
The ordinary q4 consumers run in the graph's existing field and codec; no
membership of an external algebraic parameter is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryShape
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace S
export GlobalCloseCompletionC2SignedSixSquare (signed)
end S
namespace Q
export GlobalCloseCompletionC2OrdinaryQuaternary (Outcome)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

def word : Fin 4→(Fin 4→Bool) := ![![false,false,false,false],![false,false,true,true],![false,true,false,true],![false,true,true,false]]
def coefficient (N : Macro H 4) (i : Fin 4) : K := N.network.denote (word i)

theorem mapped_normal (A B C D : K) : RingHomRealization.mapSignature K.subtype (T.normal (K:=K) A B C D)=
    T.normal (K.subtype A) (K.subtype B) (K.subtype C) (K.subtype D) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [RingHomRealization.mapSignature,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]

theorem normal_form (N : Macro H 4) (A B C D : AlgebraicComplex)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote=T.normal A B C D) :
    N.network.denote=T.normal (coefficient K H N 0) (coefficient K H N 1) (coefficient K H N 2) (coefficient K H N 3) := by
  have values (i : Fin 4) : K.subtype (coefficient K H N i)=(![A,B,C,D] : Fin 4→AlgebraicComplex) i := by
    have h := congrFun form (word i)
    fin_cases i <;> exact h
  apply RingHomDescent.signature_injective K.subtype
  rw [form,mapped_normal,values,values,values,values]
  rfl

theorem signed_form (N : Macro H 4) (B C D : AlgebraicComplex)
    (form : RingHomRealization.mapSignature K.subtype N.network.denote=S.signed B C D) :
    N.network.denote=S.signed (coefficient K H N 1) (coefficient K H N 2) (coefficient K H N 3) := by
  have values (i : Fin 4) : K.subtype (coefficient K H N i)=(![0,B,C,D] : Fin 4→AlgebraicComplex) i := by
    have h := congrFun form (word i)
    fin_cases i <;> exact h
  apply RingHomDescent.signature_injective K.subtype
  rw [form,GlobalCloseCompletionC2SignedSixClassified.mapped_signed]
  change S.signed B C D=S.signed (K.subtype (coefficient K H N 1))
    (K.subtype (coefficient K H N 2)) (K.subtype (coefficient K H N 3))
  rw [values,values,values]
  rfl

include back zLiteral in
theorem classified (N : Macro H 4)
    (shape : GlobalCloseCompletionC2Q4Charts.Shape (RingHomRealization.mapSignature K.subtype N.network.denote)) :
    Q.Outcome G K H N := by
  rcases shape with ⟨A,B,C,D,form⟩|⟨B,C,D,form⟩
  · exact GlobalCloseCompletionC2OrdinaryQuaternary.classified G K F H back z zLiteral N _ _ _ _
      (normal_form K H N A B C D form)
  · exact GlobalCloseCompletionC2SignedSixClassified.classified G K F H back z zLiteral N _ _ _
      (signed_form K H N B C D form)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryShape
end
