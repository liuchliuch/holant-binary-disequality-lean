import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryNativeEq4
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2KNormal

/-! The opposite-sign paired ordinary q4 branch uses the exact inverse-K
native source. Its coefficients are recovered in that source's own field;
finite chains give real Eq4 and infinite chains use the counted Ising source. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryOppositeTerminal
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1 OrdinaryNegativeCubicGadgets
namespace S
export GlobalCloseCompletionC2OrdinaryNativeSource (mapped native field presentation table graphMacro graph_value source)
end S
namespace Q
export GlobalCloseCompletionC2NativePairOutcome (deq_or_hard_to)
end Q
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (symmetric)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r degree : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K := K.algebra'
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (b i.val))
local instance : Algebra ℚ (S.field K H) := (S.field K H).algebra'
variable (back : LengthControlledOracleReduction (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (OriginalForestSource.value G))
variable (N : Macro H 4) (A C : K) (hA : A≠0) (hC : C≠0)
variable (form : N.network.denote=T.normal A A C (-C))
variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

def p : S.field K H := (S.graphMacro K H N).network.denote ![false,true,false,true]
def q : S.field K H := (S.graphMacro K H N).network.denote ![false,true,true,false]

include form in
theorem ambient_form (x : Fin 4→Bool) :
    ((S.graphMacro K H N).network.denote x : AlgebraicComplex)=
      T.normal 0 0 ((A:AlgebraicComplex)-(C:AlgebraicComplex)) ((A:AlgebraicComplex)+(C:AlgebraicComplex)) x := by
  change ((GlobalCloseCompletionC2OrdinaryNativeSource.graph K H N).denote x : AlgebraicComplex)=_
  rw [S.graph_value,form]
  have hm : RingHomRealization.mapSignature K.subtype (T.normal (K:=K) A A C (-C))=
      T.normal (A:AlgebraicComplex) (A:AlgebraicComplex) (C:AlgebraicComplex) (-(C:AlgebraicComplex)) := by
    funext w
    cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
      simp [RingHomRealization.mapSignature,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> rfl
  rw [hm,GlobalCloseCompletionC2KNormal.inverse_opposite]

include form in
theorem p_value : (p K H N : AlgebraicComplex)=(A:AlgebraicComplex)-(C:AlgebraicComplex) :=
  ambient_form K H N A C form ![false,true,false,true]
include form in
theorem q_value : (q K H N : AlgebraicComplex)=(A:AlgebraicComplex)+(C:AlgebraicComplex) :=
  ambient_form K H N A C form ![false,true,true,false]

include form in
theorem native_form : (S.graphMacro K H N).network.denote=
    EOBinaryPlaneCore.lift (M.binary (P.symmetric (p K H N) (q K H N))) := by
  funext x
  apply (S.field K H).subtype.injective
  change (S.field K H).subtype ((S.graphMacro K H N).network.denote x)=_
  have hx := ambient_form K H N A C form x
  change (S.field K H).subtype ((S.graphMacro K H N).network.denote x)=_ at hx
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,EOBinaryPlaneCore.lift,
      M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]
  all_goals first
    | exact (p_value K H N A C form).symm
    | exact (q_value K H N A C form).symm

include form hA hC in
theorem determinant : (p K H N)^2≠(q K H N)^2 := by
  intro eqn
  have h := congrArg (S.field K H).subtype eqn
  change (p K H N : AlgebraicComplex)^2=(q K H N : AlgebraicComplex)^2 at h
  rw [p_value K H N A C form,q_value K H N A C form] at h
  have hA' : (A:AlgebraicComplex)≠0 := by intro zero; exact hA (Subtype.ext zero)
  have hC' : (C:AlgebraicComplex)≠0 := by intro zero; exact hC (Subtype.ext zero)
  have live : (4:AlgebraicComplex)*(A:AlgebraicComplex)*(C:AlgebraicComplex)≠0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) hA') hC'
  apply live
  linear_combination -h

include back form hA hC zLiteral in
theorem classified : Tract (UniversalPairReduction.FiniteFamily.family (S.mapped K H)) ∨
    OrdinaryNegativeGenericXFourthCompatibilitySource.Hard G := by
  let phi : S.field K H→+*ℂ := (algebraicClosure ℚ ℂ).subtype.comp (S.field K H).subtype
  rcases Q.deq_or_hard_to (S.presentation K H) (S.table K H) phi (S.graphMacro K H N)
    (p K H N) (q K H N) (native_form K H N A C form) (determinant K H N A C hA hC form)
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (OriginalForestSource.value G) (Programme.compose (S.source K F H) back) with finite|hard
  · obtain ⟨D⟩ : Nonempty (GeneralEODEQProducerNormalize.Produced (S.table K H)) := finite
    exact GlobalCloseCompletionC2OrdinaryNativeEq4.classified K F H z zLiteral D G back
  · exact Or.inr hard

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryOppositeTerminal
end
