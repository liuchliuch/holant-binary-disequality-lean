import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryChartSource
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairOutcome
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryXAdjoin
import Holant.Projective.CyclicQuaternary.Physical

/-! The conformal Hadamard chart of the whole ordinary dictionary, over its
original field. The retained Z row gives an actual scalar X graph. Each old
edge contributes exactly its factor two; no unary or gate is assumed present. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryHadamard
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
open scoped BigOperators
namespace U
export GeneralOddNonisotropicFrame (frame norm chart)
end U
namespace C
export GlobalCloseCompletionUnaryChartSource (chartTable graph labels exact graph_value controlled scale)
end C
namespace X
export GlobalCloseCompletionOrdinaryXAdjoin (Output signatures arity old old_literal xLabel x_literal source)
end X
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K]
local instance : CharZero K := Algebra.charZero_of_charZero ℚ K
variable {degree s : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (a i.val))

private theorem sum_words4 (f : (Fin 4→Bool)→K) :
    (∑w,f w)=∑a : Bool,∑b : Bool,∑c : Bool,∑d : Bool,f ![a,b,c,d] := by
  letI : Fintype (Bool×Bool) := instFintypeProd Bool Bool
  letI : Fintype (Bool×Bool×Bool) := instFintypeProd Bool (Bool×Bool)
  letI : Fintype (Bool×Bool×Bool×Bool) := instFintypeProd Bool (Bool×Bool×Bool)
  rw [←Equiv.sum_comp Holant.Projective.CyclicQuaternary.Physical.words4.symm f]
  simp only [Fintype.sum_prod_type]
  rfl

private def words2 : (Fin 2→Bool) ≃ Bool×Bool where
  toFun w := (w 0,w 1)
  invFun w := ![w.1,w.2]
  left_inv w := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

private theorem sum_words2 (f : (Fin 2→Bool)→K) :
    (∑w,f w)=∑a : Bool,∑b : Bool,f ![a,b] := by
  rw [←Equiv.sum_comp words2.symm f]
  simp only [Fintype.sum_prod_type]
  rfl

def unary : Signature K 1 := fun _=>1
@[simp] theorem norm_unary : U.norm (unary (K:=K))=2 := by simp [U.norm,unary]; ring

theorem chart_normal (a b c d : K) :
    U.chart unary (T.normal a b c d)=T.normal (2*(a+b+c+d)) (2*(a+b-c-d))
      (2*(a-b+c-d)) (2*(a-b-c+d)) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [U.chart,U.frame,unary,Signature.coordinateAction,
    sum_words4,Fin.prod_univ_succ,
    T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3] <;> ring

theorem chart_z : U.chart (unary (K:=K)) (fun x : Fin 2→Bool=>T.Z (x 0) (x 1))=
    fun x=> -2*Signature.disequality (x 0) (x 1) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1
  all_goals simp [U.chart,U.frame,unary,Signature.coordinateAction,
    sum_words2,Fin.prod_univ_succ,
    T.Z,Signature.disequality,h0,h1] <;> ring

abbrev chartTable := C.chartTable H unary

def chartMacro {n : ℕ} (N : Macro H n) : Macro (chartTable H) n where
  network := C.graph unary N.network
  labels := C.labels unary N.network N.labels
  exact := C.exact H unary N.network N.labels N.exact
  edges := fun _=>rfl

theorem chartMacro_denote {n : ℕ} (N : Macro H n) :
    (chartMacro H N).network.denote=fun x=>(2:K)^N.network.shape.edges*U.chart unary N.network.denote x := by
  have h := C.graph_value unary (by rw [norm_unary]; norm_num) N.network N.edges
  funext x
  rw [h]
  change _=(2:K)^N.network.shape.edges*((U.norm unary)⁻¹^N.network.shape.edges*_)
  rw [norm_unary,←mul_assoc,←mul_pow,mul_inv_cancel₀ (by norm_num : (2:K)≠0),one_pow,one_mul]
  rfl

variable (z : Fin s) (literal : (⟨a z.val,H z⟩ : AnySignature K)=⟨2,fun x=>T.Z (x 0) (x 1)⟩)

include literal in
theorem z_literal : (⟨a z.val,chartTable H z⟩ : AnySignature K)=
    ⟨2,fun x=> -2*Signature.disequality (x 0) (x 1)⟩ := by
  exact (congrArg (fun f : AnySignature K=>(⟨f.1,U.chart unary f.2⟩ : AnySignature K)) literal).trans
    (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) chart_z)

def xOutput : X.Output (chartTable H) where
  network := (Macro.row z _ (z_literal H z literal)).network
  labels := (Macro.row z _ (z_literal H z literal)).labels
  exact := (Macro.row z _ (z_literal H z literal)).exact
  ordinary := (Macro.row z _ (z_literal H z literal)).edges
  scalar := -2
  nonzero := by norm_num
  denote := Macro.row_denote z _ (z_literal H z literal)

abbrev signatures := X.signatures F (chartTable H) (xOutput H z literal)
abbrev arity := X.arity (chartTable H) (xOutput H z literal)

def oldMacro {n : ℕ} (N : Macro (chartTable H) n) : Macro (signatures F H z literal) n where
  network := N.network
  labels := {
    vertex := fun v=>X.old (chartTable H) (N.labels.vertex v)
    vertex_arity := fun v=>(congrArg Sigma.fst (X.old_literal F (chartTable H) (xOutput H z literal) (N.labels.vertex v))).trans (N.labels.vertex_arity v)
    edge := N.labels.edge }
  exact := fun v=>(X.old_literal F (chartTable H) (xOutput H z literal) (N.labels.vertex v)).trans (N.exact v)
  edges := N.edges

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (s+1) 1 (arity H z literal)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F (signatures F H z literal)).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (X.source F (chartTable H) (xOutput H z literal))
    (C.controlled F H unary (by rw [norm_unary]; norm_num))

theorem normal_pair (A D : K) : T.normal A D 0 0=P.pair (M.binary (P.symmetric A D)) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,P.pair,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3]

theorem same_sign_form (N : Macro H 4) (A C : K) (form : N.network.denote=T.normal A A C C) :
    (oldMacro F H z literal (chartMacro H N)).network.denote=
      P.pair (M.binary (P.symmetric ((2:K)^N.network.shape.edges*(4*(A+C)))
        ((2:K)^N.network.shape.edges*(4*(A-C))))) := by
  change (chartMacro H N).network.denote=_
  rw [chartMacro_denote,form,chart_normal]
  have c0 : 2*(A-A+C-C)=0 := by ring
  have d0 : 2*(A-A-C+C)=0 := by ring
  rw [c0,d0,normal_pair]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [P.pair,M.binary,M.bitIndex,P.symmetric,h0,h1,h2,h3] <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryHadamard
end
