import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Hardness.BinaryCSPProgrammeNative
import Holant.Complexity.EdgeSubdivision.Reduction
import Holant.Complexity.EdgeSubdivision.VertexSubstitution
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Proofs.Closure.ProgrammeCompose

/-! A singleton native-X quaternary oracle is implemented by genuine ordinary
macros for its vertex and for X. Every native edge is subdivided, then both
literal macros are expanded. The old field, decoded answers, and arbitrary
ordered input incidence are preserved by actual controlled compilers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryNativeAccess
open Computability Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution BinaryCompose
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeNative (tables targetValue)
end B
namespace V
export EdgeSubdivision.VertexSubstitution (value computes partition)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree s : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin s)→Signature K (arity i.val))
variable (Q : Macro H 4) (X : Macro H 2)
variable (hX : X.network.denote=fun x=>Signature.disequality (x 0) (x 1))

abbrev sourceArity : ℕ→ℕ := EdgeSubdivision.targetArity 1 (fun _=>4)
def templates (i : ℕ) : Template := if i=0 then Q.template else X.template

theorem valid : ∀i<2,(templates H Q X i).WellFormed s 1 arity := by
  intro i _hi
  unfold templates
  split
  · exact Q.labels.wellFormed
  · exact X.labels.wellFormed

theorem arity_exact : FixedGadgetSubstitution.sourceArity (templates H Q X)=sourceArity := by
  funext i
  by_cases h : i=0
  · subst i
    rfl
  · have hi : ¬i<1 := by omega
    simp [FixedGadgetSubstitution.sourceArity,templates,sourceArity,EdgeSubdivision.targetArity,h,hi]

def binary (_j : Fin 1) (a b : Bool) := F.decode.symm (Signature.disequality a b)
def wire (a b : Bool) := F.decode.symm (Signature.equality a b)
def intermediate : ExactSignatureTables degree 2 1 sourceArity :=
  EdgeSubdivision.targetTables (B.tables F Q.network.denote) (binary F) (wire F)

include hX in
theorem local_value (i : Fin 2) :
    ((templates H Q X i.val).network (valid H Q X i.val i.isLt) H
      (fun _ : Fin 1=>Signature.equality)).denote = fun x=>
        F.decode ((intermediate F H Q).vertex i
          (fun j=>x (Fin.cast (congrFun (arity_exact H Q X) i.val).symm j))) := by
  fin_cases i
  · simpa [templates,intermediate,EdgeSubdivision.targetTables,B.tables,EdgeSubdivision.extendedSignatures]
      using Q.template_exact
  · simpa [templates,intermediate,EdgeSubdivision.targetTables,binary,EdgeSubdivision.extendedSignatures]
      using X.template_exact.trans hX

theorem fuse (j : Fin 1) (a b : Bool) :
    (∑uv : Bool×Bool,F.decode (wire F a uv.1)*F.decode (binary F j uv.1 uv.2)*F.decode (wire F uv.2 b))=
      F.decode ((B.tables F Q.network.denote).edge j a b) := by
  cases a <;> cases b <;>
    simp [wire,binary,B.tables,Fintype.sum_prod_type,Signature.equality,Signature.disequality]

def subdivide : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _=>4)) F.encoding
    (RawClosedNetwork.validatedEncoding 2 1 sourceArity) F.encoding
    (B.targetValue F Q.network.denote) ((intermediate F H Q).evaluate F) :=
  controlledOneQueryOfEq (EdgeSubdivision.Compiler.computes 1 1 (fun _=>4))
    (identityComputes F.encoding) ((intermediate F H Q).outputBound F)
    (B.targetValue F Q.network.denote) (fun r=>(EdgeSubdivision.evaluate_subdivision F
      (B.tables F Q.network.denote) (binary F) (wire F) (fuse F H Q) r).symm)

include hX in
theorem substitution_value (r : ExactSignatureTables.Input 2 1 sourceArity) :
    (QuaternaryOrdinaryCompanion.tables F H).evaluate F
      (V.value (templates H Q X) (arity_exact H Q X) (valid H Q X) r)=
    (intermediate F H Q).evaluate F r := by
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  have edge : (fun j a b=>F.decode ((intermediate F H Q).edge j a b))=
      (fun _ : Fin 1=>Signature.equality) := by
    funext j a b
    exact LinearEquiv.apply_symm_apply _ _
  rw [edge]
  exact V.partition (templates H Q X) (arity_exact H Q X) (valid H Q X) r.val r.property
    (fun i x=>F.decode ((intermediate F H Q).vertex i x)) H (fun _ : Fin 1=>Signature.equality)
    (local_value F H Q X hX)

def substitute : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 2 1 sourceArity) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    ((intermediate F H Q).evaluate F) ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  controlledOneQueryOfEq (V.computes (templates H Q X) (arity_exact H Q X) (valid H Q X))
    (identityComputes F.encoding) ((QuaternaryOrdinaryCompanion.tables F H).outputBound F)
    ((intermediate F H Q).evaluate F) (fun r=>(substitution_value F H Q X hX r).symm)

def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding 1 1 (fun _=>4)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (B.targetValue F Q.network.denote) ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (subdivide F H Q) (substitute F H Q X hX)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryNativeAccess
end
