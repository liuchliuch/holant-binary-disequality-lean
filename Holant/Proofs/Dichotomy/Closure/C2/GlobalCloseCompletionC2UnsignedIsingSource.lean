import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryPairCSP
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2UnsignedIsingRows
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OrdinaryNativeAccess
import Holant.Proofs.Hardness.BinaryIsingCountingSource

/-! Genuine counted-verifier Ising hardness for an ordinary equality-pair
q4 macro, with no X resource. The existing interpolation uses swapped
weights and the exact unsigned-apex identity, followed by real macro expansion. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedIsingSource
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2 OrdinaryNegativeCubicGadgets
namespace C
export GlobalCloseCompletionC2OrdinaryPairCSP (tables targetValue query_value)
end C
namespace Q
export BinaryCSPProgrammeValidated (Input inputEncoding)
end Q
namespace I
export BinaryIsingProgramme (ValidQuery validQueryEncoding validQueryValue)
end I
namespace A
export BinaryCSPProgrammeApex (expandedComputes)
end A
namespace N
export BinaryCSPProgrammeNative (pre preprocessing post)
end N
namespace B
export BinaryIsingRaw (expanded expanded_valid)
end B
namespace W
export BinaryIsingWeights (table)
end W
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair)
end P
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
namespace V
export EdgeSubdivision.VertexSubstitution (value computes partition)
end V
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree : ℕ}
variable (F : FixedField K degree) (M : Signature K 4) (p q : K)

def expand (a : I.ValidQuery) : Q.Input := ⟨B.expanded a.1.val a.2,B.expanded_valid a.1.val a.1.property a.2⟩
def computes : Computes I.validQueryEncoding Q.inputEncoding expand :=
  recode A.expandedComputes (fun a : I.ValidQuery=>(a.1.val,a.2)) (fun _=>rfl) (fun _=>rfl)

theorem unsigned_value (a : I.ValidQuery) :
    I.validQueryValue q p a=EOBinaryPlaneRaw.value (W.table p q) (expand a).val :=
  GlobalCloseCompletionC2UnsignedIsingRows.value_eq_unsigned p q a.1.val a.1.property a.2

def queryControlled (hm : M=P.pair (W.table p q)) : LengthControlledOracleReduction
    I.validQueryEncoding F.encoding O.targetEncoding F.encoding
    (I.validQueryValue q p) (C.targetValue F M) := by
  let reduction := TraceQueryControl.controlledBatch (computes.andThen N.pre) (N.post F)
    ((C.tables F M).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho a
  rw [unsigned_value,C.query_value F M _ hm (expand a)]
  simpa only [Function.comp_apply,N.preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,
    List.getD_cons_zero,C.targetValue] using reduction.reduction.correct oracle ho a

def source (hm : M=P.pair (W.table p q)) (hp : p≠0) (hq : q≠0)
    (infinite : ∀n : ℕ,0<n→(p/q)^n≠1) {α : Type} {ea : Encoding α Bool} {count : α→ℕ}
    (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
      O.targetEncoding F.encoding count (C.targetValue F M) :=
  Programme.compose (Programme.compose (Programme.compose (BinaryCSPCountingSource.source F w)
    (BinaryCSPProgrammeSigned.controlled F))
    (BinaryIsingNand.controlled F q p hq hp (fun n hn=>infinite (2*n) (by omega))))
    (queryControlled F M p q hm)

section Macro
variable {s : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (arity i.val)) (D : Macro H 4)
def templates (_ : ℕ) : Template := D.template

theorem valid : ∀i<1,(templates H D i).WellFormed s 1 arity := fun _ _=>D.labels.wellFormed

theorem arity_exact : FixedGadgetSubstitution.sourceArity (templates H D)=(fun _=>4) := rfl

theorem local_value (i : Fin 1) :
    ((templates H D i.val).network (valid H D i.val i.isLt) H
      (fun _ : Fin 1=>Signature.equality)).denote=fun x=>
      F.decode ((C.tables F D.network.denote).vertex i
        (fun j=>x (Fin.cast (congrFun (arity_exact H D) i.val).symm j))) := by
  simpa [templates,C.tables,QuaternaryOrdinaryCompanion.tables] using D.template_exact

theorem substitution_value (r : O.TargetInput) :
    (QuaternaryOrdinaryCompanion.tables F H).evaluate F
      (V.value (templates H D) (arity_exact H D) (valid H D) r)=C.targetValue F D.network.denote r := by
  rw [ExactSignatureTables.evaluate_eq_decoded,C.targetValue,ExactSignatureTables.evaluate_eq_decoded]
  simp only [QuaternaryOrdinaryCompanion.tables,C.tables,LinearEquiv.apply_symm_apply]
  simpa only [C.tables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply] using
    V.partition (templates H D) (arity_exact H D) (valid H D) r.val r.property
      (fun i x=>F.decode ((C.tables F D.network.denote).vertex i x)) H
      (fun _ : Fin 1=>Signature.equality) (local_value F H D)

def macroAccess : LengthControlledOracleReduction O.targetEncoding F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (C.targetValue F D.network.denote) ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  controlledOneQueryOfEq (V.computes (templates H D) (arity_exact H D) (valid H D))
    (identityComputes F.encoding) ((QuaternaryOrdinaryCompanion.tables F H).outputBound F)
    (C.targetValue F D.network.denote) (fun r=>(substitution_value F H D r).symm)

def sourceMacro (hm : D.network.denote=P.pair (W.table p q)) (hp : p≠0) (hq : q≠0)
    (infinite : ∀n : ℕ,0<n→(p/q)^n≠1) {α : Type} {ea : Encoding α Bool} {count : α→ℕ}
    (w : SharpPWitness ea count) : LengthControlledOracleReduction ea encodingNatBool
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding count
      ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) :=
  Programme.compose (source F D.network.denote p q hm hp hq infinite w) (macroAccess F H D)


end Macro
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2UnsignedIsingSource
end
