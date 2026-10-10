import Holant.Proofs.Hardness.BinaryCSPProgrammeMixedRecords
import Holant.Proofs.Hardness.BinaryCSPProgrammeNative
import Holant.Proofs.Hardness.EOBinaryPlaneMixed

/-! Exact validated mixed-polarity query, and its physically computed unused
variable correction in the same fixed original coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMixed
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace R
export BinaryCSPProgrammeMixedRecords (polaritiesEncoding raw row rawComputes)
end R
namespace B
export EOBinaryPlaneRaw (scope addresses addresses_scope)
end B
namespace E
export EOBinaryPlaneMixed (query query_rows query_edges endpoint value query_denote native_signed_value)
end E
namespace C
export EOBinaryPlaneCycles (Slot incidence)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
namespace N
export BinaryCSPProgrammeNative (tables targetValue target_semantics post)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

abbrev Input := P.Input×List Bool
abbrev inputEncoding := pairEncoding P.inputEncoding R.polaritiesEncoding

def rowSigns {m : ℕ} (ps : List Bool) (v : Fin m) : Fin 2→Bool := ![ps.getD v.val false,false]

def query (a : Input) : O.TargetInput :=
  E.query (EOBinaryPlaneScan.next (B.scope a.1.val a.1.property)) (rowSigns a.2)

private theorem endpoint_list {m : ℕ} (next : Equiv.Perm (C.Slot m)) (v : Fin m) (b : Bool) :
    List.ofFn (fun i : Fin 4=>let p := E.endpoint next v (EOBinaryPlaneOrient.ports ![b,false] i);
      (p.1.val,p.2))=
    if b then [((next (C.incidence v 0)).val,true),((C.incidence v 0).val,false),
      ((C.incidence v 1).val,false),((next (C.incidence v 1)).val,true)]
    else [((C.incidence v 0).val,false),((next (C.incidence v 0)).val,true),
      ((C.incidence v 1).val,false),((next (C.incidence v 1)).val,true)] := by
  cases b <;> rfl

theorem row_eq (a : Input) (v : Fin a.1.val.edges.length) :
    R.row (a.1.val,a.2) v.val=(0,List.ofFn (fun i : Fin 4=>
      let p := E.endpoint (EOBinaryPlaneScan.next (B.scope a.1.val a.1.property)) v
        (EOBinaryPlaneOrient.ports (rowSigns a.2 v) i);(p.1.val,p.2))) := by
  have h₀ : v.val*2<(BinaryCSPProgrammeRecords.addresses a.1.val).length := by
    rw [BinaryCSPProgrammeRecords.addresses_length]; omega
  have h₁ : v.val*2+1<(BinaryCSPProgrammeRecords.addresses a.1.val).length := by
    rw [BinaryCSPProgrammeRecords.addresses_length]; omega
  have hs₀ := BinaryCSPProgrammeScan.next_eq (BinaryCSPProgrammeRecords.addresses a.1.val) (v.val*2) h₀
  have hs₁ := BinaryCSPProgrammeScan.next_eq (BinaryCSPProgrammeRecords.addresses a.1.val) (v.val*2+1) h₁
  have hi₀ : (C.incidence v 0).val=v.val*2 := by
    change 0+2*v.val=v.val*2
    omega
  have hi₁ : (C.incidence v 1).val=v.val*2+1 := by
    change 1+2*v.val=v.val*2+1
    omega
  unfold rowSigns
  rw [endpoint_list,←EOBinaryPlaneScanNat.next_value,←EOBinaryPlaneScanNat.next_value,B.addresses_scope,hi₀,hi₁]
  unfold R.row BinaryCSPProgrammeRecords.row
  rw [hs₀,hs₁]
  cases a.2.getD v.val false <;> rfl

theorem raw_eq (a : Input) : R.raw (a.1.val,a.2)=(query a).val := by
  have hrows : (R.raw (a.1.val,a.2)).vertices=(query a).val.vertices := by
    rw [query,E.query_rows]
    change (List.range a.1.val.edges.length).map (R.row (a.1.val,a.2))=_
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i<a.1.val.edges.length := by simpa using hi
      simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using row_eq a ⟨i,hin⟩
  have hedges : (R.raw (a.1.val,a.2)).edges=(query a).val.edges := by
    exact (E.query_edges _ _).symm
  cases h₀ : R.raw (a.1.val,a.2)
  cases h₁ : (query a).val
  simp only [h₀,h₁] at hrows hedges
  cases hrows
  cases hedges
  rfl

def queryComputes : Computes inputEncoding O.targetEncoding query :=
  recode R.rawComputes (fun a : Input=>(a.1.val,a.2)) (fun _=>rfl) (fun a=>by
    change RawClosedNetwork.encoding.encode (R.raw (a.1.val,a.2))=
      RawClosedNetwork.encoding.encode (query a).val
    rw [raw_eq])

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (f : Signature K 2)

def mixedValue (a : Input) : K :=
  E.value (fun v z=>f (EOBinaryPlaneOrient.flipWord (rowSigns a.2 v) z)) (B.scope a.1.val a.1.property)

theorem query_value (hm : M=EOBinaryPlaneCore.lift f) (a : Input) :
    mixedValue f a=N.targetValue F M (query a)*(2 : K)^BinaryCSPProgrammeUnused.unused a.1.val := by
  rw [mixedValue,E.native_signed_value,N.target_semantics,hm,query,E.query_denote,
    BinaryCSPProgrammeUnused.unused_eq]
  exact mul_comm _ _

def unusedComputes : Computes inputEncoding unary (fun a : Input=>BinaryCSPProgrammeUnused.unused a.1.val) :=
  (Wiring.firstComputes P.inputEncoding R.polaritiesEncoding).andThen BinaryCSPProgrammeNative.unusedComputes

def preprocessing (a : Input) : List O.TargetInput×ℕ := ([query a],BinaryCSPProgrammeUnused.unused a.1.val)
def pre : Computes inputEncoding (OracleBatch.contextEncoding O.targetEncoding unary) preprocessing :=
  pairComputes (Holant.LocalDrafts.CountingHardness.RawGraphMachine.Access.list₁ O.targetEncoding queryComputes)
    unusedComputes

def controlled (hm : M=EOBinaryPlaneCore.lift f) :
    LengthControlledOracleReduction inputEncoding F.encoding O.targetEncoding F.encoding
      (mixedValue f) (N.targetValue F M) := by
  let reduction := Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch pre (N.post F)
    ((N.tables F M).outputBound F)
  refine {
    reduction := {
      machine := reduction.reduction.machine
      time := reduction.reduction.time
      correct := ?_ }
    targetOutput := reduction.targetOutput
    queryBound := reduction.queryBound
    safeQuery := reduction.safeQuery }
  intro oracle ho a
  rw [query_value F M f hm a]
  simpa only [preprocessing,OracleBatch.answers,List.map_cons,List.map_nil,List.getD_cons_zero,N.targetValue] using
    reduction.reduction.correct oracle ho a

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeMixed
