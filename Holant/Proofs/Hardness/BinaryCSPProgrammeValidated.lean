import Holant.Proofs.Hardness.BinaryCSPProgrammeRecords
import Holant.Proofs.Hardness.EOBinaryPlaneRaw

/-! The finite literal writer produces the exact well-formed original-M
query proved by the occurrence-cycle semantics. No guessed codec equality or
auxiliary signature label is used in this transport. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValidated
open Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace B
export EOBinaryPlaneRaw (scope addresses query query_rows)
end B
namespace P
export BinaryCSPProgrammeRecords (row raw rawComputes addresses addresses_length)
end P
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (TargetInput targetEncoding)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

abbrev Input := {r : Raw // r.WellFormed}
instance rawWellFormedDecidable (r : Raw) : Decidable r.WellFormed := by
  unfold Raw.WellFormed
  infer_instance
def inputEncoding : Encoding Input Bool where
  encode r := encoding.encode r.val
  decode bits := (encoding.decode bits).bind fun r =>
    if h : r.WellFormed then some ⟨r,h⟩ else none
  decode_encode r := by simp [r.property]

def query (r : Input) : O.TargetInput := B.query r.val r.property

theorem row_eq (r : Raw) (hr : r.WellFormed) (v : Fin r.edges.length) :
    P.row r v.val=(0,
      [((EOBinaryPlaneCycles.incidence v 0).val,false),
       (EOBinaryPlaneScanNat.next (B.addresses r) (EOBinaryPlaneCycles.incidence v 0).val,true),
       ((EOBinaryPlaneCycles.incidence v 1).val,false),
       (EOBinaryPlaneScanNat.next (B.addresses r) (EOBinaryPlaneCycles.incidence v 1).val,true)]) := by
  have h₀ : v.val*2<(P.addresses r).length := by rw [P.addresses_length]; omega
  have h₁ : v.val*2+1<(P.addresses r).length := by rw [P.addresses_length]; omega
  have hs₀ := BinaryCSPProgrammeScan.next_eq (P.addresses r) (v.val*2) h₀
  have hs₁ := BinaryCSPProgrammeScan.next_eq (P.addresses r) (v.val*2+1) h₁
  have hi₀ : (EOBinaryPlaneCycles.incidence v 0).val=v.val*2 := by
    change 0+2*v.val=v.val*2
    omega
  have hi₁ : (EOBinaryPlaneCycles.incidence v 1).val=v.val*2+1 := by
    change 1+2*v.val=v.val*2+1
    omega
  rw [hi₀,hi₁]
  unfold P.row
  rw [hs₀,hs₁]
  rfl

theorem raw_eq (r : Raw) (hr : r.WellFormed) : P.raw r=(B.query r hr).val := by
  have hrows : (P.raw r).vertices=(B.query r hr).val.vertices := by
    rw [B.query_rows]
    change (List.range r.edges.length).map (P.row r)=_
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i<r.edges.length := by simpa using hi
      simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using row_eq r hr ⟨i,hin⟩
  have hedges : (P.raw r).edges=(B.query r hr).val.edges := by
    exact (EOBinaryPlaneRecords.query_edges _).symm
  cases h₀ : P.raw r
  cases h₁ : (B.query r hr).val
  simp only [h₀,h₁] at hrows hedges
  cases hrows
  cases hedges
  rfl

def queryComputes : Computes inputEncoding O.targetEncoding query :=
  recode P.rawComputes Subtype.val (fun _ => rfl) (fun r => by
    change RawClosedNetwork.encoding.encode (P.raw r.val)=
      RawClosedNetwork.encoding.encode (B.query r.val r.property).val
    rw [raw_eq r.val r.property])

def polyTime : PolyTime inputEncoding O.targetEncoding query := queryComputes.toPolyTime

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryCSPProgrammeValidated
