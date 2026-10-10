import Holant.Proofs.Hardness.GeneralEOPairedCSPProgramme

/-! The physical row writer is exactly the proven validated original-family
network. This yields an actual bit-machine query compiler, output-length and
primitive-operation bounds, with the original graph codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPValidated
open Turing Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPRaw
namespace P
export GeneralEOPairedCSPProgramme (portList port row raw rawComputes)
end P
namespace R
export GeneralEOPairedCSPRecords (TargetInput query query_scan_rows query_edges)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ} (label : Fin s)
variable (p : OrientedPerfectPairing (arity label.val))

def query (r : Input p.count) : R.TargetInput (s:=s) (arity:=arity) :=
  R.query label p (GeneralEOPairedCSPScan.next (scope p r.val r.property))

theorem row_eq (r : Raw) (hr : r.WellFormed p.count) (v : Fin r.constraints) :
    P.row p label.val r v.val=(label.val,List.ofFn fun k : Fin (arity label.val)=>
      let q := p.ports.symm k
      (if q.2 then GeneralEOPairedCSPScan.NatScan.next r.addresses
        (GeneralEOPairedCSPCycles.incidence p v q.1).val
        else (GeneralEOPairedCSPCycles.incidence p v q.1).val,q.2)) := by
  unfold P.row P.portList
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  dsimp only
  have hi : (GeneralEOPairedCSPCycles.incidence p v (p.ports.symm k).1).val=
      v.val*p.count+(p.ports.symm k).1.val := by
    change (p.ports.symm k).1.val+p.count*v.val=v.val*p.count+(p.ports.symm k).1.val
    simp [Nat.mul_comm,Nat.add_comm]
  have hb : v.val*p.count+(p.ports.symm k).1.val<r.addresses.length := by
    rw [hr.1,←hi]
    exact (GeneralEOPairedCSPCycles.incidence p v (p.ports.symm k).1).isLt
  rw [hi]
  dsimp only [Function.comp_def]
  unfold P.port
  rw [BinaryCSPProgrammeScan.next_eq _ _ hb]
  rfl

theorem raw_eq (r : Input p.count) : P.raw p label.val r.val=(query label p r).val := by
  have hrows : (P.raw p label.val r.val).vertices=(query label p r).val.vertices := by
    rw [query,R.query_scan_rows,addresses_scope]
    change (List.range r.val.constraints).map (P.row p label.val r.val)=_
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i<r.val.constraints := by simpa using hi
      simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using
        row_eq label p r.val r.property ⟨i,hin⟩
  have hedges : (P.raw p label.val r.val).edges=(query label p r).val.edges :=
    (R.query_edges label p _).symm
  cases h₀ : P.raw p label.val r.val
  cases h₁ : (query label p r).val
  simp only [h₀,h₁] at hrows hedges
  cases hrows
  cases hedges
  rfl

def queryComputes : Computes (inputEncoding p.count)
    (RawClosedNetwork.validatedEncoding s 1 arity) (query label p) :=
  recode (P.rawComputes p label.val) Subtype.val (fun _=>rfl) (fun r=>by
    change RawClosedNetwork.encoding.encode (P.raw p label.val r.val)=
      RawClosedNetwork.encoding.encode (query label p r).val
    rw [raw_eq label p r])

def polyTime : PolyTime (inputEncoding p.count)
    (RawClosedNetwork.validatedEncoding s 1 arity) (query label p) :=
  (queryComputes label p).toPolyTime

theorem output_bound (r : Input p.count) :
    ((RawClosedNetwork.validatedEncoding s 1 arity).encode (query label p r)).length≤
      (queryComputes label p).outputBound.bound.eval ((inputEncoding p.count).encode r).length :=
  (queryComputes label p).outputBound.length_le r

theorem primitive_bound (r : Input p.count) :
    primitiveCost (queryComputes label p).machine ((queryComputes label p).outputs r).steps
      (some (initList (queryComputes label p).machine.computer ((inputEncoding p.count).encode r)))≤
      (primitivePolynomial (queryComputes label p)).eval ((inputEncoding p.count).encode r).length :=
  computes_primitive_cost (queryComputes label p) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPValidated
