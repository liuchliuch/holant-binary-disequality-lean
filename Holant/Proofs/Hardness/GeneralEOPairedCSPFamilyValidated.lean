import Holant.Proofs.Hardness.GeneralEOPairedCSPFamilyProgramme

/-! The mixed physical row writer emits exactly the validated original-family
occurrence-cycle graph, in each label's original ordered ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyValidated
open Turing Computability Holant Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open GeneralEOPairedCSPFamilyRaw
namespace W
export GeneralEOPairedCSPFamilyProgramme (port rowFor row raw rawComputes)
end W
namespace C
export GeneralEOPairedCSPFamilyCycles (query query_scan_rows query_edges incidence incidence_val)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {s : ℕ} {arity : ℕ→ℕ} (P : (i : Fin s)→OrientedPerfectPairing (arity i.val))

def query (r : Input P) : GeneralEOPairedCSPRecords.TargetInput (s:=s) (arity:=arity) :=
  C.query P r.val.labelsFn (GeneralEOPairedCSPScan.next (scope P r.val r.property))

theorem row_at (r : Raw s) (v : Fin r.labels.length) :
    W.row P r v.val=W.rowFor P (r.labelsFn v) r v.val := by
  unfold W.row
  have hi : v.val<(r.labels.map Fin.val).length := by simpa using v.isLt
  rw [List.getD_eq_getElem _ _ hi,List.getElem_map]
  have hl : (r.labels[v.val]).val<((List.finRange s).map (fun i=>W.rowFor P i r v.val)).length := by
    simpa using (r.labels[v.val]).isLt
  rw [List.getD_eq_getElem _ _ hl]
  simp [Raw.labelsFn,List.get_eq_getElem]

theorem incidence_eq (r : Raw s) (v : Fin r.labels.length)
    (j : Fin (P (r.labelsFn v)).count) :
    (C.incidence P r.labelsFn v j).val=r.offset P v.val+j.val := by
  rw [C.incidence_val]
  simp [Raw.labelsFn,Raw.offset,List.ofFn_get,List.map_take]

theorem row_eq (r : Raw s) (hr : r.WellFormed P) (v : Fin r.labels.length) :
    W.row P r v.val=((r.labelsFn v).val,List.ofFn fun k : Fin (arity (r.labelsFn v).val)=>
      let q := (P (r.labelsFn v)).ports.symm k
      (if q.2 then GeneralEOPairedCSPScan.NatScan.next r.addresses
        (C.incidence P r.labelsFn v q.1).val
        else (C.incidence P r.labelsFn v q.1).val,q.2)) := by
  rw [row_at]
  unfold W.rowFor GeneralEOPairedCSPProgramme.portList
  rw [List.map_ofFn]
  congr 1
  apply congrArg List.ofFn
  funext k
  dsimp only
  have hi := incidence_eq P r v ((P (r.labelsFn v)).ports.symm k).1
  have hb : r.offset P v.val+((P (r.labelsFn v)).ports.symm k).1.val<r.addresses.length := by
    rw [hr.1,←count_eq P,←hi]
    exact (C.incidence P r.labelsFn v ((P (r.labelsFn v)).ports.symm k).1).isLt
  rw [hi]
  dsimp only [Function.comp_def]
  unfold W.port
  rw [BinaryCSPProgrammeScan.next_eq _ _ hb]
  rfl

theorem raw_eq (r : Input P) : W.raw P r.val=(query P r).val := by
  have hrows : (W.raw P r.val).vertices=(query P r).val.vertices := by
    rw [query,C.query_scan_rows,addresses_scope]
    change (List.range r.val.labels.length).map (W.row P r.val)=_
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i<r.val.labels.length := by simpa using hi
      simpa only [List.getElem_map,List.getElem_range,List.getElem_ofFn] using
        row_eq P r.val r.property ⟨i,hin⟩
  have hedges : (W.raw P r.val).edges=(query P r).val.edges := by
    rw [query,C.query_edges,count_eq]
    rfl
  cases h₀ : W.raw P r.val
  cases h₁ : (query P r).val
  simp only [h₀,h₁] at hrows hedges
  cases hrows
  cases hedges
  rfl

def queryComputes : Computes (inputEncoding P)
    (RawClosedNetwork.validatedEncoding s 1 arity) (query P) :=
  recode (W.rawComputes P) Subtype.val (fun _=>rfl) (fun r=>by
    change RawClosedNetwork.encoding.encode (W.raw P r.val)=
      RawClosedNetwork.encoding.encode (query P r).val
    rw [raw_eq P r])

def polyTime : PolyTime (inputEncoding P)
    (RawClosedNetwork.validatedEncoding s 1 arity) (query P) := (queryComputes P).toPolyTime

theorem output_bound (r : Input P) :
    ((RawClosedNetwork.validatedEncoding s 1 arity).encode (query P r)).length≤
      (queryComputes P).outputBound.bound.eval ((inputEncoding P).encode r).length :=
  (queryComputes P).outputBound.length_le r

theorem primitive_bound (r : Input P) :
    primitiveCost (queryComputes P).machine ((queryComputes P).outputs r).steps
      (some (initList (queryComputes P).machine.computer ((inputEncoding P).encode r)))≤
      (primitivePolynomial (queryComputes P)).eval ((inputEncoding P).encode r).length :=
  computes_primitive_cost (queryComputes P) r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedCSPFamilyValidated
