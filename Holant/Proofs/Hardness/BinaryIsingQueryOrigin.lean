import Holant.Proofs.Hardness.BinaryIsingSource

/-! Every external query of the composed source is the actual paired-port apex
query for one positive sample j≤m. Thus empty graphs make no query, and each
native graph has at most 3m² original vertices and 6m² native-X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingSource
open Turing Computability Holant Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open BinaryCSPProgrammeCore
namespace T
export Holant.LocalDrafts.MainChain.TraceQueryControl (transcript_member)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (p q : K)
variable (hm : M=EOBinaryPlaneCore.lift (BinaryIsingWeights.table p q))

def nativeQuery (a : BinaryIsingProgramme.ValidQuery) : O.TargetInput :=
  BinaryCSPProgrammeMixed.query (A.expand a)

theorem query_singleton (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (a : BinaryIsingProgramme.ValidQuery) (t : ℕ)
    (cfg : (queryControlled F M p q hm).reduction.machine.Cfg)
    (hr : (queryControlled F M p q hm).reduction.machine.run oracle (I.validQueryEncoding.encode a) t=some cfg)
    (hq : (queryControlled F M p q hm).reduction.machine.IsQuery cfg) :
    cfg.stk (queryControlled F M p q hm).reduction.machine.queryStack=O.targetEncoding.encode (nativeQuery a) := by
  obtain ⟨n,_,run⟩ := OracleBatch.reduction_run_trace
    (BinaryCSPProgrammeApex.computes.andThen BinaryCSPProgrammeMixed.pre)
    (BinaryCSPProgrammeNative.post F) ((N.tables F M).outputBound F) oracle ho a
  have hs := T.transcript_member run t cfg hr hq
  simpa only [nativeQuery,queryControlled,BinaryCSPProgrammeApex.controlled,
    Holant.LocalDrafts.MainChain.TraceQueryControl.controlledBatch,
    Function.comp_apply,BinaryCSPProgrammeMixed.preprocessing,List.map_cons,List.map_nil,
    List.mem_singleton] using hs

variable (hp : p≠0) (hq : q≠0) (hs : ∀j,0<j→(q/p)^(2*j)≠1)

theorem actual_query_origin (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (r : P.Input) (t : ℕ) (cfg : (controlled F M p q hm hp hq hs).reduction.machine.Cfg)
    (hr : (controlled F M p q hm hp hq hs).reduction.machine.run oracle (P.inputEncoding.encode r) t=some cfg)
    (hc : (controlled F M p q hm hp hq hs).reduction.machine.IsQuery cfg) :
    ∃k<r.val.edges.length,
      cfg.stk (controlled F M p q hm hp hq hs).reduction.machine.queryStack=
        O.targetEncoding.encode (nativeQuery (r,k)) := by
  obtain ⟨ot,oc,a,it,ic,memory,hor,hoq,ha,_,hir,hiq,hcfg⟩ :=
    Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost.composeControlled_query_origin
      (BinaryIsingNand.controlled F p q hp hq hs) (queryControlled F M p q hm) oracle ho r t cfg hr hc
  obtain ⟨n,_,run⟩ := BinaryIsingProgramme.valid_execution F p q
    (encodedOracle I.validQueryEncoding F.encoding (I.validQueryValue p q))
    (encodedOracle_represents I.validQueryEncoding F.encoding (I.validQueryValue p q)) r
  have hmemb := T.transcript_member run ot oc hor hoq
  obtain ⟨b,hb,he⟩ := List.mem_map.mp hmemb
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hb
  have hea : I.validQueryEncoding.encode a=I.validQueryEncoding.encode (r,k) := ha.symm.trans he.symm
  have heq : a=(r,k) := I.validQueryEncoding.encode_injective hea
  subst a
  have hinner := query_singleton F M p q hm oracle ho (r,k) it ic hir hiq
  refine ⟨k,List.mem_range.mp hk,?_⟩
  rw [hcfg]
  exact hinner

theorem native_query_counts (r : P.Input) (k : ℕ) :
    (nativeQuery (r,k)).val.vertices.length=r.val.edges.length*3*(k+1) ∧
      (nativeQuery (r,k)).val.edges.length=r.val.edges.length*3*(k+1)*2 := by
  have h := EOBinaryPlaneMixed.query_counts
    (EOBinaryPlaneScan.next (EOBinaryPlaneRaw.scope
      (BinaryIsingRaw.expanded r.val k) (BinaryIsingRaw.expanded_valid r.val r.property k)))
    (BinaryCSPProgrammeMixed.rowSigns (BinaryIsingRaw.expandedPolarities r.val k))
  simpa only [nativeQuery,BinaryCSPProgrammeMixed.query,BinaryCSPProgrammeApex.expand,
    BinaryIsingRaw.expanded_edges_length] using h

theorem native_query_counts_le (r : P.Input) (k : ℕ) (hk : k<r.val.edges.length) :
    (nativeQuery (r,k)).val.vertices.length≤3*r.val.edges.length^2 ∧
      (nativeQuery (r,k)).val.edges.length≤6*r.val.edges.length^2 := by
  have h := native_query_counts r k
  have hb := Nat.mul_le_mul_left (r.val.edges.length*3) (show k+1≤r.val.edges.length by omega)
  rw [h.1,h.2]
  constructor <;> nlinarith

theorem empty_no_query (oracle : List Bool→List Bool)
    (ho : RepresentsOracle O.targetEncoding F.encoding (N.targetValue F M) oracle)
    (r : P.Input) (he : r.val.edges=[])
    (t : ℕ) (cfg : (controlled F M p q hm hp hq hs).reduction.machine.Cfg)
    (hr : (controlled F M p q hm hp hq hs).reduction.machine.run oracle (P.inputEncoding.encode r) t=some cfg) :
    ¬(controlled F M p q hm hp hq hs).reduction.machine.IsQuery cfg := by
  intro hc
  obtain ⟨k,hk,_⟩ := actual_query_origin F M p q hm hp hq hs oracle ho r t cfg hr hc
  simp [he] at hk

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingSource
