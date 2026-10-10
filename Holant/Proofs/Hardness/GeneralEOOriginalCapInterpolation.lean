import Holant.Proofs.Hardness.GeneralEOOriginalCapGraph
import Holant.Proofs.Hardness.GeneralEOBinaryPinInterpolation
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Tractable.Criteria
import Holant.Proofs.BinaryInterpolation.MachineCapstone
import Holant.Proofs.BinaryInterpolation.OriginalTables
import Holant.Proofs.Algorithms.TraceQueryControl

/-! The actual one-original-vertex native-X cap is compiled into every sample
chain. Source instances contain the original dictionary and directed01 only;
all final oracle queries use original labels, with no free binary oracle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOOriginalCapInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose OracleBatch
open BinaryInterpolation FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Local
export GeneralGeometricCapLocal (anti normalized infinite_of_unequal_norms)
end Local
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables
  (tables binarySlot tables_new tables_local binarySlot_new binarySlot_old right_eq_binarySlot)
end OT
namespace PQ
export Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries (Source recovery)
end PQ
namespace MC
export Holant.LocalDrafts.BinaryInterpolation.MachineCapstone
  (Data Input inputEncoding queryEncoding values interpolatedValue denominator reduction execution pre)
end MC
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {s r : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature K (a i.val)) (j : Fin s)
variable (e : Fin (a j.val) ≃ (Fin 2 ⊕ (Fin r × Bool)))
variable (he : Signature.CentralSupport (G j))
variable {d : ℕ} (F : FixedField K d)

def labels : Labelling (GeneralEOOriginalCapGraph.graph e (G j)).shape s 1 a where
  vertex _ := j
  vertex_arity _ := rfl
  edge _ := 0
abbrev g := (labels G j e).template
abbrev hg := (labels G j e).wellFormed

def kernels (_ : Fin 1) : Kernel K := Signature.disequality
abbrev cap := (GeneralEOOriginalCapGraph.graph e (G j)).denote
abbrev p := cap G j e ![false,true]
abbrev q := cap G j e ![true,false]

omit [Algebra ℚ K] [CharZero K] in
theorem template_actual : ((g G j e).network (hg G j e) G kernels).denote=cap G j e := by
  apply Labelling.denote_template_of_labels (labels G j e) G kernels
    (GeneralEOOriginalCapGraph.graph e (G j)).vertex
    (GeneralEOOriginalCapGraph.graph e (G j)).edge
  · intro v x
    rfl
  · intro k x y
    rfl

omit [Algebra ℚ K] [CharZero K] in
include he in
theorem full_table : cap G j e=Chains.binarySignature (Local.anti (p G j e) (q G j e)) :=
  GeneralEOBinaryPinInterpolation.full_table (cap G j e)
    (GeneralEOOriginalCapGraph.central e (G j) he)

def targetTables : ExactSignatureTables d s 1 a where
  vertex i x := F.decode.symm (G i x)
  edge _ x y := F.decode.symm (Signature.disequality x y)

def data : MC.Data F (targetTables G F) where
  template := g G j e
  valid := hg G j e
  binary := rfl
  edge := 0
  gamma := q G j e
  rho := p G j e/q G j e
  geometric := true

abbrev Input := MC.Input (data G j e F)
abbrev inputEncoding := MC.inputEncoding (data G j e F)
abbrev sourceSignatures := OT.binarySlot (g G j e) (hg G j e) G
  (kernels (K:=K)) rfl (Local.anti 1 0)
def sourceValue (r : Input G j e F) : K :=
  (r.val.realize r.property (sourceSignatures G j e) kernels).denote Fin.elim0

omit [Algebra ℚ K] [CharZero K] in
theorem source_old (i : Fin s) :
    (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G j e) i.val,
      sourceSignatures G j e ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K)=
    ⟨a i.val,G i⟩ :=
  OT.binarySlot_old (g G j e) (hg G j e) G kernels rfl (Local.anti 1 0) i

omit [Algebra ℚ K] [CharZero K] in
theorem source_pin :
    (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G j e) s,
      sourceSignatures G j e Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.newLabel⟩ : AnySignature K)=
    ⟨2,fun x=>if x 0=false ∧ x 1=true then 1 else 0⟩ := by
  rw [OT.binarySlot_new]
  congr 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [Chains.binarySignature,Local.anti,h0,h1]

omit [CharZero K] in
theorem query_count (r : Input G j e F) :
    (Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.queries (data G j e F) r).length=
      occurrences s r.val+1 :=
  Holant.LocalDrafts.BinaryInterpolation.EncodedBatch.query_count a (g G j e) (hg G j e) rfl 0 r

omit [CharZero K] in
theorem target_value (r : ExactSignatureTables.Input s 1 a) :
    (targetTables G F).evaluate F r=
      (r.val.realize r.property G kernels).denote Fin.elim0 := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

omit [Algebra ℚ K] [CharZero K] in
include he in
theorem macro_value : ((g G j e).network (hg G j e) G kernels).denote=
    Chains.binarySignature (Local.anti (p G j e) (q G j e)) := by
  exact (template_actual G j e).trans (full_table G j e he)

variable (hp : p G j e≠0) (hq : q G j e≠0)
  (hinf : ∀ n : ℕ,0<n → (p G j e/q G j e)^n≠1)

omit [Algebra ℚ K] [CharZero K] in
include hp hq hinf in
theorem nodes_injective (m : ℕ) : Function.Injective
    (WeightFormulas.nodes true (p G j e/q G j e) m) :=
  geometric_nodes_injective _ (div_ne_zero hp hq) hinf

include he hp hq hinf in
theorem recovery (r : Input G j e F) :
    MC.interpolatedValue (data G j e F) r=sourceValue G j e F r := by
  let S := OT.tables (g G j e) (hg G j e) G (kernels (K:=K))
  let L := OT.binarySlot (g G j e) (hg G j e) G (kernels (K:=K)) rfl (Local.anti 0 1)
  let R := sourceSignatures G j e
  have hB : (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G j e) s,
      S Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.newLabel⟩ : AnySignature K)=
      ⟨2,Chains.binarySignature (Local.anti (p G j e) (q G j e))⟩ :=
    (OT.tables_new (g G j e) (hg G j e) G kernels).trans
      (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) (macro_value G j e he))
  have hr := PQ.recovery a (g G j e) (hg G j e) rfl (0 : Fin 1)
    S L R G (kernels (K:=K))
    (Local.anti (p G j e) (q G j e)) (Local.anti 0 1) (Local.anti 1 0)
    (q G j e) (fun n=>(p G j e/q G j e)^n) hB
    (OT.binarySlot_new (g G j e) (hg G j e) G kernels rfl (Local.anti 0 1))
    (OT.binarySlot_new (g G j e) (hg G j e) G kernels rfl (Local.anti 1 0))
    rfl (Local.normalized (p G j e) (q G j e) hq) 1
    (OT.tables_local (g G j e) (hg G j e) G kernels) r one_ne_zero hq
    (nodes_injective G j e hp hq hinf _)
  dsimp only [S,R,sourceSignatures] at hr
  rw [OT.right_eq_binarySlot] at hr
  change commonNumerator _ (MC.values (data G j e F) r)/BinaryInterpolation.commonDenominator _=_
  have hs : ∀ i : Fin (occurrences s r.val+1),
      WeightFormulas.scales (q G j e) (occurrences s r.val) i≠0 := fun i=>pow_ne_zero _ hq
  change commonNumerator (queryDenominator
      (WeightFormulas.nodes true (p G j e/q G j e) (occurrences s r.val))
      (WeightFormulas.scales (q G j e) (occurrences s r.val))) (MC.values (data G j e F) r) /
      BinaryInterpolation.commonDenominator (queryDenominator
      (WeightFormulas.nodes true (p G j e/q G j e) (occurrences s r.val))
      (WeightFormulas.scales (q G j e) (occurrences s r.val)))=_
  rw [←recover_normalized_common _ _ _ (nodes_injective G j e hp hq hinf _) hs]
  have hn : WeightFormulas.nodes true (p G j e/q G j e) (occurrences s r.val)=
      (fun i : Fin (occurrences s r.val+1)=>(p G j e/q G j e)^(i.val+1)) := rfl
  rw [hn]
  simpa only [MC.values,data,target_value,WeightFormulas.scales,
    ite_true,one_mul,←pow_mul,sourceValue,sourceSignatures,
    Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.count,S,R] using hr

/-- The literal finite machine, with same-field answers and original-only queries. -/
def source : LengthControlledOracleReduction (inputEncoding G j e F) F.encoding
    (MC.queryEncoding (s:=s) (b:=1) (arity:=a)) F.encoding
    (sourceValue G j e F) ((targetTables G F).evaluate F) where
  reduction := {
    machine := (MC.reduction (data G j e F)).machine
    time := (MC.reduction (data G j e F)).time
    correct oracle ho r := by
      rw [←recovery G j e he F hp hq hinf r]
      exact (MC.reduction (data G j e F)).correct oracle ho r }
  targetOutput := (targetTables G F).outputBound F
  queryBound := (MC.pre (data G j e F)).outputBound.bound
  safeQuery oracle ho r t c hr hquery := by
    obtain ⟨n,_,ht⟩ := MC.execution (data G j e F) oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hquery
    obtain ⟨z,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨z,he.symm,(member_length_le _ _ hm).trans
      (query_context_length_le (MC.pre (data G j e F)) r).1⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOOriginalCapInterpolation
