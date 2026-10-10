import Holant.Proofs.Hardness.GeneralGeometricCapLocal
import Holant.Proofs.BinaryInterpolation.MachineCapstone
import Holant.Proofs.BinaryInterpolation.OriginalTables
import Holant.Proofs.Algorithms.TraceQueryControl

/-! Same-field geometric interpolation using actual one-original-vertex caps.
The finite cap choice and coefficient conditions are local inputs; the graph
query writer, field interpreter and execution bounds are the existing physical
binary interpolation machine, not supplied evaluators. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapInterpolation
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose OracleBatch
open BinaryInterpolation FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace Cap
export GeneralCancellationCapPin (Choice template valid template_actual oriented network)
end Cap
namespace Local
export GeneralGeometricCapLocal (anti normalized actual_cap)
end Local
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables
  (tables binarySlot tables_new tables_local binarySlot_new right_eq_binarySlot)
end OT
namespace PQ
export Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries (Source recovery)
end PQ
namespace MC
export Holant.LocalDrafts.BinaryInterpolation.MachineCapstone
  (Data Input inputEncoding queryEncoding values interpolatedValue denominator reduction execution pre)
end MC
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable (M : Signature K 4) (hM : EvenSupport M) (k : Cap.Choice)
variable {d : ℕ} (F : FixedField K d)
abbrev g := Cap.template M k
abbrev hg := Cap.valid M k
def original (_ : Fin 1) : Signature K 4 := M
def kernels (_ : Fin 1) : Kernel K := Signature.disequality
abbrev p := (Cap.oriented M k).1
abbrev q := (Cap.oriented M k).2

def targetTables : ExactSignatureTables d 1 1 (fun _=>4) where
  vertex _ x := F.decode.symm (M x)
  edge _ a b := F.decode.symm (Signature.disequality a b)

def data : MC.Data F (targetTables M F) where
  template := g M k
  valid := hg M k
  binary := rfl
  edge := 0
  gamma := q M k
  rho := p M k/q M k
  geometric := true

abbrev Input := MC.Input (data M k F)
abbrev inputEncoding := MC.inputEncoding (data M k F)
abbrev sourceSignatures := OT.binarySlot (g M k) (hg M k) (original M)
  (kernels (K:=K)) rfl (Local.anti 1 0)
def sourceValue (r : Input M k F) : K :=
  (r.val.realize r.property (sourceSignatures M k) kernels).denote Fin.elim0

theorem target_value (r : ExactSignatureTables.Input 1 1 (fun _=>4)) :
    (targetTables M F).evaluate F r=
      (r.val.realize r.property (original M) kernels).denote Fin.elim0 := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

include hM in
theorem macro_value : ((g M k).network (hg M k) (original M) kernels).denote=
    Chains.binarySignature (Local.anti (p M k) (q M k)) := by
  exact (Cap.template_actual M k).trans (Local.actual_cap M hM k)

variable (hp : p M k≠0) (hq : q M k≠0)
  (hinf : ∀ n : ℕ,0<n → (p M k/q M k)^n≠1)

include hp hq hinf in
theorem nodes_injective (m : ℕ) : Function.Injective
    (WeightFormulas.nodes true (p M k/q M k) m) :=
  geometric_nodes_injective _ (div_ne_zero hp hq) hinf

include hM hp hq hinf in
theorem recovery (r : Input M k F) :
    MC.interpolatedValue (data M k F) r=sourceValue M k F r := by
  let S := OT.tables (g M k) (hg M k) (original M) (kernels (K:=K))
  let L := OT.binarySlot (g M k) (hg M k) (original M) (kernels (K:=K)) rfl (Local.anti 0 1)
  let R := sourceSignatures M k
  have hB : (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=1) (fun _=>4) (g M k) 1,
      S Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.newLabel⟩ : AnySignature K)=
      ⟨2,Chains.binarySignature (Local.anti (p M k) (q M k))⟩ :=
    (OT.tables_new (g M k) (hg M k) (original M) kernels).trans
      (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) (macro_value M hM k))
  have hr := PQ.recovery (fun _=>4) (g M k) (hg M k) rfl (0 : Fin 1)
    S L R (original M) (kernels (K:=K))
    (Local.anti (p M k) (q M k)) (Local.anti 0 1) (Local.anti 1 0)
    (q M k) (fun n=>(p M k/q M k)^n) hB
    (OT.binarySlot_new (g M k) (hg M k) (original M) kernels rfl (Local.anti 0 1))
    (OT.binarySlot_new (g M k) (hg M k) (original M) kernels rfl (Local.anti 1 0))
    rfl (Local.normalized (p M k) (q M k) hq) 1
    (OT.tables_local (g M k) (hg M k) (original M) kernels) r one_ne_zero hq
    (nodes_injective M k hp hq hinf _)
  dsimp only [S,R,sourceSignatures] at hr
  rw [OT.right_eq_binarySlot] at hr
  change commonNumerator _ (MC.values (data M k F) r)/BinaryInterpolation.commonDenominator _=_
  have hs : ∀ i : Fin (occurrences 1 r.val+1),
      WeightFormulas.scales (q M k) (occurrences 1 r.val) i≠0 := fun i=>pow_ne_zero _ hq
  change commonNumerator (queryDenominator
      (WeightFormulas.nodes true (p M k/q M k) (occurrences 1 r.val))
      (WeightFormulas.scales (q M k) (occurrences 1 r.val))) (MC.values (data M k F) r) /
      BinaryInterpolation.commonDenominator (queryDenominator
      (WeightFormulas.nodes true (p M k/q M k) (occurrences 1 r.val))
      (WeightFormulas.scales (q M k) (occurrences 1 r.val)))=_
  rw [←recover_normalized_common _ _ _ (nodes_injective M k hp hq hinf _) hs]
  have hn : WeightFormulas.nodes true (p M k/q M k) (occurrences 1 r.val)=
      (fun i : Fin (occurrences 1 r.val+1)=>(p M k/q M k)^(i.val+1)) := rfl
  rw [hn]
  simpa only [MC.values,data,target_value,WeightFormulas.scales,
    ite_true,one_mul,←pow_mul,sourceValue,sourceSignatures,
    Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.count,S,R] using hr

/-- The literal finite machine, with same-field answers and original-only queries. -/
def source : LengthControlledOracleReduction (inputEncoding M k F) F.encoding
    (MC.queryEncoding (s:=1) (b:=1) (arity:=fun _=>4)) F.encoding
    (sourceValue M k F) ((targetTables M F).evaluate F) where
  reduction := {
    machine := (MC.reduction (data M k F)).machine
    time := (MC.reduction (data M k F)).time
    correct oracle ho r := by
      rw [←recovery M hM k F hp hq hinf r]
      exact (MC.reduction (data M k F)).correct oracle ho r }
  targetOutput := (targetTables M F).outputBound F
  queryBound := (MC.pre (data M k F)).outputBound.bound
  safeQuery oracle ho r t c hr hquery := by
    obtain ⟨n,_,ht⟩ := MC.execution (data M k F) oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hquery
    obtain ⟨z,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨z,he.symm,(member_length_le _ _ hm).trans
      (query_context_length_le (MC.pre (data M k F)) r).1⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralGeometricCapInterpolation
