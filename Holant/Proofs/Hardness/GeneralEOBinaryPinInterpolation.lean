import Holant.Proofs.Hardness.GeneralGeometricCapLocal
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Tractable.Criteria
import Holant.Proofs.BinaryInterpolation.MachineCapstone
import Holant.Proofs.BinaryInterpolation.OriginalTables
import Holant.Proofs.Algorithms.TraceQueryControl

/-! Unlimited paired-pin elimination for an arbitrary original dictionary
containing a binary EO row with nonzero unequal-norm opposite entries. Every
sample replaces every pin by a real chain of the chosen original binary row.
No local directed pin or universal non-ARS classification is claimed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryPinInterpolation
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
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature K (a i.val)) (M : Signature K 2) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature K)=⟨2,M⟩)
variable (hM : Signature.CentralSupport M)
variable {d : ℕ} (F : FixedField K d)

def labels : Labelling (Network.corolla M).shape s 1 a where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst hj
  edge k := Fin.elim0 k
abbrev g := (labels G M j hj).template
abbrev hg := (labels G M j hj).wellFormed

def kernels (_ : Fin 1) : Kernel K := Signature.disequality
abbrev p := M ![false,true]
abbrev q := M ![true,false]

omit [Algebra ℚ K] [CharZero K] in
theorem template_actual : ((g G M j hj).network (hg G M j hj) G kernels).denote=M := by
  have h := Labelling.denote_template_of_labels (labels G M j hj) G kernels
    (Network.corolla M).vertex (Network.corolla M).edge
    (fun _ x=>Chains.signature_cast_apply _ _ hj _ x) (fun k=>Fin.elim0 k)
  exact h.trans (Network.denote_corolla M)

omit [Algebra ℚ K] [CharZero K] in
include hM in
theorem full_table : M=Chains.binarySignature (Local.anti (p M) (q M)) := by
  funext x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1
  · exact hM _ (by decide)
  · rfl
  · rfl
  · exact hM _ (by decide)

def targetTables : ExactSignatureTables d s 1 a where
  vertex i x := F.decode.symm (G i x)
  edge _ x y := F.decode.symm (Signature.disequality x y)

def data : MC.Data F (targetTables G F) where
  template := g G M j hj
  valid := hg G M j hj
  binary := rfl
  edge := 0
  gamma := q M
  rho := p M/q M
  geometric := true

abbrev Input := MC.Input (data G M j hj F)
abbrev inputEncoding := MC.inputEncoding (data G M j hj F)
abbrev sourceSignatures := OT.binarySlot (g G M j hj) (hg G M j hj) G
  (kernels (K:=K)) rfl (Local.anti 1 0)
def sourceValue (r : Input G M j hj F) : K :=
  (r.val.realize r.property (sourceSignatures G M j hj) kernels).denote Fin.elim0

omit [Algebra ℚ K] [CharZero K] in
theorem source_old (i : Fin s) :
    (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G M j hj) i.val,
      sourceSignatures G M j hj ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ : AnySignature K)=
    ⟨a i.val,G i⟩ :=
  OT.binarySlot_old (g G M j hj) (hg G M j hj) G kernels rfl (Local.anti 1 0) i

omit [Algebra ℚ K] [CharZero K] in
theorem source_pin :
    (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G M j hj) s,
      sourceSignatures G M j hj Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.newLabel⟩ : AnySignature K)=
    ⟨2,fun x=>if x 0=false ∧ x 1=true then 1 else 0⟩ := by
  rw [OT.binarySlot_new]
  congr 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [Chains.binarySignature,Local.anti,h0,h1]

omit [CharZero K] in
theorem query_count (r : Input G M j hj F) :
    (Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.queries (data G M j hj F) r).length=
      occurrences s r.val+1 :=
  Holant.LocalDrafts.BinaryInterpolation.EncodedBatch.query_count a (g G M j hj) (hg G M j hj) rfl 0 r

omit [CharZero K] in
theorem target_value (r : ExactSignatureTables.Input s 1 a) :
    (targetTables G F).evaluate F r=
      (r.val.realize r.property G kernels).denote Fin.elim0 := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,targetTables,LinearEquiv.apply_symm_apply]
  rfl

omit [Algebra ℚ K] [CharZero K] in
include hM in
theorem macro_value : ((g G M j hj).network (hg G M j hj) G kernels).denote=
    Chains.binarySignature (Local.anti (p M) (q M)) := by
  exact (template_actual G M j hj).trans (full_table M hM)

variable (hp : p M≠0) (hq : q M≠0)
  (hinf : ∀ n : ℕ,0<n → (p M/q M)^n≠1)

omit [Algebra ℚ K] [CharZero K] in
include hp hq hinf in
theorem nodes_injective (m : ℕ) : Function.Injective
    (WeightFormulas.nodes true (p M/q M) m) :=
  geometric_nodes_injective _ (div_ne_zero hp hq) hinf

include hM hp hq hinf in
theorem recovery (r : Input G M j hj F) :
    MC.interpolatedValue (data G M j hj F) r=sourceValue G M j hj F r := by
  let S := OT.tables (g G M j hj) (hg G M j hj) G (kernels (K:=K))
  let L := OT.binarySlot (g G M j hj) (hg G M j hj) G (kernels (K:=K)) rfl (Local.anti 0 1)
  let R := sourceSignatures G M j hj
  have hB : (⟨Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.A (s:=s) a (g G M j hj) s,
      S Holant.LocalDrafts.BinaryInterpolation.PhysicalQueries.newLabel⟩ : AnySignature K)=
      ⟨2,Chains.binarySignature (Local.anti (p M) (q M))⟩ :=
    (OT.tables_new (g G M j hj) (hg G M j hj) G kernels).trans
      (congrArg (fun f : Signature K 2=>(⟨2,f⟩ : AnySignature K)) (macro_value G M j hj hM))
  have hr := PQ.recovery a (g G M j hj) (hg G M j hj) rfl (0 : Fin 1)
    S L R G (kernels (K:=K))
    (Local.anti (p M) (q M)) (Local.anti 0 1) (Local.anti 1 0)
    (q M) (fun n=>(p M/q M)^n) hB
    (OT.binarySlot_new (g G M j hj) (hg G M j hj) G kernels rfl (Local.anti 0 1))
    (OT.binarySlot_new (g G M j hj) (hg G M j hj) G kernels rfl (Local.anti 1 0))
    rfl (Local.normalized (p M) (q M) hq) 1
    (OT.tables_local (g G M j hj) (hg G M j hj) G kernels) r one_ne_zero hq
    (nodes_injective M hp hq hinf _)
  dsimp only [S,R,sourceSignatures] at hr
  rw [OT.right_eq_binarySlot] at hr
  change commonNumerator _ (MC.values (data G M j hj F) r)/BinaryInterpolation.commonDenominator _=_
  have hs : ∀ i : Fin (occurrences s r.val+1),
      WeightFormulas.scales (q M) (occurrences s r.val) i≠0 := fun i=>pow_ne_zero _ hq
  change commonNumerator (queryDenominator
      (WeightFormulas.nodes true (p M/q M) (occurrences s r.val))
      (WeightFormulas.scales (q M) (occurrences s r.val))) (MC.values (data G M j hj F) r) /
      BinaryInterpolation.commonDenominator (queryDenominator
      (WeightFormulas.nodes true (p M/q M) (occurrences s r.val))
      (WeightFormulas.scales (q M) (occurrences s r.val)))=_
  rw [←recover_normalized_common _ _ _ (nodes_injective M hp hq hinf _) hs]
  have hn : WeightFormulas.nodes true (p M/q M) (occurrences s r.val)=
      (fun i : Fin (occurrences s r.val+1)=>(p M/q M)^(i.val+1)) := rfl
  rw [hn]
  simpa only [MC.values,data,target_value,WeightFormulas.scales,
    ite_true,one_mul,←pow_mul,sourceValue,sourceSignatures,
    Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.count,S,R] using hr

/-- The literal finite machine, with same-field answers and original-only queries. -/
def source : LengthControlledOracleReduction (inputEncoding G M j hj F) F.encoding
    (MC.queryEncoding (s:=s) (b:=1) (arity:=a)) F.encoding
    (sourceValue G M j hj F) ((targetTables G F).evaluate F) where
  reduction := {
    machine := (MC.reduction (data G M j hj F)).machine
    time := (MC.reduction (data G M j hj F)).time
    correct oracle ho r := by
      rw [←recovery G M j hj hM F hp hq hinf r]
      exact (MC.reduction (data G M j hj F)).correct oracle ho r }
  targetOutput := (targetTables G F).outputBound F
  queryBound := (MC.pre (data G M j hj F)).outputBound.bound
  safeQuery oracle ho r t c hr hquery := by
    obtain ⟨n,_,ht⟩ := MC.execution (data G M j hj F) oracle ho r
    have hm := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member ht t c hr hquery
    obtain ⟨z,hmem,he⟩ := List.mem_map.mp hm
    exact ⟨z,he.symm,(member_length_le _ _ hm).trans
      (query_context_length_le (MC.pre (data G M j hj F)) r).1⟩

section UnequalNorms
variable {L : Type} [NormedField L] [Algebra ℚ L] [CharZero L]
variable {t : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin t)→Signature L (arity i.val)) (B : Signature L 2) (index : Fin t)
variable (hindex : (⟨arity index.val,H index⟩ : AnySignature L)=⟨2,B⟩)
variable (he : Signature.CentralSupport B)
variable {d : ℕ} (field : FixedField L d)
variable (hleft : p B≠0) (hright : q B≠0) (hnorm : ‖p B‖≠‖q B‖)

/-- The separation of all finite interpolation nodes follows from original
opposite norms, with no supplied infinite-order or termination certificate. -/
def unequalNormSource : LengthControlledOracleReduction (inputEncoding H B index hindex field) field.encoding
    (MC.queryEncoding (s:=t) (b:=1) (arity:=arity)) field.encoding
    (sourceValue H B index hindex field) ((targetTables H field).evaluate field) :=
  source H B index hindex he field hleft hright
    (Local.infinite_of_unequal_norms (p B) (q B) hright hnorm)
end UnequalNorms

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOBinaryPinInterpolation
