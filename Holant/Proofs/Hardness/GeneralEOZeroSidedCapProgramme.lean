import Holant.Proofs.Hardness.GeneralEOOriginalCapInterpolation
import Holant.Proofs.Reductions.ControlledCap
import Holant.Complexity.BinaryInterpolation.Chains.Compiler.OriginalCounts

/-! An actual one-original-vertex cap with middle coefficients p ≠ 0 and
q = 0 supplies arbitrarily many directed01 pins by scalar-corrected physical
substitution. Every pin is replaced by the cap; there is no pin oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapProgramme
open Computability Holant Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
namespace I
export GeneralEOOriginalCapInterpolation
  (g hg cap p q kernels targetTables sourceSignatures sourceValue source_old source_pin)
end I
namespace C
export Holant.LocalDrafts.Hardness.ControlledCap (scaledAdjoin)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {d s r : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature K (a i.val)) (j : Fin s)
variable (e : Fin (a j.val) ≃ (Fin 2 ⊕ (Fin r×Bool)))
variable (F : FixedField K d)

abbrev templates := Adjoin.templates s a (I.g G j e)
abbrev valid := Adjoin.wellFormed (I.g G j e) (I.hg G j e)
abbrev A := sourceArity (templates G j e)
abbrev Input := ExactSignatureTables.Input (s+1) 1 (A G j e)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (s+1) 1 (A G j e)
abbrev targetEncoding := RawClosedNetwork.validatedEncoding s 1 a
abbrev coordinates := ScaledAdjoin.coordinates F (I.targetTables G F)
  (I.g G j e) (I.hg G j e) (I.p G j e)
abbrev tables := sourceTables (templates G j e) (I.targetTables G F) (coordinates G j e F)
def signatures (i : Fin (s+1)) : Signature K (A G j e i.val) :=
  fun x => F.decode ((tables G j e F).vertex i x)
abbrev value := (tables G j e F).evaluate F

/-- The source codec has no promise on how many appended labels occur. -/
abbrev query := Compiler.value (s+1) 1 (A G j e) (templates G j e) s a
  (compilerHypotheses (templates G j e) (valid G j e))
abbrev pre := Compiler.withOccurrencesComputes (s+1) 1 (A G j e) (templates G j e) s a
  (compilerHypotheses (templates G j e) (valid G j e)) s

private def decodeAny (z : AnySignature (Fin d→ℚ)) : AnySignature K :=
  ⟨z.1,fun x=>F.decode (z.2 x)⟩

/-- Coincident original rows still keep their separate original labels. -/
theorem old_signature (i : Fin s) :
    (⟨A G j e i.val,signatures G j e F ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
      AnySignature K)=⟨a i.val,G i⟩ := by
  have h : (⟨A G j e i.val,
      coordinates G j e F ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩⟩ :
        AnySignature (Fin d→ℚ))=⟨a i.val,(I.targetTables G F).vertex i⟩ :=
    Sigma.ext (Adjoin.old_boundary (I.g G j e) i)
      (ScaledAdjoin.old_coordinates F (I.targetTables G F) (I.g G j e) (I.hg G j e) (I.p G j e) i)
  have hh := congrArg (decodeAny F) h
  change (⟨A G j e i.val,fun x=>F.decode (coordinates G j e F ⟨i.val,Nat.lt_trans i.isLt (Nat.lt_succ_self s)⟩ x)⟩ : AnySignature K)=_
  simpa only [decodeAny,I.targetTables,LinearEquiv.apply_symm_apply] using hh

variable (he : Signature.CentralSupport (G j))
variable (hp : I.p G j e≠0) (hq : I.q G j e=0)

include he hq in
/-- The scalar belongs to the same coefficient field as the actual graph. -/
theorem macro_scaled :
    ((I.g G j e).network (I.hg G j e) G I.kernels).denote=
      I.p G j e • (fun x : Fin 2→Bool=>if x 0=false ∧ x 1=true then (1:K) else 0) := by
  rw [GeneralEOOriginalCapInterpolation.macro_value G j e he,hq]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [BinaryInterpolation.Chains.binarySignature,GeneralGeometricCapLocal.anti,h0,h1]

include he hp hq in
/-- The appended row is literally directed01, with its ordered ports fixed. -/
theorem new_signature :
    (⟨A G j e s,signatures G j e F ⟨s,Nat.lt_succ_self s⟩⟩ : AnySignature K)=
      ⟨2,fun x=>if x 0=false ∧ x 1=true then 1 else 0⟩ := by
  have h : (⟨A G j e s,coordinates G j e F ⟨s,Nat.lt_succ_self s⟩⟩ :
      AnySignature (Fin d→ℚ))=⟨2,fun x=>F.decode.symm
        (((I.g G j e).network (I.hg G j e)
          (fun i y=>F.decode ((I.targetTables G F).vertex i y))
          (fun i u v=>F.decode ((I.targetTables G F).edge i u v))).denote x/I.p G j e)⟩ :=
    Sigma.ext (Adjoin.new_boundary (I.g G j e))
      (ScaledAdjoin.new_coordinates F (I.targetTables G F) (I.g G j e) (I.hg G j e) (I.p G j e))
  refine (congrArg (decodeAny F) h).trans ?_
  simp only [decodeAny,I.targetTables,LinearEquiv.apply_symm_apply]
  change (⟨2,fun x=>((I.g G j e).network (I.hg G j e) G I.kernels).denote x/I.p G j e⟩ :
    AnySignature K)=_
  rw [macro_scaled G j e he hq]
  congr 1
  funext x
  exact mul_div_cancel_left₀ _ hp

include he hp hq in
theorem signatures_literal : signatures G j e F=I.sourceSignatures G j e := by
  funext i
  by_cases hi : i.val=s
  · have hi' : i=⟨s,Nat.lt_succ_self s⟩ := Fin.ext hi
    subst i
    exact eq_of_heq (Sigma.mk.inj ((new_signature G j e F he hp hq).trans
      (I.source_pin G j e).symm)).2
  · have hil : i.val<s := by omega
    let old : Fin s := ⟨i.val,hil⟩
    exact eq_of_heq (Sigma.mk.inj ((old_signature G j e F old).trans
      (I.source_old G j e old).symm)).2

include he hp hq in
theorem value_literal (x : Input G j e) :
    value G j e F x=(x.val.realize x.property (I.sourceSignatures G j e) I.kernels).denote Fin.elim0 := by
  unfold value
  rw [ExactSignatureTables.evaluate_eq_decoded]
  change (x.val.realize x.property (signatures G j e F)
    (fun i u v=>F.decode ((I.targetTables G F).edge i u v))).denote Fin.elim0=_
  rw [signatures_literal G j e F he hp hq]
  simp only [I.targetTables,LinearEquiv.apply_symm_apply]
  rfl

/-- The finite Boolean programme compiles every cap and inverts p once per
actual pin occurrence, using the same field encoding at both ends. -/
def source : LengthControlledOracleReduction (inputEncoding G j e) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (value G j e F) ((I.targetTables G F).evaluate F) :=
  C.scaledAdjoin F (I.targetTables G F) (I.g G j e) (I.hg G j e) (I.p G j e) hp

include hp in
theorem local_denote (i : Fin (s+1)) :
    ((templates G j e i.val).network (valid G j e i.val i.isLt) G I.kernels).denote=
      (if i.val=s then I.p G j e else 1) • signatures G j e F i := by
  funext x
  change _=(if i.val=s then I.p G j e else 1)*F.decode (coordinates G j e F i x)
  unfold coordinates ScaledAdjoin.coordinates ScaledAdjoin.rescale
  rw [LinearEquiv.apply_symm_apply]
  dsimp only [Adjoin.coordinates]
  rw [decode_templateCoordinates]
  simp only [I.targetTables,LinearEquiv.apply_symm_apply]
  have hn : (if i.val=s then I.p G j e else 1)≠0 := by split_ifs <;> simp_all
  field_simp
  rfl

include hp in
theorem query_value (x : Input G j e) :
    (I.targetTables G F).evaluate F (query G j e x)=
      (I.p G j e)^occurrences s x.val*value G j e F x := by
  have h := replacement_scale_power (templates G j e) x.val x.property (valid G j e)
    (signatures G j e F) G I.kernels s (I.p G j e) (local_denote G j e F hp)
  unfold value
  simp only [ExactSignatureTables.evaluate_eq_decoded,tables,sourceTables,I.targetTables,LinearEquiv.apply_symm_apply]
  exact h

include hp in
theorem corrected_value (x : Input G j e) :
    (I.targetTables G F).evaluate F (query G j e x)*(I.p G j e)⁻¹^occurrences s x.val=
      value G j e F x := by
  rw [query_value G j e F hp]
  exact FixedFieldMachines.ScalarPower.cancel_scale_power _ _ hp _

/-- The semantic input is literally the original palette plus directed01. -/
def pinValue (x : Input G j e) : K :=
  (x.val.realize x.property (I.sourceSignatures G j e) I.kernels).denote Fin.elim0

include he hp hq in
theorem pin_recovery (x : Input G j e) :
    pinValue G j e x=(I.targetTables G F).evaluate F (query G j e x)*
      (I.p G j e)⁻¹^occurrences s x.val :=
  (value_literal G j e F he hp hq x).symm.trans (corrected_value G j e F hp x).symm

/-- A literal-pin caller with unrestricted pin multiplicity and one physical
original-family oracle call, including the actual occurrence-count correction. -/
def literalSource : LengthControlledOracleReduction (inputEncoding G j e) F.encoding
    (targetEncoding (s:=s) (a:=a)) F.encoding (pinValue G j e) ((I.targetTables G F).evaluate F) :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq (pre G j e)
    (FixedFieldMachines.ScalarPower.correction F (I.p G j e))
    ((I.targetTables G F).outputBound F) (pinValue G j e) (pin_recovery G j e F he hp hq)

theorem literalSource_machine : (literalSource G j e F he hp hq).reduction.machine=
    OracleOneQuery.Context.machine (pre G j e).machine
      (FixedFieldMachines.ScalarPower.correction F (I.p G j e)).machine :=
  Holant.LocalDrafts.Hardness.ControlledCap.controlledContextOfEq_machine _ _ _ _ _

theorem atMostOne : UniversalPairReduction.ThreeQuery.AtMostQueries
    (literalSource G j e F he hp hq).reduction.machine 1 := by
  rw [literalSource_machine]
  exact UniversalPairReduction.SmoothingCompiler.ContextCount.atMostOne _ _

@[simp] theorem macro_vertices : (I.g G j e).vertices.length=1 := by
  simp [I.g,GeneralEOOriginalCapInterpolation.labels,Labelling.template,
    GeneralEOOriginalCapGraph.graph,GeneralEOOriginalCapGraph.shape]
@[simp] theorem macro_edges : (I.g G j e).edges.length=r := by
  simp [I.g,GeneralEOOriginalCapInterpolation.labels,Labelling.template,
    GeneralEOOriginalCapGraph.graph,GeneralEOOriginalCapGraph.shape]

theorem query_counts (x : Input G j e) :
    (query G j e x).val.vertices.length=x.val.vertices.length ∧
    (query G j e x).val.edges.length=x.val.edges.length+r*occurrences s x.val := by
  have hb : ∀v∈x.val.vertices,v.1<s+1 := by
    intro v hv
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
    exact (x.property.1 i).1
  constructor
  · have h := BinaryInterpolation.Chains.Compiler.OriginalFamily.macro_vertex_sum a
      (I.g G j e) x.val.vertices hb
    rw [←replace_vertex_count,macro_vertices] at h
    change (replace (templates G j e) x.val).vertices.length=_
    change (replace (templates G j e) x.val).vertices.length+occurrences s x.val=
      x.val.vertices.length+1*occurrences s x.val at h
    omega
  · change (replace (templates G j e) x.val).edges.length=_
    rw [replace_edge_count,BinaryInterpolation.Chains.Compiler.OriginalFamily.macro_edge_sum a _ _ hb,
      macro_edges]
    rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOZeroSidedCapProgramme
