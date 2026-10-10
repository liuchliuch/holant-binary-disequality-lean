import Holant.Proofs.Hardness.EightVertexCancellationLocal
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement for the literal two-copy eight-vertex cancellation gadget.
The generated and original evaluations use the same fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export EightVertexCancellationLocal (output template valid template_denote counts)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (he : Holant.LocalDrafts.Hardness.EightVertexNonexception.EvenSupport M)

def templates (_M : Signature K 4) (_i : ℕ) : Template := N.template

omit [Algebra ℚ K] [Field K] in
theorem valid : ∀i<1,(templates M i).WellFormed 1 1 Q.arity := fun _ _=>N.valid

omit [Algebra ℚ K] [Field K] in
theorem arity_exact : sourceArity (templates M)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates M) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (N.output M x)

include he in
theorem template_denote (i : Fin 1) :
    ((templates M i.val).network (valid M i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (M)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (M)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F M i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template).network (N.valid)
    (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • N.output M
  rw [one_smul]
  exact N.template_denote M he

abbrev generatedValue :=
  (sourceTables (templates M) (V.tables F (M)) (coordinates F M)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F M r=V.value (N.output M) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates M) 1 Q.arity
    (compilerHypotheses (templates M) (valid M))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query M) :=
  Compiler.computes 1 1 Q.arity (templates M) 1 Q.arity
    (compilerHypotheses (templates M) (valid M))

omit [Algebra ℚ K] [Field K] in
theorem query_counts (r : Q.TargetInput) :
    (query M r).val.vertices.length=2*r.val.vertices.length ∧
    (query M r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates M row.1).vertices.length=2 := (N.counts).1
  have he (row : RawVertex) : (templates M row.1).edges.length=2 := (N.counts).2
  change (replace (templates M) r.val).vertices.length=_ ∧
    (replace (templates M) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

omit [Algebra ℚ K] in
include he in
theorem query_value (r : Q.TargetInput) :
    V.value (M) (query M r)=V.value (N.output M) r := by
  have hp := replacement_scale_power (templates M) r.val r.property (valid M)
    (V.signatures (N.output M)) (V.signatures (M)) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template).network (N.valid)
        (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • N.output M
      simpa using N.template_denote M he)
  have hv : V.value (M) (query M r)=
      (1 : K)^occurrences 0 r.val*V.value (N.output M) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F M) ((V.tables F (M)).evaluate F) :=
  Cap.controlledSubstitution F (templates M) (valid M)
    (V.tables F (M)) (coordinates F M)
    0 (1 : K) (by simp) (template_denote F M he)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (N.output M)) (V.value (M)) := by
  have r := substitution F M he
  have hs : generatedValue F M=V.value (N.output M) := funext (source_value F M)
  have ht : (V.tables F (M)).evaluate F=V.value (M) :=
    funext (V.evaluate F (M))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexCancellationStageAccess
