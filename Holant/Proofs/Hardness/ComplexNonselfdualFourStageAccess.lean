import Holant.Proofs.Hardness.ComplexNonselfdualFourCopy
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement for the four-copy EO compression gadget.
The generated and original evaluations use the same fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualFourStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export ComplexNonselfdualFourCopy (output template valid template_denote counts)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (k : Fin 3) (he : DenseEOUnitLocal.EOSupport M)

def templates (_i : ℕ) : Template := N.template M k

omit [Algebra ℚ K] in
theorem valid : ∀i<1,(templates M k i).WellFormed 1 1 Q.arity := fun _ _=>N.valid M k

omit [Algebra ℚ K] in
theorem arity_exact : sourceArity (templates M k)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates M k) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (N.output M k x)

include he in
theorem template_denote (i : Fin 1) :
    ((templates M k i.val).network (valid M k i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (M)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (M)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F M k i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template M k).network (N.valid M k)
    (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • N.output M k
  rw [one_smul]
  exact N.template_denote M he k

abbrev generatedValue :=
  (sourceTables (templates M k) (V.tables F (M)) (coordinates F M k)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F M k r=V.value (N.output M k) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates M k) 1 Q.arity
    (compilerHypotheses (templates M k) (valid M k))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query M k) :=
  Compiler.computes 1 1 Q.arity (templates M k) 1 Q.arity
    (compilerHypotheses (templates M k) (valid M k))

omit [Algebra ℚ K] in
theorem query_counts (r : Q.TargetInput) :
    (query M k r).val.vertices.length=4*r.val.vertices.length ∧
    (query M k r).val.edges.length=r.val.edges.length+6*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates M k row.1).vertices.length=4 := (N.counts M k).1
  have he (row : RawVertex) : (templates M k row.1).edges.length=6 := (N.counts M k).2
  change (replace (templates M k) r.val).vertices.length=_ ∧
    (replace (templates M k) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

omit [Algebra ℚ K] in
include he in
theorem query_value (r : Q.TargetInput) :
    V.value (M) (query M k r)=V.value (N.output M k) r := by
  have hp := replacement_scale_power (templates M k) r.val r.property (valid M k)
    (V.signatures (N.output M k)) (V.signatures (M)) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template M k).network (N.valid M k)
        (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • N.output M k
      simpa using N.template_denote M he k)
  have hv : V.value (M) (query M k r)=
      (1 : K)^occurrences 0 r.val*V.value (N.output M k) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F M k) ((V.tables F (M)).evaluate F) :=
  Cap.controlledSubstitution F (templates M k) (valid M k)
    (V.tables F (M)) (coordinates F M k)
    0 (1 : K) (by simp) (template_denote F M k he)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (N.output M k)) (V.value (M)) := by
  have r := substitution F M k he
  have hs : generatedValue F M k=V.value (N.output M k) := funext (source_value F M k)
  have ht : (V.tables F (M)).evaluate F=V.value (M) :=
    funext (V.evaluate F (M))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexNonselfdualFourStageAccess
