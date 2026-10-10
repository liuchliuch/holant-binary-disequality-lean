import Holant.Proofs.Hardness.ComplexFiveSupportLocal
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement for the literal one-, two- and four-copy five-support gadgets.
The generated and original evaluations use the same fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export ComplexFiveSupportLocal (output template valid template_denote counts)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (j : Fin 6) (k : Fin 3) (he : DenseEOUnitLocal.EOSupport M)

def templates (_i : ℕ) : Template := N.template M j k

omit [Algebra ℚ K] in
theorem valid : ∀i<1,(templates M j k i).WellFormed 1 1 Q.arity := fun _ _=>N.valid M j k

omit [Algebra ℚ K] in
theorem arity_exact : sourceArity (templates M j k)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates M j k) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (N.output M j k x)

include he in
theorem template_denote (i : Fin 1) :
    ((templates M j k i.val).network (valid M j k i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (M)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (M)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F M j k i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template M j k).network (N.valid M j k)
    (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • N.output M j k
  rw [one_smul]
  exact N.template_denote M he j k

abbrev generatedValue :=
  (sourceTables (templates M j k) (V.tables F (M)) (coordinates F M j k)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F M j k r=V.value (N.output M j k) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates M j k) 1 Q.arity
    (compilerHypotheses (templates M j k) (valid M j k))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query M j k) :=
  Compiler.computes 1 1 Q.arity (templates M j k) 1 Q.arity
    (compilerHypotheses (templates M j k) (valid M j k))

omit [Algebra ℚ K] in
theorem query_counts (r : Q.TargetInput) :
    (query M j k r).val.vertices.length=(![1,2,4] k)*r.val.vertices.length ∧
    (query M j k r).val.edges.length=r.val.edges.length+(![0,2,6] k)*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates M j k row.1).vertices.length=![1,2,4] k := (N.counts M j k).1
  have he (row : RawVertex) : (templates M j k row.1).edges.length=![0,2,6] k := (N.counts M j k).2
  change (replace (templates M j k) r.val).vertices.length=_ ∧
    (replace (templates M j k) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

omit [Algebra ℚ K] in
include he in
theorem query_value (r : Q.TargetInput) :
    V.value (M) (query M j k r)=V.value (N.output M j k) r := by
  have hp := replacement_scale_power (templates M j k) r.val r.property (valid M j k)
    (V.signatures (N.output M j k)) (V.signatures (M)) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template M j k).network (N.valid M j k)
        (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • N.output M j k
      simpa using N.template_denote M he j k)
  have hv : V.value (M) (query M j k r)=
      (1 : K)^occurrences 0 r.val*V.value (N.output M j k) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F M j k) ((V.tables F (M)).evaluate F) :=
  Cap.controlledSubstitution F (templates M j k) (valid M j k)
    (V.tables F (M)) (coordinates F M j k)
    0 (1 : K) (by simp) (template_denote F M j k he)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (N.output M j k)) (V.value (M)) := by
  have r := substitution F M j k he
  have hs : generatedValue F M j k=V.value (N.output M j k) := funext (source_value F M j k)
  have ht : (V.tables F (M)).evaluate F=V.value (M) :=
    funext (V.evaluate F (M))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexFiveSupportStageAccess
