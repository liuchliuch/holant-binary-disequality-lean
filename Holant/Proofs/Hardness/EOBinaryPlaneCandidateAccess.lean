import Holant.Proofs.Hardness.EOBinaryPlaneCandidateGadgets
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! Same-field physical programmes for every one of the five explicit binary
coefficient candidates. Every query contains only original-table vertices and
native-X edges, with at most two vertices per replaced occurrence. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateAccess
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export EOBinaryPlaneCandidateGadgets (output template valid template_denote counts_exact)
end N
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (f : Signature K 2) (kind : Fin 5)

def output := B.lift (N.output f kind)
def templates (_ : ℕ) : Template := N.template kind

theorem valid : ∀i<1,(templates kind i).WellFormed 1 1 Q.arity := fun _ _=>N.valid kind

theorem arity_exact : sourceArity (templates kind)=Q.arity := rfl

def coordinates (i : Fin 1) (x : Fin (sourceArity (templates kind) i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (output f kind x)

theorem template_value (i : Fin 1) :
    ((templates kind i.val).network (valid kind i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (B.lift f)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (B.lift f)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F f kind i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template kind).network (N.valid kind)
    (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • output f kind
  rw [one_smul]
  exact N.template_denote f kind

abbrev generatedValue :=
  (sourceTables (templates kind) (V.tables F (B.lift f)) (coordinates F f kind)).evaluate F

theorem source_value (r : Q.TargetInput) : generatedValue F f kind r=V.value (output f kind) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates kind) 1 Q.arity
    (compilerHypotheses (templates kind) (valid kind))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query kind) :=
  Compiler.computes 1 1 Q.arity (templates kind) 1 Q.arity
    (compilerHypotheses (templates kind) (valid kind))

theorem query_counts (r : Q.TargetInput) :
    (query kind r).val.vertices.length=(if kind.val<2 then 1 else 2)*r.val.vertices.length ∧
      (query kind r).val.edges.length=r.val.edges.length+
        (if kind.val<2 then 0 else 2)*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates kind row.1).vertices.length=
      (if kind.val<2 then 1 else 2) := (N.counts_exact kind).1
  have he (row : RawVertex) : (templates kind row.1).edges.length=
      (if kind.val<2 then 0 else 2) := (N.counts_exact kind).2
  change (replace (templates kind) r.val).vertices.length=_ ∧
    (replace (templates kind) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

def substitution : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.targetEncoding F.encoding (generatedValue F f kind) ((V.tables F (B.lift f)).evaluate F) :=
  Cap.controlledSubstitution F (templates kind) (valid kind) (V.tables F (B.lift f))
    (coordinates F f kind) 0 (1 : K) (by simp) (template_value F f kind)

attribute [local irreducible] substitution

def source : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.targetEncoding F.encoding (V.value (output f kind)) (V.value (B.lift f)) := by
  have r := substitution F f kind
  have hs : generatedValue F f kind=V.value (output f kind) := funext (source_value F f kind)
  have ht : (V.tables F (B.lift f)).evaluate F=V.value (B.lift f) := funext (V.evaluate F (B.lift f))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCandidateAccess
