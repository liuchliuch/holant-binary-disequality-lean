import Holant.Proofs.Hardness.RealDenseSelfdualPositive
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement for the two-copy positive selfdual gadget.
The generated and original evaluations use the same fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSelfdualStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export RealDenseSelfdualPositive (positiveTriple template valid template_denote counts)
export ThreeModeSignatures (original)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b c : K) (k : Fin 3)

def normalized : Signature K 4 :=
  N.original (N.positiveTriple a b c k).1 (N.positiveTriple a b c k).2.1 (N.positiveTriple a b c k).2.2

def templates (_i : ℕ) : Template := N.template a b c k

theorem valid : ∀i<1,(templates a b c k i).WellFormed 1 1 Q.arity := fun _ _=>N.valid a b c k

theorem arity_exact : sourceArity (templates a b c k)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates a b c k) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (normalized a b c k x)

theorem template_denote (i : Fin 1) :
    ((templates a b c k i.val).network (valid a b c k i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (N.original a b c)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (N.original a b c)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F a b c k i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template a b c k).network (N.valid a b c k)
    (fun _ : Fin 1=>N.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • normalized a b c k
  rw [one_smul]
  exact N.template_denote a b c k

abbrev generatedValue :=
  (sourceTables (templates a b c k) (V.tables F (N.original a b c)) (coordinates F a b c k)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F a b c k r=V.value (normalized a b c k) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates a b c k) 1 Q.arity
    (compilerHypotheses (templates a b c k) (valid a b c k))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query a b c k) :=
  Compiler.computes 1 1 Q.arity (templates a b c k) 1 Q.arity
    (compilerHypotheses (templates a b c k) (valid a b c k))

theorem query_counts (r : Q.TargetInput) :
    (query a b c k r).val.vertices.length=2*r.val.vertices.length ∧
    (query a b c k r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates a b c k row.1).vertices.length=2 := (N.counts a b c k).1
  have he (row : RawVertex) : (templates a b c k row.1).edges.length=2 := (N.counts a b c k).2
  change (replace (templates a b c k) r.val).vertices.length=_ ∧
    (replace (templates a b c k) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

theorem query_value (r : Q.TargetInput) :
    V.value (N.original a b c) (query a b c k r)=V.value (normalized a b c k) r := by
  have hp := replacement_scale_power (templates a b c k) r.val r.property (valid a b c k)
    (V.signatures (normalized a b c k)) (V.signatures (N.original a b c)) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template a b c k).network (N.valid a b c k)
        (fun _ : Fin 1=>N.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • normalized a b c k
      simpa [normalized] using N.template_denote a b c k)
  have hv : V.value (N.original a b c) (query a b c k r)=
      (1 : K)^occurrences 0 r.val*V.value (normalized a b c k) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F a b c k) ((V.tables F (N.original a b c)).evaluate F) :=
  Cap.controlledSubstitution F (templates a b c k) (valid a b c k)
    (V.tables F (N.original a b c)) (coordinates F a b c k)
    0 (1 : K) (by simp) (template_denote F a b c k)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (normalized a b c k)) (V.value (N.original a b c)) := by
  have r := substitution F a b c k
  have hs : generatedValue F a b c k=V.value (normalized a b c k) := funext (source_value F a b c k)
  have ht : (V.tables F (N.original a b c)).evaluate F=V.value (N.original a b c) :=
    funext (V.evaluate F (N.original a b c))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSelfdualStageAccess
