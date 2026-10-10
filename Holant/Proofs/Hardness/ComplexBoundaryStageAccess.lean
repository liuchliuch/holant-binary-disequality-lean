import Holant.Proofs.Hardness.ComplexBoundaryEscape
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! All-occurrence exact replacement for the two-copy complex boundary escape gadget.
The generated and original evaluations use the same fixed coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundaryStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export ComplexBoundaryEscape (first second third template valid template_denote counts)
export ThreeModeSignatures (original)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (a b : K)

def normalized : Signature K 4 :=
  N.original (N.first a b) (N.second a b) (N.third a b)

def templates (_i : ℕ) : Template := N.template a b

theorem valid : ∀i<1,(templates a b i).WellFormed 1 1 Q.arity := fun _ _=>N.valid a b

theorem arity_exact : sourceArity (templates a b)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates a b) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (normalized a b x)

theorem template_denote (i : Fin 1) :
    ((templates a b i.val).network (valid a b i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (N.original a b (a+b))).vertex j x))
      (fun j x y=>F.decode ((V.tables F (N.original a b (a+b))).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F a b i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template a b).network (N.valid a b)
    (fun _ : Fin 1=>N.original a b (a+b)) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • normalized a b
  rw [one_smul]
  exact N.template_denote a b

abbrev generatedValue :=
  (sourceTables (templates a b) (V.tables F (N.original a b (a+b))) (coordinates F a b)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F a b r=V.value (normalized a b) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates a b) 1 Q.arity
    (compilerHypotheses (templates a b) (valid a b))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query a b) :=
  Compiler.computes 1 1 Q.arity (templates a b) 1 Q.arity
    (compilerHypotheses (templates a b) (valid a b))

theorem query_counts (r : Q.TargetInput) :
    (query a b r).val.vertices.length=2*r.val.vertices.length ∧
    (query a b r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates a b row.1).vertices.length=2 := (N.counts a b).1
  have he (row : RawVertex) : (templates a b row.1).edges.length=2 := (N.counts a b).2
  change (replace (templates a b) r.val).vertices.length=_ ∧
    (replace (templates a b) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

theorem query_value (r : Q.TargetInput) :
    V.value (N.original a b (a+b)) (query a b r)=V.value (normalized a b) r := by
  have hp := replacement_scale_power (templates a b) r.val r.property (valid a b)
    (V.signatures (normalized a b)) (V.signatures (N.original a b (a+b))) V.kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template a b).network (N.valid a b)
        (fun _ : Fin 1=>N.original a b (a+b)) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • normalized a b
      simpa [normalized] using N.template_denote a b)
  have hv : V.value (N.original a b (a+b)) (query a b r)=
      (1 : K)^occurrences 0 r.val*V.value (normalized a b) r := hp
  simpa only [one_pow,one_mul] using hv

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F a b) ((V.tables F (N.original a b (a+b))).evaluate F) :=
  Cap.controlledSubstitution F (templates a b) (valid a b)
    (V.tables F (N.original a b (a+b))) (coordinates F a b)
    0 (1 : K) (by simp) (template_denote F a b)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (V.value (normalized a b)) (V.value (N.original a b (a+b))) := by
  have r := substitution F a b
  have hs : generatedValue F a b=V.value (normalized a b) := funext (source_value F a b)
  have ht : (V.tables F (N.original a b (a+b))).evaluate F=V.value (N.original a b (a+b)) :=
    funext (V.evaluate F (N.original a b (a+b)))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexBoundaryStageAccess
