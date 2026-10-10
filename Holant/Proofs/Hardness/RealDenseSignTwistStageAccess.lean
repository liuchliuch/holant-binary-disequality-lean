import Holant.Proofs.Hardness.RealDenseSignTwist
import Holant.Proofs.Hardness.ThreeModeGraphEvaluation
import Holant.Proofs.Reductions.ControlledCap

/-! Actual all-occurrence replacement by the literal two-M/two-X template.
The original occurrence count controls the physical inverse-power correction.
The source and target use one fixed field presentation; no extension or
realizability certificate is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSignTwistStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace N
export AntiselfdualNormalize (normalized template valid)
end N
structure Applicable {K : Type*} [Field K] (M : Signature K 4) (k : Fin 6) (p : K) : Prop where
  even : EvenSupport M
  cap : RealDenseSignTwist.AntisymmetricCap M k p
  nonzero : p≠0
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (k : Fin 6) (p : K)
local instance fieldCharZero : CharZero K := algebraRat.charZero K

def signatures (_i : Fin 1) : Signature K (Q.arity _i.val) := M
def kernels (_i : Fin 1) : Kernel K := Signature.disequality

def value (r : Q.TargetInput) : K :=
  (r.val.realize r.property (signatures M) kernels).denote Fin.elim0

def tables : ExactSignatureTables d 1 1 Q.arity where
  vertex i x := F.decode.symm (signatures M i x)
  edge i x y := F.decode.symm (kernels i x y)

theorem evaluate (r : Q.TargetInput) : (tables F M).evaluate F r=value M r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,tables,LinearEquiv.apply_symm_apply]
  rfl

def templates (_i : ℕ) : Template := N.template M k

omit [Algebra ℚ K] in
theorem valid : ∀i<1,(templates M k i).WellFormed 1 1 Q.arity := fun _ _=>N.valid M k

omit [Algebra ℚ K] in
theorem arity_exact : sourceArity (templates M k)=Q.arity := rfl

def coordinates (_i : Fin 1) (x : Fin (sourceArity (templates M k) _i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (N.normalized M x)

theorem template_denote (h : Applicable M k p) (i : Fin 1) :
    ((templates M k i.val).network (valid M k i.val i.isLt)
      (fun j x=>F.decode ((tables F M).vertex j x))
      (fun j x y=>F.decode ((tables F M).edge j x y))).denote=
      (if i.val=0 then p else 1) • (fun x=>F.decode (coordinates F M k i x)) := by
  fin_cases i
  simp only [tables,coordinates,LinearEquiv.apply_symm_apply]
  exact RealDenseSignTwist.template_denote M h.even k p h.cap

abbrev generatedValue := (sourceTables (templates M k) (tables F M) (coordinates F M k)).evaluate F

theorem source_value (r : Q.TargetInput) : generatedValue F M k r=value (N.normalized M) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates M k) 1 Q.arity (compilerHypotheses (templates M k) (valid M k))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query M k) :=
  Compiler.computes 1 1 Q.arity (templates M k) 1 Q.arity (compilerHypotheses (templates M k) (valid M k))

omit [Algebra ℚ K] in
theorem query_counts (r : Q.TargetInput) :
    (query M k r).val.vertices.length=2*r.val.vertices.length ∧
    (query M k r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates M k row.1).vertices.length=2 := (RealDenseSignTwist.counts M k).1
  have he (row : RawVertex) : (templates M k row.1).edges.length=2 := (RealDenseSignTwist.counts M k).2
  change (replace (templates M k) r.val).vertices.length=_ ∧ (replace (templates M k) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.map_const,List.sum_replicate,Nat.mul_comm]

omit [Algebra ℚ K] in
theorem query_value (h : Applicable M k p) (r : Q.TargetInput) :
    value M (query M k r)=p ^ occurrences 0 r.val * value (N.normalized M) r := by
  have hp := replacement_scale_power (templates M k) r.val r.property (valid M k)
    (signatures (N.normalized M)) (signatures M) kernels 0 (p) (fun i=>by
      fin_cases i
      change ((N.template M k).network (N.valid M k)
        (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
          p • N.normalized M
      exact RealDenseSignTwist.template_denote M h.even k p h.cap)
  exact hp

theorem recovery (h : Applicable M k p) (r : Q.TargetInput) :
    value M (query M k r)*(p)⁻¹ ^ occurrences 0 r.val=value (N.normalized M) r := by
  rw [query_value M k p h]
  exact ScalarPower.cancel_scale_power (p) _ (h.nonzero) (occurrences 0 r.val)

def substitution (h : Applicable M k p) :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F M k) ((tables F M).evaluate F) :=
  Cap.controlledSubstitution F (templates M k) (valid M k) (tables F M) (coordinates F M k)
    0 (p) (h.nonzero) (template_denote F M k p h)

attribute [local irreducible] substitution

def source (h : Applicable M k p) :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (value (N.normalized M)) (value M) := by
  have r := substitution F M k p h
  have hs : generatedValue F M k=value (N.normalized M) := funext (source_value F M k)
  have ht : (tables F M).evaluate F=value M := funext (evaluate F M)
  rw [hs,ht] at r
  exact r

def outputs (h : Applicable M k p) (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (value M) oracle) (r : Q.TargetInput) :=
  (source F M k p h).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSignTwistStageAccess
