import Holant.Proofs.Hardness.RealDensePortNormalize
import Holant.Proofs.Hardness.ThreeModeGraphEvaluation
import Holant.Proofs.Reductions.ControlledCap

/-! Actual all-occurrence replacement by the literal one-M/zero-X template.
The ordered boundary permutation carries scale exactly one.
The source and target use one fixed field presentation; no extension or
realizability certificate is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDensePortStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace N
export RealDensePortNormalize (normalized template valid template_denote)
end N
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (k : Fin 3)
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
  F.decode.symm (N.normalized M k x)

theorem template_denote (i : Fin 1) :
    ((templates M k i.val).network (valid M k i.val i.isLt)
      (fun j x=>F.decode ((tables F M).vertex j x))
      (fun j x y=>F.decode ((tables F M).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F M k i x)) := by
  fin_cases i
  simp only [tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template M k).network (N.valid M k) (fun _ : Fin 1=>M)
    (fun _ : Fin 1=>Signature.disequality)).denote=(1 : K) • N.normalized M k
  rw [one_smul]
  exact N.template_denote M k

abbrev generatedValue := (sourceTables (templates M k) (tables F M) (coordinates F M k)).evaluate F

theorem source_value (r : Q.TargetInput) : generatedValue F M k r=value (N.normalized M k) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates M k) 1 Q.arity (compilerHypotheses (templates M k) (valid M k))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query M k) :=
  Compiler.computes 1 1 Q.arity (templates M k) 1 Q.arity (compilerHypotheses (templates M k) (valid M k))

omit [Algebra ℚ K] in
theorem query_counts (r : Q.TargetInput) :
    (query M k r).val.vertices.length=r.val.vertices.length ∧
    (query M k r).val.edges.length=r.val.edges.length := by
  have hv (row : RawVertex) : (templates M k row.1).vertices.length=1 := (RealDensePortNormalize.counts M k).1
  have he (row : RawVertex) : (templates M k row.1).edges.length=0 := (RealDensePortNormalize.counts M k).2
  change (replace (templates M k) r.val).vertices.length=_ ∧ (replace (templates M k) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.map_const,List.sum_replicate,Nat.mul_comm]

omit [Algebra ℚ K] in
theorem query_value (r : Q.TargetInput) :
    value M (query M k r)=(1 : K) ^ occurrences 0 r.val * value (N.normalized M k) r := by
  have hp := replacement_scale_power (templates M k) r.val r.property (valid M k)
    (signatures (N.normalized M k)) (signatures M) kernels 0 (1 : K) (fun i=>by
      fin_cases i
      change ((N.template M k).network (N.valid M k)
        (fun _ : Fin 1=>M) (fun _ : Fin 1=>Signature.disequality)).denote=
          (1 : K) • N.normalized M k
      simpa using N.template_denote M k)
  exact hp

theorem recovery (r : Q.TargetInput) :
    value M (query M k r)*(1 : K)⁻¹ ^ occurrences 0 r.val=value (N.normalized M k) r := by
  rw [query_value M k]
  exact ScalarPower.cancel_scale_power (1 : K) _ (by simp) (occurrences 0 r.val)

def substitution :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (generatedValue F M k) ((tables F M).evaluate F) :=
  Cap.controlledSubstitution F (templates M k) (valid M k) (tables F M) (coordinates F M k)
    0 (1 : K) (by simp) (template_denote F M k)

attribute [local irreducible] substitution

def source :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (value (N.normalized M k)) (value M) := by
  have r := substitution F M k
  have hs : generatedValue F M k=value (N.normalized M k) := funext (source_value F M k)
  have ht : (tables F M).evaluate F=value M := funext (evaluate F M)
  rw [hs,ht] at r
  exact r

def outputs (oracle : List Bool→List Bool)
    (ho : RepresentsOracle Q.targetEncoding F.encoding (value M) oracle) (r : Q.TargetInput) :=
  (source F M k).reduction.correct oracle ho r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDensePortStageAccess
