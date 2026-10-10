import Holant.Proofs.Hardness.EOBinaryPlaneIsingGadget
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! The actual same-field two-copy complement-product substitution from the
Ising table to original lift f and native-X only. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsingAccess
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value signatures kernels tables evaluate)
end V
namespace N
export EOBinaryPlaneIsingGadget (output template template_valid template_denote counts)
end N
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (f : Signature K 2)

def output := B.lift (N.output f)
def templates (_ : ℕ) : Template := N.template

theorem valid : ∀i<1,(templates i).WellFormed 1 1 Q.arity := fun _ _=>N.template_valid

theorem arity_exact : sourceArity (templates)=Q.arity := rfl

def coordinates (i : Fin 1) (x : Fin (sourceArity (templates) i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (output f x)

theorem template_value (i : Fin 1) :
    ((templates i.val).network (valid i.val i.isLt)
      (fun j x=>F.decode ((V.tables F (B.lift f)).vertex j x))
      (fun j x y=>F.decode ((V.tables F (B.lift f)).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F f i x)) := by
  fin_cases i
  simp only [V.tables,coordinates,LinearEquiv.apply_symm_apply]
  change ((N.template).network (N.template_valid)
    (fun _ : Fin 1=>B.lift f) (fun _ : Fin 1=>Signature.disequality)).denote=
      (1 : K) • output f
  rw [one_smul]
  exact N.template_denote f

abbrev generatedValue :=
  (sourceTables (templates) (V.tables F (B.lift f)) (coordinates F f)).evaluate F

theorem source_value (r : Q.TargetInput) : generatedValue F f r=V.value (output f) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,V.tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Q.TargetInput :=
  Compiler.value 1 1 Q.arity (templates) 1 Q.arity
    (compilerHypotheses (templates) (valid))

def queryComputes : Computes Q.targetEncoding Q.targetEncoding (query) :=
  Compiler.computes 1 1 Q.arity (templates) 1 Q.arity
    (compilerHypotheses (templates) (valid))

theorem query_counts (r : Q.TargetInput) :
    (query r).val.vertices.length=2*r.val.vertices.length ∧
      (query r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates row.1).vertices.length=2 := (N.counts).2.1
  have he (row : RawVertex) : (templates row.1).edges.length=2 := (N.counts).2.2
  change (replace (templates) r.val).vertices.length=_ ∧
    (replace (templates) r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

def substitution : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.targetEncoding F.encoding (generatedValue F f) ((V.tables F (B.lift f)).evaluate F) :=
  Cap.controlledSubstitution F (templates) (valid) (V.tables F (B.lift f))
    (coordinates F f) 0 (1 : K) (by simp) (template_value F f)

attribute [local irreducible] substitution

def source : LengthControlledOracleReduction Q.targetEncoding F.encoding
    Q.targetEncoding F.encoding (V.value (output f)) (V.value (B.lift f)) := by
  have r := substitution F f
  have hs : generatedValue F f=V.value (output f) := funext (source_value F f)
  have ht : (V.tables F (B.lift f)).evaluate F=V.value (B.lift f) := funext (V.evaluate F (B.lift f))
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsingAccess
