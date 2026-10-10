import Holant.Proofs.Hardness.EOBinaryPlaneGramGraph
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess

/-! Controlled physical substitution for the four-vertex Gram graph over two
explicitly supplied lift labels. This reduction does not assert access to a
conjugate table; eliminating its second label is a separate interpolation step. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramAccess
open Holant Holant.Algebraic Holant.Complexity Computability
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace Q
export ExactTwoChainQueries (arity TargetInput targetEncoding)
end Q
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace N
export EOBinaryPlaneGramGraph (output palette template valid template_denote counts)
end N
namespace B
export EOBinaryPlaneCore (lift)
end B
namespace Cap
export Holant.LocalDrafts.Hardness.ControlledCap (controlledSubstitution)
end Cap
set_option backward.isDefEq.respectTransparency false

abbrev Input := ExactSignatureTables.Input 2 1 Q.arity
abbrev encoding := RawClosedNetwork.validatedEncoding 2 1 Q.arity

variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (f g : Signature K 2)

def value (r : Input) : K :=
  (r.val.realize r.property (N.palette f g) (fun _=>Signature.disequality)).denote Fin.elim0

def tables : ExactSignatureTables d 2 1 Q.arity where
  vertex i x := F.decode.symm (N.palette f g i x)
  edge _ x y := F.decode.symm (Signature.disequality x y)

theorem evaluate (r : Input) : (tables F f g).evaluate F r=value f g r := by
  simp only [ExactSignatureTables.evaluate_eq_decoded,tables,LinearEquiv.apply_symm_apply]
  rfl

def templates (_ : ℕ) : Template := N.template

theorem valid : ∀i<1,(templates i).WellFormed 2 1 Q.arity := fun _ _=>N.valid

def coordinates (i : Fin 1) (x : Fin (sourceArity templates i.val)→Bool) : Fin d→ℚ :=
  F.decode.symm (B.lift (N.output f g) x)

theorem template_value (i : Fin 1) :
    ((templates i.val).network (valid i.val i.isLt)
      (fun j x=>F.decode ((tables F f g).vertex j x))
      (fun j x y=>F.decode ((tables F f g).edge j x y))).denote=
      (if i.val=0 then (1 : K) else 1) • (fun x=>F.decode (coordinates F f g i x)) := by
  fin_cases i
  simp only [tables,coordinates,LinearEquiv.apply_symm_apply,ite_self,one_smul]
  exact N.template_denote f g

abbrev generatedValue := (sourceTables templates (tables F f g) (coordinates F f g)).evaluate F

theorem source_value (r : Q.TargetInput) :
    generatedValue F f g r=V.value (B.lift (N.output f g)) r := by
  simp only [generatedValue,ExactSignatureTables.evaluate_eq_decoded,sourceTables,
    coordinates,tables,LinearEquiv.apply_symm_apply]
  rfl

def query : Q.TargetInput→Input :=
  Compiler.value 1 1 Q.arity templates 2 Q.arity (compilerHypotheses templates valid)

def queryComputes : Computes Q.targetEncoding encoding query :=
  Compiler.computes 1 1 Q.arity templates 2 Q.arity (compilerHypotheses templates valid)

theorem query_counts (r : Q.TargetInput) :
    (query r).val.vertices.length=4*r.val.vertices.length ∧
      (query r).val.edges.length=r.val.edges.length+6*r.val.vertices.length := by
  have hv (row : RawVertex) : (templates row.1).vertices.length=4 := rfl
  have he (row : RawVertex) : (templates row.1).edges.length=6 := rfl
  change (replace templates r.val).vertices.length=_ ∧ (replace templates r.val).edges.length=_
  rw [replace_vertex_count,replace_edge_count]
  simp only [hv,he]
  simp [List.sum_replicate,Nat.mul_comm]

def substitution : LengthControlledOracleReduction Q.targetEncoding F.encoding
    encoding F.encoding (generatedValue F f g) ((tables F f g).evaluate F) :=
  Cap.controlledSubstitution F templates valid (tables F f g) (coordinates F f g)
    0 (1 : K) (by simp) (template_value F f g)

attribute [local irreducible] substitution

def source : LengthControlledOracleReduction Q.targetEncoding F.encoding
    encoding F.encoding (V.value (B.lift (N.output f g))) (value f g) := by
  have r := substitution F f g
  have hs : generatedValue F f g=V.value (B.lift (N.output f g)) := funext (source_value F f g)
  have ht : (tables F f g).evaluate F=value f g := funext (evaluate F f g)
  rw [hs,ht] at r
  exact r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramAccess
