import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4OrdinaryWire
import Holant.Proofs.Tetrahedral.OrdinaryReplication.Raw

/-! Replace every edge by an actual retained ordinary binary. One literal
subdivision and label recoding implement the changed-edge source; coefficients,
port order, loops, parallel edges and the full old table are preserved. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZEdgeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.CanonicalFamily
namespace E
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication.EqChoice
  (rowValue weight evaluate bit extend denote_eq_evaluate)
end E
namespace Choice
export UniversalPairReduction.Surgery.Choice (table)
end Choice
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] {degree r : ℕ} {arity : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin r)→Signature K (arity i.val)) (J : Kernel K)
variable (j : Fin r) (literal : (⟨arity j.val,H j⟩ : AnySignature K)=⟨2,fun x=>J (x 0) (x 1)⟩)

def tables : ExactSignatureTables degree r 1 arity where
  vertex i x:=F.decode.symm (H i x)
  edge _ p q:=F.decode.symm (J p q)
abbrev extended := EdgeSubdivision.extendedSignatures H (fun _ : Fin 1=>J)
abbrev extendedTables := QuaternaryOrdinaryCompanion.tables F (extended H J)
abbrev ordinaryTables := QuaternaryOrdinaryCompanion.tables F H

def label (i : Fin (r+1)) : Fin r := if h : i.val<r then ⟨i.val,h⟩ else j

include literal in
theorem label_literal (i : Fin (r+1)) :
    (⟨arity (label j i).val,H (label j i)⟩ : AnySignature K)=
      ⟨EdgeSubdivision.targetArity r arity i.val,extended H J i⟩ := by
  by_cases hi : i.val<r
  · have h:=EdgeSubdivision.extendedSignatures_old_heq H (fun _ : Fin 1=>J) ⟨i.val,hi⟩
    rw [show label j i=⟨i.val,hi⟩ by simp [label,hi]]
    exact (Sigma.ext (by simp [EdgeSubdivision.targetArity,hi]) h).symm
  · have he : i.val=r := by have := i.isLt; omega
    have hh : i=Fin.natAdd r (0 : Fin 1):=Fin.ext he
    rw [show label j i=j by simp [label,hi],literal,hh]
    exact (Sigma.ext (by simp [EdgeSubdivision.targetArity])
      (EdgeSubdivision.extendedSignatures_new_heq H (fun _ : Fin 1=>J) (0 : Fin 1))).symm

include H J literal in
theorem label_arity (i : Fin (r+1)) : arity (label j i).val=EdgeSubdivision.targetArity r arity i.val :=
  congrArg Sigma.fst (label_literal H J j literal i)
def query:=Relabel.input (label j) (label_arity H J j literal)

private def read (f : AnySignature K) (bits : List Bool):=f.2 (fun i=>bits.getD i.val false)
include literal in
theorem label_table (i : Fin (r+1)) (bits : List Bool) :
    Choice.table (extended H J) i.val bits=Choice.table H (label j i).val bits := by
  have h:=congrArg (fun f=>read f bits) (label_literal H J j literal i)
  simpa only [read,Choice.table,dif_pos i.isLt,dif_pos (label j i).isLt] using h.symm

theorem query_value (q : ExactSignatureTables.Input (r+1) 1 (EdgeSubdivision.targetArity r arity)) :
    (ordinaryTables F H).evaluate F (query H J j literal q)=(extendedTables F H J).evaluate F q := by
  rw [ExactSignatureTables.evaluate_eq_decoded,ExactSignatureTables.evaluate_eq_decoded]
  simp only [ordinaryTables,extendedTables,QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply]
  rw [E.denote_eq_evaluate,E.denote_eq_evaluate]
  unfold E.evaluate
  apply Finset.sum_congr rfl
  intro bits _
  change E.weight (Choice.table H) (E.extend bits) (q.val.vertices.map (Relabel.row (label j)))=
    E.weight (Choice.table (extended H J)) (E.extend bits) q.val.vertices
  unfold E.weight
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro row member
  have bound : row.1<r+1 := by
    obtain ⟨i,rfl⟩:=List.mem_iff_get.mp member
    exact (q.property.1 i).1
  have h:=label_table H J j literal ⟨row.1,bound⟩ (row.2.map (E.bit (E.extend bits)))
  simpa only [Function.comp_apply,E.rowValue,Relabel.row,Relabel.label,dif_pos bound] using h.symm

def relabelControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (EdgeSubdivision.targetArity r arity)) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    ((extendedTables F H J).evaluate F) ((ordinaryTables F H).evaluate F) :=
  controlledOneQueryOfEq (Relabel.computes (label j) (label_arity H J j literal))
    (identityComputes F.encoding) ((ordinaryTables F H).outputBound F)
    ((extendedTables F H J).evaluate F) (fun q=>(query_value F H J j literal q).symm)

theorem subdivision_tables : EdgeSubdivision.targetTables (tables F H J)
    (fun (_ : Fin 1) p q=>F.decode.symm (J p q))
    (fun p q=>F.decode.symm (Signature.equality p q))=extendedTables F H J := by
  unfold EdgeSubdivision.targetTables tables extendedTables QuaternaryOrdinaryCompanion.tables
  congr 1
  funext i x
  unfold extended EdgeSubdivision.extendedSignatures
  split <;> rfl

theorem fuse (i : Fin 1) (p q : Bool) :
    (∑uv : Bool×Bool,F.decode (F.decode.symm (Signature.equality p uv.1))*
      F.decode (F.decode.symm (J uv.1 uv.2))*F.decode (F.decode.symm (Signature.equality uv.2 q)))=
        F.decode ((tables F H J).edge i p q) := by
  cases p <;> cases q <;> simp [tables,Fintype.sum_prod_type,Signature.equality]

def subdivisionControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding (r+1) 1 (EdgeSubdivision.targetArity r arity)) F.encoding
    ((tables F H J).evaluate F) ((extendedTables F H J).evaluate F) := by
  apply controlledOneQueryOfEq (EdgeSubdivision.Compiler.computes r 1 arity)
    (identityComputes F.encoding) ((extendedTables F H J).outputBound F)
  intro q
  have h:=EdgeSubdivision.evaluate_subdivision F (tables F H J)
    (fun (_ : Fin 1) p q=>F.decode.symm (J p q))
    (fun p q=>F.decode.symm (Signature.equality p q)) (fuse F H J) q
  rw [subdivision_tables] at h
  exact h.symm

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 arity) F.encoding
    ((tables F H J).evaluate F) ((ordinaryTables F H).evaluate F) :=
  Programme.compose (subdivisionControlled F H J) (relabelControlled F H J j literal)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZEdgeSource
end
