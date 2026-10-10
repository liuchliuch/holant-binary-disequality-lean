import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant Holant.EightVertex.ProductAnchor
open Holant.Certificates.FourthRootOdd
open Holant.Complexity.FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommSemiring K]

def nativeChain (M : Signature K 4) : Network K 4 :=
  ((reorderNetwork (pairCorolla M)
    (wiringEquiv ![false,false,true,true]).symm).contract
      Signature.disequality).contract Signature.disequality

def oppositePrefix (u v : Bool) (t : Word) : Fin 8 → Bool :=
  Fin.cons u (Fin.cons (!u) (Fin.cons v (Fin.cons (!v) t)))

def originalCopyWord (k : Fin 2) (u v : Bool) (t : Word) : Word :=
  fun i => oppositePrefix u v t
    ((wiringEquiv ![false,false,true,true]).symm (copyPort k i))

theorem originalCopyWord_zero (u v : Bool) (t : Word) :
    originalCopyWord 0 u v t = ![t 0,t 1,u,v] := by
  funext i
  fin_cases i <;> rfl

theorem originalCopyWord_one (u v : Bool) (t : Word) :
    originalCopyWord 1 u v t = ![!u,!v,t 2,t 3] := by
  funext i
  fin_cases i <;> rfl

/-- The graph contraction theorem supplies the complete assignment sum.
There is no supplied gate equality or correctness premise. -/
theorem nativeChain_denote (M : Signature K 4) :
    (nativeChain M).denote = chainSum M := by
  funext t
  rw [nativeChain,Network.denote_contract,Network.denote_contract,
    reorderNetwork_denote,pairCorolla_denote]
  simp only [Signature.contract_disequality,Tensor.reindex_apply,Signature.tensor_apply]
  change
    (M (originalCopyWord 0 false false t) * M (originalCopyWord 1 false false t) +
      M (originalCopyWord 0 true false t) * M (originalCopyWord 1 true false t)) +
    (M (originalCopyWord 0 false true t) * M (originalCopyWord 1 false true t) +
      M (originalCopyWord 0 true true t) * M (originalCopyWord 1 true true t)) = _
  simp only [originalCopyWord_zero,originalCopyWord_one,chainSum,chainValue]

theorem nativeChain_entries (M : Signature K 4) (hM : EvenSupport M) :
    (nativeChain M).denote = table (chainEntries (entries M)) := by
  rw [nativeChain_denote,chainSum_entries M hM]

theorem nativeChain_sparse (M : Signature K 4) (hM : EvenSupport M)
    (h : SparseCase M) :
    (nativeChain M).denote = table (sparseEntries (entries M)) := by
  rw [nativeChain_entries M hM,chainEntries_sparse M h]

theorem nativeChain_vertices (M : Signature K 4) : (nativeChain M).shape.vertices = 2 := rfl
theorem nativeChain_edges (M : Signature K 4) : (nativeChain M).shape.edges = 2 := rfl
theorem nativeChain_arity (M : Signature K 4) (v : Fin (nativeChain M).shape.vertices) :
    (nativeChain M).shape.arity v = 4 := rfl
theorem nativeChain_vertex (M : Signature K 4) (v : Fin (nativeChain M).shape.vertices) :
    (nativeChain M).vertex v = M := rfl
theorem nativeChain_edge (M : Signature K 4) (e : Fin (nativeChain M).shape.edges) :
    (nativeChain M).edge e = Signature.disequality := by
  change Fin 2 at e
  fin_cases e <;> rfl

/-- The labelling records every original occurrence, with only label 0 (M)
and edge label 0 (native X). Its shape is independent of coefficient values. -/
def chainLabelling (M : Signature K 4) :
    Labelling (nativeChain M).shape 1 1 (fun _ => 4) where
  vertex := fun _ => 0
  vertex_arity := fun _ => rfl
  edge := fun _ => 0

def chainTemplate : Template := (chainLabelling (0 : Signature ℕ 4)).template

theorem chainTemplate_eq (M : Signature K 4) :
    chainTemplate = (chainLabelling M).template := rfl

theorem chainTemplate_wellFormed : chainTemplate.WellFormed 1 1 (fun _ => 4) :=
  (chainLabelling (0 : Signature ℕ 4)).wellFormed

theorem chainTemplate_boundary : chainTemplate.boundary = 4 := rfl
theorem chainTemplate_vertices : chainTemplate.vertices.length = 2 := by
  exact (chainLabelling (0 : Signature ℕ 4)).vertices_length
theorem chainTemplate_edges : chainTemplate.edges.length = 2 := by
  exact (chainLabelling (0 : Signature ℕ 4)).edges_length

/-- Literal executable records, in the original local-port order. Edge 0 is
the second contraction, edge 1 the first contraction. -/
theorem chainTemplate_records :
    chainTemplate.vertices =
      [(0,[.inl 0,.inl 1,.inr (1,false),.inr (0,false)]),
       (0,[.inr (1,true),.inr (0,true),.inl 2,.inl 3])] ∧
    chainTemplate.edges = [0,0] := by
  constructor <;> rfl

/-- The template consumes the original M at each vertex and X at each edge.
This closes the local denotation obligation of the existing physical compiler. -/
theorem chainTemplate_denote (M : Signature K 4) :
    (chainTemplate.network chainTemplate_wellFormed (fun _ => M)
      (fun _ => Signature.disequality)).denote = (nativeChain M).denote := by
  change ((chainLabelling M).template.network (chainLabelling M).wellFormed
    (fun _ => M) (fun _ => Signature.disequality)).denote = (nativeChain M).denote
  apply Labelling.denote_template_of_labels (chainLabelling M)
    (fun _ => M) (fun _ => Signature.disequality)
    (nativeChain M).vertex (nativeChain M).edge
  · intro v t
    rfl
  · intro e a b
    exact congrFun (congrFun (nativeChain_edge M e).symm a) b

end Holant.LocalDrafts.Hardness.EightVertexNonexception
