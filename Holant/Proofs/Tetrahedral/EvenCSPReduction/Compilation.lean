import Holant.Proofs.Tetrahedral.EvenCSPReduction.Cells
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Grouping


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
open Holant Holant.Complexity
open scoped BigOperators
variable {s : ℕ} {a : ℕ → ℕ} (r : Raw.Input s a)

def cell (i : Fin r.val.variables) : Cells.Cell (r.val.degree i.val) :=
  Cells.make _ (r.property.2.2 i.val i.isLt)
abbrev Extra := Σi : Fin r.val.variables,Fin (cell r i).vertices
abbrev Vertices := Fin r.val.factors.length ⊕ Extra r
abbrev EdgeIndices := Σi : Fin r.val.variables,Fin (cell r i).edges
def vertexCount := r.val.factors.length+∑i,(cell r i).vertices
def edgeCount := ∑i,(cell r i).edges

/-- Standard ordinal arithmetic: variables are in original address order,
and each cell's local edge follows all preceding cells' edges. -/
def vertexIndex : Vertices r ≃ Fin (vertexCount r) :=
  (Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv
def edgeIndex : EdgeIndices r ≃ Fin (edgeCount r) := finSigmaFinEquiv

theorem edge_index_value (i : Fin r.val.variables) (e : Fin (cell r i).edges) :
    (edgeIndex r ⟨i,e⟩).val=
      (∑j : Fin i.val,(cell r (Fin.castLE i.isLt.le j)).edges)+e.val :=
  finSigmaFinEquiv_apply (n:=fun i => (cell r i).edges) ⟨i,e⟩

def indexArity : Vertices r → ℕ :=
  Sum.elim (fun v => (r.val.factors.get v).2.length) (fun _ => 4)
def vertexArity (v : Fin (vertexCount r)) := indexArity r ((vertexIndex r).symm v)

def extraPorts : (Σq : Extra r,Fin 4) ≃
    Σi : Fin r.val.variables,(Fin (cell r i).vertices × Fin 4) where
  toFun p := ⟨p.1.1,(p.1.2,p.2)⟩
  invFun p := ⟨⟨p.1,p.2.1⟩,p.2.2⟩
  left_inv p := rfl
  right_inv p := rfl

def portEnumeration : (Σv : Fin (vertexCount r),Fin (vertexArity r v)) ≃
    (r.val.Ports ⊕ Σi : Fin r.val.variables,(Fin (cell r i).vertices × Fin 4)) :=
  (vertexIndex r).symm.sigmaCongrLeft |>.trans
    (Equiv.sumSigmaDistrib (fun v => Fin (indexArity r v))) |>.trans
    (Equiv.sumCongr (Equiv.refl _) (extraPorts r))

/-- The only grouping is the actual stable occurrence getter/idxOf
equivalence. It is derived from the input, not supplied as a layout. -/
def localPorts :
    (r.val.Ports ⊕ Σi : Fin r.val.variables,(Fin (cell r i).vertices × Fin 4)) ≃
    Σi : Fin r.val.variables,
      (Fin (r.val.degree i.val) ⊕ (Fin (cell r i).vertices × Fin 4)) :=
  (Equiv.sumCongr (Raw.grouping r) (Equiv.refl _)).trans
    (Equiv.sigmaSumDistrib _ _).symm

def portEquiv : (Σv : Fin (vertexCount r),Fin (vertexArity r v)) ≃
    (Fin (edgeCount r) × Bool) :=
  (portEnumeration r).trans (localPorts r) |>.trans
    (Equiv.sigmaCongrRight (fun i => (cell r i).ports)) |>.trans
    (Equiv.sigmaProdDistrib (fun i => Fin (cell r i).edges) Bool).symm |>.trans
    (Equiv.prodCongr (edgeIndex r) (Equiv.refl Bool))

def shape : NetworkShape 0 where
  vertices := vertexCount r
  arity := vertexArity r
  edges := edgeCount r
  ports := (portEquiv r).trans (RawClosedNetwork.closedEndsEquiv _)

theorem original_route (p : r.val.Ports) :
    ClosedLabelling.closedPortEquiv (shape r)
      ((portEnumeration r).symm (.inl p))=
      (edgeIndex r ⟨((Raw.grouping r) p).1,
        ((cell r ((Raw.grouping r) p).1).ports (.inl ((Raw.grouping r) p).2)).1⟩,
        ((cell r ((Raw.grouping r) p).1).ports (.inl ((Raw.grouping r) p).2)).2) := by
  change portEquiv r ((portEnumeration r).symm (.inl p))=_
  simp only [portEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,localPorts,
    Equiv.sumCongr_apply,Equiv.refl_apply,Equiv.sigmaSumDistrib,
    Equiv.sigmaCongrRight_apply,Equiv.sigmaProdDistrib,Equiv.prodCongr_apply]
  rfl

theorem extra_route (i : Fin r.val.variables) (v : Fin (cell r i).vertices) (j : Fin 4) :
    ClosedLabelling.closedPortEquiv (shape r)
      ((portEnumeration r).symm (.inr ⟨i,(v,j)⟩))=
      (edgeIndex r ⟨i,((cell r i).ports (.inr (v,j))).1⟩,
        ((cell r i).ports (.inr (v,j))).2) := by
  change portEquiv r ((portEnumeration r).symm (.inr ⟨i,(v,j)⟩))=_
  simp only [portEquiv,Equiv.trans_apply,Equiv.apply_symm_apply,localPorts,
    Equiv.sumCongr_apply,Equiv.refl_apply,Equiv.sigmaSumDistrib,
    Equiv.sigmaCongrRight_apply,Equiv.sigmaProdDistrib,Equiv.prodCongr_apply]
  rfl

section Labelled
variable {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val)) (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

def labelling : ClosedLabelling (shape r) s 1 a where
  vertex v := Sum.elim (Raw.label r) (fun _ => j4) ((vertexIndex r).symm v)
  vertex_arity v := by
    cases hv : (vertexIndex r).symm v with
    | inl q => simpa only [shape,vertexArity,indexArity,hv,Sum.elim_inl,Raw.label] using
        (r.property.1 q).2.symm
    | inr q => simpa only [shape,vertexArity,indexArity,hv,Sum.elim_inr] using
        congrArg Sigma.fst h4
  edge _ := 0

/-- Concrete raw records plus their actual port-multiplicity validator.
All original nullary rows, loops and parallel occurrences survive. -/
def raw : RawClosedNetwork := (labelling r G j4 h4).serialize
def query : ExactSignatureTables.Input s 1 a := (labelling r G j4 h4).validated

theorem query_valid : (raw r G j4 h4).WellFormed s 1 a :=
  (labelling r G j4 h4).serialize_wellFormed

theorem query_roundtrip :
    (RawClosedNetwork.validatedEncoding s 1 a).decode
      ((RawClosedNetwork.validatedEncoding s 1 a).encode (query r G j4 h4))=
      some (query r G j4 h4) := (labelling r G j4 h4).serialization_roundtrip

theorem raw_vertices : (raw r G j4 h4).vertices.length=vertexCount r :=
  (labelling r G j4 h4).serialize_vertices_length
theorem raw_edges : (raw r G j4 h4).edges.length=edgeCount r :=
  (labelling r G j4 h4).serialize_edges_length

end Labelled

/-- Complete physical edge words grouped by their actual variable block. -/
abbrev Words := (i : Fin r.val.variables) → Fin (cell r i).edges → Bool
def flatWords : Words r ≃ (Fin (edgeCount r) → Bool) where
  toFun w e := let q := (edgeIndex r).symm e; w q.1 q.2
  invFun w i e := w (edgeIndex r ⟨i,e⟩)
  left_inv w := by
    funext i e
    exact congrArg (fun q : EdgeIndices r => w q.1 q.2) ((edgeIndex r).symm_apply_apply ⟨i,e⟩)
  right_inv w := by
    funext e
    exact congrArg w ((edgeIndex r).apply_symm_apply e)

def bits (w : Words r) (p : r.val.Ports) : Bool :=
  (cell r ((Raw.grouping r) p).1).boundary (w ((Raw.grouping r) p).1) ((Raw.grouping r) p).2
def Supported (w : Words r) : Prop :=
  ∀i : Fin r.val.variables,∀e : Fin (cell r i).edges,w i e=w i (cell r i).root

instance supportedDecidable (w : Words r) : Decidable (Supported r w) := by
  unfold Supported
  infer_instance

/-- Both directions retain even the two choices of an unused variable.
No quotient identifying empty fibers is taken. -/
def supportedVariables : {w : Words r // Supported r w} ≃ (Fin r.val.variables → Bool) where
  toFun w i := w.val i (cell r i).root
  invFun x := ⟨(fun i _ => x i),fun _ _ => rfl⟩
  left_inv w := Subtype.ext (by funext i e; exact (w.property i e).symm)
  right_inv x := rfl

theorem supported_bits (w : Words r) (h : Supported r w) (p : r.val.Ports) :
    bits r w p=w ((Raw.route r) p) (cell r ((Raw.route r) p)).root := by
  change w ((Raw.grouping r) p).1 _=_
  rw [h ((Raw.grouping r) p).1]
  rfl

section Partition
variable {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val))

def rowProduct (w : Words r) : K :=
  ∏i : Fin r.val.variables,∏v : Fin (cell r i).vertices,
    Holant.EightVertex.ProductAnchor.equalityFour ((cell r i).row (w i) v)

theorem rowProduct_guard (w : Words r) :
    rowProduct (K:=K) r w=if Supported r w then 1 else 0 := by
  by_cases h : Supported r w
  · have row_one (i : Fin r.val.variables) (v : Fin (cell r i).vertices) :
        Holant.EightVertex.ProductAnchor.equalityFour ((cell r i).row (w i) v)=(1 : K) := by
      apply if_pos
      exact ((cell r i).support_iff (w i)).mpr (h i) v
    simp only [rowProduct]
    simp_rw [row_one]
    simp [h]
  · have bad : ¬(∀i : Fin r.val.variables,∀v : Fin (cell r i).vertices,
        ∀j : Fin 4,(cell r i).row (w i) v j=(cell r i).row (w i) v 0) := by
      intro rows
      exact h (fun i => ((cell r i).support_iff (w i)).mp (rows i))
    push_neg at bad
    obtain ⟨i,v,j,bad⟩ := bad
    have row_zero : Holant.EightVertex.ProductAnchor.equalityFour ((cell r i).row (w i) v)=(0 : K) := by
      apply if_neg
      intro good
      exact bad (good j)
    have cell_zero : (∏v,Holant.EightVertex.ProductAnchor.equalityFour ((cell r i).row (w i) v))=(0 : K) :=
      Finset.prod_eq_zero (Finset.mem_univ v) row_zero
    have all_zero : rowProduct (K:=K) r w=0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) cell_zero
    rw [all_zero,if_neg h]

def partition : K := ∑w : Words r,Raw.factorWeight G r (bits r w)*rowProduct r w

/-- Whole partition equality of the physically supported assignment set.
Unsupported words vanish; supported words are exactly original variable
assignments via supportedVariables. No desired linear equation is input. -/
theorem partition_value : partition r G=Raw.value G r := by
  unfold partition
  simp_rw [rowProduct_guard]
  rw [Finset.sum_congr_set {w : Words r | Supported r w}
    (fun w => Raw.factorWeight G r (bits r w)*(if Supported r w then 1 else 0))
    (fun w => Raw.factorWeight G r (bits r w.val))
    (by intro w hw; change Supported r w at hw; simp only [if_pos hw,mul_one])
    (by intro w hw; change ¬Supported r w at hw; simp only [if_neg hw,mul_zero])]
  calc
    _ = ∑x : Fin r.val.variables → Bool,
        Raw.factorWeight G r (bits r ((supportedVariables r).symm x).val) :=
      ((supportedVariables r).symm.sum_comp
        (fun w => Raw.factorWeight G r (bits r w.val))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1

end Partition

theorem graph_size : vertexCount r≤r.val.factors.length+Fintype.card r.val.Ports+r.val.variables ∧
    edgeCount r≤2*Fintype.card r.val.Ports+2*r.val.variables := by
  have hv : (∑i : Fin r.val.variables,(cell r i).vertices)≤
      ∑i : Fin r.val.variables,(r.val.degree i.val+1) :=
    Finset.sum_le_sum (fun i _ => (Cells.make_size _ (r.property.2.2 i.val i.isLt)).1)
  have he : (∑i : Fin r.val.variables,(cell r i).edges)≤
      ∑i : Fin r.val.variables,(2*r.val.degree i.val+2) :=
    Finset.sum_le_sum (fun i _ => (Cells.make_size _ (r.property.2.2 i.val i.isLt)).2)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one] at hv he
  rw [(Raw.degree_sum r)] at hv he
  norm_num only [Nat.cast_id] at hv he
  unfold vertexCount edgeCount
  omega

/-- Costs of the actual generated graph, charged against the original
CSP bit input, including explicitly declared unused variables. This is
a size theorem; a machine time bound cannot be inferred from it alone. -/
theorem graph_size_in_input_bits :
    vertexCount r≤3*((Raw.validatedEncoding s a).encode r).length ∧
    edgeCount r≤4*((Raw.validatedEncoding s a).encode r).length := by
  have h := graph_size r
  have hv := r.val.variable_count_le_length
  have hp := r.val.port_count_le_length
  have hf := r.val.factor_count_le_length
  change vertexCount r≤3*(Raw.encoding.encode r.val).length ∧
    edgeCount r≤4*(Raw.encoding.encode r.val).length
  omega

end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
end
