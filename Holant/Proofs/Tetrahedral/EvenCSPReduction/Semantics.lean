import Holant.Proofs.Tetrahedral.EvenCSPReduction.Compilation


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
open Holant Holant.Complexity
open scoped BigOperators
variable {s : ℕ} {a : ℕ → ℕ} (r : Raw.Input s a)

theorem original_arity (v : Fin r.val.factors.length) :
    vertexArity r (vertexIndex r (.inl v))=(r.val.factors.get v).2.length := by
  simp only [vertexArity,Equiv.symm_apply_apply,indexArity,Sum.elim_inl]

theorem extra_arity (i : Fin r.val.variables) (v : Fin (cell r i).vertices) :
    vertexArity r (vertexIndex r (.inr ⟨i,v⟩))=4 := by
  simp only [vertexArity,Equiv.symm_apply_apply,indexArity,Sum.elim_inr]

private theorem transported_fin_val {α : Type*} (f : α → ℕ) {x y : α}
    (h : x=y) (j : Fin (f x)) : (h ▸ j : Fin (f y)).val=j.val := by
  cases h
  rfl

/-- The factor's stored jth port is still the jth port of the same row. -/
theorem original_ordered_port (v : Fin r.val.factors.length)
    (j : Fin (r.val.factors.get v).2.length) :
    (portEnumeration r).symm (.inl ⟨v,j⟩)=
      ⟨vertexIndex r (.inl v),Fin.cast (original_arity r v).symm j⟩ := by
  change ((vertexIndex r).symm.sigmaCongrLeft (β:=fun q : Vertices r => Fin (indexArity r q))).symm ⟨Sum.inl v,j⟩=_
  dsimp only [Equiv.sigmaCongrLeft,Equiv.coe_fn_symm_mk]
  refine Sigma.ext ?_ ?_
  · simp only [Equiv.symm_symm]
  · apply heq_of_eq
    apply Fin.ext
    simpa only [Fin.val_cast] using transported_fin_val (indexArity r)
      ((vertexIndex r).symm.apply_symm_apply (Sum.inl v)).symm j

/-- Eq4's original port order is unchanged by the outer serialization. -/
theorem extra_ordered_port (i : Fin r.val.variables) (v : Fin (cell r i).vertices) (j : Fin 4) :
    (portEnumeration r).symm (.inr ⟨i,(v,j)⟩)=
      ⟨vertexIndex r (.inr ⟨i,v⟩),Fin.cast (extra_arity r i v).symm j⟩ := by
  change ((vertexIndex r).symm.sigmaCongrLeft (β:=fun q : Vertices r => Fin (indexArity r q))).symm ⟨Sum.inr ⟨i,v⟩,j⟩=_
  dsimp only [Equiv.sigmaCongrLeft,Equiv.coe_fn_symm_mk]
  refine Sigma.ext ?_ ?_
  · simp only [Equiv.symm_symm]
  · apply heq_of_eq
    apply Fin.ext
    simpa only [Fin.val_cast] using transported_fin_val (indexArity r)
      ((vertexIndex r).symm.apply_symm_apply (Sum.inr ⟨i,v⟩)).symm j

private theorem flatWords_at (w : Words r) (i : Fin r.val.variables)
    (e : Fin (cell r i).edges) : flatWords r w (edgeIndex r ⟨i,e⟩)=w i e :=
  congrArg (fun q : EdgeIndices r => w q.1 q.2) ((edgeIndex r).symm_apply_apply ⟨i,e⟩)

private theorem signature_cast_apply {K : Type*} {m n : ℕ}
    (f : Signature K m) (g : Signature K n)
    (h : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (x : Fin n → Bool) :
    f (fun i => x (Fin.cast (congrArg Sigma.fst h) i))=g x := by
  cases h
  rfl

section Labelled
variable {K : Type*} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val)) (j4 : Fin s)
variable (h4 : (⟨a j4.val,G j4⟩ : AnySignature K)=
  ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)

abbrev sourceNetwork := (labelling r G j4 h4).sourceNetwork G
  (fun _ : Fin 1 => Signature.equality)

private theorem original_vertex (v : Fin r.val.factors.length) :
    (labelling r G j4 h4).vertex (vertexIndex r (.inl v))=(Raw.label r) v := by
  simp only [labelling,Equiv.symm_apply_apply,Sum.elim_inl]

private theorem extra_vertex (i : Fin r.val.variables) (v : Fin (cell r i).vertices) :
    (labelling r G j4 h4).vertex (vertexIndex r (.inr ⟨i,v⟩))=j4 := by
  simp only [labelling,Equiv.symm_apply_apply,Sum.elim_inr]

private theorem original_assignment (w : Words r) (v : Fin r.val.factors.length)
    (j : Fin (a ((Raw.label r) v).val)) :
    (shape r).assignment Fin.elim0 (fun p => flatWords r w p.1)
      (vertexIndex r (.inl v))
      (Fin.cast ((r.property.1 v).2.symm.trans (original_arity r v).symm) j)=
      bits r w ((Raw.portCast r) v j) := by
  rw [ClosedLabelling.closed_assignment]
  have hp :
      (⟨vertexIndex r (.inl v),
        Fin.cast ((r.property.1 v).2.symm.trans (original_arity r v).symm) j⟩ :
        Σv : Fin (vertexCount r),Fin (vertexArity r v))=
      (portEnumeration r).symm (.inl ((Raw.portCast r) v j)) := by
    rw [original_ordered_port]
    apply Sigma.ext rfl
    apply HEq.rfl
  rw [hp,original_route]
  rw [flatWords_at]
  rfl

private theorem extra_assignment (w : Words r) (i : Fin r.val.variables)
    (v : Fin (cell r i).vertices) (j : Fin 4) :
    (shape r).assignment Fin.elim0 (fun p => flatWords r w p.1)
      (vertexIndex r (.inr ⟨i,v⟩))
      (Fin.cast (extra_arity r i v).symm j)=(cell r i).row (w i) v j := by
  rw [ClosedLabelling.closed_assignment]
  rw [←extra_ordered_port,extra_route]
  exact flatWords_at r w i ((cell r i).ports (.inr (v,j))).1

private theorem original_row (w : Words r) (v : Fin r.val.factors.length) :
    (sourceNetwork r G j4 h4).vertex (vertexIndex r (.inl v))
      ((shape r).assignment Fin.elim0 (fun p => flatWords r w p.1)
        (vertexIndex r (.inl v)))=
      G ((Raw.label r) v) (fun j => bits r w ((Raw.portCast r) v j)) := by
  unfold sourceNetwork ClosedLabelling.sourceNetwork
  apply ClosedLabelling.table_apply_congr G (original_vertex r G j4 h4 v)
  intro j
  have hj : (Fin.cast ((labelling r G j4 h4).vertex_arity
      (vertexIndex r (.inl v))) j)=
      Fin.cast ((r.property.1 v).2.symm.trans (original_arity r v).symm)
        (Fin.cast (congrArg (fun l : Fin s => a l.val)
          (original_vertex r G j4 h4 v)) j) := Fin.ext rfl
  rw [hj]
  exact original_assignment r w v _

private theorem extra_row (w : Words r) (i : Fin r.val.variables)
    (v : Fin (cell r i).vertices) :
    (sourceNetwork r G j4 h4).vertex (vertexIndex r (.inr ⟨i,v⟩))
      ((shape r).assignment Fin.elim0 (fun p => flatWords r w p.1)
        (vertexIndex r (.inr ⟨i,v⟩)))=
      Holant.EightVertex.ProductAnchor.equalityFour ((cell r i).row (w i) v) := by
  have ha := congrArg Sigma.fst h4
  let x : Fin 4 → Bool := fun j => (shape r).assignment Fin.elim0
    (fun p => flatWords r w p.1) (vertexIndex r (.inr ⟨i,v⟩))
      (Fin.cast (extra_arity r i v).symm j)
  have hx : x=(cell r i).row (w i) v := funext (extra_assignment r w i v)
  have hrow :
      (sourceNetwork r G j4 h4).vertex (vertexIndex r (.inr ⟨i,v⟩))
        ((shape r).assignment Fin.elim0 (fun p => flatWords r w p.1)
          (vertexIndex r (.inr ⟨i,v⟩)))=
      G j4 (fun j => x (Fin.cast ha j)) := by
    unfold sourceNetwork ClosedLabelling.sourceNetwork
    apply ClosedLabelling.table_apply_congr G (extra_vertex r G j4 h4 i v)
    intro j
    congr 1
  rw [hrow]
  rw [signature_cast_apply (G j4) Holant.EightVertex.ProductAnchor.equalityFour h4 x,hx]

/-- Actual original factor rows times actual Eq4 rows, for every physical
edge word, before removing any zero support or counting variables. -/
theorem vertex_product (w : Words r) :
    (∏v : Fin (vertexCount r),(sourceNetwork r G j4 h4).vertex v
      ((shape r).assignment Fin.elim0 (fun p => flatWords r w p.1) v))=
      Raw.factorWeight G r (bits r w)*rowProduct r w := by
  rw [←(vertexIndex r).prod_comp]
  simp only [Fintype.prod_sum_type,Fintype.prod_sigma,original_row,extra_row]
  rfl

theorem source_denote :
    (sourceNetwork r G j4 h4).denote Fin.elim0=Raw.value G r := by
  rw [EqualityTree.ordinary_denote _ (fun _ => rfl)]
  calc
    _ = ∑w : Words r,∏v : Fin (vertexCount r),(sourceNetwork r G j4 h4).vertex v
        ((shape r).assignment Fin.elim0 (fun p => flatWords r w p.1) v) :=
      ((flatWords r).sum_comp (fun c => ∏v : Fin (vertexCount r),
        (sourceNetwork r G j4 h4).vertex v
          ((shape r).assignment Fin.elim0 (fun p => c p.1) v))).symm
    _ = _ := by
      simp_rw [vertex_product]
      exact partition_value r G

/-- Whole raw partition identity. All scalar corrections in a subsequent
anchor substitution are additional, explicitly recorded factors. -/
theorem query_denote :
    ((query r G j4 h4).val.realize (query r G j4 h4).property G
      (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0=Raw.value G r := by
  rw [ClosedLabelling.denote_serialize]
  exact source_denote r G j4 h4

end Labelled
end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
end
