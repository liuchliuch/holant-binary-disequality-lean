import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddLayout

/-! The marked temporary labels occur only at their specified factor sites.
Every retained original occurrence and every equality-cell vertex has an
exact old-family label after all marked sites are replaced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLabels
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
namespace L
export NoXGeneralOddLayout (source eqLiteral network markerFactor marker_get mark Remaining vertices unary)
end L
namespace R
export NoXGeneralOddRaw (factors markedFactors raw input)
end R
namespace T
export NoXGeneralOddTable (table old old_literal marked)
end T
namespace C
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation (labelling vertexIndex sourceNetwork)
end C
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
export OrdinaryNegativeMixedBlockData (guards)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : a p0.val=1) (h1 : a p1.val=1)
variable (row : D.OddResource (s:=s) a n)

include h0 h1 in
theorem old_factor (f : Factor) (hf : f∈R.factors row++D.guards p0 p1) : f.1<s := by
  rcases List.mem_append.mp hf with hf|hf
  · obtain ⟨node,_,rfl⟩ := List.mem_map.mp hf
    exact node.1.isLt
  · exact (OrdinaryNegativePhaseBundleValidity.guards_good p0 p1 h0 h1 (n+row.privateCount) f hf).1

theorem tail_factor (q : Fin (L.source p0 p1 h0 h1 row).val.factors.length) (hq : n≤q.val) :
    ((L.source p0 p1 h0 h1 row).val.factors.get q).1<s := by
  apply old_factor p0 p1 h0 h1 row
  have hi : q.val-n<(R.factors row++D.guards p0 p1).length := by
    have bound:=q.isLt
    simp only [L.source,R.input,R.raw,List.length_append,R.markedFactors,List.length_ofFn] at bound ⊢
    omega
  have eqn : (L.source p0 p1 h0 h1 row).val.factors.get q=(R.factors row++D.guards p0 p1)[q.val-n] := by
    calc
      _=(L.source p0 p1 h0 h1 row).val.factors.getD q.val (0,[]) := by
        simp only [List.get_eq_getElem,List.getD_eq_getElem _ _ q.isLt]
      _=(R.factors row++D.guards p0 p1).getD (q.val-n) (0,[]) := by
        change ((R.markedFactors row++R.factors row)++D.guards p0 p1).getD q.val (0,[])=_
        rw [List.append_assoc,List.getD_append_right _ _ _ _ (by simpa [R.markedFactors] using hq)]
        simp only [R.markedFactors,List.length_ofFn]
      _=_ := List.getD_eq_getElem _ _ hi
  rw [eqn]
  exact List.getElem_mem hi

def sourceLabel (v : L.Remaining H e p0 p1 he h0 h1 row) : Fin (s+1) :=
  (C.labelling (L.source p0 p1 h0 h1 row) (T.table H) (T.old e) (L.eqLiteral H e he)).vertex v.val

theorem label_lt (v : L.Remaining H e p0 p1 he h0 h1 row) : (sourceLabel H e p0 p1 he h0 h1 row v).val<s := by
  change (Sum.elim (Raw.label (L.source p0 p1 h0 h1 row)) (fun _=>T.old e)
    ((C.vertexIndex (L.source p0 p1 h0 h1 row)).symm v.val)).val<s
  cases hv : (C.vertexIndex (L.source p0 p1 h0 h1 row)).symm v.val with
  | inr q=>exact e.isLt
  | inl q=>
      apply tail_factor p0 p1 h0 h1 row q
      by_contra low
      have hq : q.val<n := by omega
      let j : Fin n:=⟨q.val,hq⟩
      apply v.property j
      have same : L.markerFactor p0 p1 h0 h1 row j=q := Fin.ext rfl
      change C.vertexIndex (L.source p0 p1 h0 h1 row) (.inl (L.markerFactor p0 p1 h0 h1 row j))=v.val
      rw [same,←hv,Equiv.apply_symm_apply]

def labels (v : L.Remaining H e p0 p1 he h0 h1 row) : Fin s :=
  ⟨(sourceLabel H e p0 p1 he h0 h1 row v).val,label_lt H e p0 p1 he h0 h1 row v⟩

omit [Field K] in
private theorem literal_cast {m t : ℕ} (f : Signature K m) (h : m=t) :
    (⟨m,f⟩ : AnySignature K)=⟨t,fun x=>f (fun i=>x (Fin.cast h i))⟩ := by cases h;rfl

theorem literal (v : L.Remaining H e p0 p1 he h0 h1 row) :
    (⟨a (labels H e p0 p1 he h0 h1 row v).val,H (labels H e p0 p1 he h0 h1 row v)⟩ : AnySignature K)=
      ⟨(L.network H e p0 p1 he h0 h1 row).shape.arity (L.vertices H e p0 p1 he h0 h1 row (.inl v)),
        (L.network H e p0 p1 he h0 h1 row).vertex (L.vertices H e p0 p1 he h0 h1 row (.inl v))⟩ := by
  have eqn : T.old (labels H e p0 p1 he h0 h1 row v)=sourceLabel H e p0 p1 he h0 h1 row v := Fin.ext rfl
  have old:=T.old_literal H (labels H e p0 p1 he h0 h1 row v)
  rw [eqn] at old
  exact old.symm.trans (literal_cast _
    ((C.labelling (L.source p0 p1 h0 h1 row) (T.table H) (T.old e) (L.eqLiteral H e he)).vertex_arity v.val))

theorem marker_label (j : Fin n) :
    ((C.labelling (L.source p0 p1 h0 h1 row) (T.table H) (T.old e) (L.eqLiteral H e he)).vertex
      (L.mark H e p0 p1 he h0 h1 row j)).val=s := by
  simp only [C.labelling,L.mark,Equiv.symm_apply_apply,Sum.elim_inl,Raw.label]
  rw [L.marker_get]

theorem ones (j : Fin n) (x : Fin ((L.network H e p0 p1 he h0 h1 row).shape.arity
    (L.vertices H e p0 p1 he h0 h1 row (.inr j)))→Bool) :
    (L.network H e p0 p1 he h0 h1 row).vertex (L.vertices H e p0 p1 he h0 h1 row (.inr j)) x=1 := by
  dsimp only [L.network,C.sourceNetwork,ClosedLabelling.sourceNetwork,L.vertices,Equiv.coe_fn_mk,Sum.elim_inr]
  simp only [T.table,dite_eq_right (show ¬((C.labelling (L.source p0 p1 h0 h1 row) (T.table H) (T.old e)
    (L.eqLiteral H e he)).vertex (L.mark H e p0 p1 he h0 h1 row j)).val<s from by
      rw [marker_label];omega)]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLabels
end
