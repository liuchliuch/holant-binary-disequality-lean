import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTable
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Semantics

/-! Marked temporary occurrences are exactly the first n original factor
records. All remaining compiled vertices carry original labels or Eq4. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLayout
open Holant Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
namespace R
export NoXGeneralOddRaw (arity factors markedFactors raw input)
end R
namespace T
export NoXGeneralOddTable (table old old_literal marked)
end T
namespace C
export Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Compilation
  (sourceNetwork labelling vertexIndex vertexArity original_arity original_ordered_port original_route)
end C
namespace D
export OrdinaryNegativeXUniversalResource (OddResource)
export OrdinaryNegativeMixedBlockData (guards)
end D
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (e p0 p1 : Fin s)
variable (he : (⟨a e.val,H e⟩ : AnySignature K)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩)
variable (h0 : a p0.val=1) (h1 : a p1.val=1)
variable (row : D.OddResource (s:=s) a n)

def source := R.input row p0 p1 h0 h1

include he in
theorem eqLiteral : (⟨R.arity (s:=s) (a:=a) (T.old e).val,T.table H (T.old e)⟩ : AnySignature K)=
    ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := (T.old_literal H e).trans he

def network := C.sourceNetwork (source p0 p1 h0 h1 row) (T.table H) (T.old e) (eqLiteral H e he)

def markerFactor (j : Fin n) : Fin (source p0 p1 h0 h1 row).val.factors.length :=
  ⟨j.val,by simp only [source,R.input,R.raw,List.length_append,R.markedFactors,List.length_ofFn];omega⟩

theorem marker_get (j : Fin n) :
    (source p0 p1 h0 h1 row).val.factors.get (markerFactor p0 p1 h0 h1 row j)=(s,[j.val+2]) := by
  simp only [source,R.input,R.raw,markerFactor,List.get_eq_getElem]
  rw [List.getElem_append_left (by simp [R.markedFactors];omega),
    List.getElem_append_left (by simp [R.markedFactors])]
  simp only [R.markedFactors,List.getElem_ofFn]

def mark (j : Fin n) : Fin (network H e p0 p1 he h0 h1 row).shape.vertices :=
  C.vertexIndex (source p0 p1 h0 h1 row) (.inl (markerFactor p0 p1 h0 h1 row j))

theorem mark_injective : Function.Injective (mark H e p0 p1 he h0 h1 row) := by
  intro i j eqn
  have h:=Sum.inl.inj ((C.vertexIndex (source p0 p1 h0 h1 row)).injective eqn)
  apply Fin.ext
  change (markerFactor p0 p1 h0 h1 row i).val=(markerFactor p0 p1 h0 h1 row j).val
  exact congrArg Fin.val h

def Remaining := {v : Fin (network H e p0 p1 he h0 h1 row).shape.vertices // ∀j,mark H e p0 p1 he h0 h1 row j≠v}

def vertices : (Remaining H e p0 p1 he h0 h1 row ⊕ Fin n) ≃ Fin (network H e p0 p1 he h0 h1 row).shape.vertices where
  toFun:=Sum.elim Subtype.val (mark H e p0 p1 he h0 h1 row)
  invFun v:=if h : ∃j,mark H e p0 p1 he h0 h1 row j=v then .inr (Classical.choose h)
    else .inl ⟨v,fun j eqn=>h ⟨j,eqn⟩⟩
  left_inv q:=by
    cases q with
    | inl v=>
        have hn : ¬∃j,mark H e p0 p1 he h0 h1 row j=v.val := by rintro ⟨j,hj⟩;exact v.property j hj
        simp only [Sum.elim_inl,dite_eq_right hn]
        exact congrArg Sum.inl (Subtype.ext rfl)
    | inr j=>
        have hy : ∃i,mark H e p0 p1 he h0 h1 row i=mark H e p0 p1 he h0 h1 row j := ⟨j,rfl⟩
        simp only [Sum.elim_inr,dite_eq_left hy]
        exact congrArg Sum.inr (mark_injective H e p0 p1 he h0 h1 row (Classical.choose_spec hy))
  right_inv v:=by
    dsimp only
    split_ifs with h
    · exact Classical.choose_spec h
    · rfl

theorem unary (j : Fin n) : (network H e p0 p1 he h0 h1 row).shape.arity
    (vertices H e p0 p1 he h0 h1 row (.inr j))=1 := by
  change C.vertexArity (source p0 p1 h0 h1 row)
    (C.vertexIndex (source p0 p1 h0 h1 row) (.inl (markerFactor p0 p1 h0 h1 row j)))=1
  rw [C.original_arity,marker_get]
  rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralOddLayout
end
