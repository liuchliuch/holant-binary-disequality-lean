import Holant.OpenNetworkComposition.PortSum

/-! Disjoint union of arbitrary full open gadgets. All free endpoints, original
ordered vertex ports, ordinary boundaries and internal edges are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.DisjointTensor
variable {VL VR FL FR EL ER : Type*} {m n : ℕ}
variable (L : FiniteShape VL FL EL m) (R : FiniteShape VR FR ER n)

def boundary : Fin (m+n) ↪ Ports (VL⊕VR) (FL⊕FR) (SumArity L.arity R.arity) :=
  finSumFinEquiv.symm.toEmbedding.trans
    ((L.boundary.sumMap R.boundary).trans (portSum L.arity R.arity).symm.toEmbedding)

def ends : ((EL⊕ER)×Bool) ↪ Ports (VL⊕VR) (FL⊕FR) (SumArity L.arity R.arity) :=
  (Equiv.sumProdDistrib EL ER Bool).toEmbedding.trans
    ((L.ends.sumMap R.ends).trans (portSum L.arity R.arity).symm.toEmbedding)

@[simp] theorem boundary_left (j : Fin m) :
    boundary L R (Fin.castAdd n j)=leftPort L.arity R.arity (L.boundary j) := by
  simp [boundary,Function.Embedding.sumMap]
  rfl
@[simp] theorem boundary_right (j : Fin n) :
    boundary L R (Fin.natAdd m j)=rightPort L.arity R.arity (R.boundary j) := by
  simp [boundary,Function.Embedding.sumMap]
  rfl
@[simp] theorem ends_left (e : EL) (b : Bool) :
    ends L R (.inl e,b)=leftPort L.arity R.arity (L.ends (e,b)) := rfl
@[simp] theorem ends_right (e : ER) (b : Bool) :
    ends L R (.inr e,b)=rightPort L.arity R.arity (R.ends (e,b)) := rfl

theorem boundary_range_left (p : Ports VL FL L.arity) :
    (∃j,boundary L R j=leftPort L.arity R.arity p) ↔ ∃j,L.boundary j=p := by
  constructor
  · rintro ⟨j,h⟩
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j => exact ⟨j,(leftPort L.arity R.arity).injective ((boundary_left L R j).symm.trans h)⟩
    | inr j => exact (right_left_ne L.arity R.arity _ _ ((boundary_right L R j).symm.trans h)).elim
  · rintro ⟨j,h⟩
    exact ⟨Fin.castAdd n j,by rw [boundary_left,h]⟩

theorem boundary_range_right (p : Ports VR FR R.arity) :
    (∃j,boundary L R j=rightPort L.arity R.arity p) ↔ ∃j,R.boundary j=p := by
  constructor
  · rintro ⟨j,h⟩
    obtain ⟨j,rfl⟩ := finSumFinEquiv.surjective j
    cases j with
    | inl j => exact (left_right_ne L.arity R.arity _ _ ((boundary_left L R j).symm.trans h)).elim
    | inr j => exact ⟨j,(rightPort L.arity R.arity).injective ((boundary_right L R j).symm.trans h)⟩
  · rintro ⟨j,h⟩
    exact ⟨Fin.natAdd m j,by rw [boundary_right,h]⟩

theorem ends_range_left (p : Ports VL FL L.arity) :
    (∃e,ends L R e=leftPort L.arity R.arity p) ↔ ∃e,L.ends e=p := by
  constructor
  · rintro ⟨⟨(e|e),b⟩,h⟩
    · exact ⟨(e,b),(leftPort L.arity R.arity).injective h⟩
    · exact (right_left_ne L.arity R.arity _ _ h).elim
  · rintro ⟨e,h⟩
    exact ⟨(.inl e.1,e.2),congrArg (leftPort L.arity R.arity) h⟩

theorem ends_range_right (p : Ports VR FR R.arity) :
    (∃e,ends L R e=rightPort L.arity R.arity p) ↔ ∃e,R.ends e=p := by
  constructor
  · rintro ⟨⟨(e|e),b⟩,h⟩
    · exact (left_right_ne L.arity R.arity _ _ h).elim
    · exact ⟨(e,b),(rightPort L.arity R.arity).injective h⟩
  · rintro ⟨e,h⟩
    exact ⟨(.inr e.1,e.2),congrArg (rightPort L.arity R.arity) h⟩

def shape : FiniteShape (VL⊕VR) (FL⊕FR) (EL⊕ER) (m+n) where
  arity := SumArity L.arity R.arity
  boundary := boundary L R
  ends := ends L R
  ordinary_boundary_iff_unpaired := by
    rintro ⟨(v|v),k⟩
    · change (∃j,boundary L R j=leftPort L.arity R.arity (.inl ⟨v,k⟩)) ↔
        ¬∃e,ends L R e=leftPort L.arity R.arity (.inl ⟨v,k⟩)
      rw [boundary_range_left,ends_range_left]
      exact L.ordinary_boundary_iff_unpaired ⟨v,k⟩
    · change (∃j,boundary L R j=rightPort L.arity R.arity (.inl ⟨v,k⟩)) ↔
        ¬∃e,ends L R e=rightPort L.arity R.arity (.inl ⟨v,k⟩)
      rw [boundary_range_right,ends_range_right]
      exact R.ordinary_boundary_iff_unpaired ⟨v,k⟩
  freeBoundary := Sum.elim (fun f => Fin.castAdd n (L.freeBoundary f)) (fun f => Fin.natAdd m (R.freeBoundary f))
  free_boundary := by
    rintro (f|f)
    · change boundary L R (Fin.castAdd n (L.freeBoundary f))=_
      rw [boundary_left,L.free_boundary]
      rfl
    · change boundary L R (Fin.natAdd m (R.freeBoundary f))=_
      rw [boundary_right,R.free_boundary]
      rfl
  freeEdge := Sum.elim (fun f => (.inl (L.freeEdge f).1,(L.freeEdge f).2))
    (fun f => (.inr (R.freeEdge f).1,(R.freeEdge f).2))
  free_paired := by
    rintro (f|f)
    · change ends L R (.inl (L.freeEdge f).1,(L.freeEdge f).2)=_
      rw [ends_left,L.free_paired]
      rfl
    · change ends L R (.inr (R.freeEdge f).1,(R.freeEdge f).2)=_
      rw [ends_right,R.free_paired]
      rfl

end Holant.OpenNetworkComposition.DisjointTensor
