import Holant.OpenNetworkComposition.PortSum

/-! Disjoint ordinary/ordinary one-port gluing incidence. Original vertex-port
injections are explicit, old edges remain distinct, and one native edge connects
only the two selected formerly unpaired boundary occurrences. -/
noncomputable section
namespace Holant.OpenNetworkComposition.Ordinary
variable {VL VR FL FR EL ER : Type*} {n : ℕ}
variable (L : FiniteShape VL FL EL n) (R : FiniteShape VR FR ER 2) (i : Fin n)

abbrev Vertex := VL ⊕ VR
abbrev Free := FL ⊕ FR
abbrev Edge := (EL ⊕ ER) ⊕ Unit
abbrev Port := Ports (Vertex (VL := VL) (VR := VR)) (Free (FL := FL) (FR := FR)) (SumArity L.arity R.arity)

def boundary : Fin n ↪ Port L R where
  toFun j := if j=i then rightPort L.arity R.arity (R.boundary 0) else leftPort L.arity R.arity (L.boundary j)
  inj' := by
    intro j k h
    by_cases hj : j=i <;> by_cases hk : k=i
    · exact hj.trans hk.symm
    · simp only [hj,ite_true,hk,ite_false] at h
      exact (right_left_ne _ _ _ _ h).elim
    · simp only [hj,ite_false,hk,ite_true] at h
      exact (left_right_ne _ _ _ _ h).elim
    · simp only [hj,ite_false,hk,ite_false] at h
      exact L.boundary.injective ((leftPort L.arity R.arity).injective h)

def endpoint : (Edge (EL := EL) (ER := ER)) × Bool → Port L R
  | (.inl (.inl e),b) => leftPort L.arity R.arity (L.ends (e,b))
  | (.inl (.inr e),b) => rightPort L.arity R.arity (R.ends (e,b))
  | (.inr _,false) => leftPort L.arity R.arity (L.boundary i)
  | (.inr _,true) => rightPort L.arity R.arity (R.boundary 1)

theorem selected_not_end_left (p : Σ v : VL,Fin (L.arity v))
    (hp : L.boundary i=Sum.inl p) (e : EL × Bool) : L.boundary i≠L.ends e := by
  intro h
  exact (L.ordinary_boundary_iff_unpaired p).mp ⟨i,hp⟩ ⟨e,h.symm.trans hp⟩

theorem selected_not_end_right (p : Σ v : VR,Fin (R.arity v))
    (hp : R.boundary 1=Sum.inl p) (e : ER × Bool) : R.boundary 1≠R.ends e := by
  intro h
  exact (R.ordinary_boundary_iff_unpaired p).mp ⟨1,hp⟩ ⟨e,h.symm.trans hp⟩

theorem endpoint_injective (pL : Σ v : VL,Fin (L.arity v)) (pR : Σ v : VR,Fin (R.arity v))
    (hL : L.boundary i=Sum.inl pL) (hR : R.boundary 1=Sum.inl pR) :
    Function.Injective (endpoint L R i) := by
  rintro ⟨((e | e) | u),b⟩ ⟨((f | f) | v),c⟩ h
  · have he := L.ends.injective ((leftPort L.arity R.arity).injective h)
    cases he; rfl
  · exact (left_right_ne L.arity R.arity _ _ h).elim
  · cases c
    · exact (selected_not_end_left L i pL hL (e,b) ((leftPort L.arity R.arity).injective h).symm).elim
    · exact (left_right_ne L.arity R.arity _ _ h).elim
  · exact (right_left_ne L.arity R.arity _ _ h).elim
  · have he := R.ends.injective ((rightPort L.arity R.arity).injective h)
    cases he; rfl
  · cases c
    · exact (right_left_ne L.arity R.arity _ _ h).elim
    · exact (selected_not_end_right R pR hR (e,b) ((rightPort L.arity R.arity).injective h).symm).elim
  · cases b
    · exact (selected_not_end_left L i pL hL (f,c) ((leftPort L.arity R.arity).injective h)).elim
    · exact (right_left_ne L.arity R.arity _ _ h).elim
  · cases b
    · exact (left_right_ne L.arity R.arity _ _ h).elim
    · exact (selected_not_end_right R pR hR (f,c) ((rightPort L.arity R.arity).injective h)).elim
  · cases u; cases v; cases b <;> cases c
    · rfl
    · exact (left_right_ne L.arity R.arity _ _ h).elim
    · exact (right_left_ne L.arity R.arity _ _ h).elim
    · rfl

def ends (pL : Σ v : VL,Fin (L.arity v)) (pR : Σ v : VR,Fin (R.arity v))
    (hL : L.boundary i=Sum.inl pL) (hR : R.boundary 1=Sum.inl pR) :
    Edge (EL := EL) (ER := ER) × Bool ↪ Port L R :=
  ⟨endpoint L R i,endpoint_injective L R i pL pR hL hR⟩

end Holant.OpenNetworkComposition.Ordinary
