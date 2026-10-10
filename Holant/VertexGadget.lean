import Holant.OpenNetwork

/-! A single labelled vertex as an open gadget, including nullary scalar vertices. -/

namespace Holant.OpenNetworkShape

def vertex (n : ℕ) : OpenNetworkShape n where
  vertices := 1
  arity := fun _ => n
  free := 0
  edges := 0
  boundary := {
    toFun := fun i => .inl ⟨0, i⟩
    inj' := by
      intro i j h
      have h' := Sum.inl.inj h
      exact Sigma.mk.inj_iff.mp h' |>.2 |> eq_of_heq }
  ends := ⟨fun q => Fin.elim0 q.1, fun q _ _ => Fin.elim0 q.1⟩
  ordinary_boundary_iff_unpaired := by
    intro p
    constructor
    · intro _ h
      obtain ⟨q, _⟩ := h
      exact Fin.elim0 q.1
    · intro _
      obtain ⟨v, i⟩ := p
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      exact ⟨i, rfl⟩
  freeBoundary := fun f => Fin.elim0 f
  free_boundary := fun f => Fin.elim0 f
  freeEdge := fun f => Fin.elim0 f
  free_paired := fun f => Fin.elim0 f

end Holant.OpenNetworkShape

namespace Holant.OpenNetwork

variable {K : Type*} [CommSemiring K] {n : ℕ}

def singleVertex (f : Signature K n) : OpenNetwork K n where
  shape := OpenNetworkShape.vertex n
  vertex := fun _ => f
  edge := fun e => Fin.elim0 e

private def vertexAssignment (x : Fin n → Bool) :
    OpenPorts 1 (fun _ => n) 0 → Bool :=
  Sum.elim (fun p => x p.2) Fin.elim0

private theorem vertex_assignment_unique (x : Fin n → Bool)
    (z : OpenPorts 1 (fun _ => n) 0 → Bool) :
    (∀ j, z (.inl ⟨0, j⟩) = x j) ↔ z = vertexAssignment x := by
  constructor
  · intro h
    funext p
    cases p with
    | inl q =>
      obtain ⟨v, i⟩ := q
      have hv : v = 0 := Subsingleton.elim _ _
      subst v
      exact h i
    | inr i => exact Fin.elim0 i
  · rintro rfl
    intro j
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem raw_vertex (f : Signature K n) (x : Fin n → Bool) : (singleVertex f).raw x = f x := by
  unfold raw
  dsimp [singleVertex, OpenNetworkShape.vertex]
  simp only [vertex_assignment_unique]
  simp [weight, vertexAssignment]

theorem tensor_vertex (f : Signature K n) : (singleVertex f).tensor = f := by
  rw [tensor_eq_raw_of_ordinary (singleVertex f) (fun j => ⟨⟨(0 : Fin 1), j⟩, rfl⟩)]
  funext x
  exact raw_vertex f x

end Holant.OpenNetwork
