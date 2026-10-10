import Holant.Certificates.OctahedralSeparator.NativeDressed

/-! The sparse correction-and-closure graph: one original six-port vertex,
the initial pair binary, two actual leg binaries, and the final pair binary.
Undressed legs use the original ports, with no artificial identity vertices. -/
namespace Holant.Certificates.OctahedralSeparator.Native
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sparseArity : Fin 5 → ℕ := Fin.cases 6 (fun _ => 2)

def sparsePortMap : (Σ v : Fin 5, Fin (sparseArity v)) → (Fin 2 ⊕ (Fin 6 × Bool)) := fun p =>
  Fin.cases (fun i => ![.inr (0,false),.inr (1,false),.inr (2,false),
      .inr (3,false),.inl 0,.inr (4,false)] i)
    (fun v => fun i : Fin 2 =>
      ![![.inr (0,true),.inr (1,true)],
        ![.inr (5,false),.inr (3,true)],
        ![.inl 1,.inr (4,true)],
        ![.inr (2,true),.inr (5,true)]] v i) p.1 p.2

def sparsePortInv : (Fin 2 ⊕ (Fin 6 × Bool)) → (Σ v : Fin 5, Fin (sparseArity v))
  | .inl j => ![⟨0,(4 : Fin 6)⟩,⟨3,(0 : Fin 2)⟩] j
  | .inr (e,b) => if b then
      ![⟨1,(0 : Fin 2)⟩,⟨1,(1 : Fin 2)⟩,⟨4,(0 : Fin 2)⟩,⟨2,(1 : Fin 2)⟩,⟨3,(1 : Fin 2)⟩,⟨4,(1 : Fin 2)⟩] e
    else ![⟨0,(0 : Fin 6)⟩,⟨0,(1 : Fin 6)⟩,⟨0,(2 : Fin 6)⟩,⟨0,(3 : Fin 6)⟩,⟨0,(5 : Fin 6)⟩,⟨2,(0 : Fin 2)⟩] e

def sparseShape : NetworkShape 2 where
  vertices := 5
  arity := sparseArity
  edges := 6
  ports := {
    toFun := sparsePortMap
    invFun := sparsePortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [sparseArity] at i <;> fin_cases i <;> rfl
    right_inv q := by
      cases q with
      | inl j => fin_cases j <;> rfl
      | inr q => rcases q with ⟨e,b⟩; fin_cases e <;> cases b <;> rfl }

def sparseLabels (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (v : Fin 5) → Signature ℂ (sparseArity v) :=
  Fin.cases h (fun v =>
    ![binarySignature (pairVertex K),binarySignature (legVertex L1),
      binarySignature (legVertex L3),binarySignature (pairVertex M)] v)

def sparseNetwork (h : Signature ℂ 6) (K L1 L3 M : Binary) : Network ℂ 2 where
  shape := sparseShape
  vertex := sparseLabels h K L1 L3 M
  edge := fun _ => Signature.disequality

/-- Choices are ordered as the final closure pair, the two surviving internal
leg bits, and the original first pair. -/
def sparseChoices : (Fin 6 → Bool) ≃ (Bool × Bool × Bool × Bool × Bool × Bool) where
  toFun c := (!(c 2),!(c 5),!(c 3),!(c 4),!(c 0),!(c 1))
  invFun q := ![!q.2.2.2.2.1,!q.2.2.2.2.2,!q.1,!q.2.2.1,!q.2.2.2.1,!q.2.1]
  left_inv c := by funext i; fin_cases i <;> simp
  right_inv q := by
    rcases q with ⟨u,v,y,z,a,b⟩
    simp

theorem sparse_product (h : Signature ℂ 6) (K L1 L3 M : Binary)
    (x : Fin 2 → Bool) (u v y z a b : Bool) :
    (∏ w : Fin 5, sparseLabels h K L1 L3 M w
      (sparseShape.assignment x
        (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z,a,b))) w)) =
      M u v * (L1 v y * L3 (x 1) z * (K a b * h ![a,b,u,y,x 0,z])) := by
  have ha : sparseShape.assignment x
      (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z,a,b))) (0 : Fin 5) =
        ![a,b,u,y,x 0,z] := by
    funext i
    fin_cases i <;> simp [sparseShape,NetworkShape.assignment,sparsePortMap,
      Network.endpointChoiceAssignment,sparseChoices]
  simp only [sparseShape,Fin.prod_univ_succ]
  change h (sparseShape.assignment x
      (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z,a,b))) (0 : Fin 5)) * _ = _
  rw [ha]
  change h ![a,b,u,y,x 0,z] *
    (pairVertex K (!a) (!b) * (legVertex L1 (!(!v)) (!y) *
      (legVertex L3 (x 1) (!z) * (pairVertex M (!u) (!v) * 1)))) = _
  simp only [Bool.not_not,pairVertex_edge,legVertex_edge,mul_one]
  ring

/-- The equality slots constrain the literal first and third residual ports. -/
theorem sparse_coordinateAction (f : Signature ℂ 4) (L1 L3 : Binary) (x : Fin 4 → Bool) :
    Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3] f x =
      ∑ y : Bool, ∑ z : Bool, L1 (x 1) y * L3 (x 3) z * f ![x 0,y,x 2,z] := by
  rw [Signature.coordinateAction,TetrahedralOrientation.sum_four]
  simp [Fin.prod_univ_succ,Signature.equality]

/-- Exact finite sum with original output order5/6 and both native-X pair boxes. -/
theorem sparse_target_apply (h : Signature ℂ 6) (K L1 L3 M : Binary) (x : Fin 2 → Bool) :
    Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
        (Signature.contract K h)) x =
      ∑ u : Bool, ∑ v : Bool, ∑ y : Bool, ∑ z : Bool, ∑ a : Bool, ∑ b : Bool,
        M u v * (L1 v y * L3 (x 1) z * (K a b * h ![a,b,u,y,x 0,z])) := by
  rw [Signature.contract]
  simp_rw [sparse_coordinateAction,Signature.contract]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have he : Fin.cons a (Fin.cons b (![u,y,x 0,z] : Fin 4 → Bool)) =
      ![a,b,u,y,x 0,z] := by
    funext i
    fin_cases i <;> rfl
  change M u v * (L1 v y * L3 (x 1) z *
    (K a b * h (Fin.cons a (Fin.cons b ![u,y,x 0,z])))) = _
  rw [he]

theorem sparseNetwork_denote (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (sparseNetwork h K L1 L3 M).denote = Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
        (Signature.contract K h)) := by
  rw [sparseNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 6 → Bool, ∏ v : Fin 5, sparseLabels h K L1 L3 M v
    (sparseShape.assignment x (Network.endpointChoiceAssignment c) v)) = _
  rw [← sparseChoices.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [sparse_product]
  exact (sparse_target_apply h K L1 L3 M x).symm

/-- Four binaries total: first-pair box, two corrections, and final-pair box. -/
def sparseResources (h : Signature ℂ 6) (K L1 L3 M : Binary) : SignatureFamily ℂ :=
  {p | p = ⟨6,h⟩ ∨ p = ⟨2,binarySignature (pairVertex K)⟩ ∨
    p = ⟨2,binarySignature (legVertex L1)⟩ ∨
    p = ⟨2,binarySignature (legVertex L3)⟩ ∨
    p = ⟨2,binarySignature (pairVertex M)⟩}

theorem sparse_realizes (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    Gadget.Realizes (sparseResources h K L1 L3 M) .disequality
      (Signature.contract M
        (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
          (Signature.contract K h))) := by
  have hr := Gadget.realizes_network (sparseNetwork h K L1 L3 M)
    (sparseResources h K L1 L3 M) .disequality
    (by intro v; fin_cases v
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr rfl))))
    (by intro e; rfl)
  rwa [sparseNetwork_denote] at hr

@[simp] theorem sparseNetwork_vertices (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (sparseNetwork h K L1 L3 M).shape.vertices = 5 := rfl

@[simp] theorem sparseNetwork_edges (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (sparseNetwork h K L1 L3 M).shape.edges = 6 := rfl

/-- Resource membership alone gives the actual sparse graph in an ambient family. -/
theorem sparse_realizes_of_mem (F : SignatureFamily ℂ)
    (h : Signature ℂ 6) (K L1 L3 M : Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ F)
    (hK : (⟨2,binarySignature (pairVertex K)⟩ : AnySignature ℂ) ∈ F)
    (hL1 : (⟨2,binarySignature (legVertex L1)⟩ : AnySignature ℂ) ∈ F)
    (hL3 : (⟨2,binarySignature (legVertex L3)⟩ : AnySignature ℂ) ∈ F)
    (hM : (⟨2,binarySignature (pairVertex M)⟩ : AnySignature ℂ) ∈ F) :
    Gadget.Realizes F .disequality
      (Signature.contract M
        (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3]
          (Signature.contract K h))) := by
  apply (sparse_realizes h K L1 L3 M).mono
  rintro p (rfl | rfl | rfl | rfl | rfl)
  · exact hh
  · exact hK
  · exact hL1
  · exact hL3
  · exact hM

@[simp] theorem sparseNetwork_binary_vertices (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (Finset.univ.filter (fun v => (sparseNetwork h K L1 L3 M).shape.arity v = 2)).card = 4 := by
  change (Finset.univ.filter (fun v : Fin 5 => sparseArity v = 2)).card = 4
  decide

@[simp] theorem sparseNetwork_ancestor_vertices (h : Signature ℂ 6) (K L1 L3 M : Binary) :
    (Finset.univ.filter (fun v => (sparseNetwork h K L1 L3 M).shape.arity v = 6)).card = 1 := by
  change (Finset.univ.filter (fun v : Fin 5 => sparseArity v = 6)).card = 1
  decide

end
end Holant.Certificates.OctahedralSeparator.Native
