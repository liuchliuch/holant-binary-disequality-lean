import Holant.Certificates.TetrahedralOrientation.PhysicalDenotation

/-! Literal native-X realization of a first-pair contraction followed by four
ordered boundary matrices. Every binary resource is an actual vertex. -/
namespace Holant.Certificates.OctahedralSeparator.Native
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Binary := Kernel ℂ

def binarySignature (U : Binary) : Signature ℂ 2 := fun x => U (x 0) (x 1)

/-- The vertex placed between two native X edges. -/
def pairVertex (K : Binary) : Binary := fun a b => K (!a) (!b)

/-- Boundary-first, internal-second binary for the column action of L. -/
def legVertex (L : Binary) : Binary := Kernel.mul L Signature.disequality

theorem pairVertex_eq_sandwich (K : Binary) :
    pairVertex K = Kernel.mul (Kernel.mul Signature.disequality K) Signature.disequality := by
  funext a b
  exact (Kernel.disequality_sandwich K a b).symm

@[simp] theorem pairVertex_edge (K : Binary) (a b : Bool) :
    pairVertex K (!a) (!b) = K a b := by simp [pairVertex]

@[simp] theorem legVertex_edge (L : Binary) (a b : Bool) :
    legVertex L a (!b) = L a b := by simp [legVertex,Kernel.mul_disequality]

def dressedArity : Fin 6 → ℕ := Fin.cases 6 (fun _ => 2)

def dressedPortMap : (Σ v : Fin 6, Fin (dressedArity v)) → (Fin 4 ⊕ (Fin 6 × Bool)) := fun p =>
  Fin.cases (fun i => .inr (i,false))
    (fun v => Fin.cases (fun i : Fin 2 => .inr ((if i = 0 then 0 else 1),true))
      (fun j => fun i : Fin 2 => if i = 0 then .inl j else .inr (j.succ.succ,true)) v) p.1 p.2

def dressedPortInv : (Fin 4 ⊕ (Fin 6 × Bool)) → (Σ v : Fin 6, Fin (dressedArity v))
  | .inl j => ⟨j.succ.succ,(0 : Fin 2)⟩
  | .inr (e,b) => if b then
      Fin.cases ⟨(1 : Fin 6),(0 : Fin 2)⟩
        (fun e' => Fin.cases ⟨(1 : Fin 6),(1 : Fin 2)⟩
          (fun j => ⟨j.succ.succ,(1 : Fin 2)⟩) e') e
    else ⟨(0 : Fin 6),e⟩

def dressedShape : NetworkShape 4 where
  vertices := 6
  arity := dressedArity
  edges := 6
  ports := {
    toFun := dressedPortMap
    invFun := dressedPortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [dressedArity] at i <;> fin_cases i <;> rfl
    right_inv q := by
      cases q with
      | inl j => fin_cases j <;> rfl
      | inr q => rcases q with ⟨e,b⟩; fin_cases e <;> cases b <;> rfl }

def dressedLabels (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (v : Fin 6) → Signature ℂ (dressedArity v) :=
  Fin.cases h (fun v => Fin.cases (binarySignature (pairVertex K))
    (fun j => binarySignature (legVertex (L j))) v)

def dressedNetwork (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) : Network ℂ 4 where
  shape := dressedShape
  vertex := dressedLabels h K L
  edge := fun _ => Signature.disequality

/-- The first pair is original ports1/2; output order is original3/4/5/6. -/
def dressedChoices : (Fin 6 → Bool) ≃ (Bool × Bool × (Fin 4 → Bool)) where
  toFun c := (!(c 0),!(c 1),fun j => !(c j.succ.succ))
  invFun q := ![!q.1,!q.2.1,!(q.2.2 0),!(q.2.2 1),!(q.2.2 2),!(q.2.2 3)]
  left_inv c := by funext j; fin_cases j <;> simp
  right_inv q := by
    rcases q with ⟨a,b,y⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext j; fin_cases j <;> simp

theorem dressed_product (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary)
    (x y : Fin 4 → Bool) (a b : Bool) :
    (∏ v : Fin 6, dressedLabels h K L v
      (dressedShape.assignment x (Network.endpointChoiceAssignment (dressedChoices.symm (a,b,y))) v)) =
      h (Fin.cons a (Fin.cons b y)) * K a b * ∏ j : Fin 4, L j (x j) (y j) := by
  have ha : dressedShape.assignment x
      (Network.endpointChoiceAssignment (dressedChoices.symm (a,b,y))) (0 : Fin 6) =
        Fin.cons a (Fin.cons b y) := by
    funext i
    fin_cases i <;> simp [dressedShape,NetworkShape.assignment,dressedPortMap,
      Network.endpointChoiceAssignment,dressedChoices,Fin.cons] <;> rfl
  simp only [dressedShape,Fin.prod_univ_succ]
  change h (dressedShape.assignment x
      (Network.endpointChoiceAssignment (dressedChoices.symm (a,b,y))) (0 : Fin 6)) * _ = _
  rw [ha]
  change h (Fin.cons a (Fin.cons b y)) *
    (pairVertex K (!a) (!b) * (legVertex (L 0) (x 0) (!(y 0)) *
      (legVertex (L 1) (x 1) (!(y 1)) *
        (legVertex (L 2) (x 2) (!(y 2)) *
          (legVertex (L 3) (x 3) (!(y 3)) * 1))))) = _
  simp [legVertex_edge,pairVertex_edge,mul_one,mul_assoc]

theorem dressedNetwork_denote (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (dressedNetwork h K L).denote = Signature.coordinateAction L (Signature.contract K h) := by
  rw [dressedNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 6 → Bool, ∏ v : Fin 6, dressedLabels h K L v
    (dressedShape.assignment x (Network.endpointChoiceAssignment c) v)) = _
  rw [← dressedChoices.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [dressed_product]
  simp only [Signature.coordinateAction,Signature.contract,Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Exactly one ancestor, the first-pair binary, and four ordered leg resources. -/
def dressedResources (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) : SignatureFamily ℂ :=
  {p | p = ⟨6,h⟩ ∨ p = ⟨2,binarySignature (pairVertex K)⟩ ∨
    ∃ j : Fin 4, p = ⟨2,binarySignature (legVertex (L j))⟩}

theorem dressed_realizes (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    Gadget.Realizes (dressedResources h K L) .disequality
      (Signature.coordinateAction L (Signature.contract K h)) := by
  have hr := Gadget.realizes_network (dressedNetwork h K L) (dressedResources h K L) .disequality
    (by intro v; fin_cases v
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨0,rfl⟩)
        · exact Or.inr (Or.inr ⟨1,rfl⟩)
        · exact Or.inr (Or.inr ⟨2,rfl⟩)
        · exact Or.inr (Or.inr ⟨3,rfl⟩))
    (by intro e; rfl)
  rwa [dressedNetwork_denote] at hr

@[simp] theorem dressedNetwork_vertices (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (dressedNetwork h K L).shape.vertices = 6 := rfl

@[simp] theorem dressedNetwork_edges (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary) :
    (dressedNetwork h K L).shape.edges = 6 := rfl

/-- Membership in any ambient resource family suffices; no realization callback is assumed. -/
theorem dressed_realizes_of_mem (F : SignatureFamily ℂ)
    (h : Signature ℂ 6) (K : Binary) (L : Fin 4 → Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ F)
    (hK : (⟨2,binarySignature (pairVertex K)⟩ : AnySignature ℂ) ∈ F)
    (hL : ∀ j, (⟨2,binarySignature (legVertex (L j))⟩ : AnySignature ℂ) ∈ F) :
    Gadget.Realizes F .disequality (Signature.coordinateAction L (Signature.contract K h)) := by
  apply (dressed_realizes h K L).mono
  rintro p (rfl | rfl | ⟨j,rfl⟩)
  · exact hh
  · exact hK
  · exact hL j

@[simp] theorem dressedNetwork_binary_vertices (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    (Finset.univ.filter (fun v => (dressedNetwork h K L).shape.arity v = 2)).card = 5 := by
  change (Finset.univ.filter (fun v : Fin 6 => dressedArity v = 2)).card = 5
  decide

@[simp] theorem dressedNetwork_ancestor_vertices (h : Signature ℂ 6)
    (K : Binary) (L : Fin 4 → Binary) :
    (Finset.univ.filter (fun v => (dressedNetwork h K L).shape.arity v = 6)).card = 1 := by
  change (Finset.univ.filter (fun v : Fin 6 => dressedArity v = 6)).card = 1
  decide

end
end Holant.Certificates.OctahedralSeparator.Native
