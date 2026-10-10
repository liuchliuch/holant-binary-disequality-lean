import Holant.Complexity.EdgeSubdivision.Labels
import Holant.Complexity.FixedGadgetSubstitution.Identity
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! The two-vertex path used in equality-wire equivalence. Its vertex resources
are the opposite literal binary; its one internal edge is the target wire. -/
namespace Holant.Complexity.EdgeSubdivision.WirePath
noncomputable section
open FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def portMap : (Σ _ : Fin 2, Fin 2) → (Fin 2 ⊕ (Fin 1×Bool)) :=
  fun p => if p.1=0 then (if p.2=0 then .inl 0 else .inr (0,false))
    else (if p.2=0 then .inr (0,true) else .inl 1)

def shape : NetworkShape 2 where
  vertices := 2
  arity _ := 2
  edges := 1
  ports := Equiv.ofBijective portMap (by decide)

def labelling (s : ℕ) (arity : ℕ → ℕ) :
    Labelling shape (s+1) 1 (targetArity s arity) where
  vertex _ := Fin.last s
  vertex_arity _ := by simp [shape,targetArity]
  edge _ := 0

def template (s : ℕ) (arity : ℕ → ℕ) : Template := (labelling s arity).template

theorem valid (s : ℕ) (arity : ℕ → ℕ) :
    (template s arity).WellFormed (s+1) 1 (targetArity s arity) :=
  (labelling s arity).wellFormed

@[simp] theorem boundary (s : ℕ) (arity : ℕ → ℕ) : (template s arity).boundary=2 := rfl

variable {K : Type*} [CommSemiring K]
def network (B W : Bool → Bool → K) : Network K 2 where
  shape := shape
  vertex _ x := B (x (0 : Fin 2)) (x (1 : Fin 2))
  edge _ := W

def assignmentPair : ((Fin 1×Bool) → Bool) ≃ (Bool×Bool) where
  toFun z := (z (0,false),z (0,true))
  invFun uv p := if p.2 then uv.2 else uv.1
  left_inv z := by
    funext p
    rcases p with ⟨e,c⟩
    have he : e=0 := Subsingleton.elim _ _
    subst e
    cases c <;> rfl
  right_inv uv := rfl

theorem denote (B W : Bool → Bool → K) (x : Fin 2 → Bool) :
    (network B W).denote x = ∑ uv : Bool×Bool,
      B (x 0) uv.1 * W uv.1 uv.2 * B uv.2 (x 1) := by
  unfold Network.denote
  apply Fintype.sum_equiv assignmentPair
  intro z
  simp only [network,shape,Fin.prod_univ_two,Fin.prod_univ_one,
    NetworkShape.assignment,Equiv.ofBijective_apply,portMap]
  simp [assignmentPair]
  ring

def kernel (p : Bool) (a b : Bool) : K := if a^^b=p then 1 else 0

theorem kernel_sandwich (p q a b : Bool) :
    (∑ uv : Bool×Bool,
      kernel (K:=K) p a uv.1 * kernel q uv.1 uv.2 * kernel p uv.2 b) = kernel q a b := by
  cases p <;> cases q <;> cases a <;> cases b <;>
    simp [Fintype.sum_prod_type,Fintype.sum_bool,kernel]

theorem denote_kernel (p q : Bool) (x : Fin 2 → Bool) :
    (network (kernel (K:=K) p) (kernel q)).denote x = kernel q (x 0) (x 1) := by
  rw [denote]
  exact kernel_sandwich p q _ _

theorem template_denote (s : ℕ) (arity : ℕ → ℕ)
    (source : (i : Fin s) → Signature K (arity i.val)) (p q : Bool) :
    ((template s arity).network (valid s arity)
      (extendedSignatures source (fun _ : Fin 1 => kernel p))
      (fun _ : Fin 1 => kernel q)).denote =
      (fun x : Fin 2 → Bool => kernel q (x 0) (x 1)) := by
  change (((labelling s arity).template).network (labelling s arity).wellFormed
      (extendedSignatures source (fun _ : Fin 1 => kernel p))
      (fun _ : Fin 1 => kernel q)).denote = _
  rw [Labelling.denote_template]
  have h : (Labelling.sourceNetwork (labelling s arity)
      (extendedSignatures source (fun _ : Fin 1 => kernel p))
      (fun _ : Fin 1 => kernel q)) = network (kernel p) (kernel q) := by
    unfold Labelling.sourceNetwork network
    congr 1
    funext v x
    simp [labelling,extendedSignatures]
  rw [h]
  exact funext (denote_kernel p q)

end
end Holant.Complexity.EdgeSubdivision.WirePath
