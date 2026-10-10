import Holant.Proofs.Hardness.EONegativeWitness
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Actual original-labelled disjoint unions for the arbitrary-arity EO
support reduction. The boundary contains every original incidence exactly
once; no equality vertex, pinning signature or extra coefficient is inserted.
The empty union is the empty graph, rather than an added scalar vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeTensorCore
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable {s t : ℕ} {a : ℕ → ℕ}
variable (labels : Fin t → Fin s)

abbrev Port := (v : Fin t) × Fin (a (labels v).val)
abbrev arity := Fintype.card (Port (a:=a) labels)
def boundary : Port (a:=a) labels ≃ Fin (arity (a:=a) labels) := Fintype.equivFin _

def shape : NetworkShape (arity (a:=a) labels) where
  vertices := t
  arity v := a (labels v).val
  edges := 0
  ports := {
    toFun p := .inl (boundary labels p)
    invFun p := p.elim (boundary labels).symm (fun q => Fin.elim0 q.1)
    left_inv p := (boundary labels).symm_apply_apply p
    right_inv p := by
      rcases p with p | p
      · exact congrArg Sum.inl ((boundary labels).apply_symm_apply p)
      · exact Fin.elim0 p.1 }

def graph {K : Type*} (G : (i : Fin s) → Signature K (a i.val)) :
    Network K (arity (a:=a) labels) where
  shape := shape labels
  vertex v := G (labels v)
  edge e := Fin.elim0 e

def labelling : Labelling (shape (a:=a) labels) s 1 a where
  vertex := labels
  vertex_arity _ := rfl
  edge e := Fin.elim0 e

abbrev template := (labelling (a:=a) labels).template
abbrev valid := (labelling (a:=a) labels).wellFormed

/-- Local words are assembled along the actual boundary incidence bijection. -/
def word (x : (v : Fin t) → Fin (a (labels v).val) → Bool) :
    Fin (arity (a:=a) labels) → Bool := fun j =>
  x ((boundary labels).symm j).1 ((boundary labels).symm j).2

@[simp] theorem word_boundary (x : (v : Fin t) → Fin (a (labels v).val) → Bool)
    (v : Fin t) (i : Fin (a (labels v).val)) :
    word labels x (boundary labels ⟨v,i⟩)=x v i := by
  change (fun p : Port (a:=a) labels => x p.1 p.2) ((boundary labels).symm (boundary labels ⟨v,i⟩))=_
  rw [Equiv.symm_apply_apply]

def readWord (x : Fin (arity (a:=a) labels) → Bool)
    (v : Fin t) (i : Fin (a (labels v).val)) : Bool := x (boundary labels ⟨v,i⟩)

@[simp] theorem word_read (x : Fin (arity (a:=a) labels) → Bool) :
    word labels (readWord labels x)=x := by
  funext j
  simp [word,readWord]

theorem triple_word (x y z : (v : Fin t) → Fin (a (labels v).val) → Bool) :
    tripleXor (word labels x) (word labels y) (word labels z)=
      word labels (fun v => tripleXor (x v) (y v) (z v)) := rfl

theorem arity_sum : arity (a:=a) labels=∑v,a (labels v).val := by
  simp [arity,Port,Fintype.card_sigma]

private theorem charge_sum {n : ℕ} (x : Fin n → Bool) :
    charge x=∑i,if x i then (1:ℤ) else -1 := by
  have h (b : Bool) : (if b then (1:ℤ) else -1)=2*(if b then (1:ℤ) else 0)-1 := by
    cases b <;> rfl
  simp only [h,Finset.sum_sub_distrib,←Finset.mul_sum]
  simp [charge,weight]

theorem charge_word (x : (v : Fin t) → Fin (a (labels v).val) → Bool) :
    charge (word labels x)=∑v,charge (x v) := by
  simp only [charge_sum]
  calc
    _ = ∑p : Port (a:=a) labels,if x p.1 p.2 then (1:ℤ) else -1 := by
      apply Fintype.sum_equiv (boundary (a:=a) labels).symm
      intro j
      rfl
    _ = _ := Fintype.sum_sigma _

variable {K : Type*} [Field K]
variable (G : (i : Fin s) → Signature K (a i.val))

theorem denote_word (x : (v : Fin t) → Fin (a (labels v).val) → Bool) :
    (graph labels G).denote (word labels x)=∏v,G (labels v) (x v) := by
  have ha (z : (Fin 0 × Bool) → Bool) (v : Fin t) :
      (shape labels).assignment (word labels x) z v=x v := by
    funext i
    exact word_boundary labels x v i
  simp only [Network.denote,graph,ha]
  simp [shape]

theorem denote_read (x : Fin (arity (a:=a) labels) → Bool) :
    (graph labels G).denote x=∏v,G (labels v) (readWord labels x v) := by
  rw [←word_read labels x,denote_word]
  simp only [word_read]

theorem supported_word (x : (v : Fin t) → Fin (a (labels v).val) → Bool)
    (h : ∀v,G (labels v) (x v)≠0) : (graph labels G).denote (word labels x)≠0 := by
  rw [denote_word]
  exact Finset.prod_ne_zero_iff.mpr (fun v _=>h v)

theorem missing_word (x : (v : Fin t) → Fin (a (labels v).val) → Bool)
    (v : Fin t) (h : G (labels v) (x v)=0) : (graph labels G).denote (word labels x)=0 := by
  rw [denote_word]
  exact Finset.prod_eq_zero (Finset.mem_univ v) h

theorem central (h : ∀v,Signature.CentralSupport (G (labels v))) :
    Signature.CentralSupport (graph labels G).denote := by
  intro x hx
  by_contra hn
  have hp : ∀v,G (labels v) (readWord labels x v)≠0 := by
    rw [denote_read] at hn
    exact fun v => Finset.prod_ne_zero_iff.mp hn v (Finset.mem_univ v)
  have hc : ∀v,charge (readWord labels x v)=0 := by
    intro v
    have hw : 2*weight (readWord labels x v)=a (labels v).val := by
      by_contra hw
      exact hp v (h v _ hw)
    unfold charge
    omega
  have hh := charge_word labels (readWord labels x)
  rw [word_read] at hh
  simp only [hc,Finset.sum_const_zero] at hh
  unfold charge at hh
  omega

theorem template_denote :
    ((template labels).network (valid labels) G
      (fun _ : Fin 1=>Signature.disequality)).denote=(graph labels G).denote := by
  apply Labelling.denote_template_of_labels (labelling labels) G
    (fun _ : Fin 1=>Signature.disequality) (graph labels G).vertex (graph labels G).edge
  · intro v x
    rfl
  · intro e
    exact Fin.elim0 e

@[simp] theorem vertices : (graph labels G).shape.vertices=t := rfl
@[simp] theorem edges : (graph labels G).shape.edges=0 := rfl
@[simp] theorem template_vertices : (template (a:=a) labels).vertices.length=t := by
  exact (labelling labels).vertices_length
@[simp] theorem template_edges : (template (a:=a) labels).edges.length=0 := by
  exact (labelling labels).edges_length

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEONegativeTensorCore
