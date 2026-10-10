import Holant.NetworkContraction
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence


namespace Holant.LocalDrafts.Hardness.NativeCap
open Holant.Complexity.FixedGadgetSubstitution

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Ordered binary block followed by the surviving ordered block. -/
def frontProduct (b : Bool → Bool → K) (a : Signature K n) : Signature K (n + 2) :=
  fun x => b (x 0) (x 1) * a (fun i => x i.succ.succ)

def capScalar (b : Bool → Bool → K) : K := b false true + b true false

/-- One original vertex, one real X edge, no extra signature or scalar vertex. -/
def graph (h : Signature K (n + 2)) : Network K n :=
  (Network.corolla h).contract Signature.disequality

@[simp] theorem graph_vertices (h : Signature K (n + 2)) :
    (graph h).shape.vertices = 1 := rfl

@[simp] theorem graph_edges (h : Signature K (n + 2)) :
    (graph h).shape.edges = 1 := rfl

theorem graph_denote (b : Bool → Bool → K) (a : Signature K n) :
    (graph (frontProduct b a)).denote = capScalar b • a := by
  funext x
  rw [graph, Network.denote_contract_disequality]
  simp only [Network.denote_corolla, frontProduct, Fin.cons_zero, Fin.cons_succ]
  change b false true * a x + b true false * a x =
    (b false true + b true false) * a x
  exact (add_mul _ _ _).symm

theorem graph_denote_of_factorization (h : Signature K (n + 2))
    (b : Bool → Bool → K) (a : Signature K n) (hf : h = frontProduct b a) :
    (graph h).denote = capScalar b • a := by
  rw [hf]
  exact graph_denote b a

variable {s : ℕ} {arity : ℕ → ℕ}

/-- Read the original table without changing the order of any original port. -/
def retainedTensor (signatures : (i : Fin s) → Signature K (arity i.val))
    (j : Fin s) (hj : arity j.val = n + 2) : Signature K (n + 2) :=
  fun x => signatures j (fun i => x (Fin.cast hj i))

/-- Literal retained label on the only vertex; edge label zero is native X. -/
def labelling (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : Labelling (graph h).shape s 1 arity where
  vertex _ := j
  vertex_arity _ := hj
  edge _ := 0

def template (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : Template := (labelling h j hj).template

theorem template_wellFormed (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : (template h j hj).WellFormed s 1 arity :=
  (labelling h j hj).wellFormed

@[simp] theorem template_boundary (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : (template h j hj).boundary = n := rfl

@[simp] theorem template_vertices (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : (template h j hj).vertices.length = 1 := by
  exact (labelling h j hj).vertices_length

@[simp] theorem template_edges (h : Signature K (n + 2)) (j : Fin s)
    (hj : arity j.val = n + 2) : (template h j hj).edges.length = 1 := by
  exact (labelling h j hj).edges_length

/-- Serialization preserves the actual ordered gadget, rather than merely a
claimed tensor formula attached to arbitrary query bytes. -/
theorem template_denote
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (j : Fin s) (hj : arity j.val = n + 2) :
    ((template (retainedTensor signatures j hj) j hj).network
      (template_wellFormed _ j hj) signatures (fun _ => Signature.disequality)).denote =
      (graph (retainedTensor signatures j hj)).denote := by
  apply Labelling.denote_template_of_labels
  · intro v x
    rfl
  · intro e u v
    change Fin 1 at e
    have he : e = 0 := Subsingleton.elim _ _
    subst e
    rfl

theorem template_denote_factor
    (signatures : (i : Fin s) → Signature K (arity i.val))
    (j : Fin s) (hj : arity j.val = n + 2)
    (b : Bool → Bool → K) (a : Signature K n)
    (hf : retainedTensor signatures j hj = frontProduct b a) :
    ((template (retainedTensor signatures j hj) j hj).network
      (template_wellFormed _ j hj) signatures (fun _ => Signature.disequality)).denote =
      capScalar b • a := by
  rw [template_denote]
  exact graph_denote_of_factorization _ b a hf

end Holant.LocalDrafts.Hardness.NativeCap
