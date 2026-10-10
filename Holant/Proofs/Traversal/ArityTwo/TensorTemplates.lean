import Holant.Proofs.Traversal.ArityTwo.TensorNetwork
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence
import Holant.Complexity.FixedGadgetSubstitution.Incidence


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorTemplates
open Holant Holant.Complexity Holant.Tractable
open FixedGadgetSubstitution TensorNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} (family : Fin s → AnySignature AlgebraicComplex)
variable (hf : ∀ i, SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) (family i).2)

abbrev data (i : Fin s) := ofSource (family i).2 (hf i)
abbrev Label := Σ i : Fin s, (data family hf i).Vertex
abbrev size := Fintype.card (Label family hf)
def order : Label family hf ≃ Fin (size family hf) := Fintype.equivFin _
def localArity (i : Label family hf) := (data family hf i.1).vertexArity i.2
def localSignature (i : Label family hf) : Signature AlgebraicComplex (localArity family hf i) :=
  (data family hf i.1).finite.vertex i.2

def arity (j : ℕ) : ℕ :=
  if h : j < size family hf then localArity family hf ((order family hf).symm ⟨j,h⟩) else 0

@[simp] theorem arity_fin (j : Fin (size family hf)) :
    arity family hf j.val = localArity family hf ((order family hf).symm j) := by
  simp only [arity, dif_pos j.isLt, Fin.eta]

@[simp] theorem arity_order (i : Label family hf) :
    arity family hf ((order family hf) i).val = localArity family hf i := by simp

def signatures (j : Fin (size family hf)) : Signature AlgebraicComplex (arity family hf j.val) :=
  fun x => localSignature family hf ((order family hf).symm j)
    (fun k => x (Fin.cast (arity_fin family hf j).symm k))

theorem arity_le (j : Fin (size family hf)) : arity family hf j.val ≤ 2 := by
  rw [arity_fin]
  obtain ⟨i,v⟩ := (order family hf).symm j
  cases v with
  | none => exact Nat.zero_le _
  | some k => exact ofSource_arity (family i).2 (hf i) k

variable (b : ℕ)

abbrev labelling (i : Fin s) :
    Labelling (data family hf i).network.shape (size family hf) b (arity family hf) where
  vertex v := order family hf ⟨i,(Fintype.equivFin (data family hf i).Vertex).symm v⟩
  vertex_arity v := by
    rw [arity_order]
    rfl
  edge e := Fin.elim0 e

def template (i : Fin s) : Template := (labelling family hf b i).template

theorem template_wellFormed (i : Fin s) :
    (template family hf b i).WellFormed (size family hf) b (arity family hf) :=
  (labelling family hf b i).wellFormed

@[simp] theorem template_boundary (i : Fin s) : (template family hf b i).boundary = (family i).1 := rfl

@[simp] theorem template_edges (i : Fin s) : (template family hf b i).edges = [] := by
  simp [template,Labelling.template,labelling,Data.network,FiniteNetwork.toNetwork]

theorem localSignature_congr {u v : Label family hf} (h : u = v)
    (x : Fin (localArity family hf u) → Bool) (y : Fin (localArity family hf v) → Bool)
    (hx : ∀ k, x k = y (Fin.cast (congrArg (localArity family hf) h) k)) :
    localSignature family hf u x = localSignature family hf v y := by
  subst v
  exact congrArg (localSignature family hf u) (funext hx)

theorem template_denote (i : Fin s) (edges : Fin b → Kernel AlgebraicComplex) :
    ((template family hf b i).network (template_wellFormed family hf b i)
      (signatures family hf) edges).denote = (family i).2 := by
  have h := Labelling.denote_template_of_labels (labelling family hf b i)
    (signatures family hf) edges (data family hf i).network.vertex (data family hf i).network.edge
    (by
      intro v x
      let u : Label family hf := ⟨i,(Fintype.equivFin (data family hf i).Vertex).symm v⟩
      change localSignature family hf ((order family hf).symm ((order family hf) u))
        (fun k => x (Fin.cast ((labelling family hf b i).vertex_arity v)
          (Fin.cast (arity_fin family hf ((order family hf) u)).symm k))) =
        localSignature family hf u x
      apply localSignature_congr family hf ((order family hf).symm_apply_apply u)
      intro k
      congr 1)
    (by intro e; exact Fin.elim0 e)
  exact h.trans (ofSource_network (family i).2 (hf i))

/-- Invalid labels are outside the faithful validated input language. Giving
them an empty template makes the source arity a total natural-number function. -/
abbrev templates (j : ℕ) : Template :=
  if h : j < s then template family hf b ⟨j,h⟩ else ⟨0,[],[]⟩

@[simp] theorem templates_fin (i : Fin s) : templates family hf b i.val = template family hf b i := by
  simp [templates,i.isLt]

abbrev originalArity := FixedGadgetSubstitution.sourceArity (templates family hf b)

@[simp] theorem originalArity_fin (i : Fin s) : originalArity family hf b i.val = (family i).1 := by
  simp [originalArity,FixedGadgetSubstitution.sourceArity]

def originalSignatures (i : Fin s) : Signature AlgebraicComplex (originalArity family hf b i.val) :=
  fun x => (family i).2 (fun k => x (Fin.cast (originalArity_fin family hf b i).symm k))

theorem templates_wellFormed (j : ℕ) (hj : j < s) :
    (templates family hf b j).WellFormed (size family hf) b (arity family hf) := by
  simpa [templates,hj] using template_wellFormed family hf b ⟨j,hj⟩

theorem templates_exact (i : Fin s) (edges : Fin b → Kernel AlgebraicComplex) :
    ((templates family hf b i.val).network (templates_wellFormed family hf b i.val i.isLt)
      (signatures family hf) edges).denote = originalSignatures family hf b i := by
  have aux (t : Template) (ht : t = template family hf b i)
      (hw : t.WellFormed (size family hf) b (arity family hf))
      (hb : t.boundary = (family i).1) :
      (t.network hw (signatures family hf) edges).denote =
        fun x => (family i).2 (fun k => x (Fin.cast hb.symm k)) := by
    subst t
    simpa only [template_boundary, Fin.cast_refl, id_eq] using template_denote family hf b i edges
  exact aux _ (templates_fin family hf b i) _ (originalArity_fin family hf b i)

end
end Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorTemplates
