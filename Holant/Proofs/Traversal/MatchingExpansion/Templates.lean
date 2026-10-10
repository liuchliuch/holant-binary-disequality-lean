import Holant.Proofs.Traversal.MatchingExpansion.Factors
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence
import Holant.Complexity.FixedGadgetSubstitution.Incidence
import Holant.Proofs.Algorithms.RawArityTransport
import Holant.Complexity.BinaryInterpolation.Chains.Template


namespace Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Templates
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.TraversalCompletion.ArityTwo.TensorNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ} (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (opposite : Bool) (hf : ∀ i, SourceTensorClosure (matchingImage opposite) (G i))

def data (i : Fin s) := Factors.data (Orientation.transformed G opposite i)
  (Orientation.inverse_closure opposite (G i) (hf i))
abbrev Label := Σ i : Fin s, (data G opposite hf i).Vertex
def size := Fintype.card (Label G opposite hf)
def order : Label G opposite hf ≃ Fin (size G opposite hf) := Fintype.equivFin _
def localArity (i : Label G opposite hf) := (data G opposite hf i.1).vertexArity i.2
def localSignature (i : Label G opposite hf) : Signature AlgebraicComplex (localArity G opposite hf i) :=
  (data G opposite hf i.1).finite.vertex i.2

def arity (j : ℕ) : ℕ :=
  if h : j < size G opposite hf then localArity G opposite hf ((order G opposite hf).symm ⟨j,h⟩) else 0

@[simp] theorem arity_fin (j : Fin (size G opposite hf)) :
    arity G opposite hf j.val = localArity G opposite hf ((order G opposite hf).symm j) := by
  simp [arity,j.isLt]
@[simp] theorem arity_order (i : Label G opposite hf) :
    arity G opposite hf ((order G opposite hf) i).val = localArity G opposite hf i := by simp

def signatures (j : Fin (size G opposite hf)) : Signature AlgebraicComplex (arity G opposite hf j.val) :=
  fun x => localSignature G opposite hf ((order G opposite hf).symm j)
    (fun k => x (Fin.cast (arity_fin G opposite hf j).symm k))

private theorem oneHot_cast {m n : ℕ} (h : m=n) (f : Signature AlgebraicComplex m)
    (hf : Signature.OneHot f) :
    Signature.OneHot (fun x : Fin n → Bool => f (fun j => x (Fin.cast h j))) := by
  subst n
  simpa using hf

theorem oneHot (j : Fin (size G opposite hf)) : Signature.OneHot (signatures G opposite hf j) := by
  exact oneHot_cast (arity_fin G opposite hf j).symm
    (localSignature G opposite hf ((order G opposite hf).symm j))
    (Factors.vertex_oneHot _ _ ((order G opposite hf).symm j).2)

private theorem signature_at_label (l : Label G opposite hf) :
    (⟨arity G opposite hf ((order G opposite hf) l).val,
      signatures G opposite hf ((order G opposite hf) l)⟩ : AnySignature AlgebraicComplex)=
        ⟨localArity G opposite hf l,localSignature G opposite hf l⟩ := by
  apply Sigma.ext (arity_order G opposite hf l)
  have hc : ∀{m n : ℕ} (h : m=n) (f : Signature AlgebraicComplex m),
      HEq (fun x : Fin n → Bool => f (fun j => x (Fin.cast h j))) f := by
    intro m n h f
    subst n
    rfl
  have h := hc (arity_fin G opposite hf ((order G opposite hf) l)).symm
    (localSignature G opposite hf ((order G opposite hf).symm ((order G opposite hf) l)))
  have hs : (order G opposite hf).symm ((order G opposite hf) l)=l :=
    Equiv.symm_apply_apply _ _
  have ht : (⟨localArity G opposite hf ((order G opposite hf).symm ((order G opposite hf) l)),
      localSignature G opposite hf ((order G opposite hf).symm ((order G opposite hf) l))⟩ : AnySignature AlgebraicComplex)=
        ⟨localArity G opposite hf l,localSignature G opposite hf l⟩ :=
    congrArg (fun t => (⟨localArity G opposite hf t,localSignature G opposite hf t⟩ : AnySignature AlgebraicComplex)) hs
  exact h.trans (Sigma.mk.inj_iff.mp ht).2

def labelling (i : Fin s) :
    Labelling (data G opposite hf i).network.shape (size G opposite hf) 1 (arity G opposite hf) where
  vertex v := order G opposite hf ⟨i,(Fintype.equivFin (data G opposite hf i).Vertex).symm v⟩
  vertex_arity v := by rw [arity_order]; rfl
  edge e := Fin.elim0 e

def template (i : Fin s) : Template := (labelling G opposite hf i).template
theorem template_wellFormed (i : Fin s) :
    (template G opposite hf i).WellFormed (size G opposite hf) 1 (arity G opposite hf) :=
  (labelling G opposite hf i).wellFormed
@[simp] theorem template_boundary (i : Fin s) : (template G opposite hf i).boundary = a i.val := rfl
@[simp] theorem template_edges (i : Fin s) : (template G opposite hf i).edges = [] := by
  simp [template,Labelling.template,labelling,Data.network,FiniteNetwork.toNetwork]

theorem template_denote (i : Fin s) :
    ((template G opposite hf i).network (template_wellFormed G opposite hf i)
      (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote =
        Orientation.transformed G opposite i := by
  have h := Labelling.denote_template_of_labels (labelling G opposite hf i)
    (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)
    (data G opposite hf i).network.vertex (data G opposite hf i).network.edge
    (by
      intro v x
      exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
        (signatures G opposite hf ((labelling G opposite hf i).vertex v))
        ((data G opposite hf i).network.vertex v)
        (signature_at_label G opposite hf ⟨i,(Fintype.equivFin (data G opposite hf i).Vertex).symm v⟩)
        ((labelling G opposite hf i).vertex_arity v) x)
    (by intro e; exact Fin.elim0 e)
  exact h.trans (Factors.network_exact _ _)

def templates (j : ℕ) : Template :=
  if h : j < s then template G opposite hf ⟨j,h⟩ else ⟨0,[],[]⟩
@[simp] theorem templates_fin (i : Fin s) : templates G opposite hf i.val = template G opposite hf i := by
  simp [templates,i.isLt]

theorem hypotheses (j : ℕ) (hj : j<s) :
    (templates G opposite hf j).WellFormed (size G opposite hf) 1 (arity G opposite hf) ∧
      (templates G opposite hf j).boundary = a j := by
  constructor
  · simpa only [templates,dif_pos hj] using template_wellFormed G opposite hf ⟨j,hj⟩
  · simp [templates,hj]

def derivedArity := FixedGadgetSubstitution.sourceArity (templates G opposite hf)
theorem arityAgree (i : Fin s) : a i.val = derivedArity G opposite hf i.val := by
  simp [derivedArity,FixedGadgetSubstitution.sourceArity]

theorem templates_exact (i : Fin s) :
    ((templates G opposite hf i.val).network (hypotheses G opposite hf i.val i.isLt).1
      (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote =
        RawArityTransport.signatures (arityAgree G opposite hf) (Orientation.transformed G opposite) i := by
  have he : HEq (((templates G opposite hf i.val).network
      (hypotheses G opposite hf i.val i.isLt).1 (signatures G opposite hf)
      (fun _ : Fin 1 => Signature.disequality)).denote) (Orientation.transformed G opposite i) := by
    have ht := templates_fin G opposite hf i
    have hc : ∀{u v : Template} (hu : u.WellFormed (size G opposite hf) 1 (arity G opposite hf))
        (hv : v.WellFormed (size G opposite hf) 1 (arity G opposite hf)), u=v →
        HEq (u.network hu (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote
          (v.network hv (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote := by
      intro u v hu hv h
      cases h
      rfl
    exact (hc _ (template_wellFormed G opposite hf i) ht).trans
      (heq_of_eq (template_denote G opposite hf i))
  have hsigma : (⟨derivedArity G opposite hf i.val,
      ((templates G opposite hf i.val).network (hypotheses G opposite hf i.val i.isLt).1
        (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote⟩ : AnySignature AlgebraicComplex)=
      ⟨a i.val,Orientation.transformed G opposite i⟩ :=
    Sigma.ext (arityAgree G opposite hf i).symm he
  funext x
  exact (Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    (Orientation.transformed G opposite i)
    ((templates G opposite hf i.val).network (hypotheses G opposite hf i.val i.isLt).1
      (signatures G opposite hf) (fun _ : Fin 1 => Signature.disequality)).denote
    hsigma.symm (arityAgree G opposite hf i) x).symm

end
end Holant.LocalDrafts.TraversalCompletion.MatchingExpansion.Templates
