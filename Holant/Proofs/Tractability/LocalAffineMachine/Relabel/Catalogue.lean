import Holant.Proofs.Algorithms.LocalAffine.FiniteLabels
import Holant.Proofs.Tractability.AffineMachine.FamilySolver


namespace Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Catalogue

open Holant.Tractable Holant.Complexity Holant.Tractable.AffinePhase
open MainChain
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ}

abbrev V := LocalAffineLabels.VertexLabel (s := s) (arity := arity)
abbrev E := LocalAffineLabels.EdgeLabel (b := b)
abbrev vertexCount := Fintype.card (V (s := s) (arity := arity))
abbrev edgeCount := Fintype.card (E (b := b))
def vertexEquiv := Fintype.equivFin (V (s := s) (arity := arity))
def edgeEquiv := Fintype.equivFin (E (b := b))
def vertexCode (a : V (s := s) (arity := arity)) := (vertexEquiv a).val
def edgeCode (a : E (b := b)) := (edgeEquiv a).val

def targetArity (k : ℕ) : ℕ :=
  if h : k < vertexCount (s := s) (arity := arity) then
    arity ((vertexEquiv.symm ⟨k, h⟩).1.val) else 0

@[simp] theorem arity_index (i : Fin (vertexCount (s := s) (arity := arity))) :
    targetArity (s := s) (arity := arity) i.val = arity ((vertexEquiv.symm i).1.val) := by simp only [targetArity, dif_pos i.isLt]

@[simp] theorem arity_code (a : V (s := s) (arity := arity)) :
    targetArity (s := s) (arity := arity) (vertexCode a) = arity a.1.val := by simp [vertexCode]

def transport {m n : ℕ} (h : m = n) (f : Signature AlgebraicComplex m) : Signature AlgebraicComplex n :=
  fun x => f (fun j => x (Fin.cast h j))

theorem transport_affine {m n : ℕ} (h : m = n) {f : Signature AlgebraicComplex m} (hf : Affine f) :
    Affine (transport h f) := by
  cases h
  change Affine (fun x => f (fun j => x j))
  exact hf

variable (D : LocalAffineLabels.Family s b arity)

def family : AffineMachine.Assembly.Family (vertexCount (s := s) (arity := arity))
    (edgeCount (b := b)) (targetArity (s := s) (arity := arity)) where
  signatures i := transport (arity_index i).symm (LocalAffineLabels.vertex D (vertexEquiv.symm i))
  kernels i u v := LocalAffineLabels.edge D (edgeEquiv.symm i) ![u, v]
  vertexAffine i := transport_affine _ (LocalAffineLabels.vertex_affine D _)
  edgeAffine i := by
    have he : (fun x : Word 2 => LocalAffineLabels.edge D (edgeEquiv.symm i) ![x 0, x 1]) =
        LocalAffineLabels.edge D (edgeEquiv.symm i) := by
      funext x; congr 1; funext j; fin_cases j <;> rfl
    rw [he]
    exact LocalAffineLabels.edge_affine D _

theorem vertex_value (a : V (s := s) (arity := arity))
    (x : Word (targetArity (s := s) (arity := arity) (vertexCode a))) :
    (family D).signatures (vertexEquiv a) x =
      LocalAffineLabels.vertex D a (fun j => x (Fin.cast (arity_code a).symm j)) := by
  have hv : ∀ (c : V (s := s) (arity := arity)), c = a →
      ∀ he : arity c.1.val = targetArity (s := s) (arity := arity) (vertexCode a),
      LocalAffineLabels.vertex D c (fun j => x (Fin.cast he j)) =
        LocalAffineLabels.vertex D a (fun j => x (Fin.cast (arity_code a).symm j)) := by
    intro c hc he
    subst c
    rfl
  exact hv (vertexEquiv.symm (vertexEquiv a)) (vertexEquiv.symm_apply_apply a) _

theorem lookup_arity (i : Fin (vertexCount (s := s) (arity := arity)))
    (a : V (s := s) (arity := arity)) (hi : i = vertexEquiv a) :
    arity a.1.val = targetArity (s := s) (arity := arity) i.val := by
  subst i
  exact (arity_code a).symm

/-- Transport at an arbitrary encoded finite index, avoiding an invalid
dependent rewrite of the assignment word when the label is identified. -/
theorem vertex_lookup (i : Fin (vertexCount (s := s) (arity := arity)))
    (a : V (s := s) (arity := arity)) (hi : i = vertexEquiv a)
    (x : Word (targetArity (s := s) (arity := arity) i.val)) :
    (family D).signatures i x = LocalAffineLabels.vertex D a (fun j => x (Fin.cast (lookup_arity i a hi) j)) := by
  subst i
  exact vertex_value D a x

theorem edge_value (a : E (b := b)) (u v : Bool) :
    (family D).kernels (edgeEquiv a) u v = LocalAffineLabels.edge D a ![u, v] := by
  simp [family]

end
end Holant.LocalDrafts.Tractability.LocalAffineMachine.Relabel.Catalogue
