import Holant.Proofs.Algorithms.LocalAffine.Reference
import Holant.Complexity.ClosedNetworkSemantics


set_option backward.isDefEq.respectTransparency false

namespace Holant.LocalDrafts.MainChain.LocalAffineLabels
open Holant.Tractable AffinePhase Holant.Complexity
open LocalAffineTwists
noncomputable section

structure Family (s b : ℕ) (arity : ℕ → ℕ) where
  signatures : (i : Fin s) → Signature AlgebraicComplex (arity i.val)
  kernels : Fin b → Bool → Bool → AlgebraicComplex
  vertexLocal : ∀ i, LocalAffine (signatures i)
  edgeLocal : ∀ i, LocalAffine (kernelSignature (kernels i))

variable {s b : ℕ} {arity : ℕ → ℕ} (D : Family s b arity)

abbrev VertexLabel := Σ i : Fin s, Word (arity i.val)
abbrev EdgeLabel := Fin b × Word 2

def vertex (a : VertexLabel (s:=s) (arity:=arity)) : Signature AlgebraicComplex (arity a.1.val) :=
  if D.signatures a.1 a.2 ≠ 0 then inverseTwist a.2 (D.signatures a.1) else 0

def edge (a : EdgeLabel (b:=b)) : Signature AlgebraicComplex 2 :=
  if kernelSignature (D.kernels a.1) a.2 ≠ 0 then
    localTwist a.2 (kernelSignature (D.kernels a.1)) else 0

theorem vertex_affine (a : VertexLabel (s:=s) (arity:=arity)) : Affine (vertex D a) := by
  unfold vertex
  split_ifs with h
  · exact inverseTwist_affine _ (D.vertexLocal a.1) a.2 h
  · exact affine_zero _

theorem edge_affine (a : EdgeLabel (b:=b)) : Affine (edge D a) := by
  unfold edge
  split_ifs with h
  · exact D.edgeLocal a.1 a.2 h
  · exact affine_zero _

theorem vertex_label_count : Fintype.card (VertexLabel (s:=s) (arity:=arity)) =
    ∑ i : Fin s, 2^(arity i.val) := by
  simp [VertexLabel,Word,Fintype.card_sigma,Fintype.card_fun]

theorem edge_label_count : Fintype.card (EdgeLabel (b:=b)) = 4*b := by
  simp [EdgeLabel,Word,Fintype.card_fun,Nat.mul_comm]

abbrev Input := {r : RawClosedNetwork // r.WellFormed s b arity}

def network (r : Input (s:=s) (b:=b) (arity:=arity)) : Network AlgebraicComplex 0 :=
  r.val.realize r.property D.signatures D.kernels

def vertexLabel (r : Input (s:=s) (b:=b) (arity:=arity))
    (z : (Fin r.val.edges.length × Bool) → Bool) (v : Fin r.val.vertices.length) :
    VertexLabel (s:=s) (arity:=arity) :=
  ⟨r.val.signatureLabel r.property v, (network D r).shape.assignment Fin.elim0 z v⟩

def edgeLabel (D : Family s b arity) (r : Input (s:=s) (b:=b) (arity:=arity))
    (z : (Fin r.val.edges.length × Bool) → Bool) (e : Fin r.val.edges.length) :
    EdgeLabel (b:=b) := ⟨r.val.edgeLabel r.property e, ![z (e,false),z (e,true)]⟩

def labelled (r : Input (s:=s) (b:=b) (arity:=arity))
    (z : (Fin r.val.edges.length × Bool) → Bool) : Network AlgebraicComplex 0 where
  shape := (network D r).shape
  vertex v := vertex D (vertexLabel D r z v)
  edge e u v := edge D (edgeLabel D r z e) ![u,v]

theorem labelled_eq_gauged (r : Input (s:=s) (b:=b) (arity:=arity))
    (z : (Fin r.val.edges.length × Bool) → Bool)
    (hz : (network D r).assignmentTerm Fin.elim0 z ≠ 0) :
    labelled D r z = LocalAffineNetwork.gauged (network D r) z := by
  have hv (v : Fin r.val.vertices.length) :=
    (network D r).vertex_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hz v
  have he (e : Fin r.val.edges.length) :=
    (network D r).edge_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 z hz e
  have hv' : (fun v => vertex D (vertexLabel D r z v)) =
      (fun v => inverseTwist (LocalAffineNetwork.vertexReference (network D r) z v)
        ((network D r).vertex v)) := by
    funext v
    simp only [vertex,vertexLabel]
    erw [if_pos (hv v)]
    rfl
  have he' : (fun e u v => edge D (edgeLabel D r z e) ![u,v]) =
      (fun e u v => localTwist (LocalAffineNetwork.edgeReference (network D r) z e)
        (kernelSignature ((network D r).edge e)) ![u,v]) := by
    funext e u v
    simp only [edge,edgeLabel]
    erw [if_pos (he e)]
    rfl
  unfold labelled LocalAffineNetwork.gauged
  erw [hv',he']

def reference (r : Input (s:=s) (b:=b) (arity:=arity)) :
    Option ((Fin r.val.edges.length × Bool) → Bool) :=
  LocalAffineReference.reference (network D r)
    (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
    (fun e => D.edgeLocal (r.val.edgeLabel r.property e))

theorem selected_correct (r : Input (s:=s) (b:=b) (arity:=arity)) :
    match reference D r with
    | none => (network D r).denote Fin.elim0 = 0
    | some z => (labelled D r z).denote Fin.elim0 = (network D r).denote Fin.elim0 := by
  cases h : reference D r with
  | none => exact LocalAffineReference.reference_none_zero _ _ _ h
  | some z =>
    dsimp only
    erw [labelled_eq_gauged D r z (LocalAffineReference.reference_supported (network D r)
      (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
      (fun e => D.edgeLocal (r.val.edgeLabel r.property e)) z h)]
    exact LocalAffineNetwork.denote_gauged _ _

/-- A constant derived from the finite source family, including zero-label
inconsistent rows. It is not an assumed polynomial bound. -/
def rowBudget : ℕ :=
  (∑ i, (LocalAffineSupport.localSystem (D.signatures i) (D.vertexLocal i)).rows) +
    ∑ i, (LocalAffineSupport.localSystem (kernelSignature (D.kernels i)) (D.edgeLocal i)).rows

theorem vertex_rows_le (i : Fin s) :
    (LocalAffineSupport.localSystem (D.signatures i) (D.vertexLocal i)).rows ≤ rowBudget D := by
  unfold rowBudget
  exact (Finset.single_le_sum (f := fun j => (LocalAffineSupport.localSystem (D.signatures j) (D.vertexLocal j)).rows) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (Nat.le_add_right _ _)

theorem edge_rows_le (i : Fin b) :
    (LocalAffineSupport.localSystem (kernelSignature (D.kernels i)) (D.edgeLocal i)).rows ≤
      rowBudget D := by
  unfold rowBudget
  exact (Finset.single_le_sum (f := fun j => (LocalAffineSupport.localSystem (kernelSignature (D.kernels j)) (D.edgeLocal j)).rows) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans
    (Nat.le_add_left _ _)

theorem global_rows_le (r : Input (s:=s) (b:=b) (arity:=arity)) :
    (LocalAffineSupport.global (network D r)
      (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
      (fun e => D.edgeLocal (r.val.edgeLabel r.property e))).rows ≤
      (r.val.vertices.length+r.val.edges.length)*rowBudget D := by
  rw [LocalAffineSupport.global_rows]
  have hv := Finset.sum_le_sum (s:=Finset.univ)
    (fun v _ => vertex_rows_le D (r.val.signatureLabel r.property v))
  have he := Finset.sum_le_sum (s:=Finset.univ)
    (fun e _ => edge_rows_le D (r.val.edgeLabel r.property e))
  change (∑ v, (LocalAffineSupport.localSystem (D.signatures (r.val.signatureLabel r.property v)) _).rows) +
    (∑ e, (LocalAffineSupport.localSystem (kernelSignature (D.kernels (r.val.edgeLabel r.property e))) _).rows) ≤ _
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, add_mul] using Nat.add_le_add hv he

end
end Holant.LocalDrafts.MainChain.LocalAffineLabels
