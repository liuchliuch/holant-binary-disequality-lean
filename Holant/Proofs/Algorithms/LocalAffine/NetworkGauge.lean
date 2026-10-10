import Holant.Proofs.Algorithms.LocalAffine.Twists
import Holant.ChargeConservation
import Holant.Tractable.CommonTransform


namespace Holant.LocalDrafts.MainChain.LocalAffineNetwork
open Holant.Tractable LocalAffineTwists
noncomputable section

variable (G : Network AlgebraicComplex 0)

def vertexReference (z : (Fin G.shape.edges × Bool) → Bool) (v : Fin G.shape.vertices) :=
  G.shape.assignment Fin.elim0 z v

def edgeReference (z : (Fin G.shape.edges × Bool) → Bool) (e : Fin G.shape.edges) : Fin 2 → Bool :=
  ![z (e,false),z (e,true)]

def gauged (reference : (Fin G.shape.edges × Bool) → Bool) : Network AlgebraicComplex 0 where
  shape := G.shape
  vertex v := inverseTwist (vertexReference G reference v) (G.vertex v)
  edge e u v := localTwist (edgeReference G reference e) (kernelSignature (G.edge e)) ![u,v]

theorem phase_balance (reference z : (Fin G.shape.edges × Bool) → Bool) :
    (∏ v, phaseWeight (vertexReference G reference v) (G.shape.assignment Fin.elim0 z v)) =
      ∏ e, phaseWeight (edgeReference G reference e) (edgeReference G z e) := by
  unfold phaseWeight vertexReference edgeReference
  simp only [NetworkShape.assignment_closed]
  rw [NetworkShape.prod_closedPorts G.shape
    (fun p => if reference p && z p then zetaEight else 1)]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro e _
  cases hrf : reference (e,false) <;> cases hrt : reference (e,true) <;>
    cases hzf : z (e,false) <;> cases hzt : z (e,true) <;>
    simp [Fintype.prod_bool,Fin.prod_univ_succ,hrf,hrt,hzf,hzt]

/-- Each original port occurs once in a vertex and once in an edge tensor.
The opposite local phase choices therefore cancel term by term, including
loops, repeated edges, zero terms and disconnected/nullary components. -/
theorem term_gauged (reference z : (Fin G.shape.edges × Bool) → Bool) :
    (gauged G reference).assignmentTerm Fin.elim0 z = G.assignmentTerm Fin.elim0 z := by
  simp only [Network.assignmentTerm,gauged,inverseTwist,localTwist_formula,
    kernelSignature,Matrix.cons_val_zero,Matrix.cons_val_one,Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  change
    ((∏ v, phaseWeight (vertexReference G reference v) (G.shape.assignment Fin.elim0 z v))⁻¹ *
      (∏ v, G.vertex v (G.shape.assignment Fin.elim0 z v))) *
      ((∏ e, phaseWeight (edgeReference G reference e) (edgeReference G z e)) *
        ∏ e, G.edge e (z (e,false)) (z (e,true))) = _
  rw [←phase_balance]
  have hn : (∏ v, phaseWeight (vertexReference G reference v)
      (G.shape.assignment Fin.elim0 z v)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun v _ => phaseWeight_ne_zero _ _)
  calc
    _ = ((∏ v, phaseWeight (vertexReference G reference v)
          (G.shape.assignment Fin.elim0 z v))⁻¹ *
        (∏ v, phaseWeight (vertexReference G reference v)
          (G.shape.assignment Fin.elim0 z v))) *
        ((∏ v, G.vertex v (G.shape.assignment Fin.elim0 z v)) *
          ∏ e, G.edge e (z (e,false)) (z (e,true))) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hn,one_mul]

theorem denote_gauged (reference : (Fin G.shape.edges × Bool) → Bool) :
    (gauged G reference).denote Fin.elim0=G.denote Fin.elim0 := by
  change (∑ z, (gauged G reference).assignmentTerm Fin.elim0 z) =
    ∑ z, G.assignmentTerm Fin.elim0 z
  apply Finset.sum_congr rfl
  intro z _
  exact term_gauged G reference z

theorem gauged_vertices_affine
    (hvertex : ∀ v, LocalAffine (G.vertex v))
    (reference : (Fin G.shape.edges × Bool) → Bool)
    (href : G.assignmentTerm Fin.elim0 reference ≠ 0) :
    ∀ v, Affine ((gauged G reference).vertex v) := by
  intro v
  exact inverseTwist_affine _ (hvertex v) _
    (G.vertex_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 reference href v)

theorem gauged_edges_affine
    (hedge : ∀ e, LocalAffine (kernelSignature (G.edge e)))
    (reference : (Fin G.shape.edges × Bool) → Bool)
    (href : G.assignmentTerm Fin.elim0 reference ≠ 0) :
    ∀ e, Affine (kernelSignature ((gauged G reference).edge e)) := by
  intro e
  have he : kernelSignature ((gauged G reference).edge e) =
      localTwist (edgeReference G reference e) (kernelSignature (G.edge e)) := by
    funext x
    change localTwist _ _ ![x 0,x 1]=localTwist _ _ x
    congr 1
    funext j
    fin_cases j <;> rfl
  rw [he]
  apply hedge e
  exact G.edge_ne_zero_of_assignmentTerm_ne_zero Fin.elim0 reference href e

/-- This semantic existence split is intentionally not called an algorithm.
The remaining implementation must solve the explicit global GF(2) support
system and emit the selected finite twist labels on the original raw graph. -/
theorem zero_or_affine_gauge
    (hvertex : ∀ v, LocalAffine (G.vertex v))
    (hedge : ∀ e, LocalAffine (kernelSignature (G.edge e))) :
    G.denote Fin.elim0=0 ∨
      ∃ reference : (Fin G.shape.edges × Bool) → Bool,
        G.assignmentTerm Fin.elim0 reference ≠ 0 ∧
        (gauged G reference).denote Fin.elim0=G.denote Fin.elim0 ∧
        (∀ v, Affine ((gauged G reference).vertex v)) ∧
        ∀ e, Affine (kernelSignature ((gauged G reference).edge e)) := by
  classical
  by_cases h : ∃ reference, G.assignmentTerm Fin.elim0 reference ≠ 0
  · obtain ⟨reference,href⟩ := h
    exact Or.inr ⟨reference,href,denote_gauged G reference,
      gauged_vertices_affine G hvertex reference href,gauged_edges_affine G hedge reference href⟩
  · left
    push_neg at h
    change (∑ z, G.assignmentTerm Fin.elim0 z)=0
    exact Finset.sum_eq_zero (fun z _ => h z)

end
end Holant.LocalDrafts.MainChain.LocalAffineNetwork
