import Holant.Certificates.NormalizedDihedralQ6.ContractionSupport
import Holant.NetworkContraction
import Holant.NetworkAsGadget

/-! A literal one-vertex, one-edge gadget for the A.11 contraction.
The original signature label and all six original local port IDs are retained;
only the external incidence order puts the chosen pair first. -/
namespace Holant.Certificates.NormalizedDihedralQ6
open Holant
set_option backward.isDefEq.respectTransparency false

variable {K : Type*}

def orderedCorolla (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) : Network K 6 where
  shape := {
    vertices := 1
    arity := fun _ => 6
    edges := 0
    ports := {
      toFun q := .inl ((orderedPorts p hp).symm q.2)
      invFun q := Sum.elim (fun i => ⟨0,orderedPorts p hp i⟩) (fun q => Fin.elim0 q.1) q
      left_inv q := by
        rcases q with ⟨v,i⟩
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        simp
      right_inv q := by
        cases q with
        | inl i => simp
        | inr q => exact Fin.elim0 q.1 } }
  vertex := fun _ => h
  edge := fun e => Fin.elim0 e

variable [CommSemiring K]

theorem orderedCorolla_denote (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) :
    (orderedCorolla h p hp).denote = Tensor.reindex (orderedPorts p hp).symm h := by
  funext x
  dsimp [Network.denote,orderedCorolla,NetworkShape.assignment]
  simp
  rfl

def contractionNetwork (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) : Network K 4 :=
  (orderedCorolla h p hp).contract (parityKernel γ)

theorem contractionNetwork_denote (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    (contractionNetwork h p hp γ).denote = contractAt h p hp γ := by
  rw [contractionNetwork,Network.denote_contract,orderedCorolla_denote]
  rfl

@[simp] theorem contractionNetwork_vertices (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    (contractionNetwork h p hp γ).shape.vertices = 1 := rfl
@[simp] theorem contractionNetwork_edges (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    (contractionNetwork h p hp γ).shape.edges = 1 := rfl
@[simp] theorem contractionNetwork_vertex (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (v : Fin 1) : (contractionNetwork h p hp γ).vertex v = h := rfl

/-- The physical loop ends are exactly the requested two original local port occurrences. -/
theorem contractionNetwork_endpoints (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    (contractionNetwork h p hp γ).shape.ports.symm (.inr ((0 : Fin 1),false)) = ⟨(0 : Fin 1),p.1⟩ ∧
    (contractionNetwork h p hp γ).shape.ports.symm (.inr ((0 : Fin 1),true)) = ⟨(0 : Fin 1),p.2⟩ := by
  constructor <;> rfl

theorem contractionNetwork_boundary (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool)
    (i : Fin 4) : (contractionNetwork h p hp γ).shape.ports.symm (.inl i) =
      ⟨(0 : Fin 1),(remainingEquiv p hp i).val⟩ := rfl

/-- Direct exact realization by h and the actual selected I/X structural kernel. -/
theorem contraction_realizes (h : Signature K 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    Gadget.Realizes ({⟨6,h⟩} : SignatureFamily K) (parityEdge γ) (contractAt h p hp γ) := by
  have hg := Gadget.realizes_network (contractionNetwork h p hp γ)
    ({⟨6,h⟩} : SignatureFamily K) (parityEdge γ)
    (by intro v; exact Set.mem_singleton _) (by intro e; change Fin 1 at e; have he : e = 0 := Subsingleton.elim _ _; subst e; rfl)
  rwa [contractionNetwork_denote] at hg

end Holant.Certificates.NormalizedDihedralQ6
