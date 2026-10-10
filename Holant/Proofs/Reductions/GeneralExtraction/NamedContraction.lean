import Holant.NetworkContraction
import Holant.NetworkTensor
import Holant.Proofs.BinaryInterpolation.SingularExtraction.PairDescent


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
set_option backward.isDefEq.respectTransparency false
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.Certificates.MatchingContractionClosure

variable {K P Q : Type*} {n m : ℕ}

def Uses (N : Network K n) (F : SignatureFamily K) : Prop :=
  ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature K) ∈ F

def Native [Semiring K] (N : Network K n) : Prop :=
  ∀ e, N.edge e = Signature.disequality

def reboundary (N : Network K n) (e : Fin n ≃ Fin m) : Network K m where
  shape := { N.shape with
    ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

variable [Field K]

theorem reboundary_denote (N : Network K n) (e : Fin n ≃ Fin m) (x : Fin m → Bool) :
    (reboundary N e).denote x = N.denote (fun i => x (e i)) := by
  classical
  unfold Network.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    apply congrArg (N.vertex v)
    funext i
    change Sum.elim x z ((Equiv.sumCongr e (Equiv.refl _)) (N.shape.ports ⟨v, i⟩)) = _
    unfold NetworkShape.assignment
    cases N.shape.ports ⟨v, i⟩ <;> rfl
  · rfl

structure Named (K P : Type*) where
  arity : ℕ
  boundary : P ≃ Fin arity
  graph : Network K arity

def Named.denote (N : Named K P) : Tensor K P :=
  fun x => N.graph.denote (fun i => x (N.boundary.symm i))

def ofNetwork (N : Network K n) : Named K (Fin n) := ⟨n, Equiv.refl _, N⟩

def Named.close [Fintype P] [DecidableEq P] (N : Named K P)
    (i j : P) (hij : i ≠ j) : Named K (Remaining i j) :=
  let r := Fintype.equivFin (Remaining i j)
  ⟨Fintype.card (Remaining i j), r,
    (reboundary N.graph (N.boundary.symm.trans (pairOrder i j hij r).symm)).contract
      Signature.disequality⟩

/-- Denotation follows from the actual reclassified ports and the actual new
edge, not from an assumed equation for the requested output signature. -/
theorem Named.close_denote [Fintype P] [DecidableEq P] (N : Named K P)
    (i j : P) (hij : i ≠ j) :
    (N.close i j hij).denote = contractPair i j Signature.disequality N.denote := by
  let r := Fintype.equivFin (Remaining i j)
  have h := contractPair_ordered i j hij r N.denote
  funext x
  have he := congrFun h (fun a => x (r.symm a))
  simpa only [Named.close, Named.denote, Network.denote_contract,
    Signature.contract, reboundary_denote, Tensor.reindex,
    Equiv.trans_apply, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using he.symm

@[simp] theorem Named.close_vertices [Fintype P] [DecidableEq P] (N : Named K P)
    (i j : P) (hij : i ≠ j) :
    (N.close i j hij).graph.shape.vertices = N.graph.shape.vertices := rfl

theorem Named.close_uses [Fintype P] [DecidableEq P] (N : Named K P)
    (i j : P) (hij : i ≠ j) (F : SignatureFamily K) (h : Uses N.graph F) :
    Uses (N.close i j hij).graph F := h

theorem Named.close_native [Fintype P] [DecidableEq P] (N : Named K P)
    (i j : P) (hij : i ≠ j) (h : Native N.graph) :
    Native (N.close i j hij).graph := by
  intro e
  refine Fin.cases ?_ (fun e => ?_) e
  · rfl
  · exact h e

theorem Named.card [Fintype P] (N : Named K P) : Fintype.card P = N.arity := by
  simpa using Fintype.card_congr N.boundary

theorem Named.constant (N : Named K P) (b : Bool) :
    N.denote (fun _ => b) = N.graph.denote (fun _ => b) := rfl

end Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
