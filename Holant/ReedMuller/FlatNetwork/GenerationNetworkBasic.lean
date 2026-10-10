import Holant.ReedMuller.FlatNetwork.Generation
import Holant.ReedMuller.FlatNetwork.Primitives
import Holant.NetworkTensor
import Holant.NetworkContraction

/-! Literal boundary relabelling and the initial disjoint adjacent I pairs.
These constructions preserve the supplied vertex signatures and all edge data. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {K : Type*} {n m : ℕ}

/-- Only change the boundary incidence order; every local port stays fixed. -/
def reindex (N : Network K n) (e : Fin n ≃ Fin m) : Network K m where
  shape := {
    vertices := N.shape.vertices
    arity := N.shape.arity
    edges := N.shape.edges
    ports := N.shape.ports.trans (Equiv.sumCongr e (Equiv.refl _)) }
  vertex := N.vertex
  edge := N.edge

@[simp] theorem reindex_vertices (N : Network K n) (e : Fin n ≃ Fin m) :
    (reindex N e).shape.vertices = N.shape.vertices := rfl
@[simp] theorem reindex_edges (N : Network K n) (e : Fin n ≃ Fin m) :
    (reindex N e).shape.edges = N.shape.edges := rfl

theorem denote_reindex [CommSemiring K] (N : Network K n) (e : Fin n ≃ Fin m) :
    (reindex N e).denote = Tensor.reindex e N.denote := by
  funext x
  unfold Network.denote Tensor.reindex
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·) ?_ rfl
  apply Finset.prod_congr rfl
  intro v _
  congr 1
  funext i
  change Sum.elim x z ((Equiv.sumCongr e (Equiv.refl _)) (N.shape.ports ⟨v,i⟩)) =
    Sum.elim (fun j => x (e j)) z (N.shape.ports ⟨v,i⟩)
  cases N.shape.ports ⟨v,i⟩ <;> rfl

/-- Predicate recording the literal allowed resources. -/
def Allowed (N : Network ℂ n) : Prop :=
  (∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature ℂ) = ⟨2, fun x => Signature.equality (x 0) (x 1)⟩ ∨
    (⟨N.shape.arity v, N.vertex v⟩ : AnySignature ℂ) = ⟨8, rmCore⟩) ∧
  ∀ e, N.edge e = Signature.equality ∨ N.edge e = Signature.disequality

theorem allowed_reindex (N : Network ℂ n) (e : Fin n ≃ Fin m) (hN : Allowed N) :
    Allowed (reindex N e) := hN

/-- Coordinates of an added pair precede all old boundary coordinates. -/
def prependPairEquiv (n : ℕ) : Fin (2+n) ≃ Fin (n+2) := finCongr (Nat.add_comm 2 n)

def prependPair (N : Network ℂ n) : Network ℂ (n+2) :=
  reindex ((Network.corolla (fun x : Fin 2 → Bool => Signature.equality (x 0) (x 1))).tensor N)
    (prependPairEquiv n)

@[simp] theorem prependPair_vertices (N : Network ℂ n) :
    (prependPair N).shape.vertices = N.shape.vertices+1 := by
  simp [prependPair, Network.corolla, Nat.add_comm]
@[simp] theorem prependPair_edges (N : Network ℂ n) :
    (prependPair N).shape.edges = N.shape.edges := by
  simp [prependPair, Network.corolla]

theorem denote_prependPair (N : Network ℂ n) (x : Fin (n+2) → Bool) :
    (prependPair N).denote x = Signature.equality (x 0) (x 1) *
      N.denote (fun i => x i.succ.succ) := by
  rw [prependPair, denote_reindex]
  simp only [Tensor.reindex, Network.denote_tensor, Signature.tensor_apply, Network.denote_corolla]
  congr 1
  congr 1
  funext i
  congr 1
  apply Fin.ext
  simp [prependPairEquiv]

theorem allowed_tensor (L : Network ℂ n) (R : Network ℂ m)
    (hL : Allowed L) (hR : Allowed R) : Allowed (L.tensor R) := by
  constructor
  · intro v
    dsimp only [Network.tensor, FiniteNetwork.toNetwork]
    cases (Fintype.equivFin (Fin L.shape.vertices ⊕ Fin R.shape.vertices)).symm v with
    | inl v => exact hL.1 v
    | inr v => exact hR.1 v
  · intro e
    dsimp only [Network.tensor, FiniteNetwork.toNetwork]
    cases (Fintype.equivFin (Fin L.shape.edges ⊕ Fin R.shape.edges)).symm e with
    | inl e => exact hL.2 e
    | inr e => exact hR.2 e

theorem allowed_prependPair (N : Network ℂ n) (hN : Allowed N) : Allowed (prependPair N) := by
  apply allowed_reindex
  apply allowed_tensor _ _ ?_ hN
  exact ⟨fun _ => Or.inl rfl, fun e => Fin.elim0 e⟩

theorem flat_zero_value (D : BinaryCode n) (x : Fin n → Bool) :
    flatSignature 1 0 D x = if vectorWord x ∈ D then 1 else 0 := by
  simp only [flatSignature, sub_zero, Pi.zero_apply, Units.val_one]
  rfl

/-- The empty graph followed by actual disjoint I vertices. The irrelevant
odd branch only makes the family total; resource claims require even arity. -/
def initial : (n : ℕ) → Network ℂ n
  | 0 => Network.empty
  | 1 => Network.corolla (flatSignature 1 0 (⊥ : BinaryCode 1))
  | n+2 => prependPair (initial n)

theorem denote_initial (n : ℕ) : (initial n).denote = flatSignature 1 0 (standardPairs n) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    funext x
    rw [flat_zero_value]
    have hx : vectorWord x = (0 : BinaryVector 0) := Subsingleton.elim _ _
    simp [initial, standardPairs, hx]
  | one => exact Network.denote_corolla _
  | more n ih _ =>
    funext x
    rw [initial, denote_prependPair, ih, flat_zero_value, flat_zero_value]
    change Signature.equality (x 0) (x 1) *
      (if vectorWord (fun i => x i.succ.succ) ∈ standardPairs n then 1 else 0) =
      if vectorWord x ∈ pairExtension (standardPairs n) then 1 else 0
    rw [mem_pairExtension]
    have he : vectorWord x 0 = vectorWord x 1 ↔ x 0 = x 1 := boolEquiv.apply_eq_iff_eq
    have ht : dropTwo (vectorWord x) = vectorWord (fun i => x i.succ.succ) := rfl
    rw [he, ht]
    by_cases h : x 0 = x 1 <;>
      by_cases hp : vectorWord (fun i => x i.succ.succ) ∈ standardPairs n <;>
      simp [Signature.equality, h, hp]

theorem initial_edges (n : ℕ) : (initial n).shape.edges = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih _ => simpa only [initial, prependPair_edges] using ih

theorem initial_vertices (n : ℕ) (hn : Even n) : (initial n).shape.vertices = n / 2 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => obtain ⟨a, ha⟩ := hn; omega
  | more n ih _ =>
    have he : Even n := by obtain ⟨a, ha⟩ := hn; exact even_iff_two_dvd.mpr (by omega)
    rw [initial, prependPair_vertices, ih he]
    omega

theorem allowed_initial (n : ℕ) (hn : Even n) : Allowed (initial n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨fun v => Fin.elim0 v, fun e => Fin.elim0 e⟩
  | one => obtain ⟨a, ha⟩ := hn; omega
  | more n ih _ =>
    have he : Even n := by obtain ⟨a, ha⟩ := hn; exact even_iff_two_dvd.mpr (by omega)
    exact allowed_prependPair _ (ih he)

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
