import Holant.ReedMuller.FlatNetwork.GenerationNetworkLifts
import Holant.NetworkAsGadget

/-! Uniform conversion to the repository's native-X gadget convention.
Every old I/X edge becomes one actual I/X binary vertex and two native X
edges. Old vertices, all local port orders and boundary incidence are retained. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {n : ℕ}

def nativeFamily : SignatureFamily ℂ := {f |
  f = ⟨2, fun x => Signature.equality (x 0) (x 1)⟩ ∨
  f = ⟨2, fun x => Signature.disequality (x 0) (x 1)⟩ ∨ f = ⟨8, rmCore⟩}

def subdivisionPorts (E : Type*) (n : ℕ) :
    ((Fin n ⊕ (E × Bool)) ⊕ (E × Bool)) ≃ (Fin n ⊕ ((E × Bool) × Bool)) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr q) => .inr (q,false)
    | .inr q => .inr (q,true)
  invFun
    | .inl i => .inl (.inl i)
    | .inr (q,false) => .inl (.inr q)
    | .inr (q,true) => .inr q
  left_inv := by rintro ((i | q) | q) <;> rfl
  right_inv := by rintro (i | ⟨q,b⟩); rfl; cases b <;> rfl

def subdivisionVertexPorts (N : Network ℂ n) :
    (Σ v : Fin N.shape.vertices ⊕ Fin N.shape.edges,
      Fin (Sum.elim N.shape.arity (fun _ => 2) v)) ≃
      ((Σ v : Fin N.shape.vertices, Fin (N.shape.arity v)) ⊕ (Fin N.shape.edges × Bool)) where
  toFun
    | ⟨.inl v,i⟩ => .inl ⟨v,i⟩
    | ⟨.inr e,i⟩ => .inr (e,finTwoEquiv i)
  invFun
    | .inl ⟨v,i⟩ => ⟨.inl v,i⟩
    | .inr (e,b) => ⟨.inr e,finTwoEquiv.symm b⟩
  left_inv := by rintro ⟨v | e,i⟩; rfl; simp
  right_inv := by rintro (⟨v,i⟩ | ⟨e,b⟩); rfl; simp

def subdivisionFinite (N : Network ℂ n) :
    FiniteNetwork ℂ (Fin N.shape.vertices ⊕ Fin N.shape.edges) (Fin N.shape.edges × Bool) n where
  arity := Sum.elim N.shape.arity (fun _ => 2)
  ports := (subdivisionVertexPorts N).trans
    ((Equiv.sumCongr N.shape.ports (Equiv.refl _)).trans (subdivisionPorts _ n))
  vertex := fun v => match v with
    | .inl v => N.vertex v
    | .inr e => fun x : Fin 2 → Bool => N.edge e (x 0) (x 1)
  edge := fun _ => Signature.disequality

def native (N : Network ℂ n) : Network ℂ n := (subdivisionFinite N).toNetwork

@[simp] theorem native_vertices (N : Network ℂ n) :
    (native N).shape.vertices = N.shape.vertices+N.shape.edges := by
  simp [native, FiniteNetwork.toNetwork]

@[simp] theorem native_edges (N : Network ℂ n) :
    (native N).shape.edges = 2*N.shape.edges := by
  simp [native, FiniteNetwork.toNetwork, Nat.mul_comm]

@[simp] theorem native_edge (N : Network ℂ n) (e : Fin (native N).shape.edges) :
    (native N).edge e = Signature.disequality := rfl

def subdivisionAssignments (E : Type*) :
    (((E × Bool) × Bool) → Bool) ≃ (((E × Bool) → Bool) × ((E × Bool) → Bool)) where
  toFun z := (fun q => z (q,false), fun q => z (q,true))
  invFun p q := if q.2 then p.2 q.1 else p.1 q.1
  left_inv := by intro z; funext q; rcases q with ⟨q,b⟩; cases b <;> rfl
  right_inv := fun _ => rfl

private theorem subdivision_old_assignment (N : Network ℂ n) (x : Fin n → Bool)
    (a b : (Fin N.shape.edges × Bool) → Bool) (v : Fin N.shape.vertices) :
    (fun i => Sum.elim x ((subdivisionAssignments (Fin N.shape.edges)).symm (a,b))
      ((subdivisionFinite N).ports ⟨.inl v,i⟩)) = N.shape.assignment x a v := by
  funext i
  dsimp [subdivisionFinite, subdivisionVertexPorts, NetworkShape.assignment]
  cases hp : N.shape.ports ⟨v,i⟩ <;>
    simp [Equiv.sumCongr_apply, hp, subdivisionPorts, subdivisionAssignments]

private theorem subdivision_new_assignment (N : Network ℂ n) (x : Fin n → Bool)
    (a b : (Fin N.shape.edges × Bool) → Bool) (e : Fin N.shape.edges) :
    (subdivisionFinite N).vertex (.inr e)
      (fun i => Sum.elim x ((subdivisionAssignments (Fin N.shape.edges)).symm (a,b))
        ((subdivisionFinite N).ports ⟨.inr e,i⟩)) = N.edge e (b (e,false)) (b (e,true)) := rfl

private theorem prod_disequality {ι : Type*} [Fintype ι] (a b : ι → Bool) :
    (∏ i, (Signature.disequality (a i) (b i) : ℂ)) =
      if b = (fun i => !(a i)) then 1 else 0 := by
  simp only [Signature.disequality, Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    exact Bool.eq_not_iff.mpr (Ne.symm (h i))
  · intro h i
    have hi := congrFun h i
    exact Ne.symm (Bool.eq_not_iff.mp hi)

theorem allowed_edge_complement (N : Network ℂ n) (hN : Allowed N)
    (e : Fin N.shape.edges) (a b : Bool) : N.edge e (!a) (!b) = N.edge e a b := by
  rcases hN.2 e with hi | hx
  · rw [hi]
    cases a <;> cases b <;> rfl
  · rw [hx]
    cases a <;> cases b <;> rfl

/-- Exact sum-product subdivision: the X edges force the new binary's bits
to be the complements of the old bits, and X E X = E for both I and X. -/
theorem denote_native (N : Network ℂ n) (hN : Allowed N) :
    (native N).denote = N.denote := by
  let : DecidableEq (Fin N.shape.edges × Bool) := Classical.decEq _
  funext x
  rw [native, FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  change (∑ z : ((Fin N.shape.edges × Bool) × Bool) → Bool,
    (∏ v, (subdivisionFinite N).vertex v (fun i => Sum.elim x z ((subdivisionFinite N).ports ⟨v,i⟩))) *
      ∏ e, (subdivisionFinite N).edge e (z (e,false)) (z (e,true))) = _
  rw [← (subdivisionAssignments (Fin N.shape.edges)).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, subdivision_old_assignment,
    subdivision_new_assignment]
  change (∑ a : (Fin N.shape.edges × Bool) → Bool, ∑ b : (Fin N.shape.edges × Bool) → Bool,
    ((∏ v, N.vertex v (N.shape.assignment x a v)) *
      (∏ e, N.edge e (b (e,false)) (b (e,true)))) *
      (∏ q, Signature.disequality (a q) (b q))) = _
  simp only [prod_disequality, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [allowed_edge_complement N hN]
  unfold Network.denote
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl

theorem native_vertex_mem (N : Network ℂ n) (hN : Allowed N)
    (v : Fin (native N).shape.vertices) :
    (⟨(native N).shape.arity v, (native N).vertex v⟩ : AnySignature ℂ) ∈ nativeFamily := by
  dsimp only [native, FiniteNetwork.toNetwork]
  cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.edges)).symm v with
  | inl v =>
    rcases hN.1 v with hi | hr
    · exact Or.inl hi
    · exact Or.inr (Or.inr hr)
  | inr e =>
    rcases hN.2 e with hi | hx
    · exact Or.inl (by simp [subdivisionFinite, hi])
    · exact Or.inr (Or.inl (by simp [subdivisionFinite, hx]))

/-- Downstream consumers get the standard actual-gadget predicate with only
native-X edges and explicit supplied I, X and RM vertex resources. -/
theorem realizes_native (N : Network ℂ n) (hN : Allowed N) :
    Gadget.Realizes nativeFamily .disequality N.denote := by
  rw [← denote_native N hN]
  exact Gadget.realizes_network (native N) nativeFamily .disequality
    (native_vertex_mem N hN) (fun _ => rfl)

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
