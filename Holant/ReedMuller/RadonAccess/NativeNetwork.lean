import Holant.ReedMuller.RadonAccess.ProgramNetwork

/-! Native-X subdivision for arbitrary supplied vertex signatures. Only the
literal I/X edge condition is needed for the denotation identity. -/
namespace Holant.ReedMuller.RadonAccess
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork GenerationNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

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

theorem edge_complement (N : Network ℂ n) (hN : EdgesIX N)
    (e : Fin N.shape.edges) (a b : Bool) : N.edge e (!a) (!b) = N.edge e a b := by
  rcases hN e with hi | hx
  · rw [hi]
    cases a <;> cases b <;> rfl
  · rw [hx]
    cases a <;> cases b <;> rfl

/-- Exact sum-product subdivision: the X edges force the new binary's bits
to be the complements of the old bits, and X E X = E for both I and X. -/
theorem native_denote_of_edges (N : Network ℂ n) (hN : EdgesIX N) :
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
  simp only [edge_complement N hN]
  unfold Network.denote
  apply Finset.sum_congr
  · ext a
    simp
  · intro a _
    rfl


theorem uses_native (F : SignatureFamily ℂ) (N : Network ℂ n) (hN : Uses F N)
    (hE : EdgesIX N)
    (hI : (⟨2,fun x => Signature.equality (x 0) (x 1)⟩ : AnySignature ℂ)∈F)
    (hX : (⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ : AnySignature ℂ)∈F) :
    Uses F (native N) := by
  intro v
  dsimp only [native,FiniteNetwork.toNetwork]
  cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Fin N.shape.edges)).symm v with
  | inl v => exact hN v
  | inr e =>
    change (⟨2,fun x => N.edge e (x 0) (x 1)⟩ : AnySignature ℂ)∈F
    rcases hE e with hi | hx
    · rw [hi];exact hI
    · rw [hx];exact hX

theorem realizes_native_of_uses (F : SignatureFamily ℂ) (N : Network ℂ n)
    (hN : Uses F N) (hE : EdgesIX N)
    (hI : (⟨2,fun x => Signature.equality (x 0) (x 1)⟩ : AnySignature ℂ)∈F)
    (hX : (⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ : AnySignature ℂ)∈F) :
    Gadget.Realizes F .disequality N.denote := by
  rw [←native_denote_of_edges N hE]
  exact Gadget.realizes_network (native N) F .disequality (uses_native F N hN hE hI hX)
    (fun _ => rfl)

end
end Holant.ReedMuller.RadonAccess
