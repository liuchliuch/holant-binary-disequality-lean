import Holant.OpenNetworkComposition.Semantics
import Holant.NetworkGluing.Finite
import Mathlib.Logic.Equiv.Sum

/-! Every finite open network without free stubs is an ordinary ordered-port
network. The proof partitions all original ports into boundary and edge ends
and compares the complete assignment sums. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.OrdinaryNormalization
variable {K V F E : Type*} {n : ℕ} [CommSemiring K]
variable [Fintype V] [Fintype F] [Fintype E] [IsEmpty F]
variable (M : OpenNetworkComposition.FiniteNetwork K V F E n)

def boundaryEnds : Fin n ⊕ (E × Bool) → Ports V F M.shape.arity :=
  Sum.elim M.shape.boundary M.shape.ends

theorem boundaryEnds_bijective : Function.Bijective (boundaryEnds M) := by
  constructor
  · intro a b hab
    cases a with
    | inl i =>
      cases b with
      | inl j => exact congrArg Sum.inl (M.shape.boundary.injective hab)
      | inr e =>
        change M.shape.boundary i=M.shape.ends e at hab
        cases hi : M.shape.boundary i with
        | inl p =>
          exact False.elim ((M.shape.ordinary_boundary_iff_unpaired p).mp ⟨i,hi⟩
            ⟨e,hab.symm.trans hi⟩)
        | inr f => exact isEmptyElim f
    | inr e =>
      cases b with
      | inl i =>
        change M.shape.ends e=M.shape.boundary i at hab
        cases hi : M.shape.boundary i with
        | inl p =>
          exact False.elim ((M.shape.ordinary_boundary_iff_unpaired p).mp ⟨i,hi⟩
            ⟨e,hab.trans hi⟩)
        | inr f => exact isEmptyElim f
      | inr f => exact congrArg Sum.inr (M.shape.ends.injective hab)
  · intro p
    cases p with
    | inr f => exact isEmptyElim f
    | inl p =>
      classical
      by_cases h : ∃ e,M.shape.ends e=.inl p
      · obtain ⟨e,he⟩ := h
        exact ⟨.inr e,he⟩
      · obtain ⟨j,hj⟩ := (M.shape.ordinary_boundary_iff_unpaired p).mpr h
        exact ⟨.inl j,hj⟩

def partition : (Fin n ⊕ (E × Bool)) ≃ Ports V F M.shape.arity :=
  Equiv.ofBijective (boundaryEnds M) (boundaryEnds_bijective M)

@[simp] theorem partition_boundary (j : Fin n) :
    partition M (.inl j)=M.shape.boundary j := rfl
@[simp] theorem partition_ends (e : E × Bool) :
    partition M (.inr e)=M.shape.ends e := rfl

def ordinary : Holant.FiniteNetwork K V E n where
  arity := M.shape.arity
  ports := (Equiv.sumEmpty (Σ v,Fin (M.shape.arity v)) F).symm.trans (partition M).symm
  vertex := M.vertex
  edge e := (M.edge e).value

def assignments : (Ports V F M.shape.arity → Bool) ≃
    ((Fin n → Bool) × ((E × Bool) → Bool)) where
  toFun z := (fun j => z (M.shape.boundary j),fun e => z (M.shape.ends e))
  invFun p q := Sum.elim p.1 p.2 ((partition M).symm q)
  left_inv z := by
    funext q
    obtain ⟨q,rfl⟩ := (partition M).surjective q
    simp only [Equiv.symm_apply_apply]
    cases q <;> rfl
  right_inv p := by
    rcases p with ⟨x,z⟩
    apply Prod.ext <;> funext j
    · change Sum.elim x z ((partition M).symm ((partition M) (.inl j)))=x j
      simp only [Equiv.symm_apply_apply,Sum.elim_inl]
    · change Sum.elim x z ((partition M).symm ((partition M) (.inr j)))=z j
      simp only [Equiv.symm_apply_apply,Sum.elim_inr]

theorem weight_assignments (x : Fin n → Bool) (z : E × Bool → Bool) :
    M.weight ((assignments M).symm (x,z)) =
      (∏ v,M.vertex v (fun i => Sum.elim x z ((ordinary M).ports ⟨v,i⟩))) *
        ∏ e,(M.edge e).value (z (e,false)) (z (e,true)) := by
  unfold FiniteNetwork.weight
  apply congrArg₂ (·*·)
  · rfl
  · apply Finset.prod_congr rfl
    intro e _
    change (M.edge e).value
      (Sum.elim x z ((partition M).symm ((partition M) (.inr (e,false)))))
      (Sum.elim x z ((partition M).symm ((partition M) (.inr (e,true))))) = _
    simp only [Equiv.symm_apply_apply,Sum.elim_inr]

theorem ordinary_denote : (ordinary M).denote=M.tensor := by
  classical
  letI : DecidableEq F := Classical.decEq F
  have hk : M.boundaryKernel=fun _ => Signature.equality := by
    funext j
    cases h : M.shape.boundary j with
    | inl p => simp [FiniteNetwork.boundaryKernel,h]
    | inr f => exact isEmptyElim f
  rw [FiniteNetwork.tensor,hk,Signature.coordinateAction_equality]
  symm
  funext x
  unfold FiniteNetwork.raw
  trans ∑ yz : (Fin n → Bool) × (E × Bool → Bool),
    if ∀j,(assignments M).symm yz (M.shape.boundary j)=x j then
      M.weight ((assignments M).symm yz) else 0
  · apply Fintype.sum_equiv (assignments M)
    intro z
    simp only [Equiv.symm_apply_apply]
  rw [Fintype.sum_prod_type]
  have hb (y : Fin n → Bool) (z : E × Bool → Bool) :
      (∀ j,(assignments M).symm (y,z) (M.shape.boundary j)=x j) ↔ y=x := by
    change (∀ j,Sum.elim y z ((partition M).symm ((partition M) (.inl j)))=x j) ↔ _
    simp only [Equiv.symm_apply_apply,Sum.elim_inl,funext_iff]
  simp only [weight_assignments,hb]
  rw [Finset.sum_comm]
  simp
  rfl

theorem original_vertex (v : V) :
    (⟨(ordinary M).toNetwork.shape.arity ((Fintype.equivFin V) v),
      (ordinary M).toNetwork.vertex ((Fintype.equivFin V) v)⟩ : AnySignature K) =
      ⟨M.shape.arity v,M.vertex v⟩ := by
  exact congrArg (fun w : V => (⟨M.shape.arity w,M.vertex w⟩ : AnySignature K))
    ((Fintype.equivFin V).symm_apply_apply v)

theorem exists_ordinary_of_isEmpty (family : SignatureFamily K)
    (hv : ∀v,(⟨M.shape.arity v,M.vertex v⟩ : AnySignature K)∈family)
    (he : ∀e,M.edge e=.disequality) :
    ∃N : Network K n,
      (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature K)∈family) ∧
      (∀e,N.edge e=Signature.disequality) ∧ N.denote=M.tensor := by
  refine ⟨(ordinary M).toNetwork,?_,?_,?_⟩
  · intro v
    exact hv ((Fintype.equivFin V).symm v)
  · intro e
    change (M.edge ((Fintype.equivFin E).symm e)).value=Signature.disequality
    rw [he]
    rfl
  · rw [Holant.FiniteNetwork.denote_toNetwork]
    exact ordinary_denote M
end Holant.OpenNetworkComposition.OrdinaryNormalization
