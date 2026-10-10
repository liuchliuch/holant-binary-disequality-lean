import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseMinimalRank

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparsePinTwist
open Holant Holant.Tractable
open OrdinaryNegativeSparseMinimalRank
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

def fixedProduct {M : Type*} [CommMonoid M] (p : Fin n→Bool ⊕ Fin m) (w : Bool→M) : M :=
  ∏b : Bool,∏_j∈Finset.univ.filter (fun j=>p j=Sum.inl b),w b

/-- Every exposed variable occurs at one and only one original port. -/
theorem product_pure {M : Type*} [CommMonoid M] (p : Fin n→Bool ⊕ Fin m)
    (hp : PurePins p) (w : Bool→M) (x : Fin m→Bool) :
    (∏j : Fin n,w (T.substitute p x j))=fixedProduct p w*∏i : Fin m,w (x i) := by
  classical
  have hf (i : Fin m) : (∏j∈Finset.univ.filter (fun j=>p j=Sum.inr i),w (x i))=w (x i) := by
    obtain ⟨j,hj,unique⟩ := hp i
    have he : Finset.univ.filter (fun j=>p j=Sum.inr i)={j} := by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      exact ⟨unique a,fun h=>h ▸ hj⟩
    rw [he,Finset.prod_singleton]
  have h := Finset.prod_fiberwise' (Finset.univ : Finset (Fin n)) p
    (fun s : Bool ⊕ Fin m=>Sum.elim w (fun i=>w (x i)) s)
  rw [Fintype.prod_sum_type] at h
  simp only [Sum.elim_inl,Sum.elim_inr,hf] at h
  calc
    _=∏j : Fin n,Sum.elim w (fun i=>w (x i)) (p j) := by
      apply Finset.prod_congr rfl
      intro j _
      cases hj : p j <;> simp [T.substitute,hj]
    _=_ := h.symm

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparsePinTwist
end
