import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberCoordinates
import Holant.Tensor

/-! A constant original edge label exposes a genuine tensor factor over a
nontrivial partition of the original ports, with both factors nonzero. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
open scoped BigOperators
open Holant.Certificates.MatchingContractionClosure
namespace Fiber

def HasProperTensorFactor {P : Type*} (h : Tensor ℂ P) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ ports : (Fin m ⊕ Fin n) ≃ P,
    ∃ f : Signature ℂ m, ∃ g : Signature ℂ n,
      f ≠ 0 ∧ g ≠ 0 ∧ h = Tensor.reindex ports (Tensor.tensor f g)

theorem factor_of_split {P A B : Type*} [Fintype A] [Fintype B]
    (ports : (A ⊕ B) ≃ P) (f : Tensor ℂ A) (g : Tensor ℂ B) (h : Tensor ℂ P)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B) (hn : h ≠ 0)
    (he : h = Tensor.reindex ports (Tensor.tensor f g)) : HasProperTensorFactor h := by
  let eA := (Fintype.equivFin A).symm
  let eB := (Fintype.equivFin B).symm
  let p := (Equiv.sumCongr eA eB).trans ports
  let f' := Tensor.reindex eA.symm f
  let g' := Tensor.reindex eB.symm g
  have hh : h = Tensor.reindex p (Tensor.tensor f' g') := by
    rw [he]
    funext x
    simp only [p,f',g',Tensor.reindex,Tensor.tensor,Equiv.trans_apply,Equiv.sumCongr_apply,
      Sum.map_inl,Sum.map_inr,Equiv.apply_symm_apply]
  refine ⟨_,_,hA,hB,p,f',g',?_,?_,hh⟩
  · intro hz
    apply hn
    rw [hh,hz]
    funext x
    simp [Tensor.reindex,Tensor.tensor]
  · intro hz
    apply hn
    rw [hh,hz]
    funext x
    simp [Tensor.reindex,Tensor.tensor]

def splitEdge {r : ℕ} (e : Fin r) : (Bool ⊕ (OtherEdges e × Bool)) ≃ (Fin r × Bool) where
  toFun := Sum.elim (fun b => (e,b)) (fun db => (db.1.val,db.2))
  invFun jb := if h : jb.1 = e then .inl jb.2 else .inr (⟨jb.1,h⟩,jb.2)
  left_inv x := by
    cases x with
    | inl b => simp
    | inr db => simp [db.1.property]
  right_inv jb := by
    dsimp only
    split_ifs with h
    · exact Prod.ext h.symm rfl
    · rfl

def edgeRemainder {r : ℕ} (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r) :
    Tensor ℂ (OtherEdges e × Bool) :=
  fun x => ∑ a, weight a*∏ d : OtherEdges e, E (labels a d.val) (x (d,false)) (x (d,true))

theorem constant_edge_split {P : Type*} {r : ℕ} (M : Matching P r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r) (b : Label)
    (hlabel : ∀ a, weight a ≠ 0 → labels a e = b) :
    tensor M weight labels = Tensor.reindex ((splitEdge e).trans M.ports)
      (Tensor.tensor (fun x : Bool → Bool => E b (x false) (x true)) (edgeRemainder weight labels e)) := by
  classical
  funext x
  change (∑ a, weight a*M.tensor (labels a) x) =
    E b (x (M.ports (e,false))) (x (M.ports (e,true))) *
      ∑ a, weight a*∏ d : OtherEdges e,
        E (labels a d.val) (x (M.ports (d.val,false))) (x (M.ports (d.val,true)))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hw : weight a = 0
  · simp only [hw,zero_mul,mul_zero]
  · rw [Matching.tensor,Fintype.prod_eq_mul_prod_compl e,hlabel a hw]
    rw [Finset.prod_subtype (p := fun d : Fin r => d ≠ e) {e}ᶜ (by intro d; simp)]
    ring

theorem constant_edge_factor {P : Type*} {r : ℕ} (M : Matching P r) (hr : 2 ≤ r)
    (weight : Label → ℂ) (labels : Label → Fin r → Label) (e : Fin r) (b : Label)
    (hn : tensor M weight labels ≠ 0) (hlabel : ∀ a, weight a ≠ 0 → labels a e = b) :
    HasProperTensorFactor (tensor M weight labels) := by
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.mpr hr
  obtain ⟨j,hj⟩ := exists_ne e
  apply factor_of_split ((splitEdge e).trans M.ports)
    (fun x : Bool → Bool => E b (x false) (x true)) (edgeRemainder weight labels e)
    (tensor M weight labels) (by decide) _ hn (constant_edge_split M weight labels e b hlabel)
  exact Fintype.card_pos_iff.mpr ⟨(⟨j,hj⟩,false)⟩

theorem factor_reindex_iff {P Q : Type*} (e : P ≃ Q) (h : Tensor ℂ P) :
    HasProperTensorFactor (Tensor.reindex e h) ↔ HasProperTensorFactor h := by
  constructor
  · rintro ⟨m,n,hm,hn,ports,f,g,hf,hg,he⟩
    refine ⟨m,n,hm,hn,ports.trans e.symm,f,g,hf,hg,?_⟩
    have hh := congrArg (Tensor.reindex e.symm) he
    simpa only [Tensor.reindex_trans,Equiv.self_trans_symm,Tensor.reindex_refl] using hh
  · rintro ⟨m,n,hm,hn,ports,f,g,hf,hg,he⟩
    exact ⟨m,n,hm,hn,ports.trans e,f,g,hf,hg,congrArg (Tensor.reindex e) he⟩

end Fiber
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
