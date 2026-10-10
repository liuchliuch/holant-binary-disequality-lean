import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineFiberVariation


/-! Exact standard-Pauli eight-port label rigidity from actual cross cards. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingContractionClosure
open MatchingCard
namespace Fiber
variable {P : Type*} [Fintype P] [LinearOrder P]

def survivorIndex (i : Fin 4) (hi : i ≠ 2) : Fin (Fintype.card (OtherEdges (2 : Fin 4))) :=
  Fintype.equivFin (OtherEdges (2 : Fin 4)) ⟨i,hi⟩

theorem survivorIndex_injective (i j : Fin 4) (hi : i ≠ 2) (hj : j ≠ 2)
    (he : survivorIndex i hi = survivorIndex j hj) : i = j :=
  congrArg Subtype.val ((Fintype.equivFin (OtherEdges (2 : Fin 4))).injective he)

theorem fused_at_survivor (labels : Label → Fin 4 → Label) (a : Label) (i : Fin 4) (hi : i ≠ 2) :
    fusedLabels 1 2 0 labels a (survivorIndex i hi) =
      if i = 1 then labels a 1+labels a 2 else labels a i := by
  simp only [fusedLabels,survivorIndex,Equiv.symm_apply_apply,MatchingCard.spliceLabel,theta_zero,add_zero]

theorem fused_variation_obstruction (M : Matching P 4) (weight : Label → ℂ)
    (labels : Label → Fin 4 → Label) (hfirst : ∀ a, labels a 0 = a) (hw : ∀ a, weight a ≠ 0)
    (hthird : LabelVaries labels 3) (hfused : ∃ a b, labels a 1+labels a 2 ≠ labels b 1+labels b 2) :
    ¬ PairSafe (tensor M weight labels) := by
  intro hs
  let i₀ := survivorIndex 0 (by decide)
  let i₁ := survivorIndex 1 (by decide)
  let i₃ := survivorIndex 3 (by decide)
  have h01 : i₀ ≠ i₁ := fun h => (by decide : (0 : Fin 4) ≠ 1) (survivorIndex_injective _ _ _ _ h)
  have h03 : i₀ ≠ i₃ := fun h => (by decide : (0 : Fin 4) ≠ 3) (survivorIndex_injective _ _ _ _ h)
  have h13 : i₁ ≠ i₃ := fun h => (by decide : (1 : Fin 4) ≠ 3) (survivorIndex_injective _ _ _ _ h)
  have hlabel (a : Label) : fusedLabels 1 2 0 labels a i₀ = a := by
    rw [fused_at_survivor]
    exact hfirst a
  have hv₀ : LabelVaries (fusedLabels 1 2 0 labels) i₀ := by
    refine ⟨0,xLabel,?_⟩
    rw [hlabel,hlabel]
    decide
  have hv₁ : LabelVaries (fusedLabels 1 2 0 labels) i₁ := by
    obtain ⟨a,b,h⟩ := hfused
    refine ⟨a,b,?_⟩
    simpa only [i₁,fused_at_survivor,ite_true] using h
  have hv₃ : LabelVaries (fusedLabels 1 2 0 labels) i₃ := by
    obtain ⟨a,b,h⟩ := hthird
    refine ⟨a,b,?_⟩
    simpa only [i₃,fused_at_survivor,show (3 : Fin 4) ≠ 1 by decide,ite_false] using h
  have hwn (a : Label) : fusedWeight weight labels 1 2 0 a ≠ 0 :=
    fun h => hw a ((fusedWeight_zero_iff weight labels 1 2 0 a).mp h)
  have hnot := three_variable_edges_not_safe (fusedMatching M 1 2)
    (fusedWeight weight labels 1 2 0) (fusedLabels 1 2 0 labels) i₀ hlabel hwn
    i₀ i₁ i₃ h01 h03 h13 hv₀ hv₁ hv₃
  apply hnot
  have huv : M.ports (1,true) ≠ M.ports (2,false) := by
    intro h
    exact (by decide : (1 : Fin 4) ≠ 2) (congrArg Prod.fst (M.ports.injective h))
  have hh := hs _ _ huv 0
  rwa [contract_cross_fiber M weight labels 1 2 (by decide) 0] at hh

theorem permutation_varies (p : Equiv.Perm Label) : ∃ a b, p a ≠ p b := by
  refine ⟨p.symm 0,p.symm xLabel,?_⟩
  simp only [Equiv.apply_symm_apply]
  decide

/-- With four pairs, a safe four-term fiber can only fuse two label maps
when their pointwise sum is constant. This is the standard-Pauli alternative
to the exotic transpose obstruction. -/
theorem fused_sum_constant (M : Matching P 4) (weight : Label → ℂ)
    (perms : Fin 4 → Equiv.Perm Label) (hfirst : ∀a,perms 0 a=a)
    (hw : ∀a,weight a≠0) (safe : PairSafe (tensor M weight (fun a e=>perms e a))) :
    ∀a b,perms 1 a+perms 2 a=perms 1 b+perms 2 b := by
  intro a b
  by_contra different
  exact fused_variation_obstruction M weight (fun a e=>perms e a) hfirst hw
    (permutation_varies (perms 3)) ⟨a,b,different⟩ safe


def reenumerate (M : Matching P 4) (p : Equiv.Perm (Fin 4)) : Matching P 4 :=
  ⟨(Equiv.prodCongr p (Equiv.refl Bool)).trans M.ports⟩

theorem reenumerate_tensor (M : Matching P 4) (p : Equiv.Perm (Fin 4))
    (labels : Fin 4→Label) (x : P→Bool) :
    (reenumerate M p).tensor (fun e=>labels (p e)) x=M.tensor labels x := by
  change (∏e : Fin 4,E (labels (p e)) (x (M.ports (p e,false))) (x (M.ports (p e,true))))=_
  exact Equiv.prod_comp p (fun e=>E (labels e) (x (M.ports (e,false))) (x (M.ports (e,true))))

theorem tensor_change (M : Matching P 4) (p : Equiv.Perm (Fin 4))
    (weight : Label→ℂ) (perms : Fin 4→Equiv.Perm Label) (e : Equiv.Perm Label) :
    tensor (reenumerate M p) (fun a=>weight (e a)) (fun a i=>perms (p i) (e a))=
      tensor M weight (fun a i=>perms i a) := by
  funext x
  change (∑a,weight (e a)*(reenumerate M p).tensor (fun i=>perms (p i) (e a)) x)=
    ∑a,weight a*M.tensor (fun i=>perms i a) x
  calc
    _=∑a,weight (e a)*M.tensor (fun i=>perms i (e a)) x := by
      apply Finset.sum_congr rfl
      intro a _
      rw [reenumerate_tensor M p (fun i=>perms i (e a))]
    _=_ := Equiv.sum_comp e (fun a=>weight a*M.tensor (fun i=>perms i a) x)

theorem ordered_sum_constant (M : Matching P 4) (weight : Label→ℂ)
    (perms : Fin 4→Equiv.Perm Label) (hw : ∀a,weight a≠0)
    (safe : PairSafe (tensor M weight (fun a i=>perms i a)))
    (p : Equiv.Perm (Fin 4)) :
    ∀a b,perms (p 1) a+perms (p 2) a=perms (p 1) b+perms (p 2) b := by
  let e := (perms (p 0)).symm
  let q : Fin 4→Equiv.Perm Label := fun i=>e.trans (perms (p i))
  have first : ∀a,q 0 a=a := fun a=>(perms (p 0)).apply_symm_apply a
  have changeSafe : PairSafe (tensor (reenumerate M p) (fun a=>weight (e a)) (fun a i=>q i a)) := by
    change PairSafe (tensor (reenumerate M p) (fun a=>weight (e a)) (fun a i=>perms (p i) (e a)))
    rw [tensor_change]
    exact safe
  have h := fused_sum_constant (reenumerate M p) (fun a=>weight (e a)) q first (fun a=>hw (e a)) changeSafe
  intro a b
  have hh := h (perms (p 0) a) (perms (p 0) b)
  simpa only [q,e,Equiv.trans_apply,Equiv.symm_apply_apply] using hh

def pairOrder1 : Equiv.Perm (Fin 4) where
  toFun := ![2,0,1,3]
  invFun := ![1,2,0,3]
  left_inv := by decide
  right_inv := by decide

def pairOrder2 : Equiv.Perm (Fin 4) where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by decide
  right_inv := by decide

def pairOrder3 : Equiv.Perm (Fin 4) where
  toFun := ![1,0,3,2]
  invFun := ![1,0,3,2]
  left_inv := by decide
  right_inv := by decide

/-- Every one of the four label maps is a translation of the protected
identity label. The conclusion is derived solely from the actual proper cards. -/
theorem label_translations (M : Matching P 4) (weight : Label→ℂ)
    (perms : Fin 4→Equiv.Perm Label) (hfirst : ∀a,perms 0 a=a)
    (hw : ∀a,weight a≠0) (safe : PairSafe (tensor M weight (fun a i=>perms i a))) :
    ∀i a,perms i a=a+perms i 0 := by
  have h1 := ordered_sum_constant M weight perms hw safe pairOrder1
  have h2 := ordered_sum_constant M weight perms hw safe pairOrder2
  have h3 := ordered_sum_constant M weight perms hw safe pairOrder3
  have core (i : Fin 4) (h : ∀a b,perms 0 a+perms i a=perms 0 b+perms i b) (a : Label) :
      perms i a=a+perms i 0 := by
    have hh := h a 0
    rw [hfirst,hfirst,zero_add] at hh
    calc
      perms i a=a+(a+perms i a) := by rw [←add_assoc,label_add_self,zero_add]
      _=a+perms i 0 := congrArg (a+·) hh
  intro i a
  fin_cases i
  · change perms 0 a=a+perms 0 0
    rw [hfirst,hfirst,add_zero]
  · exact core 1 h1 a
  · exact core 2 h2 a
  · exact core 3 h3 a

end Fiber
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
