import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureCompressionGraph

/-! Exact evaluation of the signed compression graph, including pins,
empty columns, both boundary orientations, and every native-edge sum. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionValue
open Holant
open scoped BigOperators
namespace G
export NoIPureCompressionGraph (Fixed Fiber Vertices arity ports mask fixedSign fixedBit fixed_eq vertex finite)
end G
namespace S
export NoIPureCompressionGraph (signedWord)
end S
namespace P
export NoIPurePairedHardForm (paired compatible)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {K : Type} [Field K] {n m : ℕ}

def assignments (n : ℕ) : ((Fin n × Bool) → Bool) ≃ ((Fin n → Bool) × (Fin n → Bool)) where
  toFun z := (fun i => z (i,false),fun i => z (i,true))
  invFun p := fun (i,b) => if b then p.2 i else p.1 i
  left_inv z := by funext p; rcases p with ⟨i,b⟩; cases b <;> rfl
  right_inv p := rfl

def columnWord (p : Fin n → Bool ⊕ Fin m) (z : Fin (m*2) → Bool)
    (y : Fin n → Bool) (j : Fin m) : Fin (2 + Fintype.card (G.Fiber p j)) → Bool :=
  Fin.addCases (fun b => z (finProdFinEquiv (j,b)))
    (fun k => y ((Fintype.equivFin (G.Fiber p j)).symm k).val)

def aux (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (y : Fin n → Bool) : K :=
  (∏ i : G.Fixed p, if y i.val = !(G.fixedSign base p i) then 1 else 0) *
    ∏ j : Fin m, NoIPureMergeSigned.row (G.mask base p j) (columnWord p z y j)

theorem raw_value (f : Signature K n) (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) :
    (G.finite f base p).denote z = ∑ x : Fin n → Bool, ∑ y : Fin n → Bool,
      f x * aux base p z y * ∏ i : Fin n, Signature.disequality (x i) (y i) := by
  classical
  letI : DecidableEq (Fin n) := Classical.decEq _
  unfold FiniteNetwork.denote
  erw [←(assignments n).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  apply Finset.sum_congr (by ext y; simp)
  intro y _
  have root : (fun i : Fin n => Sum.elim z ((assignments n).symm (x,y))
      ((G.finite f base p).ports ⟨.inl (),i⟩)) = x := rfl
  have fixed (i : G.Fixed p) : (fun k : Fin 1 => Sum.elim z ((assignments n).symm (x,y))
      ((G.finite f base p).ports ⟨.inr (.inl i),k⟩)) = (fun _ => y i.val) := rfl
  have col (j : Fin m) : (fun k : Fin (2 + Fintype.card (G.Fiber p j)) =>
      Sum.elim z ((assignments n).symm (x,y))
        ((G.finite f base p).ports ⟨.inr (.inr j),k⟩)) = columnWord p z y j := by
    funext k
    obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin 2 ⊕ Fin (Fintype.card (G.Fiber p j)) ≃ _).surjective k
    cases k <;> simp [G.finite,G.ports,NoIPureCompressionGraph.toPort,columnWord,assignments]
  have rootV : (G.finite f base p).vertex (.inl ())
      (fun i => Sum.elim z ((assignments n).symm (x,y))
        ((G.finite f base p).ports ⟨.inl (),i⟩)) = f x := congrArg f root
  have fixedV (i : G.Fixed p) : (G.finite f base p).vertex (.inr (.inl i))
      (fun k => Sum.elim z ((assignments n).symm (x,y))
        ((G.finite f base p).ports ⟨.inr (.inl i),k⟩)) =
      if y i.val = !(G.fixedSign base p i) then 1 else 0 :=
    congrArg (fun w : Fin 1 → Bool => if w 0 = !(G.fixedSign base p i) then (1:K) else 0) (fixed i)
  have colV (j : Fin m) : (G.finite f base p).vertex (.inr (.inr j))
      (fun k => Sum.elim z ((assignments n).symm (x,y))
        ((G.finite f base p).ports ⟨.inr (.inr j),k⟩)) =
      NoIPureMergeSigned.row (G.mask base p j) (columnWord p z y j) :=
    congrArg (NoIPureMergeSigned.row (K:=K) (G.mask base p j)) (col j)
  simp only [Fintype.prod_sum_type,Fintype.prod_unique,rootV,fixedV,colV]
  change (f x * ((∏ i : G.Fixed p, _) * ∏ j : Fin m, _)) *
    (∏ i : Fin n, Signature.disequality (x i) (y i)) = _
  unfold aux
  ring

theorem prod_indicator {ι : Type} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (∏ i, if P i then (1:K) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i,hi⟩ := not_forall.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem edge_indicator (x y : Fin n → Bool) :
    (∏ i, Signature.disequality (x i) (y i) : K) =
      if y = (fun i => !(x i)) then 1 else 0 := by
  have each (i : Fin n) : (Signature.disequality (x i) (y i) : K) =
      if y i = !(x i) then 1 else 0 := by cases x i <;> cases y i <;> rfl
  simp only [each,prod_indicator,funext_iff]
  split_ifs <;> rfl

theorem value_sum (f : Signature K n) (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) :
    (G.finite f base p).denote z = ∑ x : Fin n → Bool, f x * aux base p z (fun i => !(x i)) := by
  rw [raw_value]
  apply Finset.sum_congr rfl
  intro x _
  simp only [edge_indicator,mul_ite,mul_one,mul_zero]
  simp

theorem column_indicator (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (x : Fin n → Bool) (j : Fin m) :
    (NoIPureMergeSigned.row (G.mask base p j) (columnWord p z (fun i => !(x i)) j) : K) =
      if z (finProdFinEquiv (j,(1:Fin 2))) = !(z (finProdFinEquiv (j,(0:Fin 2)))) ∧
        ∀ i : G.Fiber p j, x i.val = (base i.val ^^ z (finProdFinEquiv (j,(0:Fin 2))))
      then 1 else 0 := by
  classical
  have all_eq (v : Fin n → Bool) :
      (∀ k : Fin (Fintype.card (G.Fiber p j)),
        x ((Fintype.equivFin (G.Fiber p j)).symm k).val =
          v ((Fintype.equivFin (G.Fiber p j)).symm k).val) ↔
      ∀ i : G.Fiber p j, x i.val = v i.val :=
    ((Fintype.equivFin (G.Fiber p j)).forall_congr_left
      (p:=fun i : G.Fiber p j => x i.val = v i.val)).symm
  cases h0 : z (finProdFinEquiv (j,(0:Fin 2))) <;>
    cases h1 : z (finProdFinEquiv (j,(1:Fin 2))) <;>
    simp [NoIPureMergeSigned.row,G.mask,columnWord,funext_iff,Fin.forall_fin_add,
      Fin.forall_fin_succ,h0,h1,all_eq]
  all_goals simp only [all_eq (fun i => !(base i)),Subtype.forall]

def target (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) : Fin n → Bool :=
  S.signedWord base p (fun j => z (finProdFinEquiv (j,(0:Fin 2))))

theorem target_fixed (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (i : G.Fixed p) : target base p z i.val = G.fixedSign base p i := by
  simp only [target,S.signedWord,G.fixed_eq,Sum.elim_inl,id_eq]
  cases hb : base i.val <;> simp [G.fixedSign,hb]

theorem target_fiber (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (j : Fin m) (i : G.Fiber p j) :
    target base p z i.val = (base i.val ^^ z (finProdFinEquiv (j,(0:Fin 2)))) := by
  simp [target,S.signedWord,i.property]

theorem conditions (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (x : Fin n → Bool) :
    ((∀ i : G.Fixed p, x i.val = G.fixedSign base p i) ∧
      ∀ j : Fin m, z (finProdFinEquiv (j,(1:Fin 2))) = !(z (finProdFinEquiv (j,(0:Fin 2)))) ∧
        ∀ i : G.Fiber p j, x i.val = (base i.val ^^ z (finProdFinEquiv (j,(0:Fin 2))))) ↔
      P.compatible z ∧ x = target base p z := by
  constructor
  · rintro ⟨fixed,cols⟩
    refine ⟨fun j => (cols j).1,funext fun i => ?_⟩
    cases h : p i with
    | inl b => exact (fixed ⟨i,⟨b,h⟩⟩).trans (target_fixed base p z ⟨i,⟨b,h⟩⟩).symm
    | inr j => exact ((cols j).2 ⟨i,h⟩).trans (target_fiber base p z j ⟨i,h⟩).symm
  · rintro ⟨good,rfl⟩
    exact ⟨target_fixed base p z,fun j => ⟨good j,target_fiber base p z j⟩⟩

theorem aux_indicator (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m)
    (z : Fin (m*2) → Bool) (x : Fin n → Bool) :
    (aux base p z (fun i => !(x i)) : K) =
      if P.compatible z ∧ x = target base p z then 1 else 0 := by
  classical
  simp only [aux,Bool.not_inj_iff,column_indicator,prod_indicator]
  have mul_indicator (A B : Prop) [Decidable A] [Decidable B] :
      (if A then (1:K) else 0) * (if B then 1 else 0) = if A ∧ B then 1 else 0 := by
    by_cases a : A <;> by_cases b : B <;> simp [a,b]
  simp only [mul_indicator,conditions]

theorem value (f : Signature K n) (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) :
    (G.finite f base p).denote = P.paired (fun z => f (S.signedWord base p z)) := by
  funext z
  rw [value_sum]
  simp only [aux_indicator]
  by_cases good : P.compatible z
  · simp [P.paired,good,target]
  · simp [P.paired,good]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionValue
end
