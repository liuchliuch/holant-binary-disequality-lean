import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeRow
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPureMergeWords
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePairedHardForm

/-! The actual signed-column compression graph. Each original port is joined
by one native-X edge to a pin or a signed equality merger. Every logical
column exposes the fixed interleaved opposite pair, including empty columns. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionGraph
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1500000
set_option Elab.async false
variable {n m : ℕ}

def signedWord (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) (z : Fin m → Bool) :
    Fin n → Bool := fun i => base i ^^ Sum.elim id z (p i)

def column (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) (j : Fin m) : ℤ :=
  ∑ i : Fin n, if p i = Sum.inr j then (if base i then -1 else 1) else 0

abbrev Fixed (p : Fin n → Bool ⊕ Fin m) := {i : Fin n // ∃ b, p i = Sum.inl b}
abbrev Fiber (p : Fin n → Bool ⊕ Fin m) (j : Fin m) := {i : Fin n // p i = Sum.inr j}
instance (p : Fin n → Bool ⊕ Fin m) : Fintype (Fixed p) := inferInstanceAs (Fintype {i // ∃b,p i=Sum.inl b})
instance (p : Fin n → Bool ⊕ Fin m) (j : Fin m) : Fintype (Fiber p j) := inferInstanceAs (Fintype {i // p i=Sum.inr j})
abbrev Vertices (p : Fin n → Bool ⊕ Fin m) := Unit ⊕ (Fixed p ⊕ Fin m)

def arity (p : Fin n → Bool ⊕ Fin m) : Vertices p → ℕ
  | .inl _ => n
  | .inr (.inl _) => 1
  | .inr (.inr j) => 2 + Fintype.card (Fiber p j)

def fixedBit (p : Fin n → Bool ⊕ Fin m) (i : Fixed p) : Bool :=
  match p i.val with
  | .inl b => b
  | .inr _ => false

theorem fixed_eq (p : Fin n → Bool ⊕ Fin m) (i : Fixed p) : p i.val = Sum.inl (fixedBit p i) := by
  obtain ⟨b,h⟩ := i.property
  simp [fixedBit,h]

def toPort (p : Fin n → Bool ⊕ Fin m) :
    (Σ v : Vertices p, Fin (arity p v)) → (Fin (m*2) ⊕ (Fin n × Bool))
  | ⟨.inl _,i⟩ => .inr (i,false)
  | ⟨.inr (.inl i),_⟩ => .inr (i.val,true)
  | ⟨.inr (.inr j),i⟩ =>
    match (finSumFinEquiv : Fin 2 ⊕ Fin (Fintype.card (Fiber p j)) ≃ _).symm i with
    | .inl b => .inl (finProdFinEquiv (j,b))
    | .inr k => .inr (((Fintype.equivFin (Fiber p j)).symm k).val,true)

def fromPort (p : Fin n → Bool ⊕ Fin m) :
    (Fin (m*2) ⊕ (Fin n × Bool)) → (Σ v : Vertices p, Fin (arity p v))
  | .inl b => ⟨.inr (.inr (finProdFinEquiv.symm b).1),
      Fin.castAdd _ (finProdFinEquiv.symm b).2⟩
  | .inr (i,false) => ⟨.inl (),i⟩
  | .inr (i,true) =>
    match h : p i with
    | .inl b => ⟨.inr (.inl ⟨i,⟨b,h⟩⟩),(0 : Fin 1)⟩
    | .inr j => ⟨.inr (.inr j),Fin.natAdd 2 ((Fintype.equivFin (Fiber p j)) ⟨i,h⟩)⟩

def ports (p : Fin n → Bool ⊕ Fin m) :
    (Σ v : Vertices p, Fin (arity p v)) ≃ (Fin (m*2) ⊕ (Fin n × Bool)) where
  toFun := toPort p
  invFun := fromPort p
  left_inv := by
    rintro ⟨(_|i|j),k⟩
    · rfl
    · obtain ⟨b,h⟩ := i.property
      change Fin 1 at k
      fin_cases k
      simp only [toPort,fromPort]
      split
      · rfl
      · rename_i j hj
        simp [h] at hj
    · obtain ⟨k,rfl⟩ := (finSumFinEquiv : Fin 2 ⊕ Fin (Fintype.card (Fiber p j)) ≃ _).surjective k
      cases k with
      | inl b =>
        simp only [toPort,finSumFinEquiv_apply_left,finSumFinEquiv_symm_apply_castAdd]
        exact congrArg (fun q : Fin m × Fin 2 =>
          (⟨.inr (.inr q.1),Fin.castAdd _ q.2⟩ : Σ v : Vertices p, Fin (arity p v)))
          ((finProdFinEquiv : Fin m × Fin 2 ≃ _).symm_apply_apply (j,b))
      | inr k =>
        have h := ((Fintype.equivFin (Fiber p j)).symm k).property
        simp only [toPort,fromPort,finSumFinEquiv_apply_right,finSumFinEquiv_symm_apply_natAdd]
        split
        · rename_i b hb
          simp [h] at hb
        · rename_i j' hj
          have eqj : j' = j := Sum.inr.inj (hj.symm.trans h)
          subst j'
          simp
  right_inv := by
    rintro (b|⟨i,b⟩)
    · obtain ⟨⟨j,k⟩,rfl⟩ := (finProdFinEquiv : Fin m × Fin 2 ≃ _).surjective b
      simp [toPort,fromPort]
    · cases b
      · rfl
      · simp only [fromPort]
        split
        · rfl
        · simp [toPort]

def mask (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    Fin (2 + Fintype.card (Fiber p j)) → Bool :=
  Fin.addCases ![false,true] (fun k => !(base ((Fintype.equivFin (Fiber p j)).symm k).val))

def fixedSign (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) (i : Fixed p) : Bool :=
  if base i.val then !(fixedBit p i) else fixedBit p i

def vertex {K : Type} [Field K] (f : Signature K n)
    (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) :
    (v : Vertices p) → Signature K (arity p v)
  | .inl _ => f
  | .inr (.inl i) => fun x => if x (0 : Fin 1) = !(fixedSign base p i) then 1 else 0
  | .inr (.inr j) => NoIPureMergeSigned.row (mask base p j)

def finite {K : Type} [Field K] (f : Signature K n)
    (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) :
    FiniteNetwork K (Vertices p) (Fin n) (m*2) where
  arity := arity p
  ports := ports p
  vertex := vertex f base p
  edge _ := Signature.disequality

theorem mask_charge (base : Fin n → Bool) (p : Fin n → Bool ⊕ Fin m) (j : Fin m) :
    charge (mask base p j) = column base p j := by
  classical
  change charge (Fin.addCases ![false,true]
    (fun k => !(base ((Fintype.equivFin (Fiber p j)).symm k).val))) = _
  rw [NoIPureMergeWords.charge_append]
  have first : charge (![false,true] : Fin 2 → Bool) = 0 := by decide
  rw [first,zero_add]
  have sum_charge {r : ℕ} (w : Fin r → Bool) :
      charge w = ∑i : Fin r, if w i then (1:ℤ) else -1 := by
    unfold charge weight
    simp only [Nat.cast_sum]
    have hh : (r:ℤ) = ∑_i : Fin r, (1:ℤ) := by simp
    rw [hh,Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases w i <;> norm_num
  rw [sum_charge,←(Fintype.equivFin (Fiber p j)).sum_comp]
  simp only [Equiv.symm_apply_apply]
  have sign (i : Fin n) : (if !(base i) then (1:ℤ) else -1) =
      if base i then -1 else 1 := by cases base i <;> rfl
  simp only [sign]
  unfold column
  rw [←Finset.sum_filter]
  convert (Finset.sum_subtype_eq_sum_filter (s:=Finset.univ)
    (p:=fun i : Fin n => p i = Sum.inr j) (fun i => if base i then (-1:ℤ) else 1))
      using 1 <;> simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureCompressionGraph
end
