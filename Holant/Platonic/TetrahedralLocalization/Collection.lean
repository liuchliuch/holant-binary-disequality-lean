import Holant.Platonic.TetrahedralLocalization.OneStep
import Holant.Platonic.RainbowLocalization.PhysicalKernelLift

/-! Finite disjoint original-port records for arbitrary iterated pair cards.
Each step adds precisely one kernel to the same original tensor occurrence. -/
namespace Holant.Platonic.TetrahedralLocalization
open Holant Holant.Platonic.StabilizerShortening Holant.Tractable.AffinePhase
open Holant.Certificates.MatchingContractionClosure
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {o m n : ℕ} {E : Type*}

/-- Add the next pair to the existing original-port partition. -/
def addPairPorts (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) : CollectionPorts (Fin o) (Fin n) (Option E) where
  toFun
    | .inl j => p (.inl (q (.inr j)))
    | .inr (none,b) => p (.inl (q (.inl b)))
    | .inr (some e,b) => p (.inr (e,b))
  invFun j := match p.symm j with
    | .inl i => match q.symm i with
      | .inl b => .inr (none,b)
      | .inr i => .inl i
    | .inr (e,b) => .inr (some e,b)
  left_inv j := by
    cases j with
    | inl j => simp
    | inr eb => rcases eb with ⟨e,b⟩;cases e <;> simp
  right_inv j := by
    obtain ⟨j,rfl⟩ := p.surjective j
    cases j with
    | inl j => obtain ⟨j,rfl⟩ := q.surjective j;cases j <;> simp
    | inr eb => rcases eb with ⟨e,b⟩;simp

@[simp] theorem addPairPorts_boundary (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) (j : Fin n) :
    addPairPorts p q (.inl j)=p (.inl (q (.inr j))) := rfl
@[simp] theorem addPairPorts_new (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) (b : Bool) :
    addPairPorts p q (.inr (none,b))=p (.inl (q (.inl b))) := rfl
@[simp] theorem addPairPorts_old (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) (e : E) (b : Bool) :
    addPairPorts p q (.inr (some e,b))=p (.inr (e,b)) := rfl

theorem addPair_assignment (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) (x : Word n) (a b : Bool)
    (y : E → Bool × Bool) :
    collectionAssignment (addPairPorts p q) x (Option.elim' (a,b) y)=
      collectionAssignment p (pairInsert q a b x) y := by
  ext j
  obtain ⟨j,rfl⟩ := (addPairPorts p q).surjective j
  cases j with
  | inl j => rw [collectionAssignment_boundary,addPairPorts_boundary,collectionAssignment_boundary,pairInsert_remaining]
  | inr eb =>
    rcases eb with ⟨e,c⟩
    rw [collectionAssignment_edge]
    cases e with
    | none => cases c <;> simp
    | some e => simp

def optionLabels : (Option E → Bool × Bool) ≃ ((Bool × Bool) × (E → Bool × Bool)) where
  toFun y := (y none,fun e => y (some e))
  invFun z := Option.elim' z.1 z.2
  left_inv y := by funext e;cases e <;> rfl
  right_inv z := rfl

variable [Fintype E] [DecidableEq E]

/-- Exact Fubini identity that flattens a further card into the original graph. -/
theorem contractCollection_addPair (p : CollectionPorts (Fin o) (Fin m) E)
    (q : (Bool ⊕ Fin n) ≃ Fin m) (C : E → Kernel ℂ) (K : Kernel ℂ)
    (f : Signature ℂ o) :
    contractCollection (addPairPorts p q) (Option.elim' K C) f=
      pairCard q K (contractCollection p C f) := by
  ext x
  unfold contractCollection
  rw [← optionLabels.symm.sum_comp
    (fun y : Option E → Bool × Bool =>
      kernelProduct (Option.elim' K C) y * f (collectionAssignment (addPairPorts p q) x y))]
  rw [Fintype.sum_prod_type]
  simp only [optionLabels,Equiv.coe_fn_symm_mk]
  simp only [Fintype.sum_prod_type,pairCard,LinearMap.coe_mk,AddHom.coe_mk,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro y hy
  change kernelProduct (Option.elim' K C) (Option.elim' (a,b) y) *
    f (collectionAssignment (addPairPorts p q) x (Option.elim' (a,b) y))=_
  rw [addPair_assignment]
  simp [kernelProduct,Fintype.prod_option,mul_assoc]

/-- No contraction: the original external-port order is preserved. -/
def emptyPorts (n : ℕ) : CollectionPorts (Fin n) (Fin n) Empty where
  toFun := Sum.elim id (fun x => nomatch x.1)
  invFun := Sum.inl
  left_inv j := by cases j with
    | inl j => rfl
    | inr eb => exact isEmptyElim eb.1
  right_inv j := rfl

@[simp] theorem emptyCollection (f : Signature ℂ n) :
    contractCollection (emptyPorts n) (fun e : Empty => nomatch e) f=f := by
  ext x
  have ha (y : Empty → Bool × Bool) : collectionAssignment (emptyPorts n) x y=x := rfl
  simp [contractCollection,ha,kernelProduct]

/-- The literal port bijection gives the exact linear kernel count. -/
theorem collection_arity (p : CollectionPorts (Fin o) (Fin n) E) :
    n+2*Fintype.card E=o := by
  have h := Fintype.card_congr p
  simpa [Nat.mul_comm] using h

end
end Holant.Platonic.TetrahedralLocalization
