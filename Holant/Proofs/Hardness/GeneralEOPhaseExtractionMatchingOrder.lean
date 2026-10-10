import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingNormalForm
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Pi

/-! The adjacent-pair normal form is an exact sum over one Boolean choice per
pair. Reordering complete pairs preserves that sum, and hence the value of the
corresponding actual native closure. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingOrder
open Holant
open scoped BigOperators
namespace M
export GeneralEOPhaseExtractionMatchingNormalForm (value)
end M
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace H
export GeneralEOPhaseExtractionLoopTomography (merge)
end H
set_option backward.isDefEq.respectTransparency false

def paired : (k : ℕ) → (Fin k→Bool) → (Fin (2*k)→Bool)
  | 0,_ => Fin.elim0
  | k+1,z => O.word (z 0) (!(z 0)) (paired k (Fin.tail z))

theorem value_sum (k : ℕ) (f : Signature ℂ (2*k)) :
    M.value k f=∑z : Fin k→Bool,f (paired k z) := by
  classical
  induction k with
  | zero => simp [M.value,GeneralEOPhaseExtractionMatchingNormalForm.value,paired]
  | succ k ih =>
    let : Fintype (Bool × (Fin k → Bool)) := instFintypeProd Bool (Fin k → Bool)
    let e : (Bool × (Fin k → Bool)) ≃ (Fin (k+1) → Bool) := Fin.consEquiv (fun _ => Bool)
    have he (b : Bool) (z : Fin k → Bool) : e (b,z)=Fin.cons b z := rfl
    rw [GeneralEOPhaseExtractionMatchingNormalForm.value,ih]
    rw [←e.sum_comp (fun z => f (paired (k+1) z))]
    simp only [Fintype.sum_prod_type,he,paired,Fin.cons_zero,Fin.tail_cons]
    simp only [Fintype.sum_bool,Bool.not_true,Bool.not_false]
    change (∑z : Fin k→Bool,
      (f (O.word false true (paired k z))+f (O.word true false (paired k z))))=_
    rw [Finset.sum_add_distrib,add_comm]

def port (k : ℕ) : (Fin k×Fin 2) ≃ Fin (2*k) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2))

theorem port_val {k : ℕ} (j : Fin k) (b : Fin 2) :
    (port k (j,b)).val=b.val+2*j.val := rfl

theorem port_zero (k : ℕ) (b : Fin 2) : port (k+1) (0,b)=Fin.castLE (by omega) b := by
  apply Fin.ext
  simp [port_val]

theorem port_succ {k : ℕ} (j : Fin k) (b : Fin 2) :
    port (k+1) (j.succ,b)=(port k (j,b)).succ.succ := by
  apply Fin.ext
  simp only [port_val,Fin.val_succ]
  omega

theorem paired_port (k : ℕ) (z : Fin k→Bool) (j : Fin k) (b : Fin 2) :
    paired k z (port k (j,b))=if b=0 then z j else !(z j) := by
  induction k with
  | zero => exact Fin.elim0 j
  | succ k ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · fin_cases b <;> rfl
    · rw [port_succ]
      change paired k (Fin.tail z) (port k (j,b))=_
      exact ih _ j

def blockPerm {k : ℕ} (p : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (2*k)) :=
  (port k).symm.trans ((Equiv.prodCongr p (Equiv.refl _)).trans (port k))

theorem blockPerm_port {k : ℕ} (p : Equiv.Perm (Fin k)) (j : Fin k) (b : Fin 2) :
    blockPerm p (port k (j,b))=port k (p j,b) := by
  simp [blockPerm]

theorem paired_blockPerm {k : ℕ} (p : Equiv.Perm (Fin k)) (z : Fin k→Bool) :
    paired k z ∘ blockPerm p=paired k (z ∘ p) := by
  funext i
  obtain ⟨⟨j,b⟩,rfl⟩ := (port k).surjective i
  simp only [Function.comp_apply,blockPerm_port,paired_port]

def relabel {k : ℕ} (p : Equiv.Perm (Fin k)) : (Fin k→Bool) ≃ (Fin k→Bool) where
  toFun z := z ∘ p
  invFun z := z ∘ p.symm
  left_inv z := by funext i; simp
  right_inv z := by funext i; simp

theorem value_blockPerm {k : ℕ} (f : Signature ℂ (2*k)) (p : Equiv.Perm (Fin k)) :
    M.value k (Tensor.reindex (blockPerm p) f)=M.value k f := by
  rw [value_sum,value_sum]
  change (∑z : Fin k→Bool,f (paired k z ∘ blockPerm p))=_
  simp_rw [paired_blockPerm]
  exact (relabel p).sum_comp (fun z => f (paired k z))

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingOrder
