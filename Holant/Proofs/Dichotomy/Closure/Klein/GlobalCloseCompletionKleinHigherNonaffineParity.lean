import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinStandardRealLine
import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorParity

/-! Universal Pauli parity reconstruction. Every proper card needs only one
support parity, not a matching or Affine normal form. Projective determination
applies to the input and its full Z-sign twist, retaining zero cards. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParity
open Holant
open Holant.Pauli.ProjectiveDetermination
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.CompatibleClosure (pairOrder)
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def bitSign (b : Bool) : ℂ := if b then -1 else 1

def wordSign {I : Type*} [Fintype I] (x : I→Bool) : ℂ := ∏i,bitSign (x i)

def HasParity {I : Type*} [Fintype I] (f : Tensor ℂ I) : Prop :=
  ∀x y,f x≠0→f y≠0→wordSign x=wordSign y

def twist {I : Type*} [Fintype I] (f : Tensor ℂ I) : Tensor ℂ I := fun x=>wordSign x*f x

def paritySign (p : ZMod 2) : ℂ := if p=0 then 1 else -1

theorem paritySign_add (p q : ZMod 2) : paritySign (p+q)=paritySign p*paritySign q := by
  fin_cases p <;> fin_cases q <;> norm_num [paritySign] <;> decide

theorem paritySign_injective : Function.Injective paritySign := by
  intro p q
  fin_cases p <;> fin_cases q <;> norm_num [paritySign]

theorem wordSign_parity {n : ℕ} (x : Fin n→Bool) : wordSign x=paritySign (ClosureSixPort.parity x) := by
  have finite (S : Finset (Fin n)) :
      (∏i∈S,bitSign (x i))=paritySign (∑i∈S,ClosureSixPort.bit (x i)) := by
    induction S using Finset.induction_on with
    | empty => simp [paritySign]
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi,Finset.sum_insert hi,paritySign_add,ih]
      congr 1
      cases x i <;> norm_num [bitSign,ClosureSixPort.bit,paritySign]
  exact finite Finset.univ

theorem hasParity_iff {n : ℕ} (f : Signature ℂ n) :
    HasParity f ↔ GlobalCloseCompletionProductAncestorParity.PureParity f := by
  constructor
  · intro h x y hx hy
    apply paritySign_injective
    simpa only [wordSign_parity] using h x y hx hy
  · intro h x y hx hy
    rw [wordSign_parity,wordSign_parity,h x y hx hy]

theorem parity_iff_dependent {I : Type*} [Fintype I] (f : Tensor ℂ I) :
    HasParity f ↔ Dependent f (twist f) := by
  constructor
  · intro h
    by_cases zero : f=0
    · exact Or.inl zero
    obtain ⟨x,hx⟩ : ∃x,f x≠0 := by by_contra! none;exact zero (funext none)
    refine Or.inr ⟨wordSign x,?_⟩
    funext y
    by_cases hy : f y=0
    · simp only [twist,hy,mul_zero]
    · change wordSign y*f y=wordSign x*f y
      rw [h y x hy hx]
  · rintro (zero|⟨c,equation⟩) x y hx hy
    · exact (hx (congrFun zero x)).elim
    · have ex := congrFun equation x
      have ey := congrFun equation y
      exact (mul_right_cancel₀ hx ex).trans (mul_right_cancel₀ hy ey).symm

theorem wordSign_fill {I : Type*} [Fintype I] [DecidableEq I]
    (r s : I) (hne : r≠s) (a b : Bool) (z : Rest r s→Bool) :
    wordSign (fill r s a b z)=bitSign a*bitSign b*wordSign z := by
  rw [wordSign,prod_ports r s hne]
  simp only [fill_left,fill_right r s hne,fill_rest]
  rfl

def kernelSign (k : Label) : ℂ := if k<2 then 1 else -1

theorem kernel_twist (k : Label) (a b : Bool) :
    kernel k a b*(bitSign a*bitSign b)=kernelSign k*kernel k a b := by
  fin_cases k <;> cases a <;> cases b <;> norm_num [kernel,bitSign,kernelSign]

theorem card_twist {I : Type*} [Fintype I] [DecidableEq I]
    (r s : I) (hne : r≠s) (k : Label) (f : Tensor ℂ I) :
    card r s k (twist f)=fun z=>kernelSign k*twist (card r s k f) z := by
  funext z
  simp only [card,twist,wordSign_fill r s hne,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  calc
    _=(kernel k a b*(bitSign a*bitSign b))*(wordSign z*f (fill r s a b z)) := by ring
    _=_ := by rw [kernel_twist];ring

theorem dependent_scale_right {I : Type*} (u v : I→ℂ) (h : Dependent u v) (c : ℂ) :
    Dependent u (fun x=>c*v x) := by
  rcases h with zero|⟨d,equation⟩
  · exact Or.inl zero
  · refine Or.inr ⟨c*d,?_⟩
    rw [equation]
    funext x
    ring

theorem pauli_parity (n : ℕ) (large : 5≤n) (f : Signature ℂ n)
    (cards : ∀u v : Fin n,u<v→∀k : Label,HasParity (card u v k f)) : HasParity f := by
  apply (parity_iff_dependent f).mpr
  apply pauli_projective_determination n large
  intro u v less k
  rw [card_twist u v (ne_of_lt less)]
  exact dependent_scale_right _ _ ((parity_iff_dependent _).mp (cards u v less k)) _

theorem parity_reindex {I J : Type*} [Fintype I] [Fintype J]
    (e : I≃J) (f : Tensor ℂ I) (h : HasParity f) : HasParity (Tensor.reindex e f) := by
  intro x y hx hy
  have hh := h (fun i=>x (e i)) (fun i=>y (e i)) hx hy
  unfold wordSign at hh ⊢
  rw [Equiv.prod_comp e (fun i=>bitSign (x i)),Equiv.prod_comp e (fun i=>bitSign (y i))] at hh
  exact hh

theorem ordered_parity {n : ℕ} (f : Signature ℂ (n+2)) (large : 5≤n+2)
    (cards : ∀order : Equiv.Perm (Fin (n+2)),∀k : Label,
      HasParity (Signature.contract (kernel k) (Tensor.reindex order.symm f))) : HasParity f := by
  apply pauli_parity (n+2) large
  intro u v less k
  have h := cards (pairOrder u v) k
  rw [←GlobalCloseCompletionKleinStandardRealLine.card_order u v (ne_of_lt less) k f] at h
  have h' := parity_reindex (remainingOrder u v (ne_of_lt less)) _ h
  simpa only [Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl] using h'

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParity
end
