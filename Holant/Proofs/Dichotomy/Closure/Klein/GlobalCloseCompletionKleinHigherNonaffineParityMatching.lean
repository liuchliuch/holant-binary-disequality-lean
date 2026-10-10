import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineParity
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineCurrent

/-! Every literal standard-Pauli matching has one actual support parity.
The statement retains arbitrary matching size, physical port order and scale. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParityMatching
open Holant
open scoped BigOperators
open GlobalCloseCompletionKleinHigherNonaffine
open GlobalCloseCompletionKleinHigherNonaffineParity
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

theorem E_parity (a : Label) (u v : Bool) (live : E a u v≠0) :
    bitSign u*bitSign v=if a.2=0 then 1 else -1 := by
  rcases label_cases a with rfl|rfl|rfl|rfl <;> cases u <;> cases v <;>
    simp_all [E,EOver,xLabel,yLabel,zLabel,bitSign]

theorem wordSign_matching {P : Type*} [Fintype P] {r : ℕ}
    (M : Matching P r) (x : P→Bool) :
    wordSign x=∏e,bitSign (x (M.ports (e,false)))*bitSign (x (M.ports (e,true))) := by
  unfold wordSign
  rw [←Equiv.prod_comp M.ports (fun i=>bitSign (x i)),Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,mul_comm]

theorem matching_parity {P : Type*} [Fintype P] {r : ℕ}
    (M : Matching P r) (labels : Fin r→Label) (c : ℂ) :
    HasParity (fun x=>c*M.tensor labels x) := by
  intro x y hx hy
  have vx := Finset.prod_ne_zero_iff.mp ((mul_ne_zero_iff.mp hx).2)
  have vy := Finset.prod_ne_zero_iff.mp ((mul_ne_zero_iff.mp hy).2)
  rw [wordSign_matching M x,wordSign_matching M y]
  apply Finset.prod_congr rfl
  intro e he
  exact (E_parity (labels e) _ _ (vx e he)).trans (E_parity (labels e) _ _ (vy e he)).symm

theorem zero_parity {P : Type*} [Fintype P] : HasParity (0 : Tensor ℂ P) := by
  intro x y hx _
  exact (hx rfl).elim

theorem pauli_parity {P : Type*} [Fintype P] (f : Tensor ℂ P)
    (matching : MatchingCard.PauliMatchingOrZero f) : HasParity f := by
  rcases matching with rfl|⟨r,M,labels,c,_nonzero,rfl⟩
  · exact zero_parity
  · exact matching_parity M labels c

theorem scale_parity {P : Type*} [Fintype P] (f : Tensor ℂ P) (h : HasParity f) (c : ℂ) :
    HasParity (fun x=>c*f x) := by
  intro x y hx hy
  exact h x y (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffineParityMatching
end
