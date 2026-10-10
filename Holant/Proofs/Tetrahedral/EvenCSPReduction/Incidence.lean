import Holant.Proofs.Tetrahedral.EvenCSPReduction.Data


namespace Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open Holant
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

section General
variable {K P V : Type*} [CommSemiring K] [Fintype P] [Fintype V] [DecidableEq P] [DecidableEq V]
variable (ρ : P → V)

theorem equality_guard (z : P → Bool) (x : V → Bool) :
    (∏v : V,∏p : P,if ρ p=v then Signature.equality (K:=K) (z p) (x v) else 1)=
      if z=(fun p => x (ρ p)) then 1 else 0 := by
  rw [Finset.prod_comm]
  have he (p : P) : (∏v : V,if ρ p=v then Signature.equality (K:=K) (z p) (x v) else 1)=
      Signature.equality (z p) (x (ρ p)) := by
    simp
  simp_rw [he]
  simp only [Signature.equality,Fintype.prod_boole,←funext_iff]

/-- Complete partition identity, including all zero-degree variables and
every repeated/nullary factor. No surjectivity of ρ is assumed. -/
theorem incidence_partition (W : (P → Bool) → K) :
    (∑z : P → Bool,W z * ∏v : V,
      (∑b : Bool,∏p : P,if ρ p=v then Signature.equality (z p) b else 1))=
      ∑x : V → Bool,W (fun p => x (ρ p)) := by
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [equality_guard ρ]
  simp

/-- No unconstrained edge-bit choice can duplicate a supported incidence
word. The missing variable coordinates are precisely the empty fibers. -/
theorem pullback_equal_iff (x y : V → Bool) :
    (fun p => x (ρ p))=(fun p => y (ρ p)) ↔ ∀v ∈ Set.range ρ,x v=y v := by
  constructor
  · intro h v hv
    obtain ⟨p,rfl⟩ := hv
    exact congrFun h p
  · intro h
    funext p
    exact h (ρ p) ⟨p,rfl⟩

end General

namespace Raw
variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

theorem incidence_value (r : Input s a) : incidenceValue G r=value G r := by
  simpa only [incidenceValue,value,variableWeight] using
    incidence_partition (route r) (factorWeight G r)

theorem unused_variable (r : Input s a) (i : Fin r.val.variables)
    (hi : r.val.degree i.val=0) (z : r.val.Ports → Bool) :
    variableWeight (K:=K) r z i=2 := by
  have hn := (r.val.degree_zero_iff i.val).mp hi
  have hp (p : r.val.Ports) : route r p≠i := by
    intro he
    exact hn p (congrArg Fin.val he)
  simp [variableWeight,hp,Fintype.sum_bool]

end Raw
end Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
