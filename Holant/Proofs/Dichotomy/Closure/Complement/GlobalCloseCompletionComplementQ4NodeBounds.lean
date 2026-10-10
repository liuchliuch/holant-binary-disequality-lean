import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4NodeMachine
import Holant.OneHot.ArithmeticSizeTree

/-! Structural size bounds for every actual emitted node. Each of the four
unary exponents is at most the original marked-vertex count. Both machine
modes therefore share the same linear root-value budget. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeBounds
open Holant Holant.OneHot
namespace M
export GlobalCloseCompletionComplementQ4NodeMachine (C4 coordinates total product node roots)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K A : Type} [Field K] [Algebra ℚ K]
variable (coeff : A→K) (unit : A) (hone : coeff unit=1)

theorem power {value : K} (h : ArithmeticSize.Bound coeff 1 value) (n : ℕ) :
    ArithmeticSize.Bound coeff n (value^n) := by
  induction n with
  | zero=>simpa only [pow_zero] using (ArithmeticSize.Bound.one (coeff:=coeff))
  | succ n ih=>simpa only [pow_succ] using ih.mul h

include hone in
theorem product_bound (v : Fin 4→K) (hv : ∀i,ArithmeticSize.Bound coeff 1 (v i)) (x : M.C4) :
    ArithmeticSize.Bound coeff (M.total x) (M.product v x) := by
  exact (((power coeff (hv 0) (M.coordinates x 0)).mul (power coeff (hv 1) (M.coordinates x 1))).mul
    (power coeff (hv 2) (M.coordinates x 2))).mul (power coeff (hv 3) (M.coordinates x 3))

include hone in
theorem node_bound (v : Fin 4→K) (hv : ∀i,ArithmeticSize.Bound coeff 1 (v i))
    (supportMode : Bool) (j : Fin 4) (n : ℕ) (x : M.C4)
    (bound : ∀i,M.coordinates x i≤n) : ArithmeticSize.Bound coeff (4*n+1) (M.node v supportMode j x) := by
  have total : M.total x≤4*n := by
    have h0:=bound 0
    have h1:=bound 1
    have h2:=bound 2
    have h3:=bound 3
    unfold M.total
    omega
  have product := (product_bound coeff unit hone v hv x).mono unit hone (by omega : M.total x≤4*n+1)
  have zero : ArithmeticSize.Bound coeff (4*n+1) (0:K):=ArithmeticSize.Bound.zero unit _
  have one : ArithmeticSize.Bound coeff (4*n+1) (1:K):=
    (ArithmeticSize.Bound.one (coeff:=coeff)).mono unit hone (by omega)
  unfold M.node
  split_ifs <;> assumption

include hone in
theorem roots_bound (v : Fin 4→K) (hv : ∀i,ArithmeticSize.Bound coeff 1 (v i))
    (supportMode : Bool) (j : Fin 4) (n : ℕ) :
    ∀x∈M.roots v supportMode j n,ArithmeticSize.Bound coeff (4*n+1) x := by
  intro x member
  simp only [M.roots,List.mem_flatMap,List.mem_map,List.mem_range] at member
  obtain ⟨a,ha,b,hb,c,hc,d,hd,rfl⟩:=member
  apply node_bound coeff unit hone v hv supportMode j n
  intro i
  fin_cases i <;> dsimp [M.coordinates] <;> omega

theorem roots_length (v : Fin 4→K) (supportMode : Bool) (j : Fin 4) (n : ℕ) :
    (M.roots v supportMode j n).length=(n+1)^4 := by
  simp [M.roots,List.length_flatMap]
  ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4NodeBounds
end
