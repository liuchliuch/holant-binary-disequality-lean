import Holant.Proofs.Traversal.ArityTwo.Bytecode
import Holant.OneHot.ArithmeticSize


namespace Holant.LocalDrafts.TraversalCompletion.ArityTwo
open Holant Holant.OneHot.ArithmeticSize
open scoped BigOperators
variable {A B K : Type*} [CommSemiring K]
variable (family : B → K) (unit : B) (hunit : family unit = 1)
variable (coeff : A → K) (hlit : ∀ a, Bound family 1 (coeff a))

include unit hunit

private theorem dot_bound {b : ℕ} (hb : 1 ≤ b) {p q x y : K}
    (hp : Bound family 1 p) (hq : Bound family 1 q)
    (hx : Bound family b x) (hy : Bound family b y) :
    Bound family (b+2) (p*x+q*y) ∧
      ∀ z ∈ dotTrace p q x y, Bound family (b+2) z := by
  have hpx : Bound family (b+1) (p*x) := by simpa [Nat.add_comm] using hp.mul hx
  have hqy : Bound family (b+1) (q*y) := by simpa [Nat.add_comm] using hq.mul hy
  have hs : Bound family (b+2) (p*x+q*y) := hpx.add unit hunit hqy
  have hs' : Bound family (b+2) (q*y+p*x) := by simpa [add_comm] using hs
  have hp' := hp.mono unit hunit (show 1 ≤ b+2 by omega)
  have hq' := hq.mono unit hunit (show 1 ≤ b+2 by omega)
  have hx' := hx.mono unit hunit (show b ≤ b+2 by omega)
  have hy' := hy.mono unit hunit (show b ≤ b+2 by omega)
  have hpx' := hpx.mono unit hunit (show b+1 ≤ b+2 by omega)
  have hqy' := hqy.mono unit hunit (show b+1 ≤ b+2 by omega)
  refine ⟨hs, ?_⟩
  intro z hz
  simp only [dotTrace,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

include hlit in
theorem matrix_bound {b : ℕ} (hb : 1 ≤ b) (M : Kernel A) (v : Bool → K)
    (hv : ∀ a, Bound family b (v a)) :
    (∀ a, Bound family (b+2) (Kernel.act (realizeMatrix coeff M) v a)) ∧
      ∀ z ∈ matrixTrace coeff M v, Bound family (b+2) z := by
  have hd a := dot_bound family unit hunit hb (hlit (M a false)) (hlit (M a true))
    (hv false) (hv true)
  refine ⟨?_, ?_⟩
  · intro a
    simpa only [Kernel.act_apply,realizeMatrix] using (hd a).1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (hd true).2 z hz
    · exact (hd false).2 z hz

include hlit in
theorem transfer_bound {b : ℕ} (hb : 1 ≤ b) (ms : List (Kernel A)) (v : Bool → K)
    (hv : ∀ a, Bound family b (v a)) :
    (∀ a, Bound family (b+2*ms.length) (message (ms.map (realizeMatrix coeff)) v a)) ∧
      ∀ z ∈ transferTrace coeff v ms, Bound family (b+2*ms.length) z := by
  induction ms with
  | nil => simpa [transferTrace] using hv
  | cons M ms ih =>
    have hm := matrix_bound family unit hunit coeff hlit (by omega : 1 ≤ b+2*ms.length)
      M (message (ms.map (realizeMatrix coeff)) v) ih.1
    have heq : b+2*(M::ms).length = (b+2*ms.length)+2 := by simp; omega
    rw [heq]
    refine ⟨?_, ?_⟩
    · simpa only [List.map_cons,message_cons] using hm.1
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact (ih.2 z hz).mono unit hunit (by omega)
      · exact hm.2 z hz

include hlit in
theorem path_bound (l r : Bool → A) (ms : List (Kernel A)) :
    Bound family (2*ms.length+3)
      (pathValue (fun b => coeff (l b)) (ms.map (realizeMatrix coeff)) (fun b => coeff (r b))) ∧
      ∀ z ∈ pathTrace coeff l ms r, Bound family (2*ms.length+3) z := by
  have ht := transfer_bound family unit hunit coeff hlit (by decide : 1 ≤ 1)
    ms (fun b => coeff (r b)) (fun b => hlit (r b))
  have hd := dot_bound family unit hunit (by omega : 1 ≤ 1+2*ms.length)
    (hlit (l false)) (hlit (l true)) (ht.1 false) (ht.1 true)
  have heq : 1+2*ms.length+2 = 2*ms.length+3 := by omega
  rw [heq] at hd
  refine ⟨?_, ?_⟩
  · simpa [pathValue, add_comm] using hd.1
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact (ht.2 z hz).mono unit hunit (by omega)
    · exact hd.2 z hz

theorem basis_bound (b a : Bool) : Bound family 1 (basis (K := K) b a) := by
  by_cases h : a = b
  · simpa [basis,h] using (Bound.one (coeff := family)).mono unit hunit (by decide : 0 ≤ 1)
  · simpa [basis,h] using Bound.zero (coeff := family) unit 1

include hlit in
theorem cycle_bound (ms : List (Kernel A)) :
    Bound family (2*ms.length+2) (cycleValue (ms.map (realizeMatrix coeff))) ∧
      ∀ z ∈ cycleTrace coeff ms, Bound family (2*ms.length+2) z := by
  have ht b := transfer_bound family unit hunit coeff hlit (by decide : 1 ≤ 1)
    ms (basis b) (basis_bound family unit hunit b)
  have hfalse : Bound family (1+2*ms.length) (product (ms.map (realizeMatrix coeff)) false false) := by
    simpa only [message_basis] using (ht false).1 false
  have htrue : Bound family (1+2*ms.length) (product (ms.map (realizeMatrix coeff)) true true) := by
    simpa only [message_basis] using (ht true).1 true
  have hadd := htrue.add unit hunit hfalse
  have heq : 1+2*ms.length+1 = 2*ms.length+2 := by omega
  rw [heq] at hadd
  refine ⟨?_, ?_⟩
  · simpa [cycleValue,Kernel.trace,add_comm] using hadd
  · intro z hz
    simp only [cycleTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with (hz | hz) | rfl | rfl | rfl
    · exact ((ht false).2 z hz).mono unit hunit (by omega)
    · exact ((ht true).2 z hz).mono unit hunit (by omega)
    · exact htrue.mono unit hunit (by omega)
    · exact hfalse.mono unit hunit (by omega)
    · exact hadd

/-- A structural quantity, computed from the descriptor without evaluating it. -/
def Component.budget : Component A → ℕ
  | .scalar _ => 1
  | .path _ ms _ => 2*ms.length+3
  | .cycle _ ms => 2*(ms.length+1)+2

include hlit in
theorem Component.bound (c : Component A) :
    Bound family c.budget (c.eval coeff) ∧
      ∀ z ∈ c.trace coeff, Bound family c.budget z := by
  cases c with
  | scalar a => exact ⟨hlit a, by simp [Component.trace]⟩
  | path l ms r => exact path_bound family unit hunit coeff hlit l r ms
  | cycle M ms =>
    simpa [Component.budget,Component.eval,Component.trace] using
      (cycle_bound family unit hunit coeff hlit (M::ms))

end Holant.LocalDrafts.TraversalCompletion.ArityTwo
