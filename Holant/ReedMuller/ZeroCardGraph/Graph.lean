import Holant.ReedMuller.ZeroCardGraph.Cards
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The graph is defined from the original tensor. Its equality with the
literal zero-card graph is proved, then its complete bipartite components are
derived from one actual supported word and propagation along paths. -/
namespace Holant.ReedMuller.ZeroCardGraph
open Holant
variable {ι K : Type*} [DecidableEq ι]
section Zero
variable [Zero K]

 def graph (f : Tensor K ι) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ ∀ x : ι → Bool,f x ≠ 0 → x i ≠ x j
  symm := by
    constructor
    intro i j h
    exact ⟨h.1.symm,fun x hx => (h.2 x hx).symm⟩
  loopless := by constructor; intro i h; exact h.1 rfl

 theorem graph_adj {f : Tensor K ι} {i j : ι} :
    (graph f).Adj i j ↔ i ≠ j ∧ ∀ x : ι → Bool,f x ≠ 0 → x i ≠ x j := Iff.rfl

 private theorem xor_chain (a b c : Bool) : (a ^^ c)=((a ^^ b) ^^ (b ^^ c)) := by
  cases a <;> cases b <;> cases c <;> decide
 private theorem xor_true (a b : Bool) : (a ^^ b)=true ↔ a ≠ b := by
  cases a <;> cases b <;> decide

 theorem walk_parity (f : Tensor K ι) (w x : ι → Bool) (hw : f w ≠ 0) (hx : f x ≠ 0)
    {i j : ι} (p : (graph f).Walk i j) : (x i ^^ x j)=(w i ^^ w j) := by
  induction p with
  | nil => simp
  | @cons i j k hij p ih =>
    have hxij := (xor_true (x i) (x j)).mpr (hij.2 x hx)
    have hwij := (xor_true (w i) (w j)).mpr (hij.2 w hw)
    rw [xor_chain (x i) (x j) (x k),xor_chain (w i) (w j) (w k),hxij,hwij,ih]

 theorem reachable_parity (f : Tensor K ι) (w x : ι → Bool) (hw : f w ≠ 0) (hx : f x ≠ 0)
    {i j : ι} (hp : (graph f).Reachable i j) : (x i ^^ x j)=(w i ^^ w j) := by
  obtain ⟨p⟩ := hp
  exact walk_parity f w x hw hx p

/-- This is the literal complete-bipartite adjacency statement on each actual
connected component, including isolated vertices. -/
 theorem component_bipartite (f : Tensor K ι) (w : ι → Bool) (hw : f w ≠ 0)
    (root i j : ι) (hi : (graph f).Reachable root i) (hj : (graph f).Reachable root j) :
    (graph f).Adj i j ↔ w i ≠ w j := by
  constructor
  · intro h
    exact h.2 w hw
  · intro h
    refine ⟨fun he => h (congrArg w he),?_⟩
    intro x hx
    apply (xor_true (x i) (x j)).mp
    rw [reachable_parity f w x hw hx (hi.symm.trans hj)]
    exact (xor_true (w i) (w j)).mpr h

 theorem components_complete_bipartite (f : Tensor K ι) (hf : f ≠ 0) :
    ∃ w : ι → Bool, f w ≠ 0 ∧ ∀ root i j,
      (graph f).Reachable root i → (graph f).Reachable root j →
      ((graph f).Adj i j ↔ w i ≠ w j) := by
  classical
  have hex : ∃ w,f w ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hf (funext hh)
  obtain ⟨w,hw⟩ := hex
  exact ⟨w,hw,component_bipartite f w hw⟩

end Zero

 section Field
 variable [Field K]
 theorem graph_zero_cards (htwo : (2:K) ≠ 0) (f : Tensor K ι) (i j : ι) (hij : i ≠ j) :
    (graph f).Adj i j ↔ card f i j false=0 ∧ card f i j true=0 := by
  rw [zero_cards_iff_opposite htwo]
  exact ⟨fun h => h.2,fun h => ⟨hij,h⟩⟩
 end Field

end Holant.ReedMuller.ZeroCardGraph
