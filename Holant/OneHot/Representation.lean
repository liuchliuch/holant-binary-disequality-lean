import Holant.OneHot.NetworkBridge.Table
import Holant.Network

/-! Every actual one-hot signature is exactly its zero/singleton coefficient
representation, including arity zero. This is a semantic reconstruction theorem,
not a membership oracle or a gadget realization claim. -/

namespace Holant.OneHot

variable {K : Type*} {n : ℕ}

/-- A weight-one Boolean word has exactly one true coordinate. -/
theorem word_eq_singleton_of_weight_one (x : Fin n → Bool) (hx : weight x = 1) :
    ∃ i : Fin n, x = fun j => decide (j = i) := by
  classical
  have hc : (Finset.univ.filter fun j => x j = true).card = 1 := by
    simpa only [weight, Finset.card_filter] using hx
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  refine ⟨i, funext fun j => ?_⟩
  have hm : x j = true ↔ j = i := by
    have h := congrArg (fun s : Finset (Fin n) => j ∈ s) hi
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using Iff.of_eq h
  cases h : x j <;> simp_all

/-- Equality with the literal canonical table built from the signature's actual
values at the zero word and each singleton word. No nonzero assumptions occur. -/
theorem eq_table_of_oneHot [CommSemiring K] {f : Signature K n}
    (hf : Signature.OneHot f) :
    f = table (f (fun _ => false)) (fun i => f (fun j => decide (j = i))) := by
  funext x
  by_cases h0 : weight x = 0
  · have hx : x = fun _ => false := funext ((weight_eq_zero_iff x).mp h0)
    rw [hx, table_zero]
  · by_cases h1 : weight x = 1
    · obtain ⟨i, rfl⟩ := word_eq_singleton_of_weight_one x h1
      rw [table_singleton]
    · have hlarge : 1 < weight x := by omega
      rw [hf x hlarge]
      simp [table, Nat.not_le.mpr hlarge]

/-- Canonical coefficients characterize the whole one-hot support class exactly. -/
theorem oneHot_iff_eq_table [CommSemiring K] (f : Signature K n) :
    Signature.OneHot f ↔
      f = table (f (fun _ => false)) (fun i => f (fun j => decide (j = i))) := by
  constructor
  · exact eq_table_of_oneHot
  · intro h
    rw [h]
    exact table_oneHot _ _

end Holant.OneHot

namespace Holant.Network

variable {K : Type*} [CommSemiring K] {n : ℕ}

/-- Reconstruct every local label from its actual zero and singleton coefficients,
without changing any vertex, edge, port occurrence, or edge tensor. -/
def oneHotTables (N : Network K n) : Network K n where
  shape := N.shape
  vertex v := OneHot.table (N.vertex v (fun _ => false))
    (fun i => N.vertex v (fun j => decide (j = i)))
  edge := N.edge

/-- Canonical coefficient reconstruction preserves the original graph sum exactly. -/
theorem denote_oneHotTables (N : Network K n)
    (hN : ∀ v, Signature.OneHot (N.vertex v)) : N.oneHotTables.denote = N.denote := by
  apply denote_congr
  · intro v x
    exact congrFun (OneHot.eq_table_of_oneHot (hN v)).symm x
  · intro e a b
    rfl

end Holant.Network
