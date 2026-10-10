import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSixLinearPacked

/-! Exact linear expansion of the literal six-port source and its sixteen
cross-pair Bell probes. Positional encoding is linear up to one fixed bias. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncoding
open scoped BigOperators
namespace D
export GlobalCloseCompletionKleinSixFiniteData (line source card sign fill)
end D
namespace C
export GlobalCloseCompletionKleinGramCertificate (pauli word)
end C
namespace P
export GlobalCloseCompletionKleinSixPacked (encode)
end P
namespace L
export GlobalCloseCompletionKleinSixLinearPacked (bias)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384
set_option Elab.async false

def lift (e : Fin 4) (a : Fin 48) (w : Fin 64) : ℤ :=
  C.pauli e (w.val.testBit 5) (w.val.testBit 4)*D.line a ⟨w.val%16,Nat.mod_lt _ (by decide)⟩

def linearCard (e : Fin 4) (a : Fin 48) (j k : Fin 4) (x : Fin 16) : ℤ :=
  ∑t : Fin 4,C.pauli k (C.word t 0) (C.word t 1)*lift e a (D.fill j x t)

def coefficient (e : Fin 4) (a : Fin 48) (j k : Fin 4) : ℤ :=
  ∑x : Fin 16,linearCard e a j k x*9^x.val

theorem source_lift (a b c : Fin 48) (s : Fin 8) (w : Fin 64) :
    D.source a b c s w=lift 0 0 w+D.sign s 0*lift 1 a w+
      D.sign s 1*lift 2 b w+D.sign s 2*lift 3 c w := by
  fin_cases w <;> norm_num [D.source,lift,C.pauli,Nat.testBit_eq_decide_div_mod_eq] <;> ring

theorem card_lift (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) (x : Fin 16) :
    D.card a b c s j k x=linearCard 0 0 j k x+D.sign s 0*linearCard 1 a j k x+
      D.sign s 1*linearCard 2 b j k x+D.sign s 2*linearCard 3 c j k x := by
  unfold D.card linearCard
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  rw [source_lift]
  ring

theorem bias_value : L.bias=(∑i : Fin 16,(4:ℤ)*9^i.val) := by decide +kernel

theorem code_expansion (a b c : Fin 48) (s : Fin 8) (j k : Fin 4) :
    P.encode (D.card a b c s j k)=L.bias+coefficient 0 0 j k+D.sign s 0*coefficient 1 a j k+
      D.sign s 1*coefficient 2 b j k+D.sign s 2*coefficient 3 c j k := by
  rw [bias_value]
  unfold P.encode coefficient
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [card_lift]
  ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinSixEncoding
