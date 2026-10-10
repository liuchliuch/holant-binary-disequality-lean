import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityCertificate
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeParityEncoding

/-! The finite operator acts on the actual unbounded natural multiplicities,
not just their Boolean representatives. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLinearCounts
open scoped BigOperators
namespace D
export NoXReciprocalRankThreeParityData (column functional dot schedule selector)
end D
namespace C
export NoXReciprocalRankThreeParityCertificates (selected column_value)
end C
namespace E
export NoXReciprocalRankThreeParityEncoding (encode count_mod)
end E
namespace P
export OrdinaryNegativeSparseRankThreeParity (image)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false

def total (v : Fin 7→ℕ) (r : Fin 64) (j : Fin 7) : ℕ :=
  v j+∑k : Fin 25,∑i : Fin 7,if P.image (D.schedule r k) i=j.succ then v i else 0

theorem linear (v : Fin 7→ℕ) (r : Fin 64) (j : Fin 7) :
    total v r j=∑i : Fin 7,v i*((if i=j then 1 else 0)+
      ∑k : Fin 25,if P.image (D.schedule r k) i=j.succ then 1 else 0) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_comm]
  simp [total]

theorem mod_two (v : Fin 7→ℕ) (r : Fin 64) (j : Fin 7) :
    total v r j%2=D.dot (E.encode v) r := by
  rw [linear,Finset.sum_nat_mod]
  have hnorm :
      (∑i : Fin 7,(v i*((if i=j then 1 else 0)+
        ∑k : Fin 25,if P.image (D.schedule r k) i=j.succ then 1 else 0))%2)=
      ∑i : Fin 7,(v i%2*D.column r i j)%2 := by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_mod _ _ _
  rw [hnorm]
  simp_rw [C.column_value,E.count_mod]
  unfold D.dot
  apply congrArg (fun z : ℕ=>z%2)
  apply Finset.sum_congr rfl
  intro i _
  cases hp:NoXReciprocalRankThreeParityData.bit (E.encode v) i <;>
    cases hq:D.functional r i <;> simp [hp,hq]


theorem even_pair (p n : Fin 7→ℕ)
    (hp:(E.encode p).val≠127) (hn:(E.encode n).val≠127)
    (hc:(E.encode n).val≠127-(E.encode p).val) :
    ∀j,Even (total p (D.selector (E.encode p) (E.encode n)) j) ∧
      Even (total n (D.selector (E.encode p) (E.encode n)) j) := by
  have h:=C.selected (E.encode p) (E.encode n) hp hn hc
  intro j
  constructor
  · rw [Nat.even_iff,mod_two,h.1]
  · rw [Nat.even_iff,mod_two,h.2]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeLinearCounts
