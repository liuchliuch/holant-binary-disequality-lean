import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLinearSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffineCounts
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase

/-! The finite rank-three repair acts on arbitrary actual signed ports. It
requires no Affine face premise and can feed either ordinary, uniform or
LocalAffine semantic preservation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeSchedule
open Holant Holant.Tractable
open OrdinaryNegativeSignedPortsCore (Port)
open scoped BigOperators
namespace P
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace E
export NoXReciprocalRankThreeParityEncoding (encode count_mod all_bits complementary)
end E
namespace A
export NoXReciprocalRankThreeAffinePorts (Transform transformed offset)
export NoXReciprocalRankThreeAffineData (inputBit plus minus schedule)
end A
namespace L
export NoXReciprocalRankThreeLinearSource (schedule offset_zero)
export NoXReciprocalRankThreeLinearCounts (total even_pair)
export NoXReciprocalRankThreeParityData (selector)
end L
namespace C
export NoXReciprocalRankThreeSignedCounts (transformed_count)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {n l : ℕ} (ps : Fin n→Port 7)
def rows (schedule : Fin l→A.Transform) : Fin (l+1)→Fin n→Port 7 :=
  Fin.cases ps (fun i=>A.transformed ps (schedule i))
def positive : Fin 7→ℕ := fun i=>P.signedCount ps i false
def negative : Fin 7→ℕ := fun i=>P.signedCount ps i true

theorem odd_counts (v : Fin 7→ℕ) (h:E.encode v=127) (i : Fin 7) : Odd (v i) := by
  rw [Nat.odd_iff,E.count_mod,h,E.all_bits]
  rfl

theorem total_odd (hc:(E.encode (negative ps)).val=127-(E.encode (positive ps)).val) :
    ∀i,Odd (P.bundleSize ps i) := by
  intro i
  rw [Nat.odd_iff,←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool,Nat.add_mod]
  change ((negative ps i)%2+(positive ps i)%2)%2=1
  rw [E.count_mod,E.count_mod]
  have h:=E.complementary (E.encode (positive ps)) (E.encode (negative ps)) hc i
  cases hp:NoXReciprocalRankThreeParityData.bit (E.encode (positive ps)) i <;>
    cases hn:NoXReciprocalRankThreeParityData.bit (E.encode (negative ps)) i <;> simp_all

theorem linear_counts (r : Fin 64) (q : Fin 7) (bit : Bool) :
    (∑i : Fin 26,P.signedCount (rows ps (L.schedule r) i) q bit)=
      L.total (fun k=>P.signedCount ps k bit) r q := by
  rw [Fin.sum_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,C.transformed_count,L.schedule,L.offset_zero,Bool.xor_false]
  rfl

theorem linear_even (hp:(E.encode (positive ps)).val≠127)
    (hn:(E.encode (negative ps)).val≠127)
    (hc:(E.encode (negative ps)).val≠127-(E.encode (positive ps)).val) :
    ∃l : ℕ,∃schedule : Fin l→A.Transform,∀q bit,Even (∑i,P.signedCount (rows ps schedule i) q bit) := by
  refine ⟨25,L.schedule (L.selector (E.encode (positive ps)) (E.encode (negative ps))),?_⟩
  intro q bit
  rw [linear_counts]
  have h:=L.even_pair (positive ps) (negative ps) hp hn hc q
  cases bit
  · exact h.1
  · exact h.2

theorem affine_even (side : Bool) (q : Fin 126)
    (countsMatch : ∀i bit,P.signedCount ps i bit%2=if A.inputBit side q i bit then 1 else 0) :
    ∃l : ℕ,∃schedule : Fin l→A.Transform,∀j bit,Even (∑i,P.signedCount (rows ps schedule i) j bit) := by
  refine ⟨13,A.schedule side q,?_⟩
  intro j bit
  rw [Fin.sum_univ_succ]
  simp only [rows,Fin.cases_zero,Fin.cases_succ,C.transformed_count]
  exact NoXReciprocalRankThreeAffineCounts.total_even (fun i bit=>P.signedCount ps i bit) side q countsMatch j bit

theorem choose : (∀i,Odd (P.bundleSize ps i)) ∨ (∀i bit,Odd (P.signedCount ps i bit)) ∨
    (∃l : ℕ,∃schedule : Fin l→A.Transform,∀q bit,Even (∑i,P.signedCount (rows ps schedule i) q bit)) := by
  classical
  let p:=E.encode (positive ps)
  let n:=E.encode (negative ps)
  by_cases hp:p.val=127
  · by_cases hn:n.val=127
    · right;left
      intro i bit
      cases bit
      · exact odd_counts (positive ps) (Fin.ext hp) i
      · exact odd_counts (negative ps) (Fin.ext hn) i
    · by_cases hz:n.val=0
      · left
        apply total_odd ps
        change n.val=127-p.val
        omega
      · right;right
        let q : Fin 126 := ⟨n.val-1,by have hlt:=n.isLt;omega⟩
        apply affine_even ps false q
        intro i bit
        cases bit
        · change positive ps i%2=_
          rw [E.count_mod,show E.encode (positive ps)=127 from Fin.ext hp,E.all_bits]
          simp [A.inputBit,A.plus]
        · change negative ps i%2=_
          rw [E.count_mod]
          have hnq:n.val=q.val+1:=by dsimp [q];omega
          simp only [NoXReciprocalRankThreeParityData.bit,show (E.encode (negative ps)).val=q.val+1 from hnq,
            A.inputBit,A.minus,ite_true,ite_false,Bool.false_eq_true]
  · by_cases hn:n.val=127
    · by_cases hz:p.val=0
      · left
        apply total_odd ps
        change n.val=127-p.val
        omega
      · right;right
        let q : Fin 126 := ⟨p.val-1,by have hlt:=p.isLt;omega⟩
        apply affine_even ps true q
        intro i bit
        cases bit
        · change positive ps i%2=_
          rw [E.count_mod]
          have hpq:p.val=q.val+1:=by dsimp [q];omega
          simp only [NoXReciprocalRankThreeParityData.bit,show (E.encode (positive ps)).val=q.val+1 from hpq,
            A.inputBit,A.plus,ite_true,ite_false,Bool.false_eq_true]
        · change negative ps i%2=_
          rw [E.count_mod,show E.encode (negative ps)=127 from Fin.ext hn,E.all_bits]
          simp [A.inputBit,A.minus]
    · by_cases hc:n.val=127-p.val
      · exact Or.inl (total_odd ps hc)
      · exact Or.inr (Or.inr (linear_even ps hp hn hc))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeSchedule
end
