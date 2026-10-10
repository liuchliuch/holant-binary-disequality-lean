import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeAffineSource
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeLocal
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalEvenCharacterPhase

/-! Complete ordinary separate-parity selection at rank three. The only
non-even repairs are the genuine total-odd and LocalAffine opposite cases. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeRegularSupply
open Holant Holant.Tractable
open OrdinaryNegativeSparseRankDescent
namespace P
export OrdinaryNegativeSparseRankThreePorts (port word_code)
export NoXSeparateSignedProjection (signedCount)
export OrdinaryNegativeSignedPortsIncidence (bundleSize)
end P
namespace E
export NoXReciprocalRankThreeParityEncoding (encode count_mod all_bits complementary)
end E
namespace L
export NoXReciprocalRankThreeLinearSource (positive negative evenBad)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

theorem odd_counts (v : Fin 7→ℕ) (h:E.encode v=127) (i : Fin 7) : Odd (v i) := by
  rw [Nat.odd_iff,E.count_mod,h,E.all_bits]
  rfl

variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val)) (j p0 p1 : Fin s)
variable (h0 : (⟨b p0.val,H p0⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin false⟩)
variable (h1 : (⟨b p1.val,H p1⟩ : AnySignature K)=⟨1,OrdinaryNegativeSignedPortsCore.pin true⟩)
variable (W : OrdinaryNegativeSparseMinimalRank.PinWitness (H j) 3)
variable (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,Affine (minor W.chart S z))
variable (square : Affine (fun x=>(H j x : AlgebraicComplex)^2))

theorem total_odd (hc:(E.encode (L.negative H j W)).val=127-(E.encode (L.positive H j W)).val) :
    ∀i,Odd (P.bundleSize (P.port W.chart) i) := by
  intro i
  rw [Nat.odd_iff,←NoXLocalEvenCharacterPhase.totalCount,Fintype.sum_bool,Nat.add_mod]
  change ((L.negative H j W i)%2+(L.positive H j W i)%2)%2=1
  rw [E.count_mod,E.count_mod]
  have h:=E.complementary (E.encode (L.positive H j W)) (E.encode (L.negative H j W)) hc i
  cases hp:NoXReciprocalRankThreeParityData.bit (E.encode (L.positive H j W)) i <;>
    cases hn:NoXReciprocalRankThreeParityData.bit (E.encode (L.negative H j W)) i <;> simp_all

include h0 h1 minimal square in
theorem ordinary : OrdinaryNegativeXUniversalResource.EvenBad H ∨
    (∀i,Odd (P.bundleSize (P.port W.chart) i)) ∨
    (∀i bit,Odd (P.signedCount (P.port W.chart) i bit)) := by
  classical
  let p:=E.encode (L.positive H j W)
  let n:=E.encode (L.negative H j W)
  by_cases hp:p.val=127
  · by_cases hn:n.val=127
    · right;right
      intro i bit
      cases bit
      · exact odd_counts (L.positive H j W) (Fin.ext hp) i
      · exact odd_counts (L.negative H j W) (Fin.ext hn) i
    · by_cases hz:n.val=0
      · right;left
        apply total_odd H j W
        change n.val=127-p.val
        omega
      · left
        let q : Fin 126 := ⟨n.val-1,by have hlt:=n.isLt;omega⟩
        apply NoXReciprocalRankThreeAffineSource.left H j p0 p1 h0 h1 W minimal square q (Fin.ext hp)
        change n.val=(n.val-1)+1
        omega
  · by_cases hn:n.val=127
    · by_cases hz:p.val=0
      · right;left
        apply total_odd H j W
        change n.val=127-p.val
        omega
      · left
        let q : Fin 126 := ⟨p.val-1,by have hlt:=p.isLt;omega⟩
        apply NoXReciprocalRankThreeAffineSource.right H j p0 p1 h0 h1 W minimal square q (Fin.ext hn)
        change p.val=(p.val-1)+1
        omega
    · by_cases hc:n.val=127-p.val
      · exact Or.inr (Or.inl (total_odd H j W hc))
      · exact Or.inl (L.evenBad H j p0 p1 h0 h1 W minimal square hp hn hc)

include minimal square in
theorem local_of_both (odd : ∀i bit,Odd (P.signedCount (P.port W.chart) i bit)) :
    LocalAffine (OrdinaryNegativeSparseMinimalRank.row (H j) W.pins) :=
  NoXReciprocalRankThreeLocal.local_affine _ W.chart (P.port W.chart)
    (P.word_code W.chart) odd (W.square square) W.bad minimal


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeRegularSupply
end
