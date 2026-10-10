import Holant.Dihedral.SixPortBase.FourFlat
import Holant.Dihedral.SixPortBase.Unary
import Holant.Dihedral.SixPortBase.MatchingZero
import Holant.Dihedral.SixPortBase.CrossingOriginal
import Holant.Dihedral.SixToFour.Source

/-! The all-oriented phase-card hypothesis and its literal original-port
contraction consequences. No endpoint type or factor data is supplied. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Certificates.NormalizedDihedralQ6
set_option backward.isDefEq.respectTransparency false

 def AllCards (m : ℕ) (h : Signature Scalar 6) : Prop :=
  ∀ order : Equiv.Perm (Fin 6),∀ γ t,Roots m t →
    close γ t (Tensor.reindex order.symm h)=0 ∨
    MatchingSample m 2 (close γ t (Tensor.reindex order.symm h))

 theorem AllCards.reindex {m : ℕ} {h : Signature Scalar 6} (hs : AllCards m h)
    (o : Equiv.Perm (Fin 6)) : AllCards m (Tensor.reindex o h) := by
  intro order γ t ht
  simpa only [Tensor.reindex_trans,Equiv.symm_trans,Equiv.symm_symm]
    using hs (order.trans o.symm) γ t ht

 theorem AllCards.sector_samples {m : ℕ} {h : Signature Scalar 6} (hs : AllCards m h) (γ : Bool) :
    ∀ t,Roots m t → tensorPencil (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ) t=0 ∨
      MatchingSample m 2 (tensorPencil (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ) t) := by
  intro t ht
  have hh := hs (Equiv.refl _) γ t ht
  simpa only [Equiv.refl_symm,Tensor.reindex_refl,sector_card_pencil (s:=2)] using hh

 theorem AllCards.zero_sector_factor {m : ℕ} (hm : 3≤m) {h : Signature Scalar 6}
    (hs : AllCards m h) (hn : h ≠ 0) (order : Equiv.Perm (Fin 6)) (γ : Bool)
    (hz : sectorFirst (s:=2) (Tensor.reindex order.symm h) γ=0 ∧
      sectorSecond (s:=2) (Tensor.reindex order.symm h) γ=0) : HasFactor h := by
  let q := Tensor.reindex order.symm h
  have hq : q ≠ 0 := by
    intro he
    apply hn
    have hh := congrArg (Tensor.reindex order) he
    have hzero : Tensor.reindex order (0 : Signature Scalar 6)=0 := rfl
    simpa only [q,Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl,hzero] using hh
  obtain ⟨D⟩ := exact_pencil hm (sectorFirst (s:=2) q (!γ)) (sectorSecond (s:=2) q (!γ))
    ((hs.reindex order.symm).sector_samples (!γ))
  have hf := factor_of_zero_sector q hq (!γ) D (by simpa only [Bool.not_not] using hz)
  have hh := hf.reindex order
  simpa only [q,Tensor.reindex_trans,Equiv.symm_trans_self,Tensor.reindex_refl] using hh

 theorem contractAt_close (h : Signature Scalar 6) (p : Pair) (hp : p.1 ≠ p.2) (γ : Bool) :
    contractAt h p hp γ=close γ 1 (Tensor.reindex (orderedPorts p hp).symm h) := by
  have hk : parityKernel (K:=Scalar) γ=M γ 1 := by
    funext a b
    cases γ <;> cases a <;> cases b <;> simp [parityKernel,parityEdge,EdgeKind.value,M,monomial,Signature.equality,Signature.disequality]
  rw [contractAt,hk]
  rfl

 theorem MatchingSample.coefficient_card {m : ℕ} (hm : 0<m) {q : Signature Scalar 4}
    (hq : MatchingSample m 2 q) : coefficientSupportCard q=4 := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := hq
  rw [coefficientSupportCard_eq_filter]
  exact Crossing.product_support_four p A κ (fun e => groupM_isMonomial hm (hA e)) hκ

/-- The support atlas's physical I/X card is one of the original all-oriented
phase-one cards. Both matching-coset and lowering alternatives are discharged. -/
 theorem AllCards.four_flat_factor {m : ℕ} (hm : 3≤m) {h : Signature Scalar 6}
    (hs : AllCards m h) (hn : h ≠ 0) (D : SixToFour.FourFlatData)
    (hD : ∀ x,h x ≠ 0 ↔ D.Holds x) : HasFactor h := by
  rcases SixToFour.source_six_to_four D h hD with hmatch | hlow
  · obtain ⟨o,γ,hzero⟩ := matching_coset_zero_sector h D.support
      (fun x => (hD x).trans (D.mem_support x).symm) hmatch
    exact hs.zero_sector_factor hm hn o γ hzero
  · obtain ⟨L⟩ := hlow
    have hh := hs (orderedPorts L.pair L.distinct) L.parity 1 (Roots.one m)
    rw [←contractAt_close] at hh
    rcases hh with hz|hcard
    · exact (L.output_nonzero hz).elim
    · have hc := MatchingSample.coefficient_card (by omega : 0<m) hcard
      have hc' := L.output_card
      have hn' := L.size_six_eight
      omega

 theorem AllCards.complementary_factor {m : ℕ} (hm : 3≤m) {h : Signature Scalar 6}
    (hs : AllCards m h) (hn : h ≠ 0)
    (E : ComplementarySector m (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false))
    (O : ComplementarySector m (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true)) : HasFactor h := by
  obtain ⟨D,_,hD⟩ := complementary_four_flat (by omega : 0<m) h E O
  exact hs.four_flat_factor hm hn D hD

end Holant.Dihedral.SixPortBase
