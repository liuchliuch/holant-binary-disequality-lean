import Holant.Dihedral.SixPortBase.Deck
import Holant.Dihedral.SixPortBase.Rows
import Holant.Dihedral.SixPortBase.CrossingPhysical

/-! Both remaining endpoint branches are discharged by actual original-port
phase-one cards. The P/P conclusion is an exact physical unary factor; P/C
contradicts either actual support size or the distinguished-pair projection. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Dihedral.SectorRuling
open Holant.Dihedral.CompatibleCoefficientLine Crossing
set_option backward.isDefEq.respectTransparency false

 theorem AllCards.proportional_factor {m : ℕ} (hm : 3≤m) {h : Signature Scalar 6}
    (hs : AllCards m h) (hn : h ≠ 0)
    (E : ProportionalSector m (sectorFirst (s:=2) h false) (sectorSecond (s:=2) h false))
    (O : ProportionalSector m (sectorFirst (s:=2) h true) (sectorSecond (s:=2) h true)) : HasFactor h := by
  obtain ⟨c,_,_,hc⟩ := pp_actual_card (parityWeights false E.first E.second) (parityWeights true O.first O.second)
    (paritySupported_monomial _ _) (paritySupported_monomial _ _)
    E.ports O.ports (twoFactors E.fixedEdge E.fixed E.varying) (twoFactors O.fixedEdge O.fixed O.varying) 1 1
    (twoFactors_monomial _ (groupM_isMonomial (by omega) E.fixed_mem) (groupM_isMonomial (by omega) E.varying_mem))
    (twoFactors_monomial _ (groupM_isMonomial (by omega) O.fixed_mem) (groupM_isMonomial (by omega) O.varying_mem))
    one_ne_zero one_ne_zero
  have hsizes := actual_card_rowSupport_card (by omega : 0<m) h c false
    (hs (crossingOrder c) false 1 (Roots.one m))
  rw [pp_rows h E O] at hsizes
  have hsum := hc false
  have hEpos := parityWeights_card_pos false E.first E.second E.nonzero
  have hOpos := parityWeights_card_pos true O.first O.second O.nonzero
  have hE : (binarySupport (parityWeights false E.first E.second)).card≤1 := by omega
  have hO : (binarySupport (parityWeights true O.first O.second)).card≤1 := by omega
  exact proportional_singletons_factor h hn E O
    (parityWeights_singleton false E.first E.second hE) (parityWeights_singleton true O.first O.second hO)

 theorem AllCards.no_mixed_sector {m : ℕ} (hm : 3≤m) {h : Signature Scalar 6}
    (hs : AllCards m h) (γ : Bool)
    (E : ProportionalSector m (sectorFirst (s:=2) h γ) (sectorSecond (s:=2) h γ))
    (O : ComplementarySector m (sectorFirst (s:=2) h (!γ)) (sectorSecond (s:=2) h (!γ))) : False := by
  have hVm : IsMonomial (parityWeights (!γ) O.first O.second) :=
    ⟨!γ,(fun z => if z then O.second else O.first),
      by intro z; cases z; exact O.first_ne_zero; exact O.second_ne_zero,rfl⟩
  obtain ⟨c,_,_,hc⟩ := pc_actual_card_projection
    (parityWeights γ E.first E.second) (parityWeights (!γ) O.first O.second)
    (paritySupported_monomial _ _) (paritySupported_monomial _ _) hVm
    E.ports O.ports (twoFactors E.fixedEdge E.fixed E.varying)
    (fun w => twoFactors O.fixedEdge O.fixed (axis O.parity (O.orientation ^^ w.1))) 1 1
    (twoFactors_monomial _ (groupM_isMonomial (by omega) E.fixed_mem) (groupM_isMonomial (by omega) E.varying_mem))
    (fun w => twoFactors_point _ (groupM_isMonomial (by omega) O.fixed_mem) (axis_point _ _))
    one_ne_zero one_ne_zero
  have hsizes := actual_card_rowSupport_card (by omega : 0<m) h c false
    (hs (crossingOrder c) false 1 (Roots.one m))
  have hprojections := actual_card_projection_card (by omega : 0<m) h c false
    (hs (crossingOrder c) false 1 (Roots.one m))
  rw [pc_rows h γ E O] at hsizes hprojections
  have hsum := hc false
  dsimp only at hsum
  have hEpos := parityWeights_card_pos γ E.first E.second E.nonzero
  omega

end Holant.Dihedral.SixPortBase
