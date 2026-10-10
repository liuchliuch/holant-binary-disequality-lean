import Holant.Platonic.StabilizerCode.CommutingAlignment
import Holant.Platonic.StabilizerErasure.CommutingPorts

/-! The logical Clifford needed by the no-correctable-erasure branch follows
from the actual port representatives. No extra alignment witness is required. -/
namespace Holant.Platonic.StabilizerCode
open Holant Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem logical_port_representative_involution (V : StabilizerIsometry k (n+1))
    (r : Fin (n+1)) (p : Fin 4) (Q : Pauli k)
    (hQ : ∀f,siteAction r (qubitPauli p) (V.map f)=V.map (Q.run f))
    (f : Signature ℂ k) : Q.run (Q.run f)=f := by
  apply V.injective
  rw [←hQ,←hQ,siteAction_qubitPauli_involution]

theorem no_correctable_logical_clifford (V : StabilizerIsometry k (n+1))
    (h : ∀r : Fin (n+1),¬Correctable V r) :
    ∃p : Fin (n+1) → Fin 4,∃Q : Fin (n+1) → Pauli k,
      ∃C : AnalyticClifford k,∃s : Fin (n+1) → ZMod 2,
        ∃b : Fin (n+1) → BinaryVector k,
          (∀r,p r≠0 ∧ b r≠0) ∧
          (∀r f,siteAction r (qubitPauli (p r)) (V.map f)=V.map ((Q r).run f)) ∧
          ∀r f,C.operator ((Q r).run f)=
            sign (s r) • standardPauli 0 0 (b r) (C.operator f) := by
  obtain ⟨p,Q,hp,hQ,hcomm⟩ := no_correctable_commuting_logicals V h
  obtain ⟨C,s,b,he,hb⟩ := exists_commuting_nontrivial_pauli_alignment Q hcomm
    (fun r => logical_port_representative_involution V r (p r) (Q r) (hQ r))
    (fun r => (hp r).2)
  exact ⟨p,Q,C,s,b,fun r => ⟨(hp r).1,hb r⟩,hQ,he⟩

end
end Holant.Platonic.StabilizerCode
