import Holant.Platonic.StabilizerErasure.PhysicalPauli

/-! Operators on distinct physical ports commute, and injectivity transfers
this commutation to their exact logical Pauli representatives. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k : ℕ}

theorem siteAction_commute (r s : Fin (n+1)) (hrs : r≠s)
    (R S : Bool → Bool → ℂ) (f : Signature ℂ (n+1)) :
    siteAction r R (siteAction s S f)=siteAction s S (siteAction r R f) := by
  ext w
  simp [siteAction,Function.update_of_ne hrs,Function.update_of_ne (Ne.symm hrs),
    Function.update_comm hrs]
  ring

theorem logical_representatives_commute (V : StabilizerIsometry k (n+1))
    (r s : Fin (n+1)) (hrs : r≠s) (p q : Fin 4) (P Q : Pauli k)
    (hP : ∀f,siteAction r (qubitPauli p) (V.map f)=V.map (P.run f))
    (hQ : ∀f,siteAction s (qubitPauli q) (V.map f)=V.map (Q.run f))
    (f : Signature ℂ k) : P.run (Q.run f)=Q.run (P.run f) := by
  apply V.injective
  rw [←hP,←hQ,←hQ,←hP]
  exact siteAction_commute r s hrs _ _ _

/-- A choice of one nontrivial logical Pauli per physical port, with all
pairwise commutation proved, follows from failure of every single erasure. -/
theorem no_correctable_commuting_logicals (V : StabilizerIsometry k (n+1))
    (h : ∀r : Fin (n+1),¬Correctable V r) :
    ∃p : Fin (n+1) → Fin 4,∃Q : Fin (n+1) → Pauli k,
      (∀r,p r≠0 ∧ ((Q r).shift≠0 ∨ (Q r).character≠0)) ∧
      (∀r f,siteAction r (qubitPauli (p r)) (V.map f)=V.map ((Q r).run f)) ∧
      ∀r s f,(Q r).run ((Q s).run f)=(Q s).run ((Q r).run f) := by
  choose p Q hp hQ he using fun r => not_correctable_logical_representative V r (h r)
  refine ⟨p,Q,fun r => ⟨hp r,hQ r⟩,he,?_⟩
  intro r s f
  by_cases hrs : r=s
  · subst s;rfl
  · exact logical_representatives_commute V r s hrs (p r) (p s) (Q r) (Q s) (he r) (he s) f

end
end Holant.Platonic.StabilizerErasure
